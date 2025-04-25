(* begin hide*)
  Require Export ProcessingPrograms.
  From Coq Require Import Init.Nat.
  From Coq Require Import Lists.List. Import ListNotations.
(* end hide*)

(** %\chapter{Combining programs}%  *)
  (** Simple instructions of $\mathscr{S}$ programs, make it easy to reason about them, but on the other hand, it's too laborious to write complex programs in practice. To tackle this problem we introduce "macro" instructions, to use previously defined programs in constructing the new ones. As we saw previously, it's not as simple as just inserting a predefined program somewhere in the body of the new one. Clearly, doing so arises conflicts between their labels and variables and the result won't be as desired. Thus first we must process the program such that without any conflict, it does the same task as it did before. Then add extra instructions to the main program to make it able to run the modified program on some inputs and extract the output. Finally, We abbreviate the calls to this program as a special command and call it a macro.
  There are two main steps in preprocessing a program to make it ready for insertion in any other program as described in the textbook. In the next two sections, we discuss and formally implement any of these procedures. *)

(** * Normalizing a program *)

  (** Changing the name of the labels of a program so that they will be among [A 0, A 1,...,]%\\%[A l] except the labels in the instruction which do not appear as the labels of any line (thus basically an exit label); these labels are all replaced with E 0. Clearly, renaming of labels won't change the task of the program. In fact, the effect of the program on any snapshot remains the same. But the reason for doing these will be clarified as we go through the next steps. *)

  (* Task 1: convert all line labels to be of the form A i *)

    (** The following function takes a program and checks the last [index] number of the lines and each time if the line was labeled of any form other than [A i], substitutes its label in the whole program with the first label of the form [A i] which doesn't exist in the program yet ( [max_A_lab] finds such label and  [subst_lab] replaces with it). Thus it's enough to start this function with [index = length p] to change all line labels to the desired to form. %\pagebreak%*)

    (* first we convert all labels of all lines (and their corresponding
      occurances in statements) so that all of them be of the form A i *)
    Fixpoint general_all_line_lab_A (p: prog) (index: nat):=
      match index with
        | 0 => p 
        | S i => match ith_ins_prog index p with 
          | __s s => general_all_line_lab_A p i
          | l_s l s => match l with
            | A j => general_all_line_lab_A p i
            | _ => general_all_line_lab_A (subst_lab p l (max_A_lab p)) i
            end
          end
      end.

    Definition all_line_lab_A (p: prog):= general_all_line_lab_A p (length p).

    (* Some examples *)
      (* begin hide*)
      Example all_line_lab_A_test1 : all_line_lab_A nil = nil . 
      Proof. reflexivity. Qed.
      
      Example all_line_lab_A_test2 : all_line_lab_A <{
       [    A 0    ] Y ++ ;
       [(** $ \I$*)] Y -- ;
       [    C 0    ] Z 0 → C 0;
       [    C 0    ] X 0 ++
      }> = <{
        [    A 0    ] Y ++ ;
        [(** $ \I$*)] Y -- ;
        [    A 1    ] Z 0 → A 1;
        [    A 1    ] X 0 ++
      }>. 
      Proof. reflexivity. Qed. 
      (* end hide*)
    (*  *)

    (* begin hide*)
      (* To be proved in the future if necessary... *)
      Lemma all_line_lab_A_sound: forall p: prog, forall l: lab, 
        In l (lines_lab p) -> (exists i, eq_lab l (A i) = true).
      Proof. Abort.
    (* end hide*)

  (*  *)

  (* Task 2: change all non-occured labels to E *)
    (** Next we need to normalize the exit labels. The following functions work similarly to the previous ones, except they revise the exit labels. *)

    Fixpoint general_E_only_exit (p: prog) (index: nat):=
      match index with
        | 0 => p 
        | S i => match ith_ins_prog i p with 
          | __s (cond v l) => if is_in_lab_list l (lines_lab p)
                              then general_E_only_exit p i
                              else general_E_only_exit (subst_lab p l (E 0)) i
          | l_s _ (cond v l) => if is_in_lab_list l (lines_lab p)
                              then general_E_only_exit p i
                              else general_E_only_exit (subst_lab p l (E 0)) i
          | _ => general_E_only_exit p i
          end
      end.
    Definition E_only_exit (p:prog) := general_E_only_exit p (length p + 1).

    (* Some examples *)
      (* begin hide*)
      Example E_only_exit_test1 : E_only_exit nil = nil . 
      Proof. reflexivity. Qed.

      Example E_only_exit_test2 : E_only_exit <{
          [(** $ \I$*)] Y → A 0 ;
          [    A 0    ] Y ++ ;
          [    B 0    ] Y → A 3 
        }> = <{
          [(** $ \I$*)] Y → A 0  ;
          [    A 0    ] Y ++ ;
          [    B 0    ] Y → E 0    
        }>. 
        Proof. reflexivity. Qed. 
      (* end hide*)
    (*  *)

  (** Finally, we encapsulate both of the aforementioned functions into one: *)

  Definition normalize (p: prog):= E_only_exit (all_line_lab_A p).

  (** %\pagebreak% *)
  Definition both_valued := <{
    [    A 2   ] X 0 → B 1; 
    [(** $\I$*)] Z 0 ++;
    [(** $\I$*)] Z 0 → C 1;
    [    B 1   ] X 1 → E 0;
    [(** $\I$*)] Z 1 ++;
    [(** $\I$*)] Z 1 → D 2;
    [    E 0   ] Y ++
  }>. 
  Example normalize_test : normalize both_valued = <{
    [    A 2   ] X 0 → A 4; 
    [(** $\I$*)] Z 0 ++;
    [(** $\I$*)] Z 0 → E 0;
    [    A 4   ] X 1 → A 3;
    [(** $\I$*)] Z 1 ++;
    [(** $\I$*)] Z 1 → E 0;
    [    A 3   ] Y ++
  }>. 
  Proof. reflexivity. Qed. 
  
  (* begin hide*)
    (* To be proved in the future if necessary... *)
    Lemma normalization_sound: forall p, a_equal p (normalize p).
    Proof. Abort.
  (* end hide*)
(*  *)

(** * Localizing a program  *)
  (** The next step to preparing a program to be inserted in another one is localization. We need to change its variables so that all of them act as local variables. Furthermore, we save the new names of the original input and output variables somewhere, so that later on we'll able to successfully execute the program in another program. It's also necessary to make changes so that after finishing the task, it won't exist the whole main program. Thus (assuming it's a normal program) we add a superfluous instruction labeled [E 0] to play the role of the finish line (and the only way to exit).*)
  
  (** For simplicity, we use states for saving the names (more precisely, the coding) of the replaced local variables and pair such state with the corresponding program: *)
  
  Inductive local_prog_inout:= | lp_inout (lp: prog) (input: state).

  (** What follows is a general function which in addition to a program, takes a local variable ([zfloor]), an [index] and a [state]. The task is to start from the last line of the program and replace the non-local variable with the given local variable (in the whole program, using [subst_var]) and save the code of the new names of the variables in the given state, and repeat this procedure for [index] times. Thus if we append the aforementioned superfluous instruction and let [zfloor] be the first non-occured local variable of the program ([max_Z_var p]), [index:= length p] and [st:= nil] then The result would be the desired localized program. %\pagebreak%*)

  (* Convert all labels to be Z i's ≥ some Z j (zfloor) 
    and simultaneously save the new name of appeared Y and X k's*)
    Fixpoint general_localize (p: prog) (zfloor: var) (index: nat) (inout: state):=
      match index with 
      | 0 => lp_inout p inout
      | S k => match v_ (_s (ith_ins_prog index p)) with 
        | Z j => general_localize p zfloor k inout
        | v => general_localize 
          (subst_var p v zfloor)
          (next_Z zfloor)
          k
          (var_update_state v (# zfloor) inout)
        end
      end.

  Definition localize (p: prog):=
    general_localize (<{p ; [ E 0 ] skip Y}>) (max_Z_var p) (length p) nil.

  (* Some examples *)
    (* begin hide*)
    Example localize_test1 : localize <{
        [(** $ \I$*)] Y ++;
        [    A 0    ] Z 0 ++;
        [(** $ \I$*)] X 5 --
      }> = lp_inout <{
        [(** $ \I$*)] Z 2 ++;
        [    A 0    ] Z 0 ++;
        [(** $ \I$*)] Z 1  --;
        [    E 0    ] skip (Z 2) 
      }> [# Z 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; # Z 2]. 
    Proof. reflexivity. Qed. 
    (* end hide*)

  (* *)
  (* [???] de-localize and show combination is a-eq *)
  
  (** As mentioned at the beginning of this section, in order to localization make sense, the program to be localized should be normal at first (o.w. the superfluous instruction $ \\ $ [<{[ E 0 ] skip Y}>] won't act as the only finish line). Thus combining localization with normalization we define the following: *)

  Definition local_normal (p:prog):= localize( normalize p).
  Example local_normal_test1 : local_normal both_valued =  lp_inout <{
    [    A 2   ] Z 4 → A 4; 
    [(** $\I$*)] Z 0 ++;
    [(** $\I$*)] Z 0 → E 0;
    [    A 4   ] Z 3 → A 3;
    [(** $\I$*)] Z 1 ++;
    [(** $\I$*)] Z 1 → E 0;
    [    A 3   ] Z 2 ++;
    [    E 0   ] skip (Z 2)
  }> [# Z 3; 0; # Z 4; # Z 2 ].
  Proof. reflexivity. Qed.
(*  *)

(** * Making programs compatible *)

  (** Now that we have implemented the machinery for local-normalizing programs it's time to shift the labels ([using lab_shift]) and variables (using [var_shift]) so that no conflict arises when a program is inserted in another one. Furthermore, it's important to preserve the form of the variables and labels so that they remain localized. Two functions [next_eq_even] and [next_eq_5k] take care of this: *)

  Definition local_normal_prog (p: prog):=    
    match local_normal p with | lp_inout p i => p end.

  Definition local_normal_inout (p: prog):=    
    match local_normal p with | lp_inout p inout => inout end.

  Definition next_eq_even (n: nat):= if even n then n else S n.

  Fixpoint next_eq_5k (n: nat):= match n with 
    | 0 => 0 | S ( S (S ( S (S m)))) => (next_eq_5k m) + 5 | _ => 5 end.

  Definition make_compatible (p: prog) (p': prog):=
    lab_shift 
      (var_shift (local_normal_prog p') (next_eq_even(# (max_var p))))
      (next_eq_5k (# (max_lab p))). (**  *)

  (* Some examples *) 
    (** The following example shows how conflicts are handled:*)

    Example make_compatible1_test1 : make_compatible <{
        [    A 3   ] Z 2 → E 0
      }> both_valued = <{
        [    A 6   ] Z 8 → A 8; 
        [(** $\I$*)] Z 4 ++;
        [(** $\I$*)] Z 4 → E 4;
        [    A 8   ] Z 7 → A 7;
        [(** $\I$*)] Z 5 ++;
        [(** $\I$*)] Z 5 → E 4;
        [    A 7   ] Z 6 ++;
        [    E 4   ] skip (Z 6) 
      }>. 
    Proof. reflexivity. Qed. 
    
    (* begin hide*)
    Example make_compatible_test2 : make_compatible <{
        [    A 1    ] X 0 → A 3;
        [    B 0    ] Z 3 → E 0
      }> <{
        [    C 2    ] Y ++;
        [(** $ \I$*)] Z 0 → E 2
      }> = <{
        [    A 2    ] Z 6 ++;
        [(** $ \I$*)] Z 5 → E 2;
        [    E 2    ] skip (Z 6) 
      }>. 
    Proof. reflexivity. Qed. 
    (* end hide*)

    (* The reason for the harmless gap (instead of Z 4, Z 5 we have Z 5, Z 6) is that after localization, the codes of all variables are positive. but [var_shift is designed in a way that Y (which is coded as 0) is replaced with the first possible option, X 0 with the second one and... (see the shift parameter). *)
  (* *)

  (** Similarly the saved input names are needed to be shifted, thus we should do the same on the state. The [state_shift_if_updated] checks what variables are localized and shifts them as much as they fit the compatible program. *)

  Definition mac_inout (p: prog) (p': prog):=    
    state_shift_if_updated (local_normal_inout p') (next_eq_even(# (max_var p))).
  
  (* Some examples *) 
    Example mac_inout_test1 : mac_inout <{
      [    A 3   ] Z 2 → E 0
    }> both_valued = [# Z 7; 0; # Z 8; # Z 6]. 
    Proof. reflexivity. Qed. 
    
  (* begin hide*)
    Example mac_inout_test2 : mac_inout 
      <{
        [    A 1    ] X 0 → A 3;
        [    B 0    ] Z 3 → E 0
      }>
      <{
        [    C 2    ] Y ++;
        [(** $ \I$*)] Z 0 → E 2
      }>  =  [# Z 6]. 
    Proof. reflexivity. Qed. 
  (* end hide*)
  (* *)
  
(*  *)

(** * Executing a local program *)
  (** We formally define a macro to be the tripple of a variable, a program and a list of variables as inputs: *)

  Inductive macro:= | vpi (v: var) (p: prog) (i: list var).

  (** A macro as an instruction in the middle of a program tells that "run the program [p] on the inputs [i] and save its output value in the variable [v]".
  To fully unravel what a macro does, despite making the program in macro compatible with the main program, we need to add extra instructions to the main program, so that it can execute the local program. There are three tasks to be done here:
    - cleaning the value of all variables of [p]. This seems reduntand at first glance, but in fact it's necessary if [p] is going to be executed in a loop
    - allocating the values of the variables in the list of inputs [i] to the input variables of [p] 
    - extracting the output of [p] and save it in [w] *)

  (** The function [total_var_clear] does the first job (not so efficiently) while using different labels for each  loop of [var_clear], so no conflicts will arise:*)

    Fixpoint total_var_clear (p: prog) (floor: nat):=
      match p with
        | nil => nil
        | i::p' => <{
          var_clear (B floor) (ins_var i) ;
          total_var_clear p' (floor + 1)
        }>  
      end.
      (* a more sophisticated function can prevent repetitions too. *)
      (* Compute total_var_clear both_valued 3. *)

  (** The task is done by the [in_allocations] function. It takes a list of variables and the name of local inputs. Then for each variable in the list, based on its rank in the list, the function checks whether the original program takes such input (i.e. whether [X rank] is used in the program or not). If there wasn't such input, it skips this variable, otherwise, it generates instructions to allocate the value of the variable to the corresponding new name of the input and repeats this procedure for all variables in the list. Similar to the previous function, it uses the parameter [floor] to prevent conflicts between labels.*)

  Fixpoint in_allocations (lv' : list var)(inout : state)(floor : nat)(w : var):=
    match lv' with 
      | nil => nil
      | v'::l => if (state_var inout (X (length l))) =? 0
        then (in_allocations l inout floor w) 
        else <{
            var_transmit (C floor)(D floor)(E floor) 
              w (decode_var (state_var inout (X (length l)))) v';         
            (** [\\] $recall\,\, that$ [w] $can\,\, be\,\, reused\,\, without\,\, making\,\, real\,\, confliction.$*) 

            in_allocations l inout (floor+1) w
          }>
    end.

  (* Some examples *) 
    (** %\pagebreak% *)
    Example in_allocations_test1 : in_allocations 
    [X 2] [# Z 0 ; 0 ] 5 (Z 1) = 
    <{ 
      [(** $ \I$*)] X 2 → C 5 ;
      [(** $ \I$*)] Z 1 ++ ;
      [(** $ \I$*)] Z 1 → E 5 ;
      [    C 5    ] X 2 -- ; 
      [(** $ \I$*)] Z 0 ++ ;
      [(** $ \I$*)] Z 1 ++ ;
      [(** $ \I$*)] X 2 → C 5 ;
      [    D 5    ] Z 1 -- ; 
      [(** $ \I$*)] X 2 ++ ;
      [(** $ \I$*)] Z 1 → D 5 ;
      [    E 5    ] Z 1 --
    }>. 
    Proof. reflexivity. Qed.
  (* *)
  
  (** Finally the [unravel_macro] below combines all the instructions and preprocessing and does the third task: *)
  
  Definition lab_index (l: lab) := match l with 
    | A i => i | B i => i | C i => i| D i => i| E i => i end.

  Definition loc_Y (p p': prog):= decode_var(state_var (mac_inout p p') Y).

  Definition unravel_macro (p: prog) (m: macro):= 
    match m with | vpi w p' inputs => <{
      <[ B (lab_index (max_lab p) + 2) ] w ← 0 > ;
      total_var_clear (make_compatible p p') (lab_index (max_lab p) + 3);
      in_allocations (rev inputs) (mac_inout p p') (lab_index (max_lab p)+3) w;
      make_compatible p p';
      var_transmit 
        (C (lab_index (max_lab p) + 2))
        (D (lab_index (max_lab p) + 2))
        (E (lab_index (max_lab p) + 2))
        (max_Z_var p) w (loc_Y p p')
      }>
    end.
    (* the shifted E 0 of the localized program can be E (lab_index (max_lab p) or E (lab_index (max_lab p)+1 tops. And because of the previously mentioned gap, (max_Z_var p) remained fresh thus it's used without confliction *)
  

  (* some examples *)
    (* begin hide*)
      Example unravel_macro_test1: unravel_macro <{
        [    A 1    ] X 0 → A 3;
        [    B 0    ] Z 3 → E 0
      }> (vpi (Z 1) <{
          [    C 2    ] Y ++;
          [(** $ \I$*)] X 0 → E 2
        }> [X 0] ) = <{
        <[B 3] Z 1 ← 0>;
        <[B 4] Z 6 ← 0>;
        <[B 5] Z 5 ← 0>;
        <[B 6] Z 6 ← 0>;
        var_transmit (C 4) (D 4) (E 4) (Z 1) (Z 5) (X 0);
        [    A 2    ] Z 6 ++;
        [(** $ \I$*)] Z 5 → E 2;
        [    E 2    ] skip (Z 6);
        var_transmit (C 3) (D 3) (E 3) (Z 4) (Z 1) (Z 6) 
      }>.
      Proof. reflexivity. Qed. 
    (* end hide*)
  (*  *)

(** * Using macros in practice *)
  (** Macro lines are of the form [w ← P(v1,v2,...,vk)]. Currently, we formalized what such a line means in the middle of a program, but we still need to tell coq how to distinguish this lines from the original lines of a real program and then recursively unravel and insert them. To facilitate this process, we stipulate that no unlabeled [skip v] instruction should be used in the main program and the programs in macros (Clearly this is not an actual limitation). This is because the implemented functions to recognize macros, tactically replace them with the commands of the forbidden form while extracting them, so that later on find their place. For example, observe the following function which extracts the lines prior to a presumably separated macro:*)

  Fixpoint past_macro (p: prog) (w: var):=
    match p with 
    | nil => nil  (** (won't happen in practice)*)

    | __s (skip w) ::p' =>  match past_macro p' w with 
        | nil => p' 
        | _ => past_macro p' w 
        end
    | _ :: p' => past_macro p' w 
    end.
      
  (** And the following function, uses [past_macro], once in order and once reversely before and after unraveling the macro, so reconstruct the whole concrete program: *)

  Definition ins_mac (p: prog) (m: macro):= 
    match m with 
    | vpi w _ _ => (rev (past_macro (rev p) w) ++ (unravel_macro p m) ++ past_macro p w)
    end.

  (* Some examples *)
    (* begin hide*)
    Example insert_macros_test1 : ins_mac <{
      [    A 1    ] X 0 → A 3;
      [(** $ \I$*)] skip (Z 1); 
      [    B 0    ] Z 3 → E 0
    }> (vpi (Z 1) <{
        [    C 2    ] Y ++;
        [(** $ \I$*)] X 0 → E 2
      }> [X 0]) = <{
        [    A 1    ] X 0 → A 3;
        <[B 3] Z 1 ← 0>;
        <[B 4] Z 6 ← 0>;
        <[B 5] Z 5 ← 0>;
        <[B 6] Z 6 ← 0>;
        var_transmit (C 4) (D 4) (E 4) (Z 1) (Z 5) (X 0);
        [    A 2    ] Z 6 ++;
        [(** $ \I$*)] Z 5 → E 2;
        [    E 2    ] skip (Z 6);
        var_transmit (C 3) (D 3) (E 3) (Z 4) (Z 1) (Z 6);
        [    B 0    ] Z 3 → E 0
      }>.
    Proof. reflexivity. Qed. 
  (* end hide*)

(* formulateing macro lines W ← P (V1,V2,...Vl) *)

    (** Now the function [ins_mac] can be easily generalized to do the same on a list of macros. Furthermore, given a list of instructions containing some macros, it's easy to extract them one by one and then insert their concrete, compatible form to build up a concrete program. We omit the details of such implementation and end this chapter with a real usage of macros in practice: *)
   
    (* begin hide*)

    Fixpoint insert_macros (p: prog) (mlm: list macro):= 
      match mlm with 
      | nil => p 
      | m::lm => insert_macros (ins_mac p m) lm
      end.

    Notation " v ←< p > l ":= (vpi v p l) (in custom SProg at level 100).
    Notation "←( v , .. , v' ) ":= (cons (v: var) .. (cons (v': var) nil)..)(in custom SProg at level 60).
    (* Check <{ Z 0 ←< addition2 >←( Z 3 , X 1 ) }>. *)

    Inductive prog_macros:= | p_ml (p: prog) (l: list macro).
    Definition prog_ (pml:prog_macros) := match pml with p_ml p _ => p end.
    Definition _macros (pml:prog_macros) := match pml with p_ml _ ml => ml end.

    Inductive mac_or_singleprog:= | is_mac (vpi: macro) | is_insp (ip: prog).
   
    Definition extract_macros (p_m: prog_macros) (mc_ip:mac_or_singleprog) :=
      match mc_ip with
        | is_insp ip => match p_m with | p_ml p l => p_ml (ip ++ p) l end
        | is_mac (vpi v p' i) => match p_m with 
          | p_ml p l => p_ml (<{[ ] skip v}> :: p) ((vpi v p' i)::l)
          end
      end.

    Coercion is_mac: macro>->mac_or_singleprog.
    Coercion is_insp: prog>->mac_or_singleprog.

    Notation "{{ i , .. , j }}" := 
      (extract_macros  .. ( extract_macros (p_ml nil nil) i ) .. j )
      (in custom SProg at level 53). 

    Notation "<< pml >>":= (insert_macros (prog_ pml) (_macros pml)) (at level 60).

    (* Some examples *)
      (* Check <{ [ ] Y ++  }>.
      Compute  <<<{{{ [ ] Y ++ , [ A 0 ] Y → A 0 , [ A 0 ] Y ++  }}}>>>. *)
    (* end hide*)

    Definition multiplication2:= <<<{{{
      [    A 0   ] X 0 → A 1,
      [(** $\I$*)] Z 0 ++,
      [(** $\I$*)] Z 0 → E 0,
      [    A 1   ] X 0 --,
      (Z 1) ←<addition2>←( Z 3, X 1),
      var_transmit (B 1) (C 1) (D 1) (Z 2) (Y) (Z 1),
      [(** $\I$*)] Z 0 ++,
      [(** $\I$*)] Z 0 → A 0
    }}}>>>.

    (** I discourage you to evaluate the program by asserting examples and using
    [Proof. reflexivity. Qed.]. It takes [Coq] at least seven minutes to unravel and test it even on small inputs! Instead, use the [Compute] command like as below. After recognizing the program in a few seconds, you can evaluate it on different inputs immediately. *)
  
    (* Example multiplication1_test1:
      (<1>--[5;0;3;0]) →<{ multiplication1 | × 655}> = 15.
    Proof. reflexivity. Qed.*)

    Compute (<1>--[5;0;3;0]) →<{ multiplication2 | × 655}>. 

(** %  
    \bibliographystyle{plain}
    \bibliography{references}
    % *) 