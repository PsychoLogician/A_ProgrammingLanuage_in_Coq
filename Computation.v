(* coqc BasicDefinitions.v *)

(* begin hide*)
  Require Export BasicDefinitions.
  From Coq Require Import Init.Nat.
  From Coq Require Import Arith.PeanoNat.
  From Coq Require Import Lia.
  From Coq Require Import Lists.List. Import ListNotations.
(* end hide*)

(** %\chapter{Computation of a Program}%  *)

(** * Updating and storing information  *)
  (** To use programs for computation, we have to store the values of variables after executing each instruction. Thus we use a list of numbers called [state]. *)

  Definition state:= list nat.

  (* value of a variable *)    
    (* begin hide*)
      (* i=1 gives the head, i=length gives the last element. if i is out of range, 0 should be returned. *)  
      Fixpoint reverese_ith_val (i: nat) (s: state):=
        match s with
        | nil => 0
        | cons h t => match i with 
          | 0 => 0
          | 1 => h
          | S j => reverese_ith_val j t
          end
        end.
      (* i = 0 gives the smallest variable, i.e. Y. If i is out of range, 0 should be returned. *)
      Definition ith_val (i: nat) (s: state):= reverese_ith_val (length s - i) s.
      Definition state_var (s: state) (v: var):= ith_val (code_var v) s.
    (* end hide*)

    (** The [state_var] function simply shows the value of a variable in a state based on its code and regards the last value's index as 0 (thus representing the output) and the head represents the value of the greatest variable regarding its code. Also, we assume that the default value of all variables is 0, especially those that are not represented in the state.*)

    (* Some examples *)
      Example state_var_test1 : state_var [1;2;3;4;5] Y  = 5 . 
      Proof. reflexivity. Qed. 
      Example state_var_test2 : state_var [1;2;3;4;5] (Z 1) = 1 . 
      Proof. reflexivity. Qed. 
      Example state_var_test3 : state_var [1;2;3;4;5] (X 2) = 0 . 
      Proof. reflexivity. Qed. 
      Example state_var_test4 : state_var nil Y = 0 . 
      Proof. reflexivity. Qed. 
    (*  *)
  (*  *)

  (* updating an state + its soundness*)
    (* begin hide*)
    
    (* reverse_ith_update_state + its soundness *)
      (* i = 1 changes the head, i = length changes the last*)
      Fixpoint reverse_ith_update_state (i: nat) (n: nat) (s: state):=
        match s with 
        | nil => nil
        | cons h s' => match i with 
          | 0 => cons h s' (*won't happen in practice*)
          | 1 => cons n s'
          | S j => cons h (reverse_ith_update_state j n s')
          end
        end.

      Lemma reverse_ith_update_state_preserves_length: forall s i n, 
        length (reverse_ith_update_state i n s) = length s.
      Proof. induction s.
        - destruct i; destruct n; reflexivity.
        (* for the step, first we shall prove the trivial following: *)
        - assert (forall l, forall n: nat, length (n::l) = S (length l)). {intros; simpl; reflexivity. }
        destruct i as [|j]; destruct n as [|m]; try reflexivity; simpl; destruct j; try reflexivity.
          (* n = 0 *)
          + rewrite (H (reverse_ith_update_state (S j) 0 s) a). rewrite (IHs (S j) 0). reflexivity.
          (* n = S m *)
          + rewrite (H (reverse_ith_update_state (S j) (S m) s) a). rewrite (IHs (S j) (S m)). reflexivity.
      Qed.

      Definition in_range (i:nat) (s:state) := (0 <? i = true) /\ (i <=? length s = true).

      Lemma reverse_ith_update_state_step: forall s: state, forall i n a: nat, 
        in_range i s ->
        (reverse_ith_update_state (S i) n (a::s)) = (a:: reverse_ith_update_state i n s).
        
      Proof. intros. destruct i. + destruct H. discriminate. + reflexivity. Qed.

      Lemma  reverese_ith_val_step: forall s, forall i a, 
        in_range i s ->
        reverese_ith_val (S i) (a :: s) = reverese_ith_val i s .
      Proof. intros. destruct i. + destruct H; discriminate. + reflexivity. Qed.

      Lemma reverse_reverse_ith_update_state_updates: forall s, forall i n: nat, 
        in_range i s -> 
        reverese_ith_val i (reverse_ith_update_state i n s) = n.

      Proof. induction s.
        (* in basis case, in_range i s is refutable *)
        - intros; destruct H as [co nt]; simpl in nt. destruct i; discriminate. 
        (* step *)
        - induction i as [|j]; destruct n as [|m];
            try (intro cont; destruct cont; discriminate);
            intro H; destruct H as [naive sup]; destruct j as [|k];
              try (simpl; reflexivity);
              replace (S (S k) <=? length (a:: s)) with (S k <=? length s) in sup;
                try rewrite reverse_ith_update_state_step; try rewrite reverese_ith_val_step; try rewrite IHs;
                  try reflexivity;
                  apply conj;
                    try reflexivity; try assumption;
                    rewrite reverse_ith_update_state_preserves_length; assumption.
      Qed.
      
      Lemma reverse_ith_update_state_updates: forall s, forall i n, 
      in_range (length s - i) s -> 
      ith_val i (reverse_ith_update_state (length s - i) n s) = n.

      Proof. intros. unfold ith_val.
        rewrite reverse_ith_update_state_preserves_length.
        rewrite reverse_reverse_ith_update_state_updates.
        reflexivity. assumption.
      Qed.

      (* For the future... *)
        (* Lemma reverse_ith_update_state_no_interruption: forall s, forall j i n: nat, 
        in_range i s -> in_range j s -> i =? j = false ->
        ith_val j (reverse_ith_update_state i n s) = ith_val j s. *)
      (*  *)

    (*  *)

    (* ith_insert_state + its soundness *)
      (* i = k insterts k new 0's then n *)
      Fixpoint ith_insert_state (i: nat) (n: nat) (s: state):=
        match i with 
        | 0 => cons n s
        | S j => ith_insert_state j n (cons 0 s)
        end.
      
      Lemma ith_insert_state_form: forall i n: nat,  forall s, 
      exists s',
      ith_insert_state i n s = n::s' /\ length s' = length s + i.
      Proof. induction i.
        - intros. simpl. exists s. apply conj. + reflexivity. + lia.
        - intros. simpl. destruct (IHi n (0::s)) as [s''].
          exists s''. destruct H as [ H length]. apply conj.
            + assumption. + rewrite length. simpl. lia.  
      Qed.  

      Lemma length_val_head: forall s a, ith_val (length s) (a::s) = a.
      Proof. unfold ith_val. intros. 
        replace (length (a::s) - length s) with 1.
        reflexivity. simpl (length (a::s)). lia. 
      Qed.

      Lemma ith_insert_state_updates: forall i n s, 
        (length s <=? i) = true ->
        ith_val i (ith_insert_state (i - length s) n s) = n.
      Proof. induction i.
        - simpl. destruct s.
          + simpl. reflexivity. 
          + intros. discriminate.
        - intros n s len_bound. 
          assert (exists s', ith_insert_state (S i - length s) n s = n::s' /\ length s' = 1+i) as H. { replace (1+i) with (length s + (S i - length s)).
          apply ith_insert_state_form. apply Nat.leb_le in len_bound. lia. }
          destruct H as [s' [form len]]. rewrite form. simpl in len. rewrite <- len. apply length_val_head.
      Qed.

      (* For the future... *)
        (* Lemma ith_insert_state_no_interruption: forall i j n s, 
        (length s <=? i) = true -> (i =? j = false) ->
        ith_val j (ith_insert_state (i - length s) n s) = ith_val j s. *)
      (*  *)

    (*  *)
    
    (* Combining two previous definitions, we can define a function that updates the values of variables in a state. *)
    Definition var_update_state (v: var) (n: nat) (s: state):= 
      if code_var v <? length s
        then reverse_ith_update_state (length s - code_var v) n s
        else ith_insert_state ((code_var v) - length s) n s.

    (* end hide*)

    (** Next we have the [var_update_state] function which updates the value of a variable in a state as desired. As we mentioned before, the default value of all variables is 0, thus if this variable is not seen in the state yet, first the value of all hidden variables (0) between this variable and the head of the state should emerge. The following examples clarify this matter:*)

    (* Some examples *)
      Example var_update_state_test1: var_update_state Y 5 nil = [5]. 
      Proof. reflexivity. Qed. 
      
      Example var_update_state_test2 : var_update_state (X 2) 3 nil = [3;0;0;0;0;0]. 
      Proof. reflexivity. Qed. (** %\pagebreak% *)

      Example var_update_state_test3 :
      var_update_state (Z 1) 4 (var_update_state (X 2) 3 nil) = [3;4;0;0;0;0].
      Proof. reflexivity. Qed. 

      Example var_update_state_test4 :
      var_update_state (X 2) 4 (var_update_state (X 2) 3 nil) = [4;0;0;0;0;0].
      Proof. reflexivity. Qed. 
    (*  *)

    (** The theorem below states that the implemented algorithm for updating the value of a variable in a state, actually does this task.*)

    Theorem var_update_state_updates: forall v: var, forall s: state, forall n: nat,
      state_var (var_update_state v n s) v = n.
    (* begin hide*)
    Proof. intros. 
      unfold var_update_state. destruct (code_var v <? length s) eqn: E.
        - unfold state_var. rewrite reverse_ith_update_state_updates. reflexivity.
          apply conj. 
          + apply Nat.ltb_lt. apply Nat.ltb_lt in E. lia. 
          + apply Nat.leb_le. apply Nat.leb_le in E. lia.
        - unfold state_var. apply ith_insert_state_updates. apply Nat.leb_le.
          apply Nat.ltb_nlt in E. lia.
    Qed.
    (* For the future... *)
      (* Theorem var_update_state_no_interruption: 
        forall v v': var, forall s: state, forall n: nat,
        eq_var v v' = false -> state_var (var_update_state v n s) v' = state_var s v'.
      Proof.  Abort. *)
    (* end hide*)

    (** The proof of the theorem uses some lemmas about the details of the implementation, which are rather tedious, thus we won't mention them here.*)
  (*  *)
(*  *)

(** * The evaluation procedure *)
  (** Based on the possible instructions in a program, we can update a state only in the two following manner: *)

  Definition var_increment_state (v: var) (s: state):=
    var_update_state v (S (state_var s v )) s.

  Definition var_decrement_state (v: var) (s: state):=
    var_update_state v ((state_var s v ) - 1) s.

  (** Soundness of these two functions immediately follows from [var_update_state_updates]:*)

  Theorem var_increment_state_increments: forall v: var, forall s: state,
    state_var (var_increment_state v s) v = S (state_var s v).

  Proof. intros. unfold var_increment_state. rewrite var_update_state_updates. lia.
  Qed.

  Theorem var_decrement_state_decrements: forall v: var, forall s: state,
    state_var (var_decrement_state v s) v = (state_var s v) -1.
  Proof. intros. unfold var_decrement_state. rewrite var_update_state_updates. lia.
  Qed.

  (** Now we shall define the effect of a statement on a state: *)

  (* effect of a statement on a state *)
    Definition statement_on_state (st: statement) (s: state):= 
      match st with
      | inc v => var_increment_state v s
      | dec v => var_decrement_state v s
      | _ => s
      end.

    (** %\pagebreak% Here is an example: *)

      Example statement_on_state_test1 :
        statement_on_state (<{(Z 0) ++}>) nil = [1;0;0].
      Proof. reflexivity. Qed.

      (* Example statement_on_state_test1 : nil --<{(Z 0) ++}>→  = [1;0;0].
      Proof. reflexivity. Qed.  *)
  (*  *)

  (** The next step is to formalize the notion of commuting between the instructions (lines) of a program. Thus in addition to the state, we store the number of the line of the current instruction and call this pair an [snapshot]:*)
  
  (* snapshot *)
    Inductive snapshot:= | line_state (i: nat) (s: state).

    Definition line_ (ls: snapshot):= match ls with | line_state i s => i end.

    Definition _state (ls: snapshot):= match ls with | line_state i s => s end.

    Notation " < l >-- s ":= (line_state l s) (at level 200).

    (** Regarding a program, we call any snapshot with a line number equal to [length p + 1] a terminal snapshot.*)

    Definition terminal_snap (p: prog) (sn: snapshot):= line_ sn =? length p + 1.

  (*  *)

  (* Finding a line with a desired label in a given program *)
    (* start from 1 not 0. There is no correct instruction where i is outside of the range, and the default garbage is [ ] skip Y *)
    
    (* begin hide*)        

    Definition ith_ins_prog (i: nat) (p: prog):= nth ((length p) - i) p (__s (skip Y)).

    (* example *)
      Example ith_ins_prog_test1 : ith_ins_prog 3 (<{
        [     ] Y++;
        [     ] Z 0 --;
        [ A 0 ] Z 0 → A 0;
        [     ] skip ( X 0)   
      }>) = <{[ A 0 ] Z 0 → A 0}>.
      Proof. reflexivity. Qed. 
    (*  *)

    Fixpoint general_line_finder (default: nat) (index: nat) (l: lab) (p: prog):=
      match p with
      | nil => default
      | (__s s)::p'  => general_line_finder default (index -1) l p'
      | (l_s l' s)::p'  => if eq_lab l l' 
        then min (general_line_finder default (index-1) l p') (index)
        else general_line_finder default (index -1) l p'
      end. (** %\footnote{[eq_lab] simply checks the equality of two labels.}% *)

    (* search for the first line labeled with a given label in the program.
      output (length p) + 1 if fails. *)
    Definition line_finder (l: lab) (p: prog):=
      general_line_finder 
        ((length p) + 1) ((length p)) l p.
    
    (* Some examples *)
      Example line_finder_test1: line_finder (A 0) nil = 1. 
      Proof. reflexivity. Qed. 
    
      Example line_finder_test2 : line_finder (A 0) (<{
        [     ] Y++;
        [     ] Z 0 --;
        [ A 0 ] Z 0 → A 0;
        [     ] skip ( X 0)   
      }>) = 3.
      Proof. reflexivity. Qed. 
    (*  *)
    (* end hide*)

    (* iterations *)
      (** The mechanism of computing the [successor] of a [non-terminal snapshot] namely %\\%[<i>--s] by a program is as follows: 
        - case 1) If the ith instruction is increment, decrement or skip a variable, then do the corresponding statement on [s] and increase [i] by 1.
        - case 2) If the ith instruction is a conditional for the variable [v] and label [l], then 
          - 2a) If the value of [v] is 0 in [s], then only increase [i] by 1.
          - 2b) If the value of [v] is not 0 in [s], then find the first line in the program labeled [l] and replace [i]  with its line number. If there is no such label, replace [i] with %\\% [length p + 1].

      The successor of a [terminal snapshot] is assumed to be itself. %\pagebreak%
      *)

      Definition successor_sn (sn: snapshot) (p: prog):=
        if (length p) <? line_ sn
          then sn
          else line_state 
              (** [//] $ line\,\, after\,\, one\,\, iteration $*)

                  (match (_s (ith_ins_prog (line_ sn) p)) with
                  | cond v l => match state_var (_state sn) v with
                    | 0 => (line_ sn) + 1
                    | _ => line_finder l p
                    end
                  | _ => (line_ sn) + 1
                  end)
              (** [//] $ state\,\, after\,\, one\,\, iteration $*)

                  (statement_on_state
                    (_s (ith_ins_prog (line_ sn) p))
                    (_state sn)).

      (** The following function repeats this procedure for arbitrarily [n] number of times: *)

      Fixpoint n_iteration (sn: snapshot) (p: prog) (n: nat):=
        match n with 
        | 0 => sn
        | S k => successor_sn (n_iteration sn p k) p
        end.

      (* Notation "s --<{ p }>→ ":= (successor_sn s p) (at level 40, left associativity). *)
      Notation "s →<{ p | × n } ":= (n_iteration s p n) (at level 50, left associativity).
      Notation "s →<{ p | × n }> " :=
        (ith_val 0 (_state (n_iteration s p n))) (at level 50).

      (** Recall the [var_clear] program:
        [    l   ] v --;
        [(** $\J$*)] v → l 
      The following examples show how an instantiation of this program reduces the value of some variable and then terminates, step by step: *)

        Example successor_sn_test0:
          (<1>--[2;0]) →<{ <{<[A 0] X 0 ← 0>}> | × 0 }= <1>--[2;0]. 
        Proof. reflexivity. Qed. 
        Example successor_sn_test1:
          (<1>--[2;0]) →<{ <{<[A 0] X 0 ← 0>}> | × 1 }= <2>--[1;0]. 
        Proof. reflexivity. Qed. 
        Example successor_sn_test2:
          (<2>--[1;0]) →<{ <{<[A 0] X 0 ← 0>}> | × 1 }= <1>--[1;0]. 
        Proof. reflexivity. Qed. 
        Example successor_sn_test3: 
          (<1>--[1;0]) →<{ <{<[A 0] X 0 ← 0>}> | × 1 }= <2>--[0;0]. 
        Proof. reflexivity. Qed. 
        Example successor_sn_test4:
          (<2>--[0;0]) →<{ <{<[A 0] X 0 ← 0>}> | × 1 }= <3>--[0;0]. 
        Proof. reflexivity. Qed. 
        Example successor_sn_test5:
          (<3>--[0;0]) →<{<{ <[A 0] X 0 ← 0>}> | × 1 }= <3>--[0;0]. 
        Proof. reflexivity. Qed.

      (** Or simply we can compute:  *)
      
        Example n_iteration_test1 :
          (<1>--[2;0]) →<{ <{<[A 0] X 0 ← 0>}> | × 5 }>= 0.
        Proof. reflexivity. Qed.

      (** Another example is to test the [addition2] on some examples: *)

        Example length_of_addition2: (length addition2) = 22.
        Proof. reflexivity. Qed.

        Example n_iteration_addition2_test1 :
          (<1>--[5;0;3;0]) →<{ addition2 | × 60 }= <23>--[5;0;3;8].
        Proof. reflexivity. Qed.

      (** The value of all variables is as desired, and the line number is correctly 23 which shows the program has been terminated. *)

    (*  *)

(** * Computation and related notions *)
  (** A computation of a program is a list of snapshots, each of them (except the first one) being the successor of the previous one and the last one being a terminal snapshot: *)
    
    Definition head_snap (snl: list snapshot):=
      match snl with
      | nil => <0>--nil (** (can't be the successor of any snapshot)*)

      | cons sn l => sn 
      end.

    Inductive computation : prog -> list snapshot -> Prop :=
      | emp_comp (p: prog): computation p nil 
      | final_comp (p: prog) (sn: snapshot): 
        (terminal_snap p sn = true) -> computation p [sn]
      | body_comp (p: prog) (sn: snapshot ) (sl: list snapshot): 
        computation p sl -> sn →<{p |× 1}= (head_snap sl)
        -> computation p (sn::sl).

  (** The [halt] predicate is expressed as follows: *)

    Definition halt (p: prog) (s: snapshot):= exists n: nat,
      terminal_snap p (n_iteration s p n) = true.

    Check option nat.
    (* Is this the reason that coq forgets n in exists!? *)
    Definition final_result (p: prog) (sn : snapshot) :option nat:=
      if exists n: nat, terminal_snap p (n_iteration sn p n) = true then 
       (sn →<{p |× n }>)
      else 0 .
 
  (** %\pagebreak% We call two programs [a_equal] if their effect is the same on any snapshot. *)

    Definition a_equal (p p':prog) := forall s:snapshot, 
      successor_sn s p = successor_sn s p'.

  (** For example, any program is [a_equal] to the result of renaming of its labels (but not vice versa). However this doesn't hold for the renaming of variables. We'll use these renamings in the next chapter while formalizing macros. *)
  (*  *)