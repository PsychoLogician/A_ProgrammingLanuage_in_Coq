Require Export Computation.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Definition bigger_var (v: var) (v': var):=
  if code_var v <? code_var v' then v' else v.

Definition lower_var (v: var) (v': var):=
if code_var v <? code_var v' then v else v'.

(* discriminate labels and instructions *)
  (* extract labels of a prog as a list (repeatation might occur)*)
  Fixpoint lines_lab(p:prog) :=
    match p with 
    | nil => nil
    | (l_s l s):: p' => l::(lines_lab p') 
    | (__s s)::p' => lines_lab p'
    end.
(*  *)

(* extract variables of a prog as a list (repeatatoin might occur)*)
  Definition v_ (s: statement):=
    match s with | inc v => v | dec v => v | skip v => v | cond v _ => v end.

  Fixpoint prog_var(p:prog) :=
    match p with 
    | nil => nil
    | (l_s l s):: p' => (v_ s) :: (prog_var p')
    | (__s s)::p' => (v_ s) :: (prog_var p')
    end.

  (* Some examples *)
    Example lines_lab_test1 : lines_lab 
      <{
        [ A 0 ] (skip Y);
        [     ] Y++
      }>
      = (A 0):: nil.
    Proof. reflexivity. Qed.

    Example lines_lab_test2 : lines_lab 
      <{
        [ ] (skip Y)
      }>
      =  nil.
    Proof. reflexivity. Qed.

    Example prog_var_test1 : prog_var
      <{
        [ A 0 ] Y -- 
      }>
      = Y :: nil.
    Proof. reflexivity. Qed.
(*  *)

(* extract maximum label 
  (first label greater than all labels in a program )*)
    
  Fixpoint max_lab_list(l: list lab):=
    match l with
    | nil => A 0
    | L::l'=> if code_lab (max_lab_list l') <=? code_lab L 
      then next_lab L
      else max_lab_list l'
    end.
  Definition max_lab (p: prog):= max_lab_list (lines_lab p).

  (* Some examples *) 
    Example  max_lab_test2 : max_lab
    <{
      [ A 0 ] Z 3 ++;
      [ E 0 ] Y -- 
    }> = A 1. 
    Proof. reflexivity. Qed. 
  (*  *)

  Lemma next_code_lab_suc: forall l, S (code_lab l) = code_lab (next_lab l).
  Proof. destruct l; simpl; lia. Qed.

  (* to prove in the future if necessary. *)
  Lemma max_lab_is_upperbound: forall p: prog, forall l: lab, 
    In l (lines_lab p) -> (code_lab l <? code_lab (max_lab p)) = true.
  Proof. induction p as [|i p]; intro l.
    - intros contra; destruct contra.
    - intro H. simpl in H. destruct i. destruct H. 
      + subst. unfold "<?". rewrite next_code_lab_suc. unfold max_lab. simpl. 
        destruct (code_lab (max_lab_list (lines_lab p)) <=? code_lab l) eqn:E.
        * apply Nat.leb_refl.
        * apply Nat.leb_le. apply Nat.leb_nle in E. rewrite <- next_code_lab_suc.
        lia.
      + apply IHp in H. unfold max_lab. simpl. apply Nat.ltb_lt in H.
        destruct (code_lab (max_lab_list (lines_lab p)) <=? code_lab l0) eqn:E.
        * apply Nat.leb_le. apply Nat.leb_le in E. rewrite <- next_code_lab_suc. 
        (* the rest shouldn't be hard *)
        Abort.
(*  *)

(* extract maximum variable
  (first variable which is greater than all variables in a program) *)

  Fixpoint max_var_list (l:list var) := 
    match l with
    | nil => Y
    | v::l' => if code_var (max_var_list l') <=? code_var v
      then next_var v
      else max_var_list l'
    end.
  Definition max_var (p: prog):= max_var_list (prog_var p).

  (* Some examples *) 
    Example  max_var_test2 : max_var
    <{
    [ ] Y++;
    [ ] Z 4 --
    }> = X 5. 
    Proof. reflexivity. Qed. 
  (*  *)

  Lemma max_var_is_upperbound: forall p: prog, forall v: var, 
    In v (prog_var p) -> (code_var v <? code_var (max_var p)) = true.
  Proof. (* similar to max_lab_is_upperbound *) Abort.
(*  *)

(* substituing variables *)
  Definition subst_var_statement (s: statement) (v: var) (v': var):= 
    match s with 
    | inc v'' => if eq_var v'' v then inc v' else s
    | dec v'' => if eq_var v'' v then dec v' else s
    | skip v'' => if eq_var v'' v then skip v' else s
    | cond v'' l => if eq_var v'' v then cond v' l else s
    end.

  Fixpoint subst_var (p:prog) (v:var) (v':var):=
    match p with 
    | nil => p
    | (l_s l s)::p' => 
      (l_s l (subst_var_statement s v v'))::(subst_var p' v v')
    | (__s s)::p' => 
      (__s (subst_var_statement s v v'))::(subst_var p' v v')
    end.

  (* some examples *)
    Example subst_var_test1: subst_var nil (Z 2) Y  = nil. 
    Proof. reflexivity. Qed. 

    Example subst_var_test2 : subst_var (<{
      [ ] X 0 → A 0 
      }>) (X 0) (Z 10) = (<{
        [ ] Z 10 → A 0 
      }>). 
    Proof. reflexivity. Qed. 

    Example subst_var_test3 : subst_var (<{
      [     ] X 0 → A 0 ;
      [     ] Z 3 ++ ;
      [ A 0 ] skip Y ;
      [     ] X 0 ++
      }>) (X 0) Y = 
      <{
        [     ] Y → A 0 ;
        [     ] Z 3 ++ ;
        [ A 0 ] skip Y ;
        [     ] Y ++
      }>.
    Proof. reflexivity. Qed. 
(*  *)

(* substituing labels *)
  Definition subst_lab_statement (s: statement) (l: lab) (l': lab):= 
    match s with 
    | cond v l'' => if eq_lab l'' l then cond v l' else s
    | _ => s
    end.

  (* change all labels (even in statements) equal to a specified label 
    to another specified label *)
  Fixpoint subst_lab (p: prog) (l: lab) (l':lab):=
    match p with 
    | nil => p
    | (l_s l'' s) :: p'=> if eq_lab l'' l then
      (l_s l' (subst_lab_statement s l l')) :: (subst_lab p' l l')
      else 
      (l_s l'' (subst_lab_statement s l l')) :: (subst_lab p' l l')
    | (__s s)::p' => (__s (subst_lab_statement s l l')):: (subst_lab p' l l')
    end.

  (* some examples *)
  Example subst_lab_test1 : subst_lab (<{
    [ A 0 ] Y++ ;
    [     ] Z 0 -- 
    }>) (A 0) (B 3)= <{
      [ B 3 ] Y++ ;
      [     ] Z 0 -- 
    }>. 
  Proof. reflexivity. Qed. 
(*  *)

(* Shifting variables and labels (renaming)*)
(* shift all variables *)

  (* given an upper_bound "max" and a "shift" value, all variable
    with code i<max are replaced with the var with the code i+shift*)
  Fixpoint general_var_shift (p: prog) (max: nat) (shift: nat):= 
    match max with
    | 0 => p 
    | S i => general_var_shift 
              (subst_var p (decode_var i) (decode_var (i + shift)))
              i
              shift
    end.

  (* shift all variables of a program *)
  Definition var_shift (p: prog) (shift: nat):= 
    general_var_shift (p) (code_var (max_var p)) (shift).

  (* Example *)
    Example var_shift_test1 : var_shift (
      <{
       [  ] Y ++ ;
       [  ] Z 0 -- ;
       [  ] skip (X 2) 
      }> 
      ) 4 =  <{
        [  ] Z 1 ++ ;
        [  ] Z 2 -- ;
        [  ] skip (X 4) 
      }>  . 
    Proof. reflexivity. Qed. 
  (*  *)

(* shift all labels *)

  (* given an upper_bound "max" and a "shift" value, all labels
    with code i<max are replaced with the lab having the code i+shift*)
  Fixpoint general_lab_shift (p: prog) (max: nat) (shift: nat):= 
    match max with
    | 0 => p 
    | S i => general_lab_shift 
            (subst_lab p (decode_lab i) (decode_lab (i + shift)))
            i
            shift
    end.

  Definition lab_shift (p: prog) (shift: nat):= 
    general_lab_shift (p) (code_lab (max_lab p)) (shift). 

  (* Example *)
    Example lab_shift_test1 : lab_shift (
      <{
       [ A 0 ] Y ++ ;
       [ B 1 ] Y -- ;
       [     ] Y → A 0 ;
       [ E 5 ] Y --
      }>
    ) 6 = <{
      [ B 1 ] Y ++ ;
      [ C 2 ] Y -- ;
      [     ] Y → B 1 ;
      [ A 7 ] Y --
     }> . 
    Proof. reflexivity. Qed.
  (*  *)
(*  *)

(* Other definitions *)
  Fixpoint is_in_lab_list (L: lab) (l: list lab):=
    match l with 
    | nil => false 
    | cons h t => if eq_lab L h then true else is_in_lab_list L t
    end.

  Definition next_same_lab (l: lab):= 
    match l with 
    | A i => A (i+1)
    | B i => B (i+1)
    | C i => C (i+1)
    | D i => D (i+1)
    | E i => E (i+1)
  end.
(*  *)

(* working on "A" labels*)
      (* (first label of the form A i which is greater than all other labels
    of the form A i in a program ) *)
    Fixpoint max_A_lab_list(l: list lab) :=
      match l with
      | nil => A 0
      | (A i) :: l'=> if code_lab (max_A_lab_list l') <=? code_lab (A i)
        then A (i+1)
        else max_A_lab_list l'
      | _ :: l' => max_A_lab_list l'
      end.
    Definition max_A_lab (p: prog):= max_A_lab_list (lines_lab p).
(*  *)

(* working on "Z" variables *)
  Definition ins_var (i: ins):= v_ (_s i).

    (* (first var of the form Z i which is greater than all other labels
  of the form Z i in a program ) *)
  Fixpoint max_Z_var ( p:prog) :=
    match p with 
    | nil => Z 0
    | i::p' => match ins_var i with
      | Z j => bigger_var (max_Z_var p') (Z (j+1))
      | _ => max_Z_var p' 
      end 
    end.

  (* Some examples *) 
    Example max_Z_var_test1 : max_Z_var (<{
     [ (** $ \I$*) ] Y ++ ;
     [     A 0     ] Z 1 -- 
    }>) = Z 2 . 
    Proof. reflexivity. Qed. 

    Example max_Z_var_test2 : max_Z_var (<{<[ A 0 ] Y ← 0>}>) = Z 0 . 
    Proof. reflexivity. Qed.  
  (* *)

  Definition next_Z (v:var) := match v with
    | Y => Z 0 | X i => Z i | Z i => Z (i+1) end.
(*  *)

(* Shift state *)
  Fixpoint state_shift_if_updated (inout: state) (shift: nat):=
    match inout with 
    | nil => nil 
    | name::inout' => if name =? 0
      then 0:: state_shift_if_updated inout' shift
      else name+shift :: state_shift_if_updated inout' shift
    end.
(*  *)