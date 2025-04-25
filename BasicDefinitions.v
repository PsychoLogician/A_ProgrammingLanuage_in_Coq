(* Libraries and latex commands *) 
  (* begin hide*)
  From Coq Require Import Init.Nat.
  From Coq Require Import Arith.PeanoNat.
  From Coq Require Import Lia.
  From Coq Require Import Lists.List. Import ListNotations.
  (* Module Sprogramming. *)
  (* end hide*)
  (** % \newcommand{\I}{\hspace{18.5pt}} %  *)
  (** % \newcommand{\J}{\hspace{5pt}} %  *)
(*  *)
  
(** %\chapter{A Programming Language}%  *)

(** * Defining a program *)

  (** Our development of computability theory will be based on a specific
  programming language $\mathscr{S}$. We will use certain letters as variables whose values are natural numbers. There are three kinds of variables separated by the letters Y, X and Z to represent the output, input variables and local variables. *)

  (* variables and labels *)
    Inductive var: Type:= 
      | Y | X(i:nat) | Z(i:nat).

    (** In addition to variables, there are labels that are used to commute between different instructions of a program. These labels are exhibited by certain letters and an index%\footnote{In the original reference \cite{Davis_Sigal_Weyuker_2003}, all indices for variables and labels start from 1 not 0. But since $nat$ is a more canonical choice for our formalization, we preferred to start from 0.}%. The purpose of this separation is only to facilitate programming in practice. *)

    Inductive lab: Type:=
      | A(i:nat) | B(i:nat) | C(i:nat) | D(i:nat) | E(i:nat).
  (*  *)

  (* statements and instructions *)
    (** Combining variables and labels, there are four different kinds of statements: 
     - incrementing the value of a specified variable
     - decrementing the value of a specified variable (if it's 0 no changes happen)
     - simply do nothing to a specified variable
     - if the value of a specified variable is not 0 then go to the first statement which is labeled as specified (this statement will be clarified after defining programs) *)
    Inductive statement: Type:=
      | inc(v:var) | dec(v:var) | skip(v:var) | cond(v:var)(l: lab). 

    (** We label statements and call them instructions. It's also possible to leave some statements unlabeled but use them as instructions for a program. *)

    Inductive ins: Type:= 
      | l_s (l: lab)(s: statement) 
      | __s (s: statement).

    (* begin hide *)
      Definition _s (i: ins):= match i with | l_s l s => s | __s  s => s end.
    (* end hide*)
  (*  *)

  (** A program is simply a list of instructions. *)

    Definition prog: Type:= list ins.

  (** In the next chapter, we see how a program is assumed to work in some examples. Then we formally define the computation of a program in Chapter 2. *)

(*  *) 
  
(** * Examples of programs *) 
  (* Notations *)
    (** Before beginning to write programs, we introduce the following notations:
      - [v ++] is used for [inc v] 
      - [v --] is used for [dec v] 
      - [v -> l] is used for [cond v l] *)
    (* begin hide*)

    Declare Custom Entry SProg.
    Declare Scope SProg_scope.
    Declare Custom Entry SProg_aux.
    From Coq Require Import Lists.List. Import ListNotations.

    Notation "<{ e }>" := e (e custom SProg_aux) : SProg_scope.
    Notation "e":= e (in custom SProg_aux at level 0, e custom SProg): SProg_scope.
    
    (* Notation "( x )" := x (in custom SProg, x at level 99) : SProg_scope. *)
    Notation "x":= x (in custom SProg at level 0, x constr at level 0): SProg_scope.

    Notation "f x .. y" := (.. (f x) .. y)
                      (in custom SProg at level 0, only parsing,
                      f constr at level 0, x constr at level 9,
                      y constr at level 9): SProg_scope.

    Notation "x ++":= (inc x) (in custom SProg at level 50).
    Notation "x --":= (dec x) (in custom SProg at level 50).
    Notation "v → l":= (cond v l) (in custom SProg at level 50).

    Notation "[ ] s":= (__s s) (in custom SProg at level 51).
    Notation "[ l ] s":= (if 1=?1 then l_s l s else l_s l s) (in custom SProg at level 51).

    Notation "<{ }>":= (@nil ins: prog) (at level 60).
    (* Notation "<{ }>" := emprog (at level 60). *)

    Definition ins_to_prog (i: ins): prog:= i::<{ }>.
    (* Definition ins_to_prog (i:ins) : prog := aprog emprog i. *)

    Coercion ins_to_prog : ins >-> prog.
    
    Notation " p ; si ":= ((si: prog)++(p: prog)) (in custom SProg at level 52, left associativity).
    (* Notation " p ; i "   := (aprog (p: prog) i) (in custom SProg at level 52, left associativity). *)

    Open Scope SProg_scope.

    (* testing notations *)
      (* Check <{ [ ] X 0 ++ }>.
      Check <{ [ ] X 0 ++ ; [ A 0 ] Y ++ ; [ ] Z 0 → A 1 }>.
      Compute <{ [ ] X 0 ++ ; <{ [ A 0 ] Y ++ ; [ ] Z 0 → A 1  }> }>.
      Check [1] ++ [2]. *)
    (* end hide*)
  (*  *)

  (* clear a variable *)
    (** The following program (more strictly, program scheme) collapses the value of some arbitrary variable [v] to 0. *)

    Definition var_clear (l:lab)(v:var):prog := 
      <{
        [    l   ] v --;
        [(** $\J$*)] v → l  
      }>.
    Notation "<[ l ] v ← 0 >":= (var_clear l v) (in custom SProg at level 100).

    (** Another useful program could do the following: "increasing the value of some variable to the addition of its current value and the value of some other program". Here is an implementation:  %\pagebreak% *)

    Definition var_transmit (l1 l2 e :lab)(z v v':var):prog := 
      <{  (** [#] If v' has the value 0 then nothing has to be done. *)

        [(** $\J\J$*)] v' → l1 ;
        [(** $\J\J$*)] z ++ ;
        [(** $\J\J$*)] z → e;
        (** [#] otherwise, the first step is to empty v' in both z and v *)

        [    l1      ] v' -- ; 
        [(** $\J\J$*)] v ++ ;
        [(** $\J\J$*)] z ++;
        [(** $\J\J$*)] v' → l1;
        (** [#] next, retrieving the value of v' from z *)

        [    l2      ] z -- ; 
        [(** $\J\J$*)] v' ++ ;
        [(** $\J\J$*)] z → l2;
        [    e      ] z --
      }>.
    (** Note that the program works correctly if the labels and variables are all distinct. *)

    (** Now we might think of instantiating [var_transmit] on [Y] and [X 0] and then concatenate it to another instantiation on [Y] and [X 1] to create a program that computes the addition function. This is a good idea, but we have to be careful about the names we choose for the other parameters, i.e. the labels and the variable [z]. A good choice is as follows: *)

    Definition addition1:prog := <{
      var_transmit (A 0) (B 0) (E 0) (Z 0) Y (X 0); 
      var_transmit (A 1) (B 1) (E 1) (Z 1) Y (X 1)
    }>.

    (** We shall mention that the value of the output and the local variables is assumed to be [0] at the beginning. Now observing what this program does in the first part, we notice that the value of [Z 0] is always 0 after termination. Thus we can reuse it for the second part and eliminate [Z 1]: *)

    Definition addition2:prog := <{
      var_transmit (A 0) (B 0) (E 0) (Z 0) Y (X 0); 
      var_transmit (A 1) (B 1) (E 1) (Z 0) Y (X 1)
    }>.

    (** Although the real extended version of the program can be simplified even more, we won't go further and continue with the current version. It's also worth mentioning that as we combined programs carefully to prevent conflict, it's possible to use any program in another one in a more general form. But it's clear that in complex examples it can be too hard to manually handle the conflictions. Therefore, we formally define a machinery to automate this process in Chapter 3.*)

(* Some basic definitions: equality and next *)
  (* begin hide*)
  Definition eq_var (v: var) (v': var):=
    match v, v' with
    | Y, Y => true
    | X i, X i' => i =? i'
    | Z i, Z i' => i =? i'
    | _ , _ => false
    end.

  Definition next_var(v:var) :=
    match v with
    | Y => X 0
    | X i => Z i 
    | Z i => X (i+1)
    end.

  Definition eq_lab (l: lab) (l':lab):=
    match l, l' with
    | A i, A j => i =? j
    | B i, B j => i =? j
    | C i, C j => i =? j
    | D i, D j => i =? j
    | E i, E j => i =? j
    | _ , _ => false
    end.
  
  Definition next_lab (l: lab):=
    match l with 
    | A i => B i
    | B i => C i
    | C i => D i
    | D i => E i
    | E i => A (i+1)
    end.
  (* end hide*)

      
(** * Coding of variable and labels *)
  (** To be able to easily manipulate variables and labels and to prove facts about them, we encode them in natural numbers and decode them whenever needed. Here is the coding and decoding of variables:*)

  (* variables *)
    Definition code_var(v: var):=
      match v with 
      | Y => 0
      | X i => 2*i+1
      | Z i => 2*i+2
      end.

    Fixpoint decode_var(n:nat):=
      match n with
      | 0 => Y
      | S i => next_var(** %\footnote{simply the next variable with regard to it's code.}% *) (decode_var i)
      end.
  (*  *)

  (** And here is the coding and decoding of labels % \footnote{In the original reference \cite{Davis_Sigal_Weyuker_2003} , coding of labels start from 1 not 0. But since $nat$ is a more canonical choice for our formalization, we preferred to start from 0.} %:*)

  (* labels *)
    Definition code_lab(l: lab):=
      match l with 
      | A i => i*5
      | B i => i*5 + 1
      | C i => i*5 + 2
      | D i => i*5 + 3
      | E i => i*5 + 4
      end.

    Fixpoint decode_lab(n:nat):=
      match n with 
      | 0 => A 0
      | S i => next_lab(** %\footnote{simply the next label with regard to it's code.}% *) (decode_lab i)
      end.
  (*  *)

  (** From now on, we use [# x] to show the coding of [x], regardless of [x] is a variable or a label.*)

  (* Notation for coding *)
    (* begin hide *)
    Inductive lab_var:=
      | varib(v:var)
      | labe(l:lab).

    Definition code_lab_var (lv:lab_var):=
      match lv with 
      | varib v => code_var v 
      | labe l => code_lab l 
      end. 

    Coercion varib : var >-> lab_var.
    Coercion labe : lab >-> lab_var.
    Notation "# x" := (code_lab_var x) (at level 30).

    (* Some examples *)
      Example code_lab_var_test1: # A 0 = 0 . Proof. reflexivity. Qed.
      Example code_lab_var_test2: # B 0 = 1 . Proof. reflexivity. Qed.
      Example code_lab_var_test3: # Y = 0. Proof. reflexivity. Qed.
      Example code_lab_var_test4: # X 0 = 1 . Proof. reflexivity. Qed. 
    (* end hide *)
  (*  *)

(* Appendix: decode O code is id *)
  (* begin hide*)
  Lemma  next_code_var_suc: forall v: var,
  code_var (next_var v) = S (code_var v).
  Proof. destruct v; simpl; lia. Qed. 
      
  Theorem var_decode_code_id: forall v: var, decode_var (code_var v) = v.
  Proof. destruct v. -reflexivity.

    - induction i. + reflexivity.  +
      assert (X (S i) = next_var (next_var (X i)) ). {
        simpl. rewrite Nat.add_comm. simpl. reflexivity.
      }
      rewrite H. repeat rewrite next_code_var_suc. simpl.
      replace ((i + (i + 0) + 1)) with (2*i + 1).
      assert (code_var (X i) = 2*i + 1). {reflexivity. }
      rewrite <- H0. rewrite IHi.
      rewrite Nat.add_comm. simpl.
      rewrite Nat.add_comm. simpl.
      reflexivity. lia.

    - induction i. + reflexivity. +
      assert (Z (S i) = next_var (next_var (Z i)) ). {
        simpl. rewrite Nat.add_comm. simpl. reflexivity.
      }
      rewrite H. repeat rewrite next_code_var_suc. simpl.
      (* replace (i + 1 + (i + 1 + 0)) with (2*i+2). *)
      replace (i + (i + 0) + 2) with (2*i+2).
      assert (code_var (Z i) = 2*i+2). { reflexivity. }
      rewrite <- H0. rewrite IHi.
      rewrite Nat.add_comm. simpl.
      rewrite Nat.add_comm. simpl.
      reflexivity. lia.      
  Qed.
(* end hide*)