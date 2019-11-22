From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Coq.Relations.Relation_Operators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Totality and termination *)

(** Define Ackermann's function without using
    the nested [fix] trick.
    Try several different approaches
*)

(* Fixpoint acc (n m : nat) : nat := *)
(*   if n == 0 then *)
(*     m.+1 *)
(*   else *)
(*     if (m == 0) then *)
(*       acc (n - 1) 1 *)
(*     else *)
(*       acc (n - 1) (acc n (m - 1)). *)

(* Fixpoint acc (n m: nat) {struct n} : nat := *)
(*   if n is n'.+1 then *)
(*     if m is m'.+1 then *)
(*       acc n' (acc n m') *)
(*     else *)
(*       acc n' 1 *)
(*   else m.+1. *)

Module ProgramGames.
From Coq Require Import Program.

(* Set Printing All. *)
Search _ (?n.+1 + ?m).
(* ltnS  forall m n : nat, (m < n.+1) = (m <= n) *)
(* ltn0Sn  forall n : nat, 0 < n.+1 *)
(* ltn0  forall n : nat, (n < 0) = false *)
(* ltnSn  forall n : nat, n < n.+1 *)

(* Unset Printing Notations. *)
(* Program Fixpoint acc (n m: nat) *)
(*   {measure (nat * nat) (n, m)} : nat := *)
(*   if n is n'.+1 then *)
(*     if m is m'.+1 then *)
(*       acc n' (acc n m') *)
(*     else *)
(*       acc n' 1 *)
(*   else m.+1. *)
(* Next Obligation. *)
(*   move=> /=. rewrite ?addSn.  rewrite addnS. done. *)
(* Qed. *)
(*   Next Obligation. *)


(* Qed. *)
End ProgramGames.

From Equations Require Import Equations.

Module ProgramGames2.
  Equations acc_e (n m: nat) : nat
  by wf (n,m) (Subterm.lexprod _ _ lt lt) :=
  acc_e n'.+1 m'.+1 := acc_e n' (acc_e n'.+1 m');
  acc_e n'.+1 0 := acc_e n' 1;
  acc_e 0 m := m.+1.

  Compute acc_e 0 3.
End ProgramGames2.
Check Fix_F_2.

(** Implement the [interleave] function using
   [Fix_F_2] combinator *)

Definition interleave_fix {A} (xs ys : seq A) : seq A :=
  Fix_F_2


(** Define a list sorting function using merge sort algorithm. *)




(** * Cast and John Major Equality via cast *)

From Coq Require Import Eqdep.

Section Cast.
Variable (C : Type) (interp : C -> Type).

Definition cast A B (pf : A = B) (v : interp B) : interp A :=
  ecast _ _ (esym pf) v.

(** You need to use [Streicher_K] axiom from [Eqdep] module *)
Lemma eqc A (pf : A = A) (v : interp A) : cast pf v = v.
Proof.
Admitted.

(** Heterogeneous equality via [cast] *)
Definition jmeq A B (v : interp A) (w : interp B) :=
  forall pf, v = cast pf w.

Lemma jmrefl A (v : interp A) : jmeq v v.
Proof.
Admitted.

Lemma jmsym A B (v : interp A) (w : interp B) :
  jmeq v w -> jmeq w v.
Proof.
Admitted.

Lemma jmE A (v w : interp A) : jmeq v w <-> v = w.
Proof.
Admitted.

Lemma castE A B (pf1 pf2 : A = B) (v1 v2 : interp B) :
  v1 = v2 <-> cast pf1 v1 = cast pf2 v2.
Proof.
Admitted.

End Cast.
