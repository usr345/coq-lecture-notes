From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IntLogic.

Variables A B C : Prop.

Lemma notTrue_iff_False : (~ True) <-> False.
Proof.
  rewrite /not. split.
  - apply. done.
  - exact.
Qed.

Lemma dne_False : ~ ~ False -> False.
Proof.
  rewrite /not. apply. exact.
Qed.

Lemma dne_True : ~ ~ True -> True.
Proof.
  move=> H. apply I.
Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  move=> H. apply H. move=> H1. apply: H1. move=> a. apply: H. done.
Qed.

Lemma imp_trans : (A -> B) -> (B -> C) -> (A -> C).
Proof.
  move=> a_i_b b_i_c a. apply: b_i_c. apply: a_i_b. apply a.
Qed.

End IntLogic.


(** Let's get familiarize ourselves with some lemmas from [ssrbool] module.
    The proofs are very easy, so the lemma statements are more important here.
 *)
Section BooleanLogic.

Variables (A B : Type) (x : A) (f : A -> B) (a b : bool) (vT vF : A).

Lemma negbNE : ~~ ~~ b -> b.
Proof.
  case b. by []. by [].
Qed.

(** Figure out what [involutive] and [injective] mean
    using Coq's interactive queries. Prove the lemmas.
    Hint: to unfold a definition in the goal use [rewrite /definition] command.
 *)
Check cancel.

Lemma negbK : involutive negb.
Proof.
  rewrite /involutive. rewrite /cancel. case.
  - rewrite [negb true]/negb. rewrite [negb false]/negb. by [].
  - by [].
Qed.

Lemma negb_inj : injective negb.
Proof.
  rewrite /injective. case.
  - case. by []. by [].
  - case. by []. by [].
Qed.

Lemma ifT : b -> (if b then vT else vF) = vT.
Proof.
  case b.
  - by [].
  - rewrite [is_true false]/is_true. move /notF. move=> F. exfalso. apply F.
Qed.

Set Printing Notations.
Set Printing Coercions.

Lemma ifF : b = false -> (if b then vT else vF) = vF.
Proof.
  move-> . done.
Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof.
  by case b.
Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof.
  rewrite /negb. case b; by exact.
Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof.
  by case b.
Qed.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof.
    by case b.
Qed.

Lemma andbK : a && b || a = a.
Proof.
  case a; by case b.
Qed.

(** Find out what [left_id], [right_id] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Print left_id.
Print addb.

(* Левая единица: left_id e типа S является левой единицей операции op: S -> T -> T *)
Lemma addFb : left_id false addb.    (* [addb] means XOR (eXclusive OR operation) *)
Proof.
  rewrite /left_id. move=> x0. case x0.
  - rewrite [addb false true]/addb. done.
  - rewrite [addb false false]/addb. done.
Qed.

Print right_id.
Lemma addbF : right_id false addb.
Proof.
  rewrite /right_id. move=> x0. case x0.
  - rewrite [addb true false]/addb. rewrite [negb false]/negb. apply erefl.
  - rewrite [addb false false]/addb. done.
Qed.

Lemma addbC : commutative addb.
Proof.
  rewrite /commutative. move=> x0 y. case x0.
  - by case y.
  - by case y.
Qed.

Lemma addbA : associative addb.
Proof.
  rewrite /associative. move=> x0 y z.
  case x0.
  - case y.
    + by case z.
    + by case z.
  - case y.
    + by case z.
    + by case z.
Qed.

(** Formulate analogous laws (left/right identity, commutativity, associativity)
    for boolean AND and OR and proove those.
    Find the names of corresponding lemmas in the standard library using
    [Search] command. For instance: [Search _ andb left_id.]
    Have you noticed the naming patterns?
 *)


End BooleanLogic.



Section NaturalNumbers.
(** Figure out what [cancel], [succn], [predn] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
  About succn.
  About cancel.
Lemma succnK : cancel succn predn.
Proof.
  rewrite /cancel. rewrite /Nat.pred. by [].
Qed.

Unset Printing Notations.
Set Printing Coercions.
Lemma add0n : left_id 0 addn.
Proof.
  rewrite /left_id. rewrite /addn. move=> x. elim x.
  - rewrite [addn_rec O O]/addn_rec. rewrite [Nat.add O O]/Nat.add. done.
  - move=> n IH. rewrite [addn_rec O (S n)]/addn_rec. rewrite [Nat.add O (S n)]/Nat.add. done.
Qed.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof.
  case m.
  - by rewrite /addn.
  - move=> n0. compute. reflexivity.
Qed.

Lemma add1n n : 1 + n = n.+1.
Proof.
Admitted.

Lemma add2n m : 2 + m = m.+2.
Proof.
Admitted.

Lemma subn0 : right_id 0 subn.
Proof.
Admitted.

End NaturalNumbers.
