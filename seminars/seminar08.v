From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Odd and even numbers *)


Structure odd_nat := Odd {
  oval :> nat;
  oprop : odd oval
}.

(** Prove the main property of [odd_nat] *)
Lemma oddP (n : odd_nat) : odd n.
Proof.
  case: n=> [m pfm]. apply pfm.
Qed.

Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.

(* Prove the main property of [even_nat] *)
Lemma evenP (n : even_nat) : ~~ (odd n).
Proof.
  case: n=> [m pfm]. apply pfm.
Qed.

(** ** Part 1: Arithmetics *)


(** The objective is to make it work: knowing that
    [n] is [odd] Coq should infer that [n * 3]
    is also [odd], and that [6] is even *)
Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

(* Let's start by telling Coq that 0 is even *)
Canonical even_0 : even_nat := @Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof.
  by elim: n=>[|n'].
Qed.

Search "negb".
(* Unset Printing Notations. *)
Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof.
  elim: n=>[|n' IH] //=. by rewrite negbK.
Qed.

(** Here we teach Coq that if [m] is even,
    then [m.+1] is [odd] *)

(* Structure even_nat := Even { *)
(*   eval :> nat; *)
(*   eprop : ~~ (odd eval) *)
(* }. *)
(* Lemma oddS n : ~~ (odd n) -> odd n.+1. *)
(* Definition odd_evenMixin := Equality.Mixin *)
Canonical odd_even (m : even_nat) : odd_nat :=
                              @Odd (eval m).+1 (oddS (eprop m)).

(** Implement the dual, teach Coq that if [m]
    is [odd] then [m.+1] is [even] *)

Canonical even_odd (m : odd_nat) : even_nat :=
  @Even (oval m).+1 (evenS (oprop m)).

Search _ (reflect).
(* Print odd_mul. *)
Set Printing All.
(* odd_mul  forall m n : nat, odd (m * n) = odd m && odd n *)
(** Now let's deal with multiplication *)
Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Proof.
  case: n=> [n' pfn]. case: m=> [m' pfm]. rewrite odd_mul. case: andP=> //=. rewrite /not. case. by split.
  Restart.
    by rewrite odd_mul (oprop n) (oprop m).
  Restart.
    by rewrite odd_mul !oddP.
Qed.

(** Teach Coq that [*] preserves being [odd] *)

Canonical oddmul_Odd (n m : odd_nat) : odd_nat :=
  @Odd ((oval n)*(oval m)) (odd_mulP n m).

(* It should work now! *)
Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
Proof. by rewrite oddP evenP. Qed.


(** ** Part 2: Equality *)

(** We can't use [==] on [odd] natural numbers because
   [odd_nat] is not an [eqType] *)
Fail Check forall n : odd_nat, n == n.

(** Use the [subType] machinery in order
   to teach Coq that [odd_nat] is an [eqType] *)

(* Definition foo '(Even n _) := n. *)
Coercion nat_of_odd n_odd :=
  let: Odd n _ := n_odd in n.

Canonical odd_subType :=
  [subType for nat_of_odd].

Definition odd_eqMixin :=
  Eval hnf in [eqMixin of odd_subType by <:].

Canonical odd_eqType :=
    Eval hnf in EqType odd_nat odd_eqMixin.

(* This should work now *)
Check forall n : odd_nat, n == n.
Lemma odd_nat_eq_refl (n : odd_nat) : n == n.
Proof. by rewrite eq_refl. Qed.

(** Now deal with [even_nat] *)
Coercion nat_of_even n_even :=
  let: Even n _ := n_even in n.

Canonical even_subType :=
  [subType for nat_of_even].

Definition even_eqMixin :=
  Eval hnf in [eqMixin of even_subType by <:].

Canonical even_eqType :=
    Eval hnf in EqType even_nat even_eqMixin.

Check forall (m : even_nat), m == m.

Check forall (m : even_nat), m == m.

Lemma even_nat_eq_refl (n : even_nat) : n == n.
Proof. by rewrite eq_refl. Qed.
