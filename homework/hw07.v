From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Properties of arbitrary binary relations (not necessarily decidable) *)
(** A functional or deterministic relation *)
Definition functional {X : Type} (R : X -> X -> Prop) : Prop :=
  forall (s s1 s2 : X), R s s1 -> R s s2 -> s1 = s2.

Print eqE.
Locate "=P".
Search "eqP".
Lemma func1 :
  functional (fun x y => x.*2 == y).
Proof.
  rewrite /functional. move=> s s1 s2.
  case: (s.*2 =P s1) => //. move=> H1 _. case: (s.*2 =P s2) => //.
  move=> H2 _. rewrite <- H1. by rewrite <- H2.
  Restart.
  move=> s s1 s2.
  repeat case /eqP => // ->.
Qed.

Lemma func2 :
  ~ functional (fun x y => (x.*2 == y) || ((x, y) == (0,1))).
Proof.
  rewrite /functional /not. move=> H. move: (H 0 1 0 erefl erefl). exact.
Qed.

(** Define a notation such that {In C, functional R} restricts the domain of the relation like so:

  forall (s s1 s2 : X), C s -> R s s1 -> R s s2 -> s1 = s2

And prove the following lemma:
*)
(* Notation "{ 'In' C, functional P }" := *)
(*   let Phantom  *)
(*   (C -> functional P) *)
(*     (at level 70, no associativity) : no_scope. *)
(*   (...) (at level 0). *)
About functional.
About phantom.
Check (functional (fun x y => (x.*2 == y) || ((x, y) == (0,1)))).
Notation "{ 'In' C , P }" :=
  (let T := _ in
  let R : T -> T -> Prop := _ in
  let F : (T -> T -> Prop) -> Prop := _ in
  let _ : phant(F R) := Phant(P) in
  (* let _ : phantom Prop (F R) := Phantom Prop (P) in *)
  F (fun s1 s2 => (C s1 /\ C s2 /\ R s1 s2))).

Lemma func3 :
  {In (fun n => 0 < n), functional (fun x y => (x.*2 == y) || ((x, y) == (0,1)))}.
Proof.
  move=> /=. rewrite /functional. move=> s s1 s2. case=> Hs.
  case=> Hs1. case: orP => //. case. case: eqP => //. move=> Hs2s1 _ _.
  - case=> _. case=> Hs2. case: orP=> //. case. case: eqP => //. move=> Hs2s2 _ _.
    + by rewrite -Hs2s1 -Hs2s2.
    + case: eqP=> //. case. move=> Hs' Hs2' _ _. move: Hs. rewrite Hs'. done.
    + case: eqP=> //. case. move=> Hs' Hs2' _ _. case=> _. case=> Hs2. case: orP=> //. case: eqP=> Hss2.
      * case=> _ _. by move: Hs; rewrite -Hs'; rewrite ltnn. by move: Hs; rewrite -Hs'; rewrite ltnn.
      * case=> //. case: eqP=> //. case=> _ Hs2'' _ _. by rewrite Hs2' Hs2''.
Qed.

(* Unset Printing Notations. *)
Search _ "orb".
(* Print is_true. *)
(* prove without using [case] or [elim] tactics *)

(* negb_or  forall a b : bool, ~~ (a || b) = ~~ a && ~~ b *)
(* negb_and  forall a b : bool, ~~ (a && b) = ~~ a || ~~ b *)
(* negbK  involutive negb *)
(* orbK  forall a b : bool, (a || b) && a = a *)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
Proof.
  case E: (p ==> q)/implyP.
  - rewrite implyTb. apply: implybb.
  - rewrite implyFb. rewrite implyTb. move: E.
  Restart.
  rewrite !implybE. rewrite [~~ (~~ p || q)] negb_or. rewrite [~~ ~~ p] negbK. rewrite negb_or. rewrite negb_and. rewrite negbK. rewrite [(~~ p || q) && ~~ p] orbK. rewrite orbC. by rewrite orbN.
Qed.

(* prove without using [case] or [elim] tactics *)
Unset Printing Notations.
Search _ (addb _ _).
Lemma addb_neq12 p q :  ~~ p = q -> p (+) q.
Proof.
  move=> H. rewrite -H. rewrite addbN. rewrite negb_add. by [].
Qed.


Lemma div_fact_plus1 m p : 1 < p -> p %| m `! + 1 -> m < p.
Admitted.


(* Prove [8x = 6y + 1] has no solutions in [nat] *)
Lemma no_solution x y :
  8*x != 6*y + 1.
Admitted.



Lemma iota_add m n1 n2 :
  iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Admitted.

Definition mysum m n F := (foldr (fun i a => F i + a) 0 (iota m (n - m))).

(* "big" operator *)
Notation "\mysum_ ( m <= i < n ) F" := (mysum m n (fun i => F))
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \mysum_ ( m  <=  i  <  n ) '/  '  F ']'").

Lemma mysum_recl m n F :
  m <= n ->
  \mysum_(m <= i < n.+1) F i = \mysum_(m <= i < n) F i + F n.
Admitted.

Lemma sum_odds n :
  \mysum_(0 <= i < n) (2 * i + 1) = n ^ 2.
Admitted.
