From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Classical_reasoning.

(** We assert the classical principle of double negation elimination *)
Variable DNE : forall A : Prop, ~ ~ A -> A.

(* Lemma nat_ind2' (P : nat -> Prop) : *)
(*   P 0 -> *)
(*   P 1 -> *)
(*   (forall n, P n -> P n.+2) -> *)
(*   forall n, P n. *)
(* Proof. *)
(*   move=> P0 P1 H. *)
(*   case. *)
(*   - by []. *)
(*   - move=> n. move: (H n). *)

(* https://en.wikipedia.org/wiki/Drinker_paradox *)
Lemma drinker_paradox (P : nat -> Prop) :
  (exists x, P x) -> forall y, P y.
Proof.
  move=> x. case x. move=> x0 Px0 y.
  apply DNE. rewrite /not.
  Admitted.
(* This closes the section, discharging over DNE *)
End Classical_reasoning.

Check drinker_paradox.

Section Misc.

Variables A B : Type.
Implicit Types x y : A * B.

(* Unset Printing Notations. *)
Lemma prod_inj x y :
  x = y <-> (x.1, x.2) = (y.1, y.2).
Proof.
  split.
  - move=> H. rewrite -H. exact.
  - case. case x. case y. move=> a b a0 b0.
    rewrite /((a0, b0).1) /((a, b).1) /((a0, b0).2) /(a, b).2. move=> Eq1 Eq2. rewrite Eq1 Eq2.
    done.
Qed.

Lemma prod_inj' x y :
  x = y <-> (x.1, x.2) = (y.1, y.2).
Proof.
  by move: x y=> [x1 x2] [y1 y2].
Restart.
  by move: x y=> [? ?] [? ?].
  Restart.
  split.
  - move=> H. rewrite -H. exact.
  - case. case x. case y. move=> a b a0 b0.
    rewrite /((a0, b0).1) /((a, b).1) /((a0, b0).2) /(a, b).2. move=> Eq1 Eq2. rewrite Eq1 Eq2.
    done.
  Restart.
    by case: x; case: y.
Qed.

End Misc.

Check eqP.

Section Arithmetics.
(* Unset Printing Notations. *)

About leq_trans.
About leq_addr.
Lemma min_plus_r  n m p  :
  minn n m = n -> minn n (m + p) = n.
Proof.
  move /minn_idPl=> H. apply /minn_idPl. apply leq_trans with (n:=m).
  - exact H.
  - apply leq_addr.
  (*
  case: n => [|n'].
  - by rewrite !min0n.
  - move /minn_idPl => H. apply /minn_idPl. apply ltn_addr. apply H.
*)
Qed.

Search (minn _ _).
Lemma min_plus_minus m n p :
  minn n m + minn (n - m) p = minn n (m + p).
Proof.
  case (n <= m) eqn: NM.
  - set (H := NM).
    move: H => /minn_idPl ->.
    set (H1 := NM).
    rewrite <- (subn_eq0 n m) in H1.
    move: H1. move /eqP ->. rewrite -> min0n. rewrite -> addn0.
    move : (leq_trans NM (leq_addr p m)).
    move /minn_idPl. move ->. exact.
  - move: (leq_total n m). rewrite -> NM. simpl. move => H. move : (H). move /minn_idPr. move ->. rewrite -> addn_minr.
    Search _ (?n + (?m + ?n)).
    rewrite -> (subnKC H). done.
    (* rewrite <- (Bool.reflect_iff (minn n m = n) (n <= m) (@minn_idPl n m)) in H. *)
Qed.


Fixpoint zero (n : nat) : nat :=
  if n is n'.+1 then zero n'
  else 0.

Lemma zero_returns_zero n :
  zero n = 0.
Proof.
  by elim n.
Qed.

Search "ltn_mod".
(**
Claim: every amount of postage that is at least 12 cents can be made
       from 4-cent and 5-cent stamps. *)
(** Hint: no need to use induction here *)
Search (_ + _ - _).

Lemma my_lemma n : n %/ 4 * 4 + n %% 4 * 5 - n %% 4 * 4 = n.
Proof.
  rewrite -addnBA; last first.
  Search _ (_ * _ <= _ * _).
  - rewrite leq_mul2l. rewrite orbC. done.
  - rewrite -mulnBr. rewrite muln1.
    Print right_distributive.
  (* n %/ 4 * 4 + n %% 4 = n. *)
  symmetry. apply: divn_eq n 4.
Qed.

Lemma stamps n : 12 <= n -> exists s4 s5, s4 * 4 + s5 * 5 = n.
Proof.
  Search "mod".
  set (H := ltn_mod n 4).
  Search _ (0 < ?a.+1).
  rewrite -> ltn0Sn in H.
  move => C.
  exists ((n - (n %% 4) - (n %% 4) * 4) %/ 4), (n %% 4).
  About divn_eq.
  set (H1 := divn_eq n 4).
  assert ((12 %/ 4) * 4 <= n - n %% 4).
  - rewrite -> H1 at 1.
    Search _ (?b + ?a - ?c).
    About addnBA.
    rewrite <- (addnBA (n %/ 4 * 4) (leqnn (n %% 4))).
    rewrite -> subnn.
    rewrite -> addn0.
    Search "leq".
    rewrite -> leq_mul2r.
    simpl.
    apply leq_div2r.
    exact C.
  Search "leq".
  assert (n %% 4 <= 3).
  - by [].
  Search "divn".
  About divnBl.
  set (H3 := divn_eq (n - n %% 4 - n %% 4 * 4) 4).
  Search "subn".
  About subnK.
  Search "mod".
  rewrite <- (subnK (leq_mod (n - n %% 4 - n %% 4 * 4) 4)) in H3 at 1.
  Search _ (?a + ?b == ?c + ?b).
  About eqn_add2r.
  (* apply eq_add2r in H3. *)
  (* move : H3 <-. *)
  (* assert (n - n %% 4 = n %/ 4 * 4). *)
  (* - rewrite -> H1 at 1. *)
  (*   Search _ cancel addn subn. *)
  (*   rewrite -> addnK. *)
  (*   reflexivity. *)
  (* rewrite -> H3 at 2. *)
  (* rewrite <- mulnBl. *)
  (* Search "mod". *)
  (* rewrite -> modnMl. *)
  (* rewrite -> subn0. *)
  (* Search "subn". *)
  (* rewrite <- subnDA. *)
  (* Search "muln". *)
  (* rewrite <- (muln1 (n %% 4)) at 1. *)
  (* rewrite <- mulnDr. *)
  (* assert (1 + 4 = 5). *)
  (* - reflexivity. *)
  (* rewrite -> H4. *)
  (* Search _ (?a <= ?b -> ?a = ?b \/ ?a.+1 <= ?b). *)
  (* About leq_eqVlt. *)
  (* rewrite -> leq_eqVlt in C. *)
  (* rewrite -> leq_eqVlt in C. *)
  (* rewrite -> leq_eqVlt in C. *)
  (* move : C. *)
  (* move /orP. *)
  (* case. *)
  (* - move /eqP. *)
  (*   move => C. *)
  (*   rewrite <- C in *. *)
  (*   reflexivity. *)
  (* move /orP. *)
  (* case. *)
  (* - move /eqP. *)
  (*   move => C. *)
  (*   rewrite <- C in *. *)
  (*   reflexivity. *)
  (* move /orP. *)
  (* case. *)
  (* - move /eqP. *)
  (*   move => C. *)
  (*   rewrite <- C in *. *)
  (*   reflexivity. *)
  (* assert (n %% 4 * 5 <= 15). *)
  (* - Search "leq". *)
  (*   exact (leq_mul H2 (leqnn 5)). *)
  (* move => C. *)
  (* set (H6 := leq_trans H5 C). *)
  (* exact (subnK H6). *)
  Restart.
  move=> H. exists (n %/ 4 - n %% 4). exists (n %% 4). rewrite mulnBl.
  rewrite addnBAC; last first.
  - rewrite leq_mul2r=> /=.
    assert (H1: n %% 4 <= 3).
    { apply: ltn_mod n 4. }
    assert (H2: 3 <= n %/ 4).
    { rewrite -[3]/(12 %/ 4). apply: leq_div2r 4 12 n H. }
    (* leq_trans  forall n m p : nat, m <= n -> n <= p -> m <= p *)
    apply: leq_trans H1 H2.
  - apply my_lemma.
Qed.

End Arithmetics.


(* ======================================== *)

(** Bonus track: properties of functions and their composition.
    Feel free to skip this part.
 *)

(** Solutions for the exercises in seminar02.v, we are going to need them later *)
Section eq_comp.
Variables A B C D : Type.

(** Note: [rewrite !compA] would fail because it keeps adding [id \o ...]
    this is due to the fact that [compA] is a convertible rule,
    so it clashes with Miller pattern unification *)
Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof. by []. Qed.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof. by move=> f_id g12f a; move: (g12f a)=> /=; rewrite !f_id. Qed.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof. by move=> g_id f12g a; move: (f12g a)=> /=; rewrite g_id. Qed.

End eq_comp.



(** You might want to use the lemmas from seminar02.v, section [eq_comp] *)
Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

Lemma surj_epic f : surjective f -> epic f.
Proof.


Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Proof.
Admitted.

Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Proof.
Admitted.

Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Proof.
Admitted.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

Lemma inj_monic f : injective f -> monic f.
Proof.
Admitted.

Lemma monic_inj f : monic f -> injective f.
Proof.
Admitted.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
Admitted.

Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
Admitted.

Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
Admitted.

End MonicProperties.

End PropertiesOfFunctions.
