From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section EqType.

Lemma eq_sym (T : eqType) (x y : T) :
  (x == y) = (y == x).
Proof.
  apply /eq_sym.
Qed.
(* ^ Hint: use apply/view1/view2 mechanism *)


(** Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

Definition eq_tri (x y: tri) : bool :=
  match x, y with
  | Yes,Yes => true
  | No,No => true
  | Maybe,Maybe => true
  | _,_ => false
  end.

(* forall x y : tri, eq_tri x y = true <-> x = y. *)
Lemma eq_tri_correct : Equality.axiom eq_tri.
Proof.
  move=> x y.
  by case: x; case: y; constructor.
  (* - case x ; by case y. *)
  (* - move=> ->. by case y. *)
Qed.

Definition tri_eq_mixin := EqMixin eq_tri_correct.

Canonical tri_eqType := EqType tri tri_eq_mixin.
(** This should not fail! *)
Check (1, Yes) == (1, Maybe).
Compute (1, Yes) == (1, Maybe).

(** Define equality type for the [Empty_set] datatype *)
(** This should not fail! *)
Definition eq_Empty (x y: Empty_set) : bool :=
  false.

Lemma eq_empty_correct : Equality.axiom eq_Empty.
Proof.
  by [].
Qed.

Definition empty_eq_mixin := EqMixin eq_empty_correct.


Canonical empty_eqType := EqType Empty_set empty_eq_mixin.

Check fun v : Empty_set => (1, v) == (1, v).


Lemma predU1P (T : eqType) (x y : T) (b : bool) :
  reflect (x = y \/ b) ((x == y) || b).
Proof.
  case: b.
  (* Search _ (_ || true). *)
  - rewrite orbT. apply: ReflectT. by right.
    (* Search _ (true || _). *)
    case E: (x == y).
    + rewrite orTb. apply: ReflectT. left. move: E. by move /eqP.
      rewrite orbF. apply: ReflectF. move: E. move /eqP. move=> xny.
      case.
      * assumption.
      * done.
  Restart.
   case: b.
  (* Search _ (_ || true). *)
  - rewrite orbT. apply: ReflectT. by right.
    (* Search _ (true || _). *)
    case: eqP.
    move=> ->. apply: ReflectT.
    + by left. rewrite orbF. move=> Hxny. constructor. rewrite /not.
      move=> H. case: H.
      * exact Hxny.
        exact.
Qed.

Variables (A B : eqType) (f : A -> B) (g : B -> A).

(* Функция инъективна, когда
   forall a, b \in X, f(a) = f(b) -> a = b
 *)
(* Inductive reflect (P : Prop) : bool -> Set := *)
(*     ReflectT : P -> reflect P true *)
(*   | ReflectF : ~ P -> reflect P false *)
(* eqP *)
(*      : reflect (?x = ?y) (?x == ?y) *)

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof.
  rewrite /injective. move=> Hinj x y. case: eqP.
  - move=> Hf. apply Hinj in Hf.
    (* Как вместо этих 2-х команд применить Hinj к голове цели? *)
    case: eqP => //=.
  - rewrite /not. move=> Hf. case: eqP => //=. move=> Hxy.
    rewrite <- Hxy in Hf. case: (Hf (@erefl B (f x))).
Qed.


Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof.
  rewrite /cancel. move=> HRevExists x y. case: eqP.
  - move=> Hf. case: eqP=> //=. rewrite /not. move=> Hxny.
    set (Ex := HRevExists x).
    rewrite <- Ex in Hxny.
    rewrite Hf in Hxny.
    rewrite HRevExists in Hxny.
    case: (Hxny erefl).
  - move=> Hf. case: eqP=> //=. move=> Hxy.
    (* rewrite <- Hxy in Hf. case: (Hf erefl).*)
     move: Hf. move: Hxy <-. by case.
Qed.

Search "addnI".

Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
  case: eqP.
  - move=> H. apply addnI in H. move: H ->. by rewrite eq_refl.
    move=> H. case: eqP=> //=. move=> Eq. rewrite Eq in H. by case: H.
Qed.

Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof.
Admitted.


Lemma seq_last_notin (s : seq A) x :
        last x s \notin s = (s == [::]).
Proof.
Admitted.

End EqType.
