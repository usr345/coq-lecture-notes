From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Set Implicit Arguments.
Unset Strict Implicit.
(* Unset Printing Implicit Defensive. *)

Lemma enum_example m (r : rel 'I_m) f v (x : nat) :
  (forall j, r v j -> f v j > 0) ->
  x \in [seq f v j | j <- enum 'I_m & r v j] ->
  0 < x.
Proof.
  set (q:=enum_mem (mem (ordinal m))).
  move: q. elim=> //=.
  move=> a. case E: (r v a)=> //=. rewrite /in_mem=> /=. move=> l IH H. case: orP=> //. case. case: eqP=> // ->. move=> _ _. apply: H. apply E.
  move=> Hmem _. apply: IH. apply: H. apply Hmem.
Qed.


Section TriFinType.
(** Define [finType] structure for the following datatype *)
(**
Hints:
1. To build a [finType] structure you need to build all of its parent structures,
   i.e. [eqType], [choiceType], [countType].
2. An easy way to solve this is to use [CanChoiceMixin], [CanCountMixin], and [CanFinMixin] constructors.
3. The above hint requires mapping [tri] into an already existsing isomorphic [finType], e.g. [ordinal].
4. The [ordinal] type from above is ['I_3]

 *)
(** CanFinMixin *)
Inductive tri : predArgType :=       (* [predArgType] is necessary to make [_ \in _] notation work, see below *)
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

(* Атья Макдональд *)
Canonical tri_eqType := EqType tri tri_eq_mixin.

(* Potan. *)
Print choiceType.

Definition tri_find (P: pred tri) (_: nat) : option tri :=
  if P Yes
  then Some Yes
  else if P No
       then Some No
       else if P Maybe
            then Some Maybe
            else None.

Lemma tri_find_correct1 : forall (P : pred tri) (n : nat) (x : tri), tri_find P n = Some x -> P x.
Proof.
  move => P ? x.
  rewrite /tri_find.
    by case x, (P Yes), (P No), (P Maybe).
Qed.

Lemma tri_find_correct2 : forall P : pred tri, (exists x : tri, P x) -> exists n : nat, tri_find P n.
Proof.
  move => P.
  case => x C.
  exists 0.
  move : x C.
  rewrite /tri_find.
    by case x, (P Yes), (P No), (P Maybe).
Qed.

Lemma tri_find_correct3 : forall P Q : pred tri, P =1 Q -> tri_find P =1 tri_find Q.
Proof.
  move => P Q e ?.
  rewrite /tri_find.
  rewrite (e Yes) (e No) (e Maybe).
  reflexivity.
Qed.

  Definition tri_choiceMixin := Choice.Mixin tri_find_correct1 tri_find_correct2 tri_find_correct3.

  Canonical tri_choiceType := Eval cbn in ChoiceType tri tri_choiceMixin.
End Potan.

(* один из простых вариантов -- определить пару функций tri_to_ord и tri_of_ord (ord здесь значит "ординал"), доказать про них такую лемму *)
Print ordinal.

(** Your definitions here *)
Definition tri2ord (t: tri) : 'I_3 :=
  match t with
  | Yes => (Ordinal (erefl : 0 < 3))
  | No => (Ordinal (erefl : 1 < 3))
  | Maybe => (Ordinal (erefl : 2 < 3))
  end.

Definition nat_of_ord (m : nat) (p : 'I_m) :=
  let: @Ordinal _ n _ := p in n.

Compute (nat_of_ord (tri2ord No)).

Definition ord2tri (t: 'I_3) : tri :=
  match (nat_of_ord t) with
  | 0 => Yes
  | 1 => No
  | _ => Maybe
  end.

Print CanChoiceMixin.
Lemma ordeqtri : cancel tri2ord ord2tri.
case=> //.
Qed.

Definition bool_choiceMixin := CanChoiceMixin oddb.
Definition tri_choiceMixin := CanChoiceMixin ordeqtri.
Print bool_choiceMixin.
Print tri_choiceMixin.
Canonical bool_choiceType := Eval hnf in ChoiceType bool bool_choiceMixin.
Canonical tri_choiceType := Eval hnf in ChoiceType tri tri_choiceMixin.
Definition tri_countMixin := CanCountMixin ordeqtri.
Canonical tri_countType := Eval hnf in CountType tri tri_countMixin.
Definition tri_finMixin := CanFinMixin ordeqtri.
Canonical tri_finType := Eval hnf in FinType tri tri_finMixin.

(** This should work now: *)
Check (Yes != No) && (No \in tri) && (#| tri | == 3).


Definition tri_to_ord (x : tri) : ordinal :=

Lemma tri_cancel: cancel tri_to_ord tri_of_ord.
и воспользоваться рекомендацией из упражнения
Definition tri_eqMixin := CanEqMixin tri_cancel.
Canonical tri_eqType := EqType tri tri_eqMixin.
Definition tri_choiceMixin := CanChoiceMixin tri_cancel.
Canonical tri_choiceType := Eval hnf in ChoiceType tri tri_choiceMixin.
Definition tri_countMixin := CanCountMixin tri_cancel.
Canonical tri_countType := Eval hnf in CountType tri tri_countMixin.
Definition tri_finMixin := CanFinMixin tri_cancel.
Canonical tri_finType := Eval hnf in FinType tri tri_finMixin.

(* Definition in_mem (x : tri) (T : Type) : bool := *)

(* Definition tri_choice_mixin := choiceMixin choice_tri_correct. *)
(* Canonical tri_choiceType := choiceType tri tri_choice_mixin *)

Definition count_tri (T: type) : nat :=
  match x, y with
  | Yes,Yes => true
  | No,No => true
  | Maybe,Maybe => true
  | _,_ => false
  end.

(* Definition tri_count_mixin := countMixin count_tri_correct. *)
(* Canonical tri_countType := countType tri tri_count_mixin *)

About card.
Locate "#|".

(** This should work now: *)
Check (Yes != No) && (No \in tri) && (#| tri | == 3).
End TriFinType.



Section RecordFinType.

Variables A B C : finType.

(** Define [finType] structure for the following datatype *)
Record record : predArgType := Mk_record {
  field_A : A;
  field_B : B;
  field_C : C
  }.

(** This should work now: *)
Variable test : record.
Check (test == test) && (test \in record) && (#| record | == #| record |).

End RecordFinType.



Section DBranch.

Variable ft : finType.

(** Consider a sequence over a finite type with the restriction that all the sequence elements are unique *)
Structure dbranch : predArgType :=
  {branch :> seq ft;
   buniq : uniq branch}.

(** * Define [finType] structure for [dbranch] *)


(** Hints:
1. One way of building a [finType] structure is to embed the new construction
   into a (possibly bigger) finite type.
2. [sigT] is like [sig], but allows the second projection to live in [Type], not in [Prop].
3. Build an embedding of [dbranch] into {k : 'I_#|ft|.+1 & k.-tuple ft}
   and its partial inverse, i.e.

    Definition tag_of_dbranch d : {k : 'I_#|ft|.+1 & k.-tuple ft} := ...
    Definition dbranch_of_tag (t : {k : 'I_#|ft|.+1 & k.-tuple ft}) : option dbranch := ...

4. [PcanFinMixin] is very useful in this setting.
*)

(** Your definitions here *)

(** This should work now: *)
Variable test : dbranch.
Check (test == test) && (test \in dbranch) && (#| dbranch | == #| dbranch |).

End DBranch.



(** Bonus exercises:
There is a library to reduce boilerplate while building instances of basic MathComp classes
for inductive data types: https://github.com/arthuraa/deriving.
Install it (it's available from extra-dev opam repository) an use it to solve some of the above exercise.
*)
