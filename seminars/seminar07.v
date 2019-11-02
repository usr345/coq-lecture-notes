From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Projection using phantoms.
    Implement [swap'] definition and [swap] notation
    so that the following works: *)

(** Strictly no pattern-matching! *)

(* Definition swap' := . *)
Print erefl.
Definition swap' (A: Type) (B: Type) (a: A) (b: B)
           (_ : phantom (A * B) (a, b)) : (B * A) :=
  (b, a).

(* Definition swap'' (A: Type) (B: Type) (a: A) (b: B) *)
(*            (_ : erefl (A * B) (a, b)) : (B * A) := *)
(*   (b, a). *)

Definition swap' (A: Type) (B: Type) (a: A) (b: B)
           (_ : phantom (A * B) (a, b)) : (B * A) :=
  (b, a).


Notation "'swap' p" :=
  (@swap' _ _ _ _ (Phantom _ p)) (at level 60).

(* Notation swap p := (...). *)
(** Usage: *)
Eval hnf in swap (true || false, 41 + 1).
(**
= (41 + 1, true || false)
 *)



(** Design a unification tool so that the following
    typechecks iff X and Y can be unified *)

(* Notation "[unify X 'with' Y ]" := *)
(*   (...). *)

(* eq_op = fun T : eqType => Equality.op (Equality.class T) *)
(*       : forall T : eqType, rel T *)
(* eqE *)
(*      : forall (T : eqType) (x : T), *)
(*        eq_op x = Equality.op (Equality.class T) x *)
(* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x. *)
Print eq.

(* Definition unify {T: Type} (a: T) (_: T): @eq T a a := *)
(*   Logic.eq_refl a : Logic.eq T a a. *)
(* Решить через let*)
Notation "[unify X 'with' Y ]" := (erefl : X=Y) (at level 60).

(** Usage: *)
Check [unify 1 with 0 + 1].
Check [unify 1 with 1 + 0].
Fail Check [unify 1 with 2].
Check (fun n : nat => [unify 0 + n with n]).
Fail Check (fun n : nat => [unify n + 0 with n]).  (** this should fail *)

Definition ident := term.
Section LHS.
(** Design a tool for extracting the left-hand side expression
    from a term proving an equation *)
  Notation "['LHS' 'of' proof_of_equation ]" :=
    (let LHS := _ in
     let _ := proof_of_equation : (LHS=_) in
          LHS)
    (* (let LHS := _ in *)
    (*  let RHS := _ in *)
    (*  let _ := proof_of_equation : (LHS=RHS) in *)
    (*       LHS) *)
      (at level 60).
(*   (). *)
(*

  Notation "['LHS' 'of' prf_eq ]" :=
  (let L := _ in
      let R := _ in
        let _ := prf_eq : L = R in
           (L, R))

Check pLHS if eq].

(let L, _ := _, (prf_eq
*)
Variable prf_eq : true && false = false.
Eval cbv zeta in [LHS of prf_eq].
(** The desired result = true && false *)

End LHS.
