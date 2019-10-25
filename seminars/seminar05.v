From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section LeftPad.

(**
What is "leftpad"?

Leftpad is a function that takes a character, a length, and a string, and pads the string to that length.
It pads it by adding the character to the left.

Compute leftpad 0 5 [:: 1; 2; 3]. (* = [:: 0; 0; 1; 2; 3] *)
Compute leftpad 0 2 [:: 1; 2; 3]. (* = [:: 1; 2; 3]  *)
*)


(* [def] is the default value, i.e. type T is not empty *)
Variables (T : Type) (def : T).

(** Define the leftpad function, modeling strings as sequences of elements of type [T] *)
(* Search "nseq". *)
Check ncons.
(* Compute length [:: 1; 2; 3]. *)
Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (n-size s) c s.
  (* if (length s < n) then (nseq (n-length s) c ++ s) else s. *)

(* End LeftPad. *)
(* Compute leftpad 0 5 [:: 1; 2; 3]. *)
(* Compute leftpad 0 2 [:: 1; 2; 3]. *)

(** The following properties of the leftpad function *)
Search (length _ = _).
(* projectile *)
(* helm projectile *)
Check maxnE.
(* size_ncons *)
(*    forall (T : Type) (n : nat) (x : T) (s : seq T), *)
(*    size (ncons n x s) = n + size s *)
Lemma length_max_spec c n s :
  size (leftpad c n s) = maxn n (size s).
Proof.
  rewrite maxnC.
  rewrite size_ncons.
  rewrite maxnE.
  rewrite addnC.
  exact.
Qed.

(** Local alias for the [nth] function returning the n-th element of the input sequence *)
Local Notation nth := (nth def).

Search "nth".
(* size_ncons *)
(*    forall (T : Type) (n : nat) (x : T) (s : seq T), *)
(*    size (ncons n x s) = n + size s *)

Search (_ < _).
Lemma prefix_spec c n s :
  forall i, i < n - size s -> nth (leftpad c n s) i = c.
Proof.
  move=> i.
  rewrite /leftpad.
  Search _ seq.nth ncons.
  rewrite nth_ncons. move=> ->.
  exact.
Qed.

(* nth_ncons *)
(*    forall (T : Type) (x0 : T) (m : nat)  *)
(*      (x : T) (s : seq T) (n : nat), *)
(*    seq.nth x0 (ncons m x s) n = *)
(*    (if n < m then x else seq.nth x0 s (n - m)) *)

Lemma subnn1 : forall n: nat, subn n n = 0.
Proof.
    by elim.
Qed.

(* Set Printing All. *)
Lemma suffix_spec c n s :
  forall i, i < size s -> nth (leftpad c n s) (n - size s + i) = nth s i.
Proof.
  rewrite /leftpad. move=> i H.
  (* commutative addn *)
  rewrite addnC.
  rewrite nth_ncons. rewrite ifN.

  - rewrite -addnBA. rewrite addnC.
    (* Search _ (_ + _ - _). *)
    rewrite subnn1=> //. apply: leqnn.
  -
  (* Search _ subn ?n ?n.  Search (nth _ _ = nth _ _). *)
Admitted.

End LeftPad.
subnn
  self_inverse

Section MoreInductionExercises.

  (** Implement a recursive function performing integer division by 2 *)
(* Fixpoint div2_helper (n n2: nat) {struct n} : nat := *)
(*   match n with *)
(*   | S (S n') => div2_helper n' (S n2) *)
(*   | _ => n2 *)
(*   end. *)

(* Definition div2 (n : nat) : nat := *)
  (*   div2_helper n 0. *)

Fixpoint div2 (n : nat) : nat :=
  match n with
  | S (S n') => S (div2 n')
  | _ => O
  end.

(* You might want to uncomment the following: *)
Arguments div2 : simpl nomatch.

Lemma nat_ind2' (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+2) ->
  forall n, P n.
Proof.
  move=> H0 H1 IH n. enough(P n /\ P n.+1).
  - case: H. exact.
  - elim: n.
    + by split.
    + move=> n H. split.
      * by case: H.
      * apply IH. by case: H.
Qed.

(* Set Printing All. *)
Search leq (S _) (S _).
(* Здесь используется бинарное сравнение:
is_true (leq (div2 n) n)
 *)
Lemma div2_le n : div2 n <= n.
Proof.
  move: n.
  apply nat_ind2'; try by [].
  move=> n IH. cbn [div2]. move: IH. apply leqW.
  Restart.
  move: n.
  apply nat_ind2'; try by [].
  move=> n IH. cbn [div2]. move: IH=> /leqW. move /leqW.
    Search _ leq (S _) (S _).
  (* apply leq_ltn_trans with (div2 n). *)
Qed.

Lemma div2_correct n :
  div2 n = n./2.
Proof.
  induction n using nat_ind2'; try by[].
  simpl. rewrite IHn. exact.
Qed.

(** Strong induction principle *)
Lemma lt_wf_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
Admitted.


Fixpoint divn_my (n m : nat) {struct n} : nat :=
  if m is m'.+1 then
    if n - m' is d.+1 then
      (divn_my d m).+1
    else 0
  else 0.

Lemma divn_my_correct n m :
  divn_my n m = divn n m.
Proof.
Admitted.




Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

Lemma fib3 n :
  fib (3*n).+1 = (fib n.+1)^3 + 3 * fib n.+1 * (fib n)^2 - (fib n)^3.
Proof.
Admitted.

End MoreInductionExercises.
