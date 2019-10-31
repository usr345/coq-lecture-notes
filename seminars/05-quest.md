Состояние:

  n : nat
  IH : is_true (div2 n <= n)
  ============================
  (div2 n < n.+2) = true

Имеется лемма:

le_n_S
     : forall n m : nat,
       (n <= m)%coq_nat -> (n.+1 <= m.+1)%coq_nat

apply le_n_S.

Выдает:

Unable to unify "(?M1111.+1 <= ?M1112.+1)%coq_nat" with
 "(div2 n < n.+2) = true".

Как всё-таки применить её?

# вопрос 2

Lemma div2_le n : div2 n <= n.
Proof.
  move: n.
  apply nat_ind2'; try by [].
  move=> n IH. cbn [div2]. move: IH. apply leqW.
Qed.

Почему apply leqW. сработала?

После move: IH. наше состояние:

  n : nat
  =====================================
  forall _ : is_true (leq (div2 n) n),
  is_true (leq (S (div2 n)) (S (S n)))


Учитывая формулировку теоремы:

leqW
     : forall m n : nat, m <= n -> m <= n.+1

Я ожидал, что она преобразует голову в

is_true (leq (div2 n) S n)

Потом надо было бы как-то снять S-ы обеих частях неравенства в цели, но она почему-то решила всё (?!)

# Вопрос 3

Имеем:

Lemma suffix_spec c n s :
  forall i, i < size s -> nth (leftpad c n s) (n - size s + i) = nth s i.
Proof.
  rewrite /leftpad. move=> i H.
  (* commutative addn *)
  rewrite addnC.
  rewrite nth_ncons. rewrite ifN.

Состояние:

2 subgoals (ID 69)

  T : Type
  def, c : T
  n : nat
  s : seq T
  i : nat
  H : i < size s
  ============================
  nth s (i + (n - size s) - (n - size s)) = nth s i

subgoal 2 (ID 70) is:
 ~~ (i + (n - size s) < n - size s)

Как заменить (n - size s) - (n - size s) на 0?

Отчаявшись искать, я доказал свою лемму:

Lemma subnn1 : forall n: nat, subn n n = 0.
Proof.
    by elim.
Qed.

Но rewrite [(n - size s) - (n - size s)]/subnn1.

Выдает:

Ltac call to "rewrite (ssrrwargs) (ssrclauses)" failed.
term (n - size s - (n - size s))
does not match any subterm of the goal

Почему это нет, когда он там есть?