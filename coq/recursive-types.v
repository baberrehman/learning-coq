Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Check nat.

Print nat.

Check O.

Reset nat.

Print nat.

Print False.

Print True.

Inductive Lth (n:nat) : nat -> Prop :=
| Lth_intro1: (Lth n (S n))
| Lth_intro2: forall m: nat, (Lth n m) -> (Lth n (S m)).

Theorem zero_less_than_three : (Lth O (S(S(S O)))).
Proof.
apply Lth_intro2.
apply Lth_intro2.
apply Lth_intro1.
Qed.

