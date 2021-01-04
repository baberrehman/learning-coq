(*
A Tutorial on Recursive Types in Coq
Eduardo Giménez

HAL
*)

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

Require Import List.

Check list.

Check list nat.

Check (cons 3 (cons 2 nil)).

(*
Mutually Dependent Declarations
*)

Inductive Tree (A : Set) : Set :=
  | node : (Forest A) -> (Tree A)
with
Forest (A : Set) : Set :=
  | nochild : (Forest A)
  | addchild : (Tree A) -> (Forest A) -> (Forest A).

Inductive Even : nat -> Prop :=
  | evenO : (Even O)
  | evenS (n: nat) : (Odd n) -> Even (S n)
with
Odd : nat -> Prop :=
  | odd1 : (Odd (S O))
  | oddS (n: nat) : (Even n) -> Odd (S n).

Theorem disc1 : forall n : nat, ~((S n) = 0).
Proof.
intros. discriminate.
Qed.

Theorem disc2 : forall n : nat, ~(S (S n) = (S O)).
Proof.
discriminate.
Qed.

Theorem disc3 : forall (n : nat) Q, (S (S n) = (S O)) -> Q.
Proof.
discriminate.
Qed.


Theorem inj : forall (n m : nat), (S(S n)) = (S(S m)) -> n = m.
Proof.
intros.
injection H. auto.
Qed. 

Fixpoint add (n m : nat) : nat :=
  match n with
  | O    => O
  | S n' => S (add n' m)
 end.

Reset add.

Fixpoint add (n m : nat) : nat :=
  match m with
  | O    => O
  | S m' => S (add n m')
 end.



Fixpoint even (n: nat) : bool :=
  match n with
  | O => true
  | S m => (odd m)
  end
with
odd (n: nat) : bool :=
  match n with
  | O => false
  | S m => (even m)
  end.

Eval simpl in even.

Eval simpl in odd 1.

Check even.

Scheme Even_induction := Minimality for Even Sort Prop
with Odd_induction := Minimality for Odd Sort Prop.

Print Even_induction.

Print Acc.

Require Minus.

Require Import Arith.

(*Fixpoint div (x y : nat) : nat :=
  if (x =? O) then O
  else if (y =? O) then x
    else (S (div (minus x y) y)).*)

Lemma smaller : forall (x y : nat), (Lth (minus x y) (S x)).
Proof.
  intros.
  induction x; induction y; simpl.
  constructor. constructor.
  constructor.
Admitted.

Lemma smallerSS : forall (x y : nat), ~ (x=O) -> ~(y=O) -> (Lth (minus x y)x).
Proof.
  intros.
  destruct x; destruct y; simpl; eauto.
  congruence.
  congruence.
  congruence.
  apply smaller.
Defined.

Theorem decrease : forall (x y : nat), (Acc Lth x) -> ~(x=O) -> ~(y=O) ->
(Acc Lth (minus x y)).
intros x m H.
case H; intros n h diseqx.
apply n. apply smallerSS. apply h.
apply diseqx.
Defined.

Theorem div : forall (x y : nat), Acc Lth x -> nat.
auto.
Defined.

Print div.
