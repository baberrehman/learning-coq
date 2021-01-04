(*
Coq in a Hurry
Yves Bertot
*)

Check True.

Check true.

Eval compute in
  let f := fun x => (x * 3, x) in f 3.

Definition sum5 (a b c d e : nat) : nat := a+b+c+d+e.

Eval compute in sum5 1 2 3 4 5.

Check sum5.
Print sum5.

Definition example1 := fun x : nat => x*x+2*x+1.

Reset example1.

Definition example1 (x : nat) : nat := x*x+2*x+1.

Eval compute in example1 1.

Require Import Bool.

Eval compute in (if true then 4 else 5).

Require Import Arith.

Definition is_zero (n : nat) : bool :=
  match n with
  | O   => true
  | S p => false
  end.

Eval compute in (is_zero 1).

Fixpoint sum_n (n : nat) : nat :=
  match n with
  | O   => O
  | S p => (S p) + sum_n p
 end.

Eval compute in sum_n 4.

Fixpoint sum_n2 (n s : nat) :=
  match n with
  | O   => s
  | S p => sum_n2 p (p + s)
  end.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | 1 => false
  | S (S p) => evenb p
  end.

Require Import List.

Check 1::2::3::nil.

Fixpoint n_numbers (n : nat) : list nat :=
  match n with
  | O   => nil
  | S p => (n_numbers p) ++ (p::nil)
 end.

Eval compute in n_numbers 2.

Fixpoint n_numbers' (n : nat) : list nat :=
  match n with
  | O   => nil
  | S p => map (fun x => x) ((n_numbers' p) ++ (p::nil))
 end.

Eval compute in n_numbers' 5.

Definition head_evb (l: list nat) : bool :=
  match l with
  | nil   => false
  | a::tl => evenb a
  end.

Fixpoint sum_list (l : list nat) :=
  match l with
  | nil   => O
  | n::tl => n + (sum_list tl)
  end.

Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | nil   => n :: nil
  | a::tl => if leb n a then (n::l) else (a::insert n tl)
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | nil   => nil
  | a::tl => insert a (sort tl)
  end.

Eval compute in sort (5::4::3::2::1::nil).

Definition get_head (A : Type) (r : A) (l : list A) : A :=
  match l with
  | nil => r
  | a::tl => a
  end.

Definition get_tail (A : Type) (l : list A) : list A :=
  match l with
  | nil => nil
  | a::tl => tl
  end.

Fixpoint is_sorted (l : list nat) : bool :=
  match l with
  | nil      => true
  | a::nil   => true
  | a::tl => if leb a (get_head nat 0 tl) then (is_sorted tl) else false
  end.

Eval compute in is_sorted (0::0::nil).

Fixpoint count_n (n : nat) (l : list nat) : nat :=
  match l with
  | nil   => O
  | a::tl => if (beq_nat a n) then (S (count_n n tl)) else (count_n n tl)
  end.

Eval compute in count_n 0 (0::0::nil).

Search True.

SearchPattern (_ + _ <= _ + _).

SearchAbout leb.

Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.
Proof.
  intros.
  elim H; auto.
Qed.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
  intros.
  elim H; auto.
Qed.


Lemma test1 : forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H2 as [H2 H3].
  auto.
Qed.

Lemma test2 : forall A B C D: Prop,(A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H2 as [H2 H3].
  destruct H3 as [H3 H4].
  split; auto.
Qed.

Lemma test3 : forall A: Prop, ~(A/\~A).
Proof.
  intros.
  unfold not.
  intros.
  destruct H as [H1 H2].
  apply H2. apply H1.
Qed.

Lemma test4 : forall A B C: Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
  intros.
  destruct H; auto.
  destruct H; auto.
Qed.

Lemma test5 : forall A B: Prop, (A\/B)/\~A -> B.
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H1; auto.
  contradiction.
Qed.

Lemma exercise_universal_quantification : forall A:Type, forall P Q: A->Prop,
(forall x, P x)\/(forall y, Q y)->forall x, P x\/Q x.
Proof.
  intros.
  destruct H.
  left. apply H.
  right. apply H.
Qed.

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
Proof.
  induction n.
  simpl. reflexivity.
  simpl in IHn.
Admitted.

