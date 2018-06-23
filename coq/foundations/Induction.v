Require Import Coq.Unicode.Utf8.

Require Export Basics.

Theorem plus_n_O_firsttry : ∀ n : nat, n = n + 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag : ∀ n, minus n n = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_0_r : ∀ n : nat, n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.


Theorem plus_n_Sm : ∀ n m : nat, S (n + m) = n + (S m).
Proof.
  induction n as [|n' IHn'].
  destruct m.
  - reflexivity.
  - reflexivity.
  - simpl.
    intros m.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : ∀ n m : nat, n + m = m + n.
Proof.
  induction n as [|n' IHn'].
  intros m.
  - rewrite <- plus_n_O_firsttry.
    reflexivity.
  - intros m.
    simpl.
    rewrite <- plus_n_Sm.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem plus_assoc : ∀ n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - intros m p.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : ∀ n, double n = n + n .
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem evenb_S : ∀ n : nat, evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'.
    simpl.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

Theorem mult_0_plus' : ∀ n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : ∀ n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). {
    rewrite <- plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

