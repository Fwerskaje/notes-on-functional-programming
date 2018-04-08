Set Warnings "-notation-overridden,-parsing".
Require Export Poly.
Require Import Coq.Unicode.Utf8.
Require Import Basics.
Require Import Lists.

Theorem silly1 : ∀ (n m o p : nat),
    n = m →
    [n; o] = [n; p] →
    [n; o] = [m; p].
Proof.
  intros n m o p.
  intros Eq₁.
  intros Eq₂.
  rewrite <- Eq₁.
  apply Eq₂.
Qed.

Theorem silly2 : ∀ (n m o p : nat),
     n = m →
     (∀ (q r : nat), q = r → [q;o] = [r;p]) →
     [n;o] = [m;p].
Proof.
  intros n m o p.
  intros Eq₁.
  intros H.
  apply H.
  apply Eq₁.
Qed.

Theorem silly2a : ∀ (n m : nat),
     (n,n) = (m,m) →
     (∀ (q r : nat), (q,q) = (r,r) → [q] = [r]) →
     [n] = [m].
Proof.
  intros n m Eq₁ H.
  apply H.
  apply Eq₁.
Qed.

Theorem silly_ex :
     (∀ n, evenb n = true → oddb (S n) = true) →
     evenb 3 = true →
     oddb 4 = true.
Proof.
  intros H Eq₁.
  apply H.
  apply Eq₁.
Qed.

Module L.

  Theorem l_nil: ∀ {A : Type} {l : list A},
    l ++ [] = l.
  Proof.
    intros A l.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem app_ass : ∀ {A : Type} (l1 l2 l3 : list A),
      (l1 ++ (l2 ++ l3)) = ((l1 ++ l2) ++ l3).
  Proof.
    intros A l1 l2 l3.
    induction l1 as [|n l1' IHl1'].
    - reflexivity.
    - simpl.
      rewrite <- IHl1'.
      reflexivity.
  Qed.
      
  Theorem rev_app_distr: ∀ {A : Type} (l1 l2 : list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    induction l1 as [|n l1' IHl1'].
    - intros l2.
      simpl.
      rewrite -> l_nil.
      reflexivity.
    - intros l2.
      simpl.
      rewrite -> IHl1'.
      rewrite -> app_ass.
      reflexivity.
  Qed.

  Theorem rev_involutive : ∀ {A : Type} (l : list A),
      rev (rev l) = l.
  Proof.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite -> rev_app_distr.
      rewrite -> IHl'.
      reflexivity.
  Qed.

End L.

Import L.

Theorem silly3_firsttry : ∀ (n : nat),
     true = beq_nat n 5 →
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  apply H.
Qed.

Theorem rev_exercise1 : ∀ (l l' : list nat),
     l  = rev l' →
     l' = rev l.
Proof.
  intros l l' Eq₁.
  rewrite -> Eq₁.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Theorem trans_eq : ∀ (X:Type) (n m o : X),
  n = m → m = o → n = o.
Proof.
  intros X n m o Eq₁ Eq₂.
  rewrite -> Eq₁.
  rewrite -> Eq₂.
  reflexivity.
Qed.

Example trans_eq_example' : ∀ (a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c; d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise : ∀ (n m o p : nat),
     m = (minustwo o) →
     (n + p) = m →
     (n + p) = (minustwo o).
Proof.
  intros n m o p Eq₁ Eq₂.
  rewrite -> Eq₂.
  apply Eq₁.
Qed.

Theorem S_injective : ∀ (n m : nat),
  S n = S m →
  n = m.
Proof.
  intros n m Eq.
  inversion Eq.
  reflexivity.
Qed.

Theorem inversion_ex2 : ∀ (n m : nat),
  [n] = [m] →
  n = m.
Proof.
  intros n m Eq.
  inversion Eq as [Hnm].
  reflexivity.
Qed.

Example inversion_ex3 : ∀ (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j →
  y :: l = x :: j →
  x = y.
Proof.
  intros X x y z l j Eq₁ Eq₂.
  inversion Eq₂.
  reflexivity.
Qed.

Theorem beq_nat_0_l : ∀ n,
    beq_nat 0 n = true → n = 0.
Proof.
  intros n Eq.
  destruct n as [|n'].
  - reflexivity.
  - inversion Eq.
Qed.

Theorem inversion_ex4 : ∀ (n : nat),
  S n = O →
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem S_inj : ∀ (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b →
     beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : ∀ (n : nat),
  (beq_nat n 5 = true → beq_nat (S (S n)) 7 = true) →
  true = beq_nat n 5 →
  true = beq_nat (S (S n)) 7.
Proof.
  intros n Eq₁ Eq₂.
  simpl.
  apply Eq₂.
Qed.

Theorem m_plus_m_zero : ∀ m,
    m + m = 0 →
    m = 0.
Proof.
  intros m Eq.
  destruct m. 
  - reflexivity.
  - inversion Eq.
Qed.

Theorem S_m_m_eq_m : ∀ m,
    S O = O →
    S (S m) = S m.
Proof.
  intros m contra.
  destruct m.
  - inversion contra.
  - inversion contra.
Qed.

Theorem plus_n_n_injective : ∀ n m,
     n + n = m + m →
     n = m.
Proof.
  intros n m Eq.
 (* rewrite <- plus_id_example.*)
  
  
  induction n as [| n']. 
  - simpl in Eq.
    symmetry in Eq.
    apply m_plus_m_zero in Eq.
    symmetry.
    apply Eq.
  - rewrite -> IHn'.
    + destruct m.
      * inversion Eq.
      * apply S_m_m_eq_m.
        
        
    (*simpl in Eq.
    rewrite -> plus_n_Sm in Eq.
    symmetry in Eq.
    rewrite -> IHn'.*)
    