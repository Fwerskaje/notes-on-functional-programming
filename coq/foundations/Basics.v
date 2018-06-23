Require Import Coq.Unicode.Utf8.

Module NatPlayground.

  Inductive nat : Type :=
  | O : nat
  | S : nat → nat.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | (S k) => k
    end.

  Check (S (S (S O))).

  Fixpoint plus (x y : nat) : nat :=
    match x with
    | O => y
    | (S k) => (S (plus k y))
    end.

  Compute plus (S (S O)) (S (S (S O))).

  Fixpoint mult (x y : nat) : nat :=
    match x with
    | O => O
    | (S k) => plus y (mult k y)
    end.

  Compute mult (S (S (S O))) (S (S O)).

  Example test_mult : (mult (S (S (S O))) (S (S (S O))))
                       = (S (S (S (S (S (S (S (S (S O))))))))).
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (x y : nat) : nat :=
    match (x, y) with
    | (O, _) => O
    | (S _, O) => x
    | (S n, S k) => minus n k
    end.

  Notation "x + y" := (plus x y) (at level 50, left associativity) . 

  Notation "x - y" := (minus x y) (at level 50, left associativity).

  Notation "x × y" := (mult x y) (at level 40, left associativity).

  Compute (S (S O)) + (S (S O)) × (S (S O)).
  
End NatPlayground.

Check (S (S (S O))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | (S O) => O
  | (S (S k)) => k
  end.

Compute (minustwo 4).

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | (S O) => false
  | (S (S k)) => evenb k
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Check mult.

(* Ex 1 *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => O
  | (S O) => (S O)
  | (S k) => mult n (factorial k) 
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(* Ex2 *)

(* Потом сделаю, лучше буду прувить *)

Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l : ∀  n : nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example : ∀ n m : nat, n = m → n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

(* Ex 3 *)
Theorem plus_id_exercise : ∀ n m o : nat, n = m → m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros J.
  rewrite -> H.
  rewrite <- J.
  reflexivity.
Qed.

Theorem mult_0_plus : ∀ n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem plus_1_S_n : ∀ n : nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

(* Ex 4 *)
Theorem mult_S_1 : ∀ n m : nat, m = S n → m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_S_n.
  rewrite <- H.
  reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_1_neq_0_firsttry : ∀ n : nat, beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(*

∧-commutative : ∀ (b c : 𝔹) -> (b ∧ c) ≡ (c ∧ b)
∧-commutative tt tt = refl
∧-commutative tt ff = refl
∧-commutative ff tt = refl
∧-commutative ff ff = refl

 *)

Theorem plus_1_neq_0' : ∀ n : nat, beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' : ∀ b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*
∧-true-elim : ∀ (b c : 𝔹) → (b ∧ c) ≡ tt → c ≡ tt
∧-true-elim tt c p = p -- Hm~
∧-true-elim ff tt p = refl
∧-true-elim ff ff ()
*)

Theorem andb_true_elim2 : ∀ b c : bool, andb b c = true → c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
  - reflexivity.
  - rewrite <- H.
    destruct b.
    + reflexivity.
    + reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : ∀ n : nat, beq_nat 0 (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

(* Ex *)

Theorem identity_fn_applied_twice :
  ∀ (f : bool → bool), (∀ (x : bool), f x = x) → ∀ (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x.
  rewrite -> x.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  ∀ (f : bool → bool), (∀ (x : bool), f x = negb x) → ∀ (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x.
  rewrite -> x.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(*
∧-eq-∨ : ∀ (b c : 𝔹) -> (b ∧ c) ≡ (b ∨ c) → b ≡ c
∧-eq-∨ tt .tt refl = refl
∧-eq-∨ ff tt ()
∧-eq-∨ ff ff refl = refl
*)

(*
Theorem andb_eq_orb : ∀ (b c : bool), (andb b c = orb b c) → b = c.
Proof.
  intros b c H. (* TODO *)
 *)

(* Ex *)
Inductive bin : Type :=
| BO : bin (* 0 *)
| BS : bin -> bin (* 1 + n *)
| BTwice : bin -> bin. (* 2 × n *)

(* 
TODO
Спорно. Надо переделать.
Definition incr (n : bin) : bin :=
  match n with
  | BO => BS BO (* 0 + 1 *)
  | (BS BO) => (BS (BS BO)) (* ≠ 2 * 0, 1 + 1 + 0 *)
  | (BS k) => BTwice k (* косяк *)
  | (BTwice k) => BS (BTwice k)
  end.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | BO => 0
  | (BS k) => 1 + (bin_to_nat k)
  | (BTwice k) => 2 * (bin_to_nat k)
  end.

Compute (BTwice (BS (BTwice (BS BO)))).

(* Test with zero *)

Example test_bin_incr1 :
  bin_to_nat (incr (incr (BTwice (BTwice (BS BO))))) = 6.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr2 : (incr (incr (incr (incr BO)))) = (BTwice ().
Proof.
  reflexivity.
Qed.
*)