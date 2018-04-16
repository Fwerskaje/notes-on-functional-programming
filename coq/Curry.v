Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Unicode.Utf8.

Inductive ev : nat → Prop :=
| ev_0 : ev 0
| ev_SS : ∀ n, ev n → ev (S (S n)).

Check ev_SS.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Print ev_4.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Theorem ev_8 : ev 8.
Proof.
  apply (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).
Qed.

Definition ev_8' : ev 8 :=
  (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).

Theorem ev_plus4 : ∀ n, ev n → ev (4 + n).
Proof.
  intros n H.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
  Show Proof.
Qed.

Definition ev_plus4' : ∀ n, ev n → ev (4 + n) :=
  fun (n : nat) (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).