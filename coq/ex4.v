Set Warnings "-notation-overridden,-parsing".
(*Require Export Lists.*)
Require Import Coq.Unicode.Utf8.
Require Import Basics.

Module Lists.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X → list X → list X.

Arguments nil {X}.

Arguments cons {X} _ _.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Check (cons 1 (cons 2 (cons 3 nil))).

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Notation "x ++ y" := (app x y) (at level 60, right associativity).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons 4 (cons 4 nil).
Proof.
  reflexivity.
Qed.

Definition list123 :=
  cons 1 (cons 2 (cons 3 nil)).

Definition list123' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat' x count')
  end.

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * X) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y : Type} (xs : list X) (ys : list Y) : list (X * Y) :=
  match (xs, ys) with
  | ([], _) => []
  | (_, []) => []
  | (x :: xs', y :: ys') => (x, y) :: (combine xs' ys')
  end.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint map {X Y : Type} (f : X → Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | (x :: xs) => (f x) :: map (*X Y*) f xs
  end.

(*Arguments map {X} {Y} _ _.*)

Inductive option (X : Type) : Type :=
  | Some : X → option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | (x :: xs) => Some x
  end.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof.
  reflexivity.
Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof.
  reflexivity.
Qed.

Fixpoint filter {X : Type} (test : X → bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | (h :: t) => if test h then h :: (filter test t) else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Fixpoint gtb (x : nat) (y : nat) : bool :=
  match (x, y) with
  | (_, 0) => false
  | (0, _) => true
  | ((S n), (S m)) => gtb n m
  end.

Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (gtb 7 x) (evenb x)) l.

Compute filter_even_gt7 [1;2;3;4;5;6;7;8;9].

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
  reflexivity.
Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof.
  reflexivity.
Qed.

Definition partition {X : Type} (test : X → bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun x => notb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
  reflexivity.
Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
  reflexivity.
Qed.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Definition id {X : Type} (x : X) := x.

Theorem map_id : ∀ (X : Type) (l : list X),
    map id l = l.
Proof.
  intros X l.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Lemma distrib_map : ∀ (X Y : Type) (f : X → Y) (l : list X) (h : list X),
  map f (l ++ h) = (map f l) ++ (map f h).
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.

Theorem map_rev : ∀ (X Y : Type) (f : X → Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite <- IHl.
    apply distrib_map.
Qed.
    