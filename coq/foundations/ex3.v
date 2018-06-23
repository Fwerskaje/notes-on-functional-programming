Require Import Coq.Unicode.Utf8.

Require Export Induction.
Require Export Basics.
Module NatList.

  Inductive natprod : Type :=
  | pair : nat → nat → natprod.

  Check (pair 3 4).

  Notation "( x , y )" := (pair x y).

  Definition fst (p : natprod) : nat :=
    match p with
    | (x,_) => x
    end.

  Compute fst (3,4).

  Definition snd (p : natprod) : nat :=
    match p with
    | (_,y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

  Compute snd (4,5).

Theorem surjective_pairing_stuck : ∀ (p : natprod),
  p = (fst p, snd p).
Proof.
  destruct p.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : ∀ (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : ∀ (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  destruct p.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat → natlist → natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute (repeat 10 42).

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | (_ :: xs) => 1 + (length xs)
  end.

Compute length [1; 2; 3; 4].

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | (x :: xs) => x :: (app xs l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Compute [1; 2; 3] ++ [4; 5; 6].

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | (x :: xs) => x
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | (x :: xs) => xs
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof.
  reflexivity.
Qed.

Example test_hd2: hd 0 [] = 0.
Proof.
  reflexivity.
Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof.
  reflexivity.
Qed.

Fixpoint filter (l : natlist) (p : nat → bool) : natlist :=
  match l with
  | nil => nil
  | (x :: xs) =>
    match p x with
    | true => x :: (filter xs p)
    | false => filter xs p
    end
  end.

Check beq_nat 0.
                   
Definition nonzeros (l : natlist) : natlist :=
  filter l (fun (x : nat) => negb (beq_nat x 0)).
(* I should use composition, but I dont know how *)

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  reflexivity.
Qed.

Definition oddmembers (l : natlist) : natlist := filter l oddb.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  reflexivity.
Qed.

Definition countoddmembers (l : natlist) : nat := length (oddmembers l).

Compute oddmembers [1;0;3;1;4;5].

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof.
  reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | (x :: xs) =>
    match l2 with
    | nil => l1
    | (y :: ys) => x :: y :: (alternate xs ys)
    end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
  reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
  reflexivity.
Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
  reflexivity.
Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
  reflexivity.
Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => 0
  | (x :: xs) =>
    match beq_nat x v with
    | true => 1 + (count v xs)
    | false => count v xs
    end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
  reflexivity.
Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof.
  reflexivity.
Qed.

Definition sum : bag → bag → bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
  reflexivity.
Qed.

Definition add (v : nat) (s : bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
  reflexivity.
Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
  reflexivity.
Qed.

Definition member (v : nat) (s : bag) : bool :=
  match (length s) - (length (filter s (fun x => negb (beq_nat x v)))) with
  | O => false
  | n => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof.
  reflexivity.
Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof.
  reflexivity.
Qed.

(* Exercise: 3 stars, optional (bag_more_functions)
Muh, boring *)

Theorem tl_length_pred : ∀ l : natlist,
    pred (length l) = length (tl l).
Proof.
  destruct l.
  - reflexivity.
  - reflexivity.
Qed.

Theorem app_assoc : ∀ l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | (x :: xs) => (rev xs) ++ [x]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof.
  reflexivity.
Qed.

Example test_rev2: rev nil = nil.
Proof.
  reflexivity.
Qed.

Theorem app_length : ∀ l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  induction l1 as [|n l' IHl'].
  - reflexivity.
  - intros l2.
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.    

Theorem rev_length_firsttry : ∀ l : natlist,
  length (rev l) = length l.
Proof.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite <- IHl'.
    rewrite -> app_length.
    rewrite -> plus_comm.
    simpl.
    reflexivity.
Qed.

Theorem app_nil_r : ∀ l : natlist,
  l ++ [] = l.
Proof.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_app_distr: ∀ l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [|n l1' IHl1'].
  - intros l2.
    simpl.
    rewrite -> app_nil_r.
    reflexivity.
  - intros l2.
    simpl.
    rewrite -> IHl1'.
    rewrite -> app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : ∀ l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_assoc4 : ∀ l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  induction l1 as [|n l1' IHl1'].
  - simpl.
    intros l2 l3 l4.
    rewrite <- app_assoc.
    reflexivity.
  - intros l2 l3 l4.
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

(* TODO *) (*
Lemma nonzeros_app : ∀ l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil =>
    match l2 with
    | nil => true
    | _ => false
    end
  | (x :: xs) =>
    match l2 with
    | nil => false
    | (y :: ys) =>
      match beq_nat x y with
      | true => beq_natlist xs ys
      | false => false
      end
    end
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof.
  reflexivity.
Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof.
  reflexivity.
Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof.
  reflexivity.
Qed.

Theorem beq_natlist_refl : ∀ l : natlist,
  true = beq_natlist l l.
Proof.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite <- IHl'.
    assert (H: beq_nat n n = true). {
      induction n as [|n' IHn'].
      + reflexivity.
      + simpl.
        rewrite -> IHn'.
        reflexivity.
    }
    rewrite -> H.
    reflexivity.
Qed.

(* Boring. *)

(* Exercise: 4 stars, advanced (rev_injective) *)
Theorem rev_inj : ∀ (l1 l2 : natlist), rev l1 = rev l2 → l1 = l2.
Proof.
  intros l1 l2 Eq.
  assert (H: rev (rev l1) = l1). {
    rewrite -> rev_involutive.
    reflexivity.
  }
  rewrite <- H.
  rewrite -> Eq.
  rewrite -> rev_involutive.
  reflexivity.
Qed.  

Inductive natoption : Type :=
  | Some : nat → natoption
  | None : natoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof.
  reflexivity.
Qed.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof.
  reflexivity.
Qed.

Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof.
  reflexivity.
Qed.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(* Exercise: 2 stars (hd_error) *)
(* Boring *)

Inductive id : Type :=
| Id : nat → id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : ∀ x, true = beq_id x x.
Proof.
  destruct x.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'.
    reflexivity.
Qed.

End NatList.

Module PartialMap.
  
  Export NatList.
  
  Inductive partial_map : Type :=
  | empty : partial_map
  | record : id → nat → partial_map → partial_map.

  Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
    record x value d.

  Fixpoint find (x : id) (d : partial_map) : natoption :=
    match d with
    | empty => None
    | record y v d' => if beq_id x y
                      then Some v
                      else find x d'
    end.

  Compute find (Id 2) (record (Id 1) 42 (record (Id 2) 16 empty)).

Theorem update_eq :
  ∀ (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem update_neq :
  ∀ (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false → find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

End PartialMap.
