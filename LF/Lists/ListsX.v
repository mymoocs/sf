From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.


Definition fst (p : natprod) : nat := 


Definition snd (p : natprod) : nat :=

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=

Definition snd' (p : natprod) : nat :=
 

Definition swap_pair (p : natprod) : natprod :=
 

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.


Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.


Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.


Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.

(* Lists of Numbers *)
Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.



Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint repeat (n count : nat) : natlist :=


Fixpoint length (l:natlist) : nat :=

Fixpoint app (l1 l2 : natlist) : natlist :=


Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.


(* Head (with default) and Tail *)

Definition hd (default:nat) (l:natlist) : nat :=

Definition tl (l:natlist) : natlist :=

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

