From LF Require Export Basics.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

Proof.
  intros n.  induction n as [|n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof. intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

 
(* Exercise: 2 stars, recommended (basic_induction) *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof. intros n. induction n as [|n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed. 


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. intros n m. induction n as [|n' IHn'].
 - (* n = 0 *)
    simpl. reflexivity.
 - (* n = S n' *) 
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. intros n. induction n as [| n' IHn' ].
  - (* n = 0 *)
    simpl. intros m. rewrite <- plus_n_O_firsttry. reflexivity.
  - (* n = S n' *)
    intros m. simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn'].   
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.



(* Exercise: 2 stars (double_plus)
Consider the following function, which doubles its argument:
*)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* Use induction to prove this simple fact about double: *)

Lemma double_plus : forall n, double n = n + n .
Proof. intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

 

(* Exercise: 2 stars, optional (evenb_S)
One inconvenient aspect of our definition of evenb n is the recursive call on n - 2. 
This makes proofs about evenb n harder when done by induction on n, since we may need an induction hypothesis about n - 2. 
The following lemma gives an alternative characterization of evenb (S n) that works better with induction: *)

Lemma negb_negb_b : forall b : bool,
  negb (negb b) = b.
Proof. intros b. destruct b as [| b'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof. intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'. simpl.  rewrite negb_negb_b. simpl. reflexivity.
Qed.
  

(* Exercise: 1 star (destruct_induction)
Briefly explain the difference between the tactics destruct and induction. *)
(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_destruct_induction : option (prod nat string) := None.


  