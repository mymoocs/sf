Module NatPlayground.
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Print nat.
Eval compute in O.
Eval compute in (S O).
Eval compute in S(S O).

Fixpoint add (a b : nat) : nat := 
  match a with 
  | O => b
  | S n => S (add n b)
  end.   

Theorem add_assoc : forall (a b c : nat),
  (add a( add b c)) = (add (add a b) c).
Proof.
intros a b c.
induction a. simpl. reflexivity.
simpl. rewrite -> IHa. reflexivity.
Qed.

Print add_assoc.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition succ (n : nat) : nat := 
  match n with 
  | O => (S O)
  | s => (S s)
end.

Check (S (S (S (S O)))).

Fixpoint plus (n : nat) (m : nat) := 
  match n with 
  | O => m
  | S n' => plus n' (succ m)
end.
Compute plus (S (S (S O))) (S (S O)).

(*  plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O)))
      by the second clause of the match
==> S (S (plus (S O) (S (S O))))
      by the second clause of the match
==> S (S (S (plus O (S (S O)))))
      by the second clause of the match
==> S (S (S (S (S O))))
      by the first clause of the match
*)

End NatPlayground.

Compute (NatPlayground.succ NatPlayground.O).
Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Compute (oddb 4).
Example test_oddb2: (oddb 4) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minux (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
end.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
end.

(* Exercise: 1 star (factorial) *)
Fixpoint factorial (n:nat) : nat :=
  match n with 
  | O   => S O
  | S p => mult n (factorial p)
end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=  
  match (beq_nat n m) with
  | true => false
  | false => leb n m
end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

(* Proof by Rewriting *)
Theorem plus_id_example : forall n m:nat,
  n = m -> n + n = m + m.

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite <- H.
  reflexivity. Qed.


(* Exercise: 1 star (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros Hnm.
  rewrite <- Hnm.
  intros Hno.
  rewrite Hno.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite plus_O_n.
  reflexivity. 
Qed.
  
(*Exercise: 2 stars (mult_S_1) *)

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
 intros m n.
 simpl.
 intros H.
 rewrite <- H.
 reflexivity. 
Qed.

(*----------------------------------------------------------*)
(* Proof by Case Analysis *)


Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(*Lemma induction_test : forall n:nat, n = n -> n <= n.*)


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.


Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.


Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.


Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.


(*Exercise: 2 stars (andb_true_elim2) *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b.
  - destruct c.
      + simpl. reflexivity.
      + simpl.  intros J. rewrite J. reflexivity.
  - destruct c.
      + simpl. intros T. reflexivity.
      + simpl. intros T. rewrite T. reflexivity.
Qed.

(* Exercise: 1 star (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof. 
  intros n. destruct n as [ | n'].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(* More on Notation (Optional) *)


(* More Exercises *)
(* Exercise: 2 stars (boolean_functions) *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f. destruct b.
  - rewrite H. rewrite H. reflexivity. 
  - rewrite H. rewrite H. reflexivity.
Qed.
    

(* FILL IN HERE *)
(* The Import statement on the next line tells Coq to use the
   standard library String module.  We'll use strings more in later
   chapters, but for the moment we just need syntax for literal
   strings for the grader comments. *)
From Coq Require Export String.
(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (prod nat string) := None.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f. destruct b.
    - rewrite H. rewrite H. simpl. reflexivity.
    - rewrite H. rewrite H. simpl. reflexivity.
Qed.
    

(* Exercise: 3 stars, optional (andb_eq_orb) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->  b = c.
Proof.
  intros c. destruct c. 
    -intros b. simpl. intros H. rewrite H. reflexivity. 
    - intros b. simpl. intros H. rewrite <- H. reflexivity.
Qed.


(* Exercise: 3 stars (binary) *)
(* 
http://staff.ustc.edu.cn/~bjhua/courses/theory/2014/slides/lec1notes.html
http://kyledef.org/inzamam/2015/07/07/a-binary-number-system-in-coq/
https://www.cs.cmu.edu/~emc/15414-s14/assignment/hw2/Basics_w_ans.v
*)

Inductive bin : Type :=
           | Z  : bin
           | T  : bin -> bin
           | T' : bin -> bin.

   
Fixpoint inc (n : bin) : bin :=
  match n with
    | Z => T' Z
    | T t => T' t
    | T' n' => T (inc n')
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | Z => 0
  | T t => 2 *(bin_to_nat t)
  | T' t => 2 *(bin_to_nat t) + 1
  end.

Compute bin_to_nat (inc (inc Z)).

Example test_bin_incr1: bin_to_nat (inc (inc (inc Z))) = 3.
Proof. simpl. reflexivity. Qed.
(*
Fixpoint Simple_Collatz (b : bin) : bin :=
  match b with
    | Z => Z
    | T b' => Simple_Collatz b'
    | T' b' =>
      match b' with
        | Z => b
        | T b'' => Simple_Collatz (inc(b))
        | T' b'' => Simple_Collatz(inc(b))
      end
  end.
*)

