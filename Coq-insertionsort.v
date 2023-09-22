(*  This is a totally correct polymorphic implementation of insertion sort.
 *  Finished 19th August 2023 by Harrison Oates.
 *)

Require Import Nat.
Require Import Relations.
Require Import List.
Require Import Multiset.
Import ListNotations.

Variable A : Set.
Variable compare : A -> A -> bool.
Variable leq : A -> A -> Prop.

Hypothesis leq_trans : forall a b c, leq a b -> leq b c -> leq a c.
Hypothesis leq_total : forall a b, if compare a b then leq a b else leq b a.

Variable eqA : relation A.
Hypothesis eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y}.

Let emptyBag := EmptyBag A.
Let singletonBag := SingletonBag _ eqA_dec.

Inductive sorted : list A -> Prop := 
| sorted_nil : sorted []
| sorted_singleton : forall n, sorted [n]
| sorted_cons : forall n m p, leq n m -> sorted (m :: p) -> sorted (n :: m :: p).

Fixpoint list_contents (l:list A) : multiset A :=
    match l with
      | nil => emptyBag
      | a :: l => munion (singletonBag a) (list_contents l)
    end.

(* The functions we are trying to prove the correctness of *)
Fixpoint insert (i : A) (l : list A) :=
    match l with
    | [] => [i]
    | x :: xs => if compare i x then (i :: x :: xs) else (x :: insert i xs)
    end.

Fixpoint sort (l : list A) : list A :=
    match l with
    | [] => []
    | x :: xs => insert x (sort xs)
    end.

Theorem insertion_contents_consistent: forall x l,
    meq (list_contents (insert x l)) (list_contents (x :: l)).
Proof.
    intros.
    induction l as [ | h t IH].
    - simpl. unfold meq. intros. reflexivity.
    - simpl. case_eq (compare x h).
        + intros. simpl. unfold meq. intros. reflexivity.
        + intros.  simpl. unfold meq. intros. simpl. unfold meq in IH. rewrite IH. simpl. 
            destruct (eqA_dec h a). destruct (eqA_dec x a). 
            reflexivity.
            reflexivity.
            reflexivity.
Qed.

Theorem sort_contents: forall l,
    meq (list_contents l) (list_contents (sort l)).
Proof.
    intros.
    induction l as [ | h t IH].
    - simpl. unfold meq. reflexivity.
    - simpl. unfold meq in IH. unfold meq. intros.
    simpl. rewrite IH. rewrite insertion_contents_consistent. reflexivity.
Qed.

Lemma insert_is_sorted: forall l a,
    sorted l -> sorted (insert a l).
Proof.
intros a l S. induction S; simpl.
    - apply sorted_singleton.
    - case_eq (compare l n).
        + intros. apply sorted_cons. pose proof (leq_total l n) as L.
            rewrite H in L. apply L.
            apply sorted_singleton.
        + intros.  apply sorted_cons. pose proof (leq_total l n) as L.
            rewrite H in L. apply L.
            apply sorted_singleton.
    - case_eq (compare l m).
        + intros.
            case_eq (compare l n).
            * intros.
                apply sorted_cons. pose proof (leq_total l n) as L.
                rewrite H1 in L. apply L.
                apply sorted_cons. apply H. apply S.
            * intros. pose proof (leq_total l n) as L.
                apply sorted_cons.
                rewrite H1 in L.
                apply L.
                apply sorted_cons.
                pose proof (leq_total l m) as L2.
                rewrite H0 in L2.
                apply L2.
                apply S. 
        + intros.
            case_eq (compare l n).
            * intros.
                apply sorted_cons. pose proof (leq_total l n) as L.
                rewrite H1 in L. apply L.
                apply sorted_cons. apply H.
                apply S. 
            * intros.
                apply sorted_cons.
                apply H.
                simpl in IHS. rewrite H0 in IHS.
                apply IHS.
Qed.

Theorem insertion_sort_is_correct: forall l,
    (meq (list_contents l) (list_contents (sort l))) /\ sorted (sort l).
Proof.
    intros.
    split.
    apply sort_contents.
    induction l as [ | h t IH].
    - simpl. apply sorted_nil.
    - simpl. apply insert_is_sorted. apply IH.
Qed.  