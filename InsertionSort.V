Require Import Coq.Arith.Arith.
Require Import List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* A formalization of the insertion sort algorithm in Coq, and a mechanized proof of its correctness. *)


(*  Insert element into a list of elements sorted
    by some comparator function between elements.
    f pkt1 pkt2 returns 0 if pkt1 <= pkt2, 1 otherwise.
*)
Fixpoint insert_sorted {A : Type} (q : list A) (pkt : A) (f : A -> nat) := 
    match q with
    | [] => [pkt]
    | h :: t =>
        if Nat.leb (f pkt) (f h) then pkt :: q
        else h :: (insert_sorted t pkt f)
    end.

(*  Auxiliary sorting function on lists of elements with fuel.
    f pkt1 pkt2 returns 0 if pkt1 <= pkt2, 1 otherwise.
*)
Fixpoint sort_aux {A : Type} (fuel : nat) (q : list A) (f : A -> nat) :=
    match fuel with
    | 0 => []
    | S fuel' => match q with
        | [] => []
        | h :: t => insert_sorted (sort_aux fuel' t f) h f
        end
    end.

(* Sort a list given a function mapping elements to nats. *)
Definition sort {A : Type} (q : list A) (f : A -> nat) := sort_aux (length q) q f.

(* Verifies that a list of elements is sorted (with fuel). *)
Fixpoint sorted_aux {A : Type} (len : nat) (q : list A) (f : A -> nat) : bool :=
    match len with
    | 0 => true
    | S len' =>
        match q with
        | [] => true
        | h :: [] => true
        | h1 :: h2 :: t => 
            andb (Nat.leb (f h1) (f h2))
            (sorted_aux len' (h2 :: t) f)
        end
    end.


(*  Verifies that a list of elements is sorted
    with a given function mapping elements to nats. *)
Definition sorted {A : Type} (q : list A) (f : A -> nat) : bool :=
    sorted_aux (length q) q f.

(* Appending an element increments the length of a list. *)
Lemma list_length : forall {A : Type} (a : A) (lst: list A), length (a :: lst) = S (length lst).
Proof.
    induction lst.
    - simpl. reflexivity.
    - simpl. reflexivity. 
Qed.

(* Inverse of list_length - taking the tail of a list decrements its length. *)
Lemma tail_length : forall {A : Type} (a : A) (lst: list A) (n : nat),
    length (a :: lst) = (S n) -> length lst = n.
Proof.
    intros. simpl in H. inversion H. reflexivity.
Qed.

(* Proof that the tail of a list is sorted if the entire list is sorted. *)
Lemma tail_sorted : forall {A : Type} (h : A) (f : A -> nat) (t : list A),
    sorted (h :: t) f = true -> sorted (t) f = true.
Proof.
    unfold sorted. simpl. intros. destruct t.
    - reflexivity.
    - rewrite andb_true_iff in H. destruct H as [_ HMain]. exact HMain.
Qed.

(* Important rule that if a two-element list is sorted, the first two elements are in order. *)
Lemma sorted_meaning : forall {A : Type} (h1 h2 : A) (tl : list A) (f : A -> nat),
    sorted (h1 :: h2 :: tl) f = true -> Nat.leb (f h1) (f h2) = true.
Proof.
    unfold sorted. destruct tl.
    - simpl. intros. apply andb_prop in H. destruct H as [H' _]. exact H'.
    - simpl. intros. apply andb_prop in H. destruct H as [H' _]. exact H'.
Qed.

Lemma heads_same : forall {A : Type} (h1 h1' : A) (t1 t1' : list A), 
    (h1 :: t1 = h1' :: t1') -> h1 = h1'.
Proof.
    induction t1.
    - simpl. intros. inversion H. reflexivity.
    - simpl. intros. inversion H. reflexivity.
Qed.

(* Show that inserting into a sorted list preserves sortedness. *)
Lemma insert_preservation : forall {A : Type} (pkt : A) (f : A -> nat) (q : list A),
    (sorted q f) = true -> sorted (insert_sorted q pkt f) f = true.
Proof.
    (* h_init :: t_init form the initial head/tail of q *)
    induction q as [| h_init t_init].
    - unfold sorted. simpl. reflexivity.
    (* Split on structure of insertion sort – whether f pkt <= f h_init or otherwise. *)
    - case_eq (Nat.leb (f pkt) (f h_init)); intros Hle.
        
        (* Here, assume f pkt <= f h_init. *)
        (* Split cases on length to get past fuel constraint *)
        + intros H. simpl. unfold sorted. rewrite Hle. case_eq (length (pkt :: h_init :: t_init)).
            (* Matches base case (length 0) *)
            * simpl. intros H1. reflexivity.
            (* Matches nontrivial case that moves to list pattern matching *)
            * simpl. intros n H1. rewrite Hle. unfold sorted in H. symmetry in H1.
            apply eq_add_S in H1. rewrite H1. rewrite list_length in H. exact H.
        + intros H. simpl. rewrite Hle. unfold sorted. 
        
        (* Here, assume f pkt > f h_init. *)
        (* Split cases on length to get past fuel constraint *)
        case_eq (length (h_init :: insert_sorted t_init pkt f)).
            (* Matches base case (length 0) *)
            * simpl. intros HImp. reflexivity.
            (* Matches nontrivial case that moves to list pattern matching *)

            * intros n HSucc. simpl.
              remember (insert_sorted t_init pkt f) as sort_insert_tail.
              (* hd_of_tail :: tl_of_tail is the result of inserting pkt into the initial tail, t_init. *)
              destruct sort_insert_tail as [| hd_of_tail tl_of_tail].
                { reflexivity. }
                { apply andb_true_intro. split.
                    {
                    (* Show that the head element <= second element *)
                    case_eq ((Nat.leb (f hd_of_tail) (f pkt))).
                        {
                            intros H_hdpi_ge. apply Nat.leb_le.
                            case_eq (Nat.ltb (f hd_of_tail) (f pkt)).
                            {
                                (* Case – hd_of_tail < pkt. Here, rely on the sortedness.
                                    Since hd_of_tail is not pkt, it was in the list before pkt was inserted.
                                    In fact, h_init and hd_of_tail should be the exact same.
                                *)

                                intros H_hdpi_lt. subst. simpl in H.
                                symmetry in Heqsort_insert_tail.

                                (* Head of tail, tail of tail *)
                                unfold insert_sorted in Heqsort_insert_tail. destruct t_init as [| t_head t_tl].
                                { (* Empty list *)
                                    apply heads_same in Heqsort_insert_tail. apply Nat.leb_nle in Hle. apply Nat.nle_gt in Hle.
                                    rewrite Heqsort_insert_tail in Hle. apply Nat.lt_le_incl in Hle. exact Hle.
                                }
                                {
                                   (* Nonempty list *)
                                   case_eq (Nat.leb (f pkt) (f t_head)).
                                   { (* element lies before tail. *)
                                        intros. rewrite H0 in Heqsort_insert_tail.
                                        apply heads_same in Heqsort_insert_tail.
                                        rewrite Heqsort_insert_tail in Hle.
                                        apply Nat.leb_nle in Hle. apply Nat.nle_gt in Hle.
                                        apply Nat.lt_le_incl in Hle. exact Hle.
                                   }
                                   { (* element lies somewhere after tail. Utilize initial hypothesis, 
                                        and sorting heads lemmas. *)
                                        intros. rewrite H0 in Heqsort_insert_tail.
                                        apply heads_same in Heqsort_insert_tail.
                                        rewrite Heqsort_insert_tail in H.
                                        apply sorted_meaning in H. apply Nat.leb_le in H. exact H.
                                   }
                                }
                            }
                            { (* Case – hd_of_tail = pkt. Here, just use HLE. *)
                                intros. 
                                apply Nat.ltb_nlt in H0. apply Nat.nlt_ge in H0.
                                apply Nat.leb_nle in Hle. apply Nat.nle_gt in Hle.
                                apply Nat.leb_le in H_hdpi_ge. apply Nat.le_antisymm in H0.
                                symmetry in H0. rewrite H0 in Hle. apply Nat.lt_le_incl in Hle.
                                exact Hle. exact H_hdpi_ge.
                            }
                        }
                        { (* Case – hd_of_tail > pkt. 
                             If this happens, use transitivity that h_init <= pkt. *)
                            intros H_hdpi_ge. apply Nat.leb_le.
                            apply Nat.leb_nle in H_hdpi_ge. apply Nat.nle_gt in H_hdpi_ge.
                            apply Nat.leb_nle in Hle. apply Nat.nle_gt in Hle.
                            apply (Nat.lt_trans (f h_init) (f pkt) (f hd_of_tail)) in H_hdpi_ge.
                            apply Nat.lt_le_incl in H_hdpi_ge. exact H_hdpi_ge. exact Hle.    
                        }                    
                    }
                    (* Tail is sorted – use tail sorted lemma nd equate to IH. *)
                    { apply tail_sorted in H. rewrite H in IHt_init.
                      unfold sorted in IHt_init. specialize (IHt_init eq_refl).
                      apply tail_length in HSucc. rewrite HSucc in IHt_init. exact IHt_init.
                    }
                }
Qed.

(* THEOREM - CORRECTNESS OF SORTING.
    - Proves that our insertion sort algorithm sorts
      any list given a valid comparator function.
 *)
Theorem sorting_works : forall {A : Type} (q : list A) (f : A -> nat),
    sorted (sort q f) f = true.
Proof.
    induction q.
    - unfold sort. unfold sorted. simpl. reflexivity.
    (* Split cases on length to get past fuel constraint *)
    - intros. unfold sort. case_eq (length (a :: q)); intros n.
        (* Base case *)
        + unfold sorted. simpl. reflexivity.
        (* Apply preservation of insertion lemma. *)
        + simpl. intros. unfold sort in IHq.
          apply eq_add_S in H. rewrite H in IHq.
          apply insert_preservation. revert f. exact IHq. 
Qed.