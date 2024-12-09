Require Import Coq.Arith.Arith.
Require Import List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* An inductive type for binary search trees *)
Inductive BST :=
  | Leaf : BST
  | Node : BST -> nat -> BST -> BST.

(* Verifies that a list of elements is sorted (with fuel). *)
Fixpoint sorted_aux (len : nat) (q : list nat) : bool :=
    match len with
    | 0 => true
    | S len' =>
        match q with
        | [] => true
        | h :: [] => true
        | h1 :: h2 :: t => 
            andb (Nat.leb h1 h2)
            (sorted_aux len' (h2 :: t))
        end
    end.


(*  Verifies that a list of elements is sorted
    with a given function mapping elements to nats. *)
Definition sorted (q : list nat) : bool :=
    sorted_aux (length q) q.

(* Append two lists together *)
Fixpoint append {A : Type} (lst1 : list A) (lst2 : list A) : list A :=
match lst1 with
    | [] => lst2
    | h :: t => h :: (append t lst2)
end.

(* Insert element into BST in order *)
Fixpoint insert (n : nat) (t : BST) : BST := match t with
| Leaf => Node Leaf n Leaf
| Node l v r =>
    if Nat.eqb n v then Node l v r else
    if Nat.ltb n v then Node (insert n l) v r else
    Node l v (insert n r)
end.

(* Inorder traversal of a BST *)
Fixpoint inorder (t : BST) : list nat := match t with
| Leaf => []
| Node l v r => append (inorder l) (v :: inorder r)
end.

Theorem neq_sym : forall A (a b : A), a <> b -> b <> a.
Proof.
  intros A a b H.
  unfold not in *.
  intros Hba.  (* Assume b = a *)
  apply H.     (* Apply the original a <> b *)
  symmetry.    (* Use equality symmetry *)
  exact Hba.   (* Now a = b, contradiction *)
Qed.

(* Proof that an inorder traversal returns the tree sorted *)
Lemma inorder_is_sorted (t : BST) (n : nat) :
    sorted (inorder t) = true -> sorted (inorder (insert n t)) = true.
Proof.
    induction t.
    - unfold sorted. simpl. reflexivity.
    - intros. simpl. case_eq (Nat.eqb n0 n); intros Heq.
        + apply Nat.eqb_eq in Heq. symmetry in Heq.
        rewrite <- Nat.eqb_eq in Heq. rewrite Heq. exact H.
        + case_eq (Nat.ltb n0 n); intros Hlt.
            * simpl. apply Nat.eqb_neq in Heq. apply neq_sym in Heq.
              rewrite <- Nat.eqb_neq in Heq. rewrite Heq.
              apply Nat.ltb_lt in Hlt. apply Nat.lt_asymm in Hlt. admit. 
            * simpl. apply Nat.eqb_neq in Heq. apply neq_sym in Heq.
              rewrite <- Nat.eqb_neq in Heq. rewrite Heq.
              apply Nat.ltb_nlt in Hlt. apply Nat.nlt_ge in Hlt.
              apply Nat.eqb_neq in Heq. case_eq (Nat.ltb n n0).
                { intros. apply Nat.ltb_lt in H0. apply Nat.lt_asymm in H0.
                unfold inorder. simpl. destruct t2.
                    { destruct t1.
                        { simpl. unfold sorted. unfold sorted_aux. simpl.
                            rewrite andb_true_iff. split.
                            - apply Nat.leb_le. exact Hlt.
                            - reflexivity.  
                        }
                        { admit. }  
                    }
                    { destruct t1.
                        { simpl. unfold sorted. unfold sorted_aux. simpl.
                            rewrite andb_true_iff. split.
                            - apply Nat.leb_le in Hlt. exact Hlt.
                            - fold inorder. destruct (append (inorder t2_1) (n1 :: inorder t2_2)).
                                + reflexivity.
                                + rewrite andb_true_iff. fold sorted_aux. split.  
                        
                        }
                        { }
                    }
                  
                  admit. 
                
                }
                { intros. apply Nat.ltb_nlt in H0. apply Nat.nlt_ge in H0.
                  admit. } 
Admitted.