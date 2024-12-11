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
    if Nat.eqb n v then Node l v r
    else
        if Nat.ltb n v then Node (insert n l) v r
        else Node l v (insert n r)
end.

(* Verifies that at BST is ordered *)
Fixpoint isBST (t : BST) : bool := match t with
| Leaf => true (* Vacuously tree*)
| Node l v r =>
    andb (andb (isBST l) (isBST r))
    (match l with
    | Leaf => match r with
        | Leaf => true (* Value with two leaf children *)
        | Node _ vr _ => Nat.ltb v vr (* One leaf, one child *)
        end
    | Node _ vl _ => andb (Nat.ltb vl v) (match r with
        | Leaf => true (* One child, one leaf*)
        | Node _ vr _ => (Nat.ltb v vr) (* Two children *)
        end)
    end)
end.

Lemma true_eq_true_imp_A : forall {A : Prop}, (true = true -> A) <-> A.
Proof.
  split.
  - intros H. apply H. reflexivity.
  - intros H _. exact H.
Qed.

Lemma insert_order : forall (t : BST) (n : nat), isBST t -> match insert n t 

(* Show that insertion does not change a BST's status *)

Lemma insert_preserves_BST (t : BST) (n : nat) :
    isBST t = true -> isBST (insert n t) = true.
Proof.
    (*  l is the left subtree.
        IHtl is its IH. v is the value.
        r is the right subtree.
        IHtr is its IH.
    *)
    induction t as [| l IHtl v r IHtr].
    (* Insert into Leaf. *)
    - simpl. reflexivity.

    (* Insert into Node(l, v, r). *)
    - intros. simpl. case_eq (Nat.eqb n v); intros H_v_eq_v.
        + exact H.
        + (* First tactic – show that left and right are balanced *)
            assert (H' := H). apply andb_true_iff in H. destruct H as [Hsubtrees _].
            apply andb_true_iff in Hsubtrees.  destruct Hsubtrees as [Hl Hr].
            fold isBST in Hl. fold isBST in Hr.
        
            case_eq (Nat.ltb n v) ; intros H_v_lt_v.
                * simpl. apply andb_true_iff. split.
                {
                    (* Left subtree preserves post insertion. *)
                    apply andb_true_iff. split. {
                        assert (IHtl_handy := IHtl). rewrite Hl in IHtl_handy. rewrite true_eq_true_imp_A in IHtl_handy. exact IHtl_handy.
                    }
                    (* Right subtree preserves. *)
                    exact Hr.
                }
                { case_eq (insert n l); intros H_insl_leaf.
                    (* Prove that right side is fine *)
                    - destruct r as [| rl rv rr].
                        + reflexivity.
                        + intros. unfold isBST in H'. apply andb_true_iff in H'.
                            destruct H' as [_ Hrec]. case_eq l; intros.
                            * rewrite H in Hrec. exact Hrec.
                            * rewrite H in Hrec. apply andb_true_iff in Hrec. destruct Hrec. exact H1. 
                    - (* Prove that left side is fine *)
                        intros. apply andb_true_iff. split.
                        (* Left side fine *)
                        + rewrite H in IHtl. apply IHtl in Hl. case_eq (Nat.leb n n0); intros H_n_le_n0.
                            * admit.
                            * apply Nat.ltb_lt in  H_v_lt_v. apply Nat.leb_nle in  H_n_le_n0.
                            apply Nat.nle_gt in H_n_le_n0. 
                            apply (Nat.lt_trans n0 n v) in H_n_le_n0. apply Nat.ltb_lt. exact H_n_le_n0. exact H_v_lt_v.
                        (* Rights side fine *)
                        + destruct r.
                            * reflexivity.
                            * unfold isBST in H'. apply andb_true_iff in H'.
                            destruct H' as [_ Hrec]. case_eq l; intros.
                                { 
                                    rewrite H0 in Hrec. exact Hrec.
                                }
                                {
                                    rewrite H0 in Hrec. apply andb_true_iff in Hrec.
                                    destruct Hrec. exact H2.
                                }
                }

                * simpl. apply andb_true_iff. split.
                {   
                    (* Left subtree preserves. *)
                    apply andb_true_iff. split. exact Hl. 
                    (* Right subtree preserves post insertion. *)
                    assert (IHtr_handy := IHtr). rewrite Hr in IHtr_handy. rewrite true_eq_true_imp_A in IHtr_handy. exact IHtr_handy.
                }
                {  case_eq (insert n r); intros H_insr_leaf.
                    (* Prove that left side is fine *)
                    - destruct l as [| ll lv lr].
                        + reflexivity.
                        + intros. unfold isBST in H'. apply andb_true_iff in H'.
                        destruct H' as [_ Hrec]. case_eq r; intros.
                            * rewrite H in Hrec. exact Hrec.
                            * apply andb_true_iff. split.
                                {
                                    rewrite H in Hrec. apply andb_true_iff in Hrec. destruct Hrec. exact H0.
                                }
                                {
                                    reflexivity.
                                }
                    - (* Prove that right side is fine *)
                        admit.
                }
Admitted. 

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