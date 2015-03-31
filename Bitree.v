Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.

Inductive tree : Set :=
  leaf : tree
| node : forall (n : nat) (left right : tree), tree.

Inductive lt_tree : nat -> tree -> Prop :=
  lt_leaf : forall (n   : nat), lt_tree n leaf
| lt_node : forall (n m : nat) (l r : tree), 
   m < n -> lt_tree n l -> lt_tree n r -> lt_tree n (node m l r).

Inductive gt_tree : nat -> tree -> Prop :=
  gt_leaf : forall (n   : nat), gt_tree n leaf
| gt_node : forall (n m : nat) (l r : tree), 
   m > n -> gt_tree n l -> gt_tree n r -> gt_tree n (node m l r).

Inductive is_search_tree : tree -> Prop :=
  st_leaf : is_search_tree leaf
| st_node : forall (n : nat) (l r : tree), 
   lt_tree n l -> is_search_tree l -> gt_tree n r -> is_search_tree r ->
   is_search_tree (node n l r).

Inductive contains : nat -> tree -> Prop :=
  root_contains : forall (n : nat) (l r : tree), contains n (node n l r)
| left_contains : forall (n m : nat) (l r : tree), 
   contains n l -> contains n (node m l r)
| right_contains : forall (n m : nat) (l r : tree), 
   contains n r -> contains n (node m l r).

Hint Constructors lt_tree gt_tree is_search_tree contains.

Lemma subtree_is_search_tree n l r : is_search_tree (node n l r) ->
                                     is_search_tree l /\ lt_tree n l /\
                                     is_search_tree r /\ gt_tree n r.
Proof. admit. Qed.

Lemma containsSmall n t : (forall x, contains x t -> n < x) -> gt_tree n t.
Proof. admit. Qed.

Lemma containsBig n t : (forall x, contains x t -> n > x) -> lt_tree n t.
Proof. admit. Qed.

Lemma containsInLT n t : lt_tree n t -> forall x, contains x t -> n > x.
Proof. admit. Qed.

Lemma containsInGT n t : gt_tree n t -> forall x, contains x t -> n < x.
Proof. admit. Qed.

Lemma lt_tree_trans n m t : lt_tree n t -> n < m -> lt_tree m t.
Proof. admit. Qed.

Lemma gt_tree_trans n m t : gt_tree n t -> n > m -> gt_tree m t.
Proof. admit. Qed.

Definition add_in_search_tree : forall (t : tree) (n : nat),
  is_search_tree t -> 
  {t' | is_search_tree t' & 
        contains n t' /\ (forall (m : nat), contains m t -> contains m t')
                      /\ (forall (m : nat), contains m t' -> m = n \/ contains m t)
  }.
Proof.
  intro t. induction t.
    intros m H1. exists (node m leaf leaf); auto.
      split; auto. split; auto.
        intros n H2. inversion H2; auto. 
    intros m H1.
      remember (subtree_is_search_tree _ _ _ H1) as H2.
        inversion H2. inversion H0. inversion H4.
          remember (lt_eq_lt_dec n m) as B1.
            inversion B1.
              inversion H7.
                remember (IHt2 m H5) as B2.
                  inversion B2.
                    exists (node n t1 x).
                      apply (st_node n t1 x); try assumption.
                        apply (containsSmall n x).
                          intros p C1. inversion H10. inversion H12.
                            remember (H14 p C1) as C2.
                              inversion C2. rewrite H15. assumption.
                                apply (containsInGT n t2 H6). assumption.
                      split.
                        apply right_contains.
                          inversion H10. assumption.
                        split.
                          intros p C1. inversion C1. constructor.
                            apply left_contains. assumption.
                            apply right_contains.
                              inversion H10. inversion H17.
                                apply H18. assumption.
                          intros p C1. inversion C1. right. constructor. 
                            right. apply left_contains. assumption.
                              inversion H10. inversion H17.
                                remember (H19 p H13) as C2.
                                  inversion C2.
                                    left. assumption.
                                    right. apply right_contains. assumption.
                exists (node n t1 t2). assumption.
                  rewrite<-H8. auto.
                remember (IHt1 m H) as B2.
                  inversion B2.
                    exists (node n x t2).
                      apply (st_node n x t2); try assumption.
                        apply (containsBig n x).
                          intros p C1. inversion H9. inversion H11.
                            remember (H13 p C1) as C2.
                              inversion C2. rewrite H14. assumption.
                                apply (containsInLT n t1 H3). assumption.
                      split.
                        apply left_contains.
                          inversion H9. assumption.
                        split.
                          intros p C1. inversion C1. constructor.
                            apply left_contains.
                              inversion H9. inversion H16.
                                apply H17. assumption.
                            apply right_contains. assumption.
                          intros p C1. inversion C1. right. constructor. 
                            inversion H9. inversion H16.
                              remember (H18 p H12) as C2.
                                inversion C2. left. assumption.
                                  right. apply left_contains. assumption.
                            right. apply right_contains. assumption.
Defined. 
            
Fixpoint height (t: tree) : nat := 
  match t with
  | leaf => 0
  | node _ l r => 1 + max (height l) (height r)
  end.

