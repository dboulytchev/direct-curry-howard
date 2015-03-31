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
   lt_tree n l -> gt_tree n r -> is_search_tree l -> is_search_tree r -> 
   is_search_tree (node n l r).

Inductive contains : nat -> tree -> Prop :=
  root_contains : forall (n : nat) (l r : tree), contains n (node n l r)
| left_contains : forall (n m : nat) (l r : tree), 
   contains n l -> contains n (node m l r)
| right_contains : forall (n m : nat) (l r : tree), 
   contains n r -> contains n (node m l r).

Hint Constructors lt_tree gt_tree is_search_tree contains.

Lemma rt_contains: forall (n m : nat), contains m (node n leaf leaf) -> m = n.
Proof. intros. inversion H; try omega; inversion H2. Qed.

Lemma gt_contains : forall (t : tree) (n : nat), 
  (forall m, contains m t -> m > n) -> gt_tree n t.
Proof. intros. induction t; auto. Qed.

Lemma lt_contains : forall (t : tree) (n : nat),
  (forall m, contains m t -> m < n) -> lt_tree n t.
Proof. intros. induction t; auto. Qed.

Lemma left_lt : forall (n m : nat) (l r : tree), 
  is_search_tree (node n l r) -> contains m l -> m < n.
Proof.
  intros. induction l. inversion H0. 
    inversion H. inversion H0. inversion H4. omega.
      apply IHl1. apply st_node. 
       inversion H4. assumption. assumption.
       inversion H6. assumption. assumption. assumption.
      apply IHl2. apply st_node. 
       inversion H4. assumption. assumption.
       inversion H6. assumption. assumption. assumption.
Qed.

Lemma right_gt : forall (n m : nat) (l r : tree), 
  is_search_tree (node n l r) -> contains m r -> m > n.
Proof. 
  intros. induction r. inversion H0. 
    inversion H. inversion H0. inversion H5. omega.
      apply IHr1. apply st_node. assumption.
       inversion H5. assumption. assumption. 
       inversion H7. assumption. assumption. 
      apply IHr2. apply st_node. assumption.
       inversion H5. assumption. assumption.
       inversion H7. assumption. assumption.
Qed.

Definition add_in_search_tree : forall (t : tree) (n : nat),
  is_search_tree t -> 
  {t' | is_search_tree t' & 
        (forall (m : nat), contains m t' <-> m = n \/ contains m t)
  }.
Proof.
  intros. induction t. 
    exists (node n leaf leaf). 
       auto. intros. split. intros. left. 
       apply rt_contains in H0. assumption. 
       intros. inversion H0. rewrite H1. auto. inversion H1.    
    assert (L: is_search_tree t1). inversion H. auto.
    assert (LT: lt_tree n0 t1). inversion H. auto.
    assert (R: is_search_tree t2). inversion H. auto.
    assert (GT: gt_tree n0 t2). inversion H. auto.
    remember (lt_eq_lt_dec n n0) as B. 
      inversion B. inversion H0. 
        apply IHt1 in L. inversion L. 
          exists (node n0 x t2).
            apply st_node. apply lt_contains. intros. apply H3 in H4. 
                inversion H4. omega. apply (left_lt n0 m t1 t2); assumption.
              assumption. assumption. assumption.
            intros. split. intros. 
              inversion H4. right. auto. 
                apply H3 in H7. inversion H7. left. assumption. right. auto. right. auto.
            intros. inversion H4. rewrite H5.
              apply left_contains. apply H3. left. reflexivity.
              inversion H5. auto. apply left_contains. apply H3. right. assumption.
                apply right_contains. assumption.
        exists (node n0 t1 t2). assumption. 
          intros. split. intros. right. assumption. intros. inversion H2.
            rewrite <- H1. rewrite H3. auto. assumption.
        apply IHt2 in R. inversion R.
          exists (node n0 t1 x).
            apply st_node. assumption. apply gt_contains. intros. apply H2 in H3.
                inversion H3. omega. apply (right_gt n0 m t1 t2); assumption.  
              assumption. assumption.
            intros. split. intros. 
              inversion H3. right. auto.
                right. apply left_contains. assumption. 
                apply H2 in H6. inversion H6. left. assumption. right. 
                apply right_contains. assumption.
            intros. inversion H3. apply right_contains. apply H2. left. assumption.
                inversion H4. auto. apply left_contains. assumption.
                apply right_contains. apply H2. right. assumption.
Qed.

Fixpoint height (t: tree) : nat := 
  match t with
  | leaf => 0
  | node _ l r => 1 + max (height l) (height r)
  end.

