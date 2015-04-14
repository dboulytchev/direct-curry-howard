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

Lemma contains_in_lt n t : lt_tree n t -> forall x, contains x t -> n > x.
Proof. intros H; induction H; intros x Hi; inversion Hi; auto. Qed.

Lemma lt_insert x n (t : tree) (t' : tree) :
     n < x -> lt_tree x t ->
     (forall m, contains m t' -> m = n \/ contains m t) ->
     is_search_tree t' -> lt_tree x t'.
Proof.
  intros. apply lt_contains. intros.
    apply H1 in H3; destruct H3.
      rewrite H3; auto.
        apply (contains_in_lt x t); auto.
Qed.

Lemma contains_in_gt n t : gt_tree n t -> forall x, contains x t -> n < x.
Proof. intros H; induction H; intros x Hi; inversion Hi; auto. Qed.

Lemma gt_insert x n (t : tree) (t' : tree) :
     n > x -> gt_tree x t ->
     (forall m, contains m t' -> m = n \/ contains m t) ->
     is_search_tree t' -> gt_tree x t'.
Proof.
  intros. apply gt_contains. intros.
    apply H1 in H3; destruct H3.
      rewrite H3; auto.
        apply (contains_in_gt x t); auto.
Qed.

Program Fixpoint add_in_search_tree_prog (t : tree) (n : nat) :
    is_search_tree t ->
    {t' | is_search_tree t' /\
          (forall (m : nat), contains m t' <-> m = n \/ contains m t)
    } := fun H => 
  match t with
  | leaf       => node n leaf leaf
  | node x l r => match (lt_eq_lt_dec n x) with
                  | inleft LE => 
                    if LE
                    then let: nl := add_in_search_tree_prog l n _ in
                         node x nl r
                    else t
                  | inright GT =>
                         let: nr := add_in_search_tree_prog r n _ in
                         node x l nr
                  end
  end.
Next Obligation.
split; auto.
  intros m; clear H.
    split; intros H; inversion H; auto.
      rewrite H0; auto.
Qed.
Next Obligation. inversion H; auto. Qed.
Next Obligation.
  clear LE Heq_anonymous.
    split.
      apply st_node; inversion H; auto.
        apply (lt_insert x n l x0); auto.
          apply i0.
      intros m; split.
        intros X; inversion X; auto.
          apply (proj1 (i0 m)) in H3.
            inversion H3; auto.
        intros X; destruct X.
          assert (m = n \/ contains m l) as H2; auto.
            apply (i0 m) in H2; auto.
          inversion H1; auto.
            apply left_contains.
              apply i0; auto.
Defined.
Next Obligation.
clear LE Heq_anonymous.
  split; auto.
    intros m; split; intros X; inversion X; auto.
      rewrite H0; auto.      
Qed.      
Next Obligation. inversion H; auto. Qed.              
Next Obligation.        
  clear Heq_anonymous.
    split.
      apply st_node; inversion H; auto.    
        apply (gt_insert x n r x0); auto.
          apply i0.
      intros m; split.
        intros X; inversion X; auto.
          apply (proj1 (i0 m)) in H2.
            inversion H2; auto.
        intros X; destruct X.
          assert (m = n \/ contains m r) as H2; auto.
            apply (i0 m) in H2; auto.
          inversion H0; auto.
            apply right_contains.
              apply i0; auto.
Defined.  

Fixpoint height (t: tree) : nat := 
  match t with
  | leaf => 0
  | node _ l r => 1 + max (height l) (height r)
  end.

Fixpoint add_in_search_tree_fun t n :=
  match t with
  | leaf       => node n leaf leaf
  | node x l r => match (lt_eq_lt_dec n x) with
                  | inleft LE => 
                    if LE
                    then let: nl := add_in_search_tree_fun l n in
                         node x nl r
                    else t
                  | inright _ =>
                         let: nr := add_in_search_tree_fun r n in
                         node x l nr
                  end
  end.

Lemma add_fun_contains : forall t m x,
  contains m (add_in_search_tree_fun t x) <-> m = x \/ contains m t.
Proof.
induction t.
  intros m x; split; intros H; simpl in H; simpl.
    left. inversion H; auto; inversion H2.
    destruct H. rewrite H; auto.
      inversion H.    
  intros m x; unfold add_in_search_tree_fun; split; destruct (lt_eq_lt_dec x n); intros H.
    destruct s; fold add_in_search_tree_fun in H; auto.
      inversion H. right; auto. 
        apply IHt1 in H2. destruct H2. left; auto.
          right. constructor; auto.
        right; apply right_contains; auto.
    fold add_in_search_tree_fun in H.
      inversion H. right; auto.
        right; constructor; auto.
        apply IHt2 in H2; destruct H2; auto.
    destruct s; fold add_in_search_tree_fun; destruct H; auto;
        specialize (IHt1 m x); destruct IHt1; auto.
      inversion H; auto. rewrite <- e, H; auto. 
    fold add_in_search_tree_fun; destruct H.
      apply right_contains; apply IHt2; auto.
      inversion H; auto.    
        apply right_contains; apply IHt2; auto.
Qed.

Theorem add_in_search_tree_fun_correct : forall (t : tree) (n : nat),
  is_search_tree t -> 
  is_search_tree (add_in_search_tree_fun t n) /\ 
  (forall (m : nat), contains m (add_in_search_tree_fun t n) <-> m = n \/ contains m t).
Proof.
induction t.
  intros n _; split. constructor; auto. 
    intros m; split. apply add_fun_contains.
      intros H; destruct H; simpl. rewrite H; auto.
        inversion H; auto.
  intros x H; split.
    unfold add_in_search_tree_fun. destruct (lt_eq_lt_dec x n).
      destruct s; fold add_in_search_tree_fun; auto. constructor; inversion H; auto.
        apply lt_contains. intros m HcontM.  
          apply add_fun_contains in HcontM. destruct HcontM.
            rewrite H7; auto.
            apply (left_lt _ _ _ _ H H7). 
        apply (IHt1 x) in H5. destruct H5; auto.
      fold add_in_search_tree_fun. constructor; inversion H; auto.
        apply gt_contains. intros m HcontM.
            apply add_fun_contains in HcontM. destruct HcontM.
              rewrite H7; auto.
              apply (right_gt _ _ _ _ H H7). 
          apply (IHt2 x) in H6. destruct H6; auto.
    intros m. apply add_fun_contains.
Qed.