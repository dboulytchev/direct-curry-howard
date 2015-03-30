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
   m < n -> lt_tree n l -> lt_tree n r -> lt_tree n (node n l r).

Inductive gt_tree : nat -> tree -> Prop :=
  gt_leaf : forall (n   : nat), gt_tree n leaf
| gt_node : forall (n m : nat) (l r : tree), 
   m > n -> gt_tree n l -> gt_tree n r -> gt_tree n (node n l r).

Inductive is_search_tree : tree -> Prop :=
  st_leaf : is_search_tree leaf
| st_node : forall (n : nat) (l r : tree), 
   lt_tree n l -> gt_tree n r -> is_search_tree (node n l r).

Inductive contains : nat -> tree -> Prop :=
  root_contains : forall (n : nat) (l r : tree), contains n (node n l r)
| left_contains : forall (n m : nat) (l r : tree), 
   contains n l -> contains n (node m l r)
| right_contains : forall (n m : nat) (l r : tree), 
   contains n r -> contains n (node m l r).

Hint Constructors lt_tree gt_tree is_search_tree contains.

Definition add_in_search_tree : forall (t : tree) (n : nat),
  is_search_tree t -> 
  {t' | is_search_tree t' & 
        contains n t' /\ forall (m : nat),
        contains m t -> contains m t'
  }.
Proof.
  intros. induction t. exists (node n leaf leaf); auto. 
    assert (L: is_search_tree t1). 
      
    remember (lt_eq_lt_dec n n0) as B. inversion B. inversion H0.
      

Fixpoint height (t: tree) : nat := 
  match t with
  | leaf => 0
  | node _ l r => 1 + max (height l) (height r)
  end.

