Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.

Inductive is_smallest : nat -> list nat -> Prop :=
  smallest_unit : forall n, is_smallest n [n]
| smallest_head : forall n m tl, n <= m -> is_smallest m tl -> is_smallest n (n::tl)
| smallest_tail : forall n m tl, m <  n -> is_smallest m tl -> is_smallest m (n::tl).

Hint Constructors is_smallest.

Theorem smallest : 
  forall (l : list nat), [] <> l -> {n | is_smallest n l}.
Proof. 
  intros. 
    induction l. unfold not in H. exfalso. auto.
      destruct l eqn: L. exists a. auto. 
        remember (IHl (@nil_cons nat n l0)) as A. inversion A.
        remember (le_gt_dec a x) as A1. inversion A1. 
          exists a. eauto. 
          exists x. eauto. 
Defined.

Inductive is_sorted : list nat -> Prop :=
  sorted_nil  : is_sorted []
| sorted_one  : forall n, is_sorted [n]
| sorted_cons : forall n tl, 
    is_sorted tl -> is_smallest n (n::tl) -> is_sorted (n::tl).

Hint Constructors is_sorted.

Lemma head_is_smallest : forall (a : nat) (l : list nat),
  is_sorted (a::l) -> is_smallest a (a::l).
Proof. admit. Qed.

Lemma tail_is_sorted : forall (a : nat) (l : list nat),
  is_sorted (a::l) -> is_sorted l.
Proof. admit. Qed.

Inductive is_inserted : nat -> list nat -> list nat -> Prop :=
  ins_head : forall n tl, is_inserted n tl (n::tl)
| ins_tail : forall n m tl tl', is_inserted n tl tl' -> is_inserted n (m::tl) (m::tl').

Hint Constructors is_inserted.

Lemma smallest_invariant : forall (a n : nat) (l l' : list nat),
  a > n -> is_smallest n l -> is_inserted a l l' -> is_smallest n l'.
Proof. admit. Qed.

Inductive is_permutation : list nat -> list nat -> Prop :=
  perm_nil  : is_permutation [] []
| perm_cons : forall n l l' m, 
   is_permutation l l' -> is_inserted n l' m -> is_permutation (n::l) m.

Hint Constructors is_permutation.

Lemma insert_bigger : forall (a b : nat) (l l' : list nat),
  is_smallest a (a::l) -> b > a -> is_inserted b l l' -> is_smallest a (a::l').
Proof. admit. Qed.
(*
  intros. generalize dependent b. generalize dependent l.
    induction l'. intros. inversion H1.
      intros. inversion H1. rewrite <- H5. rewrite <- H6. 
        assert (A : is_smallest a (b::a::l)). apply (smallest_tail b a (a::l)).
          omega. assumption. 
  *)

Lemma insert_sorted : forall (a : nat) (l : list nat),
  is_sorted l -> {l' | is_inserted a l l' & is_sorted l'}.
Proof.
  intros. induction l. exists [a]; auto.
    assert (A: is_sorted l). apply (tail_is_sorted a0 l). assumption.
      apply IHl in A. inversion A. 
      destruct (le_gt_dec a a0).
        exists (a::a0::l); auto. apply (sorted_cons a (a0::l)). 
          auto. apply (smallest_head a a0 (a0::l)). auto. 
          apply head_is_smallest. assumption.
        exists (a0::x). auto. apply sorted_cons. auto.
          apply (insert_bigger a0 a l x). 
          apply (head_is_smallest a0 l). assumption. assumption. assumption.
Qed.

Theorem sort : forall (l : list nat), {l' | is_permutation l l' & is_sorted l'}.
Proof.
  intros. induction l. exists []; auto.
    inversion IHl. apply (insert_sorted a x) in H0. inversion H0. 
      exists x0. eauto. assumption.
Qed.
        

  