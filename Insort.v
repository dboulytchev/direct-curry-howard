Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.
Require Export Smallest.

Inductive is_sorted : list nat -> Prop :=
  sorted_nil  : is_sorted []
| sorted_one  : forall n, is_sorted [n]
| sorted_cons : forall n tl, 
    is_sorted tl -> is_smallest n (n::tl) -> is_sorted (n::tl).

Hint Constructors is_sorted.

Lemma head_is_smallest : forall (a : nat) (l : list nat),
  is_sorted (a::l) -> is_smallest a (a::l).
Proof. intros. inversion H; auto. Qed.

Lemma tail_is_sorted : forall (a : nat) (l : list nat),
  is_sorted (a::l) -> is_sorted l.
Proof. intros. inversion H; auto. Qed.

Inductive is_inserted : nat -> list nat -> list nat -> Prop :=
  ins_head : forall n tl, is_inserted n tl (n::tl)
| ins_tail : forall n m tl tl', is_inserted n tl tl' -> is_inserted n (m::tl) (m::tl').

Hint Constructors is_inserted.

Inductive is_permutation : list nat -> list nat -> Prop :=
  perm_nil  : is_permutation [] []
| perm_cons : forall n l l' m, 
   is_permutation l l' -> is_inserted n l' m -> is_permutation (n::l) m.

Hint Constructors is_permutation.

(* TODO: prove *) 
Lemma insert_bigger : forall (a b : nat) (l l' : list nat),
  is_smallest a (a::l) -> b > a -> is_inserted b l l' -> is_smallest a (a::l').
Proof. admit. Qed.  

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
          apply (insert_bigger a0 a l x);
            try apply (head_is_smallest a0 l); assumption.
Qed.

Theorem sort : forall (l : list nat), {l' | is_permutation l l' & is_sorted l'}.
Proof.
  intros. induction l. exists []; auto.
    inversion IHl. apply (insert_sorted a x) in H0. inversion H0. 
      exists x0. eauto. assumption.
Qed.
