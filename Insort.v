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
Proof. intros. inversion H; auto. Defined.

Lemma tail_is_sorted : forall (a : nat) (l : list nat),
  is_sorted (a::l) -> is_sorted l.
Proof. intros. inversion H; auto. Defined.

Inductive is_inserted : nat -> list nat -> list nat -> Prop :=
  ins_head : forall n tl, is_inserted n tl (n::tl)
| ins_tail : forall n m tl tl', is_inserted n tl tl' -> is_inserted n (m::tl) (m::tl').

Hint Constructors is_inserted.

Inductive is_permutation : list nat -> list nat -> Prop :=
  perm_nil  : is_permutation [] []
| perm_cons : forall n l l' m, 
   is_permutation l l' -> is_inserted n l' m -> is_permutation (n::l) m.

Hint Constructors is_permutation.

Lemma smallest_perm a n tl : is_smallest a (n :: a :: tl) -> is_smallest a (a :: n :: tl).
Proof.
intros H; inversion H.
  rewrite H0 in H. assumption.
  inversion H4.
    apply (smallest_head a n [n] (lt_le_weak _ _ H3)). constructor.
    set (le_lt_dec n m0) as S.
      inversion S.
        apply (smallest_head a n (n :: tl) (lt_le_weak _ _ H3)).                
          apply (smallest_head n m0 tl H9 H8).
        apply (smallest_head a m0 (n :: tl) H6).
          apply (smallest_tail n m0 tl H9 H8).
    omega.
Qed.

Lemma smallest_with_n a n tl : is_smallest a (a :: tl) -> a <= n -> is_smallest a (a :: n :: tl).
Proof.
intros H; inversion H; intros Hle.
  apply (smallest_head a n [n] Hle). constructor.
  apply (smallest_perm).
    set (le_lt_eq_dec a n Hle) as S.
      inversion S.
        apply (smallest_tail _ _ _ H4 H).
        rewrite<-H4.
          apply (smallest_head a a (a :: tl) (le_refl a) H). 
  omega.
Qed.

Lemma smallest_without_n a n tl : is_smallest a (a :: n :: tl) -> is_smallest a (a :: tl).
Proof.
intros H; inversion H.
  inversion H3. 
    apply smallest_unit. 
    apply (smallest_head a m0 tl).
      rewrite H4 in H3, H1.
        apply (le_trans a n m0 H1 H7). assumption.
    apply (smallest_head a m tl H1). assumption.
  omega.
Qed.

Lemma smallest_than_snd a n tl : is_smallest a (a :: n :: tl) -> a <= n.
Proof.
intros H; inversion H.
  inversion H3.
    rewrite<-H6; assumption.
    rewrite<-H4; assumption.
    apply lt_le_weak.
      apply (le_lt_trans a m n H1 H7).
  omega.
Qed.  

Lemma insert_bigger : forall (a b : nat) (l l' : list nat),
  is_smallest a (a::l) -> b > a -> is_inserted b l l' -> is_smallest a (a::l').
Proof.
intros a b l l' H1 H2 H3.
  induction H3.
    apply (smallest_with_n a n tl H1); omega.
    apply (smallest_with_n a m tl').
      apply IHis_inserted; try assumption.
        apply (smallest_without_n a m tl H1).       
      apply (smallest_than_snd a m tl H1).
Qed.

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
Defined.

Theorem sort : forall (l : list nat), {l' | is_permutation l l' & is_sorted l'}.
Proof.
  intros. induction l. exists []; auto.
    inversion IHl. apply (insert_sorted a x) in H0. inversion H0. 
      exists x0. eauto. assumption.
Defined.

Print sort.

Extraction Language Ocaml.
Extraction "insort.ml" sort.
