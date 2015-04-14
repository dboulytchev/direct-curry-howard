Require Omega.   
Require Export Bool List.
Export ListNotations.
Require Export Arith Arith.EqNat.
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

Lemma smallest_head_perm a n tl : is_smallest a (n :: a :: tl) -> is_smallest a (a :: n :: tl).
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
  apply (smallest_head_perm).
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

Inductive is_permutation : list nat -> list nat -> Prop :=
  perm_nil  : is_permutation [] []
| perm_cons : forall n l l' m, 
   is_permutation l l' -> is_inserted n l' m -> is_permutation (n::l) m.

Hint Constructors is_permutation.

Theorem sort : forall (l : list nat), {l' | is_permutation l l' & is_sorted l'}.
Proof.
  intros. induction l. exists []; auto.
    inversion IHl. apply (insert_sorted a x) in H0. inversion H0. 
      exists x0. eauto. assumption.
Defined.

Print sort.

Extraction Language Ocaml.
Extraction "insort.ml" sort.

Program Fixpoint insert_sorted_fix (a : nat) (l : list nat) :
    is_sorted l -> {l' | is_inserted a l l' /\ is_sorted l'} := fun H =>
  match l with
  | nil     => [a]
  | x :: xs => if le_gt_dec a x
               then a :: l
               else x :: (insert_sorted_fix a xs _)
  end.
Next Obligation.
split; auto.
  apply sorted_cons. assumption.
    apply (smallest_head a x). assumption.
      inversion H; auto.
Qed.
Next Obligation.
inversion H; auto.
Qed.
Next Obligation.
split.
  apply ins_tail; auto.
    apply sorted_cons; auto.
      apply (insert_bigger x a xs x0); auto.
        inversion H; auto.
Defined.            

Require Import Permutation.

Lemma insert_sorted_fix_perm (a : nat) (l : list nat) (H : is_sorted l) :
    Permutation (a :: l) (proj1_sig (insert_sorted_fix a l H)).
Proof.
  generalize dependent H.
    generalize dependent a.
      induction l.
        intros a H. unfold insert_sorted_fix; simpl; auto.
        intros b H; simpl.
          destruct (le_gt_dec b a) eqn: Hab; simpl.
            apply Permutation_refl.
            apply (@perm_trans _ (b :: a :: l) (a :: b :: l)); auto.
              apply perm_swap.
Qed.            
   
(* 
Program Fixpoint sort_prog (l : list nat) :
    {l' | Permutation l l' /\ is_sorted l'} :=
  match l with
  | nil     => nil
  | x :: xs => insert_sorted_fix x (sort_prog xs) _
  end.
Next Obligation.
  Admitted.
  split.
  admit.
Defined.
*)

(* Realization w/o dependent types *)

Fixpoint insert_fun a l :=
  match l with
  | nil     => [a]
  | x :: xs => if le_gt_dec a x
               then a :: l
               else x :: (insert_fun a xs)
  end.

Fixpoint insert_sort l :=
  match l with
  | nil     => nil
  | x :: xs => insert_fun x (insert_sort xs)
  end.

Lemma smallest_in : forall l a, is_smallest a l -> (forall x, In x l -> a <= x).
Proof.
induction l.
  intros a  H1 x H2. inversion H2.
  intros a0 H1 x H2. destruct H2.
    rewrite H in H1. clear a H.
      inversion H1; auto. apply lt_le_weak; auto.
    inversion H1.
      rewrite <- H4 in H; inversion H.
      apply (le_trans a m x H4). 
        apply (IHl _ H5 _ H).
      apply IHl; auto.        
Qed.

Lemma smallest_in_perm : forall a l l',
  is_smallest a l -> Permutation l l' -> (forall x, In x l' -> a <= x).
Proof.
intros a l l' H1 H2 x H3.
  apply (smallest_in l a H1).
    apply (Permutation_in x (Permutation_sym H2) H3).
Qed.

Lemma smallest_dec : forall l, l <> [] -> {x | is_smallest x l}.
Proof.
induction l. intros H; exfalso; auto. 
  intros _.
    destruct l. exists a; auto.
      assert (n :: l <> []) as H. intros H. inversion H.
      apply IHl in H; destruct H. 
        destruct (le_lt_dec a x).
          exists a. apply (smallest_head a x); auto.
          exists x. apply smallest_tail; auto.
Qed.

Lemma smallest_in_list : forall a l, is_smallest a l -> In a l.
Proof.
induction l; intros H; inversion H.
  constructor; auto.
  constructor; auto.
  right. apply (IHl H4).
Qed.

Lemma in_list_smallest : forall l a,
  In a l -> (forall x, In x l -> a <= x) -> is_smallest a l.
Proof.
induction l.
  intros a H; inversion H.
  intros b H1 H2.
    destruct H1.
      rewrite <- H in H2. rewrite <- H. clear b H.
        destruct l; auto.
        pose (smallest_dec (n::l)) as H3.
          assert (n::l <> []) as H4. intros H0. inversion H0.
          apply H3 in H4. destruct H4.
            assert (a <= x) as H5. apply H2. right.
              apply (smallest_in_list _ _ i).
            apply (smallest_head _ x); auto.
      assert (b <= a) as H1. apply H2. left; auto.
      destruct (le_lt_eq_dec _ _ H1).
        apply smallest_tail; auto. 
          apply IHl; auto.
            intros x H3. apply H2; right; auto.
        rewrite e. rewrite e in H2, H. clear b H1 e.
          apply (smallest_head _ a). apply le_refl.
            apply IHl; auto. intros x H3. apply H2.
              right; auto.
Qed.

Lemma smallest_perm : forall a l l', is_smallest a l -> Permutation l l' -> is_smallest a l'.
Proof.
intros a l l' H1 H2. 
  apply in_list_smallest.
    apply (Permutation_in _ H2). apply (smallest_in_list _ _ H1).
    apply (smallest_in_perm _ _ _ H1 H2).
Qed.

Lemma insert_fun_to_sort : forall a l, is_sorted l ->
  Permutation (insert_fun a l) (a :: l) /\ is_sorted (insert_fun a l).
Proof.
intros a l. induction l; intros H.
  split; auto. unfold insert_fun; auto.
  assert (is_sorted l) as H1. inversion H; auto.
    unfold insert_fun.
      destruct (le_gt_dec a a0) eqn: H2; fold insert_fun.
        split; auto; constructor; auto.
          apply (smallest_head _ a0); auto.
            apply head_is_smallest; auto.
        split.
          eapply (@perm_trans _ _ (a0 :: a :: l)); constructor.
            apply (IHl H1).
          destruct (IHl H1). constructor; auto.
            apply (smallest_perm a0 (a0 :: a :: l)).
              apply smallest_head_perm.
                apply smallest_tail; auto.
                  apply head_is_smallest; auto.
              constructor. apply Permutation_sym. auto.
Qed.

Theorem insert_sort_is_sort :
  forall l, Permutation (insert_sort l) l /\  is_sorted (insert_sort l).
Proof.
intros l; induction l; simpl; auto.
  destruct IHl as [H1 H2].
    pose (H := insert_fun_to_sort a (insert_sort l)).
      destruct H as [H3 H4]; auto.
       split; auto. eapply (@perm_trans _ _ (a :: insert_sort l)); auto.
Qed.