Require Omega. 
Require Export Bool List.
Export ListNotations.
Require Export Arith Arith.EqNat.
Require Export Smallest Insort.

Function dist a b := max a b - min a b.

Inductive are_merged : list nat -> list nat -> list nat -> Prop :=
  merged_nil_left: forall (l : list nat), are_merged [] l l
| merged_nil_right : forall (l : list nat), are_merged l [] l
| merged_le : forall m n l l' l'', 
    m <= n -> are_merged l (n::l') l'' -> are_merged (m::l) (n::l') (m::l'')
| merged_gt : forall m n l l' l'', 
    n <= m -> are_merged (m::l) l' l'' -> are_merged (m::l) (n::l') (n::l'').

Require Import Permutation.

Lemma dist_S_l a b: dist a b <= 1 -> min a b = a -> dist (S a) b <= 1.
Proof.
unfold dist. intros H1 H2. rewrite H2 in H1. 
  assert (a <= b) as H_3. rewrite <- H2; apply Min.le_min_r; auto.
  assert (max a b = b) as H0. apply max_r; auto. rewrite H0 in H1.
  inversion H1 as [H_1|c H_1 H_2];
  destruct (Min.min_spec (S a) b) as [H3|H3]; destruct H3 as [H3 H4];
  destruct (Max.max_spec (S a) b) as [H5|H5]; destruct H5 as [H5 H6]; try omega.
Qed.

Lemma dist_S_r a b: dist a b <= 1 -> min a b = b -> dist a (S b) <= 1.
Proof. 
unfold dist. intros H1 H2. rewrite H2 in H1. 
  assert (b <= a) as H_3. rewrite <- H2; apply Min.le_min_l; auto.
  assert (max a b = a) as H0. apply max_l; auto. rewrite H0 in H1.
  inversion H1 as [H_1|c H_1 H_2];
  destruct (Min.min_spec a (S b)) as [H3|H3]; destruct H3 as [H3 H4];
  destruct (Max.max_spec a (S b)) as [H5|H5]; destruct H5 as [H5 H6]; try omega.
Qed.

Lemma can_split : forall (l : list nat), 
  {l' | Permutation ((fst l') ++ (snd l')) l & dist (length (fst l')) (length (snd l')) <= 1}.
Proof.
induction l. exists ([], []); auto.
  destruct IHl. destruct x as [pl pr]. simpl in p, l0.
    unfold dist in l0.
      destruct (Min.min_dec (length pl) (length pr)) as [H1 | H1].
        exists (a :: pl, pr). simpl. apply perm_skip; auto.
          simpl. apply dist_S_l; auto.              
        exists (pl, a :: pr). simpl.
          apply Permutation_sym; apply Permutation_cons_app; apply Permutation_sym; auto.
          simpl. apply dist_S_r; auto.
Qed.

Lemma merged_permutation : forall (l l' l'': list nat), 
  are_merged l l' l'' -> Permutation (l ++ l') l''.
Proof.
intros. induction H; simpl; try rewrite app_nil_r; auto.
  apply Permutation_sym. apply (@Permutation_cons_app _ l'' (m :: l) l' n).
    apply Permutation_sym; auto.
Qed.

Lemma merge : forall (a b : list nat),
  is_sorted a -> is_sorted b -> {ab | is_sorted ab & are_merged a b ab}.
Proof.
induction a as [| ah al].
  intros b _ H. exists b; auto. constructor.
  induction b as [| bh bl].
    intros H _. exists (ah::al); auto. constructor.
    intros H1 H2. destruct (lt_eq_lt_dec ah bh) as [H3|H3].
      assert (is_sorted al) as H4. apply (tail_is_sorted _ _ H1).
      pose (IHal (bh::bl) H4 H2) as H5. destruct H5 as [l H5 H6].
      exists (ah::l); auto. constructor; auto. apply in_list_smallest. left; auto.
        intros x H; destruct H. omega.
        apply merged_permutation in H6. apply Permutation_sym in H6.
          apply (Permutation_in x H6) in H. apply in_app_or in H. destruct H.
            apply (smallest_in (ah::al)). apply head_is_smallest; auto. right; auto.
            apply (le_trans ah bh x). destruct H3; omega.
              apply (smallest_in (bh::bl)). apply head_is_smallest; auto. auto.
        apply merged_le; destruct H3; auto; omega. 
    assert (is_sorted bl) as H4. apply (tail_is_sorted _ _ H2).
    pose (IHbl H1 H4) as H5. destruct H5 as [l H5 H6].
      exists (bh::l); auto. constructor; auto. apply in_list_smallest. left; auto.
        intros x H; destruct H. omega.
        apply merged_permutation in H6. apply Permutation_sym in H6.
          apply (Permutation_in x H6) in H. apply in_app_or in H. destruct H.
            apply (le_trans bh ah x). destruct H3; omega.
              apply (smallest_in (ah::al)). apply head_is_smallest; auto. auto.
            apply (smallest_in (bh::bl)). apply head_is_smallest; auto. right; auto.
        apply merged_gt. omega. auto.
Qed.


Theorem genListInd_big_l {A} (P : list A -> Type) (l : list A) :
  P [] ->
  (forall l1 : list A,
      (forall l2, length l2 <  length l1 -> P l2)  ->
      (forall l2, length l2 <= length l1 -> P l2)
  ) ->
  (forall l1 : list A, length l1 <= length l -> P l1).
Proof.
intros HBase; induction l.
  intros _ l1; simpl.
    destruct l1; auto. intros H; apply le_Sn_0 in H; inversion H.
  intros H1. apply H1. intros l2 H2. simpl in H2.
    apply gt_S_le in H2. apply IHl; auto.
Qed.

Theorem genListInd_big {A} (P : list A -> Type) :
  P [] ->
  (forall l : list A,
      (forall l1, length l1 <  length l -> P l1) ->
      (forall l1, length l1 <= length l -> P l1)
  ) ->
  (forall l : list A, P l).
Proof. intros HBase HStep l; apply (genListInd_big_l P l); auto. Qed.

Theorem genListInd {A} (P : list A -> Type) :
  P [] -> (forall l1, (forall l2, length l2 < length l1 -> P l2) -> P l1) ->
  (forall l, P l).
Proof.
intros HBase HStep. apply genListInd_big; auto.
  intros l H1 l1 H2. apply HStep. intros l2 H3. apply H1.
    apply (lt_le_trans _ _ _ H3 H2).
Qed.

Theorem merge_sort : forall (l : list nat), {l' | Permutation l l' & is_sorted l'}.
Proof.
apply genListInd. exists []; auto.
  intros l HStep.
    pose (can_split l). destruct s as [x H1 H2]. destruct x as [hl rl]. simpl in H1, H2.
      destruct hl; destruct rl. exists []; auto; simpl in H1; rewrite <- H1; auto.
        simpl in H1, H2. unfold dist in H2; simpl in H2.
          apply le_S_gt in H2; destruct rl. exists [n]; auto; rewrite <- H1; auto.
            simpl in H2; omega.
        rewrite app_nil_r in H1. unfold dist in H2; simpl in H2.
          apply le_S_gt in H2; destruct hl. exists [n]; auto; rewrite <- H1; auto.
            simpl in H2; omega.
        assert (length (n  :: hl) < length l) as H3.
          rewrite <- (Permutation_length H1).
            rewrite app_length. apply NPeano.Nat.lt_add_pos_r. simpl; omega.
        assert (length (n0 :: rl) < length l) as H4.
          rewrite <- (Permutation_length H1).
            rewrite app_length. apply NPeano.Nat.lt_add_pos_l. simpl; omega.
        apply HStep in H3; apply HStep in H4. destruct H3; destruct H4.
          pose (merge x x0 i i0) as H3. destruct H3. exists x1; auto.
            remember (Permutation_app p p0) as H3. clear HeqH3. apply Permutation_sym in H1.
              apply (Permutation_trans H1) in H3. apply (Permutation_trans H3).
                apply merged_permutation; auto.
Qed.


(* Program Fixpoint Definition. *)

Program Fixpoint can_split_fix (l : list nat) :
  {l' | Permutation ((fst l') ++ (snd l')) l /\ dist (length (fst l')) (length (snd l')) <= 1} :=
  match l with
  | [] => ([], [])
  | a :: l =>
    let: (pl, pr) := can_split_fix l in
    match (Min.min_dec (length pl) (length pr)) with
    | left  _ => (a::pl, pr)
    | right _ => (pl, a::pr)
    end 
  end.
Next Obligation. split. apply perm_skip; auto. apply dist_S_l; auto. Defined.
Next Obligation.
split. apply Permutation_sym; apply Permutation_cons_app; apply Permutation_sym; auto.
  apply dist_S_r; auto.
Defined.

Definition mm (lls : list nat * list nat) := let (l1, l2) := lls in length l1 + length l2.

Require Import Coq.Program.Wf Recdef.

Program Fixpoint merge_fix (ab : list nat * list nat) {measure (mm ab)} :
    is_sorted (fst ab) -> is_sorted (snd ab) ->
     {l | is_sorted l /\ are_merged (fst ab) (snd ab) l} := fun aS bS =>
  let: a := fst ab in (* In case you use 'let' instead 'let:' there will be not *)
  let: b := snd ab in (* information in obligation proof.                       *)
  match a with
  | [] => b
  | ah :: al =>
    match b with
    | [] => ah :: al
    | bh :: bl =>
      match lt_eq_lt_dec ah bh with
      | inleft  _ => let: l := merge_fix (al, bh::bl) _ _ in
                     ah :: l
      | inright _ => let: l := merge_fix (ah::al, bl) _ _ in
                     bh :: l  (* In case you use 'a' instread of 'ah::al'   *)
      end                     (* There will be not enough information in    *)
    end                       (* obligation proof. The same thing with 'b'. *)
  end.
Next Obligation. split; auto. simpl. apply merged_nil_left.              Qed.
Next Obligation. split. rewrite Heq_a; auto.  apply merged_nil_right.    Qed.
Next Obligation. simpl in *; rewrite <- Heq_a, <- Heq_b. simpl. omega.   Qed.
Next Obligation. simpl in *. rewrite <- Heq_a in aS. inversion aS; auto. Qed.
Next Obligation. simpl in *. rewrite <- Heq_b in bS; auto.               Qed.
Next Obligation.
simpl in *.
  remember (merge_fix (al, bh :: bl)
            (merge_fix_obligation_3 (l0, l1) merge_fix aS bS l0 eq_refl l1
               eq_refl ah al Heq_a bh bl Heq_b wildcard' Heq_anonymous1)
            (merge_fix_obligation_4 (l0, l1) merge_fix aS bS l0 eq_refl l1
               eq_refl ah al Heq_a bh bl Heq_b wildcard' Heq_anonymous1)
            (merge_fix_obligation_5 (l0, l1) merge_fix aS bS l0 eq_refl l1
               eq_refl ah al Heq_a bh bl Heq_b wildcard' Heq_anonymous1)).
  clear Heqs. destruct s; simpl; destruct a; simpl in *.
    split.
      constructor; auto. apply in_list_smallest. left; auto.
        intros y H1; destruct H1. omega.
          apply merged_permutation in H0. apply Permutation_sym in H0.
            apply (Permutation_in y H0) in H1. apply in_app_or in H1. destruct H1.
              apply (smallest_in (ah :: al)). apply head_is_smallest; auto.
                rewrite Heq_a; auto. right; auto.
              apply (le_trans ah bh y). destruct wildcard'; omega.
                apply (smallest_in (bh :: bl)); auto. apply head_is_smallest; auto.
                  rewrite Heq_b; auto.
      constructor; auto. destruct wildcard'; omega.
Qed.
Next Obligation. simpl in *. rewrite <- Heq_a, <- Heq_b. simpl. omega.   Qed.
Next Obligation. simpl in *. rewrite Heq_a; auto.                        Qed.
Next Obligation. simpl in *. rewrite <- Heq_b in bS. inversion bS; auto. Qed.
Next Obligation.
simpl in *.
  remember (merge_fix (ah :: al, bl)
            (merge_fix_obligation_7 (l0, l1) merge_fix aS bS l0 eq_refl l1
               eq_refl ah al Heq_a bh bl Heq_b wildcard' Heq_anonymous1)
            (merge_fix_obligation_8 (l0, l1) merge_fix aS bS l0 eq_refl l1
               eq_refl ah al Heq_a bh bl Heq_b wildcard' Heq_anonymous1)
            (merge_fix_obligation_9 (l0, l1) merge_fix aS bS l0 eq_refl l1
               eq_refl ah al Heq_a bh bl Heq_b wildcard' Heq_anonymous1)).
  clear Heqs. destruct s; simpl; destruct a; simpl in *.
    split.
      constructor; auto. apply in_list_smallest. left; auto.
        intros y H1; destruct H1. omega.
          apply merged_permutation in H0. apply Permutation_sym in H0.
            apply (Permutation_in y H0) in H1. apply in_app_or in H1. destruct H1.
              apply (le_trans bh ah y). omega.
                apply (smallest_in (ah :: al)); auto. apply head_is_smallest; auto.
                  rewrite Heq_a; auto. 
              apply (smallest_in (bh :: bl)). apply head_is_smallest; auto.
                rewrite Heq_b; auto. right; auto.
     constructor; auto. omega.
Qed.

Program Fixpoint merge_sort_fix (l : list nat) {measure (length l)} :
    {l' | Permutation l l' /\ is_sorted l'} :=
  let: (nl, nr):= can_split_fix l in
  match nl, nr with
  | [], _ => nr
  | _, [] => nl
  | hl::tl, hr::tr =>
    let: sl := merge_sort_fix nl in
    let: sr := merge_sort_fix nr in
    merge_fix (sl, sr) _ _
  end.
Next Obligation.
remember (can_split_fix l) as spl. clear Heqspl. destruct spl as [lr H1].
  destruct H1 as [H1 H2]; simpl in *. rewrite <- Heq_anonymous in *; simpl in *.
    apply Permutation_sym in H1; split; auto.
      assert (length nr <= 1). unfold dist in H2; simpl in H2.
        rewrite <- minus_n_O in H2; auto.
        destruct nr; auto; destruct nr; auto. simpl in H. omega.
Qed.
Next Obligation.  
remember (can_split_fix l) as spl. clear Heqspl. destruct spl as [lr H1].
  destruct H1 as [H1 H2]; simpl in *. rewrite <- Heq_anonymous in *; simpl in *.
    rewrite app_nil_r in H1. apply Permutation_sym in H1; split; auto.
      assert (length nl <= 1). unfold dist in H2. 
        rewrite (Min.min_0_r (length nl)) in H2. rewrite (Max.max_0_r (length nl)) in H2.
        rewrite <- minus_n_O in H2; auto.
      destruct nl; auto; destruct nl; auto. simpl in H0. omega.
Qed.
Next Obligation. 
remember (can_split_fix l) as spl. clear Heqspl. destruct spl as [lr H1].
  destruct H1 as [H1 H2]; simpl in *. rewrite <- Heq_anonymous in *; simpl in *.
    apply Permutation_length in H1. rewrite <- H1. simpl.
      rewrite app_length. simpl. omega.
Qed.
Next Obligation.
remember (can_split_fix l) as spl. clear Heqspl. destruct spl as [lr H1].
  destruct H1 as [H1 H2]; simpl in *. rewrite <- Heq_anonymous in *; simpl in *.
    apply Permutation_length in H1. rewrite <- H1. simpl.
      rewrite app_length. simpl. omega.
Qed.
Next Obligation.
remember (merge_sort_fix (hl :: tl)
           (merge_sort_fix_obligation_3 l merge_sort_fix 
              (hl :: tl) (hr :: tr) Heq_anonymous hl tl hr tr eq_refl eq_refl)) as spl.
  clear Heqspl. destruct spl as [lr H1]. destruct H1 as [H1 H2]; auto.
Qed.
Next Obligation.
remember (merge_sort_fix (hr :: tr)
           (merge_sort_fix_obligation_4 l merge_sort_fix 
              (hl :: tl) (hr :: tr) Heq_anonymous hl tl hr tr eq_refl eq_refl
              (proj1_sig
                 (merge_sort_fix (hl :: tl)
                    (merge_sort_fix_obligation_3 l merge_sort_fix 
                       (hl :: tl) (hr :: tr) Heq_anonymous hl tl hr tr
                       eq_refl eq_refl))) eq_refl)) as spl.
  clear Heqspl. destruct spl as [lr H1]. destruct H1 as [H1 H2]; auto.
Qed.
Next Obligation. admit. Qed.