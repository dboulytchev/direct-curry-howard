Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.
Require Export Smallest.
Require Export Insort.

Inductive are_merged : list nat -> list nat -> list nat -> Prop :=
  merged_nil_left: forall (l : list nat), are_merged [] l l
| merged_nil_right : forall (l : list nat), are_merged l [] l
| merged_le : forall m n l l' l'', 
    m < n -> are_merged l (n::l') l'' -> are_merged (m::l) (n::l') (m::l'')
| merged_gt : forall m n l l' l'', 
    n <= m -> are_merged (m::l) l' l'' -> are_merged (m::l) (n::l') (n::l'').

Lemma can_split : forall (l : list nat), 
  {l' | (fst l') ++ (snd l') = l & (length (fst l') - length (snd l')) <= 1}.
Proof. admit. Qed.

Lemma merge : forall (a b : list nat),
  is_sorted a -> is_sorted b -> {ab | is_sorted ab & are_merged a b ab}.
Proof. admit. Qed.

Lemma merged_permutation : forall (l l' l'': list nat), 
  are_merged l l' l'' -> is_permutation (l ++ l') l''.
Proof. admit. Qed.

Theorem merge_sort : forall (l : list nat), {l' | is_permutation l l' & is_sorted l'}.
Proof.
  intro. induction l. exists []; eauto.
    remember (can_split l). inversion s. inversion x.
    