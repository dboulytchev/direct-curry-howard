Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.

Theorem ex_falso_quodlibet : forall (P:Set),
  False -> P.
Proof.  intros P contra.
  inversion contra.  
Qed.

Inductive minimal_in_list : nat -> list nat -> Prop :=
  mil_Base : forall n, minimal_in_list n [n]
| mil_Head : forall n m tl, n <= m -> minimal_in_list m tl -> minimal_in_list n (n::tl)
| mil_Tail : forall n m tl, m <  n -> minimal_in_list m tl -> minimal_in_list m (n::tl).

(*
Program Fixpoint minimal1 (l : list nat) (_ : length l > 0) : { n | minimal_in_list n l} :=
  match l with  
    [h] => h
  | h::tl => let m := minimal1 tl _ in if leb h m then h else m
  | _ => 0
  end.

Obligation 1. apply mil_Base. Qed.
Obligation 2. remember (H0 h). destruct tl. apply ex_falso_quodlibet. apply n. reflexivity.
                simpl. omega. Defined.
Obligation 3. admit. Defined.
Obligation 4. admit. Defined.
*)

(*Extraction "minimal1.ml" minimal1.*)

Ltac by_contradiction := try (simpl in *; omega; match goal with H:_ |- _ => inversion H end).

Hint Constructors minimal_in_list.
Theorem minimal : 
  forall (l : list nat), length l > 0 -> { n | minimal_in_list n l}.
Proof. 
  intros. induction l. by_contradiction.
    destruct l eqn: L. 
      exists a. auto. (*apply mil_Base.*)
      assert (A: length (n::l0) > 0). simpl in *. omega.     
      apply IHl in A. inversion A.
      remember (le_gt_dec a x) as A1.
      inversion A1. exists a. eauto. (*apply mil_Head with x; assumption.*)
                    exists x. eauto. (*apply mil_Tail; assumption. *)
Defined.

Extraction Language Ocaml.

Extraction "minimal.ml" minimal.

Print minimal.
Inductive list_sorted : list nat -> Prop :=
  ls_Nil  : list_sorted []
| ls_One  : forall n, list_sorted [n]
| ls_Cons : forall n m tl, 
    list_sorted tl -> minimal_in_list m tl -> n <= m -> list_sorted (n::tl).

Inductive list_insert : nat -> list nat -> list nat -> Prop :=
  li_Head : forall n tl, list_insert n tl (n::tl)
| li_Tail : forall n m tl tl', list_insert n tl tl' -> list_insert n (m::tl) (m::tl').

Inductive list_permutation : list nat -> list nat -> Prop :=
  lp_Nil  : list_permutation [] []
| lp_Cons : forall n l l' m, 
   list_permutation l' l -> list_insert n l' m -> list_permutation m (n::l).

Lemma minimal_in_sorted : forall n l,
  list_sorted (n::l) -> minimal_in_list n (n::l).
Proof. 
  intros. destruct l. 
    apply mil_Base.
    inversion H. apply mil_Head with m; assumption.
Qed.

Lemma minimal_in_inserted : forall l' n m l,
  minimal_in_list m l -> list_insert n l l' -> 
  (m <= n /\ minimal_in_list m l') \/ (n < m /\ minimal_in_list n l').
Proof.
  intro l'. induction l'. intros. inversion H0.
    intros. 
      remember (le_lt_dec m n) as A. clear HeqA. inversion A.
        clear A. left. split. assumption.
          inversion H0. rewrite <- H6. rewrite <- H5. 
          apply le_lt_eq_dec in H1. inversion H1. apply mil_Tail. assumption. assumption.
            rewrite <- H4. apply mil_Head with m. omega. assumption.
          rewrite <- H4 in H. inversion H. rewrite <- H10 in H5. 
            inversion H5. rewrite <- H9. rewrite <- H2. rewrite <- H9. 
              apply mil_Head with n. assumption. apply mil_Base.
          remember (le_lt_dec m1 n) as A. clear HeqA. inversion A.
          apply (IHl' n m1 tl) in H11. inversion H11. inversion H13.
            rewrite <- H2. apply mil_Head with m1. omega. assumption.
            inversion H13. rewrite <- H2. apply mil_Head with n. omega. assumption. 
              assumption.
          apply (IHl' n m1 tl) in H11. inversion H11. inversion H13.
            rewrite <- H2. apply mil_Head with m1. omega. assumption.
            inversion H13. rewrite <- H2. apply mil_Head with n. omega. assumption. 
              assumption.
          apply (IHl' n m tl) in H11. inversion H11. inversion H12. rewrite <- H2.
            apply mil_Tail. assumption. assumption. inversion H12. 
              apply lt_not_le in H13. apply ex_falso_quodlibet. apply H13. assumption.
              assumption.
        clear A. right. split. assumption.
          inversion H0. rewrite <- H6. rewrite <- H5. apply mil_Head with m. omega. 
             assumption.
          rewrite <- H4 in H. inversion H. rewrite <- H10 in H5. inversion H5.
             apply mil_Tail. omega. apply mil_Base. 
          remember (le_lt_dec n m1) as A. clear HeqA. inversion A.
          apply (IHl' n m1 tl) in H11. inversion H11. inversion H13.
             assert (HA: a < a). omega. remember (lt_irrefl a). 
             apply ex_falso_quodlibet. apply n2. assumption.
             inversion H13. apply mil_Tail. omega. assumption. assumption.
          apply (IHl' n m1 tl) in H11. inversion H11. inversion H13.
             assert (HA: a < a). omega. remember (lt_irrefl a).
             apply ex_falso_quodlibet. apply n2. assumption. 
             inversion H13. apply mil_Tail. omega. assumption. assumption.
          apply (IHl' n m tl) in H11. inversion H11. inversion H12.
             apply lt_not_le in H1. apply ex_falso_quodlibet. apply H1. assumption.
             inversion H12. apply mil_Tail. omega. assumption. assumption.
Qed.

Lemma minimal_in_inserted_preserve : forall l' n m l,
  minimal_in_list m l -> m <= n -> list_insert n l l' -> minimal_in_list m l'.
Proof. 
  intros. apply (minimal_in_inserted l' n m l) in H. 
   inversion H. inversion H2. assumption. inversion H2. apply lt_not_le in H3. 
     apply ex_falso_quodlibet. apply H3. assumption. assumption.
Qed.

Lemma minimal_in_inserted_swap : forall n m l l',
  minimal_in_list m l -> n < m -> list_insert n l l' -> minimal_in_list n l'.
Proof.
  intros. apply (minimal_in_inserted l' n m l) in H. 
    inversion H. inversion H2. apply lt_not_le in H0. apply ex_falso_quodlibet. apply H0.
      assumption. inversion H2. assumption. assumption.
Qed.

Lemma insert_sorted_exists : 
  forall l n, list_sorted l -> {l' | list_insert n l l' & list_sorted l'}.
Proof.
  intros. induction l. 
    exists [n]. apply li_Head. apply ls_One.
    remember (le_gt_dec n a) as A. 
    inversion A. 
      exists (n::a::l). 
        apply li_Head. 
        apply (ls_Cons n a (a::l)). assumption. 
        apply minimal_in_sorted. assumption. assumption.
    assert (L: list_sorted l). inversion H. apply ls_Nil. assumption.
    apply IHl in L. inversion L.
      exists (a::x). apply li_Tail. assumption. 
        inversion H. rewrite <- H5 in H1. inversion H1.
          apply ls_Cons with n. apply ls_One. apply mil_Base. omega.
          remember (le_gt_dec m n) as A1.
          inversion A1.
            assert (M: minimal_in_list m x). 
              apply (minimal_in_inserted_preserve x n m l); assumption.
            apply ls_Cons with m; assumption.
            assert (M: minimal_in_list n x). 
              apply (minimal_in_inserted_swap n m l x); assumption.
            apply ls_Cons with n; try assumption; omega.
Qed.

Theorem list_sort_exists : forall l, { l' | list_permutation l' l & list_sorted l'}.
Proof.
  intros. induction l.
    exists []. apply lp_Nil. apply ls_Nil.
    inversion IHl. 
      apply (insert_sorted_exists x a) in H0. inversion H0.
      exists x0. 
        apply lp_Cons with x; assumption. assumption.
Qed.

Inductive lists_merged : list nat -> list nat -> list nat -> Prop :=
  lm_LeftNil  : forall l, lists_merged [] l l
| lm_RightNil : forall l, lists_merged l [] l
| lm_Le       : forall m n l l' l'', m < n -> lists_merged l (n::l') l'' -> 
                                              lists_merged (m::l) (n::l') (m::l'')
| lm_Gt       : forall m n l l' l'', n <= m -> lists_merged (m::l) l' l'' ->
                                               lists_merged (m::l) (n::l') (n::l'').

Lemma merge_sorted_exists : forall l l', 
  list_sorted l -> list_sorted l' -> {l'' | lists_merged l l' l'' & list_sorted l''}.
Proof. admit. Qed.
(*
  intros l. induction l'.
    intros. exists l. apply lm_RightNil. assumption.
    intros. destruct l eqn: L. 
      exists (a::l'). apply lm_LeftNil. assumption.
      remember (le_gt_dec a n) as A. clear HeqA. inversion A.
         apply IHl' in H. inversion H. exists (a::x). apply lm_Gt. assumption. assumption.
*)
Definition sort (l : list nat) : list nat := 
  match list_sort_exists l with exist2 r _ _ => r end.
            
Extraction Language Ocaml.

Set Extraction AccessOpaque.

Extraction "sort.ml" sort.
        
Theorem pred_exists : forall n, n > 0 -> {m | S m = n}.
Proof.
  intros. destruct n. omega. 
  exists n. reflexivity.
Qed.

Definition pred (n : nat) : n > 0 -> nat := fun ev =>
  proj1_sig (pred_exists n ev).

Extraction "pred.ml" pred.

Inductive id : Type :=
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
     left. rewrite Heq. reflexivity.
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

(** The following lemmas will be useful for rewriting terms involving [eq_id_dec]. *)

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
    reflexivity.
    apply ex_falso_quodlibet; apply n; reflexivity. Qed.

(** **** Exercise: 1 star, optional (neq_id) *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
 intros.
 destruct (eq_id_dec x y). contradiction. reflexivity.
Qed.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(** For proofs involving states, we'll need several simple properties
    of [update]. *)

(** **** Exercise: 1 star (update_eq) *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros. unfold update. apply eq_id.
Qed.

(** **** Exercise: 1 star (update_neq) *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  intros. unfold update. apply neq_id. assumption.
Qed.

(** **** Exercise: 1 star (update_example) *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros. unfold update. simpl. unfold empty_state. reflexivity.
Qed.

(** **** Exercise: 1 star (update_shadow) *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros. unfold update. destruct (eq_id_dec x2 x1) eqn:D.
    reflexivity.
    reflexivity.
Qed.

(** **** Exercise: 2 stars (update_same) *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. destruct (eq_id_dec x1 x2). rewrite <- e. symmetry. assumption.
  reflexivity.
Qed.

(** **** Exercise: 3 stars (update_permute) *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros. unfold update. 
  destruct (eq_id_dec x1 x3) eqn: D1. rewrite e in H. 
    destruct (eq_id_dec x2 x3) eqn: D2. contradiction. reflexivity.
    reflexivity.
Qed.  

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                       
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
match prog with
| [] => stack
| (SPush n)::prog' => s_execute st (n :: stack) prog'
| (SLoad i)::prog' => s_execute st (st i :: stack) prog'
| op::prog' =>
   match stack with
   | y::x::stack' => 
      s_execute 
        st
        (((match op with 
           | SPlus => plus 
           | SMinus => minus 
           | SMult => mult 
           | _ => plus 
           end) x y)::stack')
        prog'
   | _ => s_execute st stack prog'
   end
end.

Lemma s_execute_composition : forall p st s s' s'' p', 
  s_execute st s p  = s' -> s_execute st s' p' = s'' -> s_execute st s (p ++ p') = s''.
Proof. admit. Qed.

Hint Resolve s_execute_composition.

Theorem compiler_exists : 
  forall (e : aexp), {p : list sinstr | forall st s, s_execute st s p = (aeval st e)::s}.
Proof.
  intros. induction e.
    exists [SPush n]. eauto.
    exists [SLoad i]. eauto.
    inversion IHe1. inversion IHe2. exists (x ++ x0 ++ [SPlus]). eauto. 
    inversion IHe1. inversion IHe2. exists (x ++ x0 ++ [SMinus]). eauto. 
    inversion IHe1. inversion IHe2. exists (x ++ x0 ++ [SMult]). eauto.
Qed.

Definition compile (e : aexp) :=
  proj1_sig (compiler_exists e).

Extraction "compile.ml" compile.

Inductive snoc : nat -> list nat -> list nat -> Prop :=
  snoc_Nil  : forall n, snoc n [] [n]
| snoc_Cons : forall n m l l', snoc n l l' -> snoc n (m::l) (m::l').

Theorem snoc_exists : forall n l, {l' | snoc n l l'}.
Proof.
  intros. induction l.
  exists [n]. apply snoc_Nil.
  inversion IHl. exists (a::x). apply snoc_Cons. assumption.
Qed.

Inductive reverse : list nat -> list nat -> Prop :=
  reverse_Nil  : reverse [] []
| reverse_Cons : forall n l l' l'', reverse l l' -> snoc n l' l'' -> reverse (n::l) l''.

Theorem reverse_exists : forall l, {l' | reverse l l'}.
Proof.
  intros. induction l.
    exists []. apply reverse_Nil.
    inversion IHl. assert (S: {m | snoc a x m}). apply snoc_exists. 
      inversion S. exists x0. apply reverse_Cons with x. assumption. assumption.
Qed.

Definition rev l := proj1_sig (reverse_exists l).

Extraction "rev.ml" rev.

Inductive counted (X : Set) : nat -> Set := count : forall n, X -> counted X n.

Definition ret  (X : Set) (x : X) : counted X 0 := count X 0 x.

Definition bind (X Y : Set) {n m : nat} : counted X n -> (X -> counted Y m) -> counted Y (m+n) :=
  fun c f => 
    match c with count n x => 
      match f x with count m y => count Y (m+n) y end
    end.

Definition increment (X : Set) {n : nat} : counted X n -> counted X (S n) := fun c =>
  match c with count n x => count X (S n) x end.

Notation "A >>= B" := (bind A B) (at level 90, right associativity).

Definition zero_counted := ret nat 80.

Print zero_counted.

Definition one_counted := increment nat zero_counted.

Print one_counted.

Fixpoint csum (n m : nat) : counted nat n := 
  match n with
  | 0    => ret nat m
  | S n' => increment nat (csum n' m)
  end.

Definition clength (X : Type) (l : list X) : counted nat (length l).
  destruct l; simpl; constructor; constructor.
Defined.

Extraction "clength.ml" clength.




  
  