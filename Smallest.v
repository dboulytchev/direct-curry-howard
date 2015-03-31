Require Omega.   
Require Export Bool List.
Export ListNotations.
Require Export Arith Arith.EqNat.

(* Fixpoint definition of the smallest element *)

Fixpoint smallest' (n:nat) (l:list nat) : nat :=
  match l with 
  | []    => n 
  | x::xs => smallest' (if le_gt_dec n x then n else x) xs 
  end.

Definition smallest (l : list nat) : ([] <> l) -> nat := 
  match l with
  | []    => fun w => match w (eq_refl []) with end
  | x::xs => fun _ => smallest' x xs
  end.

(* Inductive proposition *)

Inductive is_smallest : nat -> list nat -> Prop :=
  smallest_unit : forall n, is_smallest n [n]
| smallest_head : forall n m tl, 
    n <= m -> is_smallest m tl -> is_smallest n (n::tl)
| smallest_tail : forall n m tl, 
    m <  n -> is_smallest m tl -> is_smallest m (n::tl).

Hint Constructors is_smallest.

(* Correctness proof *)
(* TODO: shorter! more automation! *)

Lemma smallest_le : forall (l : list nat) (n : nat), smallest' n l <= n.
Proof. 
  intro. induction l. auto.
    intros. simpl. destruct (le_gt_dec n a). auto.
    remember (IHl a). omega.
Qed.

Lemma smaller_then_smallest: forall (n a : nat) (l : list nat),
  a <= smallest' n l -> a <= n -> smallest' a l = a.
Proof.
  intros. generalize dependent n. 
  induction l. reflexivity.
    intros. simpl in H. destruct (le_gt_dec n a0);
      simpl; destruct (le_gt_dec a a0); eauto; try omega. 
      remember (smallest_le l a0). omega.
Qed.
  
Lemma smaller_is_smallest : forall (a n : nat) (l : list nat), 
  a <= smallest (n::l) (nil_cons (l:=l)) -> smallest (a::n::l) (nil_cons (l:=n::l)) = a.
Proof.
  intros. simpl in *. 
    assert (A: a<=n). remember (smallest_le l n). omega.
    destruct (le_gt_dec a n). 
      simpl in H. apply (smaller_then_smallest n a l); auto. omega.
Qed.

Lemma bigger_not_smallest : forall (a n : nat) (l : list nat), 
  a > smallest (n::l) (nil_cons (l:=l)) -> 
  smallest (a::n::l) (nil_cons (l:=n::l)) = smallest (n::l) (nil_cons (l:=l)).
Proof.
  intros. simpl in *. destruct (le_gt_dec a n). 
    generalize dependent n. induction l. intros. simpl in H. omega.
      intros. simpl in *. destruct (le_gt_dec a a0);
        destruct (le_gt_dec n a0); auto.
        destruct (le_gt_dec n a0); omega. reflexivity.
Qed.

Theorem smallest_is_smallest : 
  forall (l : list nat) (w : [] <> l), is_smallest (smallest l w) l.
Proof.
  intros. induction l. unfold not in w. exfalso. auto.
    destruct l eqn: L. auto.
      remember (IHl (nil_cons(l:=l0))) as A. 
      remember (le_gt_dec a (smallest (n::l0) (nil_cons (l:=l0)))) as A1. 
      inversion A1.
      assert (AA: smallest (a::n::l0) w = a). 
        apply (smaller_is_smallest a n l0). 
        auto. 
      rewrite AA.
      apply (smallest_head a (smallest (n::l0) (nil_cons(l:=l0))) (n::l0)); 
      auto. 
      assert (AA: smallest (a::n::l0) w = smallest (n::l0) (nil_cons (l:=l0))). 
        apply (bigger_not_smallest a n l0). 
        auto.
      rewrite AA. 
      eauto.
Qed.

(* Program Fixepoint definition *)

Program Fixpoint smallestFix (l : list nat) (H : [] <> l) :
    {n | is_smallest n l} :=
  match l with
  | [] => _
  | x :: xs =>
    match xs with
    | [] => x
    | y :: ys => min x (smallestFix xs _)
    end
  end.
Next Obligation.
  clear H.
  remember (Min.min_spec x x0) as H.
  inversion H; inversion H0; rewrite H2.
    apply (@smallest_head x x0).
      omega.
      assumption.
    set (@le_lt_eq_dec x0 x H1) as S.
      inversion S.
        apply (@smallest_tail x x0 _ H3); assumption.
        rewrite H3.
        apply (@smallest_head x x0).
        omega.
        assumption.
Defined.

(* Direct construction *)

Theorem smallest'' : 
  forall (l : list nat), [] <> l -> {n | is_smallest n l}.
Proof. 
  intros. 
    induction l. unfold not in H. exfalso. auto.
      destruct l eqn: L. exists a. auto. 
        remember (IHl (nil_cons(l:=l0))) as A.         
          inversion A.
        remember (le_gt_dec a x) as A1. 
          inversion A1. 
        exists a. eauto. 
        exists x. eauto. 
Defined.
  