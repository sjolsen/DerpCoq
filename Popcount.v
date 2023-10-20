From Coq Require Import PeanoNat.

From Derp Require Import DeltaGraph.
From Derp Require Import Vector.

Fixpoint popcount {n} (g: DG n) : nat :=
  match g with
  | nil _ => 0
  | cons _ true _ t => S (popcount t)
  | cons _ false _ t => popcount t
  end.

Module Popcount.

Theorem max {n} (g: DG n) : popcount g <= n.
Proof.
  generalize dependent g.
  induction n; intros.
  - rewrite (is_nil g). apply le_0_n.
  - destruct (is_cons g) as [h [t E]]. rewrite E in *.
    simpl. destruct h.
    + apply le_n_S. apply IHn.
    + apply le_S. apply IHn.
Qed.

Theorem top {n} (g: DG n) : popcount g = n -> g = DeltaGraph.top n.
Proof.
  generalize dependent g.
  induction n; intros.
  - rewrite (is_nil g). reflexivity.
  - destruct (is_cons g) as [h [t E]]. rewrite E in *.
    inversion H; subst. destruct h.
    + unfold DeltaGraph.top, const, nat_rect. f_equal.
      apply IHn. simpl in H. injection H as H. apply H.
    + set (max t) as Ht. rewrite H1 in Ht.
      exfalso. apply (Nat.nle_succ_diag_l _ Ht).
Qed.

Theorem bitflip : forall n (g1 g2: DG n) pc,
  popcount g1 >= pc ->
  DeltaGraph.le g1 g2 ->
  g1 <> g2 ->
  popcount g2 >= S pc.
Proof.
  intros n. induction n; intros.
  - rewrite (is_nil g1) in *. rewrite (is_nil g2) in *.
    exfalso. apply H1. reflexivity.
  - destruct (is_cons g1) as [h1 [t1 E1]]. rewrite E1 in *.
    destruct (is_cons g2) as [h2 [t2 E2]]. rewrite E2 in *.
    destruct (Forall2_uncons H0).
    destruct h1; destruct h2.
    + apply le_n_S. destruct pc.
      * apply le_0_n.
      * apply (IHn t1 t2).
        -- apply le_S_n. apply H.
        -- unfold DeltaGraph.le in *. assumption.
        -- intros Contra. apply H1. f_equal. apply Contra.
    + unfold DeltaGraph.le in *.
      inversion H2.
    + simpl in H. destruct (DeltaGraph.eq_dec t1 t2).
      * apply le_n_S. rewrite e in H. apply H.
      * apply le_S. apply (IHn t1 t2).
        -- apply H.
        -- apply H3.
        -- apply n0.
    + apply (IHn t1 t2).
      -- apply H.
      -- apply H3.
      -- intros Contra. rewrite Contra in H1.
         apply H1. reflexivity.
Qed.

End Popcount.
