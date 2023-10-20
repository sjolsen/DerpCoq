From Coq Require Import PeanoNat.
From Coq Require Export Vector.

Import Vector.VectorNotations.

Theorem rect3 {A B C}
  (P: forall n, t A n -> t B n -> t C n -> Type)
  (bas : P 0 [] [] [])
  (rect : forall {n v1 v2 v3},
      P n v1 v2 v3 ->
      forall a b c, P _ (a :: v1) (b :: v2) (c :: v3)) :
  forall {n} (v1 : t A n) (v2 : t B n) (v3 : t C n), P _ v1 v2 v3.
Proof.
  intros n v1. induction v1; intros v2 v3.
  - apply case0.
    apply (case0 (fun v2 => P 0 [] v2 [])).
    apply bas.
  - apply caseS'.
    intros h0 t.
    apply (caseS' _ (fun v2 => P (S n) (h :: v1) v2 (h0 :: t))).
    intros h1 t0.
    apply rect. apply IHv1.
Defined.

Theorem nth_0 {A n} {l: t A (S n)} :
  l[@Fin.F1] = hd l.
Proof.
  apply rectS with (v := l).
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
Qed.

Theorem nth_S {A n h} {t: t A n} : forall i,
    (h :: t)[@Fin.FS i] = t[@i].
Proof. intros. simpl. reflexivity. Qed.

Theorem is_nil {A} (l: t A 0) : l = nil _.
Proof. apply case0 with (v := l). reflexivity. Qed.

Theorem is_cons {A n} (l: t A (S n)) :
  exists h t, l = (h :: t).
Proof.
  apply caseS' with (v := l). intros h t.
  exists h. exists t. reflexivity.
Qed.

Lemma eq_index {A} {n} (v1 v2: t A n) :
  (forall i, v1[@i] = v2[@i]) <-> v1 = v2.
Proof.
  split.
  - generalize dependent n. induction n; intros.
    + apply case0 with (v := v1).
      apply case0 with (v := v2).
      reflexivity.
    + destruct (is_cons v1) as [h1 [t1 E1]]. rewrite E1 in *.
      destruct (is_cons v2) as [h2 [t2 E2]]. rewrite E2 in *.
      f_equal.
      * apply (H Fin.F1).
      * apply IHn. intros i. apply (H (Fin.FS i)).
  - intros H i. rewrite H. reflexivity.
Qed.

Fixpoint indexes n : t (Fin.t n) n :=
  match n with
  | 0 => []
  | S n' => cons _ Fin.F1 _ (map Fin.FS (indexes n'))
  end.

Theorem map_idx {A B} {f: A -> B} {n} {l: t A n} :
  forall i, (map f l)[@i] = f l[@i].
Proof.
  intros i. induction i.
  - destruct (is_cons l) as [h [t E]]. rewrite E in *.
    reflexivity.
  - destruct (is_cons l) as [h [t E]]. rewrite E in *.
    simpl. apply IHi.
Qed.

Theorem indexes_idx n : forall i, (indexes n)[@i] = i.
Proof.
  intros i. induction i.
  - reflexivity.
  - simpl. rewrite map_idx. rewrite IHi. reflexivity.
Qed.

Theorem const_idx {A} (x: A) n : forall i, (const x n)[@i] = x.
Proof.
  intros i. induction i.
  - reflexivity.
  - simpl. exact IHi.
Qed.

Theorem Forall2_uncons
  {A B} {P: A -> B -> Prop} {n h1 h2 t1 t2} :
  @Forall2 _ _ P (S n) (h1 :: t1) (h2 :: t2) ->
  P h1 h2 /\ @Forall2 _ _ P n t1 t2.
Proof.
  intros H.
  inversion H; subst. split; [assumption|].
  set (projT2_eq H2) as Hv1.
  set (projT2_eq H5) as Hv2.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in Hv1 by apply Nat.eq_dec.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in Hv2 by apply Nat.eq_dec.
  simpl in Hv1. simpl in Hv2.
  rewrite Hv1 in H6. rewrite Hv2 in H6.
  apply H6.
Qed.

Theorem Forall2_indexes
  {A B} {P: A -> B -> Prop} {n}
  {l1: t A n} {l2: t B n} :
  (forall i, P l1[@i] l2[@i]) <-> Forall2 P l1 l2.
Proof.
  split.
  - apply rect2 with
      (P := fun n0 v1 v2 =>
              (forall i : Fin.t n0, P v1[@i] v2[@i]) ->
              Forall2 P v1 v2); intros.
    + apply Forall2_nil.
    + apply Forall2_cons.
      * set (H0 Fin.F1) as Hhead.
        repeat rewrite nth_0 in Hhead. simpl in Hhead.
        apply Hhead.
      * apply H. intros i. specialize (H0 (Fin.FS i)).
        repeat rewrite nth_S in H0. apply H0.
  - intros H i. induction i.
    + repeat rewrite nth_0.
      destruct (is_cons l1) as [h1 [t1 E1]].
      destruct (is_cons l2) as [h2 [t2 E2]].
      rewrite E1 in *. rewrite E2 in *.
      simpl.
      apply Forall2_uncons in H as [Hh Ht].
      apply Hh.
    + destruct (is_cons l1) as [h1 [t1 E1]].
      destruct (is_cons l2) as [h2 [t2 E2]].
      rewrite E1 in *. rewrite E2 in *.
      repeat rewrite nth_S. apply IHi.
      apply Forall2_uncons in H as [Hh Ht].
      apply Ht.
Qed.
