From Coq Require Import Sets.Cpo.

From Derp Require Import Bool.
From Derp Require Import Vector.

Definition DG n := Vector.t bool n.

Module DeltaGraph.

  Definition eq_dec {n} (g1 g2: DG n) :
    {g1 = g2} + {g1 <> g2} :=
    eq_dec _ Bool.eqb eqb_true_iff _ g1 g2.

  Definition le {n} (g1 g2: DG n) :=
    Forall2 (fun x1 x2 => Bool.le x1 x2) g1 g2.

  Definition bottom n : DG n :=
    const false _.

  Definition top n : DG n :=
    const true _.

  Theorem le_refl : forall n (g: DG n),
      le g g.
  Proof.
    intros n g.
    induction g; intros.
    * apply Forall2_nil.
    * apply Forall2_cons. apply le_refl. eapply IHg.
  Qed.

  Theorem le_trans : forall n (g1 g2 g3: DG n),
      le g1 g2 -> le g2 g3 -> le g1 g3.
  Proof.
    intros n g1 g2 g3.
    induction n, g1, g2, g3 using rect3.
    - intros. apply Forall2_nil.
    - intros.
      destruct (Forall2_uncons H).
      destruct (Forall2_uncons H0).
      apply Forall2_cons.
      + apply le_trans with b; assumption.
      + apply IHg3; assumption.
  Qed.

  Theorem le_antisym : forall n (g1 g2: DG n),
      le g1 g2 -> le g2 g1 -> g1 = g2.
  Proof.
    intros n g1 g2.
    apply rect2 with
      (P := fun n0 v1 v2 =>
              le v1 v2 ->
              le v2 v1 ->
              v1 = v2).
    - intros. reflexivity.
    - intros n0 v1 v2 IH a b H1 H2.
      destruct (Forall2_uncons H1) as [Hab Hv12].
      destruct (Forall2_uncons H2) as [Hba Hv21].
      f_equal.
      + apply Bool.le_antisym; assumption.
      + apply IH; assumption.
  Qed.

  Definition PartialOrder n : PO (DG n).
  Proof.
    apply Definition_of_PO with
      (Carrier_of := fun _ => True)
      (Rel_of := le).
    - apply Inhabited_intro with (bottom _).
      apply I.
    - unfold DG, le in *. simpl.
      apply Definition_of_order.
      + intros g.
        apply le_refl.
      + intros g1 g2 g3.
        apply le_trans.
      + intros g1 g2.
        apply le_antisym.
  Defined.

  Definition Bottom n : Bottom _ (PartialOrder n) (bottom n).
  Proof.
    apply Bottom_definition.
    - apply I.
    - induction n;
        intros g H; simpl in *; unfold le, bottom in *.
      + apply case0. apply Forall2_nil.
      + apply caseS'. intros h t. apply Forall2_cons.
        * apply false_le.
        * apply IHn. apply I.
  Defined.

End DeltaGraph.
