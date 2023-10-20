From Coq Require Import PeanoNat.

From Derp Require Import Bool.
From Derp Require Import DeltaGraph.
From Derp Require Import Denotation.
From Derp Require Import Popcount.
From Derp Require Import Vector.

Import Vector.VectorNotations.

Definition CDG (ctx: Ctx) := DG ctx.(len).

Definition step (ctx: Ctx) (prev: CDG ctx) : CDG ctx :=
  let next l1 :=
    match l1 with
    | emptyF => false
    | epsF => true
    | charF _ => false
    | catF l r => prev[@l] && prev[@r]
    | altF l r => prev[@l] || prev[@r]
    | repF _ => true
    end
  in map next ctx.(langs).

Fixpoint iter (ctx: Ctx) (n: nat) : CDG ctx :=
  match n with
  | 0 => DeltaGraph.bottom _
  | S n' => step _ (iter _ n')
  end.

Definition deltas (ctx: Ctx) : CDG ctx :=
  iter ctx ctx.(len).

Inductive DeltaF (ctx: Ctx) (P: LangF (Idx ctx) -> Prop) :
  LangF (Idx ctx) -> Prop :=
| DF_eps : DeltaF ctx P epsF
| DF_cat : forall l r,
    P ctx.(langs)[@l] ->
    P ctx.(langs)[@r] ->
    DeltaF ctx P (catF l r)
| DF_alt1 : forall l r,
    P ctx.(langs)[@l] ->
    DeltaF ctx P (altF l r)
| DF_alt2 : forall l r,
    P ctx.(langs)[@r] ->
    DeltaF ctx P (altF l r)
| DF_rep : forall l,
    DeltaF ctx P (repF l).

Fixpoint DeltaN (ctx: Ctx) n : LangF (Idx ctx) -> Prop :=
  match n with
  | 0 => fun l => False
  | S n' => fun l => DeltaF ctx (DeltaN ctx n') l
  end.

Lemma DeltaNLift1 (ctx: Ctx) : forall n l,
    DeltaN ctx n l -> DeltaN ctx (S n) l.
Proof.
  intros n. induction n; intros l H.
  - inversion H.
  - inversion H; subst.
    + apply DF_eps.
    + apply DF_cat; apply IHn; assumption.
    + apply DF_alt1. apply IHn. assumption.
    + apply DF_alt2. apply IHn. assumption.
    + apply DF_rep.
Qed.

Lemma DeltaNLift (ctx: Ctx) : forall n m l,
    n <= m -> DeltaN ctx n l -> DeltaN ctx m l.
Proof.
  intros n m l Hnm H. induction Hnm.
  - apply H.
  - apply DeltaNLift1. apply IHHnm.
Qed.

Module Step.

  Definition post (ctx: Ctx) (g: CDG ctx) n i : Set :=
    reflect (DeltaN _ n ctx.(langs)[@i]) g[@i].

  Definition pre (ctx: Ctx) (prev: CDG ctx) n i : Set :=
    match ctx.(langs)[@i] with
    | catF l r => post ctx prev n l * post ctx prev n r
    | altF l r => post ctx prev n l * post ctx prev n r
    | _ => True
    end.

  Theorem correct (ctx: Ctx) (prev: CDG ctx) : forall n i,
      pre ctx prev n i ->
      post ctx (step ctx prev) (S n) i.
  Proof.
    intros n i Hpre.
    unfold pre in Hpre. unfold step, post.
    rewrite map_idx.
    destruct ctx.(langs)[@i] eqn:E.
    - apply ReflectF. intros Contra. inversion Contra.
    - apply ReflectT. apply DF_eps.
    - apply ReflectF. intros Contra. inversion Contra.
    - unfold post in Hpre. simpl.
      destruct Hpre as [Hl Hr]. destruct Hl.
      + destruct Hr.
        * apply ReflectT. apply DF_cat; assumption.
        * apply ReflectF. intros Contra.
          inversion Contra; contradiction.
      + apply ReflectF. intros Contra.
        inversion Contra; contradiction.
    - unfold post in Hpre. simpl.
      destruct Hpre as [Hl Hr]. destruct Hl.
      + apply ReflectT. apply DF_alt1; assumption.
      + destruct Hr.
        * apply ReflectT. apply DF_alt2; assumption.
        * apply ReflectF. intros Contra.
          inversion Contra; contradiction.
    - apply ReflectT. apply DF_rep.
  Qed.

  Theorem top (ctx: Ctx) : forall g,
      step ctx g = DeltaGraph.top (len ctx) ->
      step ctx (DeltaGraph.top (len ctx)) = DeltaGraph.top (len ctx).
  Proof.
    intros. apply eq_index. intros i.
    set (proj2 (eq_index _ _) H i) as Hprev.
    unfold DeltaGraph.top in *. repeat rewrite const_idx in *.
    unfold step in *. repeat rewrite map_idx in *.
    destruct (langs ctx)[@i]; try discriminate; try reflexivity.
    - repeat rewrite const_idx. reflexivity.
    - repeat rewrite const_idx. reflexivity.
  Qed.

End Step.

Module Iter.

  Theorem correct (ctx: Ctx) : forall n i,
      Step.post ctx (iter ctx n) n i.
  Proof.
    intros n. induction n; intros i.
    - simpl. unfold Step.post, DeltaN, DeltaGraph.bottom.
      rewrite const_idx. apply ReflectF. auto.
    - apply Step.correct. unfold Step.pre.
      destruct ctx.(langs)[@i]; auto.
  Qed.

  Theorem monotone (ctx: Ctx) : forall n,
      DeltaGraph.le (iter ctx n) (iter ctx (S n)).
  Proof with (repeat rewrite map_idx in *).
    unfold DeltaGraph.le. intros n. induction n.
    - simpl. apply DeltaGraph.Bottom. apply I.
    - simpl. apply Forall2_indexes. intros i.
      unfold step...
      destruct (langs ctx)[@i]; try apply le_refl...
      + set (proj2 Forall2_indexes IHn) as IH. simpl in IH.
        apply andb_monotone.
        * specialize (IH l). unfold step in IH... apply IH.
        * specialize (IH r). unfold step in IH... apply IH.
      + set (proj2 Forall2_indexes IHn) as IH. simpl in IH.
        apply orb_monotone.
        * specialize (IH l). unfold step in IH... apply IH.
        * specialize (IH r). unfold step in IH... apply IH.
  Qed.

  Lemma bitflip (ctx: Ctx) : forall n pc,
      popcount (iter ctx n) >= pc ->
      iter ctx n <> iter ctx (S n) ->
      popcount (iter ctx (S n)) >= S pc.
  Proof.
    intros. apply (Popcount.bitflip _ (iter ctx n) (iter ctx (S n))).
    - assumption.
    - apply monotone.
    - assumption.
  Qed.

  Theorem popcount_monotone (ctx: Ctx) : forall n,
      popcount (iter ctx n) >= n
      \/ iter ctx n = iter ctx (S n).
  Proof.
    intros n. induction n.
    - simpl. left. apply le_0_n.
    - inversion IHn; subst.
      + destruct (DeltaGraph.eq_dec (iter ctx n) (iter ctx (S n))).
        * right. unfold iter. f_equal. fold iter. apply e.
        * left. apply bitflip; assumption.
      + right. unfold iter. f_equal. fold iter. apply H.
  Qed.

  Theorem top (ctx: Ctx) : forall n,
      iter ctx n = DeltaGraph.top (len ctx) ->
      step ctx (DeltaGraph.top (len ctx)) = DeltaGraph.top (len ctx).
  Proof.
    destruct ctx. generalize dependent langs.
    destruct len; intros; simpl in *.
    - unfold step.
      change (Denotation.langs {| len := 0; langs := langs |})
        with langs.
      rewrite (is_nil langs). reflexivity.
    - destruct n; simpl in *.
      + inversion H.
      + apply (Step.top _ _ H).
  Qed.

  Theorem fixpoint1 (ctx: Ctx) :
    iter ctx ctx.(len) = iter ctx (S ctx.(len)).
  Proof.
    destruct (popcount_monotone ctx ctx.(len)).
    - assert (popcount (iter ctx ctx.(len)) = ctx.(len)). {
        apply Nat.le_antisymm.
        - apply Popcount.max.
        - apply H. }
      set (Popcount.top _ H0) as Htop.
      change (iter ctx (S (len ctx))) with
        (step ctx (iter ctx (len ctx))).
      rewrite Htop. symmetry. apply (top _ _ Htop).
    - assumption.
  Qed.

  Theorem fixpoint (ctx: Ctx) : forall n,
      ctx.(len) < n -> iter ctx ctx.(len) = iter ctx n.
  Proof.
    intros. induction H.
    - apply fixpoint1.
    - change (iter ctx (S m)) with (step ctx (iter ctx m)).
      rewrite <- IHle. rewrite fixpoint1 at 1.
      reflexivity.
  Qed.

End Iter.

Module DeltaDenotation.

  Theorem forward (ctx: Ctx) : forall n i,
      DeltaN ctx n ctx.(langs)[@i] -> Delta (Denotation ctx i).
  Proof.
    intros n. induction n; intros.
    - inversion H.
    - rewrite (LangDecompose (Denotation _ _)); simpl.
      simpl in H.
      destruct ctx.(langs)[@i].
      + inversion H.
      + apply DL_eps.
      + inversion H.
      + inversion H. apply DL_cat; apply IHn; assumption.
      + inversion H.
        * apply DL_alt1. apply IHn. assumption.
        * apply DL_alt2. apply IHn. assumption.
      + apply DL_rep.
  Qed.

  Theorem reverse_exists (ctx: Ctx) : forall i,
      Delta (Denotation ctx i) ->
      exists n, DeltaN ctx n ctx.(langs)[@i].
  Proof.
    intros.
    rewrite (LangDecompose (Denotation _ _)) in H; simpl in H.
    match goal with
    | _ : Delta ?x |- _ => remember x as discrim
    end.
    generalize dependent i.
    induction H; intros;
      destruct (langs ctx)[@i];
      inversion Heqdiscrim; subst.
    - exists 1. apply DF_eps.
    - rewrite (LangDecompose (Denotation _ _)) in IHDelta1.
      rewrite (LangDecompose (Denotation _ _)) in IHDelta2.
      specialize (IHDelta1 l0 eq_refl). destruct IHDelta1 as [nl Dl].
      specialize (IHDelta2 r0 eq_refl). destruct IHDelta2 as [nr Dr].
      exists (S (max nl nr)). apply DF_cat.
      + eapply DeltaNLift. apply Nat.le_max_l. apply Dl.
      + eapply DeltaNLift. apply Nat.le_max_r. apply Dr.
    - rewrite (LangDecompose (Denotation _ _)) in IHDelta.
      specialize (IHDelta l0 eq_refl). destruct IHDelta as [nl Dl].
      exists (S nl). apply DF_alt1. apply Dl.
    - rewrite (LangDecompose (Denotation _ _)) in IHDelta.
      specialize (IHDelta r0 eq_refl). destruct IHDelta as [nr Dr].
      exists (S nr). apply DF_alt2. apply Dr.
    - exists 1. apply DF_rep.
  Qed.

  Theorem reverse (ctx: Ctx) : forall i,
      Delta (Denotation ctx i) ->
      DeltaN ctx ctx.(len) ctx.(langs)[@i].
  Proof.
    intros. destruct (reverse_exists ctx i H) as [n Hn].
    destruct (Nat.le_gt_cases n ctx.(len)).
    - apply (DeltaNLift _ _ _ _ H0 Hn).
    - assert ((iter ctx ctx.(len))[@i] = (iter ctx n)[@i]).
      { rewrite (Iter.fixpoint _ _ H0). reflexivity. }
      destruct (Iter.correct ctx n i); try contradiction.
      destruct (Iter.correct ctx ctx.(len) i); try discriminate.
      assumption.
  Qed.

End DeltaDenotation.

Theorem delta_correct (ctx: Ctx) : forall i,
    reflect (Delta (Denotation ctx i)) (deltas ctx)[@i].
Proof.
  intros i.
  set (Iter.correct ctx ctx.(len) i) as Hv.
  unfold Step.post in Hv. unfold deltas.
  destruct Hv.
  - apply ReflectT.
    apply DeltaDenotation.forward with (len ctx). assumption.
  - apply ReflectF. intros Contra. apply n.
    apply DeltaDenotation.reverse. assumption.
Qed.
