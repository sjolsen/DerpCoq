From Coq Require Import PeanoNat.
From Coq Require Import Strings.Ascii.

From Derp Require Import Bool.
From Derp Require Import DeltaGraph.
From Derp Require Import Popcount.
From Derp Require Import Vector.

Import Vector.VectorNotations.

CoInductive Lang :=
| empty
| eps
| char (c: ascii)
| cat (l r: Lang)
| alt (l r: Lang)
| rep (l: Lang).

Definition LangDecomp (l1: Lang) : Lang :=
  match l1 with
  | empty => empty
  | eps => eps
  | char c => char c
  | cat l r => cat l r
  | alt l r => alt l r
  | rep l => rep l
  end.

Lemma LangDecompose (l1: Lang) : l1 = LangDecomp l1.
Proof. case l1; intros; auto. Qed.

CoInductive Bisim : Lang -> Lang -> Prop :=
| BS_empty : Bisim empty empty
| BS_eps : Bisim eps eps
| BS_char : forall c, Bisim (char c) (char c)
| BS_cat : forall l l' r r',
    Bisim l l' ->
    Bisim r r' ->
    Bisim (cat l r) (cat l' r')
| BS_alt : forall l l' r r',
    Bisim l l' ->
    Bisim r r' ->
    Bisim (alt l r) (alt l' r')
| BS_rep : forall l l',
    Bisim l l' ->
    Bisim (rep l) (rep l').

#[export]
Hint Constructors Bisim : core.

Inductive Delta : Lang -> Prop :=
| DL_eps : Delta eps
| DL_cat l r : Delta l -> Delta r -> Delta (cat l r)
| DL_alt1 l r : Delta l -> Delta (alt l r)
| DL_alt2 l r : Delta r -> Delta (alt l r)
| DL_rep l : Delta (rep l).

Inductive Derives (c: ascii) : Lang -> Lang -> Prop :=
| DR_empty : Derives c empty empty
| DR_eps : Derives c eps empty
| DR_char1 : Derives c (char c) eps
| DR_char2 : forall c',
    c <> c'
    -> Derives c (char c') empty
| DR_cat1 : forall l l' r r',
    Delta l ->
    Derives c l l' ->
    Derives c r r' ->
    Derives c (cat l r) (alt r' (cat l' r))
| DR_cat2 : forall l l' r,
    ~ Delta l ->
    Derives c l l' ->
    Derives c (cat l r) (cat l' r)
| DR_alt : forall l l' r r',
    Derives c l l' ->
    Derives c r r' ->
    Derives c (alt l r) (alt l' r')
| DR_rep : forall l l',
    Derives c l l' ->
    Derives c (rep l) (cat l' l).

Theorem Derives_functional : forall c l l'1 l'2,
    Derives c l l'1 -> Derives c l l'2 -> l'1 = l'2.
Proof.
  intros c l l'1 l'2 D1 D2. generalize dependent l'2.
  induction D1; intros l'2 D2;
    inversion D2; subst;
    try contradiction;
    repeat f_equal;
    try apply IHD1;
    try apply IHD1_1;
    try apply IHD1_2;
    auto.
Qed.

Inductive LangF (X: Type) :=
| emptyF
| epsF
| charF (c: ascii)
| catF (l r: X)
| altF (l r: X)
| repF (l: X).

Arguments emptyF {X}.
Arguments epsF {X}.
Arguments charF {X} _.
Arguments catF {X} _ _.
Arguments altF {X} _ _.
Arguments repF {X} _.

Record Ctx :=
  { len : nat
  ; langs : Vector.t (LangF (Fin.t len)) len
  }.

Definition Idx (ctx: Ctx) := Fin.t ctx.(len).

CoFixpoint Denotation (ctx: Ctx) (i: Idx ctx) : Lang :=
  match ctx.(langs)[@i] with
  | emptyF => empty
  | epsF => eps
  | charF c => char c
  | catF l r => cat (Denotation _ l) (Denotation _ r)
  | altF l r => alt (Denotation _ l) (Denotation _ r)
  | repF l => rep (Denotation _ l)
  end.

Definition CDG (ctx: Ctx) := DG ctx.(len).

Definition step (ctx: Ctx) (prev: CDG ctx) : CDG ctx :=
  let next n :=
    match ctx.(langs)[@n] with
    | emptyF => false
    | epsF => true
    | charF _ => false
    | catF l r => prev[@l] && prev[@r]
    | altF l r => prev[@l] || prev[@r]
    | repF _ => true
    end
  in map next (indexes ctx.(len)).

Fixpoint iter (ctx: Ctx) (n: nat) : CDG ctx :=
  match n with
  | 0 => DeltaGraph.bottom _
  | S n' => step _ (iter _ n')
  end.

Inductive DeltaF (ctx: Ctx)
  (P: LangF (Fin.t ctx.(len)) -> Prop) :
  LangF (Fin.t ctx.(len)) -> Prop :=
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

Fixpoint DeltaN (ctx: Ctx) n : LangF (Fin.t ctx.(len)) -> Prop :=
  match n with
  | 0 => fun l => False
  | S n' => fun l => DeltaF ctx (DeltaN ctx n') l
  end.

Definition DGReflect (ctx: Ctx) (g: CDG ctx) n i : Set :=
  reflect (DeltaN _ n ctx.(langs)[@i]) g[@i].

Definition StepPre (ctx: Ctx) (prev: CDG ctx) n i : Set :=
  match ctx.(langs)[@i] with
  | catF l r => DGReflect ctx prev n l * DGReflect ctx prev n r
  | altF l r => DGReflect ctx prev n l * DGReflect ctx prev n r
  | _ => True
  end.

Theorem StepCorrect (ctx: Ctx) (prev: CDG ctx) : forall n i,
    StepPre ctx prev n i ->
    DGReflect ctx (step ctx prev) (S n) i.
Proof.
  intros n i Hpre.
  unfold StepPre in Hpre.
  unfold step, DGReflect.
  rewrite map_idx. rewrite indexes_idx.
  destruct ctx.(langs)[@i] eqn:E.
  - apply ReflectF. intros Contra. inversion Contra.
  - apply ReflectT. apply DF_eps.
  - apply ReflectF. intros Contra. inversion Contra.
  - unfold DGReflect in Hpre. simpl.
    destruct Hpre as [Hl Hr]. destruct Hl.
    + destruct Hr.
      * apply ReflectT. apply DF_cat; assumption.
      * apply ReflectF. intros Contra.
        inversion Contra; contradiction.
    + apply ReflectF. intros Contra.
      inversion Contra; contradiction.
  - unfold DGReflect in Hpre. simpl.
    destruct Hpre as [Hl Hr]. destruct Hl.
    + apply ReflectT. apply DF_alt1; assumption.
    + destruct Hr.
      * apply ReflectT. apply DF_alt2; assumption.
      * apply ReflectF. intros Contra.
        inversion Contra; contradiction.
  - apply ReflectT. apply DF_rep.
Qed.

Theorem IterCorrect (ctx: Ctx) : forall n i,
    DGReflect ctx (iter ctx n) n i.
Proof.
  intros n. induction n; intros i.
  - simpl. unfold DGReflect, DeltaN, DeltaGraph.bottom.
    rewrite const_idx. apply ReflectF. auto.
  - apply StepCorrect. unfold StepPre.
    destruct ctx.(langs)[@i]; auto.
Qed.

Theorem iter_monotone (ctx: Ctx) : forall n,
    DeltaGraph.le (iter ctx n) (iter ctx (S n)).
Proof with (repeat rewrite map_idx in *;
            repeat rewrite indexes_idx in *).
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

Lemma StepPopcount (ctx: Ctx) : forall n pc,
  popcount (iter ctx n) >= pc ->
  iter ctx n <> iter ctx (S n) ->
  popcount (iter ctx (S n)) >= S pc.
Proof.
  intros. apply (Popcount.bitflip _ (iter ctx n) (iter ctx (S n))).
  - assumption.
  - apply iter_monotone.
  - assumption.
Qed.

Theorem IterPopcount (ctx : Ctx) : forall n,
    popcount (iter ctx n) >= n
    \/ iter ctx n = iter ctx (S n).
Proof.
  intros n. induction n.
  - simpl. left. apply le_0_n.
  - inversion IHn; subst.
    + destruct (DeltaGraph.eq_dec (iter ctx n) (iter ctx (S n))).
      * right. unfold iter. f_equal. fold iter. apply e.
      * left. apply StepPopcount; assumption.
    + right. unfold iter. f_equal. fold iter. apply H.
Qed.

Theorem StepTop (ctx: Ctx) : forall g,
    step ctx g = DeltaGraph.top (len ctx) ->
    step ctx (DeltaGraph.top (len ctx)) = DeltaGraph.top (len ctx).
Proof.
  intros. apply eq_index. intros i.
  set (proj2 (eq_index _ _) H i) as Hprev.
  unfold DeltaGraph.top in *. repeat rewrite const_idx in *.
  unfold step in *. repeat rewrite map_idx in *.
  repeat rewrite indexes_idx in *.
  destruct (langs ctx)[@i]; try discriminate; try reflexivity.
  - repeat rewrite const_idx. reflexivity.
  - repeat rewrite const_idx. reflexivity.
Qed.

Theorem IterTop (ctx: Ctx) : forall n,
    iter ctx n = DeltaGraph.top (len ctx) ->
    step ctx (DeltaGraph.top (len ctx)) = DeltaGraph.top (len ctx).
Proof.
  destruct ctx. generalize dependent langs0.
  destruct len0; intros; simpl in *.
  - reflexivity.
  - destruct n; simpl in *.
    + inversion H.
    + apply (StepTop _ _ H).
Qed.

Theorem IterFixpoint' (ctx : Ctx) :
    iter ctx ctx.(len) = iter ctx (S ctx.(len)).
Proof.
  destruct (IterPopcount ctx ctx.(len)).
  - assert (popcount (iter ctx ctx.(len)) = ctx.(len)). {
      apply Nat.le_antisymm.
      - apply Popcount.max.
      - apply H. }
    set (Popcount.top _ H0) as Htop.
    change (iter ctx (S (len ctx))) with
      (step ctx (iter ctx (len ctx))).
    rewrite Htop. symmetry. apply (IterTop _ _ Htop).
  - assumption.
Qed.

Theorem IterFixpoint (ctx : Ctx) : forall n,
    (ctx.(len) < n)%nat ->
    iter ctx ctx.(len) = iter ctx n.
Proof.
  intros. induction H.
  - apply IterFixpoint'.
  - change (iter ctx (S m)) with (step ctx (iter ctx m)).
    rewrite <- IHle. rewrite IterFixpoint' at 1.
    reflexivity.
Qed.

Theorem DeltaNDenotation1 (ctx: Ctx) : forall n i,
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
    (n <= m)%nat -> DeltaN ctx n l -> DeltaN ctx m l.
Proof.
  intros n m l Hnm H. induction Hnm.
  - apply H.
  - apply DeltaNLift1. apply IHHnm.
Qed.

Theorem DeltaNDenotation2Exists (ctx: Ctx) : forall i,
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

Theorem DeltaNDenotation2 (ctx: Ctx) : forall i,
    Delta (Denotation ctx i) ->
    DeltaN ctx ctx.(len) ctx.(langs)[@i].
Proof.
  intros. destruct (DeltaNDenotation2Exists ctx i H) as [n Hn].
  destruct (Nat.le_gt_cases n ctx.(len)).
  - apply (DeltaNLift _ _ _ _ H0 Hn).
  - assert ((iter ctx ctx.(len))[@i] = (iter ctx n)[@i]).
    { rewrite (IterFixpoint _ _ H0). reflexivity. }
    destruct (IterCorrect ctx n i); try contradiction.
    destruct (IterCorrect ctx ctx.(len) i); try discriminate.
    assumption.
Qed.

Theorem DeltaNDenotation (ctx: Ctx) : forall i,
    DeltaN ctx ctx.(len) ctx.(langs)[@i]
    <-> Delta (Denotation ctx i).
Proof.
  split; [apply DeltaNDenotation1|apply DeltaNDenotation2].
Qed.

Definition deltas (ctx: Ctx) : CDG ctx :=
  iter ctx ctx.(len).

Theorem DeltasCorrect (ctx: Ctx) : forall i,
    reflect (Delta (Denotation ctx i)) (deltas ctx)[@i].
Proof.
  intros i.
  set (IterCorrect ctx ctx.(len) i) as Hv.
  unfold DGReflect in Hv. unfold deltas.
  destruct Hv.
  - apply ReflectT.
    apply DeltaNDenotation. assumption.
  - apply ReflectF. intros Contra. apply n.
    apply DeltaNDenotation. assumption.
Qed.
