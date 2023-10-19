From Coq Require Import Bool.
From Coq Require Import Bool.BoolOrder.
From Coq Require Import PeanoNat.
From Coq Require Import Sets.Cpo.
From Coq Require Import Strings.Ascii.
From Coq Require Import Vector.
Import Bool.BoolNotations.
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

#[local]
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

Definition DeltaGraph n := Vector.t bool n.

Definition DGLess n (g1 g2: DeltaGraph n) :=
  Forall2 (fun x1 x2 => x1 <= x2) g1 g2.

Definition DGBottom n : DeltaGraph n :=
  const false _.

Definition DGTop n : DeltaGraph n :=
  const true _.

Theorem DGLess_refl : forall n (g: DeltaGraph n),
    Forall2 (fun x1 x2 => x1 <= x2) g g.
Proof.
  intros n g.
  induction g; intros.
  * apply Forall2_nil.
  * apply Forall2_cons. apply le_refl. eapply IHg.
Qed.

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

Theorem forall_uncons
  {A B} {P: A -> B -> Prop} {n h1 h2 t1 t2} :
  @Forall2 _ _ P (S n) (h1 :: t1) (h2 :: t2) ->
  P h1 h2 /\ @Forall2 _ _ P n t1 t2.
Proof.
  intros H.
  inversion H; subst. split; [assumption|].
  set (projT2_eq H2) as Hv1.
  set (projT2_eq H5) as Hv2.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in Hv1 by apply PeanoNat.Nat.eq_dec.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in Hv2 by apply PeanoNat.Nat.eq_dec.
  simpl in Hv1. simpl in Hv2.
  rewrite Hv1 in H6. rewrite Hv2 in H6.
  apply H6.
Qed.

Theorem DGLess_trans : forall n (g1 g2 g3: DeltaGraph n),
    Forall2 (fun x1 x2 => x1 <= x2) g1 g2 ->
    Forall2 (fun x1 x2 => x1 <= x2) g2 g3 ->
    Forall2 (fun x1 x2 => x1 <= x2) g1 g3.
Proof.
  intros n g1 g2 g3.
  induction n, g1, g2, g3 using rect3.
  - intros. apply Forall2_nil.
  - intros.
    destruct (forall_uncons H).
    destruct (forall_uncons H0).
    apply Forall2_cons.
    + apply le_trans with b; assumption.
    + apply IHg3; assumption.
Qed.

Lemma le_antisym : forall a b, a <= b -> b <= a -> a = b.
  intros a b H1 H2.
  destruct a; destruct b; try reflexivity.
  - inversion H1.
  - inversion H2.
Qed.

Theorem DGLess_antisym : forall n (g1 g2: DeltaGraph n),
    Forall2 (fun x1 x2 => x1 <= x2) g1 g2 ->
    Forall2 (fun x1 x2 => x1 <= x2) g2 g1 ->
    g1 = g2.
Proof.
  intros n g1 g2.
  apply rect2 with
    (P := fun n0 v1 v2 =>
            Forall2 (fun x1 x2 : bool => x1 <= x2) v1 v2 ->
            Forall2 (fun x1 x2 : bool => x1 <= x2) v2 v1 ->
            v1 = v2).
  - intros. reflexivity.
  - intros n0 v1 v2 IH a b H1 H2.
    destruct (forall_uncons H1) as [Hab Hv12].
    destruct (forall_uncons H2) as [Hba Hv21].
    f_equal.
    + apply le_antisym; assumption.
    + apply IH; assumption.
Qed.

Definition DGLessPO n : PO (DeltaGraph n).
Proof.
  apply Definition_of_PO with
    (Carrier_of := fun _ => True)
    (Rel_of := DGLess n).
  - apply Inhabited_intro with (DGBottom _).
    apply I.
  - unfold DeltaGraph, DGLess in *. simpl.
    apply Definition_of_order.
    + intros g.
      apply DGLess_refl.
    + intros g1 g2 g3.
      apply DGLess_trans.
    + intros g1 g2.
      apply DGLess_antisym.
Defined.

Definition DGBottom_bottom n : Bottom _ (DGLessPO n) (DGBottom n).
Proof.
  apply Bottom_definition.
  - apply I.
  - induction n;
      intros g H; simpl in *; unfold DGLess, DGBottom in *.
    + apply case0. apply Forall2_nil.
    + apply caseS'. intros h t. apply Forall2_cons.
      * apply false_le.
      * apply IHn. apply I.
Defined.

Fixpoint indexes n : Vector.t (Fin.t n) n :=
  match n with
  | 0 => []
  | S n' => cons _ Fin.F1 _ (map Fin.FS (indexes n'))
  end.

Definition CDG (ctx: Ctx) := DeltaGraph ctx.(len).

Definition dgstep (ctx: Ctx) (prev: CDG ctx) : CDG ctx :=
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

Fixpoint dgiter (ctx: Ctx) (n: nat) : CDG ctx :=
  match n with
  | 0 => DGBottom _
  | S n' => dgstep _ (dgiter _ n')
  end.

Lemma nth_0 {A n} {l: Vector.t A (S n)} :
  l[@Fin.F1] = hd l.
Proof.
  apply rectS with (v := l).
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
Qed.

Lemma nth_S {A n h} {t: Vector.t A n} : forall i,
    (h :: t)[@Fin.FS i] = t[@i].
Proof. intros. simpl. reflexivity. Qed.

Theorem is_nil {A} (l: Vector.t A 0) : l = nil _.
Proof. apply case0 with (v := l). reflexivity. Qed.

Theorem is_cons {A n} (l: Vector.t A (S n)) :
  exists h t, l = (h :: t).
Proof.
  apply caseS' with (v := l). intros h t.
  exists h. exists t. reflexivity.
Qed.

Lemma Forall2_indexes
  {A B} {P: A -> B -> Prop} {n}
  {l1: Vector.t A n} {l2: Vector.t B n} :
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
      apply forall_uncons in H as [Hh Ht].
      apply Hh.
    + destruct (is_cons l1) as [h1 [t1 E1]].
      destruct (is_cons l2) as [h2 [t2 E2]].
      rewrite E1 in *. rewrite E2 in *.
      repeat rewrite nth_S. apply IHi.
      apply forall_uncons in H as [Hh Ht].
      apply Ht.
Qed.

Lemma map_idx {A B} {f: A -> B} {n} {l: Vector.t A n} :
  forall i, (map f l)[@i] = f l[@i].
Proof.
  intros i. induction i.
  - destruct (is_cons l) as [h [t E]]. rewrite E in *.
    reflexivity.
  - destruct (is_cons l) as [h [t E]]. rewrite E in *.
    simpl. apply IHi.
Qed.

Lemma indexes_idx n : forall i, (indexes n)[@i] = i.
Proof.
  intros i. induction i.
  - reflexivity.
  - simpl. rewrite map_idx. rewrite IHi. reflexivity.
Qed.

Lemma const_idx {A} (x: A) n : forall i, (const x n)[@i] = x.
Proof.
  intros i. induction i.
  - reflexivity.
  - simpl. exact IHi.
Qed.

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

Definition DGStepPre (ctx: Ctx) (prev: CDG ctx) n i : Set :=
  match ctx.(langs)[@i] with
  | catF l r => DGReflect ctx prev n l * DGReflect ctx prev n r
  | altF l r => DGReflect ctx prev n l * DGReflect ctx prev n r
  | _ => True
  end.

Theorem DGStepCorrect (ctx: Ctx) (prev: CDG ctx) : forall n i,
    DGStepPre ctx prev n i ->
    DGReflect ctx (dgstep ctx prev) (S n) i.
Proof.
  intros n i Hpre.
  unfold DGStepPre in Hpre.
  unfold dgstep, DGReflect.
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

Theorem DGIterCorrect (ctx: Ctx) : forall n i,
    DGReflect ctx (dgiter ctx n) n i.
Proof.
  intros n. induction n; intros i.
  - simpl. unfold DGReflect, DeltaN, DGBottom.
    rewrite const_idx. apply ReflectF. auto.
  - apply DGStepCorrect. unfold DGStepPre.
    destruct ctx.(langs)[@i]; auto.
Qed.

Lemma andb_monotone : forall a b c d,
    a <= c -> b <= d -> a && b <= c && d.
Proof.
  intros a b c d H1 H2.
  destruct a; destruct b; destruct c; destruct d;
    simpl in *; auto.
Qed.

Lemma orb_monotone : forall a b c d,
    a <= c -> b <= d -> a || b <= c || d.
Proof.
  intros a b c d H1 H2.
  destruct a; destruct b; destruct c; destruct d;
    simpl in *; auto.
Qed.

Theorem dgiter_monotone (ctx: Ctx) : forall n,
    DGLess _ (dgiter ctx n) (dgiter ctx (S n)).
Proof with (repeat rewrite map_idx in *;
            repeat rewrite indexes_idx in *).
  unfold DGLess. intros n. induction n.
  - simpl. apply DGBottom_bottom. apply I.
  - simpl. apply Forall2_indexes. intros i.
    unfold dgstep...
    destruct (langs ctx)[@i]; try apply le_refl...
    + set (proj2 Forall2_indexes IHn) as IH. simpl in IH.
      apply andb_monotone.
      * specialize (IH l). unfold dgstep in IH... apply IH.
      * specialize (IH r). unfold dgstep in IH... apply IH.
    + set (proj2 Forall2_indexes IHn) as IH. simpl in IH.
      apply orb_monotone.
      * specialize (IH l). unfold dgstep in IH... apply IH.
      * specialize (IH r). unfold dgstep in IH... apply IH.
Qed.

Fixpoint popcount {n} (g: DeltaGraph n) : nat :=
  match g with
  | nil _ => 0
  | cons _ true _ t => S (popcount t)
  | cons _ false _ t => popcount t
  end.

Theorem popcount_max {n} (g: DeltaGraph n) :
  (popcount g <= n)%nat.
Admitted.

Theorem popcount_top {n} (g: DeltaGraph n) :
  (popcount g = n) -> g = DGTop n.
Admitted.

Definition dg_eq_dec {n} (g1 g2: DeltaGraph n) :
  {g1 = g2} + {g1 <> g2} :=
  eq_dec _ Bool.eqb eqb_true_iff _ g1 g2.

Lemma eq_index {A} {n} (v1 v2: Vector.t A n) :
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

Lemma DGPopcount : forall n (g1 g2: DeltaGraph n) pc,
  popcount g1 >= pc ->
  DGLess _ g1 g2 ->
  g1 <> g2 ->
  popcount g2 >= S pc.
Proof.
  intros n. induction n; intros.
  - rewrite (is_nil g1) in *. rewrite (is_nil g2) in *.
    exfalso. apply H1. reflexivity.
  - destruct (is_cons g1) as [h1 [t1 E1]]. rewrite E1 in *.
    destruct (is_cons g2) as [h2 [t2 E2]]. rewrite E2 in *.
    destruct (forall_uncons H0).
    destruct h1; destruct h2.
    + apply le_n_S. destruct pc.
      * apply le_0_n.
      * apply (IHn t1 t2).
        -- apply le_S_n. apply H.
        -- unfold DGLess in *. assumption.
        -- intros Contra. apply H1. f_equal. apply Contra.
    + unfold DGLess in *.
      inversion H2.
    + simpl in H. destruct (dg_eq_dec t1 t2).
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

Lemma DGStepPopcount (ctx: Ctx) : forall n pc,
  popcount (dgiter ctx n) >= pc ->
  dgiter ctx n <> dgiter ctx (S n) ->
  popcount (dgiter ctx (S n)) >= S pc.
Proof.
  intros. apply (DGPopcount _ (dgiter ctx n) (dgiter ctx (S n))).
  - assumption.
  - apply dgiter_monotone.
  - assumption.
Qed.

Theorem DGIterPopcount (ctx : Ctx) : forall n,
    popcount (dgiter ctx n) >= n
    \/ dgiter ctx n = dgiter ctx (S n).
Proof.
  intros n. induction n.
  - simpl. left. apply le_0_n.
  - inversion IHn; subst.
    + destruct (dg_eq_dec (dgiter ctx n) (dgiter ctx (S n))).
      * right. unfold dgiter. f_equal. fold dgiter. apply e.
      * left. apply DGStepPopcount; assumption.
    + right. unfold dgiter. f_equal. fold dgiter. apply H.
Qed.

Theorem DGStepTop (ctx: Ctx) : forall g,
    dgstep ctx g = DGTop (len ctx) ->
    dgstep ctx (DGTop (len ctx)) = DGTop (len ctx).
Proof.
  intros. apply eq_index. intros i.
  set (proj2 (eq_index _ _) H i) as Hprev.
  unfold DGTop in *. repeat rewrite const_idx in *.
  unfold dgstep in *. repeat rewrite map_idx in *.
  repeat rewrite indexes_idx in *.
  destruct (langs ctx)[@i]; try discriminate; try reflexivity.
  - repeat rewrite const_idx. reflexivity.
  - repeat rewrite const_idx. reflexivity.
Qed.

Theorem DGIterTop (ctx: Ctx) : forall n,
    dgiter ctx n = DGTop (len ctx) ->
    dgstep ctx (DGTop (len ctx)) = DGTop (len ctx).
Proof.
  destruct ctx. generalize dependent langs0.
  destruct len0; intros; simpl in *.
  - reflexivity.
  - destruct n; simpl in *.
    + inversion H.
    + apply (DGStepTop _ _ H).
Qed.

Theorem DGIterFixpoint' (ctx : Ctx) :
    dgiter ctx ctx.(len) = dgiter ctx (S ctx.(len)).
Proof.
  destruct (DGIterPopcount ctx ctx.(len)).
  - assert (popcount (dgiter ctx ctx.(len)) = ctx.(len)). {
      apply Nat.le_antisymm.
      - apply popcount_max.
      - apply H. }
    set (popcount_top _ H0) as Htop.
    change (dgiter ctx (S (len ctx))) with
      (dgstep ctx (dgiter ctx (len ctx))).
    rewrite Htop. symmetry. apply (DGIterTop _ _ Htop).
  - assumption.
Qed.

Theorem DGIterFixpoint (ctx : Ctx) : forall n,
    (ctx.(len) < n)%nat ->
    dgiter ctx ctx.(len) = dgiter ctx n.
Proof.
  intros. induction H.
  - apply DGIterFixpoint'.
  - change (dgiter ctx (S m)) with (dgstep ctx (dgiter ctx m)).
    rewrite <- IHle. rewrite DGIterFixpoint' at 1.
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
  - assert ((dgiter ctx ctx.(len))[@i] = (dgiter ctx n)[@i]).
    { rewrite (DGIterFixpoint _ _ H0). reflexivity. }
    destruct (DGIterCorrect ctx n i); try contradiction.
    destruct (DGIterCorrect ctx ctx.(len) i); try discriminate.
    assumption.
Qed.

Theorem DeltaNDenotation (ctx: Ctx) : forall i,
    DeltaN ctx ctx.(len) ctx.(langs)[@i]
    <-> Delta (Denotation ctx i).
Proof.
  split; [apply DeltaNDenotation1|apply DeltaNDenotation2].
Qed.

Definition deltas (ctx: Ctx) : CDG ctx :=
  dgiter ctx ctx.(len).

Theorem DeltasCorrect (ctx: Ctx) : forall i,
    reflect (Delta (Denotation ctx i)) (deltas ctx)[@i].
Proof.
  intros i.
  set (DGIterCorrect ctx ctx.(len) i) as Hv.
  unfold DGReflect in Hv. unfold deltas.
  destruct Hv.
  - apply ReflectT.
    apply DeltaNDenotation. assumption.
  - apply ReflectF. intros Contra. apply n.
    apply DeltaNDenotation. assumption.
Qed.

Section EXAMPLES.

Fixpoint F {n} x : Fin.t (S x + n) :=
  match x with
  | 0 => Fin.F1
  | (S x') => Fin.FS (F x')
  end.

Declare Scope fin_scope.
Notation "$ x" := (F x) (at level 0, format "$ x") : fin_scope.
Open Scope fin_scope.

Example LeftRecDenotation : Lang :=
  cofix L := alt (cat L (char "x")) eps.

Example LeftRecCtx : Ctx :=
  {| langs := [epsF; charF "x"; catF $3 $1; altF $2 $0] |}.

Example LeftRec : Idx LeftRecCtx := $3.

Example LeftRecCorrect : Bisim (Denotation _ LeftRec) LeftRecDenotation.
Proof.
  cofix CH.
  rewrite (LangDecompose LeftRecDenotation).
  repeat (rewrite (LangDecompose (Denotation _ _));
          simpl; constructor).
  apply CH.
Qed.

Example LeftRecDelta : Delta LeftRecDenotation.
Proof.
  rewrite (LangDecompose LeftRecDenotation); simpl.
  apply DL_alt2. apply DL_eps.
Qed.

Compute dgiter LeftRecCtx 0.
Compute dgiter LeftRecCtx 1.
Compute dgiter LeftRecCtx 2.
Compute dgiter LeftRecCtx 3.

Example InfiniteX : Lang :=
  cofix L := cat (char "x") L.

Example InfiniteXDelta : ~ Delta InfiniteX.
Proof.
  rewrite (LangDecompose InfiniteX); simpl.
  intros Contra. inversion Contra.
  inversion H1.
Qed.

Example InfiniteNothing : Lang :=
  cofix L := alt L L.

Example InfiniteNothingDelta : ~ Delta InfiniteNothing.
Proof.
  rewrite (LangDecompose InfiniteNothing); simpl.
  intros Contra.
  remember (alt InfiniteNothing InfiniteNothing) as x.
  induction Contra; inversion Heqx; subst.
  - apply IHContra.
    rewrite (LangDecompose InfiniteNothing) at 1; simpl.
    reflexivity.
  - apply IHContra.
    rewrite (LangDecompose InfiniteNothing) at 1; simpl.
    reflexivity.
Qed.

Example InfiniteEps : Lang :=
  cofix L := cat eps L.

Example InfiniteEpsDelta : ~ Delta InfiniteEps.
Proof.
  rewrite (LangDecompose InfiniteEps); simpl.
  intros Contra.
  remember (cat eps InfiniteEps) as x.
  induction Contra; inversion Heqx; subst.
  apply IHContra2.
  rewrite (LangDecompose InfiniteEps) at 1; simpl.
  reflexivity.
Qed.

CoInductive CoDelta : Lang -> Prop :=
| CD_eps : CoDelta eps
| CD_cat l r : CoDelta l -> CoDelta r -> CoDelta (cat l r)
| CD_alt1 l r : CoDelta l -> CoDelta (alt l r)
| CD_alt2 l r : CoDelta r -> CoDelta (alt l r)
| CD_rep l : CoDelta (rep l).

Example InfiniteNothingCoDelta : CoDelta InfiniteNothing.
Proof.
  cofix CH.
  rewrite (LangDecompose InfiniteNothing); simpl.
  apply CD_alt1. apply CH.
Qed.

Example InfiniteEpsCoDelta : CoDelta InfiniteEps.
Proof.
  cofix CH.
  rewrite (LangDecompose InfiniteEps); simpl.
  apply CD_cat.
  - apply CD_eps.
  - apply CH.
Qed.

Theorem DeltaCoDelta : forall l, Delta l -> CoDelta l.
Proof.
  intros l H. induction H.
  - apply CD_eps.
  - apply CD_cat; assumption.
  - apply CD_alt1; assumption.
  - apply CD_alt2; assumption.
  - apply CD_rep.
Qed.

Theorem CoDeltaDelta : ~ forall l, CoDelta l -> Delta l.
Proof.
  intros Contra.
  apply InfiniteEpsDelta.
  apply Contra.
  apply InfiniteEpsCoDelta.
Qed.

End EXAMPLES.
