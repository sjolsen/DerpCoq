From Coq Require Import Bool.
From Coq Require Import Bool.BoolOrder.
From Coq Require Import Vector.
From Coq Require Import Sets.Cpo.
From Coq Require Import Strings.Ascii.
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

Inductive LangF (X: Set) :=
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

Record LangR :=
  { ctx : Ctx
  ; idx : Fin.t ctx.(len)
  }.

Definition rebind (l: LangR) (i: Fin.t l.(ctx).(len)) : LangR :=
  {| ctx := l.(ctx); idx := i |}.

Definition get_lang (l1: LangR) : LangF LangR.
Proof.
  destruct (l1.(ctx).(langs)[@l1.(idx)]) eqn:E.
  - exact emptyF.
  - exact epsF.
  - exact (charF c).
  - exact (catF (rebind l1 l) (rebind l1 r)).
  - exact (altF (rebind l1 l) (rebind l1 r)).
  - exact (repF (rebind l1 l)).
Defined.

CoFixpoint Denotation (l1: LangR) : Lang :=
  match (get_lang l1) with
  | emptyF => empty
  | epsF => eps
  | charF c => char c
  | catF l r => cat (Denotation l) (Denotation r)
  | altF l r => alt (Denotation l) (Denotation r)
  | repF l => rep (Denotation l)
  end.

Definition DeltaGraph n := Vector.t bool n.

Definition DGLess n (g1 g2: DeltaGraph n) :=
  Forall2 (fun x1 x2 => x1 <= x2) g1 g2.

Definition DGBottom n : DeltaGraph n :=
  const false _.

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

Definition DGDec (ctx: Ctx) (g: CDG ctx) n : Set :=
  reflect (Delta (Denotation {| ctx := ctx; idx := n |})) g[@n].

Definition DGStepPre (ctx: Ctx) (prev: CDG ctx) n : Set :=
  match ctx.(langs)[@n] with
  | catF l r => DGDec ctx prev l * DGDec ctx prev r
  | altF l r => DGDec ctx prev l * DGDec ctx prev r
  | _ => True
  end.

(* this is the wrong thing to prove... what's needed is
   a proof that dgstep computes a decision for the functor
   DeltaF underlying Delta, and that

     Delta (Denotation l) <-> Fix l.ctx.len DeltaF

   where Fix 0 F = Void; Fix (S n) F = F (Fix n F)
 *)
Theorem DGStepCorrect (ctx: Ctx) (prev: CDG ctx) : forall n,
  DGStepPre ctx prev n ->
  DGDec ctx (dgstep ctx prev) n.
Proof.
  intros n Hpre.
  unfold DGStepPre in Hpre.
  unfold dgstep, DGDec.
  rewrite map_idx. rewrite indexes_idx.
  rewrite (LangDecompose (Denotation _)).
  unfold Denotation, LangDecomp.
  fold Denotation.
  unfold get_lang.
  replace ((langs (derp.ctx {| ctx := ctx; idx := n |}))
             [@idx {| ctx := ctx; idx := n |}])
    with ctx.(langs)[@n].
  destruct ctx.(langs)[@n] eqn:E.
  - apply ReflectF. intros Contra. inversion Contra.
  - apply ReflectT. apply DL_eps.
  - apply ReflectF. intros Contra. inversion Contra.
  - unfold DGDec in Hpre.
    destruct Hpre as [Hl Hr]. destruct Hl.
    + destruct Hr.
      * apply ReflectT. apply DL_cat; assumption.
      * apply ReflectF. intros Contra.
        inversion Contra; contradiction.
    + apply ReflectF. intros Contra.
      inversion Contra; contradiction.
  - unfold DGDec in Hpre.
    destruct Hpre as [Hl Hr]. destruct Hl.
    + apply ReflectT. apply DL_alt1; assumption.
    + destruct Hr.
      * apply ReflectT. apply DL_alt2; assumption.
      * apply ReflectF. intros Contra.
        inversion Contra; contradiction.
  - apply ReflectT. apply DL_rep.
  - reflexivity.
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

Example LeftRec : LangR :=
  {| ctx := {| langs := [epsF; charF "x"; catF $3 $1; altF $2 $0] |}
  ;  idx := $3
  |}.

Example LeftRecCorrect : Bisim (Denotation LeftRec) LeftRecDenotation.
Proof.
  cofix CH.
  rewrite (LangDecompose LeftRecDenotation).
  repeat (rewrite (LangDecompose (Denotation _));
          simpl; constructor).
  apply CH.
Qed.

Example LeftRecDelta : Delta LeftRecDenotation.
Proof.
  rewrite (LangDecompose LeftRecDenotation); simpl.
  apply DL_alt2. apply DL_eps.
Qed.

Compute dgiter LeftRec.(ctx) 0.
Compute dgiter LeftRec.(ctx) 1.
Compute dgiter LeftRec.(ctx) 2.
Compute dgiter LeftRec.(ctx) 3.

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
