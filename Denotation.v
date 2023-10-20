From Coq Require Import Strings.Ascii.
From Coq Require Import Vector.

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
