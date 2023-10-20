From Coq Require Import Strings.Ascii.

From Derp Require Import Derp.
From Derp Require Import Vector.

Import Vector.VectorNotations.

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

Compute iter LeftRecCtx 0.
Compute iter LeftRecCtx 1.
Compute iter LeftRecCtx 2.
Compute iter LeftRecCtx 3.

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
