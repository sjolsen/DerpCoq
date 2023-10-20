From Coq Require Export Bool.
From Coq Require Export Bool.BoolOrder.

Import Bool.BoolNotations.

Theorem le_antisym : forall a b,
    a <= b -> b <= a -> a = b.
  intros a b H1 H2.
  destruct a; destruct b; try reflexivity.
  - inversion H1.
  - inversion H2.
Qed.

Theorem andb_monotone : forall a b c d,
    a <= c -> b <= d -> a && b <= c && d.
Proof.
  intros a b c d H1 H2.
  destruct a; destruct b; destruct c; destruct d;
    simpl in *; auto.
Qed.

Theorem orb_monotone : forall a b c d,
    a <= c -> b <= d -> a || b <= c || d.
Proof.
  intros a b c d H1 H2.
  destruct a; destruct b; destruct c; destruct d;
    simpl in *; auto.
Qed.
