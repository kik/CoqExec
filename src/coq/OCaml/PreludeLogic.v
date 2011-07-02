Require Import Prelude.

Module Axioms.
  Module Int.
    Import Prelude.Axioms.Int.

    Axiom addC : forall x y, plus x y = plus y x.
    Axiom addA : forall x y z, plus (plus x y) z = plus x (plus y z).
    Axiom add0 : forall x, plus zero x = x.
    Axiom sub0 : forall x, minus zero x = opp x.
    Axiom addN : forall x, plus (opp x) x = zero.
  End Int.
End Axioms.
