Require Import Bool.

Section Operators.
  Context (S : Type).

  Class HasOperatorPlus := {
    operatorPlus : S -> S -> S
  }.

  Class HasOperatorMinus := {
    operatorMinus : S -> S -> S
  }.

  Class HasOperatorOpp := {
    operatorOpp : S -> S
  }.

  Class HasZero := {
    zeroS : S
  }.

  Class HasOperatorMul := {
    operatorMul : S -> S -> S
  }.

  Class HasOne := {
    oneS : S
  }.

  Class HasOperatorLt := {
    operatorLt : S -> S -> bool
  }.

  Class HasOperatorLe := {
    operatorLe : S -> S -> bool
  }.

  Class HasOperatorEq := {
    operatorEq : S -> S -> bool
  }.
End Operators.

Notation "x + y" := (operatorPlus _ x y) : ops_scope.
Notation "x - y" := (operatorMinus _ x y) : ops_scope.
Notation "- x"   := (operatorOpp _ x) : ops_scope.
Notation "0"     := (zeroS _) : ops_scope.
Notation "1"     := (oneS _) : ops_scope.
Notation "x * y" := (operatorMul _ x y) : ops_scope.
Notation "x < y" := (operatorLt _ x y) : ops_scope.
Notation "x > y" := (operatorLt _ y x) : ops_scope.
Notation "x <= y" := (operatorLe _ x y) : ops_scope.
Notation "x >= y" := (operatorLe _ y x) : ops_scope.
Notation "x <= y <= z" := (x <= y && y <= z) : ops_scope.
Notation "x < y <= z"  := (x < y  && y <= z) : ops_scope.
Notation "x <= y < z"  := (x <= y && y < z) : ops_scope.
Notation "x < y < z"   := (x < y  && y < z) : ops_scope.

Delimit Scope ops_scope with O.
