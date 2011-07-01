Require Import Operator.

Class PrimitiveInteger (S : Type) := {
  IntegerHasPlus :> HasOperatorPlus S;
  IntegerHasMinus :> HasOperatorMinus S;
  IntegerHasOpp :> HasOperatorOpp S;
  IntegerHasZero :> HasZero S;
  IntegerHasMul :> HasOperatorMul S;
  IntegerHasOne :> HasOne S;
  IntegerHasLt :> HasOperatorLt S;
  IntegerHasLe :> HasOperatorLe S;
  IntegerHasEq :> HasOperatorEq S
}.

Module Type PrimitiveTypes.
  Parameter Integer : Type.
  Parameter IntegerIsPrimitiveInteger : PrimitiveInteger Integer.

End PrimitiveTypes.
