Require Import Bool Operator.

Section NumClass.
  Context (S : Type).

  Class Num := {
    numPlus :> HasOperatorPlus S;
    numMinus :> HasOperatorPlus S;
    numOpp :> HasOperatorOpp S;
    numZero :> HasZero S;
    numMul :> HasOperatorMul S;
    numOne :> HasOne S;
    numLt :> HasOperatorLt S;
    numLe :> HasOperatorLe S;
    numEq :> HasOperatorEq S
  }.

x