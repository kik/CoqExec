Require Import ssreflect ssrfun ssrbool.
Require Import Operator.

Local Open Scope ops_scope.

Section POperators.
  Context (S : Type).
  Context {plus : HasOperatorPlus S}.
  Context {minus : HasOperatorMinus S}.
  Context {opp : HasOperatorOpp S}.
  Context {zero : HasZero S}.
  Context {mul : HasOperatorMul S}.
  Context {one : HasOne S}.
  Context {lt : HasOperatorLt S}.
  Context {le : HasOperatorLe S}.
  Context {eq : HasOperatorEq S}.

  Notation "(+)" := (operatorPlus S).

  Class HasAddmC := {
    addmC : commutative (+)
  }.

  Class HasAddmA := {
    addmA : associative (+)
  }.

  Class HasAdd0m := {
    add0m : left_id 0 (+)
  }.

  Class HasSub0m := {
    sub0m : forall x : S, 0 - x = -x
  }.

  Class HasAddNm := {
    addNm : left_inverse 0 (operatorOpp S) (+)
  }.

  Context {AddmC : HasAddmC}.
  Context {AddmA : HasAddmA}.
  Context {Add0m : HasAdd0m}.
  Context {Sub0m : HasSub0m}.
  Context {AddNm : HasAddNm}.
  
  Lemma addm0 : right_id 0 (+).
  Proof. by move=> x; rewrite addmC; exact: add0m. Qed.

  Lemma addmN : right_inverse 0 (operatorOpp S) (+).
  Proof. move=> x; rewrite addmC; exact: addNm. Qed.

  (* TODO *)

End POperators.

Section Abelian.
  Context (S : Type).

  Class HasAbelianAdd := {
    AbelianAdd :> HasOperatorPlus S;
    AbelianMinus :> HasOperatorMinus S;
    AbelianOpp :> HasOperatorOpp S;
    AbelianZero :> HasZero S;
    AbelianAddA :> HasAddmA S;
    AbelianAddC :> HasAddmC S;
    AbelianAdd0m :> HasAdd0m S;
    AbelianSub0m :> HasSub0m S;
    AbelianAddNm :> HasAddNm S
  }.

  (* TODO *)
End Abelian.
