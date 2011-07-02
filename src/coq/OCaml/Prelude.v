Require Import CoqExec.Operator CoqExec.Primitive.

Extraction Language Ocaml.
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Module Axioms.
  Module Int.
    Axiom t : Set.
    Axiom plus : t -> t -> t.
    Axiom minus : t -> t -> t.
    Axiom opp : t -> t.
    Axiom zero : t.
    Axiom mul : t -> t -> t.
    Axiom one : t.
    Axiom lt : t -> t -> bool.
    Axiom le : t -> t -> bool.
    Axiom eq : t -> t -> bool.

    Extract Constant t => "int".
    Extract Constant plus => "(+)".
    Extract Constant minus => "(-)".
    Extract Constant opp => "(~-)".
    Extract Constant zero => "0".
    Extract Constant mul => "( * )".
    Extract Constant one => "1".
    Extract Constant lt => "(<)".
    Extract Constant le => "(<=)".
    Extract Constant eq => "(=)".
  End Int.
End Axioms.

Module Primitives : PrimitiveTypes.
  Definition Integer := Axioms.Int.t.
  Instance IntegerIsPrimitiveInteger : PrimitiveInteger Integer.
  Proof.
    constructor.
    exact (Build_HasOperatorPlus _ Axioms.Int.plus).
    exact (Build_HasOperatorMinus _ Axioms.Int.minus).
    exact (Build_HasOperatorOpp _ Axioms.Int.opp).
    exact (Build_HasZero _ Axioms.Int.zero).
    exact (Build_HasOperatorMul _ Axioms.Int.mul).
    exact (Build_HasOne _ Axioms.Int.one).
    exact (Build_HasOperatorLt _ Axioms.Int.lt).
    exact (Build_HasOperatorLe _ Axioms.Int.le).
    exact (Build_HasOperatorEq _ Axioms.Int.eq).
  Defined.
End Primitives.

Export Primitives.
Existing Instance IntegerIsPrimitiveInteger.

(* TODO: Notation *)
Require Import BinPos.

Fixpoint c (x : positive) : Integer :=
  match x with
    | xH => 1
    | xI y => (1 + 1) * c y + 1
    | xO y => (1 + 1) * c y
  end%O.

(* TODO: remove *)
Axiom print_int : Integer -> unit.
Extract Constant print_int => "print_int".

Definition run_main (f : unit -> unit) := f tt.
