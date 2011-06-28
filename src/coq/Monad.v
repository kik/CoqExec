
Set Implicit Arguments.

Class monad (M : Type -> Type) (A : Type) := {
  mreturn : A -> M A;
  mbind : forall {B}, M A -> (A -> M B) -> M B
}.


Notation "x >>= f" := (mbind x f) (at level 42, left associativity) : monad_scope.
Notation "x >> y" := (mbind x (fun _ => y)) (at level 42, left associativity) : monad_scope.

Open Scope monad_scope.
Delimit Scope monad_scope with m.

Notation "'ret' x" := (mreturn x) (at level 75) : monad_scope.
Notation "x <- y ; z" := (mbind y (fun x => z)) 
  (right associativity, at level 84, y at next level) : monad_scope.
Notation "x ;; y" := (mbind x (fun _ => y))
  (right associativity, at level 84) : monad_scope.
