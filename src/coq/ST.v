Require Import Monad.

Class fmonad (M : (Type -> Type) -> Type) := {
  fmreturn : forall {A : Type -> Type} {B}, (B -> A B) -> M A;
  fmbind : forall {A B : Type -> Type} {C}, M A -> ((C -> A C) -> M B) -> M B
}.

Class ST (T : (Type -> Type) -> Type) := {
  STreturn : forall {A}, T (fun _ => A);
  STbind : forall {A B : Type -> Type} {S}, T A -> (A S -> T B) -> T B;
  runST : forall {A}, T (fun _ => A) -> A
}.

Instance STmonad : forall {T} {_ : ST T} {S}, monad (fun X => T ()).

new : A -> st (fun s => ptr s A)
read : A -> (fun s => ptr 

Instance monadOfST : forall {T} {_ : ST T}, monad T.

Section Test.
  Context {ST} {stST : st ST} {S : Type}.
  Context {a b c : ST S nat}.

  Check (a;; b).
x



