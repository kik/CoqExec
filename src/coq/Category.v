Require Import Program FunctionalExtensionality Morphisms Classes.Equivalence Setoid.

Open Scope equiv_scope.
Open Scope program_scope.
Local Open Scope signature_scope.

Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import SetoidClass.

Global Generalizable All Variables.

Record Map A B {As : Setoid A} {Bs : Setoid B}  := mkMap {
  Map_fn :> A -> B;
  Map_Mor : Proper (equiv ==> equiv) Map_fn
}.

Implicit Arguments Map_fn [[A] [B]].
Implicit Arguments mkMap [[A] [B]].

Infix "-->" := Map (at level 55, right associativity).

Instance Map_respect `{As : Setoid A} `{Bs : Setoid B} (m : Map A B) :
  Proper (equiv ==> equiv) m.
Proof.
  destruct m as [m Hm]; exact Hm.
Defined.

Definition respectfulS α β `{A : Setoid α} `{B : Setoid β} : relation (Map α β) :=
  pointwise_relation α (@SetoidClass.equiv _ B).

Infix "===>" := respectfulS (at level 90).

Ltac pauto := simpl in * ; eauto with relations.

Instance Map_respectful_equiv `{A : Setoid α} `{B : Setoid  β} : @Equivalence (Map α β) (α ===> β)%signature.
Proof with simpl in *; pauto.
  constructor; red; simpl in *.
  intros [f morf] x...
  intros [f morf] [g morg] Hxy x...
  symmetry; apply Hxy.
  intros [f morf] [g morg] [h morh]...
  intros Hfg Hgh x.
  transitivity (g x)...
Qed.

Instance subrelation_respectfulS `{a : Setoid A, b : Setoid B} : subrelation (A ===> B) (equiv ==> equiv).
Proof.
  intros f g Hfg x y Hxy.  rewrite Hxy. apply Hfg.
Qed.

Instance subrelation_respectfulS' `{a : Setoid A, b : Setoid B} : @subrelation (A --> B) (equiv ==> equiv) (A ===> B).
Proof.
  intros f g Hfg x. apply Hfg. reflexivity.
Qed.
  
Instance Map_fn_morphism `{a : Setoid A, b : Setoid B} :
  Proper ((A ===> B) ==> equiv ==> equiv) (@Map_fn A B a b).
Proof. intros [m Hm] [m' Hm'] Hmm'. simpl. red. do 2 red in Hmm'. simpl in *. 
  intros. rewrite H. apply Hmm'. Qed.

Definition proper_map_equiv α β {A : Setoid α} {B : Setoid β} (f : α -> β)
  : relation (Proper (equiv ==> equiv) f)
  := fun p q => True.

Instance mkMap_morph α β {A : Setoid α} {B : Setoid β}
  : Proper (forall_relation (fun f : α -> β => proper_map_equiv α β f ==> (α ===> β))) (mkMap A B).
Proof.
  intro f. intros px py _. intro. simpl. reflexivity.
Qed.

Obligation Tactic := try typeclasses eauto || program_simplify.

Program Instance MapS α β `{A : Setoid α, B : Setoid β} : Setoid (α --> β) :=
  @Build_Setoid _ (α ===> β) _.

Infix "--->" := MapS (at level 55, right associativity).

Program Definition MapS_fn α β `{A : Setoid α, B : Setoid β} (f : α --> β) : α -> β := f.

Notation " ^ x " := (MapS_fn x) (at level 0).

Program Definition idS α {A : Setoid α} : α --> α := mkMap _ _ id _.

Program Definition composeS `{A : Setoid α, B : Setoid β, C : Setoid δ} (f : β --> δ) (g : α --> β) : α --> δ := 
  mkMap _ _ (f ∘ g) _.

Definition setoid_pointwise_relation `{a : Setoid A, b : Setoid B} : relation (A --> B) :=
  pointwise_relation A equiv.

Instance setoid_pointwise `{a : Setoid A, b : Setoid B} :
  @PER (A --> B) (@setoid_pointwise_relation A _ B _)%signature | 2.

Infix "=∙=" := setoid_pointwise_relation (at level 60).

Infix "∙" := composeS (at level 40, left associativity).

Class Functor (F : Type -> Type) := {
  fsetoid :> forall X (x : Setoid X), Setoid (F X) ;
  fmap : forall `{a : Setoid A, b : Setoid B}, (A --> B) --> F A --> F B ;
  fmap_id : forall `{a : Setoid A}, fmap (@idS A _) =∙= idS _;
  fmap_compose : forall `{a : Setoid A, b : Setoid B, c: Setoid C}
    (f : B --> C) (g : A --> B),
    fmap (f ∙ g) =∙= fmap f ∙ fmap g
}.

Class Pointed `{F : Functor η} := {
  point : forall `{a : Setoid A}, A --> η A ;
  fmap_point : forall `{a : Setoid A} `{b : Setoid B} (f : A --> B),
    fmap f ∙ point =∙= point ∙ f
}.

Class Monad `{pointed : Pointed η} := {
  join : forall `{a : Setoid α}, η (η α) --> η α ;

  (* Natural transformations. *)

  fmap_join : forall `{a : Setoid α, b: Setoid β} (f : α --> β),
    fmap f ∙ join =∙= join ∙ fmap (fmap f) ;

  (* Monad laws *)

  join_fmap_point : forall `{a : Setoid α}, join ∙ fmap point =∙= (@idS (η α) _) ;

  join_point : forall `{a : Setoid α}, join ∙ (point (A:=η α)) =∙= idS _ ;
  
  join_fmap : forall `{a : Setoid α}, join ∙ (@join (η α) _) =∙= join ∙ fmap (@join α _) }.

Inductive option_eq `{a : Setoid A} : relation (option A) :=
| option_eq_Some :> Proper (equiv ==> option_eq) Some
| option_eq_None :> Proper option_eq None.
Print Instances Proper.
Hint Resolve @option_eq_Some @option_eq_None : typeclass_instances.

Instance option_eq_refl `{a : Setoid A} : Reflexive (@option_eq A _).
  red; intros; destruct x; constructor; reflexivity.
Qed.
Instance option_eq_symmetric `{a : Setoid A} : Symmetric (@option_eq A _).
  red; intros; destruct H; constructor; auto with relations.
Qed.

Program Instance option_eq_trans `{a : Setoid A} : Transitive (@option_eq A _).

  Next Obligation.
    induction H; depelim H0. constructor. now transitivity y.
    constructor.
  Qed.

Program Instance option_setoid A {a : Setoid A} : Setoid (option A) :=
  {| equiv := option_eq |}.

  Next Obligation. constructor; typeclasses eauto. Qed.

(*
Program Definition NoneS {A:Setoid} : option_setoid A :=
  None.

Program Definition SomeS {A:Setoid} : A ---> option_setoid A :=
  mkMap (fun a => Some a).

  Next Obligation. simpl_morph. Qed.
*)

(*
Class CoPointed `{F : Functor η} := {
  extract : Π {α}, η α --> α ; 

  extract_fmap : Π {α β} (f : α --> β), extract ∙ fmap f =∙= f ∙ extract }.
*)


Ltac feq f g :=
  match f with
    | ?f ?x =>
      match g with
        | f ?y => try setoid_replace x with y ; try reflexivity
        | ?g x => feq f g
        | ?g ?y => feq f g ; try setoid_replace x with y ; try reflexivity
        | _ => idtac
      end
    | _ => idtac
  end.

Ltac fequal :=
  match goal with
    [ |- ?R ?f ?g ] => feq f g ; try reflexivity
  end.


Ltac simpl_respect := 
  let rec arrow :=
    let tac :=
      let x := fresh "x" in
      let y := fresh "y" in 
      let H := fresh "Hxy" in
        intros x y H ; arrow ; try (rewrite H)
     in
      match goal with
        | [ |- (?X ==> ?Y)%signature _ _ ] => tac
        | [ |- (?X ===> ?Y)%signature _ _ ] => 
          let x := fresh "x" in intros x ; arrow
        | [ |- _ ] => simpl ; repeat clear_subset_proofs
      end
    in 
    match goal with
      | [ |- Proper _ _ ] => red ; arrow
      | _ => arrow
    end.

Ltac simpl_morph := 
  let one_simple := simpl_respect ; fequal in
  let rec aux :=
    match goal with
      | [ |- (_ ==> _)%signature _ _ ] => one_simple ; aux
      | [ |- (_ ===> _)%signature _ _ ] => one_simple ; aux
      | [ |- Proper _ _ ] => one_simple ; aux
      | _ => idtac
    end
  in aux.


Program Definition mkMap2 `{a : Setoid A, b : Setoid B, c : Setoid C} (Map_fn : A -> B -> C) 
  (P : Proper (equiv ==> equiv ==> equiv) Map_fn) : A --> B --> C :=
  mkMap _ _ (fun a => mkMap _ _ (fun b => Map_fn a b) _) _.

  Next Obligation. 
    intros x x' Hxx'. rewrite Hxx'. reflexivity.
  Qed.

  Next Obligation. 
    intros x x' Hxx' y. simpl. rewrite Hxx'. reflexivity.
  Qed.

Program Instance option_functor : Functor (fun A => option A) :=
  { fmap := fun A a B b => mkMap2 (fun f x =>
    match x return _ with
      | Some x' => Some (f x') 
      | None => None
    end) _
   }.

  Next Obligation.
  Proof. info simpl_morph. destruct x0 ; destruct y0 ; intros; pauto.
    inversion Hxy0.
    rewrite H1. constructor. apply Hxy.
    inversion Hxy0. inversion Hxy0.
  Qed.

  Next Obligation.
  Proof. intro b. simpl. destruct b. now simpl. now simpl. Qed.


  Next Obligation.
  Proof. intro b'. simpl. destruct b'. now simpl. now simpl. Qed.

Definition option_join {A} (x : option (option A)) :=
  match x return _ with Some a => a | None => None end.

Definition option_bind {A B} (x : option A) (f : A -> option B) := 
  match x return _ with Some a => f a | None => None end.
About Monad.


Program Definition NoneS `{a : Setoid A} : option A :=
  None.

Program Definition SomeS `{a : Setoid A} : A --> option A :=
  mkMap _ _ (fun a => Some a) _.

  Next Obligation. simpl_morph. Qed.


Program Instance option_pointed : Pointed := {
  point A a := SomeS
 }.

  Next Obligation. intro a'. simpl. reflexivity. Qed.

Program Instance option_monad : Monad := {
  join A a := mkMap _ _ option_join _ }.


  Next Obligation. intros x y Hxy. unfold option_join.
    inversion Hxy. rewrite H. reflexivity. reflexivity. Qed.

  Next Obligation. intros [[a'|]|] ; now simpl. Qed.

  Solve Obligations using program_simpl ; intros [a'|] ; try now simpl. 

