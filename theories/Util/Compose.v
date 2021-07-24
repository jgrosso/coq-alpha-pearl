From mathcomp Require Import eqtype ssrbool.
From extructures Require Import fmap ord.
From AlphaPearl Require Import FiniteStructures.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

Class CanCompose (A B C : Type) :=
  { composition : A -> B -> C }.

#[global] Hint Mode CanCompose ! ! - : typeclass_instances.

Infix "∘" := composition (at level 40).

#[global] Instance function_and_fmap_CanCompose_as_fmap (A : ordType) (B C : Type) :
  CanCompose (B -> C) {fmap A → B} {fmap A → C} :=
  { composition (f : B -> C) (g : {fmap A → B}) := mapm f g }.

#[global] Instance function_and_function_CanCompose_as_function (A : ordType) (B C : Type) :
  CanCompose (B -> C) (A -> B) (A -> C) :=
  { composition (f : B -> C) (g : A -> B) a := f (g a) }.
