From mathcomp Require Import eqtype ssrbool.
From extructures Require Import fmap ord.
From AlphaPearl Require Import FiniteStructures.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

Class IsInjective (A : Type) :=
  { is_injective : A -> Prop }.

#[global] Hint Mode IsInjective ! : typeclass_instances.

#[global] Instance function_IsInjective (A B : Type) : IsInjective (A -> B) :=
  { is_injective f := ssrfun.injective f }.

#[global] Instance fmap_IsInjective (A : ordType) (B : eqType) : IsInjective {fmap A → B} :=
  { is_injective m := injectivem m }.
