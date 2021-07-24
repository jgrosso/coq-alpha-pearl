From mathcomp Require Import eqtype seq ssrbool.
From extructures Require Import fset fmap ord.
From AlphaPearl Require Import FiniteStructures.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

Class HasMembers (A F P : Type) :=
  { is_member_of : A -> F -> P }.

#[global] Hint Mode HasMembers - ! - : typeclass_instances.

Infix "∈" := is_member_of (at level 70).

#[global] Instance seq_HasMembers (A : eqType) : HasMembers A (seq A) bool :=
  { is_member_of (x : A) s := x \in s }.

#[global] Instance fmap_HasMembers (A : ordType) (B : eqType) : HasMembers (A * B) {fmap A → B} bool :=
  { is_member_of (x_y : A * B) (R : {fmap A → B}) := getm R (fst x_y) == Some (snd x_y) }.

#[global] Instance fset_HasMembers (A : ordType) : HasMembers A {fset A} bool :=
  { is_member_of (x : A) s := x \in s }.

#[global] Instance Prop_predicate_HasMembers (A : Type) : HasMembers A (A -> Prop) Prop :=
  { is_member_of (x : A) P := P x }.

#[global] Instance bool_predicate_HasMembers (A : Type) : HasMembers A (A -> bool) bool :=
  { is_member_of (x : A) (f : A -> bool) := f x }.

#[global] Instance bool_predicate_as_Prop_HasMembers (A : Type) (T : Type) `{HasMembers A T bool} : HasMembers A T Prop :=
  { is_member_of (x : A) (f : T) := x ∈ f = true }.

Notation "P__sub '⊆' P__super" := (forall a, (a ∈ P__sub : Prop) -> (a ∈ P__super : Prop)) (at level 40).
