From Coq Require Import Classes.RelationClasses Lists.List Program.Equality Setoid ssreflect Strings.String.
From mathcomp Require Import bigop choice eqtype seq ssrbool ssrfun ssrnat.
From deriving Require Import deriving.
From extructures Require Import fmap fset ord.
From AlphaPearl Require Import Alpha AlphaImpl Util.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

Import Alpha.

#[local] Open Scope fset_scope.
#[local] Open Scope string_scope.

Import AlphaStringFacts.

(** Notation inspired by _PLFA_ (https://plfa.github.io/Lambda). *)
#[local] Notation "'`' x" := (variable x) (at level 0).

#[local] Notation "'λ' x y" := (abstraction x y) (at level 200, x at level 0).

#[local] Infix "⋅" := application (at level 40).

Example examples :
  `"x" ≢_α `"y" /\
  (λ"x" `"x") ≡_α (λ"y" `"y") /\
  (λ"x" λ"y" `"x"⋅(`"x"⋅`"y")) ≡_α (λ"y" λ"x" `"y"⋅(`"y"⋅`"x")) /\
  (λ"x" `"x") ≢_α (λ"x" `"x"⋅`"y") /\
  (λ"x" `"x"⋅`"y") ≡_α (λ"a" `"a"⋅`"y") /\
  (λ"x" `"x"⋅`"y") ≢_α (λ"x" `"x"⋅`"z") /\
  (λ"x" λ"y" `"y"⋅`"x") ≢_α (λ"x" λ"y" `"x"⋅`"y") /\
  (λ"x" λ"x" `"x") ≡_α (λ"y" λ"x" `"x").
Proof.
  unfold α_equivalent.
  repeat split; try apply negbT, Bool.not_true_iff_false; intros_all;
  try apply α_equivalent_iff_α_equivalent'_free_variables;
  simpl in *.
  - apply (rwP getmP). rewrite unionmE remmE rem_valmE //.
  - repeat rewrite <- (rwP andP). repeat split;
    apply (rwP getmP); repeat rewrite unionmE remmE rem_valmE //=.
  - repeat rewrite <- (rwP andP). repeat split;
    apply (rwP getmP); repeat rewrite unionmE remmE rem_valmE //=.
    rewrite mkfmapfE !in_fsetD !in_fsetU //.
  - apply (rwP andP) in H as [].
    apply (rwP getmP) in H0.
    rewrite unionmE remmE rem_valmE /= mkfmapfE !in_fsetD !in_fsetU // in H0.
  - apply (rwP andP) in H as [].
    apply (rwP getmP) in H0.
    repeat rewrite unionmE remmE rem_valmE // in H0.
  - apply (rwP getmP). rewrite unionmE remmE rem_valmE //.
Qed.
