From AlphaPearl Require Import Util.Tactics.
From Coq Require Import Bool List ssreflect Strings.String.
Import ListNotations.
From mathcomp Require Import bigop eqtype seq ssrbool ssrnat.

Set Asymmetric Patterns.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Printing Implicit Defensive.

#[local] Open Scope string_scope.

Lemma length_append :
  forall x y : string,
    length (x ++ y) = length x + length y.
Proof.
  intros.
  gen_dep y. induction x; intros; auto.
  rewrite /= -[LHS]addn1 -[RHS]addn1. auto.
Qed.

Lemma length_concat_cons :
  forall (s : seq string) (sep x : string),
    length (concat sep s) <= length (concat sep (x :: s)).
Proof.
  intros.
  gen_dep x. induction s; intros; auto.
  rewrite /= !length_append.
  apply leq_trans with (length sep + length (concat sep (a :: s)));
  rewrite leq_addl //.
Qed.
