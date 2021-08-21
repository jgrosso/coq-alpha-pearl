From AlphaPearl Require Import Util.PlfTactics.
From Coq Require Import Bool List ssreflect.
Import ListNotations.
From mathcomp Require Import bigop eqtype seq ssrbool ssrnat.

Set Asymmetric Patterns.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Printing Implicit Defensive.

#[local] Open Scope list_scope.

(* Note that, at least for now, [maximum nil = 0]. *)
Definition maximum : list nat -> nat := foldr maxn 0.

Lemma maximum_correct : forall (l : list nat) (x : nat), x \in l -> x <= maximum l.
Proof.
  induction l; intros.
  { inverts H. }
  rewrite /= leq_max.
  rewrite in_cons in H. apply (rwP orP) in H as [].
  - apply (rwP eqP) in H. subst. rewrite leqnn //.
  - apply IHl in H. rewrite H orbT //.
Qed.

Lemma maxE r : maximum r = \max_(i <- r) i. Proof. apply foldrE. Qed.
