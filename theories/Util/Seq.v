From AlphaPearl Require Import Util.Nat Util.PlfTactics.
From Coq Require Import Bool List ssreflect.
Import ListNotations.
From mathcomp Require Import bigop eqtype seq ssrbool ssrnat.

Set Asymmetric Patterns.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Printing Implicit Defensive.

#[local] Open Scope list_scope.

Notation "x '∈' y" := (x \in y) (at level 70).

Notation "x '∉' y" := (x \notin y) (at level 70).

(* Note that, at least for now, [maximum nil = 0]. *)
Definition maximum : list nat -> nat := foldr maxn 0.

Lemma maximum_correct : forall (l : list nat) (x : nat), x ∈ l -> x <= maximum l.
Proof.
  induction l; intros.
  { inverts H. }
  rewrite /= leq_max.
  rewrite in_cons in H. apply (rwP orP) in H as [].
  - apply (rwP eqP) in H. subst. rewrite leqnn //.
  - apply IHl in H. rewrite H orbT //.
Qed.

Lemma maxE r : maximum r = \max_(i <- r) i. Proof. exact: foldrE. Qed.

Lemma bigmax_subset :
  forall sub super : seq nat,
    {subset sub <= super} ->
    \max_(x <- sub) x <= \max_(x <- super) x.
Proof.
  intros.
  gen super. induction sub; intros; simpl in *.
  - rewrite big_nil //.
  - rewrite big_cons.
    assert (a ∈ a :: sub). { rewrite in_cons eq_refl //. }
    apply H in H0.
    rewrite geq_max -{1}maxE maximum_correct //.
    apply IHsub. intros_all.
    apply H. rewrite in_cons.
    destruct (x =P a); subst; auto.
Qed.

Lemma S_bigmax :
  forall s : seq nat,
    \max_(x <- s) S x <= S (\max_(x <- s) x).
Proof.
  intros.
  induction s.
  { rewrite !big_nil //. }
  rewrite !big_cons -!maxnSS geq_max leq_max leqnn leq_max IHs orbT //.
Qed.

Lemma maximum_in :
  forall l : seq nat,
    l = nil \/ maximum l ∈ l.
Proof.
  intros.
  induction l; auto.
  right.
  rewrite in_cons.
  destruct IHl as [IHl|IHl]; subst.
  - rewrite eq_refl //.
  - destruct (maxn_either a (maximum l)) as [Hmax|Hmax]; rewrite /= Hmax.
    + rewrite eq_refl //.
    + rewrite IHl orbT //.
Qed.

Lemma maximum_leq :
  forall l1 l2 : seq nat,
    (forall n, n ∈ l1 -> n <= maximum l2) ->
      maximum l1 <= maximum l2.
Proof.
  introv Hl12.
  induction l1; auto.
  rewrite /= geq_max -(rwP andP). split.
  - rewrite Hl12 // mem_head //.
  - apply IHl1. introv Hn.
    rewrite Hl12 // in_cons Hn orbT //.
Qed.
