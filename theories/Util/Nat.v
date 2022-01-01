From AlphaPearl Require Import Util.PlfTactics.
From Coq Require Import ssreflect.
From mathcomp Require Import ssrnat.

Set Asymmetric Patterns.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Printing Implicit Defensive.

Lemma maxn_either :
  forall m n,
    maxn m n = m \/ maxn m n = n.
Proof.
  intros.
  gen n. induction m; intros.
  - right. rewrite max0n //.
  - destruct n; auto.
    rewrite maxnSS.
    destruct (IHm n) as [IHm'|IHm']; auto.
Qed.

Lemma maxn_max :
  forall m n,
    Nat.max m n = maxn m n.
Proof.
  intros.
  gen n. induction m; intros; destruct n; auto.
  rewrite /= IHm maxnSS //.
Qed.
