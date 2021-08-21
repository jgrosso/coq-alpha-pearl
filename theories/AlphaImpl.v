From Coq Require Import Classes.RelationClasses Lists.List Program.Equality Setoid ssreflect Strings.String.
From mathcomp Require Import bigop choice eqtype seq ssrbool ssrfun ssrnat.
From deriving Require Import deriving.
From extructures Require Import fmap fset ord.
From AlphaPearl Require Import Alpha Util.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

#[local] Open Scope fset_scope.

(** This is almost certainly the preferred implementation of [Alpha]. *)
Module AlphaString <: Alpha.
  #[local] Open Scope string_scope.

  Definition Fresh_seq (s : seq string) := " " ++ concat "" s.

  Lemma Fresh_seq_length :
    forall s : seq string,
      Forall (fun x => length x < length (Fresh_seq s)) s.
  Proof.
    intros.
    rewrite -> Forall_forall. intros.
    gen x. induction s; intros; auto.
    inverts H.
    - destruct s; auto.
      rewrite /= length_append leq_addr //.
    - apply leq_trans with (length (Fresh_seq s)); auto.
      rewrite /Fresh_seq !length_append leq_add2l length_concat_cons //.
  Qed.

  Lemma Fresh_seq_neq :
    forall s : seq string,
      Forall (fun x => x <> Fresh_seq s) s.
  Proof.
    intros.
    rewrite -> Forall_forall. intros.
    pose proof Fresh_seq_length s. rewrite -> Forall_forall in H0. apply H0 in H.
    intros_all. subst. rewrite ltnn // in H.
  Qed.

  Definition 𝒱 := string_ordType.

  Definition Fresh (s : {fset 𝒱}) : 𝒱 := Fresh_seq s.

  Lemma Fresh_correct : forall s : {fset 𝒱}, Fresh s ∉ s.
  Proof.
    unfold Fresh.
    intros.
    apply negbT, Bool.not_true_iff_false. intros_all.
    pose proof Fresh_seq_neq s. rewrite -> Forall_forall in H0. apply In_mem, H0 in H.
    contradiction.
  Qed.
End AlphaString.

Module AlphaStringFacts := AlphaFacts AlphaString.

(** However, we're not limited to [string]s; for example, we'll implement [Alpha nat] to prove the independence of [Alpha] from any specific [𝒱]. *)
Module AlphaNat <: Alpha.
  Definition Fresh_seq (s : seq nat) := S (∑_(i ∈ s) i).

  Lemma Fresh_seq_lt :
    forall s : seq nat,
      Forall (fun x => x < Fresh_seq s) s.
  Proof.
    unfold Fresh_seq.
    intros.
    rewrite -> Forall_forall. intros_all. subst.
    apply In_mem in H.
    gen x. induction s; intros; auto.
    rewrite big_cons.
    rewrite in_cons in H. apply (rwP orP) in H as [].
    - apply (rwP eqP) in H. subst.
      rewrite -[(a + _).+1]addn1 addnC addnA [1 + a]addnC ltn_addr // addn1 ltnSn //.
    - apply IHs in H. rewrite -[(a + ∑_(j ∈ s) j).+1]addn1 -addnA addnC ltn_addr // addn1 //.
  Qed.

  Definition 𝒱 := nat_ordType.

  Definition Fresh (s : {fset 𝒱}) : 𝒱 := Fresh_seq s.

  Lemma Fresh_correct : forall s : {fset 𝒱}, Fresh s ∉ s.
  Proof.
    unfold Fresh.
    intros.
    apply negbT, Bool.not_true_iff_false. intros_all.
    pose proof Fresh_seq_lt s. rewrite -> Forall_forall in H0. apply In_mem, H0 in H.
    rewrite ltnn // in H.
  Qed.
End AlphaNat.

Module AlphaNatFacts := AlphaFacts AlphaNat.
