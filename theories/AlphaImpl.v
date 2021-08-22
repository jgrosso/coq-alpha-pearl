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
    introv.
    rewrite -> Forall_forall. introv Hx_In_s.
    gen x. induction s; intros; auto.
    inverts Hx_In_s.
    - destruct s; auto.
      rewrite /= length_append leq_addr //.
    - apply leq_trans with (length (Fresh_seq s)); auto.
      rewrite /Fresh_seq !length_append leq_add2l length_concat_cons //.
  Qed.

  Lemma Fresh_seq_neq :
    forall s : seq string,
      Forall (fun x => x <> Fresh_seq s) s.
  Proof.
    introv.
    rewrite -> Forall_forall. introv Hx_In_s.
    pose proof Fresh_seq_length s as HFresh. rewrite -> Forall_forall in HFresh. apply HFresh in Hx_In_s.
    introv Hx. subst. rewrite ltnn // in Hx_In_s.
  Qed.

  Definition 𝒱 := string_ordType.

  Definition Fresh (s : {fset 𝒱}) : 𝒱 := Fresh_seq s.

  Lemma Fresh_correct : forall s : {fset 𝒱}, Fresh s ∉ s.
  Proof.
    unfold Fresh.
    introv.
    apply negbT, Bool.not_true_iff_false. introv HFresh.
    pose proof Fresh_seq_neq s as HnFresh. rewrite -> Forall_forall in HnFresh. apply In_mem, HnFresh in HFresh.
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
    introv.
    rewrite -> Forall_forall. introv Hx_In_s. subst.
    apply In_mem in Hx_In_s.
    gen x. induction s; intros; auto.
    rewrite big_cons.
    rewrite in_cons in Hx_In_s. apply (rwP orP) in Hx_In_s as [Hxa|Hx_In_s].
    - apply (rwP eqP) in Hxa. subst.
      rewrite -[(a + _).+1]addn1 addnC addnA [1 + a]addnC ltn_addr // addn1 ltnSn //.
    - apply IHs in Hx_In_s. rewrite -[(a + ∑_(j ∈ s) j).+1]addn1 -addnA addnC ltn_addr // addn1 //.
  Qed.

  Definition 𝒱 := nat_ordType.

  Definition Fresh (s : {fset 𝒱}) : 𝒱 := Fresh_seq s.

  Lemma Fresh_correct : forall s : {fset 𝒱}, Fresh s ∉ s.
  Proof.
    unfold Fresh.
    introv.
    apply negbT, Bool.not_true_iff_false. introv HFresh.
    pose proof Fresh_seq_lt s as HltFresh. rewrite -> Forall_forall in HltFresh. apply In_mem, HltFresh in HFresh.
    rewrite ltnn // in HFresh.
  Qed.
End AlphaNat.

Module AlphaNatFacts := AlphaFacts AlphaNat.
