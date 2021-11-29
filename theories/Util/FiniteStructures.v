From AlphaPearl Require Import Util.Seq Util.PlfTactics.
From Coq Require Import Bool List ssreflect.
Import ListNotations.
From mathcomp Require Import bigop eqtype seq ssrbool ssrnat.
From extructures Require Import fmap fset ord.

Set Asymmetric Patterns.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Printing Implicit Defensive.

#[local] Open Scope fset_scope.
#[local] Open Scope list_scope.

Notation "'∅'" := fset0 : fset_scope.

Notation "x '∪' y" := (x :|: y) (at level 52) : fset_scope.

Notation "x '∩' y" := (x :&: y) (at level 48) : fset_scope.

Notation "⋃_( x ∈ s ) y" :=
  (\bigcup_(x <- s) y)
    (at level 41, x, s at level 50, y at level 200) : fset_scope.

Notation "∑_( x ∈ s ) y" :=
  (\sum_(x <- s) y)
    (at level 41, x, s at level 50, y at level 200) : fset_scope.

Infix "⊆" := fsubset (at level 40) : fset_scope.

(** Coercions can't be overridden, so we'll define a wrapper type (and some new, yet similar-looking)
    notation to convince Coq to use this coercion instead. *)
Definition fmap_of' (S : ordType) (T : Type) := @FMap.fmap_of _ _ (Phant (S -> T)).

Notation "'{' 'fmap' S '→' T '}'" := (fmap_of' S T) (at level 0) : type_scope.

Definition fmap_to_Prop (A : ordType) (B : Type) (R : {fmap A → B}) (k : A) (v : B) : Prop :=
  getm R k = Some v.

Coercion fmap_to_Prop : fmap_of' >-> Funclass.

Arguments getmP {_ _ _ _ _}.

Arguments injectivemP {_ _ _}.

Arguments pimfsetP {_ _ _ _ _}.

Lemma fset_uniq :
  forall (A : ordType) (s : {fset A}),
    uniq s.
Proof.
  intros ?.
  apply fset_ind; auto. intros.
  rewrite -[s]fsvalK -fset_cons /=.
  assert (uniq (x :: s)). { rewrite /= H H0 //. }
  rewrite -> uniq_size_fset in *.
  rewrite fsvalK //.
Qed.

Lemma size_cons :
  forall (A : ordType) (s : {fset A}) (x : A),
    x ∉ s ->
    size (x |: s) = S (size s).
Proof.
  intros.
  assert (uniq (x :: s)). { rewrite cons_uniq H fset_uniq //. }
  rewrite uniq_size_fset in H0.
  rewrite -[s]fsvalK -fset_cons.
  apply (rwP eqP) in H0.
  rewrite -H0 fsvalK //.
Qed.

Lemma In_mem :
  forall (A : ordType) (l : list A) (x : A),
    In x l <-> x ∈ l.
Proof.
  intros.
  split; intros;
  induction l; auto.
  - inverts H.
    + apply mem_head.
    + rewrite in_cons.
      apply (rwP orP).
      auto.
  - inverts H.
  - rewrite in_cons in H.
    apply (rwP orP) in H.
    inverts H.
    + left.
      apply (rwP eqP) in H0. auto.
    + right. auto.
Qed.

Lemma In_mem_fset :
  forall (A : ordType) (l : list A) (x : A),
    In x l <-> x ∈ fset l.
Proof.
  intros.
  split; intros;
  induction l; auto.
  - rewrite fset_cons in_fsetU.
    inverts H.
    + rewrite in_fset1 eq_refl //.
    + rewrite IHl // orbT //.
  - rewrite -fset0E in H.
    inverts H.
  - rewrite fset_cons in_fsetU in H.
    apply (rwP orP) in H. inverts H.
    + rewrite in_fset1 in H0.
      apply (rwP eqP) in H0. subst.
      left. auto.
    + right. auto.
Qed.

Lemma fset1_repeat :
  forall (A : ordType) (x : A),
    fset [x; x] = fset1 x.
Proof.
  intros.
  apply eq_fset. intro.
  apply Bool.eq_true_iff_eq.
  split; intros.
  - rewrite in_fset1.
    apply In_mem_fset in H.
    inverts H; auto.
    + apply eq_refl.
    + inverts H0; auto.
      apply eq_refl.
  - rewrite in_fset1 in H.
    apply In_mem_fset.
    left.
    apply (rwP eqP) in H. auto.
Qed.

Lemma size_fset2 :
  forall (A : ordType) (x y : A),
    x <> y ->
    size (fset [x; y]) = 2.
Proof.
  intros.
  replace 2 with (size [x; y]); auto.
  symmetry.
  apply (introF eqP) in H. apply Bool.negb_true_iff in H.
  apply (rwP eqP).
  rewrite -uniq_size_fset /= in_fset1 H //.
Qed.

Lemma app_as_cat :
  forall (A : Type) (l1 l2 : list A),
    app l1 l2 = seq.cat l1 l2.
Proof. induction l1; auto. Qed.

Definition any (A : Type) (P : A -> bool) (l : list A) : bool := fold_right orb false (map P l).

Lemma anyP :
  forall {A : ordType} {P : A -> bool} {l : list A},
    reflect (exists x : A, (x ∈ l) && P x) (any P l).
Proof.
  intros.
  induction l.
  - constructor.
    intros []. auto.
  - cbn. fold (any P l).
    inverts IHl.
    + rewrite orbT. constructor.
      destruct H0 as [].
      exists x. rewrite in_cons Bool.andb_orb_distrib_l H0 orbT //.
    + destruct (P a) eqn:?;
      constructor; eauto.
      * exists a. rewrite mem_head Heqb //.
      * intros [].
        apply H0. exists x.
        rewrite in_cons in H1.
        apply (rwP andP) in H1 as [].
        rewrite H2.
        apply (rwP orP) in H1 as [].
        -- apply (rwP eqP) in H1. subst.
           rewrite H2 // in Heqb.
        -- rewrite H1 //.
Qed.

Lemma fset2_eq :
  forall (A : ordType) (x y : A),
    [fset x; y] = fset [x; y].
Proof.
  intros.
  apply eq_fset.
  intro.
  rewrite in_fset2.
  apply Bool.eq_true_iff_eq.
  split; intros.
  - apply (rwP orP) in H.
    inverts H;
    apply (rwP eqP) in H0;
    subst;
    apply In_mem_fset;
    (left + (right; left)); auto; fail.
  - apply (rwP orP).
    apply In_mem_fset in H.
    inverts H; auto.
    inverts H0; auto.
Qed.

Lemma fset2_reorder :
  forall (A : ordType) (x y : A),
    x <> y ->
    fset [x; y] = fset [y; x].
Proof.
  intros.
  apply eq_fset. intro.
  rewrite -!fset2_eq !in_fset2 Bool.orb_comm //.
Qed.

Lemma fsval_fset2 :
  forall (A : ordType) (x y : A),
    x <> y ->
    FSet.fsval (fset [x; y]) = [x; y] \/ FSet.fsval (fset [x; y]) = [y; x].
Proof.
  intros.
  assert (2 = size (fset [x; y])).
  { apply (rwP eqP).
    replace 2 with (size [x; y]) by auto.
    rewrite -uniq_size_fset /= Bool.andb_true_r.
    apply Bool.eq_true_not_negb. intro. apply H.
    rewrite mem_seq1 in H0.
    rewrite (rwP eqP) //. }
  destruct (FSet.fsval (fset [x; y])) eqn:?;
  inverts H0.
  destruct l.
  - inverts H2.
  - destruct l.
    + rewrite -fset2_eq in Heql.
      assert (s ∈ FSet.fsval [fset x; y]). { rewrite Heql mem_head //. }
      assert (s0 ∈ FSet.fsval [fset x; y]). { rewrite Heql. apply mem_last. }
      assert (x ∈ FSet.fsval [fset x; y]). { apply In_mem_fset. left. auto. }
      assert (y ∈ FSet.fsval [fset x; y]).
      { apply In_mem_fset.
        right.
        apply In_mem.
        apply In_mem_fset.
        left. auto. }
      apply (rwP (fset2P _)) in H0, H1.
      inverts H0; inverts H1; auto;
      ((assert (x ∈ [y; y]) by rewrite -Heql //) ||
       (assert (y ∈ [x; x]) by rewrite -Heql //));
      apply In_mem in H0;
      inverts H0; auto;
      inverts H1; auto;
      inverts H0; auto.
    + inverts H2.
Qed.

Lemma mapm_setm :
  forall (A : ordType) (B C : Type) (f : B -> C) (m : {fmap A -> B}) (k : A) (v : B),
    mapm f (setm m k v) = setm (mapm f m) k (f v).
Proof.
  intros.
  apply eq_fmap. intro.
  rewrite !mapmE !setmE.
  destruct (x =P k); subst; auto.
  rewrite mapmE //.
Qed.

Lemma all_fset1 :
  forall (A : ordType) (P : A -> bool) (x : A),
    all P (fset1 x) = P x.
Proof.
  intros.
  rewrite /= Bool.andb_true_r //.
Qed.

Lemma all_fset2 :
  forall (A : ordType) (P : A -> bool) (x y : A),
    all P (fset [x; y]) = P x && P y.
Proof.
  intros.
  rewrite all_fset /= Bool.andb_true_r //.
Qed.

Lemma all_fsubset :
  forall (A : ordType) (P : A -> bool) (s s__sub : {fset A}),
    fsubset s__sub s ->
    all P s ->
    all P s__sub.
Proof.
  intros. generalize dependent s__sub.
  apply (fset_ind (P := fun s__sub : {fset A} => fsubset s__sub s -> all P s__sub)); auto. intros.
  rewrite all_fsetU.
  rewrite -(rwP andP).
  rewrite fsubU1set in H2.
  apply (rwP andP) in H2 as [].
  split; auto.
  rewrite all_fset1.
  apply (rwP allP) in H0.
  auto.
Qed.

Definition rem_fsetm (A : ordType) (B : Type) (m : {fmap A -> B}) (s : {fset A}) : {fmap A -> B} :=
  filterm (fun x _ => x ∉ s) m.

Infix "∖" := rem_fsetm (at level 40).

Lemma rem_fsetm_correct :
  forall (A : ordType) (B : Type) (m : {fmap A -> B}) (s : {fset A}) (x : A),
    (x ∈ s -> getm (m ∖ s) x = None) /\ (x ∉ s -> getm (m ∖ s) x = getm m x).
Proof.
  intros.
  split; intros;
  rewrite /rem_fsetm filtermE;
  destruct (getm m x) eqn:?;
  rewrite // H //.
Qed.

Lemma rem_fsetmE :
  forall (A : ordType) (B : Type) (m : {fmap A -> B}) (s : {fset A}) (k : A),
    (m ∖ s) k = if k ∈ s then None else m k.
Proof.
  intros.
  rewrite /rem_fsetm filtermE.
  destruct (m k) eqn:?.
  - apply if_neg.
  - rewrite if_same //.
Qed.

Lemma remm_disjoint_fset :
  forall (A : ordType) (B : Type) (m : {fmap A -> B}) (s : {fset A}),
    fdisjoint (domm m) s ->
    m ∖ s = m.
Proof.
  intros.
  apply eq_fmap. intro.
  rewrite /rem_fsetm filtermE.
  destruct (getm m x) eqn:?, (x ∈ s) eqn:?; rewrite /= //.
  assert (x ∉ domm m).
  { apply Bool.eq_true_not_negb. intro. subst.
    assert (x ∈ domm m ∩ s). { rewrite in_fsetI Heqb0 H0 //. }
    apply fdisjoint_fsetI0 in H.
    rewrite H in H1. inverts H1. }
  assert (exists b, m x = Some b) by eauto. apply (rwP dommP) in H1.
  rewrite H1 in H0. inverts H0.
Qed.

Lemma remm_disjoint_fset' :
  forall (A : ordType) (B : Type) (m : {fmap A -> B}) (s : {fset A}),
    m ∖ s = m ->
    fdisjoint (domm m) s.
Proof.
  intros.
  rewrite <- H.
  apply (rwP fdisjointP).
  intros.
  apply (rwP dommP) in H0 as [].
  rewrite rem_fsetmE in H0.
  apply Bool.negb_true_iff.
  destruct (x ∈ s) eqn:?; auto.
  inverts H0.
Qed.

Lemma rem_fsetm_as_fsetD :
  forall (A : ordType) (B : Type) (m : {fmap A -> B}) (s : {fset A}),
    domm (m ∖ s) = domm m :\: s.
Proof.
  intros.
  apply eq_fset. intros_all.
  rewrite /rem_fsetm in_fsetD mem_domm filtermE.
  destruct (m x) eqn:?.
  - simpl.
    destruct (x ∈ s) eqn:?; auto.
    symmetry.
    apply (rwP dommP). eauto.
  - simpl.
    apply (rwP dommPn) in Heqo. apply Bool.negb_true_iff in Heqo.
    rewrite Heqo andbF //.
Qed.

Definition fset_flat_map (A B : ordType) (f : A -> {fset B}) (s : {fset A}) : {fset B} :=
  ⋃_(x ∈ f @: s) x.

Lemma fset_flat_mapP :
  forall {A B : ordType} {f : A -> {fset B}} {s : {fset A}} {x : B},
    reflect (exists2 y, y ∈ s & x ∈ f y) (x ∈ fset_flat_map f s).
Proof.
  intros.
  apply (iffP idP); intros.
  - rewrite /fset_flat_map in_bigcup in H. apply (rwP hasP) in H as [].
    apply (rwP imfsetP) in H as []. subst. eauto.
  - rewrite /fset_flat_map in_bigcup. apply (rwP hasP).
    destruct H. exists (f x0); eauto.
    apply (rwP imfsetP). eauto.
Qed.

Definition fproduct (A B : ordType) (xs : {fset A}) (ys : {fset B}) : {fset (A * B)} :=
  fset_flat_map (fun x : A => fset_flat_map (fun y : B => fset1 (x, y)) ys) xs.

Infix "×" := fproduct (at level 40).

Lemma fproductP :
  forall (A B : ordType) (x : A) (y : B) (xs : {fset A}) (ys : {fset B}),
    reflect (x ∈ xs /\ y ∈ ys) ((x, y) ∈ xs × ys).
Proof.
  intros.
  apply (iffP idP); intros.
  - apply (rwP fset_flat_mapP) in H as []. apply (rwP fset_flat_mapP) in H0 as [].
    rewrite in_fset1 in H1. apply (rwP eqP) in H1. inversion H1. eauto.
  - destruct H.
    apply (rwP fset_flat_mapP). exists x; eauto.
    apply (rwP fset_flat_mapP). exists y; eauto.
    rewrite in_fset1 //.
Qed.

Lemma in_codomm_remm :
  forall (A B : ordType) (m : {fmap A -> B}) (k k' : A) (v : B),
    getm m k = Some v ->
    k <> k' ->
    v ∈ codomm (remm m k').
Proof.
  intros.
  apply (rwP codommP). exists k. rewrite remmE.
  replace (k == k') with false; auto.
  symmetry. apply Bool.not_true_is_false. intro. apply (rwP eqP) in H1. auto.
Qed.

Lemma codomm_setmE :
  forall (A B : ordType) (m : {fmap A -> B}) (k : A) (v : B),
    codomm (setm m k v) = v |: codomm (remm m k).
Proof.
  intros.
  apply eq_fset. intro.
  rewrite in_fsetU in_fset1.
  destruct (x ∈ codomm (setm m k v)) eqn:?.
  - apply (rwP codommP) in Heqb as []. rewrite setmE in H.
    destruct (x0 =P k); subst.
    + inverts H. rewrite eq_refl //.
    + assert (exists x0, m x0 = Some x) by eauto. apply (rwP codommP) in H0.
      erewrite in_codomm_remm; eauto. rewrite orbT //.
  - apply Bool.negb_true_iff in Heqb.
    rewrite <- (rwP (@codommPn _ _ (setm m k v) x)) in Heqb.
    assert (setm m k v k != Some x) by auto.
    replace (x == v) with false; cycle 1.
    { symmetry. apply Bool.not_true_is_false. intro. apply (rwP eqP) in H0. subst.
      rewrite setmE eq_refl in H. apply Bool.negb_true_iff in H. rewrite eq_refl // in H. }
    symmetry.
    apply Bool.negb_true_iff.
    rewrite <- (rwP (@codommPn _ _ (remm m k) x)). intros.
    rewrite remmE.
    destruct (k' =P k); subst; auto.
    assert (setm m k v k' != Some x) by auto.
    rewrite setmE in H0.
    replace (k' == k) with false in H0; auto.
    symmetry. apply Bool.not_true_is_false. intro. apply (rwP eqP) in H0. subst.
    apply n, (rwP eqP). auto.
Qed.

Lemma remm_setm_distr :
  forall (A B : ordType) (m : {fmap A -> B}) (k k' : A) (v : B),
    k <> k' ->
    remm (setm m k v) k' = setm (remm m k') k v.
Proof.
  intros.
  apply eq_fmap. intro.
  rewrite remmE !setmE remmE.
  destruct (x =P k'), (x =P k); auto.
  subst. exfalso. auto.
Qed.

Lemma remm_emptym :
  forall (A : ordType) (B : Type) (k : A),
    remm (@emptym _ B) k = emptym.
Proof.
  intros.
  apply eq_fmap. intro.
  rewrite remmE.
  destruct (x =P k); auto.
Qed.

Lemma fsetI0_fdisjoint :
  forall (T : ordType) (s1 s2 : {fset T}),
    s1 ∩ s2 = ∅ ->
    fdisjoint s1 s2.
Proof.
  intros.
  apply (rwP fdisjointP). intros.
  apply Bool.negb_true_iff, Bool.not_true_iff_false. intros_all.
  assert (x ∈ s1 ∩ s2). { rewrite -(rwP (fsetIP _ s1 s2)) //. }
  rewrite H in_fset0 // in H2.
Qed.

Lemma rem_fsetmI0 :
  forall (A : ordType) (B : Type) (m : {fmap A -> B}),
    m ∖ ∅ = m.
Proof.
  intros.
  apply eq_fmap. intros_all.
  rewrite rem_fsetmE //.
Qed.

Definition rem_valm {A B : ordType} (m : {fmap A -> B}) (v : B) : {fmap A -> B} :=
  filterm (fun _ v' => v != v') m.

Lemma rem_valmE :
  forall (A B : ordType) (m : {fmap A -> B}) (k : A) (v : B),
    getm (rem_valm m v) k =
      match m k with
      | Some v' => if v == v' then None else Some v'
      | None => None
      end.
Proof.
  intros.
  rewrite /rem_valm filtermE.
  destruct (m k) eqn:?; auto.
  simpl. destruct (v =P s); auto.
Qed.

Lemma eq_fmap' :
  forall (A B : ordType) (m1 m2 : {fmap A -> B}),
    (forall (a : A) (b : B), m1 a = Some b <-> m2 a = Some b) ->
    m1 = m2.
Proof.
  intros.
  apply eq_fmap. intros_all.
  destruct (m1 x) eqn:?.
  - apply H in Heqo. auto.
  - cut (forall y : B, m2 x <> Some y).
    { intros_all.
      destruct (m2 x) eqn:?; auto.
      exfalso. apply (H0 s). auto. }
    intros_all.
    apply H in H0. rewrite H0 // in Heqo.
Qed.

Lemma domm_codomm_invm :
  forall (A B : ordType) (m : {fmap A -> B}),
    injectivem m ->
    domm m = codomm (invm m).
Proof.
  intros.
  apply (rwP injectivemP) in H.
  apply eq_fset. intros_all.
  destruct (x ∈ domm m) eqn:?.
  - apply (rwP dommP) in Heqb as [].
    symmetry. apply (rwP codommP).
    exists x0.
    apply getm_inv.
    rewrite invmK //.
  - apply Bool.negb_true_iff, (rwP dommPn) in Heqb.
    symmetry. apply Bool.negb_true_iff, (rwP codommPn). intros_all.
    apply Bool.negb_true_iff, Bool.not_true_iff_false. intros_all.
    apply (rwP eqP), getm_inv in H0.
    rewrite Heqb // in H0.
Qed.

Lemma codomm_domm_invm :
  forall (A B : ordType) (m : {fmap A -> B}),
    injectivem m ->
    codomm m = domm (invm m).
Proof.
  intros.
  apply (rwP injectivemP) in H.
  apply eq_fset. intros_all.
  destruct (x ∈ codomm m) eqn:?.
  - apply (rwP dommP) in Heqb as [].
    symmetry. apply (rwP codommP).
    exists x0.
    apply getm_inv. auto.
  - apply Bool.negb_true_iff, (rwP dommPn) in Heqb.
    symmetry. apply Bool.negb_true_iff, (rwP dommPn). auto.
Qed.

Lemma invm_None :
  forall (A B : ordType) (m : {fmap A -> B}) (x : B),
    injectivem m ->
    invm m x = None <-> x ∉ codomm m.
Proof.
  intros.
  split; intros.
  - rewrite codomm_domm_invm; auto.
    apply (rwP dommPn). auto.
  - rewrite <- (rwP (@codommPn _ _ m x)) in H0.
    cut (forall y, invm m x <> Some y).
    { intros. destruct (invm m x) eqn:?; auto. exfalso. apply (H1 s). auto. }
    intros_all.
    pose proof H0 y. apply Bool.negb_true_iff, Bool.not_true_iff_false in H2. apply H2.
    rewrite (getm_inv (k := x)); auto. rewrite eq_refl //.
Qed.

Lemma fsetU_repeat : forall (A : ordType) (s : {fset A}), s ∪ s = s.
Proof.
  intros.
  apply eq_fset. intros_all.
  rewrite in_fsetU Bool.orb_diag //.
Qed.

Lemma fsetU_noop :
  forall (A : ordType) (s s' : {fset A}),
    s' ⊆ s ->
    s ∪ s' = s.
Proof.
  intros.
  apply eq_fset. intros_all.
  rewrite in_fsetU.
  destruct (x ∈ s) eqn:?; auto.
  apply (rwP fsubsetP) in H.
  apply Bool.not_true_iff_false. intros_all.
  apply H in H0. rewrite H0 // in Heqb.
Qed.

Lemma fsubset_fsetU :
  forall (A : ordType) (s1 s2 s3 : {fset A}),
    s1 ⊆ s2 ->
    (s1 ∪ s3) ⊆ (s2 ∪ s3).
Proof.
  intros.
  apply (rwP fsubsetP) in H.
  apply (rwP fsubsetP). intros_all.
  rewrite in_fsetU.
  rewrite in_fsetU in H0. apply (rwP orP) in H0 as [].
  - apply H in H0. rewrite H0 //.
  - rewrite H0 orbT //.
Qed.

Lemma remm_mapm :
  forall (A : ordType) (B : Type) (f : B -> B) (m : {fmap A → B}) (x : A),
    remm (mapm f m) x = mapm f (remm m x).
Proof.
  intros.
  apply eq_fmap. intros_all.
  rewrite remmE !mapmE remmE.
  destruct (x0 =P x); subst; auto.
Qed.

Lemma codomm_mapm :
  forall (A B : ordType) (f : B -> B) (m : {fmap A → B}),
    codomm (mapm f m) = f @: codomm m.
Proof.
  intros.
  apply eq_fset. intros_all.
  apply Bool.eq_iff_eq_true. split; intros.
  - apply (rwP codommP) in H as [].
    rewrite mapmE in H.
    destruct (getm m x0) eqn:?; inverts H.
    apply (rwP imfsetP). exists s; auto.
    apply (rwP codommP). eauto.
  - apply (rwP imfsetP) in H as [].
    apply (rwP codommP) in H as [].
    subst.
    apply (rwP codommP).
    exists x1. rewrite mapmE H //.
Qed.
