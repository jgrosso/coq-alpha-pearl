(* The code style is pretty messy, since we've been prioritizing prototyping speed so far.
   However, now that the main results have been formalized, we intend to heavily refactor the proof scripts.

   ===== TODOs =====
   These will probably be rendered moot by [compute-sets] (assuming it is a success):
     - Standardize naming for [domm], [codomm], [co_domm], [co_domain], etc.

   These will best be tackled after finishing (or abandoning) [compute-sets]:
     - Name hypotheses explicitly in proofs.
     - Use [Lemma]s or ([Hint Extern]s) to remove duplication in proofs. (Maybe in combination with [autorewrite]?)
     - Clean up ordering of definitions/lemmas/parameters/notations/etc.
     - Improve names of lemmas/theorems/etc.
     - Remove dead code.
     - Break up into separate files?
     - Implement custom printing for notations.
     - Improve compilation speed.

   These are specific to [compute-sets]:
     - Change all the [*_type] proofs to talk about [domm] and [codomm], and re-add any that were removed from this branch despite being referenced in the paper.
     - Prove the original, fully-generalized theorems from the paper. *)

From Coq Require Import Classes.RelationClasses Lists.List Program.Equality Setoid ssreflect.
From mathcomp Require Import bigop choice eqtype seq ssrbool ssrfun ssrnat.
From deriving Require Import deriving.
From extructures Require Import fmap fset ord.
From AlphaPearl Require Import Util.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

#[local] Open Scope fset_scope.

Module Type Alpha.
  Parameter 𝒱 : ordType.

  Parameter Fresh : {fset 𝒱} -> 𝒱.

  Parameter Fresh_correct : forall s : {fset 𝒱}, Fresh s ∉ s.
End Alpha.

Module AlphaFacts (Import M : Alpha).
  #[local] Notation "x '∪' '{' y '}'" := (x :|: fset1 y) (at level 52) : fset_scope.

  Inductive term : Type :=
  | abstraction : 𝒱 -> term -> term
  | application : term -> term -> term
  | variable : 𝒱 -> term.

  #[export] Hint Constructors term : core.

  Canonical term_indType := IndType term [indDef for term_rect].

  Canonical term_eqType := EqType term [derive eqMixin for term].

  Canonical term_choiceType := ChoiceType term [derive choiceMixin for term].

  Canonical term_ordType := OrdType term [derive ordMixin for term].

  Implicit Types (W X Y Z : {fset 𝒱}) (t u : term) (v w x y z : 𝒱) (R S : {fmap 𝒱 → 𝒱}).

  Fixpoint free_variables t : {fset 𝒱} :=
    match t with
    | abstraction x t => free_variables t :\ x
    | application t1 t2 => free_variables t1 ∪ free_variables t2
    | variable x => fset1 x
    end.

  #[local] Notation FV := free_variables.

  Definition Tm X t : bool := fsubset (FV t) X.

  (** Page 2: "Instead of defining a set of terms we define a family of sets Tm(X) of terms with free variables in X ⊆fin 𝒱 inductively...." *)
  Section in_Tm.
    #[local] Reserved Notation "t '∈' 'Tm' X" (at level 40).

    Inductive in_Tm : {fset 𝒱} -> term -> Prop :=
    | Tm_variable : forall X x,
        x ∈ X ->
        variable x ∈ Tm X
    | Tm_application : forall X t u,
        t ∈ Tm X -> u ∈ Tm X ->
        application t u ∈ Tm X
    | Tm_abstraction : forall X t x,
        t ∈ Tm (X ∪ {x}) ->
        abstraction x t ∈ Tm X

    where "t '∈' 'Tm' X" := (in_Tm X t).
  End in_Tm.

  #[local] Hint Constructors in_Tm : core.

  Lemma TmP : forall X t, reflect (in_Tm X t) (t ∈ Tm X).
  Proof.
    rewrite /Tm /in_mem /=.
    intros.
    gen X. induction t; intros; simpl;
    ((rewrite fsubD1set fsetUC; destruct (IHt (X ∪ {s}))) ||
     (rewrite fsubUset; destruct (IHt1 X), (IHt2 X)) ||
     (rewrite fsub1set; destruct (s ∈ X) eqn:?));
    constructor; intros_all; auto;
    inverts H; auto.
    rewrite /= Heqb // in H2.
  Qed.

  Definition is_subset_of R X Y : Prop :=
    forall x y, R x y -> (x ∈ X) && (y ∈ Y).

  #[local] Notation "R '⊆' X '×' Y" := (is_subset_of R X Y) (at level 40, X at next level).

  #[local] Notation partial_bijection := is_injective (only parsing).

  (** Page 3: "Given R a partial bijection as above and x, y ∈ 𝒱 we define the symmetric update of R as...." *)
  Definition update R x y : {fmap 𝒱 → 𝒱} :=
    unionm (remm (rem_valm _ R y) x) [fmap (x, y)].

  #[local] Notation "R '⦅' x ',' y '⦆'" := (update R x y) (at level 0).

  (** Page 3: "It is easy to see that R(x,y) is a partial bijection." *)
  Lemma partial_bijection_update :
    forall R x y,
      partial_bijection R ->
      partial_bijection R⦅x,y⦆.
  Proof.
    rewrite /partial_bijection /=.
    intros.
    apply (rwP injectivemP) in H.
    rewrite <- (rwP injectivemP). intros_all.
    apply (rwP dommP) in H0 as [].
    rewrite /update !unionmE /= !remmE !setmE !rem_valmE in H0, H1.
    destruct (x0 =P x); subst.
    - inverts H0.
      destruct (x2 =P x); subst; auto.
      destruct (getm R x2) eqn:?; rewrite ?Heqo // in H1.
      destruct (x1 =P s); subst; inverts H1.
      exfalso. auto.
    - destruct (getm R x0) eqn:?; rewrite ?Heqo // in H0, H1.
      destruct (y =P s); subst; inverts H0.
      destruct (x2 =P x); subst.
      * inverts H1. exfalso. auto.
      * destruct (getm R x2) eqn:?; rewrite ?Heqo0 // in H1.
        destruct (y =P s); subst; inverts H1.
        apply H.
        -- apply (rwP dommP). eauto.
        -- rewrite Heqo //.
  Qed.

  (** Page 3: "R(x,y) ... ∈ (X ∪ {x}) × (Y ∪ {y})." *)
  Lemma update_type :
    forall X Y R x y,
      (forall a b : 𝒱, R a b -> a ∈ X /\ b ∈ Y) ->
      R ⊆ X × Y ->
      R⦅x,y⦆ ⊆ (X ∪ {x}) × (Y ∪ {y}).
  Proof.
    unfold is_subset_of.
    intros.
    rewrite /= !in_fsetU !in_fset1.
    rewrite /fmap_to_Prop /update unionmE remmE setmE rem_valmE /= in H1.
    destruct (x0 =P x); subst; inverts H1.
    - rewrite eq_refl !orbT //.
    - destruct (getm R x0) eqn:?.
      + destruct (y =P s); subst; inverts H3.
        apply H in Heqo as []. simpl in *. rewrite H1 H2 //.
      + inverts H3.
  Qed.

  #[local] Reserved Notation "t '≡_α^' R u" (at level 40, R at level 0).

  Fixpoint α_equivalent' R t u : bool :=
    match t, u with
    | variable x, variable y => (x, y) ∈ R
    | application t u, application t' u' => t ≡_α^R t' && (u ≡_α^R u')
    | abstraction x t, abstraction y u => t ≡_α^R⦅x,y⦆ u
    | _, _ => false
    end

  where "t '≡_α^' R u" := (α_equivalent' R t u).

  (** Page 3: "We now define ≡α^R ⊆ Tm(X) × Tm(Y) parametrized by a partial bijection R ⊆ X × Y, inductively...." *)
  Section α_equivalent''.
    #[local] Reserved Notation "t '≡_α^' R u" (at level 40, R at level 0).

    Inductive α_equivalent'' : {fmap 𝒱 -> 𝒱} -> term -> term -> Prop :=
    | α_equivalent''_variable : forall R x y,
        (x, y) ∈ R ->
        variable x ≡_α^R variable y
    | α_equivalent''_application : forall R t t' u u',
        t ≡_α^R t' -> u ≡_α^R u' ->
        application t u ≡_α^R application t' u'
    | α_equivalent''_abstraction : forall R t u x y,
        t ≡_α^R⦅x,y⦆ u ->
        abstraction x t ≡_α^R abstraction y u

    where "x '≡_α^' R y" := (α_equivalent'' R x y).
  End α_equivalent''.

  #[local] Hint Constructors α_equivalent'' : core.

  Lemma α_equivalent'P : forall R t u, reflect (α_equivalent'' R t u) (t ≡_α^R u).
  Proof.
    intros.
    destruct (t ≡_α^R u) eqn:?; constructor.
    - gen R u. induction t; intros;
      destruct u; inverts Heqb; auto.
      apply (rwP andP) in H0 as []; auto.
    - intros_all.
      dependent induction H; inverts Heqb; auto.
      + simpl in *. rewrite H // in H1.
      + apply negbT, (rwP nandP) in H2 as []; apply negbTE in H1; auto.
  Qed.

  (** Page 3: "We now define ≡α^R ⊆ Tm(X) × Tm(Y)." *)
  Lemma α_equivalent'_type :
    forall R t u,
      t ≡_α^R u ->
      t ∈ Tm (domm R) /\ u ∈ Tm (codomm R).
  Proof.
    rewrite /in_mem /= /Tm.
    intros_all.
    gen R u. induction t; simpl; intros;
    destruct u; inverts H;
    simpl in *.
    - apply IHt in H1 as []. apply (rwP fsubsetP) in H, H0.
      split; apply (rwP fsubsetP); intros_all;
      rewrite in_fsetD in_fset1 in H1; apply (rwP andP) in H1 as []; apply negbTE in H1.
      + apply H, (rwP dommP) in H2 as [].
        rewrite unionmE remmE rem_valmE setmE H1 in H2.
        destruct (getm R x) eqn:?; cycle 1.
        { inverts H2. }
        destruct (s0 =P s1); subst; inverts H2.
        apply (rwP dommP). eauto.
      + apply H0, (rwP codommP) in H2 as [].
        rewrite unionmE remmE rem_valmE setmE /= in H2.
        destruct (x0 =P s); subst; auto.
        { inverts H2. rewrite eq_refl // in H1. }
        destruct (getm R x0) eqn:?; cycle 1.
        { inverts H2. }
        destruct (s0 =P s1); subst; inverts H2.
        apply (rwP codommP). eauto.
    - apply (rwP andP) in H1 as [].
      apply IHt1 in H as []. apply IHt2 in H0 as [].
      apply (rwP fsubsetP) in H, H0, H1, H2.
      split; apply (rwP fsubsetP); intros_all;
      rewrite in_fsetU in H3; apply (rwP orP) in H3 as []; auto.
    - rewrite /in_mem /= /in_mem /= in H1. apply (rwP getmP) in H1.
      rewrite !fsub1set.
      split.
      + apply (rwP dommP). eauto.
      + apply (rwP codommP). eauto.
  Qed.

  (** Page 3: "Given X, Y, Z ⊂fin 𝒱 we write 1X = ...." *)
  Definition identity : {fset 𝒱} -> {fmap 𝒱 → 𝒱} := mkfmapf id.

  Class Identity (A : Type) :=
    { identity' : forall X, A }.

  #[global] Hint Mode Identity ! : typeclass_instances.

  #[local] Notation "'1__' X" := (identity' X) (at level 40).

  #[global] Instance fmap_𝒱_Identity : Identity {fmap 𝒱 → 𝒱} :=
    { identity' := identity }.

  #[global] Instance fmap_term_Identity : Identity {fmap 𝒱 → term} :=
    { identity' X := mapm variable (1__X : {fmap 𝒱 → 𝒱}) }.

  #[global] Instance fmap_to_Prop_Identity : Identity (𝒱 -> 𝒱 -> Prop) :=
    { identity' := identity }.

  (** Page 3: "1X ... ⊆ X × X." *)
  Lemma identity_type : forall X, (1__X : {fmap 𝒱 → 𝒱}) ⊆ X × X.
  Proof.
    intros_all.
    rewrite /identity' /= /fmap_to_Prop mkfmapfE in H.
    destruct (x ∈ X) eqn:?; rewrite Heqb in H;
    inverts H. auto.
  Qed.

  (** Page 3: "1X... obviously is a partial bijection." *)
  Lemma partial_bijection_identity : forall X, partial_bijection (1__X : {fmap 𝒱 → 𝒱}).
  Proof.
    intros.
    rewrite /partial_bijection /fmap_IsInjective /injective /identity' /fmap_𝒱_Identity /identity.
    intros.
    rewrite <- (rwP injectivemP).
    intros_all.
    apply (rwP dommP) in H as [].
    rewrite !mkfmapfE in H, H0.
    destruct (x ∈ X) eqn:?; rewrite Heqb in H, H0; inverts H.
    destruct (x2 ∈ X) eqn:?; rewrite Heqb0 in H0; inverts H0.
    auto.
  Qed.

  (** Page 3: "Given R ⊆ X × Y and S ⊆ Y × Z we write...." *)
  Definition converse R : {fmap 𝒱 → 𝒱} := invm R.

  #[local] Notation "R 'ᵒ'" := (converse R) (at level 40).

  (** Page 3: "Rᵒ ... ⊆ Y × X." *)
  Lemma converse_type :
    forall X Y R,
      R ⊆ X × Y ->
      R ᵒ ⊆ Y × X.
  Proof.
    intros_all.
    apply getm_inv, H in H0. rewrite andbC //.
  Qed.

  (** Page 3: "Both operations are closed under partial bijections." *)
  Lemma converse_closed_under_partial_bijection :
    forall R,
      partial_bijection R ->
      partial_bijection (R ᵒ).
  Proof.
    intros.
    apply (rwP injectivemP) in H.
    simpl. rewrite <- (rwP injectivemP). intros_all.
    apply (rwP dommP) in H0 as []. rewrite H0 in H1.
    symmetry in H1. apply getm_inv in H0, H1. rewrite H0 in H1. inverts H1. auto.
  Qed.

  (** Page 3: "Given R ⊆ X × Y and S ⊆ Y × Z we write...." *)
  Definition compose R S : {fmap 𝒱 → 𝒱} :=
    mkfmapfp
      (fun k =>
        match getm R k with
        | Some v => getm S v
        | None => None
        end)
      (domm R).

  #[local] Notation "R ';' S" := (compose R S) (at level 40).

  (** Page 3: "R;S ... ⊆ X × Z." *)
  Lemma compose_type :
    forall X Y Z R S,
      R ⊆ X × Y ->
      S ⊆ Y × Z ->
      R; S ⊆ X × Z.
  Proof.
    intros_all.
    rewrite /fmap_to_Prop mkfmapfpE in H1.
    destruct (x ∈ domm R) eqn:?; rewrite Heqb // in H1.
    apply (rwP dommP) in Heqb as []. rewrite H2 in H1.
    apply H, (rwP andP) in H2 as []. apply H0, (rwP andP) in H1 as []. rewrite H2 H4 //.
  Qed.

  (** Page 3: "Both operations are closed under partial bijections." *)
  Lemma compose_closed_under_partial_bijection :
    forall R S,
      partial_bijection R ->
      partial_bijection S ->
      partial_bijection (R; S).
  Proof.
    unfold partial_bijection.
    intros.
    apply (rwP injectivemP) in H, H0.
    simpl. rewrite <- (rwP injectivemP). intros_all.
    apply (rwP dommP) in H1 as [].
    rewrite !mkfmapfpE in H1, H2.
    destruct (x ∈ domm R) eqn:?; rewrite Heqb in H1, H2; cycle 1.
    { inverts H1. }
    apply (rwP dommP) in Heqb as []. rewrite H3 in H1, H2.
    rewrite H1 in H2.
    destruct (x2 ∈ domm R) eqn:?; rewrite Heqb in H2; cycle 1.
    { inverts H2. }
    apply (rwP dommP) in Heqb as []. rewrite H4 -H1 in H2.
    apply H0 in H2; cycle 1.
    { apply (rwP dommP). eauto. }
    subst.
    rewrite -H3 in H4. apply H in H4; auto.
    apply (rwP dommP). rewrite H3 in H4. eauto.
  Qed.

  (** Page 3: Lemma 1.1. *)
  Lemma update_identity : forall X x, (1__X) ⦅x,x⦆ = 1__(X ∪ {x}).
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite unionmE mkfmapfE in_fsetU in_fset1 remmE rem_valmE /= setmE mkfmapfE.
    destruct (x0 =P x); subst.
    - rewrite orbT //.
    - destruct (x0 ∈ X) eqn:?; rewrite Heqb.
      + replace (x == id x0) with false; auto.
        symmetry. apply Bool.not_true_iff_false. intros_all.
        apply (rwP eqP) in H. auto.
      + rewrite emptymE //.
  Qed.

  (** Page 3: Lemma 1.2. *)
  Lemma update_converse :
    forall R x y,
      partial_bijection R ->
      R⦅x,y⦆ᵒ = R ᵒ⦅y,x⦆.
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite /converse /update !unionmE !remmE !rem_valmE /= !setmE.
    destruct (x0 =P y); subst.
    - apply getm_inv. rewrite invmK.
      + rewrite unionmE remmE rem_valmE setmE eq_refl //.
      + intros_all.
        epose proof @partial_bijection_update _ _ _ H. apply (rwP injectivemP) in H2. apply H2; eauto.
    - destruct (invm R x0) eqn:?; rewrite ?Heqo.
      + apply getm_inv in Heqo.
        destruct (x =P s); subst.
        * apply invm_None.
          { apply partial_bijection_update. auto. }
          rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros.
          rewrite unionmE remmE rem_valmE setmE.
          destruct (k' =P s); subst.
          -- apply Bool.negb_true_iff, Bool.not_true_iff_false. intros_all.
            apply (rwP eqP) in H0. inverts H0. auto.
          -- destruct (getm R k') eqn:?; rewrite ?Heqo0; auto.
            destruct (y =P s0); subst; auto.
            apply Bool.negb_true_iff, Bool.not_true_iff_false. intros_all.
            apply (rwP eqP) in H0. inverts H0.
            apply n0. apply (rwP injectivemP) in H. apply H.
            ++ apply (rwP dommP). eauto.
            ++ rewrite Heqo //.
        * apply getm_inv. rewrite invmK; cycle 1.
          { intros_all.
            epose proof @partial_bijection_update _ _ _ H. apply (rwP injectivemP) in H2. apply H2; eauto. }
          rewrite unionmE remmE rem_valmE setmE.
          replace (s == x) with false; cycle 1.
          { symmetry. apply Bool.not_true_iff_false. intros_all. apply (rwP eqP) in H0. subst. auto. }
          destruct (getm R s) eqn:?; rewrite ?Heqo0.
          -- destruct (y =P s0); subst; inverts Heqo; auto. exfalso. auto.
          -- rewrite Heqo // in Heqo0.
      + apply invm_None in Heqo; auto.
        apply invm_None.
        { apply partial_bijection_update. auto. }
        rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros.
        rewrite unionmE remmE rem_valmE setmE.
        destruct (k' =P x); subst.
        * apply Bool.negb_true_iff, Bool.not_true_iff_false. intros_all. apply (rwP eqP) in H0. inverts H0. auto.
        * destruct (getm R k') eqn:?; rewrite ?Heqo0 //.
          destruct (y =P s); subst; auto.
          rewrite <- (rwP (@codommPn _ _ R x0)) in Heqo.
          apply Bool.negb_true_iff, Bool.not_true_iff_false. intros_all.
          apply (rwP eqP) in H0. inverts H0. pose proof (Heqo k'). rewrite Heqo0 eq_refl // in H0.
  Qed.

  (** Page 3: Lemma 1.3. *)
  Lemma update_compose :
    forall R S x y z k v,
      getm (R⦅x,y⦆; S⦅y,z⦆) k = Some v ->
      getm (R; S)⦅x,z⦆ k = Some v.
  Proof.
    intros.
    rewrite unionmE remmE rem_valmE setmE.
    destruct (k =P x); subst.
    - rewrite eq_refl /=. f_equal.
      rewrite mkfmapfpE in H.
      destruct (x ∈ domm (R⦅x,y⦆)) eqn:?; rewrite Heqb // in H.
      apply (rwP dommP) in Heqb as []. rewrite H0 in H.
      rewrite !unionmE !remmE !rem_valmE !setmE !eq_refl /= in H, H0.
      destruct (x0 =P y); subst; inverts H; auto.
      inverts H0. contradiction.
    - apply (introF eqP) in n. rewrite n mkfmapfpE.
      rewrite mkfmapfpE in H.
      destruct (k ∈ domm (R⦅x,y⦆)) eqn:?; rewrite Heqb // in H.
      apply (rwP dommP) in Heqb as [].
      rewrite unionmE remmE rem_valmE setmE /= n in H, H0.
      destruct (getm R k) eqn:?; rewrite ?Heqo in H, H0; cycle 1.
      { inverts H0. }
      destruct (y =P s); subst; inverts H0.
      rewrite /= unionmE remmE rem_valmE setmE in H.
      apply not_eq_sym, (introF (@eqP 𝒱 _ _)) in n0. rewrite n0 in H.
      destruct (getm S x0) eqn:?; rewrite ?Heqo0 // in H.
      destruct (z =P s); subst; inverts H.
      assert (exists x0, getm R k = Some x0) by eauto. apply (rwP dommP) in H. rewrite H.
      apply (introF eqP) in n1. rewrite n1 //.
  Qed.

  Lemma α_equivalent'_supermap :
    forall (R__sub R__super : {fmap 𝒱 → 𝒱}) t u,
      (forall (k : 𝒱) v, getm R__sub k = Some v -> getm R__super k = Some v) ->
      t ≡_α^R__sub u ->
      t ≡_α^R__super u.
  Proof.
    intros.
    gen R__sub R__super u. induction t; intros;
    destruct u; inverts H0.
    - apply IHt with (R__super := R__super⦅s,s0⦆) in H2; cycle 1.
      { intros.
        rewrite unionmE remmE rem_valmE setmE /= in H0.
        rewrite unionmE remmE rem_valmE setmE /=.
        destruct (k =P s); subst; auto.
        destruct (getm R__sub k) eqn:?.
        + apply H in Heqo; rewrite Heqo.
          destruct (s0 =P s1); inverts H0. auto.
        + inverts H0. }
      rewrite /= H2 //.
    - apply (rwP andP) in H2 as [].
      apply IHt1 with (R__super := R__super) in H0; auto.
      apply IHt2 with (R__super := R__super) in H1; auto.
      rewrite /= H0 H1 //.
    - apply (rwP getmP), H in H2. apply (rwP getmP). auto.
  Qed.

  Lemma α_equivalent'_with_behaviorally_identical_maps :
    forall R S t u,
      (forall x y, R x y -> x ∈ FV t -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    intros.
    gen R S u. induction t; intros;
    destruct u; inverts H0.
    - apply IHt with (R := R⦅s,s0⦆); auto. intros_all.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in H0.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
      destruct (x =P s); subst; auto.
      destruct (getm R x) eqn:?; cycle 1.
      { inverts H0. }
      destruct (s0 =P s1); subst; inverts H0.
      apply H in Heqo.
      + rewrite Heqo. apply (introF eqP) in n0. rewrite n0 //.
      + simpl in *. rewrite /= in_fsetD in_fset1 H1 andbT. apply (introF eqP) in n. rewrite n //.
    - apply (rwP andP) in H2 as [].
      simpl. rewrite <- (rwP andP). split;
      simpl in *; (apply IHt1 with R + apply IHt2 with R); auto;
      intros;
      apply H; auto;
      rewrite /= in_fsetU H3 ?orbT //.
    - apply (rwP getmP), H in H2.
      + simpl in *. apply (rwP getmP). rewrite H2 //.
      + rewrite /= in_fset1 eq_refl //.
  Qed.

  (** Page 4: "We now define ≡α = ≡α^1X." *)
  Definition α_equivalent t u := t ≡_α^(1__(FV t)) u.

  Infix "≡_α" := α_equivalent (at level 40).

  Notation "t '≢_α' u" := (~~ (t ≡_α u)) (at level 40).

  (** We will use these notations when the assumptions make it impossible for a substitution to fail, but Coq can't figure that out (without a lot of dependent-type boilerplate, which we want to avoid for clarity). *)
  (* We will use [#[program]] to discover the wildcard variables, since their values don't actually matter. *)
  #[local] Notation "a '`≡_α' b" :=
    (odflt (variable _) a ≡_α odflt (variable _) b) (at level 40).

  #[local] Notation "a '`≡_α^' R b" :=
    (odflt (variable _) a ≡_α^R odflt (variable _) b) (at level 40, R at level 0).

  (** Page 4: Proposition 2.1. *)
  Proposition α_equivalent'_identity :
    forall X t,
      t ∈ Tm X ->
      t ≡_α^(1__X) t.
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    gen X. induction t; intros; simpl.
    - rewrite update_identity.
      apply IHt. simpl. intros_all.
      rewrite in_fsetU in_fset1 orbC.
      destruct (x =P s); subst; auto.
      apply (introF eqP) in n.
      apply H. rewrite /= in_fsetD in_fset1 n H0 //.
    - rewrite <- (rwP andP). split;
      apply α_equivalent'_supermap with (R__sub := 1__X); auto; intros;
      (apply IHt1 || apply IHt2); simpl; intros_all;
      apply H; rewrite /= in_fsetU H0 ?orbT //.
    - assert (s ∈ fset1 s). { rewrite in_fset1 eq_refl //. }
      apply H in H0. simpl in *.
      apply (rwP getmP). rewrite mkfmapfE H0 //.
  Qed.

  (** Page 4: Proposition 2.2. *)
  Proposition α_equivalent'_converse :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      u ≡_α^(R ᵒ) t.
  Proof.
    intros.
    gen R u. induction t; intros;
    destruct u; inverts H0.
    - apply IHt in H2.
      + rewrite /= -update_converse //.
      + apply partial_bijection_update. auto.
    - apply (rwP andP) in H2 as [].
      apply IHt1 in H0; auto. apply IHt2 in H1; auto.
      rewrite /= H0 H1 //.
    - apply (rwP getmP) in H2.
      apply (rwP getmP), getm_inv. rewrite invmK //.
      apply (rwP injectivemP). auto.
  Qed.

  (** Page 4: Proposition 2.3. *)
  Proposition α_equivalent'_compose :
    forall R S t u (v : term),
      t ≡_α^R u ->
      u ≡_α^S v ->
      t ≡_α^(R;S) v.
  Proof.
    intros.
    gen u v R S. induction t; intros;
    destruct u, v; inverts H; inverts H0.
    - apply IHt with (S := S⦅s0,s1⦆) (v := v) in H2; auto.
      apply α_equivalent'_supermap with (R__super := (R;S)⦅s,s1⦆) in H2; cycle 1.
      { intros. eapply update_compose; eauto. }
      rewrite /= H2 //.
    - apply (rwP andP) in H1 as [], H2 as [].
      apply IHt1 with (R := R) (S := S) (v := v1) in H1; auto.
      apply IHt2 with (R := R) (S := S) (v := v2) in H2; auto.
      rewrite /= H1 H2 //.
    - apply (rwP getmP) in H1, H2.
      apply (rwP getmP). rewrite /= mkfmapfpE.
      assert (exists s0, getm R s = Some s0) by eauto. apply (rwP dommP) in H. rewrite H H2 //.
  Qed.

  Lemma α_equivalent'_maps_all_FV :
    forall R t u x,
      t ≡_α^R u ->
      x ∈ FV t ->
      exists y, getm R x = Some y /\ y ∈ FV u.
  Proof.
    intros.
    gen R u. induction t; intros_all;
    destruct u; inverts H.
    - rewrite /= in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
      pose proof H2. apply IHt in H2 as (? & ? & ?); auto.
      rewrite unionmE remmE rem_valmE setmE /= in H2.
      destruct (x =P s); subst; auto.
      destruct (getm R x) eqn:?; cycle 1.
      { inverts H2. }
      destruct (s0 =P s1); subst; inverts H2.
      exists x0. split; auto. simpl in *. rewrite /= in_fsetD in_fset1 H3 //.
      apply not_eq_sym, (introF eqP) in n0. rewrite n0 //.
    - apply (rwP andP) in H2 as [].
      rewrite /= in_fsetU in H0. apply (rwP orP) in H0 as [].
      + apply IHt1 with (u := u1) in H as (? & ? & ?); auto.
        exists x0. simpl in *. rewrite in_fsetU H2 //.
      + apply IHt2 with (u := u2) in H1 as (? & ? & ?); auto.
        exists x0. simpl in *. rewrite in_fsetU H2 orbT //.
    - apply (rwP getmP) in H2.
      rewrite /= in_fset1 in H0. apply (rwP eqP) in H0. subst.
      exists s0. rewrite /= in_fset1 eq_refl //.
  Qed.

  Lemma α_equivalent'_maps_all_FV' :
    forall R t u y,
      partial_bijection R ->
      t ≡_α^R u ->
      y ∈ FV u ->
      exists x, getm R x = Some y /\ x ∈ FV t.
  Proof.
    intros.
    apply α_equivalent'_converse in H0; auto.
    pose proof α_equivalent'_maps_all_FV _ _ _ _ H0 H1 as (? & ? & ?).
    apply getm_inv in H2. eauto.
  Qed.

  Lemma α_equivalent'_implies_related_FV :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      FV u = pimfset (getm R) (FV t).
  Proof.
    intros.
    apply eq_fset. intros_all.
    rewrite in_pimfset.
    symmetry.
    destruct (x ∈ FV u) eqn:?.
    - eapply α_equivalent'_maps_all_FV' in Heqb as (? & ? & ?); eauto.
      apply (rwP imfsetP). simpl in *. eauto.
    - apply Bool.not_true_iff_false. intros_all.
      apply (rwP imfsetP) in H1 as [].
      eapply α_equivalent'_maps_all_FV in H1 as (? & ? & ?); eauto.
      rewrite H1 in H2. inverts H2.
      simpl in *. rewrite H3 // in Heqb.
  Qed.

  Lemma α_equivalent'_bijection_includes_all_FV :
    forall R t u,
      t ≡_α^R u ->
      t ∈ Tm (domm R).
  Proof.
    intros.
    rewrite /Tm /in_mem /=. apply (rwP fsubsetP).
    gen R u. induction t; intros_all;
    destruct u; inverts H.
    - rewrite /= in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
      cut (x ∈ domm R⦅s,s0⦆ = true).
      { intros.
        simpl in *. apply (rwP dommP) in H1 as [].
        rewrite unionmE remmE rem_valmE setmE /= in H1.
        destruct (x =P s); subst; auto.
        destruct (getm R x) eqn:?.
        - eapply (rwP dommP). eauto.
        - inverts H1. }
      eapply IHt; eauto.
    - apply (rwP andP) in H2 as [].
      rewrite /= /in_mem /= in_fsetU in H0. apply (rwP orP) in H0 as [].
      apply IHt1 in H; auto. apply IHt2 in H1; auto.
    - apply (rwP getmP) in H2.
      simpl in *. rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst.
      apply (rwP dommP). eauto.
  Qed.

  Lemma α_equivalent'_bijection_includes_all_FV' :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      u ∈ Tm (codomm R).
  Proof.
    intros.
    eapply α_equivalent'_converse in H0; eauto.
    rewrite codomm_domm_invm //.
    eapply α_equivalent'_bijection_includes_all_FV; eauto.
  Qed.

  Lemma α_equivalent_implies_same_FV :
    forall t u,
      t ≡_α u ->
      FV u = FV t.
  Proof.
    intros.
    replace (FV t) with (pimfset (getm (1__(FV t) : {fmap 𝒱 → 𝒱})) (FV t)); cycle 1.
    { apply eq_fset. intros_all.
      rewrite in_pimfset.
      destruct (x ∈ FV t) eqn:?.
      - apply (rwP imfsetP).
        exists x; auto.
        rewrite mkfmapfE Heqb //.
      - apply negbTE, (introN imfsetP). intros [].
        rewrite mkfmapfE in H1.
        rewrite H0 in H1. inverts H1. rewrite H0 // in Heqb. }
    eapply α_equivalent'_implies_related_FV; eauto.
    apply partial_bijection_identity.
  Qed.

  Lemma domm_identity : forall X, domm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    intros.
    apply eq_fset. intros_all.
    destruct (x ∈ X) eqn:?.
    - apply (rwP dommP). exists x. rewrite mkfmapfE Heqb //.
    - apply negbTE. rewrite <- (rwP dommPn).
      rewrite mkfmapfE. rewrite Heqb //.
  Qed.

  Lemma α_equivalent'_implies_α_equivalent :
    forall t u,
      t ≡_α u <-> exists X, t ≡_α^(1__X) u.
  Proof.
    intros.
    split; intros; eauto.
    inverts H.
    apply α_equivalent'_with_behaviorally_identical_maps with (R := 1__x); auto.
    simpl. intros.
    rewrite /fmap_to_Prop mkfmapfE in H.
    rewrite /fmap_to_Prop mkfmapfE H1.
    eapply α_equivalent'_bijection_includes_all_FV in H0; eauto.
    rewrite domm_identity /= in H0. apply (rwP fsubsetP) in H0. apply H0 in H1. rewrite H1 // in H.
  Qed.

  Lemma compose_identity_right : forall R, R; (1__(codomm R)) = R.
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite mkfmapfpE.
    destruct (x ∈ domm R) eqn:?; rewrite Heqb.
    - apply (rwP dommP) in Heqb as []. rewrite H mkfmapfE.
      destruct (x0 ∈ codomm R) eqn:?; rewrite Heqb //.
      apply negbT in Heqb.
      rewrite <- (rwP (@codommPn _ 𝒱 _ _)) in Heqb.
      pose proof Heqb x. rewrite H eq_refl // in H0.
    - apply negbT, (rwP dommPn) in Heqb. auto.
  Qed.

  Lemma compose_identity_left : forall R, (1__(domm R)); R = R.
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite mkfmapfpE mkfmapfE domm_mkfmapf in_fset.
    destruct (x ∈ domm R) eqn:?; rewrite Heqb //.
    apply negbT, (rwP dommPn) in Heqb. auto.
  Qed.

  Lemma codomm_identity : forall X, codomm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    intros.
    apply eq_fset. intros_all.
    destruct (x ∈ X) eqn:?.
    - apply (rwP codommP). exists x. rewrite mkfmapfE Heqb //.
    - apply negbTE. rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros_all.
      apply (introN eqP). intros_all.
      rewrite mkfmapfE in H.
      destruct (k' ∈ X) eqn:?; rewrite Heqb0 in H; inverts H.
      rewrite Heqb0 // in Heqb.
  Qed.

  Lemma compose_identity :
    forall X Y,
      (1__X); (1__Y) = 1__(X ∩ Y).
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite mkfmapfpE !mkfmapfE in_fsetI.
    destruct (x ∈ X) eqn:?; rewrite Heqb;
    rewrite domm_identity Heqb // mkfmapfE.
    destruct (x ∈ Y) eqn:?; rewrite Heqb0 //.
  Qed.

  Lemma compose_identity' : forall X, (1__X); (1__X) = 1__X.
  Proof.
    intros.
    pose proof codomm_identity X.
    pose proof compose_identity_right (1__X). rewrite H // in H0.
  Qed.

  Lemma converse_identity : forall X, (1__X)ᵒ = 1__X.
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite mkfmapfE.
    destruct (x ∈ X) eqn:?; rewrite Heqb.
    - apply getm_inv. rewrite invmK.
      + rewrite mkfmapfE Heqb //.
      + apply (rwP injectivemP). apply partial_bijection_identity.
    - apply invm_None.
      + apply partial_bijection_identity.
      + rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros_all.
        apply (introN eqP). intros_all.
        rewrite mkfmapfE in H.
        destruct (k' ∈ X) eqn:?; rewrite Heqb0 in H; inverts H.
        rewrite Heqb0 // in Heqb.
  Qed.

  (** Page 4: "≡α is... reflexive." *)
  Corollary α_equivalent_reflexive : forall t, t ≡_α t.
  Proof.
    intros. apply α_equivalent'_identity. rewrite /Tm /in_mem /= fsubsetxx //.
  Qed.

  (** Page 4: "≡α is... transitive." *)
  Corollary α_equivalent_transitive :
    forall t u (v : term),
      t ≡_α u ->
      u ≡_α v ->
      t ≡_α v.
  Proof.
    intros.
    pose proof α_equivalent'_compose _ _ _ _ _ H H0.
    rewrite compose_identity in H1.
    apply α_equivalent'_supermap with (R__sub := 1__(FV t ∩ FV u)); auto.
    intros.
    rewrite mkfmapfE in_fsetI in H2.
    rewrite mkfmapfE.
    destruct (k ∈ FV t) eqn:?; rewrite Heqb //.
    destruct (k ∈ FV u) eqn:?; inverts H2. auto.
  Qed.

  (** Page 4: "≡α is... symmetric." *)
  Corollary α_equivalent_symmetric :
    forall t u,
      t ≡_α u ->
      u ≡_α t.
  Proof.
    intros.
    apply α_equivalent'_converse in H.
    - rewrite converse_identity in H.
      unfold α_equivalent.
      eapply α_equivalent'_implies_α_equivalent; eauto.
    - apply partial_bijection_identity.
  Qed.

  (** Page 4: Corollary 3. *)
  #[global] Instance α_equivalent_Equivalence : Equivalence α_equivalent.
  Proof.
    split; intros_all.
    - apply α_equivalent_reflexive.
    - apply α_equivalent_symmetric. auto.
    - eapply α_equivalent_transitive; eauto.
  Qed.

  (** Since Coq doesn't directly support quotient types, we're representing "Tm^α(X)" as "Tm(X)" and manually proving that functions respect "≡α". *)

  Implicit Types f g : {fmap 𝒱 → term}.

  (** Page 4: "Given a substitution f and x ∈ 𝒱, t ∈ Tm(Y) we define the update...." *)
  Definition update_substitution (A : Type) : {fmap 𝒱 → A} -> 𝒱 -> A -> {fmap 𝒱 → A} := @setm _ _.

  #[local] Notation "f '[' x ',' t ']'" := (update_substitution f x t) (at level 10, x at next level, t at next level).

  Definition codomm_Tm_set f : {fset 𝒱} := ⋃_(i ∈ codomm f) (FV i).

  Lemma codomm_Tm_setP :
    forall {f} {x},
      reflect (exists t, x ∈ FV t /\ t ∈ codomm f) (x ∈ codomm_Tm_set f).
  Proof.
    intros.
    destruct (x ∈ codomm_Tm_set f) eqn:?; constructor;
    rewrite /= /codomm_Tm_set in_bigcup in Heqb.
    - apply (rwP hasP) in Heqb as []. exists x0. auto.
    - apply negbT, (rwP hasPn) in Heqb. intros (? & ? & ?).
      apply Heqb in H0. simpl in *. rewrite H // in H0.
  Qed.

  #[local] Reserved Notation "'⦇' f '⦈'".

  (** Page 4: "A substitution can be extended to a function on terms ⦇f⦈ ∈ Tm(X) ⟶ Tm(Y)...." *)
  Fixpoint lift_substitution f t : term :=
    match t with
    | variable x => odflt t (getm f x)
    | application t u => application (⦇f⦈ t) (⦇f⦈ u)
    | abstraction x t =>
      let Y := codomm_Tm_set f in
      let z := Fresh Y in
      abstraction z (⦇f[x,variable z]⦈ t)
    end

  where "'⦇' f '⦈'" := (lift_substitution f).

  #[global] Instance lift_substitution_Identity : Identity ({fmap 𝒱 → term} -> term -> term) :=
    { identity' _ (f : {fmap 𝒱 → term}) := ⦇f⦈ }.

  Lemma α_equivalent_update :
    forall R t u x y,
      x ∉ domm R ->
      y ∉ codomm R ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    intros.
    apply α_equivalent'_supermap with (R__sub := R); auto. intros.
    apply (rwP dommPn) in H.
    destruct (k =P x); subst.
    { rewrite H // in H2. }
    rewrite <- (rwP (@codommPn _ _ R y)) in H0.
    destruct (y =P v); subst.
    { pose proof H0 k. rewrite H2 eq_refl // in H3. }
    apply (introF eqP) in n, n0.
    rewrite unionmE remmE rem_valmE setmE n H2 n0 //.
  Qed.

  Lemma α_equivalent_update_reorder :
    forall R t u x y z z',
      z ∉ domm R ->
      z' ∉ codomm R ->
      t ≡_α^(R⦅x,y⦆) u ->
      t ≡_α^(R⦅z,z'⦆⦅x,y⦆) u.
  Proof.
    intros.
    apply α_equivalent'_supermap with (R__sub := R⦅x,y⦆); auto. intros.
    rewrite unionmE remmE rem_valmE setmE /= in H2.
    repeat rewrite unionmE remmE rem_valmE setmE /=.
    destruct (k =P x); subst; auto.
    destruct (k =P z); subst.
    - destruct (getm R z) eqn:?; cycle 1.
      { inverts H2. }
      destruct (y =P s); subst; inverts H2.
      assert (z ∈ domm R) by (apply (rwP dommP); eauto). rewrite H2 // in H.
    - destruct (getm R k) eqn:?; cycle 1.
      { inverts H2. }
      destruct (y =P s); subst; inverts H2.
      destruct (z' =P v); subst.
      { assert (v ∈ codomm R) by (apply (rwP codommP); eauto). rewrite H2 // in H0. }
      apply (introF eqP) in n1. rewrite /= n1 //.
  Qed.

  Lemma in_update :
    forall R x y z z',
      z ∉ domm R ->
      z' ∉ codomm R ->
      (x, y) ∈ R ->
      (x, y) ∈ R⦅z,z'⦆.
  Proof.
    intros.
    simpl in *.
    apply (rwP getmP) in H1.
    apply (rwP getmP).
    rewrite /update unionmE remmE rem_valmE setmE /= H1.
    destruct (x =P z); subst.
    { assert (z ∈ domm R) by (apply (rwP dommP); eauto). rewrite H2 // in H. }
    destruct (z' =P y); subst; auto.
    assert (y ∈ codomm R) by (apply (rwP codommP); eauto). rewrite H2 // in H0.
  Qed.

  Lemma update_repeat_noop :
    forall R x y,
      R⦅x,y⦆⦅x,y⦆ = R⦅x,y⦆.
  Proof.
    intros.
    apply eq_fmap. intros_all.
    repeat rewrite !unionmE !remmE !rem_valmE !setmE /=.
    destruct (x0 =P x); subst; auto.
    destruct (getm R x0) eqn:?; auto.
    destruct (y =P s); subst; auto.
    apply (introF eqP) in n0. rewrite /= n0 //.
  Qed.

  Lemma codomm_Tm_setPn :
    forall {f} {x},
      reflect (forall t, ~ (x ∈ FV t /\ t ∈ codomm f)) (x ∉ codomm_Tm_set f).
  Proof.
    intros.
    destruct (x ∉ codomm_Tm_set f) eqn:?;
    rewrite /= /codomm_Tm_set in_bigcup in Heqb;
    constructor; intros_all.
    - destruct H.
      apply negbTE, Bool.not_true_iff_false in Heqb. apply Heqb.
      apply (rwP hasP). exists t; auto.
    - apply Bool.negb_false_iff, (rwP hasP) in Heqb as [].
      apply H with x0. auto.
  Qed.

  Lemma α_equivalent'_with_behaviorally_identical_maps' :
    forall R S t u,
      (forall x y, R x y -> x ∈ FV t -> y ∈ FV u -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    intros.
    gen R S u. induction t; intros;
    destruct u; inverts H0.
    - apply IHt with (R := R⦅s,s0⦆); auto. intros_all.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in H0.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
      destruct (x =P s); subst; auto.
      destruct (getm R x) eqn:?; cycle 1.
      { inverts H0. }
      destruct (s0 =P s1); subst; inverts H0.
      apply H in Heqo.
      + rewrite Heqo. apply (introF eqP) in n0. rewrite n0 //.
      + simpl in *. rewrite /= in_fsetD in_fset1 H1 andbT. apply (introF eqP) in n. rewrite n //.
      + simpl in *. rewrite in_fsetD in_fset1 H3 andbT. apply not_eq_sym, (introF eqP) in n0. rewrite n0 //.
    - apply (rwP andP) in H2 as [].
      simpl. rewrite <- (rwP andP). split;
      simpl in *; (apply IHt1 with R + apply IHt2 with R); auto;
      intros;
      apply H; auto;
      rewrite /= in_fsetU ?H3 ?H4 ?orbT //.
    - apply (rwP getmP), H in H2.
      + simpl in *. apply (rwP getmP). rewrite H2 //.
      + rewrite /= in_fset1 eq_refl //.
      + rewrite /= in_fset1 eq_refl //.
  Qed.

  (** Page 5: Lemma 5. *)
  #[program] Lemma lemma5 :
    forall R S f g,
      R ⊆ domm f × domm g ->
      partial_bijection R ->
      partial_bijection S ->
      (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
      forall x y z z',
        z ∉ codomm_Tm_set f ->
        z' ∉ codomm_Tm_set g ->
        forall w w' : 𝒱, R⦅x,y⦆ w w' -> getm (f[x,variable z]) w `≡_α^(S⦅z,z'⦆) getm (g[y,variable z']) w'.
  Proof.
    intros.
    rewrite /fmap_to_Prop /update unionmE remmE rem_valmE setmE /= in H5.
    rewrite /update_substitution /update !setmE.
    destruct (w =P x); subst.
    - inverts H5.
      rewrite !eq_refl.
      apply (rwP getmP).
      rewrite /= unionmE remmE rem_valmE eq_refl setmE eq_refl //.
    - destruct (getm R w) eqn:?; cycle 1.
      { inverts H5. }
      destruct (y =P s); subst; inverts H5.
      apply not_eq_sym, (introF eqP) in n0. rewrite n0.
      pose proof Heqo. apply H2 in Heqo. inverts Heqo.
      apply H, (rwP andP) in H5 as [].
      simpl in *. apply (rwP dommP) in H5 as [], H6 as [].
      rewrite -> H5, H6 in *. simpl in *.
      apply α_equivalent'_with_behaviorally_identical_maps' with (R := S); auto. intros.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
      destruct (x2 =P z); subst.
      { rewrite <- (rwP codomm_Tm_setPn) in H3.
        exfalso. apply H3 with x0. split; auto.
        simpl. apply (rwP codommP). eauto. }
      rewrite H8.
      destruct (z' =P y0); subst; auto.
      rewrite <- (rwP codomm_Tm_setPn) in H4.
      exfalso. apply H4 with x1. split; auto.
      simpl. apply (rwP codommP). eauto.
  Qed.

  Lemma subset_domm_substitution :
    forall f x t,
      fsubset (domm f) (domm (f[x,t])).
  Proof.
    intros.
    apply (rwP fsubsetP). intros_all.
    apply (rwP dommP) in H as [].
    apply (rwP dommP).
    rewrite setmE.
    destruct (x0 =P x); subst; eauto.
  Qed.

  (** Page 4: Proposition 4. *)
  #[program] Proposition substitution_preserves_α_congruence' :
    forall R S f g,
      R ⊆ domm f × domm g ->
      partial_bijection R ->
      partial_bijection S ->
      (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
      forall t u, t ≡_α^R u -> ⦇f⦈ t ≡_α^S ⦇g⦈ u.
  Proof.
    intros.
    gen R S f g u. induction t; intros;
    destruct u; inverts H3.
    - eapply IHt with (R := R⦅s,s0⦆); eauto.
      + apply partial_bijection_update. auto.
      + apply partial_bijection_update. auto.
      + rewrite !domm_set /=. intros_all.
        rewrite /= !in_fsetU !in_fset1.
        rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in H3.
        destruct (x =P s); subst.
        { inverts H3. rewrite eq_refl //. }
        destruct (getm R x) eqn:?; cycle 1.
        { inverts H3. }
        destruct (s0 =P s1); subst; inverts H3.
        apply H, (rwP andP) in Heqo as []. simpl in *. rewrite H3 H4 orbT //.
      + intros. eapply lemma5; eauto; apply Fresh_correct.
    - apply (rwP andP) in H5 as [].
      eapply IHt1 with (S := S) in H3; eauto.
      eapply IHt2 with (S := S) in H4; eauto.
      rewrite /= H3 H4 //.
    - apply (rwP getmP) in H5. simpl in *.
      pose proof H5. apply H2 in H3.
      apply H, (rwP andP) in H5 as [].
      simpl in *. apply (rwP dommP) in H4 as [], H5 as [].
      rewrite -> H4, H5 in *. auto.
  Qed.

  #[program] Corollary substitution_preserves_α_congruence_identity :
    forall f g,
      (forall x, x ∈ domm f ∩ domm g -> getm f x `≡_α^(1__(codomm_Tm_set f ∩ codomm_Tm_set g)) getm g x) ->
      forall t u, t ≡_α^(1__(domm f ∩ domm g)) u -> ⦇f⦈ t ≡_α^(1__(codomm_Tm_set f ∩ codomm_Tm_set g)) ⦇g⦈ u.
  Proof.
    intros.
    eapply substitution_preserves_α_congruence'; eauto;
    try apply partial_bijection_identity.
    - simpl. intros_all.
      rewrite /fmap_to_Prop mkfmapfE in_fsetI in H1.
      destruct (x ∈ domm f) eqn:?; inverts H1.
      destruct (x ∈ domm g) eqn:?; inverts H3.
      rewrite /= Heqb0 //.
    - intros.
      rewrite /= /identity /fmap_to_Prop mkfmapfE in_fsetI in H1.
      destruct (x ∈ domm f) eqn:?; inverts H1.
      destruct (x ∈ domm g) eqn:?; inverts H3.
      apply H. rewrite /= in_fsetI Heqb Heqb0 //.
  Qed.

  (** Page 5: "Clearly, the preservation property arises as a special case by setting R = 1X and S = 1Y." *)
  #[program] Theorem substitution_preserves_α_congruence :
    forall f g,
      (forall x, x ∈ domm f ∩ domm g -> getm f x `≡_α getm g x) ->
      forall t u, t ∈ Tm (domm f ∩ domm g) -> t ≡_α u -> ⦇f⦈ t ≡_α ⦇g⦈ u.
  Proof.
    intros.
    eapply α_equivalent'_implies_α_equivalent. exists (codomm_Tm_set f ∩ codomm_Tm_set g).
    apply substitution_preserves_α_congruence_identity.
    - simpl. intros.
      rewrite in_fsetI in H2. apply (rwP andP) in H2 as [].
      assert (x ∈ domm f ∩ domm g). { rewrite in_fsetI H2 H3 //. }
      apply H in H4.
      apply (rwP dommP) in H2 as [], H3 as [].
      rewrite H2 H3 /=. rewrite H2 H3 /= in H4.
      apply α_equivalent'_supermap with (R__sub := 1__(FV x0)); auto.
      intros.
      rewrite mkfmapfE in H5.
      destruct (k ∈ FV x0) eqn:?; rewrite Heqb in H5; inverts H5.
      rewrite mkfmapfE in_fsetI.
      assert (v ∈ codomm_Tm_set f).
      { apply (rwP codomm_Tm_setP). exists x0. split; auto.
        simpl. apply (rwP codommP). eauto. }
      assert (v ∈ codomm_Tm_set g).
      { apply (rwP codomm_Tm_setP). exists x1.
        apply α_equivalent_implies_same_FV in H4.
        rewrite H4. split; auto.
        simpl. apply (rwP codommP). eauto. }
      rewrite H5 H6 //.
    - apply α_equivalent'_supermap with (R__sub := 1__(FV t)); auto.
      intros.
      rewrite mkfmapfE in H2.
      destruct (k ∈ FV t) eqn:?; rewrite Heqb in H2; inverts H2.
      simpl in *. apply (rwP fsubsetP) in H0. apply H0 in Heqb. rewrite mkfmapfE Heqb //.
  Qed.

  (** Page 5: "A consequence of proposition 4 is that substitution is an operation on α-equivalence classes." *)
  Theorem substitution_respects_α_equivalence :
    forall f t u,
      t ∈ Tm (domm f) ->
      t ≡_α u ->
      ⦇f⦈ t ≡_α ⦇f⦈ u.
  Proof.
    intros.
    eapply substitution_preserves_α_congruence; eauto.
    - reflexivity.
    - rewrite fsetIid //.
  Qed.

  Lemma codomm_Tm_set_mapm_variable :
    forall R,
      codomm_Tm_set (mapm variable R) = codomm R.
  Proof.
    intros.
    apply eq_fset. intros_all.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H0 as [].
      rewrite mapmE in H0.
      destruct (getm R x1) eqn:?; inverts H0.
      rewrite in_fset1 in H. apply (rwP eqP) in H. subst.
      apply (rwP codommP). eauto.
    - apply (rwP codommP) in H as [].
      apply (rwP codomm_Tm_setP). exists (variable x). simpl. split.
      + rewrite in_fset1 eq_refl //.
      + apply (rwP codommP). exists x0. rewrite mapmE H //.
  Qed.

  (** Page 6: Lemma 7. *)
  Lemma lemma7 :
    forall (f : {fmap 𝒱 → 𝒱}) t,
      partial_bijection f ->
      t ∈ Tm (domm f) ->
      ⦇mapm variable f⦈ t ≡_α^(f ᵒ) t.
  Proof.
    intros.
    apply (rwP fsubsetP) in H0.
    gen f. induction t; intros; simpl in *.
    - rewrite /= /update_substitution -mapm_setm -/update_substitution -update_converse //.
      rewrite codomm_Tm_set_mapm_variable.
      replace (setm f s (Fresh (codomm f))) with (f⦅s,Fresh (codomm f)⦆); cycle 1.
      { apply eq_fmap. intros_all.
        rewrite unionmE remmE rem_valmE !setmE /=.
        destruct (x =P s); subst; auto.
        destruct (getm f x) eqn:?; auto.
        destruct (Fresh (codomm f) =P s0); subst; auto.
        assert (Fresh (codomm f) ∈ codomm f). { apply (rwP codommP). eauto. }
        pose proof Fresh_correct (codomm f). rewrite H1 // in H2. }
      apply IHt; auto.
      + apply partial_bijection_update. auto.
      + intros_all.
        apply (rwP dommP).
        rewrite unionmE remmE rem_valmE setmE /=.
        destruct (x =P s); subst; simpl; eauto.
        assert (x ∈ FV t :\ s).
        { apply (introF eqP) in n. rewrite in_fsetD in_fset1 n H1 //. }
        apply H0, (rwP dommP) in H2 as []. rewrite H2 /=.
        destruct (Fresh (codomm f) =P x0); subst; simpl; eauto.
        assert (Fresh (codomm f) ∈ codomm f). { apply (rwP codommP). eauto. }
        pose proof Fresh_correct (codomm f). rewrite H3 // in H4.
    - rewrite <- (rwP andP). split.
      + apply IHt1; auto. intros_all.
        apply H0. rewrite in_fsetU H1 //.
      + apply IHt2; auto. intros_all.
        apply H0. rewrite in_fsetU H1 orbT //.
    - apply α_equivalent'_converse; auto.
      rewrite /= mapmE.
      assert (s ∈ fset1 s). { rewrite in_fset1 eq_refl //. }
      apply H0, (rwP dommP) in H1 as [].
      rewrite H1 /=. apply (rwP getmP). auto.
  Qed.

  (** Page 6: "η(x) = x." *)
  Definition η__ X : {fmap 𝒱 → term} := 1__X.

  (** Page 6: "ηX ∈ X ⟶ Tm^α(X)." *)
  Lemma η_type :
    forall X,
      codomm_Tm_set (η__ X) = domm (η__ X).
  Proof.
    intros_all.
    apply eq_fset. intros_all.
    rewrite domm_map domm_mkfmapf in_fset.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H0 as [].
      rewrite mapmE mkfmapfE in H0.
      destruct (x1 ∈ X) eqn:?; rewrite Heqb in H0; inverts H0.
      rewrite in_fset1 in H. apply (rwP eqP) in H. subst. auto.
    - apply (rwP codomm_Tm_setP). exists (variable x). split.
      { rewrite /= in_fset1 eq_refl //. }
      simpl. apply (rwP codommP). exists x.
      rewrite mapmE mkfmapfE H //.
  Qed.

  Lemma update_substitution_overwrite :
    forall f x y y',
      f[x,variable y][x,variable y'] = f[x, variable y'].
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite !setmE.
    destruct (x0 =P x); subst; auto.
  Qed.

  Lemma update_substitution_reorder :
    forall f x x' y y',
      x <> x' ->
      f[x,variable y][x',variable y'] = f[x',variable y'][x,variable y].
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite !setmE.
    destruct (x0 =P x); subst; auto.
    apply (introF eqP) in H. rewrite H //.
  Qed.

  Lemma α_equivalent_update' :
    forall R t u x y,
      x ∉ FV t ->
      y ∉ FV u ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    intros.
    apply α_equivalent'_with_behaviorally_identical_maps' with (R := R); auto. intros.
    rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE.
    simpl in *.
    destruct (x0 =P x); subst.
    { rewrite H3 // in H. }
    rewrite H2.
    destruct (y =P y0); subst; auto.
    rewrite H4 // in H0.
  Qed.

  Lemma domm_update_substitution :
    forall f x t,
      domm (f[x,t]) = domm f ∪ {x}.
  Proof.
    intros.
    apply eq_fset. intros_all.
    rewrite in_fsetU in_fset1.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP dommP) in H as [].
      rewrite setmE in H.
      destruct (x0 =P x); subst.
      { apply orbT. }
      rewrite orbF.
      apply (rwP dommP). eauto.
    - apply (rwP dommP).
      rewrite setmE.
      apply (rwP orP) in H as [].
      + apply (rwP dommP) in H as [].
        destruct (x0 =P x); subst; eauto.
      + rewrite H. eauto.
  Qed.

  Lemma FV_lift_substitution :
    forall f t,
      t ∈ Tm (domm f) ->
      FV (⦇f⦈ t) = ⋃_(u ∈ pimfset (getm f) (FV t)) (FV u).
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    apply eq_fset. intros_all.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true.
    split; intros.
    - apply (rwP hasP).
      gen f. induction t; intros; simpl in *.
      + rewrite in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
        apply IHt in H1 as [].
        * apply (rwP pimfsetP) in H1 as [].
          rewrite setmE in H3.
          destruct (x1 =P s); subst.
          { inverts H3. rewrite in_fset1 in H2. rewrite H2 // in H0. }
          exists x0; auto.
          apply (rwP pimfsetP). exists x1; auto.
          apply (introF eqP) in n.
          rewrite in_fsetD in_fset1 n H1 //.
        * intros_all.
          rewrite domm_update_substitution in_fsetU in_fset1 orbC.
          destruct (x0 =P s); subst; auto.
          apply (introF eqP) in n.
          apply H. rewrite in_fsetD in_fset1 n H2 //.
      + rewrite in_fsetU in H0. apply (rwP orP) in H0 as [].
        * apply IHt1 in H0 as []; cycle 1.
          { intros_all. apply H. rewrite in_fsetU H1 //. }
          apply (rwP pimfsetP) in H0 as [].
          exists x0; auto.
          apply (rwP pimfsetP). exists x1; auto.
          rewrite in_fsetU H0 //.
        * apply IHt2 in H0 as []; cycle 1.
          { intros_all. apply H. rewrite in_fsetU H1 orbT //. }
          apply (rwP pimfsetP) in H0 as [].
          exists x0; auto.
          apply (rwP pimfsetP). exists x1; auto.
          rewrite in_fsetU H0 orbT //.
      + assert (s ∈ fset1 s). { rewrite in_fset1 eq_refl //. }
        apply H, (rwP dommP) in H1 as [].
        exists x0.
        * apply (rwP (@pimfsetP _ _ (getm f) (fset1 s) x0)). exists s; auto.
          rewrite in_fset1 eq_refl //.
        * rewrite H1 // in H0.
    - apply (rwP hasP) in H0 as [].
      apply (rwP pimfsetP) in H0 as [].
      gen f. induction t; intros; simpl in *.
      + rewrite in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
        rewrite in_fsetD in_fset1.
        assert (x ∈ codomm_Tm_set f).
        { apply (rwP codomm_Tm_setP). exists x0. split; auto. simpl. apply (rwP codommP). eauto. }
        pose proof Fresh_correct (codomm_Tm_set f).
        destruct (x =P Fresh (codomm_Tm_set f)); subst.
        { rewrite H4 // in H5. }
        apply IHt; auto.
        * intros_all.
          rewrite domm_set in_fsetU in_fset1.
          destruct (x2 =P s); subst; auto.
          apply (introF eqP) in n0.
          apply H.
          rewrite in_fsetD in_fset1 n0 H6 //.
        * apply negbTE in H0. rewrite setmE H0 //.
      + rewrite in_fsetU.
        rewrite in_fsetU in H0.
        apply (rwP orP) in H0 as [].
        * eapply IHt1 in H0; eauto.
          -- rewrite H0 //.
          -- intros_all. apply H. rewrite in_fsetU H3 //.
        * eapply IHt2 in H0; eauto.
          -- rewrite H0 orbT //.
          -- intros_all. apply H. rewrite in_fsetU H3 orbT //.
      + rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst.
        rewrite H2 //.
  Qed.

  (** Page 4: "⦇f⦈ ∈ Tm(X) ⟶ Tm(Y)." *)
  Lemma lift_substitution_type :
    forall f t,
      t ∈ Tm (domm f) ->
      ⦇f⦈ t ∈ Tm (codomm_Tm_set f).
  Proof.
    intros.
    rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
    rewrite FV_lift_substitution // in_bigcup in H0. apply (rwP hasP) in H0 as [].
    apply (rwP pimfsetP) in H0 as [].
    apply (rwP codomm_Tm_setP). exists x0. split; auto.
    simpl. apply (rwP codommP). eauto.
  Qed.

  #[program] Lemma lift_substitution_indistinguishable_substitutions' :
    forall R f g t,
      t ∈ Tm (domm f ∩ domm g) ->
      (forall x, x ∈ FV t -> getm f x `≡_α^R getm g x) ->
      ⦇f⦈ t ≡_α^R ⦇g⦈ t.
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    gen R f g. induction t; intros.
    - apply IHt; simpl; intros_all.
      + rewrite in_fsetI !domm_set !in_fsetU !in_fset1.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        assert (x ∈ FV t :\ s). { rewrite in_fsetD in_fset1 n H1 //. }
        apply H in H2. rewrite /= in_fsetI in H2. apply (rwP andP) in H2 as [].
        rewrite H2 H3 //.
      + rewrite !setmE.
        destruct (x =P s); subst.
        { apply (rwP getmP). rewrite /= unionmE remmE rem_valmE setmE eq_refl //. }
        apply (introF eqP) in n.
        assert (x ∈ FV t :\ s). { rewrite in_fsetD in_fset1 n H1 //. }
        apply α_equivalent_update'; eauto;
        apply negbT, Bool.not_true_iff_false; intros_all; simpl in *;
        apply H in H2; rewrite in_fsetI in H2; apply (rwP andP) in H2 as [];
        apply (rwP dommP) in H2 as [], H4 as []; rewrite ?H2 ?H4 /= in H3;
        (pose proof Fresh_correct (codomm_Tm_set f)); (pose proof Fresh_correct (codomm_Tm_set g));
        rewrite <- (rwP codomm_Tm_setPn) in H5; rewrite <- (rwP codomm_Tm_setPn) in H6.
        * apply (H5 x0). split; auto. simpl. apply (rwP codommP). eauto.
        * apply (H6 x1). split; auto. simpl. apply (rwP codommP). eauto.
    - simpl. rewrite <- (rwP andP). split;
      (apply IHt1 || apply IHt2); simpl; intros_all;
      (apply H || apply H0); rewrite /= in_fsetU H1 ?orbT //.
    - apply H0. rewrite /= in_fset1 eq_refl //.
  Qed.

  #[program] Lemma lift_substitution_indistinguishable_substitutions :
    forall f g t,
      t ∈ Tm (domm f ∩ domm g) ->
      (forall x, x ∈ FV t -> getm f x `≡_α getm g x) ->
      ⦇f⦈ t ≡_α ⦇g⦈ t.
  Proof.
    intros.
    apply lift_substitution_indistinguishable_substitutions'; auto.
    simpl. intros.
    apply (rwP fsubsetP) in H.
    do 2 pose proof H1. apply H0 in H1.
    apply H in H2. rewrite /= in_fsetI in H2. apply (rwP andP) in H2 as [].
    apply (rwP dommP) in H2 as [].
    eapply α_equivalent'_supermap; cycle 1.
    { apply H1. }
    intros.
    rewrite mkfmapfE H2 in H5. inverts H5.
    destruct (k ∈ FV x0) eqn:?; rewrite Heqb in H7; inverts H7.
    rewrite mkfmapfE Heqb.
    cut (v ∈ FV (⦇f⦈ t) : Prop). { intros. rewrite H5 //. }
    rewrite FV_lift_substitution; cycle 1.
    { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      apply H in H5. rewrite /= in_fsetI in H5. apply (rwP andP) in H5 as []. auto. }
    rewrite in_bigcup. apply (rwP hasP). exists x0; auto.
    apply (rwP pimfsetP). eauto.
  Qed.

  (** Page 7: "We have to show ⦇f[[z0 = z1]]⦈ ∘ g[[x = z0]](v) ≡α (⦇f⦈ ∘ g)[[x = z1]](v)." *)
  #[program] Lemma lift_update_substitution_compose_substitution_update :
    forall f g x z0 z1,
      fsubset (codomm_Tm_set g) (domm f) ->
      z1 ∉ codomm_Tm_set f ->
      z0 ∉ codomm_Tm_set g ->
      forall v, v ∈ (domm g ∪ {x}) -> getm (⦇f[z0,variable z1]⦈ ∘ g[x,variable z0]) v `≡_α getm ((⦇f⦈ ∘ g)[x,variable z1]) v.
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    rewrite !setmE !mapmE /= !setmE.
    rewrite in_fsetU in_fset1 in H2. apply (rwP orP) in H2 as []; cycle 1.
    { rewrite H2 /= setmE eq_refl. reflexivity. }
    destruct (v =P x); subst.
    { rewrite /= setmE eq_refl. reflexivity. }
    apply (rwP dommP) in H2 as []. rewrite H2 /=.
    apply lift_substitution_indistinguishable_substitutions; simpl; intros.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      rewrite domm_set in_fsetI in_fsetU in_fset1 orbC.
      destruct (x1 ∈ domm f) eqn:?; auto.
      assert (x1 ∈ codomm_Tm_set g).
      { apply (rwP codomm_Tm_setP). exists x0. split; auto. simpl. apply (rwP codommP). eauto. }
      apply H in H4. rewrite /= Heqb // in H4.
    - rewrite setmE.
      destruct (x1 =P z0); subst.
      + assert (z0 ∈ codomm_Tm_set g).
        { apply (rwP codomm_Tm_setP). exists x0. split; auto. simpl. apply (rwP codommP). eauto. }
        rewrite H4 // in H1.
      + reflexivity.
  Qed.

  Lemma FV_lift_substitution_η :
    forall X t,
      t ∈ Tm X ->
      FV (⦇η__ X⦈ t) = FV t.
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    rewrite FV_lift_substitution; cycle 1.
    { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      rewrite domm_map domm_mkfmapf in_fset. apply H. auto. }
    apply eq_fset. intros_all.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP hasP) in H0 as [].
      apply (rwP pimfsetP) in H0 as [].
      rewrite mapmE mkfmapfE in H2.
      destruct (x1 ∈ X) eqn:?; rewrite Heqb in H2; inverts H2.
      rewrite in_fset1 in H1. apply (rwP eqP) in H1. subst. auto.
    - apply (rwP hasP). exists (variable x).
      + apply (rwP pimfsetP). exists x; auto.
        apply H in H0. simpl in *.
        rewrite mapmE mkfmapfE H0 //.
      + rewrite in_fset1 eq_refl //.
  Qed.

  Proposition monad_substitution1 :
    forall X t,
      t ∈ Tm X ->
      ⦇η__ X⦈ t ≡_α t.
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    transitivity (⦇η__(FV t)⦈ t).
    { apply lift_substitution_indistinguishable_substitutions; simpl; intros.
      - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
        rewrite in_fsetI !domm_map domm_mkfmapf domm_mkfmapf !in_fset H0 andbT. auto.
      - rewrite !mapmE !mkfmapfE H0. apply H in H0. simpl in *. rewrite H0. reflexivity. }
    rewrite /α_equivalent -converse_identity.
    rewrite FV_lift_substitution_η //.
    apply lemma7.
    - apply partial_bijection_identity.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. rewrite domm_mkfmapf in_fset H0 //.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. auto.
  Qed.

  #[program] Proposition monad_substitution2 :
    forall f x,
      x ∈ domm f ->
      getm (⦇f⦈ ∘ η__(domm f)) x `≡_α getm f x.
  Proof.
    simpl. intros. rewrite !mapmE mkfmapfE H. reflexivity.
  Qed.

  #[program] Lemma codomm_Tm_set_mapm :
    forall f g,
      fsubset (codomm_Tm_set g) (domm f) ->
      codomm_Tm_set (mapm ⦇f⦈ g) = ⋃_(x ∈ codomm_Tm_set g) (FV (odflt (variable _) (getm f x))).
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    apply eq_fset. intros_all.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP codomm_Tm_setP) in H0 as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H1 as [].
      rewrite mapmE in H1.
      destruct (getm g x1) eqn:?; inverts H1.
      rewrite FV_lift_substitution in H0; cycle 1.
      { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
        apply H, (rwP codomm_Tm_setP). exists t. split; auto. simpl. apply (rwP codommP). eauto. }
      rewrite in_bigcup in H0. apply (rwP hasP) in H0 as [].
      apply (rwP pimfsetP) in H0 as [].
      simpl in *.
      apply (rwP hasP). exists x2.
      { apply (rwP codomm_Tm_setP). exists t. split; auto. simpl. apply (rwP codommP). eauto. }
      rewrite H2 //.
    - apply (rwP hasP) in H0 as [].
      pose proof H0. simpl in *. apply H, (rwP dommP) in H0 as [].
      rewrite H0 /= in H1.
      apply (rwP codomm_Tm_setP) in H2 as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H3 as [].
      apply (rwP codomm_Tm_setP). exists (⦇f⦈ x2). split.
      { rewrite FV_lift_substitution; cycle 1.
        { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          apply H, (rwP codomm_Tm_setP). exists x2. split; auto. simpl. apply (rwP codommP). eauto. }
        rewrite /= in_bigcup. apply (rwP hasP). exists x1; auto.
        apply (rwP pimfsetP). exists x0; auto. }
      simpl. apply (rwP codommP). exists x3.
      rewrite mapmE H3 //.
  Qed.

  Proposition monad_substitution3 :
    forall f g t,
      fsubset (codomm_Tm_set g) (domm f) ->
      t ∈ Tm (domm g) ->
      (⦇f⦈ ∘ ⦇g⦈) t ≡_α ⦇⦇f⦈ ∘ g⦈ t.
  Proof.
    intros.
    apply (rwP fsubsetP) in H, H0.
    gen f g. induction t; intros.
    - set (z0 := Fresh (codomm_Tm_set g)).
      set (z1 := Fresh (codomm_Tm_set f)).
      set (X := FV (⦇f[z0,variable z1]⦈ (⦇g[s,variable z0]⦈ t))).
      assert (forall k v : 𝒱, getm (1__X) k = Some v -> getm (1__(X :\ z1 ∪ {z1})) k = Some v).
      { intros.
        rewrite mkfmapfE in H1.
        rewrite mkfmapfE in_fsetU in_fsetD !in_fset1 orbC.
        destruct (k =P z1); subst; auto.
        destruct (z1 ∈ X) eqn:?; rewrite Heqb in H1; inverts H1. auto. }
      transitivity (⦇f⦈ (abstraction z0 (⦇g[s,variable z0]⦈ t))).
      { rewrite /α_equivalent/= update_identity -/z0 -/z1 -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto.
        apply α_equivalent'_identity.
        rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. auto. }
      transitivity (abstraction z1 ((⦇f[z0,variable z1]⦈ ∘ ⦇g[s,variable z0]⦈) t)).
      { rewrite /α_equivalent /= update_identity -/z0 -/z1 -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto.
        apply α_equivalent'_identity.
        rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. auto. }
      assert (⦇f[z0,variable z1]⦈ (⦇g[s,variable z0]⦈ t) ≡_α ⦇⦇f[z0,variable z1]⦈ ∘ g[s,variable z0]⦈ t).
      { apply IHt; simpl; intros_all;
        rewrite domm_set in_fsetU in_fset1.
        - destruct (x =P z0); subst; auto.
          apply (rwP codomm_Tm_setP) in H2 as (? & ? & ?).
          simpl in *. apply (rwP codommP) in H3 as [].
          rewrite setmE in H3.
          destruct (x1 =P s); subst.
          { inverts H3. rewrite in_fset1 in H2. apply (rwP eqP) in H2. subst. contradiction. }
          apply H, (rwP codomm_Tm_setP). exists x0. split; auto.
          simpl. apply (rwP codommP). eauto.
        - destruct (x =P s); subst; auto.
          apply (introF eqP) in n.
          apply H0. rewrite /= in_fsetD in_fset1 n H2 //. }
      transitivity (abstraction z1 (⦇⦇f[z0,variable z1]⦈ ∘ g[s,variable z0]⦈ t)).
      { rewrite /α_equivalent /= update_identity -/z0 -/z1 -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto. }
      transitivity (abstraction z1 (⦇(⦇f⦈ ∘ g)[s,variable z1]⦈ t)).
      { apply α_equivalent_implies_same_FV in H2.
        rewrite /α_equivalent /= update_identity -/z0 -/z1 H2 -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto.
        rewrite /X -H2.
        apply lift_substitution_indistinguishable_substitutions; simpl; intros.
        - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          rewrite in_fsetI domm_set !domm_map domm_set !in_fsetU in_fset1 Bool.andb_diag.
          destruct (x =P s); subst; auto.
          apply (introF eqP) in n.
          apply H0. rewrite /= in_fsetD in_fset1 n H3 //.
        - apply lift_update_substitution_compose_substitution_update; auto; try apply Fresh_correct.
          + apply (rwP fsubsetP). auto.
          + rewrite in_fsetU in_fset1 orbC.
            destruct (x =P s); subst; auto.
            apply (introF eqP) in n.
            apply H0. rewrite /= in_fsetD in_fset1 n H3 //. }
      rewrite /α_equivalent /=.
      apply substitution_preserves_α_congruence' with (R := 1__(FV t)).
      { rewrite !domm_set !domm_map. intros_all.
        rewrite <- (rwP andP).
        split;
        rewrite /= !in_fsetU !in_fset1;
        rewrite /fmap_to_Prop mkfmapfE in H3;
        destruct (x ∈ FV t) eqn:?; rewrite Heqb in H3; inverts H3;
        destruct (y =P s); subst; auto;
        apply (introF eqP) in n;
        simpl in *; apply H0; rewrite /= in_fsetD in_fset1 n Heqb //. }
      { apply partial_bijection_identity. }
      { apply partial_bijection_update, partial_bijection_identity. }
      { intros.
        rewrite /fmap_to_Prop mkfmapfE in H3.
        destruct (x ∈ FV t) eqn:?; rewrite Heqb in H3; inverts H3.
        rewrite !setmE !mapmE.
        destruct (x' =P s); subst.
        { apply (rwP getmP). rewrite /= unionmE remmE rem_valmE setmE eq_refl //. }
        apply (introF eqP) in n.
        simpl in *.
        assert (x' ∈ FV t :\ s). { rewrite in_fsetD in_fset1 n Heqb //. }
        apply H0, (rwP dommP) in H3 as []. rewrite H3 /=.
        assert {subset FV x <= codomm_Tm_set g}.
        { intros_all. apply (rwP codomm_Tm_setP). exists x. split; auto. simpl. apply (rwP codommP). eauto. }
        assert {subset FV (⦇f⦈ x) <= codomm_Tm_set (mapm ⦇f⦈ g)}.
        { intros_all.
          rewrite FV_lift_substitution in H5; cycle 1.
          { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. apply H, H4, H5. }
          rewrite in_bigcup in H5. apply (rwP hasP) in H5 as [].
          apply (rwP pimfsetP) in H5 as [].
          rewrite /= codomm_Tm_set_mapm; cycle 1.
          { apply (rwP fsubsetP). intros_all. auto. }
          rewrite in_bigcup.
          apply (rwP hasP). exists x2.
          { apply H4. auto. }
          rewrite /= H7 //. }
        assert {subset FV (⦇f⦈ x) <= codomm_Tm_set f}.
        { intros_all.
          rewrite FV_lift_substitution in H6; cycle 1.
          { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
            apply H, (rwP codomm_Tm_setP). exists x. split; auto. simpl. apply (rwP codommP). eauto. }
          rewrite in_bigcup in H6. apply (rwP hasP) in H6 as [].
          apply (rwP pimfsetP) in H6 as [].
          apply (rwP codomm_Tm_setP). exists x1. split; auto. simpl. apply (rwP codommP). eauto. }
        assert (Fresh (codomm_Tm_set (mapm ⦇f⦈ g)) ∉ FV (⦇f⦈ x)).
        { pose proof Fresh_correct (codomm_Tm_set (mapm ⦇f⦈ g)).
          apply negbT, Bool.not_true_iff_false. intros_all.
          apply H5 in H8. simpl in *. rewrite H8 // in H7. }
        assert (z1 ∉ FV (⦇f⦈ x)).
        { subst z1.
          pose proof Fresh_correct (codomm_Tm_set f).
          apply negbT, Bool.not_true_iff_false. intros_all.
          apply H6 in H9. simpl in *. rewrite H9 // in H8. }
        apply α_equivalent_update'; auto.
        apply α_equivalent'_supermap with (R__sub := 1__(FV (⦇f⦈ x))); cycle 1.
        { apply α_equivalent_reflexive. }
        intros.
        rewrite mkfmapfE in H9.
        rewrite mkfmapfE in_fsetD in_fset1.
        destruct (k ∈ FV (⦇f⦈ x)) eqn:?; rewrite Heqb0 in H9; inverts H9.
        destruct (v =P z1); subst.
        { rewrite Heqb0 // in H8. }
        rewrite FV_lift_substitution; cycle 1.
        { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          rewrite domm_set domm_map in_fsetU in_fset1.
          destruct (x0 =P s); subst; auto.
          apply (introF eqP) in n1.
          apply H0. rewrite in_fsetD in_fset1 n1 H9 //. }
        rewrite in_bigcup /=.
        cut (has (fun i => v ∈ FV i)
                  (pimfset (getm ((mapm ⦇f⦈ g)[s,variable z1])) (FV t)) : Prop).
        { intros. rewrite H9 //. }
        apply (rwP hasP). exists (⦇f⦈ x); auto.
        rewrite <- (rwP (@pimfsetP _ _ (getm ((mapm ⦇f⦈ g)[s,variable z1])) (FV t) (⦇f⦈ x))).
        exists x'; auto.
        rewrite setmE mapmE n H3 //. }
      apply α_equivalent'_identity.
      rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. auto.
    - rewrite /α_equivalent /=. rewrite <- (rwP andP). split.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (⦇f⦈ (⦇g⦈ t1)))); cycle 1.
        { apply IHt1; auto. simpl in *. intros_all. apply H0. rewrite in_fsetU H1 //. }
        intros.
        rewrite mkfmapfE in H1.
        destruct (k ∈ FV (⦇f⦈ (⦇g⦈ t1))) eqn:?; rewrite Heqb in H1; inverts H1.
        rewrite mkfmapfE in_fsetU Heqb //.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (⦇f⦈ (⦇g⦈ t2)))); cycle 1.
        { apply IHt2; auto. simpl in *. intros_all. apply H0. rewrite in_fsetU H1 orbT //. }
        intros.
        rewrite mkfmapfE in H1.
        destruct (k ∈ FV (⦇f⦈ (⦇g⦈ t2))) eqn:?; rewrite Heqb in H1; inverts H1.
        rewrite mkfmapfE in_fsetU Heqb orbT //.
    - simpl in *.
      assert (s ∈ fset1 s). { rewrite in_fset1 //. }
      apply H0, (rwP dommP) in H1 as []. rewrite mapmE H1. reflexivity.
  Qed.

  Notation "t '[' x '=' u ']'" := (⦇(1__(FV t))[x,u]⦈ t) (at level 10, x at next level, u at next level).

  #[local] Notation "t '[' x '⟵' u ']'" := (t[x=u]) (at level 10, x at next level, u at next level).

  (** Page 5: "To show that substitution is well behaved, i.e. laws such as...." *)
  Lemma substitution_law1 :
    forall t u x,
      x ∉ FV t ->
      t[x⟵u] ≡_α t.
  Proof.
    intros.
    transitivity (⦇η__(FV t)⦈ t).
    - apply lift_substitution_indistinguishable_substitutions; simpl; intros.
      + rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
        rewrite !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI in_fsetU !in_fset H0 orbT //.
      + rewrite setmE mapmE.
        destruct (x0 =P x); subst.
        { rewrite H0 // in H. }
        reflexivity.
    - apply monad_substitution1.
      rewrite /Tm /in_mem /= fsubsetxx //.
  Qed.

  Lemma codomm_update_substitution :
    forall f x t,
      codomm_Tm_set (f[x,t]) = codomm_Tm_set (remm f x) ∪ FV t.
  Proof.
    intros.
    apply eq_fset. intros_all.
    rewrite in_fsetU.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H0 as [].
      rewrite setmE in H0.
      destruct (x2 =P x); subst.
      { inverts H0. rewrite H orbT //. }
      apply (rwP orP). left.
      apply (rwP codomm_Tm_setP). exists x1. split; auto.
      simpl in *. apply (rwP codommP). exists x2.
      apply (introF eqP) in n.
      rewrite remmE n H0 //.
    - apply (rwP codomm_Tm_setP).
      apply (rwP orP) in H as [].
      + apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
       simpl in *. apply (rwP codommP) in H0 as [].
       rewrite remmE in H0.
       destruct (x2 =P x); subst.
       { inverts H0. }
       exists x1. split; auto.
       apply (rwP codommP). exists x2.
       apply (introF eqP) in n.
       rewrite setmE n H0 //.
      + exists t. split; auto.
        apply (rwP codommP). exists x.
        rewrite setmE eq_refl //.
  Qed.

  Lemma domm_identity' :
    forall X,
      domm (1__X : {fmap 𝒱 → term}) = X.
  Proof.
    intros.
    rewrite domm_map domm_identity //.
  Qed.

  Lemma codomm_identity' :
    forall X,
      codomm (1__X : {fmap 𝒱 → term}) = variable @: X.
  Proof.
    intros.
    apply eq_fset. intros_all.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP codommP) in H as [].
      rewrite mapmE mkfmapfE in H.
      apply (rwP imfsetP).
      destruct (x0 ∈ X) eqn:?; rewrite Heqb in H; inverts H.
      eauto.
    - apply (rwP imfsetP) in H as []. subst.
      apply (rwP codommP). exists x0.
      rewrite mapmE mkfmapfE H //.
  Qed.

  Lemma FV_after_substitute :
    forall t u x,
      x ∈ FV t ->
      FV (t[x⟵u]) = (FV t :\ x) ∪ FV u.
  Proof.
    intros.
    simpl.
    replace (FV t :\ x) with (codomm_Tm_set (remm (1__(FV t)) x)); cycle 1.
    { apply eq_fset. intros_all.
      rewrite in_fsetD in_fset1.
      destruct (x0 =P x); subst.
      - apply negbTE, (rwP codomm_Tm_setPn). simpl. intros ? [].
        apply (rwP codommP) in H1 as [].
        rewrite remmE mapmE mkfmapfE in H1.
        destruct (x0 =P x); subst.
        { inverts H1. }
        destruct (x0 ∈ FV t) eqn:?; rewrite Heqb in H1; inverts H1.
        rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst. auto.
      - destruct (x0 ∈ FV t) eqn:?.
        + apply (rwP codomm_Tm_setP). exists (variable x0). simpl. split.
          * rewrite in_fset1 eq_refl //.
          * apply (rwP codommP). exists x0.
          apply (introF eqP) in n.
          rewrite remmE mapmE mkfmapfE n Heqb //.
        + apply negbTE, (rwP codomm_Tm_setPn). simpl. intros ? [].
          apply (rwP codommP) in H1 as [].
          rewrite remmE mapmE mkfmapfE in H1.
          destruct (x1 =P x); subst.
          { inverts H1. }
          destruct (x1 ∈ FV t) eqn:?; rewrite Heqb0 in H1; inverts H1.
          rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst. rewrite Heqb0 // in Heqb. }
    rewrite FV_lift_substitution.
    - apply eq_fset. intros_all.
      apply Bool.eq_iff_eq_true. split; simpl; intros.
      + rewrite in_fsetU.
        rewrite in_bigcup in H0. apply (rwP hasP) in H0 as [].
        apply (rwP pimfsetP) in H0 as [].
        rewrite setmE mapmE mkfmapfE in H2.
        destruct (x2 =P x); subst.
        { inverts H2. simpl in *. rewrite H1 orbT //. }
        rewrite H0 in H2. inverts H2.
        rewrite in_fset1 in H1. apply (rwP eqP) in H1. subst.
        apply (rwP orP). left.
        apply (rwP codomm_Tm_setP). exists (variable x2). split.
        * rewrite /= in_fset1 eq_refl //.
        * apply (rwP codommP). exists x2.
          apply (introF eqP) in n.
          rewrite remmE mapmE mkfmapfE n H0 //.
      + rewrite in_bigcup. apply (rwP hasP).
        rewrite in_fsetU in H0. apply (rwP orP) in H0 as [].
        * apply (rwP codomm_Tm_setP) in H0 as (? & ? & ?).
          simpl in *. apply (rwP codommP) in H1 as [].
          rewrite remmE mapmE mkfmapfE in H1.
          destruct (x2 =P x); subst.
          { inverts H1. }
          destruct (x2 ∈ FV t) eqn:?; rewrite Heqb in H1; inverts H1.
          rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst.
          exists (variable x2).
          -- apply (rwP pimfsetP). exists x2; auto.
             apply (introF eqP) in n.
             rewrite setmE mapmE mkfmapfE n Heqb //.
          -- rewrite /= in_fset1 eq_refl //.
        * exists u; auto.
          apply (rwP pimfsetP). exists x; auto.
          rewrite setmE mapmE mkfmapfE eq_refl //.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset H0 orbT //.
  Qed.

  Lemma FV_noop_substitute :
    forall t u x,
      x ∉ FV t ->
      FV (t[x⟵u]) = FV t.
  Proof.
    intros.
    apply α_equivalent_implies_same_FV.
    symmetry. apply substitution_law1. auto.
  Qed.

  Lemma domm_update_identity :
    forall t u x,
      domm ((1__(FV t))[x, u]) = FV t ∪ {x}.
  Proof.
    intros.
    rewrite domm_update_substitution domm_map domm_mkfmapf fsvalK //.
  Qed.

  Lemma codomm_Tm_set_update_identity :
    forall X u x,
      codomm_Tm_set ((1__X)[x, u]) = (X :\ x) ∪ FV u.
  Proof.
    intros.
    rewrite codomm_update_substitution. repeat f_equal.
    apply eq_fset. intros_all.
    rewrite in_fsetD in_fset1.
    apply Bool.eq_iff_eq_true. split; intros.
    + apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H0 as [].
      rewrite remmE mapmE mkfmapfE in H0.
      destruct (x2 =P x); subst.
      { inverts H0. }
      destruct (x2 ∈ X) eqn:?; rewrite Heqb in H0; inverts H0.
      rewrite in_fset1 in H. apply (rwP eqP) in H. subst.
      apply (introF eqP) in n.
      rewrite n Heqb //.
    + apply (rwP andP) in H as [].
      apply (rwP codomm_Tm_setP). exists (variable x0). split.
      * rewrite /= in_fset1 eq_refl //.
      * apply (rwP codommP). exists x0.
        apply negbTE in H.
        rewrite remmE mapmE mkfmapfE H H0 //.
  Qed.

  (** Page 5: "To show that substitution is well behaved, i.e. laws such as...." *)
  Lemma substitution_law2 :
    forall t u (v : term) x y,
      x <> y ->
      x ∉ FV v -> (* See Exercise 2.2 in http://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/geuvers.pdf. *)
      t[x⟵u][y⟵v] ≡_α t[y⟵v][x⟵u[y⟵v]].
  Proof.
    intros.
    symmetry.
    transitivity (⦇⦇(1__(FV(⦇(1__(FV t))[y,v]⦈ t)))[x,⦇(1__(FV u))[y,v]⦈ u]⦈ ∘ (1__(FV t))[y,v]⦈ t).
    { destruct (y ∈ FV t) eqn:?. (* TODO Can we remove the [destruct]s of this form? *)
      - apply monad_substitution3; try rewrite /Tm /in_mem /=; apply (rwP fsubsetP); intros_all;
        rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset.
        + rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1.
          destruct (x0 =P x); subst; auto.
          apply (rwP codomm_Tm_setP) in H1 as (? & ? & ?).
          simpl in *. apply (rwP codommP) in H2 as [].
          rewrite setmE mapmE mkfmapfE in H2.
          destruct (x2 =P y); subst.
          { inverts H2. rewrite H1 orbT //. }
          apply (introF eqP) in n0.
          destruct (x2 ∈ FV t) eqn:?; rewrite Heqb0 in H2; inverts H2.
          rewrite in_fset1 in H1. apply (rwP eqP) in H1. subst.
          rewrite n0 Heqb0 //.
        + rewrite H1 orbT //.
      - transitivity (⦇(1__(FV(⦇(1__(FV t))[y,v]⦈ t)))[x,⦇(1__(FV u))[y,v]⦈ u]⦈ t).
        { apply substitution_respects_α_equivalence.
          - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
            rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset H1 orbT //.
          - apply substitution_law1. simpl in *. rewrite Heqb //. }
        apply lift_substitution_indistinguishable_substitutions; simpl; intros.
        + rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          rewrite !domm_set !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset !in_fset1 H1 orbT andbT.
          destruct (x0 =P x); subst; auto.
          rewrite FV_noop_substitute //. simpl in *. rewrite Heqb //.
        + rewrite !setmE !mapmE !setmE !mapmE !mkfmapfE H1.
          destruct (x0 =P x); subst.
          { apply (introF eqP) in H. rewrite /= H /= setmE mapmE eq_refl. reflexivity. }
          apply (introF eqP) in n.
          rewrite FV_noop_substitute; cycle 1.
          { simpl in *. rewrite Heqb //. }
          rewrite H1 /=.
          destruct (x0 =P y); subst.
          { rewrite /= H1 // in Heqb. }
          rewrite /= setmE mapmE mkfmapfE n H1. reflexivity. }
    symmetry.
    transitivity (⦇⦇(1__(FV (⦇(1__(FV t))[x,u]⦈ t)))[y,v]⦈ ∘ (1__(FV t))[x,u]⦈ t).
    { destruct (x ∈ FV t) eqn:?.
      - apply monad_substitution3; try rewrite /Tm /in_mem /=; apply (rwP fsubsetP); intros_all; rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset1 in_fset.
        + rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1.
          destruct (x0 =P y); subst; auto.
          apply (rwP codomm_Tm_setP) in H1 as (? & ? & ?).
          simpl in *. apply (rwP codommP) in H2 as [].
          rewrite setmE mapmE mkfmapfE in H2.
          destruct (x2 =P x); subst.
          { inverts H2. rewrite H1 !orbT //. }
          apply (introF eqP) in n0.
          destruct (x2 ∈ FV t) eqn:?; rewrite Heqb0 in H2; inverts H2.
          rewrite in_fset1 in H1. apply (rwP eqP) in H1. subst.
          rewrite n0 Heqb0 //.
        + rewrite H1 orbT //.
      - transitivity (⦇(1__(FV (⦇(1__(FV t))[x,u]⦈ t)))[y,v]⦈ t).
        { apply substitution_respects_α_equivalence; cycle 1.
          { apply substitution_law1. simpl in *. rewrite Heqb //. }
          rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset in_fset1 H1 orbT //. }
        apply lift_substitution_indistinguishable_substitutions; simpl; intros.
        + rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          rewrite !domm_set !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset !in_fset1 H1 orbT andbT FV_noop_substitute; cycle 1.
          { simpl in *. rewrite Heqb //. }
          destruct (x0 =P y); subst; auto.
        + rewrite !mapmE !setmE !mapmE !mkfmapfE H1.
          destruct (x0 =P y); subst.
          { apply not_eq_sym, (introF eqP) in H. rewrite H /= setmE eq_refl. reflexivity. }
          apply (introF eqP) in n.
          destruct (x0 =P x); subst.
          { rewrite /= H1 // in Heqb. }
          rewrite /= setmE mapmE mkfmapfE n FV_noop_substitute; cycle 1.
          { simpl in *. rewrite Heqb //. }
          rewrite H1. reflexivity. }
    apply lift_substitution_indistinguishable_substitutions; simpl; intros.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      rewrite !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset !in_fset1 H1 !orbT //.
    - rewrite !mapmE !setmE !mapmE !mkfmapfE H1.
      destruct (x0 =P x); subst.
      + apply (introF eqP) in H. rewrite H /= setmE mapmE mkfmapfE eq_refl /=.
        apply lift_substitution_indistinguishable_substitutions; simpl; intros.
        * rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          rewrite domm_set domm_map domm_set domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset1 !in_fset H2 orbT andbT.
          destruct (x =P y); subst; auto.
          rewrite /= FV_after_substitute // in_fsetU in_fsetD !in_fset1 H2 !orbT //.
        * rewrite !setmE !mapmE !mkfmapfE H2.
          destruct (x0 =P y); subst.
          { reflexivity. }
          rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1 H2 orbT. reflexivity.
      + destruct (x0 =P y); subst.
        * rewrite /= setmE mapmE eq_refl FV_after_substitute //.
          transitivity (⦇1__(FV v)⦈ v).
          { symmetry. apply monad_substitution1.
            rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. auto. }
          apply lift_substitution_indistinguishable_substitutions; simpl; intros.
          -- rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
             rewrite domm_set !domm_map !domm_mkfmapf in_fsetI in_fsetU in_fset in_fset in_fsetU in_fsetD !in_fset1 H2 !orbT //.
          -- rewrite setmE !mapmE !mkfmapfE in_fsetU in_fsetD in_fset1 H2 orbT.
             destruct (x0 =P x); subst.
             { rewrite H2 // in H0. }
             reflexivity.
        * apply (introF eqP) in n, n0.
          rewrite /= !setmE !mapmE !mkfmapfE n n0.
          destruct (x ∈ FV t) eqn:?.
          -- rewrite FV_after_substitute // in_fsetU in_fsetD in_fset1 H1 andbT n /=.
             destruct (y ∈ FV t) eqn:?.
             ++ rewrite FV_after_substitute // in_fsetU in_fsetD in_fset1 H1 n0. reflexivity.
             ++ rewrite FV_noop_substitute; cycle 1.
                { rewrite Heqb0 //. }
                rewrite H1. reflexivity.
          -- rewrite FV_noop_substitute; cycle 1.
             { rewrite Heqb //. }
             rewrite H1.
             destruct (y ∈ FV t) eqn:?.
             ++ rewrite FV_after_substitute // in_fsetU in_fsetD in_fset1 H1 andbT n0. reflexivity.
             ++ rewrite FV_noop_substitute; cycle 1.
                { rewrite Heqb0 //. }
                rewrite H1. reflexivity.
  Qed.

  (** Page 7: "A monad gives rise to its Kleisli-category...." *)

  (** TODO Explicitly formalize the resulting Kliesli-category? *)

  Implicit Types (c d i j n : nat) (ϕ ψ : {fmap 𝒱 → nat}).

  Definition nat_to_pred n i : bool := i < n.

  (** Page 7: "Here we identify n ∈ Nat with the set {i ∈ Nat | i < n}." *)
  Canonical nat_predType := PredType nat_to_pred.

  Inductive de_Bruijn_term : Type :=
  | de_Bruijn_abstraction : de_Bruijn_term -> de_Bruijn_term
  | de_Bruijn_application : de_Bruijn_term -> de_Bruijn_term -> de_Bruijn_term
  | de_Bruijn_variable : nat -> de_Bruijn_term.

  #[local] Coercion de_Bruijn_variable : nat >-> de_Bruijn_term.

  Implicit Types (dBt dBu : de_Bruijn_term).

  Fixpoint de_Bruijn_Tm n dBt : bool :=
    match dBt with
    | de_Bruijn_abstraction dBt =>
      dBt ∈ de_Bruijn_Tm (S n)
    | de_Bruijn_application dBt dBu =>
      (dBt ∈ de_Bruijn_Tm n) && (dBu ∈ de_Bruijn_Tm n)
    | de_Bruijn_variable i =>
      i ∈ n
    end.

  #[local] Notation "'Tm^db'" := de_Bruijn_Tm.

  (** Page 7: "For any n ∈ Nat we define the set Tm^db(n) of de Bruijn terms with at most n free Variables inductively by the following rules:...." *)
  Section in_de_Bruijn_Tm.
    Reserved Notation "x '∈' 'Tm^db' n" (at level 40).

    Inductive in_de_Bruijn_Tm : nat -> de_Bruijn_term -> Prop :=
    | de_Bruijn_Tm_variable : forall n i,
        i ∈ n ->
        i ∈ Tm^db n
    | de_Bruijn_Tm_application : forall n dBt dBu,
        dBt ∈ Tm^db n ->
        dBu ∈ Tm^db n ->
        de_Bruijn_application dBt dBu ∈ Tm^db n
    | de_Bruijn_Tm_abstraction : forall n dBt,
        dBt ∈ Tm^db (n + 1) ->
        de_Bruijn_abstraction dBt ∈ Tm^db n

    where "t '∈' 'Tm^db' n" := (in_de_Bruijn_Tm n t).
  End in_de_Bruijn_Tm.

  Lemma de_Bruijn_TmP : forall n dBt, reflect (in_de_Bruijn_Tm n dBt) (dBt ∈ Tm^db n).
  Proof.
    rewrite /in_mem /=.
    simpl. intros.
    gen n. induction dBt; simpl; intros; rewrite /in_mem /=.
    - destruct (IHdBt n.+1); repeat constructor.
      + rewrite addn1 //.
      + intros_all. apply n0. inverts H. rewrite addn1 // in H2.
    - destruct (IHdBt1 n); repeat constructor.
      + destruct (IHdBt2 n); repeat constructor; auto.
        intros_all. apply n0. inverts H. auto.
      + intros_all. inverts H. auto.
    - rewrite /nat_to_pred.
      gen n0. induction n; intros;
      destruct n0; repeat constructor; intros_all; simpl in *;
      try solve [inverts H; inverts H2].
      replace (n.+1 < n0.+1) with (n < n0) by auto.
      (pose proof (IHn n0)); inverts H; repeat constructor.
      { simpl. auto. }
      intros_all. inverts H. simpl in *.
      rewrite /in_mem /= /nat_to_pred in H4.
      replace (n.+1 < n0.+1) with (n < n0) in H4 by auto.
      rewrite H4 // in H0.
  Qed.

  Lemma de_Bruijn_Tm_subset :
    forall n n' dBt,
      n <= n' ->
      dBt ∈ Tm^db n ->
      dBt ∈ Tm^db n'.
  Proof.
    rewrite /in_mem /=.
    intros.
    gen n n'. induction dBt; intros; simpl in *.
    - apply IHdBt with (n.+1); auto.
    - apply (rwP andP) in H0 as [].
      eapply IHdBt1 with (n' := n') in H0; auto. eapply IHdBt2 with (n' := n') in H1; auto.
      rewrite /in_mem /= H0 H1 //.
    - apply leq_trans with n0; auto.
  Qed.

  Definition update_ϕ x ϕ : {fmap 𝒱 → nat} :=
    setm (mapm S ϕ) x 0.

  #[local] Notation "ϕ '^+' x" := (update_ϕ x ϕ).

  Definition codomm_𝐍 ϕ : nat :=
    S (\max_(i <- codomm ϕ) i).

  Lemma ϕ_type :
    forall ϕ n,
      n ∈ codomm ϕ ->
      n ∈ codomm_𝐍 ϕ.
  Proof.
    intros. rewrite /codomm_𝐍 -maxE. apply maximum_correct. auto.
  Qed.

  Lemma domm_update_ϕ :
    forall ϕ x,
      domm (ϕ^+x) = domm ϕ ∪ {x}.
  Proof.
    intros.
    rewrite domm_set domm_map fsetUC //.
  Qed.

  Lemma codomm_𝐍_update_ϕ :
    forall ϕ x,
      codomm_𝐍 (ϕ^+x) <= S (codomm_𝐍 ϕ).
  Proof.
    unfold codomm_𝐍.
    intros.
    rewrite codomm_setmE remm_mapm codomm_mapm big_idem_fsetU1 /=; try apply maxnn.
    rewrite max0n big_idem_imfset /=; try apply maxnn.
    pose proof codomm_rem ϕ x. apply (rwP fsubsetP), bigmax_subset in H.
    change (\max_(i <- codomm (remm ϕ x)) i.+1 <= (\max_(i <- codomm ϕ) i).+1).
    apply leq_trans with ((\max_(i <- codomm (remm ϕ x)) i).+1); auto.
    apply S_bigmax.
  Qed.

  Lemma codomm_update_ϕ :
    forall ϕ x,
      {subset codomm (ϕ^+x) <= S (codomm_𝐍 ϕ)}.
  Proof.
    intros_all.
    apply (rwP codommP) in H as [].
    rewrite setmE mapmE in H.
    destruct (x1 =P x); subst.
    { inverts H. auto. }
    destruct (getm ϕ x1) eqn:?; inverts H.
    apply ϕ_type. simpl. apply (rwP codommP). eauto.
  Qed.

  (** Page 8: "where ϕ^+x(y) = ...." *)
  Lemma update_ϕ_correct :
    forall ϕ x y,
      y ∈ domm ϕ ∪ {x} ->
      getm (ϕ^+x) y =
      if y == x
      then Some 0
      else omap S (getm ϕ y).
  Proof.
    simpl. intros.
    rewrite setmE mapmE.
    rewrite /= in_fsetU in_fset1 in H. apply (rwP orP) in H as [].
    - destruct (y =P x); auto.
    - rewrite H //.
  Qed.

  (** Page 8: "Note that ϕ^+x is an injection, if ϕ is." *)
  Lemma injective_update_ϕ :
    forall ϕ x,
      is_injective ϕ ->
      is_injective (ϕ^+x).
  Proof.
    intros.
    apply (rwP injectivemP) in H.
    apply (rwP (@injectivemP _ _ (ϕ^+x))). intros_all.
    apply (rwP dommP) in H0 as [].
    rewrite setmE mapmE in H0.
    rewrite !setmE !mapmE in H1.
    destruct (x0 =P x); subst.
    - inverts H0.
      destruct (x2 =P x); subst; auto.
      destruct (getm ϕ x2) eqn:?; inverts H1.
    - destruct (x2 =P x); subst;
      destruct (getm ϕ x0) eqn:?; inverts H0.
      { inverts H1. }
      + destruct (getm ϕ x2) eqn:?; inverts H1.
        rewrite -Heqo0 in Heqo. apply H in Heqo; auto.
        rewrite Heqo0 in Heqo. apply (rwP dommP). eauto.
  Qed.

  #[local] Reserved Notation "t '^' ϕ" (at level 30, ϕ at level 30).

  (** Pages 7-8: "we assign to any t ∈ Tm(X) a de Bruijn term t^ϕ ∈ Tm^db(n) by...." *)
  Fixpoint to_de_Bruijn t ϕ : de_Bruijn_term :=
    match t with
    | variable x =>
      de_Bruijn_variable (odflt 0 (getm ϕ x))
    | application t u =>
      de_Bruijn_application (t^ϕ) (u^ϕ)
    | abstraction x t =>
      de_Bruijn_abstraction (t^(ϕ^+x))
    end

  where "t '^' ϕ" := (to_de_Bruijn t ϕ).

  (** Page 8: "t^ϕ ∈ Tm^db(n)". *)
  Lemma to_de_Bruijn_type :
    forall ϕ t,
      t ∈ Tm (domm ϕ) ->
      t^ϕ ∈ Tm^db (codomm_𝐍 ϕ).
  Proof.
    rewrite /in_mem /= /Tm.
    intros.
    apply (rwP fsubsetP) in H.
    gen ϕ. induction t; intros; simpl in *.
    - apply de_Bruijn_Tm_subset with (codomm_𝐍 (ϕ^+s)).
      + apply codomm_𝐍_update_ϕ.
      + apply IHt. intros_all.
        rewrite domm_set domm_map in_fsetU in_fset1.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply H. rewrite in_fsetD in_fset1 n H0 //.
    - apply (rwP (@andP (Tm^db _ _) (Tm^db _ _))). split;
      (apply IHt1 || apply IHt2); simpl; intros_all;
      apply H; rewrite in_fsetU H0 ?orbT //.
    - assert (s ∈ fset1 s). { rewrite in_fset1 eq_refl //. }
      apply H, (rwP dommP) in H0 as []. rewrite H0.
      apply ϕ_type, (rwP codommP). eauto.
  Qed.

  (** Page 8: "where R is the pullback of ϕ and ψ, i.e. ...." *)
  Definition is_pullback R ϕ ψ : Prop :=
    forall x y, R x y <-> (x ∈ domm ϕ /\ getm ϕ x = getm ψ y).

  Lemma lemma9' :
    forall R ϕ ψ x y,
      R ⊆ domm ϕ × domm ψ ->
      is_injective ϕ ->
      is_injective ψ ->
      is_pullback R ϕ ψ ->
      is_pullback (R⦅x,y⦆) (ϕ^+x) (ψ^+y).
  Proof.
    simpl. intros_all.
    rewrite /fmap_to_Prop unionmE remmE rem_valmE !setmE !mapmE /=.
    split; intros.
    - destruct (x0 =P x); subst.
      { inverts H3. rewrite eq_refl.
        split; auto. apply (rwP dommP). rewrite setmE mapmE eq_refl. eauto. }
      destruct (getm R x0) eqn:?; cycle 1.
      { inverts H3. }
      destruct (y =P s); subst; inverts H3.
      pose proof Heqo. apply H, (rwP andP) in Heqo as [].
      simpl in *. apply (rwP dommP) in H4 as [].
      apply (rwP dommP) in H5 as [].
      apply not_eq_sym, (introF eqP) in n0.
      apply H2 in H3. rewrite H4 H5 in H3. inverts H3.
      rewrite H4 H5 n0.
      split.
      + apply (rwP dommP). apply (introF eqP) in n. rewrite setmE mapmE n H4 /=. eauto.
      + inverts H7. auto.
    - destruct H3.
      destruct (x0 =P x); subst.
      + destruct (y0 =P y); subst; auto.
        destruct (getm ψ y0) eqn:?; inverts H4.
      + destruct (getm R x0) eqn:?.
        * pose proof Heqo.
          apply H, (rwP andP) in H5 as [].
          simpl in *. apply (rwP dommP) in H5 as [].
          apply (rwP dommP) in H6 as [].
          rewrite H5 in H4.
          destruct (y0 =P y); subst.
          { inverts H4. }
          destruct (getm ψ y0) eqn:?; inverts H4.
          assert (R x0 y0). { apply H2. rewrite H5 Heqo0 //. split; auto. apply (rwP dommP). eauto. }
          rewrite H4 in Heqo. inverts Heqo.
          destruct (y =P s); subst; auto.
          contradiction.
        * destruct (getm ϕ x0) eqn:?;
          destruct (y0 =P y); subst; inverts H4.
          -- destruct (getm ψ y0) eqn:?; inverts H6.
             rewrite -Heqo1 in Heqo0.
             assert (x0 ∈ domm ϕ). { apply (rwP dommP). rewrite Heqo0 Heqo1. eauto. }
             assert (x0 ∈ domm ϕ /\ getm ϕ x0 = getm ψ y0) by auto.
             apply H2 in H5. rewrite H5 // in Heqo.
          -- destruct (getm ψ y0) eqn:?; inverts H6.
             rewrite -Heqo1 in Heqo0.
             apply (rwP dommP) in H3 as [].
             apply (introF eqP) in n.
             rewrite setmE mapmE n Heqo0 Heqo1 // in H3.
  Qed.

  (** Page 8: Lemma 9. *)
  Lemma lemma9 :
    forall R ϕ ψ t u,
      R ⊆ domm ϕ × domm ψ ->
      is_injective ϕ ->
      is_injective ψ ->
      is_pullback R ϕ ψ ->
      t ∈ Tm (domm ϕ) ->
      u ∈ Tm (domm ψ) ->
      t ≡_α^R u <-> t^ϕ = u^ψ.
  Proof.
    intros.
    apply (rwP fsubsetP) in H3, H4.
    gen R ϕ ψ u. induction t; intros; split; intros;
    destruct u; inverts H5; simpl in *.
    - f_equal.
      eapply IHt; eauto; intros_all.
      + apply injective_update_ϕ. auto.
      + rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply H3. rewrite in_fsetD in_fset1 n H5 //.
      + rewrite !domm_update_ϕ. eapply update_type; eauto.
        intros. apply (rwP andP). auto.
      + apply injective_update_ϕ. auto.
      + apply lemma9'; simpl; eauto.
      + rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s0); subst; auto.
        apply (introF eqP) in n.
        apply H4. rewrite in_fsetD in_fset1 n H5 //.
    - eapply IHt in H7; eauto; intros_all.
      + apply injective_update_ϕ. auto.
      + rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply H3. rewrite in_fsetD in_fset1 n H6 //.
      + rewrite !domm_update_ϕ. eapply update_type; eauto.
        intros. apply (rwP andP). auto.
      + apply injective_update_ϕ. auto.
      + apply lemma9'; simpl; eauto.
      + rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s0); subst; auto.
        apply (introF eqP) in n.
        apply H4. rewrite in_fsetD in_fset1 n H6 //.
    - apply (rwP andP) in H7 as [].
      eapply IHt1 with (ϕ := ϕ) (ψ := ψ) in H5; cycle 1; intros_all; eauto.
      { apply H3. rewrite in_fsetU H8 //. }
      { apply H4. rewrite in_fsetU H8 //. }
      eapply IHt2 with (ϕ := ϕ) (ψ := ψ) in H6; cycle 1; intros_all; eauto.
      { apply H3. rewrite in_fsetU H8 orbT //. }
      { apply H4. rewrite in_fsetU H8 orbT //. }
      rewrite H5 H6 //.
    - eapply IHt1 in H7; cycle 1; intros_all; eauto.
      { apply H3. rewrite in_fsetU H6 //. }
      { apply H4. rewrite in_fsetU H6 //. }
      eapply IHt2 in H8; cycle 1; intros_all; eauto.
      { apply H3. rewrite in_fsetU H6 orbT //. }
      { apply H4. rewrite in_fsetU H6 orbT //. }
      rewrite H7 H8 //.
    - apply (rwP getmP) in H7.
      apply H2 in H7 as [].
      simpl in *. apply (rwP dommP) in H5 as [].
      rewrite H5 in H6. rewrite H5 -H6 //.
    - rewrite <- (rwP getmP).
      assert (s ∈ fset1 s). { rewrite in_fset1 //. }
      apply H3, (rwP dommP) in H5 as [].
      assert (s0 ∈ fset1 s0). { rewrite in_fset1 //. }
      apply H4, (rwP dommP) in H6 as [].
      rewrite H5 H6 /= in H7. subst.
      apply H2. split.
      + simpl. apply (rwP dommP). eauto.
      + rewrite H5 H6 //.
  Qed.

  Lemma identity_is_pullback :
    forall ϕ,
      is_injective ϕ ->
      is_pullback (1__(domm ϕ)) ϕ ϕ.
  Proof.
    intros.
    repeat (split; intros).
    - rewrite /fmap_to_Prop mkfmapfE in H0.
      destruct (x ∈ domm ϕ) eqn:?; rewrite Heqb in H0; inverts H0. auto.
    - rewrite /fmap_to_Prop mkfmapfE in H0.
      destruct (x ∈ domm ϕ) eqn:?; rewrite Heqb in H0; inverts H0. auto.
    - destruct H0.
      simpl in *. rewrite /fmap_to_Prop mkfmapfE H0.
      apply (rwP injectivemP) in H0; auto.
      apply H0 in H1; subst; auto.
  Qed.

  (** Page 7: Proposition 8. *)
  Proposition to_de_Bruijn_chooses_canonical_representations :
    forall t u ϕ,
      is_injective ϕ ->
      t ∈ Tm (domm ϕ) ->
      u ∈ Tm (domm ϕ) ->
      t ≡_α u <-> t^ϕ = u^ϕ.
  Proof.
    intros.
    split; intros.
    - apply lemma9 with (R := 1__(domm ϕ)); auto.
      + apply identity_type.
      + apply identity_is_pullback. auto.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV t)); auto. intros.
        rewrite mkfmapfE in H3.
        destruct (k ∈ FV t) eqn:?; rewrite Heqb in H3; inverts H3.
        apply (rwP fsubsetP) in H0.
        apply H0 in Heqb.
        rewrite mkfmapfE Heqb //.
    - eapply lemma9 with (R := 1__(domm ϕ)) in H2; auto.
      + apply α_equivalent'_implies_α_equivalent. eauto.
      + apply identity_type.
      + apply identity_is_pullback. auto.
  Qed.

  #[local] Reserved Notation "'↑_' c '^' d dBt" (at level 40, c at level 0, d at level 0).

  Fixpoint de_Bruijn_shift d c dBt : de_Bruijn_term :=
    match dBt with
    | de_Bruijn_variable k =>
      if k < c
      then k
      else k + d
    | de_Bruijn_abstraction dBt =>
      de_Bruijn_abstraction (↑_(c + 1)^d dBt)
    | de_Bruijn_application dBt dBu =>
      de_Bruijn_application (↑_c^d dBt) (↑_c^d dBu)
    end

  where "'↑_' c '^' d dBt" := (de_Bruijn_shift d c dBt).

  #[local] Notation "'↑^' d dBt" := (↑_0^d dBt) (at level 40, d at level 0).

  Example TAPL_6_2_2_1 : ↑^2 (de_Bruijn_abstraction (de_Bruijn_abstraction (de_Bruijn_application 1 (de_Bruijn_application 0 2)))) = de_Bruijn_abstraction (de_Bruijn_abstraction (de_Bruijn_application 1 (de_Bruijn_application 0 4))).
  Proof. reflexivity. Qed.

  Example TAPL_6_2_2_2 : ↑^2 (de_Bruijn_abstraction (de_Bruijn_application (de_Bruijn_application 0 1) (de_Bruijn_abstraction (de_Bruijn_application (de_Bruijn_application 0 1) 2)))) = de_Bruijn_abstraction (de_Bruijn_application (de_Bruijn_application 0 3) (de_Bruijn_abstraction (de_Bruijn_application (de_Bruijn_application 0 1) 4))).
  Proof. reflexivity. Qed.

  Lemma TAPL_6_2_3 :
    forall n dBt c d,
      dBt ∈ Tm^db n ->
      ↑_c^d dBt ∈ Tm^db (n + d).
  Proof.
    rewrite /in_mem /=.
    intros.
    gen n c d. induction dBt; intros; repeat rewrite /in_mem /=.
    - eapply IHdBt in H; eauto.
    - apply (rwP andP) in H as [].
      rewrite <- (rwP (@andP (Tm^db (n + d) (↑_c^d dBt1)) (Tm^db (n + d) (↑_c^d dBt2)))).
      split; eauto.
    - rewrite /nat_to_pred.
      destruct (n < c) eqn:?.
      + rewrite ltn_addr //.
      + rewrite ltn_add2r //.
  Qed.

  #[local] Reserved Notation "'[' j '↦' s ']' dBt" (at level 40, j at level 200, s at level 200).

  Fixpoint de_Bruijn_substitution j (s : de_Bruijn_term) dBt : de_Bruijn_term :=
    match dBt with
    | de_Bruijn_variable k =>
      if k == j
      then s
      else de_Bruijn_variable k
    | de_Bruijn_abstraction t1 =>
      de_Bruijn_abstraction ([j + 1 ↦ ↑^1 s]t1)
    | de_Bruijn_application t1 t2 =>
      de_Bruijn_application ([j↦s]t1) ([j↦s]t2)
    end

  where "'[' j '↦' s ']' dBt" := (de_Bruijn_substitution j s dBt).

  Section TAPL_6_2_5.
    Variables (a b x y : 𝒱) (ϕ_a ϕ_b : nat) (ϕ : {fmap 𝒱 → nat}).

    Hypotheses (HFV_distinct : uniq (a :: b :: x :: y :: nil))
               (Hϕ_inj : is_injective ϕ)
               (Hϕ_a : ϕ a ϕ_a)
               (Hϕ_b : ϕ b ϕ_b).

    Let Hbx : b <> x.
    Proof.
      intros_all. subst.
      pose proof HFV_distinct.
      rewrite /= !mem_seq2 eq_refl andbF // in H.
    Qed.

    Let Hay : a <> y.
    Proof.
      intros_all. subst.
      pose proof HFV_distinct.
      rewrite /= mem_seq3 eq_refl !orbT // in H.
    Qed.

    Let Hby : b <> y.
    Proof.
      intros_all. subst.
      pose proof HFV_distinct.
      rewrite /= mem_seq2 eq_refl orbT andbF // in H.
    Qed.

    Example TAPL_6_2_5_1 :
      let t := application (variable b) (abstraction x (abstraction y (variable b))) in
      let u := variable a in
      [ϕ_b↦u^ϕ] (t^ϕ) = (t[b⟵u])^ϕ.
    Proof.
      intros. subst t u.
      repeat rewrite /= !setmE !mapmE ?eq_refl. repeat f_equal.
      { rewrite Hϕ_b !eq_refl /= Hϕ_a //. }
      apply (introF eqP) in Hbx, Hby.
      rewrite !addn1 Hbx Hby Hϕ_b /= !setmE !mapmE eq_refl.
      destruct (a =P Fresh
                     (codomm_Tm_set
                        (((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                               (variable a)]) [x,
                                                                                               (variable
                                                                                                  (Fresh
                                                                                                     (codomm_Tm_set
                                                                                                        ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                                                                                                              (variable a)]))))]))).
      { pose proof Fresh_correct
             (codomm_Tm_set
                        (((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                               (variable a)]) [x,
                                                                                               (variable
                                                                                                  (Fresh
                                                                                                     (codomm_Tm_set
                                                                                                        ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                                                                                                              (variable a)]))))])).
        rewrite -e /= in H. rewrite <- (rwP codomm_Tm_setPn) in H.
        exfalso. apply (H (variable a)).
        simpl. split.
        { rewrite in_fset1 eq_refl //. }
        apply (rwP codommP). exists b.
        rewrite !setmE mapmE eq_refl Hbx //. }
      rewrite setmE mapmE.
      destruct
        (a =P Fresh
              (codomm_Tm_set ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b, (variable a)]))).
      { pose proof Fresh_correct
             (codomm_Tm_set ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b, (variable a)])).
        rewrite -e in H.
        rewrite <- (rwP codomm_Tm_setPn) in H.
        exfalso. apply (H (variable a)).
        simpl. split.
        { rewrite in_fset1 eq_refl //. }
        apply (rwP codommP). exists b.
        rewrite setmE mapmE eq_refl //. }
      rewrite Hϕ_a //.
    Qed.

    Example TAPL_6_2_5_2 :
      let t := application (variable b) (abstraction x (abstraction y (variable b))) in
      let u := application (variable a) (abstraction y (variable a)) in
      [ϕ_b↦u^ϕ] (t^ϕ) = (t[b⟵u])^ϕ.
    Proof.
      intros. subst t u.
      repeat rewrite /= !setmE !mapmE ?eq_refl. repeat f_equal.
      { rewrite Hϕ_b !eq_refl /= Hϕ_a //. }
      apply (introF eqP) in Hbx, Hay, Hby.
      rewrite !addn1 Hbx Hay Hby Hϕ_a Hϕ_b eq_refl /= !setmE !mapmE Hay !setmE !mapmE.
      set (m := (mapm variable (identity (b |: fset1 b :\ y :\ x)))[b,application (variable a) (abstraction y (variable a))]).
      destruct (a =P Fresh (codomm_Tm_set (m[x,variable (Fresh (codomm_Tm_set m))]))).
      { pose proof Fresh_correct (codomm_Tm_set (m[x,variable (Fresh (codomm_Tm_set m))])).
        rewrite -e /= in H. rewrite <- (rwP codomm_Tm_setPn) in H.
        exfalso. apply (H (application (variable a) (abstraction y (variable a)))). simpl. split.
        { rewrite in_fsetU in_fset1 eq_refl //. }
        apply (rwP codommP). exists b.
        rewrite !setmE mapmE Hbx eq_refl //. }
      rewrite !setmE !mapmE.
      destruct (a =P Fresh (codomm_Tm_set m)).
      { pose proof Fresh_correct (codomm_Tm_set m).
        rewrite -e in H.
        rewrite <- (rwP codomm_Tm_setPn) in H.
        exfalso. apply (H (application (variable a) (abstraction y (variable a)))). simpl. split.
        { rewrite in_fsetU in_fset1 eq_refl //. }
        apply (rwP codommP). exists b.
        rewrite setmE mapmE eq_refl //. }
      rewrite Hϕ_a //.
    Qed.
  End TAPL_6_2_5.

  Lemma TAPL_6_2_6 :
    forall j n dBt dBu,
      dBt ∈ Tm^db n ->
      dBu ∈ Tm^db n ->
      j <= n ->
      [j↦dBu]dBt ∈ Tm^db n.
  Proof.
    intros.
    gen j n dBu. induction dBt; intros; simpl in *.
    - apply IHdBt; auto.
      + rewrite addn1 //.
      + apply TAPL_6_2_3 with (c := 0) (d := 1) in H0.
        rewrite addn1 // in H0.
    - apply (rwP andP) in H as [].
      eapply IHdBt1 with (dBu := dBu) in H; eauto.
      eapply IHdBt2 with (dBu := dBu) in H2; eauto.
      rewrite /in_mem /= H H2 //.
    - destruct (n =P j); subst; auto.
  Qed.

  Lemma codomm_Tm_set_identity :
    forall X,
      codomm_Tm_set (1__X) = X.
  Proof.
    intros.
    apply eq_fset. intros_all.
    apply Bool.eq_iff_eq_true. split; simpl; intros.
    - apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H0 as [].
      rewrite mapmE mkfmapfE in H0.
      destruct (x1 ∈ X) eqn:?; rewrite Heqb in H0; inverts H0.
      rewrite in_fset1 in H. apply (rwP eqP) in H. subst. auto.
    - apply (rwP codomm_Tm_setP).
      exists (variable x). split.
      + rewrite /= in_fset1 eq_refl //.
      + rewrite codomm_identity'.
        apply (rwP imfsetP). exists x; auto.
  Qed.

  Lemma variable_substitution_as_α_equivalent' :
    forall t x y,
      y ∉ FV t ->
      t[x⟵variable y] ≡_α^(1__(FV t :\ x))⦅y,x⦆ t.
  Proof.
    intros.
    replace ((1__(FV t :\ x))⦅y,x⦆) with (((1__(FV t :\ x))⦅x,y⦆)ᵒ); cycle 1.
    { rewrite update_converse.
      - rewrite converse_identity //.
      - apply partial_bijection_identity. }
    simpl.
    replace ((mapm variable (identity (FV t)))[x,variable y]) with (mapm variable ((1__(FV t))⦅x,y⦆)); cycle 1.
    { apply eq_fmap. intros_all.
      rewrite setmE !mapmE mkfmapfE unionmE remmE rem_valmE setmE /= mkfmapfE.
      destruct (x0 =P x); subst; auto.
      destruct (x0 ∈ FV t) eqn:?; rewrite Heqb //.
      destruct (y =P x0); subst; auto.
      rewrite Heqb // in H. }
    replace ((identity (FV t :\ x))⦅x,y⦆ᵒ) with ((identity (FV t))⦅x,y⦆ᵒ); cycle 1.
    { apply eq_fmap. intros_all.
      rewrite !update_converse.
      - rewrite !unionmE !remmE !rem_valmE !setmE /=.
        destruct (x0 =P y); subst; auto.
        rewrite !converse_identity !mkfmapfE !in_fsetD !in_fset1.
        destruct (x0 =P x); subst; auto.
        destruct (x ∈ FV t) eqn:?; rewrite Heqb // eq_refl //.
      - apply partial_bijection_identity.
      - apply partial_bijection_identity. }
    apply lemma7.
    - apply partial_bijection_update, partial_bijection_identity.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      apply (rwP dommP).
      rewrite unionmE remmE rem_valmE setmE /= mkfmapfE.
      destruct (x0 =P x); subst; simpl; eauto.
      rewrite H0.
      destruct (y =P x0); subst; simpl; eauto.
      rewrite H0 // in H.
  Qed.

  Lemma update_as_update_ϕ :
    forall t u x y ϕ,
      is_injective ϕ ->
      t ∈ Tm (domm ϕ ∪ {y}) ->
      u ∈ Tm (domm ϕ ∪ {x}) ->
      t ≡_α^(1__(domm ϕ))⦅y,x⦆ u ->
      t^ϕ^+y = u^ϕ^+x.
  Proof.
    unfold Tm.
    intros.
    apply (rwP fsubsetP) in H0, H1.
    apply lemma9 with (R := (1__(domm ϕ))⦅y,x⦆); auto.
    - rewrite !domm_set ![_ |: _]fsetUC. apply update_type.
      + simpl. intros.
        rewrite /fmap_to_Prop mkfmapfE in H3.
        destruct (a ∈ domm ϕ) eqn:?; rewrite Heqb0 in H3; inverts H3.
        rewrite domm_map Heqb0 //.
      + rewrite domm_map. apply identity_type.
    - apply injective_update_ϕ. auto.
    - apply injective_update_ϕ. auto.
    - eapply lemma9'; eauto.
      + apply identity_type.
      + eapply identity_is_pullback; eauto.
    - rewrite /Tm /in_mem domm_set domm_map /= fsetUC. apply (rwP fsubsetP). intros_all. apply H0. auto.
    - rewrite /Tm /in_mem domm_set domm_map /= fsetUC. apply (rwP fsubsetP). intros_all. apply H1. auto.
  Qed.

  Lemma to_de_Bruijn_with_indistinguishable_ϕ :
    forall ϕ ψ t,
      (forall x, x ∈ FV t -> getm ϕ x = getm ψ x) ->
      t^ϕ = t^ψ.
  Proof.
    intros.
    gen ϕ ψ. induction t; intros; simpl in *; f_equal.
    - apply IHt. simpl. intros.
      rewrite !setmE !mapmE.
      destruct (x =P s); subst; auto.
      f_equal.
      apply H.
      apply (introF eqP) in n.
      rewrite in_fsetD H0 in_fset1 n //.
    - apply IHt1. simpl. intros.
      apply H.
      rewrite in_fsetU H0 //.
    - apply IHt2. simpl. intros.
      apply H.
      rewrite in_fsetU H0 orbT //.
    - f_equal. apply H. rewrite in_fset1 eq_refl //.
  Qed.

  Lemma update_ϕ_remm :
    forall ϕ x,
      (remm ϕ x)^+x = ϕ^+x.
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite !setmE !mapmE remmE.
    destruct (x0 =P x); subst; auto.
  Qed.

  Lemma substitution_id :
    forall t x,
      t[x⟵variable x] ≡_α t.
  Proof.
    intros.
    destruct (x ∈ FV t) eqn:?; cycle 1.
    { apply substitution_law1. rewrite Heqb //. }
    transitivity (⦇η__(FV t)⦈ t); cycle 1.
    { apply monad_substitution1. rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all. auto. }
    apply lift_substitution_indistinguishable_substitutions; simpl; intros.
    - rewrite /in_mem /Tm /=. apply (rwP fsubsetP). intros_all.
      rewrite in_fsetI !domm_set domm_map !domm_mkfmapf !in_fsetU !in_fset1 !in_fset orbC H //.
    - rewrite setmE mapmE mkfmapfE H.
      destruct (x0 =P x); subst; reflexivity.
  Qed.

  Lemma injective_remm_ϕ :
    forall ϕ x,
      is_injective ϕ ->
      is_injective (remm ϕ x).
  Proof.
    intros.
    simpl.
    rewrite <- (rwP injectivemP). intros_all.
    rewrite domm_rem in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
    apply negbTE in H0.
    rewrite !remmE H0 in H1.
    destruct (x2 =P x); subst.
    - apply (rwP dommP) in H2 as []. rewrite H1 // in H2.
    - apply (rwP injectivemP) in H. apply H in H1; auto.
  Qed.

  Lemma substitution_as_update_ϕ :
    forall ϕ t x y,
      is_injective ϕ ->
      t ∈ Tm (domm ϕ) ->
      y ∉ FV t ->
      (t[x⟵variable y])^ϕ^+y = t^ϕ^+x.
  Proof.
    unfold Tm.
    intros.
    apply (rwP fsubsetP) in H0.
    destruct (x =P y); subst.
    { apply to_de_Bruijn_chooses_canonical_representations.
      - apply injective_update_ϕ. auto.
      - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
        rewrite FV_noop_substitute // in H2.
        apply H0 in H2.
        rewrite domm_set domm_map in_fsetU in_fset1 orbC H2 //.
      - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
        apply H0 in H2.
        rewrite domm_set domm_map in_fsetU in_fset1 orbC H2 //.
      - apply substitution_id. }
    eapply update_as_update_ϕ; eauto.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      rewrite in_fsetU in_fset1 orbC.
      destruct (x0 =P y); subst; auto.
      apply H0.
      destruct (x ∈ FV t) eqn:?.
      + rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1 in H2.
        apply (rwP orP) in H2 as [].
        * apply (rwP andP) in H2 as []. auto.
        * apply (rwP eqP) in H2. subst. contradiction.
      + rewrite FV_noop_substitute // Heqb // in H2.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
      apply H0 in H2.
      rewrite in_fsetU in_fset1 H2 //.
    - apply α_equivalent'_supermap with (R__sub := (1__(FV t :\ x))⦅y,x⦆).
      + simpl. intros.
        rewrite unionmE remmE rem_valmE setmE mkfmapfE in_fsetD in_fset1 /= in H2.
        rewrite unionmE remmE rem_valmE setmE mkfmapfE /=.
        destruct (k =P y); subst; auto.
        destruct (k =P x); subst.
        { inverts H2. }
        destruct (k ∈ FV t) eqn:?; cycle 1.
        { inverts H2. }
        simpl in *.
        destruct (x =P k); subst; inverts H2.
        apply H0 in Heqb.
        apply not_eq_sym, (introF eqP) in n1.
        simpl in *. rewrite Heqb n1 //.
      + apply variable_substitution_as_α_equivalent'. auto.
  Qed.

  Lemma de_Bruijn_substitution_identity :
    forall dBt i,
      [i↦i]dBt = dBt.
  Proof.
    intros.
    gen i. induction dBt; intros;
    simpl; f_equal; auto.
    destruct (n =P i); subst; auto.
  Qed.

  Lemma substitution_noop_if_shadow :
    forall t u x,
      (abstraction x t)[x⟵u] ≡_α abstraction x t.
  Proof.
    intros.
    apply substitution_law1.
    rewrite /= in_fsetD in_fset1 eq_refl //.
  Qed.

  Lemma old_index_after_update_ϕ :
    forall ϕ x i,
      is_injective ϕ ->
      getm ϕ x = Some i ->
      forall y, ~ getm (ϕ^+x) y = Some (S i).
  Proof.
    intros_all.
    rewrite setmE mapmE in H1.
    destruct (y =P x); subst.
    { inverts H1. }
    destruct (getm ϕ y) eqn:?; inverts H1.
    rewrite -Heqo in H0.
    apply (rwP injectivemP) in H.
    apply H in H0; auto.
    apply (rwP dommP). exists i.
    rewrite H0 Heqo //.
  Qed.

  Lemma noop_de_Bruijn_substitution :
    forall ϕ i t dBu,
      t ∈ Tm (domm ϕ) ->
      i ∉ codomm ϕ ->
      let dBt := t^ϕ in
      [i↦dBu]dBt = dBt.
  Proof.
    intros.
    subst dBt.
    apply (rwP fsubsetP) in H.
    rewrite <- (rwP (@codommPn _ _ ϕ i)) in H0.
    gen ϕ i dBu. induction t; intros;
    simpl; f_equal.
    - apply IHt; simpl; intros_all.
      { rewrite domm_set domm_mapi in_fsetU in_fset1.
        destruct (x =P s); subst; auto.
        simpl in *. apply H.
        apply (introF eqP) in n.
        rewrite in_fsetD in_fset1 n H1 //. }
      rewrite setmE mapmE addn1.
      destruct (k' =P s); subst; auto.
      destruct (getm ϕ k') eqn:?; auto.
      pose proof H0 k'. rewrite Heqo // in H1.
    - apply IHt1; auto. simpl in *. intros_all.
      apply H. rewrite in_fsetU H1 //.
    - apply IHt2; auto. simpl in *. intros_all.
      apply H. rewrite in_fsetU H1 orbT //.
    - destruct (getm ϕ s) eqn:?.
      + pose proof H0 s. rewrite Heqo in H1.
        apply negbTE in H1.
        cbn in *. rewrite H1 //.
      + destruct i; auto.
        apply (rwP dommPn) in Heqo.
        pose proof H s ltac:(rewrite /= in_fset1 eq_refl //).
        simpl in H1. rewrite H1 // in Heqo.
  Qed.

  (* See https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.8.7101&rep=rep1&type=pdf. *)
  Definition decr (s : {fset nat}) : {fset nat} :=
    predn @: (s :\ 0).

  (* TODO Overload [FV] notation to include this. *)
  Fixpoint de_Bruijn_FV dBt : {fset nat} :=
    match dBt with
    | de_Bruijn_abstraction dBt =>
      decr (de_Bruijn_FV dBt)
    | de_Bruijn_application dBt1 dBt2 =>
      de_Bruijn_FV dBt1 ∪ de_Bruijn_FV dBt2
    | de_Bruijn_variable n =>
      fset1 n
    end.

  #[local] Notation FV' := de_Bruijn_FV.

  Lemma FV'_as_FV :
    forall ϕ t,
      t ∈ Tm (domm ϕ) ->
      FV' (t^ϕ) = pimfset (getm ϕ) (FV t).
  Proof.
    intros.
    apply (rwP fsubsetP) in H.
    apply eq_fset. intros_all.
    gen x ϕ. induction t; intros; simpl in *.
    - assert (t ∈ Tm (domm (ϕ^+s))).
      { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
        rewrite domm_set domm_mapi in_fsetU in_fset1.
        destruct (x0 =P s); subst; auto.
        apply H.
        apply (introF eqP) in n.
        rewrite in_fsetD in_fset1 n H0 //. }
      apply (rwP fsubsetP) in H0.
      pose proof (fun i => @IHt i _ H0).
      apply Bool.eq_iff_eq_true. split; intros.
      + apply (rwP pimfsetP).
        apply (rwP imfsetP) in H2 as [].
        rewrite !in_fsetD !in_fset1 in H2.
        apply (rwP andP) in H2 as [].
        destruct x0.
        { inverts H2. }
        simpl in H3. subst. clear H2.
        pose proof H1 (x0.+1). rewrite H4 in H2.
        symmetry in H2. apply (rwP pimfsetP) in H2 as [].
        rewrite setmE mapmE in H3.
        destruct (x =P s); subst.
        { inverts H3. }
        apply (introF eqP) in n.
        assert (x ∈ domm ϕ).
        { apply H. rewrite in_fsetD in_fset1 n H2 //. }
        apply (rwP dommP) in H5 as [].
        rewrite H5 in H3. inverts H3.
        exists x; auto.
        rewrite in_fsetD in_fset1 n H2 //.
      + apply (rwP pimfsetP) in H2 as [].
        rewrite in_fsetD in_fset1 in H2. apply (rwP andP) in H2 as [].
        apply (rwP imfsetP).
        exists (x.+1); auto.
        rewrite !in_fsetD !in_fset1 (H1 (x.+1)) /=.
        apply (rwP pimfsetP). exists x0; auto.
        apply negbTE in H2.
        rewrite setmE mapmE H2 H3 //.
    - rewrite in_fsetU.
      apply Bool.eq_iff_eq_true. split; intros.
      + apply (rwP pimfsetP).
        apply (rwP orP) in H0 as [].
        * rewrite IHt1 in H0.
          -- apply (rwP pimfsetP) in H0 as [].
             exists x0; auto. rewrite in_fsetU H0 //.
          -- intros_all. apply H. rewrite in_fsetU H0 //.
        * rewrite IHt2 in H0.
          -- apply (rwP pimfsetP) in H0 as [].
             exists x0; auto. rewrite in_fsetU H0 orbT //.
          -- intros_all. apply H. rewrite in_fsetU H0 orbT //.
      + apply (rwP orP).
        apply (rwP pimfsetP) in H0 as [].
        rewrite in_fsetU in H0. apply (rwP orP) in H0 as [].
        * left. rewrite IHt1.
          -- apply (rwP pimfsetP). eauto.
          -- intros_all. apply H. rewrite in_fsetU H2 //.
        * right. rewrite IHt2.
          -- apply (rwP pimfsetP). eauto.
          -- intros_all. apply H. rewrite in_fsetU H2 orbT //.
    - rewrite in_fset1.
      apply Bool.eq_iff_eq_true. split; intros.
      + apply (rwP eqP) in H0. subst.
        assert (s ∈ domm ϕ). { apply H. rewrite in_fset1 eq_refl //. }
        apply (rwP dommP) in H0 as [].
        apply (rwP (@pimfsetP _ _ _ (fset1 s) _)). exists s.
        * rewrite in_fset1 eq_refl //.
        * rewrite H0 //.
      + apply (rwP (@pimfsetP _ _ _ (fset1 s) _)) in H0 as [].
        rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst.
        rewrite H1 eq_refl //.
  Qed.

  Lemma noop_de_Bruijn_substitution' :
    forall ϕ i x t dBu,
      is_injective ϕ ->
      t ∈ Tm (domm ϕ) ->
      getm ϕ x = Some i ->
      x ∉ FV t ->
      let dBt := t^ϕ in
      [i↦dBu]dBt = dBt.
  Proof.
    intros.
    subst dBt.
    apply (rwP fsubsetP) in H0.
    gen ϕ x i dBu. induction t; intros;
    simpl in *.
    - f_equal.
      rewrite in_fsetD in_fset1 negb_and negbK in H2.
      destruct (x =P s); subst.
      + pose proof old_index_after_update_ϕ _ H H1.
        apply noop_de_Bruijn_substitution.
        * rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros_all.
          rewrite domm_set domm_mapi in_fsetU in_fset1.
          destruct (x =P s); subst; auto.
          apply (introF eqP) in n.
          apply H0. rewrite in_fsetD in_fset1 n H4 //.
        * rewrite <- (rwP (@codommPn _ _ (ϕ^+s) _)). intros.
          apply negbT, Bool.not_true_iff_false. intros_all.
          apply (rwP eqP) in H4.
          apply H3 with k'. rewrite -addn1 //.
      + pose proof old_index_after_update_ϕ _ H H1.
        erewrite IHt; eauto.
        * apply injective_update_ϕ. auto.
        * intros_all.
          rewrite domm_set domm_mapi in_fsetU in_fset1.
          destruct (x0 =P s); subst; auto.
          apply (introF eqP) in n0.
          apply H0. rewrite in_fsetD in_fset1 n0 H4 //.
        * apply (introF eqP) in n.
          rewrite setmE mapmE n H1 /= addn1 //.
    - rewrite in_fsetU negb_or in H2. apply (rwP andP) in H2 as [].
      erewrite IHt1; cycle 1; eauto.
      { intros_all. apply H0. rewrite in_fsetU H4 //. }
      erewrite IHt2; cycle 1; eauto.
      intros_all. apply H0. rewrite in_fsetU H4 orbT //.
    - assert (s ∈ domm ϕ). { apply H0. rewrite in_fset1 eq_refl //. }
      apply (rwP dommP) in H3 as []. rewrite H3 /=.
      destruct (x0 =P i); subst; auto.
      rewrite -H3 in H1.
      apply (rwP injectivemP) in H. apply H in H1.
      + subst. rewrite in_fset1 eq_refl // in H2.
      + apply (rwP dommP). rewrite H1. eauto.
  Qed.

  Lemma update_substitution_reorder' :
    forall f x x' t t',
      x <> x' ->
      f[x,t][x',t'] = f[x',t'][x,t].
  Proof.
    intros.
    apply eq_fmap. intros_all.
    rewrite !setmE.
    destruct (x0 =P x); subst; auto.
    apply (introF eqP) in H. rewrite H //.
  Qed.

  (** Page 8: "I leave it to the reader to show that -^ϕ preserves substitution, i.e. it maps substitutions to named terms as given here to substitution on de Bruijn terms."

      This is the only result not yet formalized.
   *)
  Lemma TAPL_6_2_8 :
    forall ϕ t u x,
      fsubset (FV t ∪ FV u ∪ {x}) (domm ϕ) ->
      is_injective ϕ ->
      (t[x⟵u])^ϕ = [odflt 0 (getm ϕ x)↦u^ϕ](t^ϕ).
  Proof.
  Admitted.
End AlphaFacts.
