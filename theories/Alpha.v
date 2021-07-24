(* TODO
   - Name hypotheses.
   - Use [Hint Extern]s or [Lemma]s to clean up proofs.
   - Clean up ordering of definitions/lemmas/parameters/notations/etc.
   - Remove [bool]/[Prop] output distinctions?
     - Alternately, why is [\in] sometimes required for bool predicates instead of [∈]?
   - Implement [𝒱] and [Alpha] concretely (with both [string] and [nat]?).
   - Remove dead code.
   - Add documentation for [`≡_α] notations, and define them globally instead of redefining them.
   - Improve names of lemmas/theorems/etc.
   - Standardize naming for [domm], [codomm], [co_domm], [co_domain], etc.
   - Create specialized versions of lemmas that use e.g. [domm f] instead of [X] and [codomm_Tm_set f] instead of [Y].
   - Set [Hint Mode]s correctly and remove unnecessary casts (and the [via] notation). *)

From Coq Require Import Classes.RelationClasses Lia Lists.List Program.Equality Setoid ssreflect.
From mathcomp Require Import choice eqtype seq ssrbool ssrfun ssrnat.
From deriving Require Import deriving.
From extructures Require Import fmap fset ord.
From AlphaPearl Require Import Util.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

Module Alpha.
  #[local] Open Scope fset_scope.

  #[local] Notation "x '∪' '{' y '}'" := (x :|: fset1 y) (at level 52) : fset_scope.

  Parameter 𝒱 : ordType.

  Inductive term : Type :=
  | abstraction : 𝒱 -> term -> term
  | application : term -> term -> term
  | variable : 𝒱 -> term.

  #[export] Hint Constructors term : core.

  Canonical term_indType := IndType term [indDef for term_rect].

  Canonical term_eqType := EqType term [derive eqMixin for term].

  Canonical term_choiceType := ChoiceType term [derive choiceMixin for term].

  Canonical term_ordType := OrdType term [derive ordMixin for term].

  Implicit Types (W X Y Z : {fset 𝒱}) (t u : term) (x y z : 𝒱) (R S : {fmap 𝒱 → 𝒱}).

  Fixpoint Tm X t : bool :=
    match t with
    | abstraction x t => t ∈ Tm (X ∪ {x})
    | application t u => (t ∈ Tm X) && (u ∈ Tm X)
    | variable x => x ∈ X
    end.

  (* TODO Use (currently defined below) [∈] notation. *)
  Section in_Tm.
    #[local] Reserved Notation "t '∈' 'Tm' X" (at level 40).

    Inductive in_Tm : {fset 𝒱} -> term -> Prop :=
    | Tm_variable : forall X x,
        x ∈ X : Prop ->
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
    intros.
    simpl in *.
    gen_dep X. induction t; intros;
    rewrite /in_mem /=.
    - destruct (IHt (X ∪ {s})); constructor; intro_all; auto.
      inverts H. auto.
    - destruct (t1 ∈ Tm X) eqn:?; simpl in *; rewrite Heqy.
      + apply (rwP (IHt1 _)) in Heqy.
        destruct (t2 ∈ Tm X) eqn:?; simpl in *; rewrite Heqy0.
        * apply (rwP (IHt2 _)) in Heqy0. constructor. auto.
        * constructor. intro_all. inverts H.
          apply (rwP (IHt1 _)) in H3.
          apply (rwP (IHt2 _)) in H4.
          rewrite H4 // in Heqy0.
      + constructor. intro_all. inverts H.
        apply (rwP (IHt1 _)) in H3.
        apply (rwP (IHt2 _)) in H4.
        rewrite H3 // in Heqy.
    - destruct (s \in X) eqn:?; constructor; auto.
      intro_all. inverts H.
      simpl in *. rewrite H2 // in Heqb.
  Qed.

  #[local] Notation "R '⊆' X '×' Y" :=
    (forall a b, R a b -> (a ∈ X) /\ (b ∈ Y)) (at level 40, X at next level).

  Notation partial_bijection := is_injective.

  Definition update R x y : {fmap 𝒱 → 𝒱} :=
    unionm (remm (rem_valm _ R y) x) [fmap (x, y)].

  #[local] Notation "R '⦅' x ',' y '⦆'" := (update R x y) (at level 0).

  Lemma partial_bijection_update :
    forall R x y,
      partial_bijection R ->
      partial_bijection R⦅x,y⦆.
  Proof.
    rewrite /partial_bijection /=.
    intros.
    apply (rwP (injectivemP _)) in H.
    rewrite <- (rwP (injectivemP _)). intro_all.
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

  Lemma update_type :
    forall X Y R x y,
      (forall a b : 𝒱, R a b -> (a ∈ X : bool) : Prop /\ b ∈ Y) ->
      (R : {fmap 𝒱 → 𝒱}) ⊆ X × Y ->
      R⦅x,y⦆ ⊆ (X ∪ {x}) × (Y ∪ {y}).
  Proof.
    intros.
    rewrite /= !in_fsetU !in_fset1.
    rewrite /fmap_to_Prop /update unionmE remmE setmE rem_valmE /= in H1.
    destruct (a =P x); subst; inverts H1.
    - rewrite eq_refl !orbT //.
    - destruct (getm R a) eqn:?.
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

  Section α_equivalent''.
    #[local] Reserved Notation "t '≡_α^' R u" (at level 40, R at level 0).

    Inductive α_equivalent'' : {fmap 𝒱 -> 𝒱} -> term -> term -> Prop :=
    | α_equivalent''_variable : forall R x y,
        (x, y) ∈ R : Prop ->
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
    - gen_dep R u. induction t; intros;
      destruct u; inverts Heqb; auto;
      apply (rwP andP) in H0 as []; auto.
    - intro_all.
      dependent induction H; inverts Heqb; auto.
      + simpl in *. rewrite H // in H1.
      + apply negbT, (rwP nandP) in H2 as []; apply negbTE in H1; auto.
  Qed.

  Lemma superset_in_Tm :
    forall (X__sub X__super : {fset 𝒱}) t,
      X__sub ⊆ X__super ->
      t ∈ Tm X__sub : Prop ->
      t ∈ Tm X__super : Prop.
  Proof.
    rewrite /in_mem.
    intros.
    gen_dep X__sub X__super. induction t; intros; inverts H0.
    - apply IHt with (X__sub := X__sub ∪ {s}); auto.
      apply (rwP fsubsetP). apply fsubset_fsetU. rewrite <- (rwP fsubsetP). auto.
    - apply (rwP andP) in H2 as [].
      apply (IHt1 X__super) in H0; auto.
      apply (IHt2 X__super) in H1; auto.
      simpl in *.
      rewrite /in_mem /= H0 H1 //.
    - apply H in H2. auto.
  Qed.

  Lemma α_equivalent'_type :
    forall X Y x y R,
      R ⊆ X × Y ->
      (fun t u => t ≡_α^R u) ⊆ Tm X × Tm Y.
  Proof.
    intros.
    gen_dep b R X Y. induction a; intros;
    destruct b; inverts H0.
    - split;
      apply IHa with (X := X ∪ {s}) (Y := Y ∪ {s0}) in H2 as []; auto;
      intros; split; eapply (@update_type X Y _ s s0) in H as []; eauto.
    - apply (rwP andP) in H2 as [].
      eapply IHa1 in H0 as []; eauto.
      eapply IHa2 in H1 as []; eauto.
      simpl in *. rewrite /in_mem /= H0 H1 H2 H3 //.
    - apply (rwP eqP) in H2.
      apply H in H2 as []. auto.
  Qed.

  Class HasCoDomain (A B T : Type) :=
    { has_co_domm :
        forall (F__A F__B : Type) (_ : HasMembers A F__A Prop) (_ : HasMembers B F__B Prop),
          T -> F__A -> F__B -> Prop }.

  Arguments has_co_domm {_} {_} {_} {_} {_} {_} {_} {_} _ _ _.

  #[global] Hint Mode HasCoDomain - - ! : typeclass_instances.

  #[global] Instance function_HasCoDomain (A B : eqType) : HasCoDomain A B (A -> B) :=
    { has_co_domm _ _ _ _ (f : A -> B) P__A P__B := forall a : A, (a : Equality.sort A) ∈ P__A : Prop -> f a ∈ P__B : Prop }.

  (* TODO The domm condition does *not* need to be bidirectional, I don't think. *)
  #[global] Instance fmap_HasCoDomain (A B : ordType) : HasCoDomain A B {fmap A → B} :=
    { has_co_domm _ _ _ _ m P__A P__B := (forall a : A, a ∈ domm m : Prop <-> a ∈ P__A) /\ Forall (fun b => b ∈ P__B) (codomm m) }.

  #[global] Instance partial_function_HasCoDomain (A B : Type) : HasCoDomain A B (A -> option B) :=
    { has_co_domm _ _ _ _ (f : A -> option B) P__A P__B :=
        (forall a, (exists b, f a = Some b) <-> a ∈ P__A) /\ (forall b, (exists a, f a = Some b) -> b ∈ P__B : Prop) }.

  #[local] Notation "f '∈' X '→' Y" :=
    (has_co_domm f X Y) (at level 70, X at next level, Y at next level) : type_scope.

  (* TODO Remove, and also remove explicit type annotations of [: Prop] where possible *)
  #[local] Notation "f '∈' X '→' Y 'via' H" :=
    (@has_co_domm _ _ _ H _ _ _ _ f X Y) (at level 70, X at next level, Y at next level) : type_scope.

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

  Lemma identity_type : forall X, (1__X : {fmap 𝒱 → 𝒱}) ⊆ X × X.
  Proof.
    intros.
    rewrite /identity' /= /fmap_to_Prop mkfmapfE in H.
    destruct (a \in X) eqn:?; rewrite Heqb0 // in H.
    inverts H. auto.
  Qed.

  Lemma identity_type' : forall X, (1__X) ∈ X → X via fmap_HasCoDomain _ _.
  Proof.
    intros.
    repeat (split; intros); simpl in *.
    - apply (rwP dommP) in H as []. rewrite mkfmapfE in H.
      destruct (a \in X) eqn:?; rewrite Heqb in H; inverts H. auto.
    - apply (rwP dommP). rewrite mkfmapfE H. eauto.
    - apply Forall_forall. intros.
      apply In_mem, (rwP codommP) in H as []. rewrite mkfmapfE in H.
      destruct (x0 \in X) eqn:?; rewrite Heqb in H; inverts H; auto.
  Qed.

  Lemma partial_bijection_identity : forall X, partial_bijection (1__X : {fmap 𝒱 → 𝒱}).
  Proof.
    intros.
    rewrite /partial_bijection /fmap_IsInjective /injective /identity' /fmap_𝒱_Identity /identity.
    intros.
    rewrite <- (rwP (injectivemP _)).
    intro_all.
    apply (rwP dommP) in H as [].
    rewrite !mkfmapfE in H, H0.
    destruct (x \in X) eqn:?; rewrite Heqb in H, H0; inverts H.
    destruct (x2 \in X) eqn:?; rewrite Heqb0 in H0; inverts H0.
    auto.
  Qed.

  Definition converse R : {fmap 𝒱 → 𝒱} := invm R.

  #[local] Notation "R 'ᵒ'" := (converse R) (at level 40).

  Lemma converse_type :
    forall X Y R,
      R ⊆ X × Y ->
      R ᵒ ⊆ Y × X.
  Proof.
    intros ? ? ? ?.
    intros.
    rewrite /fmap_to_Prop in H0. apply getm_inv in H0. apply H in H0 as []. auto.
  Qed.

  Lemma converse_closed_under_partial_bijection :
    forall R,
      partial_bijection R ->
      partial_bijection (R ᵒ).
  Proof.
    intros.
    apply (rwP (injectivemP _)) in H.
    simpl. rewrite <- (rwP (injectivemP _)). intro_all.
    apply (rwP dommP) in H0 as []. rewrite H0 in H1.
    symmetry in H1. apply getm_inv in H0, H1. rewrite H0 in H1. inverts H1. auto.
  Qed.

  Definition compose R S : {fmap 𝒱 → 𝒱} :=
    mkfmapfp
      (fun k =>
        match getm R k with
        | Some v => getm S v
        | None => None
        end)
      (domm R).

  #[local] Notation "R ';' S" := (compose R S) (at level 40).

  Lemma compose_type :
    forall X Y Z R S,
      R ⊆ X × Y ->
      S ⊆ Y × Z ->
      R; S ⊆ X × Z.
  Proof.
    intros.
    rewrite /fmap_to_Prop mkfmapfpE in H1.
    destruct (a \in domm R) eqn:?; rewrite Heqb0 // in H1.
    apply (rwP dommP) in Heqb0 as []. rewrite H2 in H1.
    apply H in H2 as []. apply H0 in H1 as []. auto.
  Qed.

  Lemma compose_closed_under_partial_bijection :
    forall R S,
      partial_bijection R ->
      partial_bijection S ->
      partial_bijection (R; S).
  Proof.
    unfold partial_bijection.
    intros.
    apply (rwP (injectivemP _)) in H, H0.
    simpl. rewrite <- (rwP (injectivemP _)). intro_all.
    apply (rwP dommP) in H1 as [].
    rewrite !mkfmapfpE in H1, H2.
    destruct (x \in domm R) eqn:?; rewrite Heqb in H1, H2; cycle 1.
    { inverts H1. }
    apply (rwP dommP) in Heqb as []. rewrite H3 in H1, H2.
    rewrite H1 in H2.
    destruct (x2 \in domm R) eqn:?; rewrite Heqb in H2; cycle 1.
    { inverts H2. }
    apply (rwP dommP) in Heqb as []. rewrite H4 -H1 in H2.
    apply H0 in H2; cycle 1.
    { apply (rwP dommP). eauto. }
    subst.
    rewrite -H3 in H4. apply H in H4; auto.
    apply (rwP dommP). rewrite H3 in H4. eauto.
  Qed.

  Lemma update_identity : forall X x, (1__X) ⦅x,x⦆ = 1__(X ∪ {x}).
  Proof.
    intros.
    apply eq_fmap. intro_all.
    rewrite unionmE mkfmapfE in_fsetU in_fset1 remmE rem_valmE /= setmE mkfmapfE.
    destruct (x0 =P x); subst.
    - rewrite orbT //.
    - destruct (x0 \in X) eqn:?; rewrite Heqb.
      + replace (x == id x0) with false; auto.
        symmetry. apply Bool.not_true_iff_false. intro_all.
        apply (rwP eqP) in H. auto.
      + rewrite emptymE //.
  Qed.

  Lemma update_converse :
    forall R x y,
      partial_bijection R ->
      R⦅x,y⦆ᵒ = R ᵒ⦅y,x⦆.
  Proof.
    intros.
    apply eq_fmap. intro_all.
    rewrite /converse /update !unionmE !remmE !rem_valmE /= !setmE.
    destruct (x0 =P y); subst.
    - apply getm_inv. rewrite invmK.
      + rewrite unionmE remmE rem_valmE setmE eq_refl //.
      + intro_all.
        epose proof @partial_bijection_update _ _ _ H. apply (rwP (injectivemP _)) in H2. apply H2; eauto.
    - destruct (invm R x0) eqn:?; rewrite ?Heqo.
      + apply getm_inv in Heqo.
        destruct (x =P s); subst.
        * apply invm_None.
          { apply partial_bijection_update. auto. }
          rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros.
          rewrite unionmE remmE rem_valmE setmE.
          destruct (k' =P s); subst.
          -- apply Bool.negb_true_iff, Bool.not_true_iff_false. intro_all.
            apply (rwP eqP) in H0. inverts H0. auto.
          -- destruct (getm R k') eqn:?; rewrite ?Heqo0; auto.
            destruct (y =P s0); subst; auto.
            apply Bool.negb_true_iff, Bool.not_true_iff_false. intro_all.
            apply (rwP eqP) in H0. inverts H0.
            apply n0. apply (rwP (injectivemP _)) in H. apply H.
            ++ apply (rwP dommP). eauto.
            ++ rewrite Heqo //.
        * apply getm_inv. rewrite invmK; cycle 1.
          { intro_all.
            epose proof @partial_bijection_update _ _ _ H. apply (rwP (injectivemP _)) in H2. apply H2; eauto. }
          rewrite unionmE remmE rem_valmE setmE.
          replace (s == x) with false; cycle 1.
          { symmetry. apply Bool.not_true_iff_false. intro_all. apply (rwP eqP) in H0. subst. auto. }
          destruct (getm R s) eqn:?; rewrite ?Heqo0.
          -- destruct (y =P s0); subst; inverts Heqo; auto. exfalso. auto.
          -- rewrite Heqo // in Heqo0.
      + apply invm_None in Heqo; auto.
        apply invm_None.
        { apply partial_bijection_update. auto. }
        rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros.
        rewrite unionmE remmE rem_valmE setmE.
        destruct (k' =P x); subst.
        * apply Bool.negb_true_iff, Bool.not_true_iff_false. intro_all. apply (rwP eqP) in H0. inverts H0. auto.
        * destruct (getm R k') eqn:?; rewrite ?Heqo0 //.
          destruct (y =P s); subst; auto.
          rewrite <- (rwP (@codommPn _ _ R x0)) in Heqo.
          apply Bool.negb_true_iff, Bool.not_true_iff_false. intro_all.
          apply (rwP eqP) in H0. inverts H0. pose proof (Heqo k'). rewrite Heqo0 eq_refl // in H0.
  Qed.

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
      destruct (x \in domm (R⦅x,y⦆)) eqn:?; rewrite Heqb // in H.
      apply (rwP dommP) in Heqb as []. rewrite H0 in H.
      rewrite !unionmE !remmE !rem_valmE !setmE !eq_refl /= in H, H0.
      destruct (x0 =P y); subst; inverts H; auto.
      inverts H0. contradiction.
    - apply (introF eqP) in n. rewrite n mkfmapfpE.
      rewrite mkfmapfpE in H.
      destruct (k \in domm (R⦅x,y⦆)) eqn:?; rewrite Heqb // in H.
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

  Proposition α_equivalent'_identity :
    forall X t,
      t ∈ Tm X : Prop ->
      t ≡_α^(1__X) t.
  Proof.
    intros.
    gen_dep X. induction t; intros;
    rewrite /in_mem in H; inverts H.
    - apply IHt in H1. rewrite /= update_identity //.
    - apply (rwP andP) in H1 as [].
      apply IHt1 in H. apply IHt2 in H0.
      rewrite /= H H0 //.
    - rewrite /= mkfmapfE H1 //.
  Qed.

  Proposition α_equivalent'_converse :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      u ≡_α^(R ᵒ) t.
  Proof.
    intros.
    gen_dep R u. induction t; intros;
    destruct u; inverts H0.
    - apply IHt in H2.
      + rewrite /= -update_converse //.
      + apply partial_bijection_update. auto.
    - apply (rwP andP) in H2 as [].
      apply IHt1 in H0; auto. apply IHt2 in H1; auto.
      rewrite /= H0 H1 //.
    - simpl. rewrite <- (rwP eqP). apply getm_inv. rewrite invmK.
      + apply (rwP eqP). auto.
      + apply (rwP (injectivemP _)). auto.
  Qed.

  Lemma α_equivalent'_supermap :
    forall (R__sub R__super : {fmap 𝒱 → 𝒱}) t u,
      (forall (k v : 𝒱), getm R__sub k = Some v -> getm R__super k = Some v) ->
      t ≡_α^R__sub u ->
      t ≡_α^R__super u.
  Proof.
    intros.
    gen_dep R__sub R__super u. induction t; intros;
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
    - apply (rwP eqP), H in H2. rewrite /= H2 //.
  Qed.

  Proposition α_equivalent'_compose :
    forall R S t u v,
      t ≡_α^R u ->
      u ≡_α^S v ->
      t ≡_α^(R;S) v.
  Proof.
    intros.
    gen_dep u v R S. induction t; intros;
    destruct u, v; inverts H; inverts H0.
    - apply IHt with (S := S⦅s0,s1⦆) (v := v) in H2; auto.
      apply α_equivalent'_supermap with (R__super := (R;S)⦅s,s1⦆) in H2; cycle 1.
      { intros. eapply update_compose; eauto. }
      rewrite /= H2 //.
    - apply (rwP andP) in H1 as [], H2 as [].
      apply IHt1 with (R := R) (S := S) (v := v1) in H1; auto.
      apply IHt2 with (R := R) (S := S) (v := v2) in H2; auto.
      rewrite /= H1 H2 //.
    - apply (rwP eqP) in H1, H2.
      rewrite /= mkfmapfpE.
      assert (exists s0, getm R s = Some s0) by eauto. apply (rwP dommP) in H. rewrite H H2.
      rewrite <- (rwP eqP). auto.
  Qed.

  Lemma identity_supermap :
    forall (X__sub X__super : {fset 𝒱}),
      X__sub ⊆ X__super ->
      forall k v : 𝒱, getm (1__X__sub) k = Some v -> getm (1__X__super) k = Some v.
  Proof.
    intros.
    rewrite mkfmapfE in H0. rewrite mkfmapfE.
    destruct (k \in X__sub) eqn:?; rewrite Heqb // in H0. inverts H0.
    apply H in Heqb. simpl in *. rewrite Heqb //.
  Qed.

  Lemma compose_identity_right : forall R, R; (1__(codomm R)) = R.
  Proof.
    intros.
    apply eq_fmap. intro_all.
    rewrite mkfmapfpE.
    destruct (x \in domm R) eqn:?; rewrite Heqb.
    - apply (rwP dommP) in Heqb as []. rewrite H mkfmapfE.
      destruct (x0 \in codomm R) eqn:?; rewrite Heqb //.
      apply negbT in Heqb.
      rewrite <- (rwP (@codommPn _ 𝒱 _ _)) in Heqb.
      pose proof Heqb x. rewrite H eq_refl // in H0.
    - apply negbT, (rwP dommPn) in Heqb. auto.
  Qed.

  Lemma compose_identity_left : forall R, (1__(domm R)); R = R.
  Proof.
    intros.
    apply eq_fmap. intro_all.
    rewrite mkfmapfpE mkfmapfE domm_mkfmapf in_fset.
    destruct (x \in domm R) eqn:?; rewrite Heqb //.
    apply negbT, (rwP dommPn) in Heqb. auto.
  Qed.

  Lemma domm_identity : forall X, domm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    intros.
    apply eq_fset. intro_all.
    destruct (x \in X) eqn:?.
    - apply (rwP dommP). exists x. rewrite mkfmapfE Heqb //.
    - apply negbTE. rewrite <- (rwP dommPn).
      rewrite mkfmapfE. rewrite Heqb //.
  Qed.

  Lemma codomm_identity : forall X, codomm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    intros.
    apply eq_fset. intro_all.
    destruct (x \in X) eqn:?.
    - apply (rwP codommP). exists x. rewrite mkfmapfE Heqb //.
    - apply negbTE. rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intro_all.
      apply (introN eqP). intro_all.
      rewrite mkfmapfE in H.
      destruct (k' \in X) eqn:?; rewrite Heqb0 in H; inverts H.
      rewrite Heqb0 // in Heqb.
  Qed.

  Lemma compose_identity :
    forall X Y,
      (1__X); (1__Y) = 1__(X ∩ Y).
  Proof.
    intros.
    apply eq_fmap. intro_all.
    rewrite mkfmapfpE !mkfmapfE in_fsetI.
    destruct (x \in X) eqn:?; rewrite Heqb;
    rewrite domm_identity Heqb // mkfmapfE.
    destruct (x \in Y) eqn:?; rewrite Heqb0 //.
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
    apply eq_fmap. intro_all.
    rewrite mkfmapfE.
    destruct (x \in X) eqn:?; rewrite Heqb.
    - apply getm_inv. rewrite invmK.
      + rewrite mkfmapfE Heqb //.
      + apply (rwP (injectivemP _)). apply partial_bijection_identity.
    - apply invm_None.
      + apply partial_bijection_identity.
      + rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intro_all.
        apply (introN eqP). intro_all.
        rewrite mkfmapfE in H.
        destruct (k' \in X) eqn:?; rewrite Heqb0 in H; inverts H.
        rewrite Heqb0 // in Heqb.
  Qed.

  Fixpoint free_variables t : {fset 𝒱} :=
    match t with
    | abstraction x t => free_variables t :\ x
    | application t1 t2 => free_variables t1 ∪ free_variables t2
    | variable x => fset1 x
    end.

  Lemma in_Tm_free_variables : forall t, t ∈ Tm (free_variables t) : Prop.
  Proof.
    intros.
    rewrite /in_mem /=.
    induction t; simpl.
    - apply superset_in_Tm with (X__sub := free_variables t); auto.
      intros.
      simpl in *. rewrite in_fsetU in_fsetD in_fset1 H.
      destruct (a =P s); auto.
    - apply (rwP (@andP (t1 \in Tm (free_variables t1 ∪ free_variables t2))
  (t2 \in Tm (free_variables t1 ∪ free_variables t2)))). split.
      + apply superset_in_Tm with (X__sub := free_variables t1); auto. apply (rwP fsubsetP), fsubsetUl.
      + apply superset_in_Tm with (X__sub := free_variables t2); auto. apply (rwP fsubsetP), fsubsetUr.
    - rewrite in_fset1 eq_refl //.
  Qed.

  Lemma in_Tm_iff_superset_free_variables : forall X t, free_variables t ⊆ X <-> (t ∈ Tm X).
  Proof.
    intros.
    split; intros.
    - rewrite /in_mem /=.
      gen_dep X. induction t; intros; simpl in *.
      + apply IHt. intros.
        destruct (a =P s); subst.
        * rewrite in_fsetU in_fset1 eq_refl orbT //.
        * assert (a \in free_variables t :\ s).
          { rewrite in_fsetD H0 in_fset1 andbT.
            apply negbT, Bool.not_true_iff_false. intro_all.
            apply (rwP eqP) in H1. subst. auto. }
          apply H in H1.
          rewrite in_fsetU H1 //.
      + apply (rwP (@andP (Tm X t1) (Tm X t2))). split;
        (apply IHt1 || apply IHt2); intros; apply H; rewrite in_fsetU H0 ?orbT //.
      + apply H. rewrite in_fset1 eq_refl //.
    - gen_dep X. induction t; intros;
      rewrite /in_mem /= in H, H0.
      + rewrite in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
        apply IHt in H; auto.
        simpl in *. rewrite in_fsetU in_fset1 in H. apply (rwP orP) in H as []; auto.
        apply (rwP eqP) in H. subst. rewrite eq_refl // in H0.
      + apply (rwP andP) in H as [].
        rewrite in_fsetU in H0. apply (rwP orP) in H0 as []; eauto.
      + rewrite mem_seq1 in H0. apply (rwP eqP) in H0. subst. auto.
  Qed.

  Definition α_equivalent t u := exists X, t ≡_α^(1__X) u.

  Infix "≡_α" := α_equivalent (at level 40).

  Corollary α_equivalent_reflexive : forall t, t ≡_α t.
  Proof.
    intros.
    exists (free_variables t).
    apply α_equivalent'_identity, in_Tm_free_variables.
  Qed.

  Corollary α_equivalent_transitive :
    forall t u v,
      t ≡_α u ->
      u ≡_α v ->
      t ≡_α v.
  Proof.
    intros ? ? ? [Xtu Htu] [Xuv Huv].
    pose proof α_equivalent'_compose _ _ _ _ _ Htu Huv.
    rewrite compose_identity in H.
    unfold α_equivalent. eauto.
  Qed.

  Corollary α_equivalent_symmetric :
    forall t u,
      t ≡_α u ->
      u ≡_α t.
  Proof.
    intros ? ? [].
    apply α_equivalent'_converse in H.
    - rewrite converse_identity in H. unfold α_equivalent. eauto.
    - apply partial_bijection_identity.
  Qed.

  #[global] Instance α_equivalent_Equivalence : Equivalence α_equivalent.
  Proof.
    split; intro_all.
    - apply α_equivalent_reflexive.
    - apply α_equivalent_symmetric. auto.
    - eapply α_equivalent_transitive; eauto.
  Qed.

  Implicit Types f g : {fmap 𝒱 → term}.

  Definition update_substitution (A : Type) : {fmap 𝒱 → A} -> 𝒱 -> A -> {fmap 𝒱 → A} := @setm _ _.

  #[local] Notation "f '[' x ',' t ']'" := (update_substitution f x t) (at level 10, x at next level, t at next level).

  Lemma update_substitution_type :
    forall X Y f x t,
      f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
      t ∈ Tm Y : Prop ->
      f[x,t] ∈ (X ∪ {x}) → Tm Y via fmap_HasCoDomain 𝒱 term_ordType.
  Proof.
    intros.
    destruct H.
    repeat (split; intros); simpl in *.
    - apply (rwP dommP) in H2 as [].
      rewrite setmE in H2.
      destruct (a =P x); subst.
      + inverts H2. rewrite in_fsetU in_fset1 eq_refl orbT //.
      + assert (a \in domm f) by (eapply (rwP dommP); eauto). apply H in H3. rewrite in_fsetU H3 //.
    - apply (rwP dommP).
      rewrite setmE.
      rewrite in_fsetU in_fset1 in H2. apply (rwP orP) in H2 as [].
      + apply H in H2. apply (rwP dommP) in H2 as [].
        destruct (a =P x); subst; eauto.
      + apply (rwP eqP) in H2. subst.
        rewrite eq_refl. eauto.
    - apply Forall_forall. intros. apply In_mem, (rwP codommP) in H2 as [].
      rewrite setmE in H2.
      destruct (x1 =P x); subst.
      + inverts H2. auto.
      + rewrite -> Forall_forall in H1.
        assert (x0 \in codomm f) by (eapply (rwP codommP); eauto). apply In_mem, H1 in H3. auto.
  Qed.

  Definition codomm_Tm_set f : {fset 𝒱} := ⋃_(i ∈ codomm f) (free_variables i).

  Lemma codomm_Tm_setP :
    forall {f} {x},
      reflect (exists t, x ∈ free_variables t /\ t ∈ codomm f) (x ∈ codomm_Tm_set f).
  Proof.
    intros.
    destruct (x ∈ codomm_Tm_set f) eqn:?; constructor;
    rewrite /= /codomm_Tm_set in_bigcup in Heqy.
    - apply (rwP hasP) in Heqy as []. exists x0. auto.
    - apply negbT, (rwP hasPn) in Heqy. intros (? & ? & ?).
      apply Heqy in H0. simpl in *. rewrite H // in H0.
  Qed.

  Lemma substitution_type : forall f, f ∈ domm f → Tm (codomm_Tm_set f).
  Proof.
    intros.
    repeat (split; intros); auto.
    rewrite -> Forall_forall. intros.
    apply In_mem in H.
    apply in_Tm_iff_superset_free_variables. intros.
    apply (rwP codomm_Tm_setP). eauto.
  Qed.

  Lemma substitution_type_domm :
    forall X Y f,
      f ∈ X → Tm Y ->
      domm f = X.
  Proof.
    intros.
    destruct H.
    apply eq_fset. intro_all.
    destruct (x \in domm f) eqn:?.
    - apply H in Heqb. auto.
    - symmetry. apply Bool.not_true_iff_false. intro_all.
      apply H in H1. simpl in *. rewrite H1 // in Heqb.
  Qed.

  Lemma substitution_type_codomm :
    forall X Y f,
      f ∈ X → Tm Y ->
      codomm f ⊆ Tm Y.
  Proof.
    intros.
    destruct H. rewrite -> Forall_forall in H1. apply In_mem, H1 in H0. auto.
  Qed.

  Lemma in_codomm_implies_in_Tm_codomm_set :
    forall f t,
      t ∈ codomm f : Prop ->
      t ∈ Tm (codomm_Tm_set f) : Prop.
  Proof.
    intros.
    apply in_Tm_iff_superset_free_variables. intros.
    apply (rwP codomm_Tm_setP). eauto.
  Qed.

  Lemma codomm_Tm_setPn :
    forall {f} {x},
      reflect (forall t, ~ (x ∈ free_variables t /\ t ∈ codomm f)) (x ∉ codomm_Tm_set f).
  Proof.
    intros.
    destruct (x ∉ codomm_Tm_set f) eqn:?;
    rewrite /= /codomm_Tm_set in_bigcup in Heqb;
    constructor; intro_all.
    - destruct H.
      apply negbTE, Bool.not_true_iff_false in Heqb. apply Heqb.
      apply (rwP hasP). exists t; auto.
    - apply Bool.negb_false_iff, (rwP hasP) in Heqb as [].
      apply H with x0. auto.
  Qed.

  Lemma codomm_Tm_set_update_substitution :
    forall f x t,
      x ∉ domm f ->
      codomm_Tm_set (f[x,t]) = codomm_Tm_set f ∪ free_variables t.
  Proof.
    intros.
    apply eq_fset. intro_all.
    rewrite in_fsetU.
    destruct (x0 \in codomm_Tm_set f) eqn:?.
    - apply (rwP codomm_Tm_setP) in Heqb as (? & ? & ?).
      apply (rwP codomm_Tm_setP). exists x1. split; auto.
      simpl in *. apply (rwP codommP) in H1 as [].
      apply (rwP codommP). exists x2.
      rewrite setmE.
      destruct (x2 =P x); subst; auto.
      apply (rwP dommPn) in H. rewrite H // in H1.
    - destruct (x0 \in free_variables t) eqn:?.
      + apply (rwP codomm_Tm_setP). exists t. split; auto.
        simpl in *. apply (rwP codommP). exists x. rewrite setmE eq_refl //.
      + apply negbT in Heqb. rewrite <- (rwP codomm_Tm_setPn) in Heqb.
        apply negbTE. apply (rwP codomm_Tm_setPn). intros ? [].
        simpl in *. apply (rwP codommP) in H1 as [].
        rewrite setmE in H1.
        destruct (x1 =P x); subst.
        { inverts H1. rewrite Heqb0 // in H0. }
        apply Heqb with t0. split; auto.
        apply (rwP codommP). eauto.
  Qed.

  Lemma codomm_Tm_set_update_substitution' :
    forall f x t,
      codomm_Tm_set (f[x,t]) ⊆ (codomm_Tm_set f ∪ free_variables t).
  Proof.
    intros.
    apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
    simpl in *. apply (rwP codommP) in H0 as [].
    rewrite setmE in H0.
    destruct (x1 =P x); subst.
    { inverts H0. rewrite in_fsetU H orbT //. }
    assert (a \in codomm_Tm_set f).
    { apply (rwP codomm_Tm_setP). exists x0. split; auto.
      apply (rwP codommP). eauto. }
    rewrite in_fsetU H1 //.
  Qed.

  Parameter Fresh : {fset 𝒱} -> 𝒱.

  Parameter Fresh_correct : forall X, Fresh X ∉ X.

  #[local] Reserved Notation "'`⦇' f '⦈'".

  (* TODO Calculate [Y] internally (i.e. via [codomm_Tm_set]?) rather than requiring it to
          be passed as an argument?
     UPDATE This might not actually be a good idea, since I think it makes some induction
            hypotheses too specific (since it's no longer possible to use a [Y] from
            [f ∈ X → Tm Y], for example). Maybe have a backup notation for "explicitly pass in
            Y" and let [`⦇_⦈] be the autocomputed case? *)
  Fixpoint lift_substitution f Y t : term :=
    match t with
    | variable x => odflt t (getm f x)
    | application t u => application (`⦇f⦈ Y t) (`⦇f⦈ Y u)
    | abstraction x t =>
      let z := Fresh Y in
      abstraction z (`⦇f[x,variable z]⦈ (Y ∪ {z}) t)
    end

  where "'`⦇' f '⦈'" := (lift_substitution f).

  #[local] Notation "'⦇' f '⦈'" := (lift_substitution f (codomm_Tm_set f)).

  #[global] Instance lift_substitution_Identity : Identity ({fmap 𝒱 → term} -> term -> term) :=
    { identity' X (f : {fmap 𝒱 → term}) := `⦇f⦈ X }.

  Lemma enlarge_codomain :
    forall X (P__sub P__super : term -> Prop) f,
      P__sub ⊆ P__super ->
      f ∈ X → P__sub via fmap_HasCoDomain 𝒱 term_ordType ->
      f ∈ X → P__super via fmap_HasCoDomain 𝒱 term_ordType.
  Proof.
    intros.
    destruct H0. rewrite -> Forall_forall in H1.
    repeat (split; intros).
    - rewrite -H0 //.
    - rewrite H0 //.
    - apply Forall_forall. intros.
      apply H1 in H2. simpl in *. auto.
  Qed.

  Lemma lift_substitution_type' :
    forall X Y f,
      f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
      `⦇f⦈ Y ∈ Tm X → Tm Y via function_HasCoDomain term_ordType term_ordType.
  Proof.
    intro_all.
    rewrite /in_mem /=.
    gen_dep X Y f. induction a; intros.
    - apply (IHa (f[s, variable (Fresh Y)]) (Y ∪ {Fresh Y}) (X ∪ {s})); intro_all; auto.
      apply enlarge_codomain with (P__super := Tm (Y ∪ {Fresh Y})) in H; cycle 1.
      { intros. simpl in *. apply superset_in_Tm with Y; auto. intros. simpl in *. rewrite in_fsetU H2 //. }
      apply update_substitution_type with (x := s) (t := variable (Fresh Y)) in H; auto.
      rewrite /in_mem /= in_fsetU in_fset1 eq_refl orbT //.
    - apply (rwP andP) in H0 as [].
      eapply IHa1 in H0; eauto.
      eapply IHa2 in H1; eauto.
      simpl in *. rewrite /in_mem /= H0 H1 //.
    - destruct H. rewrite -> Forall_forall in H1.
      apply H in H0. apply (rwP (@dommP _ _ f s)) in H0 as [].
      rewrite /= H0.
      assert (x \in codomm f) by (eapply (rwP codommP); eauto).
      apply In_mem, H1 in H2. auto.
  Qed.

  Lemma lift_substitution_type :
    forall X Y f,
      f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
      ⦇f⦈ ∈ Tm X → Tm Y via function_HasCoDomain term_ordType term_ordType.
  Proof.
    intro_all.
    apply superset_in_Tm with (X__sub := codomm_Tm_set f).
    - intros. simpl in *.
      apply (rwP codomm_Tm_setP) in H1 as (? & ? & ?). simpl in *.
      destruct H. rewrite -> Forall_forall in H3.
      apply In_mem, H3 in H2.
      destruct (in_Tm_iff_superset_free_variables Y x).
      apply H5; auto.
    - assert (f ∈ X → Tm (codomm_Tm_set f)).
      { replace X with (domm f); cycle 1.
        { eapply substitution_type_domm; eauto. }
        apply substitution_type. }
      eapply lift_substitution_type'; eauto.
  Qed.

  Lemma update_substitution_identity :
    forall X x u,
      u ∈ Tm X : Prop ->
      (1__X)[x,u] ∈ X ∪ {x} → Tm X via fmap_HasCoDomain 𝒱 term_ordType.
  Proof.
    intro_all.
    repeat split; intros; simpl in *.
    - apply (rwP dommP) in H0 as [].
      rewrite setmE in H0.
      destruct (a =P x); subst.
      + rewrite in_fsetU in_fset1 eq_refl orbT //.
      + rewrite mapmE mkfmapfE in H0.
        destruct (a \in X) eqn:?; rewrite Heqb in H0; inverts H0. rewrite in_fsetU Heqb //.
    - apply (rwP dommP). rewrite setmE mapmE mkfmapfE.
      rewrite in_fsetU in_fset1 in H0. apply (rwP orP) in H0 as []; rewrite H0; eauto.
      destruct (a =P x); subst; simpl; eauto.
    - apply Forall_forall. intros.
      apply In_mem, (rwP codommP) in H0 as [].
      rewrite setmE mapmE mkfmapfE in H0.
      destruct (x1 =P x); subst.
      { inverts H0. auto. }
      destruct (x1 \in X) eqn:?; rewrite Heqb // in H0.
      inverts H0. auto.
  Qed.

  Lemma lift_substitution_update_identity_type :
    forall X x u,
      u ∈ Tm X : Prop ->
      `⦇(1__X : {fmap 𝒱 → term})[x,u]⦈ X ∈ Tm (X ∪ {x}) → Tm X via function_HasCoDomain term_eqType term_eqType.
  Proof.
    intros.
    eapply lift_substitution_type'; eauto.
    apply update_substitution_identity. auto.
  Qed.

  Lemma α_equivalent_update :
    forall X Y R t u x y,
      R ⊆ X × Y ->
      x ∉ X ->
      y ∉ Y ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    intros.
    apply α_equivalent'_supermap with (R__sub := R); auto. intros.
    pose proof H3. apply H in H3 as [].
    rewrite unionmE remmE rem_valmE setmE H4 /=.
    destruct (k =P x); subst.
    { simpl in *. rewrite H3 // in H0. }
    destruct (y =P v); subst; auto.
    simpl in *. rewrite H5 // in H1.
  Qed.

  Lemma α_equivalent_update_reorder :
    forall X Y R t u x y z z',
      R ⊆ X × Y ->
      z ∉ X ->
      z' ∉ Y ->
      t ≡_α^(R⦅x,y⦆) u ->
      t ≡_α^(R⦅z,z'⦆⦅x,y⦆) u.
  Proof.
    intros.
    apply α_equivalent'_supermap with (R__sub := R⦅x,y⦆); auto. intros.
    rewrite unionmE remmE rem_valmE setmE /= in H3.
    repeat rewrite unionmE remmE rem_valmE setmE /=.
    destruct (k =P x); subst; auto.
    destruct (k =P z); subst.
    - destruct (getm R z) eqn:?; cycle 1.
      { inverts H3. }
      destruct (y =P s); subst; inverts H3.
      apply H in Heqo as [].
      simpl in *. rewrite H3 // in H0.
    - destruct (getm R k) eqn:?; cycle 1.
      { inverts H3. }
      destruct (y =P s); subst; inverts H3.
      apply H in Heqo as [].
      destruct (z' =P v); subst.
      { simpl in *. rewrite H4 // in H1. }
      apply (introF eqP) in n1. rewrite /= n1 //.
  Qed.

  Lemma in_update :
    forall R X Y x y z z',
      R ⊆ X × Y ->
      z ∉ X ->
      z' ∉ Y ->
      (x, y) ∈ R : Prop ->
      (x, y) ∈ R⦅z,z'⦆ : Prop.
  Proof.
    intros.
    simpl in *.
    apply (rwP eqP) in H2.
    apply (rwP (@eqP _ _ (Some y))).
    rewrite /update unionmE remmE rem_valmE setmE /= H2.
    destruct (x =P z); subst.
    { apply H in H2 as []. rewrite H2 // in H0. }
    destruct (z' =P y); subst; auto.
    apply H in H2 as []. rewrite H3 // in H1.
  Qed.

  Lemma update_repeat_noop :
    forall R x y,
      R⦅x,y⦆⦅x,y⦆ = R⦅x,y⦆.
  Proof.
    intros.
    apply eq_fmap. intro_all.
    repeat rewrite !unionmE !remmE !rem_valmE !setmE /=.
    destruct (x0 =P x); subst; auto.
    destruct (getm R x0) eqn:?; auto.
    destruct (y =P s); subst; auto.
    apply (introF eqP) in n0. rewrite /= n0 //.
  Qed.

  Lemma α_equivalent'_maps_all_free_variables :
    forall R t u x,
      t ≡_α^R u ->
      x ∈ free_variables t : Prop ->
      exists y, getm R x = Some y /\ y ∈ free_variables u.
  Proof.
    intros.
    gen_dep R u. induction t; intro_all;
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
    - apply (rwP eqP) in H2.
      rewrite /= in_fset1 in H0. apply (rwP eqP) in H0. subst.
      exists s0. rewrite /= in_fset1 eq_refl //.
  Qed.

  Lemma α_equivalent'_maps_all_free_variables' :
    forall R t u y,
      partial_bijection R ->
      t ≡_α^R u ->
      y ∈ free_variables u : Prop ->
      exists x, getm R x = Some y /\ x ∈ free_variables t.
  Proof.
    intros.
    apply α_equivalent'_converse in H0; auto.
    pose proof α_equivalent'_maps_all_free_variables _ _ _ H0 H1 as (? & ? & ?).
    apply getm_inv in H2. eauto.
  Qed.

  Lemma α_equivalent'_implies_related_free_variables :
    forall X Y R t u,
      partial_bijection R ->
      R ∈ X → Y via fmap_HasCoDomain 𝒱 𝒱 ->
      t ≡_α^R u ->
      free_variables u = pimfset (getm R) (free_variables t).
  Proof.
    intros.
    apply eq_fset. intro_all.
    rewrite in_pimfset.
    symmetry.
    destruct (x \in free_variables u) eqn:?.
    - eapply α_equivalent'_maps_all_free_variables' in Heqb as (? & ? & ?); eauto.
      apply (rwP imfsetP). simpl in *. eauto.
    - apply Bool.not_true_iff_false. intro_all.
      apply (rwP imfsetP) in H2 as [].
      eapply α_equivalent'_maps_all_free_variables in H2 as (? & ? & ?); eauto.
      rewrite H2 in H3. inverts H3.
      simpl in *. rewrite H4 // in Heqb.
  Qed.

  Lemma α_equivalent'_bijection_includes_all_free_variables :
    forall R t u,
      t ≡_α^R u ->
      free_variables t ⊆ domm R.
  Proof.
    intros.
    gen_dep R u. induction t; intro_all;
    destruct u; inverts H.
    - rewrite /= in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
      cut (a ∈ domm R⦅s,s0⦆ = true).
      { intros.
        simpl in *. apply (rwP dommP) in H1 as [].
        rewrite unionmE remmE rem_valmE setmE /= in H1.
        destruct (a =P s); subst; auto.
        destruct (getm R a) eqn:?.
        - eapply (rwP dommP). eauto.
        - inverts H1. }
      eapply IHt; eauto.
    - apply (rwP andP) in H2 as [].
      rewrite /= /in_mem /= in_fsetU in H0. apply (rwP orP) in H0 as [].
      apply IHt1 in H; auto. apply IHt2 in H1; auto.
    - apply (rwP eqP) in H2. simpl in *. rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst.
      eapply (rwP dommP). eauto.
  Qed.

  Lemma α_equivalent'_bijection_includes_all_free_variables' :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      free_variables u ⊆ codomm R.
  Proof.
    intros.
    eapply α_equivalent'_converse in H0; eauto.
    rewrite codomm_domm_invm //.
    eapply α_equivalent'_bijection_includes_all_free_variables; eauto.
  Qed.

  Lemma α_equivalent_implies_same_free_variables :
    forall t u,
      t ≡_α u ->
      free_variables u = free_variables t.
  Proof.
    intros.
    destruct H.
    replace (free_variables t) with (pimfset (getm (1__x : {fmap 𝒱 → 𝒱})) (free_variables t)); cycle 1.
    { apply eq_fset. intro_all.
      rewrite in_pimfset.
      destruct (x0 \in free_variables t) eqn:?.
      - apply (rwP imfsetP).
        exists x0; auto.
        rewrite mkfmapfE.
        destruct (x0 \in x) eqn:?; rewrite Heqb0 //.
        apply α_equivalent'_bijection_includes_all_free_variables with (a := x0) in H; auto.
        simpl in *. apply (rwP dommP) in H as []. rewrite mkfmapfE Heqb0 // in H.
      - apply negbTE, (introN imfsetP). intros [].
        rewrite mkfmapfE in H1.
        destruct (x1 \in x) eqn:?; rewrite Heqb0 in H1; inverts H1.
        rewrite H0 // in Heqb. }
    eapply α_equivalent'_implies_related_free_variables; eauto.
    - apply partial_bijection_identity.
    - apply identity_type'.
  Qed.

  Lemma α_equivalent'_with_behaviorally_identical_maps :
    forall R S t u,
      (forall x y, R x y -> x ∈ free_variables t : Prop -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    intros.
    gen_dep R S u. induction t; intros;
    destruct u; inverts H0.
    - apply IHt with (R := R⦅s,s0⦆); auto. intro_all.
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
    - apply (rwP eqP), H in H2.
      + simpl in *. rewrite H2 //.
      + rewrite /= in_fset1 eq_refl //.
  Qed.

  Lemma α_equivalent'_with_free_variables :
    forall t u,
      t ≡_α u ->
      t ≡_α^(1__(free_variables t)) u.
  Proof.
    intros.
    destruct H.
    apply α_equivalent'_with_behaviorally_identical_maps with (R := 1__x); auto.
    intros.
    simpl in *. rewrite /fmap_to_Prop mkfmapfE H1.
    rewrite /fmap_to_Prop mkfmapfE in H0.
    destruct (x0 \in x) eqn:?; rewrite Heqb // in H0.
  Qed.

  Lemma α_equivalent'_with_Tm_set :
    forall X t u,
      t ∈ Tm X : Prop ->
      u ∈ Tm X : Prop ->
      t ≡_α u ->
      t ≡_α^(1__X) u.
  Proof.
    intros.
    destruct H1.
    apply α_equivalent'_with_behaviorally_identical_maps with (R := 1__x); auto.
    intros.
    replace x0 with y in *; cycle 1.
    { rewrite /fmap_to_Prop mkfmapfE in H2. destruct (x0 \in x) eqn:?; rewrite Heqb in H2; inverts H2. auto. }
    rewrite /fmap_to_Prop mkfmapfE in H2.
    destruct (y \in x) eqn:?; rewrite Heqb // in H2.
    rewrite /fmap_to_Prop mkfmapfE.
    assert (free_variables t ⊆ X). { apply in_Tm_iff_superset_free_variables. auto. }
    apply H4 in H3. simpl in *. rewrite H3 //.
  Qed.

  Section substitution_preserves_α_congruence.
    #[local] Notation "a '`≡_α^' R b" :=
      (odflt (variable _) a ≡_α^R odflt (variable _) b) (at level 40, R at level 0).

    #[program] Lemma lemma5 :
      forall R S X X' Y Y' f g,
        f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        g ∈ X' → Tm Y' via fmap_HasCoDomain 𝒱 term_ordType ->
        R ⊆ X × X' ->
        S ⊆ Y × Y' ->
        partial_bijection R ->
        partial_bijection S ->
        (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
        forall x y z z',
          z ∉ Y ->
          z' ∉ Y' ->
          forall w w' : 𝒱, R⦅x,y⦆ w w' -> getm (f[x,variable z]) w `≡_α^(S⦅z,z'⦆) getm (g[y,variable z']) w'.
    Proof.
      intros.
      rewrite /fmap_to_Prop /update unionmE remmE rem_valmE setmE /= in H8.
      rewrite /update_substitution /update !setmE.
      destruct (w =P x); subst.
      - inverts H8.
        rewrite !eq_refl.
        rewrite /= unionmE remmE rem_valmE eq_refl setmE eq_refl //.
      - destruct (getm R w) eqn:?; cycle 1.
        { inverts H8. }
        destruct (y =P s); subst; inverts H8.
        apply not_eq_sym, (introF eqP) in n0. rewrite n0.
        apply H5 in Heqo. inverts Heqo.
        eapply α_equivalent_update; auto.
    Qed.

    Lemma subset_co_domm :
      forall R X X' Y Y',
        R ⊆ X × Y ->
        X ⊆ X' ->
        Y ⊆ Y' ->
        R ⊆ X' × Y'.
    Proof.
      intros.
      apply H in H2 as [].
      apply H0 in H2. apply H1 in H3. auto.
    Qed.

    Lemma subset_domm_substitution :
      forall f x t,
        domm f ⊆ domm (f[x,t]).
    Proof.
      simpl. intros.
      apply (rwP dommP) in H as [].
      apply (rwP dommP).
      rewrite setmE.
      destruct (a =P x); subst; eauto.
    Qed.

    #[program] Proposition substitution_preserves_α_congruence'' :
      forall R S X X' Y Y' f g W W',
        f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        g ∈ X' → Tm Y' via fmap_HasCoDomain 𝒱 term_ordType ->
        R ⊆ X × X' ->
        S ⊆ W × W' ->
        partial_bijection R ->
        partial_bijection S ->
        codomm_Tm_set f ⊆ W ->
        codomm_Tm_set g ⊆ W' ->
        (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
        forall t u, t ≡_α^R u -> `⦇f⦈ W t ≡_α^S `⦇g⦈ W' u.
    Proof.
      intros.
      gen_dep R S X X' Y Y' f g u W W'. induction t; intros;
      destruct u; inverts H8.
      - assert (f ∈ X → Tm W via fmap_HasCoDomain 𝒱 term_ordType).
        { apply enlarge_codomain with (P__sub := Tm (codomm_Tm_set f)).
          - intros. apply superset_in_Tm with (X__sub := codomm_Tm_set f); auto.
          - replace X with (domm f); cycle 1.
            { eapply substitution_type_domm; eauto. }
            apply substitution_type. }
        assert (g ∈ X' → Tm W' via fmap_HasCoDomain 𝒱 term_ordType).
        { apply enlarge_codomain with (P__sub := Tm (codomm_Tm_set g)).
          - intros. apply superset_in_Tm with (X__sub := codomm_Tm_set g); auto.
          - replace X' with (domm g); cycle 1.
            { eapply substitution_type_domm; eauto. }
            apply substitution_type. }
        assert (S ⊆ W × W').
        { intro_all.
          apply H2 in H11 as [].
          simpl in *. split; auto. }
        (unshelve epose proof (lemma5 H8 H9 _ _ _ _ H7 s s0 _ _ (Fresh_correct W) (Fresh_correct W'))); eauto.
        simpl.
        eapply IHt with (Y := Y ∪ {Fresh W}) (Y' := Y' ∪ {Fresh W'}) in H12; eauto.
        + simpl. intros. apply codomm_Tm_set_update_substitution' in H13.
          simpl in *. rewrite in_fsetU in_fset1 in H13. rewrite in_fsetU in_fset1.
          apply (rwP orP) in H13 as [].
          * apply H6 in H13. rewrite H13 //.
          * rewrite H13 orbT //.
        + simpl. intros. apply codomm_Tm_set_update_substitution' in H13.
          simpl in *. rewrite in_fsetU in_fset1 in H13. rewrite in_fsetU in_fset1.
          apply (rwP orP) in H13 as [].
          * apply H5 in H13. rewrite H13 //.
          * rewrite H13 orbT //.
        + apply update_substitution_type.
          apply enlarge_codomain with (P__sub := Tm Y'); eauto.
          * intros. apply superset_in_Tm with (X__sub := Y'); eauto; intros; simpl in *.
            rewrite in_fsetU H14 //.
          * apply H0.
          * rewrite /= in_fsetU in_fset1 eq_refl orbT //.
        + apply update_substitution_type.
          apply enlarge_codomain with (P__sub := Tm Y); eauto.
          * intros. apply superset_in_Tm with (X__sub := Y); eauto; intros; simpl in *.
            rewrite in_fsetU H14 //.
          * apply H.
          * rewrite /= in_fsetU in_fset1 eq_refl orbT //.
        + intros.
          rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in H13.
          destruct (a =P Fresh W); subst.
          * inverts H13.
            do 2 rewrite /= in_fsetU in_fset1 eq_refl orbT //.
          * destruct (getm S a) eqn:?.
            -- apply H11 in Heqo as [].
               destruct (Fresh W' =P s1); subst; inverts H13.
               simpl in *. rewrite !in_fsetU H14 H15 //.
            -- inverts H13.
        + apply partial_bijection_update. auto.
        + intros.
          rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in H13.
          destruct (a =P s); subst.
          * inverts H13.
            do 2 rewrite /= in_fsetU in_fset1 eq_refl orbT //.
          * destruct (getm R a) eqn:?.
            -- apply H1 in Heqo as [].
               destruct (s0 =P s1); subst; inverts H13.
               simpl in *. rewrite !in_fsetU H14 H15 //.
            -- inverts H13.
        + apply partial_bijection_update. auto.
      - apply (rwP andP) in H10 as [].
        eapply IHt1 with (X := X) (Y := Y) (X' := X') (Y' := Y') (f := f) (g := g) (S := S) in H8; eauto.
        eapply IHt2 with (X := X) (Y := Y) (X' := X') (Y' := Y') (f := f) (g := g) (S := S) in H9; eauto.
        rewrite /= H8 H9 //.
      - apply (rwP eqP) in H10.
        pose proof H10. apply H1 in H8 as []. apply H in H8. apply H0 in H9.
        simpl in *.
        apply (rwP dommP) in H8 as []. apply (rwP dommP) in H9 as []. apply H7 in H10.
        rewrite H8 H9 in H10.
        rewrite H8 H9 //.
    Qed.

    #[program] Corollary substitution_preserves_α_congruence_identity' :
      forall X Y f g W1 W2,
        f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        g ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        codomm_Tm_set f ⊆ W1 ->
        codomm_Tm_set g ⊆ W2 ->
        (forall x, (1__X : {fmap 𝒱 → 𝒱}) x x -> getm f x `≡_α^(1__(W1 ∩ W2)) getm g x) ->
        forall t u, t ≡_α^(1__X) u -> `⦇f⦈ W1 t ≡_α^(1__(W1 ∩ W2)) `⦇g⦈ W2 u.
    Proof.
      intros.
      eapply substitution_preserves_α_congruence''; eauto;
      try solve [apply identity_type | apply partial_bijection_identity].
      - intros.
        rewrite /fmap_to_Prop mkfmapfE in_fsetI in H5.
        destruct (a \in W1) eqn:?; inverts H5.
        destruct (a \in W2) eqn:?; inverts H7. auto.
      - intros.
        rewrite /= /identity /fmap_to_Prop mkfmapfE in H5.
        destruct (x \in X) eqn:?; rewrite Heqb // in H5. inverts H5.
        apply H3. rewrite /= /identity /fmap_to_Prop mkfmapfE Heqb //.
    Qed.

    #[program] Corollary substitution_preserves_α_congruence_identity :
      forall X Y f g,
        f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        g ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        (forall x, (1__X : {fmap 𝒱 → 𝒱}) x x -> getm f x `≡_α^(1__Y) getm g x) ->
        forall t u, t ≡_α^(1__X) u -> `⦇f⦈ Y t ≡_α^(1__Y) `⦇g⦈ Y u.
    Proof.
      intros.
      replace (1__Y) with (1__(Y ∩ Y) : {fmap 𝒱 → 𝒱}) by rewrite fsetIid //.
      eapply substitution_preserves_α_congruence_identity'; eauto; intros.
      - destruct H. rewrite -> Forall_forall in H4.
        apply (rwP codomm_Tm_setP) in H3 as (? & ? & ?).
        apply In_mem, H4 in H5.
        eapply in_Tm_iff_superset_free_variables in H5; eauto.
      - destruct H0. rewrite -> Forall_forall in H4.
        apply (rwP codomm_Tm_setP) in H3 as (? & ? & ?).
        apply In_mem, H4 in H5.
        eapply in_Tm_iff_superset_free_variables in H5; eauto.
      - rewrite fsetIid. auto.
    Qed.

    #[local] Notation "a '`≡_α' b" :=
      (odflt (variable _) a ≡_α odflt (variable _) b) (at level 40).

    #[program] Theorem substitution_preserves_α_congruence :
      forall X Y f g,
        f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        g ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        (forall x, x ∈ X : Prop -> getm f x `≡_α getm g x) ->
        forall t u, t ∈ Tm X : Prop -> u ∈ Tm X : Prop -> t ≡_α u -> `⦇f⦈ Y t ≡_α `⦇g⦈ Y u.
    Proof.
      intros.
      pose proof substitution_preserves_α_congruence_identity _ H H0.
      unshelve eassert (forall x, (1__X : {fmap 𝒱 → 𝒱}) x x -> getm f x `≡_α^(1__Y) getm g x); eauto.
      { intros.
        assert (x \in X).
        { rewrite /fmap_to_Prop mkfmapfE in H6.
          destruct (x \in X) eqn:?; rewrite Heqb // in H6. }
        do 2 pose proof H7.
        destruct H, H0. simpl in *.
        apply H, (rwP dommP) in H7 as []. apply H0, (rwP dommP) in H8 as [].
        assert (x0 \in codomm f) by (eapply (rwP codommP); eauto).
        assert (x1 \in codomm g) by (eapply (rwP codommP); eauto).
        rewrite H7 H8.
        rewrite -> Forall_forall in H10, H11.
        apply In_mem, H10 in H12. apply In_mem, H11 in H13.
        apply α_equivalent'_with_Tm_set; auto.
        pose proof H1 x H9. rewrite H7 H8 // in H14. }
      pose proof H5 H6.
      assert (`⦇f⦈ Y t \in Tm Y). { eapply lift_substitution_type'; eauto. }
      assert (`⦇g⦈ Y u \in Tm Y). { eapply lift_substitution_type'; eauto. }
      pose proof H4. apply α_equivalent'_with_Tm_set with (X := X) in H4; auto.
      apply H7 in H4. exists Y. apply H4.
    Qed.
  End substitution_preserves_α_congruence.

  Lemma α_equivalent_implies_both_in_Tm :
    forall X t u,
      t ∈ Tm X : Prop ->
      t ≡_α u ->
      u ∈ Tm X : Prop.
  Proof.
    intros.
    apply α_equivalent_implies_same_free_variables in H0.
    pose proof in_Tm_free_variables t. rewrite <- H0 in H1.
    apply superset_in_Tm with (X__sub := free_variables u); eauto.
    - intros.
      rewrite H0 in H1.
      assert (t \in Tm X). { auto. }
      eapply in_Tm_iff_superset_free_variables in H3; eauto.
      eapply H4; eauto.
      rewrite -H0 //.
    - apply in_Tm_free_variables.
  Qed.

  Theorem substitution_respects_α_equivalence :
    forall X Y f t u,
      f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
      t ∈ Tm X : Prop ->
      u ∈ Tm X : Prop ->
      t ≡_α u ->
      `⦇f⦈ Y t ≡_α `⦇f⦈ Y u.
  Proof.
    intros.
    eapply substitution_preserves_α_congruence; eauto.
    reflexivity.
  Qed.

  Lemma lemma_7 :
    forall X Y (f : {fmap 𝒱 → 𝒱}) t,
      f ∈ X → Y ->
      partial_bijection f ->
      t ∈ Tm X : Prop ->
      `⦇mapm variable f⦈ Y t ≡_α^(f ᵒ) t.
  Proof.
    intros.
    destruct H. rewrite -> Forall_forall in H2.
    gen_dep f X Y. induction t; intros; simpl in *.
    - rewrite /= /update_substitution -mapm_setm -/update_substitution -update_converse //.
      replace (setm f s (Fresh Y)) with (f⦅s,Fresh Y⦆); cycle 1.
      { apply eq_fmap. intro_all.
        rewrite unionmE remmE rem_valmE !setmE /=.
        destruct (x =P s); subst; auto.
        destruct (getm f x) eqn:?; auto.
        destruct (Fresh Y =P s0); subst; auto.
        assert (Fresh Y \in codomm f) by (eapply (rwP codommP); eauto). apply In_mem, H2 in H3.
        pose proof Fresh_correct Y. rewrite /= H3 // in H4. }
      apply IHt with (X := X ∪ {s}); auto.
      + repeat (split; intros).
        * rewrite in_fsetU in_fset1.
          apply (rwP dommP) in H3 as [].
          rewrite unionmE remmE rem_valmE setmE /= in H3.
          destruct (a =P s); subst.
          { rewrite orbT //. }
          destruct (getm f a) eqn:?; cycle 1.
          { inverts H3. }
          destruct (Fresh Y =P s0); subst; inverts H3.
          assert (a \in domm f) by (eapply (rwP dommP); eauto). apply H in H3. rewrite H3 //.
        * rewrite in_fsetU in_fset1 in H3.
          apply (rwP dommP).
          rewrite unionmE remmE rem_valmE setmE /=.
          apply (rwP orP) in H3 as [].
          -- apply H, (rwP dommP) in H3 as [].
             destruct (a =P s); subst; simpl; eauto.
             destruct (getm f a) eqn:?; cycle 1; inverts H3.
             destruct (Fresh Y =P x); subst.
             { assert (Fresh Y \in codomm f) by (eapply (rwP codommP); eauto).
               apply In_mem, H2 in H3. pose proof Fresh_correct Y. rewrite H3 // in H4. }
             simpl. eauto.
          -- apply (rwP eqP) in H3. subst. rewrite eq_refl /=. eauto.
      + intros. apply In_mem, (rwP codommP) in H3 as [].
        rewrite in_fsetU in_fset1.
        rewrite unionmE remmE rem_valmE setmE /= in H3.
        destruct (x0 =P s); subst.
        { inverts H3. rewrite eq_refl orbT //. }
        destruct (getm f x0) eqn:?; cycle 1.
        { inverts H3. }
        destruct (Fresh Y =P s0); subst.
        { assert (Fresh Y \in codomm f) by (eapply (rwP codommP); eauto).
          apply In_mem, H2 in H4. pose proof Fresh_correct Y. rewrite H4 // in H5. }
        inverts H3.
        assert (x \in codomm f) by (eapply (rwP codommP); eauto). apply In_mem, H2 in H3. rewrite H3 //.
      + apply partial_bijection_update. auto.
    - apply (rwP andP) in H1 as []. rewrite <- (rwP andP). split.
      + eapply IHt1; auto. apply H1.
      + eapply IHt2; auto. apply H3.
    - apply α_equivalent'_converse; auto.
      rewrite /= mapmE.
      destruct (getm f s) eqn:?; simpl; auto.
      apply H, (rwP dommP) in H1. destruct H1. rewrite H1 // in Heqo.
  Qed.

  Definition η__ X : {fmap 𝒱 → term} := 1__X.

  Lemma η_type :
    forall X,
      η__ X ∈ X → Tm X via fmap_HasCoDomain 𝒱 term_ordType.
  Proof.
    intro_all.
    rewrite /= /η__.
    repeat (split; intros).
    - apply (rwP dommP) in H as [].
      destruct (a \in X) eqn:?; rewrite mapmE mkfmapfE Heqb // in H.
    - apply (rwP dommP). exists (variable a).
      rewrite mapmE mkfmapfE H //.
    - rewrite -> Forall_forall. intros.
      apply In_mem, (rwP codommP) in H as []. rewrite mapmE mkfmapfE in H.
      destruct (x0 \in X) eqn:?; rewrite Heqb // in H.
      inverts H.
      auto.
  Qed.

  Lemma update_substitution_overwrite :
    forall X Y f x y y',
      f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
      f[x,variable y][x,variable y'] = f[x, variable y'].
  Proof.
    intros.
    apply eq_fmap. intro_all.
    rewrite !setmE.
    destruct (x0 =P x); subst; auto.
  Qed.

  Lemma update_substitution_reorder :
    forall X Y f x x' y y',
      f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
      x <> x' ->
      f[x,variable y][x',variable y'] = f[x',variable y'][x,variable y].
  Proof.
    intros.
    apply eq_fmap. intro_all.
    rewrite !setmE.
    destruct (x0 =P x); subst; auto.
    apply (introF eqP) in H0. rewrite H0 //.
  Qed.

  Lemma α_equivalent'_with_behaviorally_identical_maps' :
    forall R S t u,
      (forall x y, R x y -> x ∈ free_variables t : Prop -> y ∈ free_variables u : Prop -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    intros.
    gen_dep R S u. induction t; intros;
    destruct u; inverts H0.
    - apply IHt with (R := R⦅s,s0⦆); auto. intro_all.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in H0.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
      destruct (x =P s); subst; auto.
      destruct (getm R x) eqn:?; cycle 1.
      { inverts H0. }
      destruct (s0 =P s1); subst; inverts H0.
      apply H in Heqo.
      + rewrite Heqo. apply (introF eqP) in n0. rewrite n0 //.
      + simpl in *. rewrite /= in_fsetD in_fset1 H1. apply (introF eqP) in n. rewrite n //.
      + simpl in *. rewrite /= in_fsetD in_fset1 H3 andbT. apply not_eq_sym, (introF eqP) in n0. rewrite n0 //.
    - apply (rwP andP) in H2 as [].
      simpl. rewrite <- (rwP andP). split;
      simpl in *; (apply IHt1 with R + apply IHt2 with R); auto;
      intros;
      apply H; auto;
      rewrite /= in_fsetU ?H3 ?H4 ?orbT //.
    - apply (rwP eqP), H in H2.
      + simpl in *. rewrite H2 //.
      + rewrite /= in_fset1 eq_refl //.
      + rewrite /= in_fset1 eq_refl //.
  Qed.

  Lemma α_equivalent_update' :
    forall X Y R t u x y,
      x ∉ X ->
      y ∉ Y ->
      t ∈ Tm X : Prop ->
      u ∈ Tm Y : Prop ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    intros.
    apply α_equivalent'_with_behaviorally_identical_maps' with (R := R); auto. intros.
    rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
    destruct (x0 =P x); subst.
    - pose proof in_Tm_iff_superset_free_variables X t as []. apply H8 in H5; auto.
      simpl in *. rewrite H5 // in H.
    - rewrite /fmap_to_Prop in H4. rewrite H4.
      destruct (y =P y0); subst; auto.
      pose proof in_Tm_iff_superset_free_variables Y u as []. apply H8 in H6; auto.
      simpl in *. rewrite H6 // in H0.
  Qed.

  Section lift_substitution_indistinguishable_substitutions.
    #[local] Notation "a '`≡_α' b" :=
      (odflt (variable _) a ≡_α odflt (variable _) b) (at level 40).

    #[local] Notation "a '`≡_α^' R b" :=
      (odflt (variable _) a ≡_α^R odflt (variable _) b) (at level 40, R at level 0).

    #[program] Lemma lift_substitution_indistinguishable_substitutions'' :
      forall R X Y1 Y2 Z1 Z2 f g t W1 W2,
        f ∈ Z1 → Tm Y1 ->
        g ∈ Z2 → Tm Y2 ->
        X ⊆ Z1 ->
        X ⊆ Z2 ->
        t ∈ Tm X : Prop ->
        (forall x, x ∈ X : Prop -> getm f x `≡_α^R getm g x) ->
        codomm_Tm_set f ⊆ W1 ->
        codomm_Tm_set g ⊆ W2 ->
        `⦇f⦈ W1 t ≡_α^R `⦇g⦈ W2 t.
    Proof.
      intros.
      gen_dep R X Y1 Y2 Z1 Z2 f g W1 W2. induction t; intros.
      - set (z1 := Fresh W1).
        set (z2 := Fresh W2).
        set (f' := f[s,variable z1]).
        set (g' := g[s,variable z2]).
        set (X' := X ∪ {s}).
        set (Y1' := Y1 ∪ {z1}).
        set (Y2' := Y2 ∪ {z2}).
        set (Z1' := Z1 ∪ {s}).
        set (Z2' := Z2 ∪ {s}).
        set (W1' := W1 ∪ {z1}).
        set (W2' := W2 ∪ {z2}).
        set (R' := R⦅z1,z2⦆).
        assert (f' ∈ Z1' → Tm Y1').
        { apply update_substitution_type.
          - apply enlarge_codomain with (P__sub := Tm Y1); auto. intros.
            apply superset_in_Tm with (X__sub := Y1); auto. intros.
            simpl in *. rewrite in_fsetU H8 //.
          - rewrite /= in_fsetU in_fset1 eq_refl orbT //. }
        assert (g' ∈ Z2' → Tm Y2').
        { apply update_substitution_type.
          - apply enlarge_codomain with (P__sub := Tm Y2); auto. intros.
            apply superset_in_Tm with (X__sub := Y2); auto. intros.
            simpl in *. rewrite in_fsetU H9 //.
          - rewrite /= in_fsetU in_fset1 eq_refl orbT //. }
        eassert (forall x, x ∈ X' : Prop -> getm f' x `≡_α^R' getm g' x).
        { subst R' f' g' X'. intros.
          rewrite !setmE.
          destruct (x =P s); subst.
          { rewrite /= unionmE remmE rem_valmE setmE /= eq_refl //. }
          destruct H, H0. rewrite -> Forall_forall in f0, f1.
          apply α_equivalent_update' with (X := W1) (Y := W2); auto; try apply Fresh_correct.
          - rewrite /= in_fsetU in_fset1 in H9. apply (rwP orP) in H9 as [].
            + simpl in *. apply H1, i, (rwP dommP) in H as []. rewrite H.
              assert (x0 \in codomm f) by (eapply (rwP codommP); eauto).
              simpl in *.
              apply superset_in_Tm with (X__sub := codomm_Tm_set f); auto.
              apply in_codomm_implies_in_Tm_codomm_set. auto.
            + apply (rwP eqP) in H. subst. contradiction.
          - rewrite /= in_fsetU in_fset1 in H9. apply (rwP orP) in H9 as [].
            + simpl in *. apply H2, i0, (rwP dommP) in H as []. rewrite H.
              assert (x0 \in codomm g) by (eapply (rwP codommP); eauto).
              apply superset_in_Tm with (X__sub := codomm_Tm_set g); auto.
              apply in_codomm_implies_in_Tm_codomm_set in H0. auto.
            + apply (rwP eqP) in H. subst. contradiction.
          - apply H4.
            rewrite /= in_fsetU in_fset1 in H9. apply (rwP orP) in H9 as []; auto.
            apply (rwP eqP) in H. subst. contradiction. }
        assert (X' ⊆ Z1').
        { intros.
          rewrite /= in_fsetU in_fset1.
          rewrite /= in_fsetU in_fset1 in H10. apply (rwP orP) in H10 as [].
          - apply H1 in H10. simpl in *. rewrite H10 //.
          - rewrite H10 orbT //. }
        assert (X' ⊆ Z2').
        { intros.
          rewrite /= in_fsetU in_fset1.
          rewrite /= in_fsetU in_fset1 in H11. apply (rwP orP) in H11 as [].
          - apply H2 in H11. simpl in *. rewrite H11 //.
          - rewrite H11 orbT //. }
        assert (codomm_Tm_set f' ⊆ W1').
        { intro_all.
          apply (rwP codomm_Tm_setP) in H12 as (? & ? & ?).
          simpl in *. apply (rwP codommP) in H13 as [].
          rewrite setmE in H13.
          destruct (x0 =P s); subst.
          { inverts H13. rewrite /= in_fset1 in H12. apply (rwP eqP) in H12. subst.
            rewrite in_fsetU in_fset1 eq_refl orbT //. }
          assert (a \in W1).
          { apply H5, (rwP codomm_Tm_setP). exists x. split; auto. eapply (rwP codommP); eauto. }
          rewrite in_fsetU H14 //. }
        assert (codomm_Tm_set g' ⊆ W2').
        { intro_all.
          apply (rwP codomm_Tm_setP) in H13 as (? & ? & ?).
          simpl in *. apply (rwP codommP) in H14 as [].
          rewrite setmE in H14.
          destruct (x0 =P s); subst.
          { inverts H14. rewrite /= in_fset1 in H13. apply (rwP eqP) in H13. subst.
            rewrite in_fsetU in_fset1 eq_refl orbT //. }
          assert (a \in W2).
          { apply H6, (rwP codomm_Tm_setP). exists x. split; auto. eapply (rwP codommP); eauto. }
          rewrite /= in_fsetU H15 //. }
        pose proof IHt W2' W1' g' H13 f' H12 Z2' Z1' Y2' H8 Y1' H7 X' H10 H11 H3 R' H9.
        rewrite /= H14 //.
      - simpl in *. apply (rwP andP) in H3 as [].
        apply IHt1 with (f := f) (g := g) (Y1 := Y1) (Y2 := Y2) (Z1 := Z1) (Z2 := Z2) (R := R) (W1 := W1) (W2 := W2) in H3; auto.
        apply IHt2 with (f := f) (g := g) (X := X) (Y1 := Y1) (Y2 := Y2) (Z1 := Z1) (Z2 := Z2) (R := R) (W1 := W1) (W2 := W2) in H5; auto.
        rewrite /= H3 H5 //.
      - simpl in *.
        destruct (getm f s) eqn:?.
        + assert (s \in domm f) by (eapply (rwP dommP); eauto).
          pose proof H3. apply H2, H0, (rwP dommP) in H3 as []. rewrite -Heqo. apply H4. auto.
        + apply H1, H, (rwP dommP) in H3 as []. rewrite Heqo // in H3.
    Qed.

    #[program] Lemma lift_substitution_indistinguishable_substitutions' :
      forall X Y1 Y2 Z1 Z2 f g t,
        f ∈ Z1 → Tm Y1 ->
        g ∈ Z2 → Tm Y2 ->
        X ⊆ Z1 ->
        X ⊆ Z2 ->
        t ∈ Tm X : Prop ->
        (forall x, x ∈ X : Prop -> getm f x `≡_α getm g x) ->
        `⦇f⦈ Y1 t ≡_α `⦇g⦈ Y2 t.
    Proof.
      intros.
      set (W := codomm_Tm_set f ∪ codomm_Tm_set g).
      assert (codomm_Tm_set f ⊆ Y1).
      { simpl. intros.
        apply (rwP codomm_Tm_setP) in H5 as (? & ? & ?).
        destruct H. rewrite -> Forall_forall in H7.
        apply In_mem, H7 in H6.
        pose proof in_Tm_iff_superset_free_variables Y1 x. apply H8; auto. }
      assert (codomm_Tm_set g ⊆ Y2).
      { simpl. intros.
        apply (rwP codomm_Tm_setP) in H6 as (? & ? & ?).
        destruct H0. rewrite -> Forall_forall in H8.
        apply In_mem, H8 in H7.
        pose proof in_Tm_iff_superset_free_variables Y2 x. apply H9; auto. }
      eassert (forall x, x ∈ X : Prop -> getm f x `≡_α^(1__W) getm g x).
      { intros.
        apply α_equivalent'_with_Tm_set.
        - simpl in *. apply H1, H, (rwP dommP) in H7 as []. rewrite H7 /=.
          assert (x0 \in codomm f) by (apply (rwP codommP); eauto).
          apply in_codomm_implies_in_Tm_codomm_set in H8.
          apply superset_in_Tm with (codomm_Tm_set f); auto. intros.
          simpl in *. rewrite in_fsetU H9 //.
        - simpl in *. apply H2, H0, (rwP dommP) in H7 as []. rewrite H7 /=.
          assert (x0 \in codomm g) by (apply (rwP codommP); eauto).
          apply in_codomm_implies_in_Tm_codomm_set in H8.
          apply superset_in_Tm with (codomm_Tm_set g); auto. intros.
          simpl in *. rewrite in_fsetU H9 orbT //.
        - apply H4. auto. }
      unshelve epose proof @lift_substitution_indistinguishable_substitutions'' (1__W) X Y1 Y2 Z1 Z2 f g t Y1 Y2 H H0 H1 H2 H3 H7 H5 H6.
      exists W. auto.
    Qed.

    Lemma codomm_Tm_set_correct :
      forall X Y f t,
        f ∈ X → Tm Y ->
        t ∈ Tm X : Prop ->
        `⦇f⦈ Y t ≡_α ⦇f⦈ t.
    Proof.
      intros.
      eapply lift_substitution_indistinguishable_substitutions'; eauto; intros.
      - apply substitution_type_domm in H. rewrite -H. apply substitution_type.
      - reflexivity.
    Qed.

    #[program] Lemma lift_substitution_indistinguishable_substitutions :
      forall X Y1 Y2 Z1 Z2 f g t,
        f ∈ Z1 → Tm Y1 ->
        g ∈ Z2 → Tm Y2 ->
        X ⊆ Z1 ->
        X ⊆ Z2 ->
        t ∈ Tm X : Prop ->
        (forall x, x ∈ X : Prop -> getm f x `≡_α getm g x) ->
        ⦇f⦈ t ≡_α ⦇g⦈ t.
    Proof.
      intros.
      transitivity (`⦇f⦈ Y1 t).
      - symmetry. eapply codomm_Tm_set_correct; eauto.
        apply superset_in_Tm with (X__sub := X); auto.
      - transitivity (`⦇g⦈ Y2 t).
        + eapply lift_substitution_indistinguishable_substitutions'; eauto.
        + eapply codomm_Tm_set_correct; eauto.
          apply superset_in_Tm with (X__sub := X); auto.
    Qed.
  End lift_substitution_indistinguishable_substitutions.

  Lemma free_variables_lift_substitution_subset' :
    forall X Y f t,
      f ∈ X → Tm Y ->
      t ∈ Tm X : Prop ->
      free_variables (`⦇f⦈ Y t) ⊆ Y.
  Proof.
    intro_all.
    apply lift_substitution_type' in H.
    eapply H, in_Tm_iff_superset_free_variables in H0; eauto.
  Qed.

  Section monad_substitution.
    #[local] Notation "a '`≡_α' b" :=
      (odflt (variable _) a ≡_α odflt (variable _) b) (at level 40).

    #[local] Notation "a '`≡_α^' R b" :=
      (odflt (variable _) a ≡_α^R odflt (variable _) b) (at level 40, R at level 0).

    #[program] Lemma lift_update_substitution_compose_substitution_update :
      forall X Y Z f g x z0 z1,
        g ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
        f ∈ Y → Tm Z via fmap_HasCoDomain 𝒱 term_ordType ->
        z1 ∉ Z ->
        z0 ∉ Y ->
        forall v, v \in (X ∪ {x}) -> getm (`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) ∘ g[x,variable z0]) v `≡_α getm ((`⦇f⦈ Z ∘ g)[x,variable z1]) v.
    Proof.
      intros. exists (Z ∪ {z1}). intros.
      rewrite !setmE !mapmE /= !setmE.
      destruct (v =P x).
      { subst. rewrite /= setmE eq_refl. apply α_equivalent'_identity.
        apply superset_in_Tm with (X__sub := fset1 z1).
        - intros. simpl in *. rewrite in_fsetU H4 orbT //.
        - apply in_Tm_free_variables. }
      destruct (getm g v) eqn:?.
      - destruct lift_substitution_indistinguishable_substitutions' with (X := Y) (Y1 := Z ∪ {z1}) (Y2 := Z) (Z1 := Y ∪ {z0}) (Z2 := Y) (f := f[z0,variable z1]) (g := f) (t := t); eauto.
        + apply update_substitution_type.
          * apply enlarge_codomain with (P__sub := Tm Z); eauto. intros.
            apply superset_in_Tm with (X__sub := Z); auto. intros.
            simpl in *. rewrite in_fsetU H5 //.
          * rewrite /= in_fsetU in_fset1 eq_refl orbT //.
        + intros. simpl in *. rewrite in_fsetU H4 //.
        + destruct H. rewrite -> Forall_forall in H4.
          assert (t \in codomm g) by (eapply (rwP codommP); eauto). apply In_mem, H4 in H5. auto.
        + intros.
          rewrite setmE.
          destruct (x0 =P z0); subst.
          * simpl in *. rewrite H4 // in H2.
          * reflexivity.
        + simpl.
          assert (`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) t ≡_α `⦇f⦈ Z t) by (exists x0; auto).
          apply α_equivalent'_with_free_variables in H5.
          apply α_equivalent'_supermap with (R__sub := 1__(free_variables (`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) t))); auto.
          intros.
          rewrite mkfmapfE in H6.
          destruct (k \in free_variables (`⦇ f [z0, (variable z1)] ⦈ (Z ∪ {z1}) t)) eqn:?; rewrite Heqb // in H6.
          inverts H6.
          destruct H. rewrite -> Forall_forall in H6.
          assert (t \in codomm g) by (eapply (rwP codommP); eauto). apply In_mem, H6 in H7.
          apply free_variables_lift_substitution_subset' with (X := Y ∪ {z0}) in Heqb; auto.
          * simpl in *. rewrite mkfmapfE Heqb //.
          * apply update_substitution_type.
            -- apply enlarge_codomain with (P__sub := Tm Z); auto. intros.
               apply superset_in_Tm with (X__sub := Z); auto. intros.
               simpl in *. rewrite in_fsetU H9 //.
            -- apply superset_in_Tm with (X__sub := fset1 z1).
               ++ intros. simpl in *. rewrite in_fsetU H8 orbT //.
               ++ apply in_Tm_free_variables.
          * apply superset_in_Tm with (X__sub := Y); auto. intros.
            simpl in *. rewrite in_fsetU H8 //.
      - simpl in *.
        rewrite in_fsetU in_fset1 in H3. apply (rwP orP) in H3 as [].
        + apply H, (rwP dommP) in H3 as []. rewrite Heqo // in H3.
        + apply (rwP eqP) in H3. subst. contradiction.
    Qed.

    #[program] Proposition monad_substitution' :
      forall X Y Z f g,
        g ∈ X → Tm Y ->
        f ∈ Y → Tm Z ->
        (forall t, t ∈ Tm X : Prop -> `⦇η__ X⦈ X t ≡_α t) /\
        (forall x, x ∈ X : Prop -> getm (`⦇f⦈ X ∘ η__ X) x `≡_α getm f x) /\
        (forall t, t ∈ Tm X : Prop -> (`⦇f⦈ Z ∘ `⦇g⦈ Y) t ≡_α `⦇`⦇f⦈ Z ∘ g⦈ Z t).
    Proof.
      intros.
      repeat split; intros.
      - exists X.
        rewrite -converse_identity.
        apply lemma_7 with (X := X) (Y := X) (f := 1__X); auto.
        + apply identity_type'.
        + apply partial_bijection_identity.
      - simpl in *. rewrite /η__ /= /identity /= !mapmE mkfmapfE H1.
        apply α_equivalent_reflexive.
      - gen_dep f g X Y Z. induction t; intros.
        + set z0 := Fresh Y.
          set z1 := Fresh Z.
          assert ((`⦇f⦈ Z ∘ `⦇g⦈ Y) (abstraction s t) = `⦇f⦈ Z (abstraction z0 (`⦇g[s,variable z0]⦈ (Y ∪ {z0}) t))) by auto.
          assert (`⦇f⦈ Z (abstraction z0 (`⦇g[s,variable z0]⦈ (Y ∪ {z0}) t)) = abstraction z1 ((`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) ∘ `⦇g[s,variable z0]⦈ (Y ∪ {z0})) t)) by auto.
          assert (abstraction z1 ((`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) ∘ `⦇g[s,variable z0]⦈ (Y ∪ {z0})) t) ≡_α abstraction z1 (`⦇`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) ∘ g[s,variable z0]⦈ (Z ∪ {z1}) t)).
          { unshelve epose proof IHt (Z ∪ {z1}) (Y ∪ {z0}) (X ∪ {s}) H1 (g[s,variable z0]) _ (f[z0,variable z1]) _ as [].
            - apply update_substitution_type.
              + apply enlarge_codomain with (P__sub := Tm Y); auto. intros.
                apply superset_in_Tm with (X__sub := Y); auto. intros. simpl in *. rewrite in_fsetU H5 //.
              + rewrite /= in_fsetU in_fset1 eq_refl orbT //.
            - apply update_substitution_type.
              + apply enlarge_codomain with (P__sub := Tm Z); auto. intros.
                apply superset_in_Tm with (X__sub := Z); auto. intros. simpl in *. rewrite in_fsetU H5 //.
              + rewrite /= in_fsetU in_fset1 eq_refl orbT //.
            - apply α_equivalent'_supermap with (R__super := (1__x)⦅z1,z1⦆) in H4.
              + exists x. auto.
              + intros.
                rewrite mkfmapfE in H5.
                rewrite unionmE remmE rem_valmE setmE /= mkfmapfE.
                destruct (k \in x) eqn:?; rewrite Heqb in H5; inverts H5.
                destruct (v =P z1); subst; auto.
                apply not_eq_sym, (introF eqP) in n. rewrite Heqb n //. }
          assert (abstraction z1 (`⦇`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) ∘ g[s,variable z0]⦈ (Z ∪ {z1}) t) ≡_α abstraction z1 (`⦇(`⦇f⦈ Z ∘ g)[s,variable z1]⦈ (Z ∪ {z1}) t)).
          { set (f' := mapm (`⦇f[z0,variable z1]⦈ (Z ∪ {z1})) (g[s,variable z0])).
            set (g' := (mapm (`⦇f⦈ Z) g)[s,variable z1]).
            assert (`⦇f[z0,variable z1]⦈ (Z ∪ {z1}) ∈ Tm (Y ∪ {z0}) → Tm (Z ∪ {z1})).
            { apply lift_substitution_type', update_substitution_type.
              - apply enlarge_codomain with (P__sub := Tm Z); auto. intros.
                apply superset_in_Tm with (X__sub := Z); auto. intros.
                simpl in *. rewrite in_fsetU H6 //.
              - apply superset_in_Tm with (X__sub := fset1 z1).
                + intros.
                  rewrite /= in_fset1 in H5. apply (rwP eqP) in H5. subst.
                  rewrite /= in_fsetU in_fset1 eq_refl orbT //.
                + apply in_Tm_free_variables. }
            assert (f' ∈ (X ∪ {s}) → Tm (Z ∪ {z1})).
            { repeat (split; intros).
              - simpl in *. apply (rwP dommP) in H6 as [].
                rewrite mapmE setmE in H6.
                destruct (a =P s); subst.
                + rewrite in_fsetU in_fset1 eq_refl orbT //.
                + destruct (getm g a) eqn:?; inverts H6.
                  assert (a \in domm g) by (eapply (rwP dommP); eauto). apply H in H6. rewrite in_fsetU H6 //.
              - apply (rwP dommP).
                rewrite mapmE setmE.
                destruct (a =P s); subst.
                + rewrite /= setmE eq_refl. eauto.
                + rewrite /= in_fsetU in_fset1 in H6. apply (rwP orP) in H6 as [].
                  * simpl in *. apply H, (rwP dommP) in H6 as []. rewrite H6 /=. eauto.
                  * apply (rwP eqP) in H6. subst. contradiction.
              - rewrite -> Forall_forall. intros. apply In_mem, (rwP codommP) in H6 as [].
                rewrite mapmE setmE in H6.
                destruct (x0 =P s); subst.
                + rewrite /= setmE eq_refl in H6. inverts H6.
                  apply superset_in_Tm with (X__sub := fset1 z1).
                  * intros. simpl in *. rewrite in_fsetU H6 orbT //.
                  * apply in_Tm_free_variables.
                + destruct (getm g x0) eqn:?; inverts H6.
                  destruct H. rewrite -> Forall_forall in H6.
                  assert (t0 \in codomm g) by (eapply (rwP codommP); eauto). apply In_mem, H6 in H7.
                  apply superset_in_Tm with (X__super := Y ∪ {z0}) in H7; auto. intros.
                  simpl in *. rewrite in_fsetU H8 //. }
            assert (g' ∈ (X ∪ {s}) → Tm (Z ∪ {z1})).
            { repeat (split; intros).
              - simpl in *. apply (rwP dommP) in H7 as [].
                rewrite setmE mapmE in H7.
                destruct (a =P s); subst.
                { inverts H7. rewrite in_fsetU in_fset1 eq_refl orbT //. }
                destruct (getm g a) eqn:?; inverts H7.
                assert (a \in domm g) by (eapply (rwP dommP); eauto). apply H in H7. rewrite in_fsetU H7 //.
              - apply (rwP dommP).
                rewrite setmE mapmE.
                destruct (a =P s); subst; eauto.
                rewrite /= in_fsetU in_fset1 in H7. apply (rwP orP) in H7 as [].
                + simpl in *. apply H, (rwP dommP) in H7 as []. rewrite H7 /=. eauto.
                + apply (rwP eqP) in H7. subst. contradiction.
              - rewrite -> Forall_forall. intros. apply In_mem, (rwP codommP) in H7 as [].
                rewrite setmE mapmE in H7.
                destruct (x0 =P s); subst.
                + inverts H7.
                  apply superset_in_Tm with (X__sub := fset1 z1).
                  * intros. simpl in *. rewrite in_fsetU H7 orbT //.
                  * apply in_Tm_free_variables.
                + destruct (getm g x0) eqn:?; inverts H7.
                  destruct H. rewrite -> Forall_forall in H7.
                  assert (t0 \in codomm g) by (eapply (rwP codommP); eauto). apply In_mem, H7 in H8.
                  apply superset_in_Tm with (X__sub := Z).
                  * intros. simpl in *. rewrite in_fsetU H9 //.
                  * eapply lift_substitution_type'; eauto. }
            pose proof (@lift_update_substitution_compose_substitution_update X Y Z f g s z0 z1 H H0 ltac:(apply Fresh_correct) ltac:(apply Fresh_correct)).
            destruct (@lift_substitution_indistinguishable_substitutions' (X ∪ {s}) _ _ _ _ f' g' t H6 H7 ltac:(auto) ltac:(auto) H1 H8).
            exists x. rewrite /= update_identity.
            destruct (z1 ∈ x) eqn:?.
            - replace (x ∪ {z1}) with x; auto.
              apply eq_fset. intro_all.
              rewrite in_fsetU in_fset1 orbC.
              destruct (x0 =P z1); subst; auto.
            - apply α_equivalent'_supermap with (R__sub := 1__x); auto. intros.
              rewrite mkfmapfE in H10.
              rewrite mkfmapfE in_fsetU in_fset1.
              destruct (k \in x) eqn:?; rewrite Heqb // in H10. }
          assert (abstraction z1 (`⦇(`⦇f⦈ Z ∘ g)[s,variable z1]⦈ (Z ∪ {z1}) t) = `⦇`⦇f⦈ Z ∘ g⦈ Z (abstraction s t)) by auto.
          rewrite H2 H3.
          etransitivity; eauto.
        + simpl in *. apply (rwP andP) in H1 as [].
          eapply IHt1 in H1 as []; eauto.
          eapply IHt2 in H2 as []; eauto.
          exists (x ∪ x0).
          simpl. rewrite <- (rwP andP). split.
          * apply α_equivalent'_supermap with (R__sub := 1__x); auto. intros.
            rewrite mkfmapfE in H3.
            rewrite mkfmapfE in_fsetU.
            destruct (k \in x) eqn:?; rewrite Heqb in H3; inverts H3. auto.
          * apply α_equivalent'_supermap with (R__sub := 1__x0); auto. intros.
            rewrite mkfmapfE in H3.
            rewrite mkfmapfE in_fsetU.
            destruct (k \in x0) eqn:?; rewrite Heqb in H3; inverts H3. rewrite orbT //.
        + simpl in *. rewrite mapmE. eapply H, (rwP dommP) in H1 as []. rewrite H1. reflexivity.
    Qed.

    Lemma function_fmap_compose_has_co_domain :
      forall (f : term -> term) g X Y Z,
        f ∈ Tm Y → Tm Z ->
        g ∈ X → Tm Y ->
        (f ∘ g) ∈ X → Tm Z via fmap_HasCoDomain 𝒱 term_ordType.
    Proof.
      intros.
      destruct H0. rewrite -> Forall_forall in H1.
      repeat split; intros; simpl in *.
      - apply (rwP dommP) in H2 as [].
        rewrite mapmE in H2.
        destruct (getm g a) eqn:?; inverts H2.
        assert (a \in domm g) by (apply (rwP dommP); eauto).
        apply H0 in H2. auto.
      - apply (rwP dommP).
        apply H0, (rwP dommP) in H2 as [].
        exists (f x). rewrite mapmE H2 //.
      - rewrite -> Forall_forall. intros.
        apply In_mem, (rwP codommP) in H2 as [].
        rewrite mapmE in H2.
        destruct (getm g x0) eqn:?; inverts H2.
        assert (t \in codomm g) by (apply (rwP codommP); eauto).
        apply In_mem, H1 in H2.
        apply H in H2. auto.
    Qed.

    #[program] Proposition monad_substitution :
      forall X Y Z f g,
        g ∈ X → Tm Y ->
        f ∈ Y → Tm Z ->
        (forall t, t ∈ Tm X : Prop -> ⦇η__ X⦈ t ≡_α t) /\
        (forall x, x ∈ X : Prop -> getm (⦇f⦈ ∘ η__ X) x `≡_α getm f x) /\
        (forall t, t ∈ Tm X : Prop -> (⦇f⦈ ∘ ⦇g⦈) t ≡_α ⦇⦇f⦈ ∘ g⦈ t).
    Proof.
      intros.
      repeat split; intros.
      - transitivity (`⦇η__ X⦈ X t).
        + symmetry. eapply codomm_Tm_set_correct; eauto. apply η_type.
        + eapply monad_substitution'; eauto.
      - transitivity (odflt (variable x) (getm (`⦇f⦈ X ∘ η__ X) x)).
        + simpl in *. rewrite !mapmE mkfmapfE !H1 /=. reflexivity.
        + eapply monad_substitution'; eauto.
      - transitivity ((`⦇f⦈ Z ∘ ⦇g⦈) t : term).
        { symmetry. eapply codomm_Tm_set_correct; eauto.
          apply superset_in_Tm with (X__sub := codomm_Tm_set g).
          * intros. simpl in *.
            apply (rwP codomm_Tm_setP) in H2 as (? & ? & ?).
            destruct H. rewrite -> Forall_forall in H4.
            simpl in *. apply In_mem, H4 in H3.
            destruct (in_Tm_iff_superset_free_variables Y x).
            eapply H6 with a in H3; auto.
          * eapply lift_substitution_type'; eauto.
            replace X with (domm g); cycle 1.
            { eapply substitution_type_domm; eauto. }
            apply substitution_type. }
        transitivity ((`⦇f⦈ Z ∘ `⦇g⦈ Y) t : term).
        { eapply substitution_respects_α_equivalence; eauto.
          - eapply lift_substitution_type; eauto.
          - eapply lift_substitution_type'; eauto.
          - symmetry. eapply codomm_Tm_set_correct; eauto. }
        transitivity (`⦇`⦇f⦈ Z ∘ g⦈ Z t).
        { eapply monad_substitution'; eauto. }
        transitivity (`⦇⦇f⦈ ∘ g⦈ Z t).
        { eapply lift_substitution_indistinguishable_substitutions'; eauto.
          - eapply function_fmap_compose_has_co_domain; eauto.
            eapply lift_substitution_type'; auto.
          - eapply function_fmap_compose_has_co_domain; eauto.
            eapply lift_substitution_type; auto.
          - intros.
            rewrite /= !mapmE.
            simpl in H, H2. apply H, (rwP dommP) in H2 as [].
            rewrite H2.
            eapply codomm_Tm_set_correct; eauto.
            destruct H. rewrite -> Forall_forall in H3.
            assert (x0 \in codomm g) by (apply (rwP codommP); eauto).
            apply In_mem, H3 in H4. auto. }
        eapply codomm_Tm_set_correct; eauto.
        eapply function_fmap_compose_has_co_domain; eauto.
        apply lift_substitution_type; auto.
    Qed.
  End monad_substitution.

  Notation "t '[' x '=' u ']'" := (⦇(1__(free_variables t))[x,u]⦈ t) (at level 10, x at next level, u at next level).

  #[local] Notation "t '[' x '⟵' u ']'" := (t[x=u]) (at level 10, x at next level, u at next level).

  #[local] Notation FV := free_variables.

  Lemma free_variables_lift_substitution_subset :
    forall X Y f t,
      f ∈ X → Tm Y via fmap_HasCoDomain 𝒱 term_ordType ->
      t ∈ Tm X : Prop ->
      free_variables (⦇f⦈ t) ⊆ Y.
  Proof.
    intro_all.
    pose proof in_Tm_iff_superset_free_variables Y (⦇f⦈ t). apply H2; auto.
    apply lift_substitution_type in H.
    apply H. auto.
  Qed.

  Lemma substitution_law1 :
    forall t u x,
      x ∉ FV t ->
      t[x⟵u] ≡_α t.
  Proof.
    intros.
    transitivity (⦇η__(FV t)⦈ t).
    - apply (@lift_substitution_indistinguishable_substitutions (FV t) (FV t ∪ FV u) (FV t) (FV t ∪ {x}) (FV t)); auto.
      + apply update_substitution_type.
        * apply enlarge_codomain with (P__sub := Tm (FV t)).
          -- intros. apply superset_in_Tm with (X__sub := FV t); auto. intros.
             simpl in *. rewrite in_fsetU H1 //.
          -- apply η_type.
        * apply superset_in_Tm with (X__sub := FV u).
          -- intros. simpl in *. rewrite in_fsetU H0 orbT //.
          -- apply in_Tm_free_variables.
      + apply η_type.
      + intros. simpl in *. rewrite in_fsetU H0 //.
      + apply in_Tm_free_variables.
      + intros. simpl in *.
        rewrite setmE mapmE mkfmapfE H0 /=.
        destruct (x0 =P x); subst.
        * rewrite H0 // in H.
        * reflexivity.
    - eapply monad_substitution; try apply η_type.
      apply in_Tm_free_variables.
  Qed.

  Lemma domm_update_substitution :
    forall f x t,
      domm (f[x,t]) = domm f ∪ {x}.
  Proof.
    intros.
    apply eq_fset. intro_all.
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

  Lemma codomm_update_substitution :
    forall f x t,
      codomm_Tm_set (f[x,t]) = codomm_Tm_set (remm f x) ∪ FV t.
  Proof.
    intros.
    apply eq_fset. intro_all.
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

  Lemma free_variables_lift_substitution :
    forall f t,
      t ∈ Tm (domm f) : Prop ->
      FV (⦇f⦈ t) = ⋃_(u ∈ pimfset (getm f) (FV t)) FV u.
  Proof.
    intros.
    apply eq_fset. intro_all.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true.
    split; intros.
    - apply (rwP hasP).
      gen_dep f. induction t; intros; simpl in *.
      + rewrite in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
        replace (FV (`⦇f[s,variable (Fresh (codomm_Tm_set f))]⦈ (codomm_Tm_set f ∪ {Fresh (codomm_Tm_set f)}) t)) with (FV (⦇f[s,variable (Fresh (codomm_Tm_set f))]⦈ t)) in H1; cycle 1.
        { apply α_equivalent_implies_same_free_variables.
          eapply codomm_Tm_set_correct.
          - apply update_substitution_type; auto.
            + apply enlarge_codomain with (P__sub := Tm (codomm_Tm_set f)).
              * intros. apply superset_in_Tm with (X__sub := codomm_Tm_set f); auto. simpl. intros.
                rewrite in_fsetU H3 //.
              * apply substitution_type.
            + apply superset_in_Tm with (X__sub := fset1 (Fresh (codomm_Tm_set f))).
              * simpl. intros. rewrite in_fsetU H2 orbT //.
              * rewrite /= in_fset1 eq_refl //.
          - auto. }
        apply IHt in H1 as [].
        * apply (rwP (pimfsetP _ _ _)) in H1 as [].
          rewrite setmE in H3.
          destruct (x1 =P s); subst.
          { inverts H3. rewrite in_fset1 in H2. rewrite H2 // in H0. }
          exists x0; auto.
          apply (rwP (pimfsetP _ _ _)). exists x1; auto.
          apply (introF eqP) in n.
          rewrite in_fsetD in_fset1 n H1 //.
        * rewrite domm_update_substitution. auto.
      + apply (rwP andP) in H as [].
        rewrite in_fsetU in H0. apply (rwP orP) in H0 as [].
        * apply IHt1 in H as []; auto.
          apply (rwP (pimfsetP _ _ _)) in H as [].
          exists x0; auto.
          apply (rwP (pimfsetP _ _ _)). exists x1; auto.
          rewrite in_fsetU H //.
        * apply IHt2 in H1 as []; auto.
          apply (rwP (pimfsetP _ _ _)) in H1 as [].
          exists x0; auto.
          apply (rwP (pimfsetP _ _ _)). exists x1; auto.
          rewrite in_fsetU H1 orbT //.
      + apply (rwP dommP) in H as [].
        rewrite H in H0.
        exists x0; auto.
        apply (rwP (pimfsetP (getm f) (fset1 s) x0)). exists s; auto.
        rewrite in_fset1 eq_refl //.
    - apply (rwP hasP) in H0 as [].
      apply (rwP (pimfsetP _ _ _)) in H0 as [].
      gen_dep f. induction t; intros; simpl in *.
      + rewrite in_fsetD in_fset1 in H0. apply (rwP andP) in H0 as [].
        rewrite in_fsetD in_fset1.
        assert (x \in FV (`⦇f[s,variable (Fresh (codomm_Tm_set f))]⦈ (codomm_Tm_set f ∪ {Fresh (codomm_Tm_set f)}) t)).
        { replace (FV (`⦇f[s,variable (Fresh (codomm_Tm_set f))]⦈ (codomm_Tm_set f ∪ {Fresh (codomm_Tm_set f)}) t)) with (FV (⦇f[s,variable (Fresh (codomm_Tm_set f))]⦈ t)); cycle 1.
          { apply α_equivalent_implies_same_free_variables.
            eapply codomm_Tm_set_correct.
            - apply update_substitution_type; auto.
              + apply enlarge_codomain with (P__sub := Tm (codomm_Tm_set f)).
                * intros. apply superset_in_Tm with (X__sub := codomm_Tm_set f); auto. simpl. intros.
                  rewrite in_fsetU H5 //.
                * apply substitution_type.
              + apply superset_in_Tm with (X__sub := fset1 (Fresh (codomm_Tm_set f))).
                * simpl. intros. rewrite in_fsetU H4 orbT //.
                * rewrite /= in_fset1 eq_refl //.
            - auto. }
          apply IHt; auto.
          - rewrite domm_update_substitution. auto.
          - apply negbTE in H0. rewrite setmE H0 //. }
        rewrite H4 andbT.
        apply negbT, (introF eqP). intro_all. subst.
        assert (Fresh (codomm_Tm_set f) \in codomm_Tm_set f).
        { apply (rwP codomm_Tm_setP). exists x0. split; auto. apply (rwP codommP). eauto. }
        pose proof Fresh_correct (codomm_Tm_set f). rewrite H5 // in H6.
      + apply (rwP andP) in H as [].
        rewrite in_fsetU.
        rewrite in_fsetU in H0.
        apply (rwP orP) in H0 as [].
        * eapply IHt1 in H; eauto. rewrite H //.
        * eapply IHt2 in H3; eauto. rewrite H3 orbT //.
      + apply (rwP dommP) in H as [].
        rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst.
        rewrite H in H2. inverts H2. rewrite H //.
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
    apply eq_fset. intro_all.
    apply Bool.eq_iff_eq_true. split; intros.
    - apply (rwP codommP) in H as [].
      rewrite mapmE mkfmapfE in H.
      apply (rwP imfsetP).
      destruct (x0 \in X) eqn:?; rewrite Heqb in H; inverts H.
      eauto.
    - apply (rwP imfsetP) in H as []. subst.
      apply (rwP codommP). exists x0.
      rewrite mapmE mkfmapfE H //.
  Qed.

  Lemma noop_substitution :
    forall t u x,
      x ∉ FV t ->
      t[x⟵u] ≡_α t.
  Proof.
    intros.
    transitivity (⦇1__(FV t)⦈ t).
    { eapply lift_substitution_indistinguishable_substitutions with (X := FV t).
      - apply substitution_type.
      - apply substitution_type.
      - simpl. intros.
        apply (rwP dommP).
        rewrite setmE mapmE mkfmapfE.
        destruct (a =P x); subst; eauto.
        rewrite H0 /=. eauto.
      - intros. rewrite domm_identity' //.
      - apply in_Tm_free_variables.
      - simpl. intros.
        rewrite setmE mapmE mkfmapfE.
        destruct (x0 =P x); subst.
        + rewrite H0 // in H.
        + rewrite H0. reflexivity. }
    eapply monad_substitution; try apply η_type.
    apply in_Tm_free_variables.
  Qed.

  Lemma free_variables_after_substitute :
    forall t u x,
      x ∈ FV t : Prop ->
      FV (t[x⟵u]) = (FV t :\ x) ∪ FV u.
  Proof.
    intros.
    simpl.
    replace (FV t :\ x) with (codomm_Tm_set (remm (1__(FV t)) x)); cycle 1.
    { apply eq_fset. intro_all.
      rewrite in_fsetD in_fset1.
      destruct (x0 =P x); subst.
      - apply negbTE, (rwP codomm_Tm_setPn). simpl. intros ? [].
        apply (rwP codommP) in H1 as [].
        rewrite remmE mapmE mkfmapfE in H1.
        destruct (x0 =P x); subst.
        { inverts H1. }
        destruct (x0 \in FV t) eqn:?; rewrite Heqb in H1; inverts H1.
        rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst. auto.
      - destruct (x0 \in FV t) eqn:?.
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
          destruct (x1 \in FV t) eqn:?; rewrite Heqb0 in H1; inverts H1.
          rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst. rewrite Heqb0 // in Heqb. }
    rewrite free_variables_lift_substitution.
    - apply eq_fset. intro_all.
      apply Bool.eq_iff_eq_true. split; simpl; intros.
      + rewrite in_fsetU.
        rewrite in_bigcup in H0. apply (rwP hasP) in H0 as [].
        apply (rwP (pimfsetP _ _ _)) in H0 as [].
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
          destruct (x2 \in FV t) eqn:?; rewrite Heqb in H1; inverts H1.
          rewrite in_fset1 in H0. apply (rwP eqP) in H0. subst.
          exists (variable x2).
          -- apply (rwP (pimfsetP _ _ _)). exists x2; auto.
             apply (introF eqP) in n.
             rewrite setmE mapmE mkfmapfE n Heqb //.
          -- rewrite /= in_fset1 eq_refl //.
        * exists u; auto.
          apply (rwP (pimfsetP _ _ _)). exists x; auto.
          rewrite setmE mapmE mkfmapfE eq_refl //.
    - apply superset_in_Tm with (X__sub := FV t).
      + simpl. intros.
        apply (rwP dommP).
        rewrite setmE mapmE mkfmapfE.
        destruct (a =P x); subst; eauto.
        rewrite H0 /=. eauto.
      + apply in_Tm_free_variables.
  Qed.

  Lemma free_variables_noop_substitute :
    forall t u x,
      x ∉ FV t : Prop ->
      FV (t[x⟵u]) = FV t.
  Proof.
    intros.
    apply α_equivalent_implies_same_free_variables.
    symmetry. apply noop_substitution. auto.
  Qed.

  Lemma domm_update_identity :
    forall t u x,
      domm ((1__(FV t))[x, u]) = FV t ∪ {x}.
  Proof.
    intros.
    rewrite domm_update_substitution domm_map domm_mkfmapf fsvalK //.
  Qed.

  Lemma codomm_Tm_set_update_identity :
    forall t u x,
      codomm_Tm_set ((1__(FV t))[x, u]) = (FV t :\ x) ∪ FV u.
  Proof.
    intros.
    rewrite codomm_update_substitution. repeat f_equal.
    apply eq_fset. intro_all.
    rewrite in_fsetD in_fset1.
    apply Bool.eq_iff_eq_true. split; intros.
    + apply (rwP codomm_Tm_setP) in H as (? & ? & ?).
      simpl in *. apply (rwP codommP) in H0 as [].
      rewrite remmE mapmE mkfmapfE in H0.
      destruct (x2 =P x); subst.
      { inverts H0. }
      destruct (x2 \in FV t) eqn:?; rewrite Heqb in H0; inverts H0.
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

  Lemma substitution_law2 :
    forall t u v x y,
      x <> y ->
      x ∉ FV v -> (* See Exercise 2.2 in http://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/geuvers.pdf. *)
      t[x⟵u][y⟵v] ≡_α t[y⟵v][x⟵u[y⟵v]].
  Proof.
    intros.
    symmetry.
    transitivity (⦇⦇(1__(FV(⦇(1__(FV t))[y,v]⦈ t)))[x,⦇(1__(FV u))[y,v]⦈ u]⦈ ∘ (1__(FV t))[y,v]⦈ t).
    { destruct (y ∈ FV t) eqn:?. (* TODO Can we remove this [destruct] if we remove the equality
                                              constraint on domains, owing to the observation that
                                              [Y] when [y ∉ FV t] is a subset of [Y] when [y ∈ FV t])? *)
      - eapply monad_substitution with (X := FV t ∪ {y}) (Y := FV t :\ y ∪ FV v ∪ {x}).
        + apply enlarge_codomain with (P__sub := Tm (FV t :\ y ∪ FV v)).
          * intros. apply superset_in_Tm with (X__sub := FV t :\ y ∪ FV v); auto. simpl. intros.
            rewrite in_fsetU H2 //.
          * applys_eq substitution_type 1 2.
            -- rewrite domm_update_substitution domm_identity' //.
            -- rewrite codomm_Tm_set_update_identity //.
        + applys_eq substitution_type 2.
          rewrite domm_update_substitution domm_identity' free_variables_after_substitute //.
        + apply superset_in_Tm with (X__sub := FV t).
          * simpl. intros. rewrite in_fsetU H1 //.
          * apply in_Tm_free_variables.
      - transitivity (⦇(1__(FV(⦇(1__(FV t))[y,v]⦈ t)))[x,⦇(1__(FV u))[y,v]⦈ u]⦈ t).
        { eapply substitution_respects_α_equivalence with (t := (⦇(1__(FV t))[y, v]⦈ t)) (u := t).
          - apply substitution_type.
          - apply superset_in_Tm with (X__sub := FV (⦇(1__(FV t))[y, v]⦈ t)).
            + intros.
              rewrite domm_update_substitution domm_identity' free_variables_noop_substitute; cycle 1.
              { simpl in *. rewrite Heqy0 //. }
              rewrite free_variables_noop_substitute in H1; cycle 1.
              { simpl in *. rewrite Heqy0 //. }
              simpl in *. rewrite in_fsetU H1 //.
            + apply in_Tm_free_variables.
          - rewrite domm_update_substitution domm_identity' free_variables_noop_substitute; cycle 1.
            { simpl in *. rewrite Heqy0 //. }
            apply superset_in_Tm with (X__sub := FV t).
            + simpl. intros. rewrite in_fsetU H1 //.
            + apply in_Tm_free_variables.
          - apply noop_substitution. simpl in *. rewrite Heqy0 //. }
        eapply lift_substitution_indistinguishable_substitutions.
        + apply substitution_type.
        + apply substitution_type.
        + intros.
          rewrite domm_update_identity free_variables_noop_substitute.
          * simpl in *. rewrite in_fsetU H1 //.
          * simpl in *. rewrite Heqy0 //.
        + intros.
          rewrite domm_map domm_update_identity.
          simpl in *. rewrite in_fsetU H1 //.
        + apply in_Tm_free_variables.
        + intros.
          rewrite !mapmE !setmE !mapmE !mkfmapfE.
          simpl in *.
          destruct (x0 =P x); subst.
          * apply (introF eqP) in H.
            rewrite H H1 /= setmE eq_refl /=. reflexivity.
          * destruct (x0 =P y); subst.
            { rewrite H1 // in Heqy0. }
            rewrite H1 free_variables_noop_substitute; cycle 1.
            { rewrite Heqy0 //. }
            apply (introF eqP) in n.
            rewrite H1 /= setmE mapmE mkfmapfE n H1. reflexivity. }
    symmetry.
    transitivity (⦇⦇(1__(FV (⦇(1__(FV t))[x,u]⦈ t)))[y,v]⦈ ∘ (1__(FV t))[x,u]⦈ t).
    { destruct (x ∈ FV t) eqn:?.
      - eapply monad_substitution with (X := FV t ∪ {x}) (Y := FV (t[x⟵u]) ∪ {y}).
        + rewrite free_variables_after_substitute //.
          apply enlarge_codomain with (P__sub := Tm (FV t :\ x ∪ FV u)).
          * intros. apply superset_in_Tm with (X__sub := FV t :\ x ∪ FV u); auto. simpl. intros.
            rewrite in_fsetU H2 //.
          * applys_eq substitution_type 1 2.
            -- rewrite domm_update_identity //.
            -- rewrite codomm_Tm_set_update_identity //.
        + applys_eq substitution_type 1 2.
          * rewrite domm_update_identity //.
          * rewrite codomm_Tm_set_update_identity //.
        + apply superset_in_Tm with (X__sub := FV t).
          * simpl. intros. rewrite in_fsetU H1 //.
          * apply in_Tm_free_variables.
      - transitivity (⦇(1__(FV (⦇(1__(FV t))[x,u]⦈ t)))[y,v]⦈ t).
        { simpl.
          set (t' := (⦇(mapm variable (identity (FV t)))[x,u]⦈ t)).
          set (f := ⦇(mapm variable (identity (FV t')))[y,v]⦈).
          eapply substitution_respects_α_equivalence.
          - apply substitution_type.
          - rewrite domm_update_identity.
            apply superset_in_Tm with (X__sub := FV t').
            + simpl. intros. rewrite in_fsetU H1 //.
            + apply in_Tm_free_variables.
          - rewrite domm_update_identity /t'.
            rewrite free_variables_noop_substitute; cycle 1.
            { simpl in *. rewrite Heqy0 //. }
            apply superset_in_Tm with (X__sub := FV t).
            + simpl. intros. rewrite in_fsetU H1 //.
            + apply in_Tm_free_variables.
          - apply noop_substitution. simpl in *. rewrite Heqy0 //. }
        eapply lift_substitution_indistinguishable_substitutions.
        + apply substitution_type.
        + apply substitution_type.
        + intros.
          rewrite domm_update_identity free_variables_noop_substitute.
          * simpl in *. rewrite in_fsetU H1 //.
          * simpl in *. rewrite Heqy0 //.
        + simpl. intros. rewrite domm_map domm_update_identity in_fsetU H1 //.
        + apply in_Tm_free_variables.
        + simpl. intros.
          apply not_eq_sym, (introF eqP) in H.
          rewrite !mapmE !setmE !mapmE !mkfmapfE.
          destruct (x0 =P y); subst.
          * rewrite H H1 /= setmE eq_refl /=. reflexivity.
          * destruct (x0 =P x); subst.
            { simpl in *. rewrite H1 // in Heqy0. }
            apply (introF eqP) in n.
            rewrite H1 /= setmE n mapmE /= mkfmapfE free_variables_noop_substitute; cycle 1.
            { simpl in *. rewrite Heqy0 //. }
            reflexivity. }
    eapply lift_substitution_indistinguishable_substitutions.
    - apply substitution_type.
    - apply substitution_type.
    - simpl. intros. rewrite domm_map domm_update_identity in_fsetU H1 //.
    - simpl. intros. rewrite domm_map domm_update_identity in_fsetU H1 //.
    - apply in_Tm_free_variables.
    - simpl. intros.
      rewrite !mapmE !setmE !mapmE !mkfmapfE.
      apply (introF eqP) in H.
      destruct (x0 =P x); subst.
      + rewrite H H1 /= setmE eq_refl free_variables_after_substitute /= //.
        eapply lift_substitution_indistinguishable_substitutions.
        * apply substitution_type.
        * apply substitution_type.
        * simpl. intros. rewrite domm_set domm_map in_fsetU in_fset1 domm_mkfmapf fsvalK in_fsetU in_fsetD in_fset1.
          destruct (a =P y); subst; auto.
          destruct (a =P x); subst.
          -- apply H2.
          -- rewrite H2 orbT //.
        * simpl. intros. rewrite domm_set domm_map in_fsetU in_fset1 domm_mkfmapf fsvalK H2 orbT //.
        * apply in_Tm_free_variables.
        * simpl. intros.
          rewrite !setmE !mapmE !mkfmapfE.
          destruct (x0 =P y); subst.
          { reflexivity. }
          rewrite in_fsetU in_fsetD in_fset1 H2 orbT. reflexivity.
      + rewrite H1 /=.
        destruct (x0 =P y); subst.
        * rewrite setmE mapmE eq_refl /=.
          rewrite free_variables_after_substitute //.
          transitivity (⦇1__(FV v)⦈ v).
          { symmetry. eapply monad_substitution; try apply η_type. apply in_Tm_free_variables. }
          eapply lift_substitution_indistinguishable_substitutions.
          -- apply substitution_type.
          -- apply substitution_type.
          -- simpl. intros. rewrite domm_map domm_mkfmapf fsvalK H2 //.
          -- simpl. intros.
             rewrite domm_set domm_map domm_mkfmapf !in_fsetU !in_fset1 fsvalK in_fsetU in_fsetD in_fset1.
             destruct (a =P x); subst; auto.
             destruct (a =P y); subst.
             ++ apply H2.
             ++ rewrite H2 orbT //.
          -- apply in_Tm_free_variables.
          -- simpl. intros.
             rewrite !mapmE !mkfmapfE !setmE H2 !mapmE !mkfmapfE in_fsetU in_fsetD in_fset1 H2 orbT.
             destruct (x0 =P x); subst.
             { rewrite H2 // in H0. }
             reflexivity.
        * apply (introF eqP) in n, n0.
          rewrite /= !setmE !mapmE !mkfmapfE n n0 /=.
          destruct (x ∈ FV t) eqn:?.
          -- rewrite free_variables_after_substitute // !in_fsetU !in_fsetD !in_fset1 n H1 /=.
             destruct (y ∈ FV t) eqn:?.
             ++ rewrite free_variables_after_substitute // !in_fsetU !in_fsetD !in_fset1 n0 H1.
                reflexivity.
             ++ rewrite free_variables_noop_substitute; cycle 1.
                { simpl in *. rewrite Heqy1 //. }
                rewrite H1. reflexivity.
          -- rewrite free_variables_noop_substitute; cycle 1.
             { simpl in *. rewrite Heqy0 //. }
             rewrite H1.
             destruct (y ∈ FV t) eqn:?.
             ++ rewrite free_variables_after_substitute // !in_fsetU !in_fsetD !in_fset1 n0 H1.
                reflexivity.
             ++ rewrite free_variables_noop_substitute; cycle 1.
                { simpl in *. rewrite Heqy1 //. }
                rewrite H1. reflexivity.
  Qed.

  (* TODO Formalize the resulting Kliesli-category. *)

  Implicit Types (n i : nat) (ϕ : {fmap 𝒱 → nat}).

  #[global] Instance nat_HasMembers : HasMembers nat nat bool :=
    { is_member_of i n := i < n }.

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

  Section in_de_Bruijn_Tm.
    Reserved Notation "x '∈' 'Tm^db' n" (at level 40).

    Inductive in_de_Bruijn_Tm : nat -> de_Bruijn_term -> Prop :=
    | de_Bruijn_Tm_variable : forall n i,
        i ∈ n : Prop ->
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
    simpl. intros.
    gen_dep n. induction dBt; simpl; intros.
    - destruct (IHdBt n.+1); repeat constructor.
      + rewrite addn1 //.
      + intro_all. apply n0. inverts H. rewrite addn1 // in H2.
    - destruct (IHdBt1 n); repeat constructor.
      + destruct (IHdBt2 n); repeat constructor; auto.
        intro_all. apply n0. inverts H. auto.
      + intro_all. inverts H. auto.
    - gen_dep n0. induction n; intros;
      destruct n0; repeat constructor; intro_all; simpl in *;
      try solve [inverts H; inverts H2].
      replace (n.+1 < n0.+1) with (n < n0) by auto.
      (pose proof (IHn n0)); inverts H; repeat constructor.
      { simpl. auto. }
      intro_all. inverts H. simpl in *.
      replace (n.+1 < n0.+1) with (n < n0) in H4 by auto.
      rewrite H4 // in H0.
  Qed.

  Definition ϕ_add x : {fmap 𝒱 → nat} -> {fmap 𝒱 → nat} :=
    mapim (fun y ϕy => if y == x then 0 else ϕy + 1).

  #[local] Notation "ϕ '^+' x" := (ϕ_add x ϕ).

  #[local] Reserved Notation "t '^' ϕ" (at level 30, ϕ at level 30).

  Fixpoint to_de_Bruijn t (ϕ : {fmap 𝒱 → nat}) : de_Bruijn_term :=
    match t with
    | variable x =>
      de_Bruijn_variable (getm ϕ x)
    | application t u =>
      de_Bruijn_application (t^ϕ) (u^ϕ)
    | abstraction x t =>
      de_Bruijn_abstraction (t^(ϕ^+x))
    end

  where "t '^' ϕ" := (to_de_Bruijn t ϕ).

  #[local] Notation "t '^ϕ'" := (to_de_Bruijn t) (at level 40).
End Alpha.
