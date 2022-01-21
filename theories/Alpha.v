(* ===== TODOs =====
  - Use [Lemma]s (or [Hint Extern]s) to remove duplication in proofs.
  - Clean up ordering of definitions/lemmas/parameters/notations/etc.
  - Improve names of lemmas/theorems/etc.
  - Remove dead code.
  - Break up into separate files?
  - Improve compilation speed.
  - Improve evaluation speed.
  - Set up extraction. *)

From Coq Require Import Classes.RelationClasses Lists.List Program.Equality Program.Tactics Setoid ssreflect.
From Equations Require Import Equations.
From mathcomp Require Import bigop choice eqtype seq ssrbool ssrfun ssrnat.
From deriving Require Import deriving.
From extructures Require Import fmap fset ord.
From AlphaPearl Require Import Util.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

Obligation Tactic := program_simpl.

#[local] Open Scope fset_scope.

Definition Fresh_correct (𝒱 : ordType) (Fresh : {fset 𝒱} -> 𝒱) : Prop :=
  forall s : {fset 𝒱}, Fresh s ∉ s.

Module Type Alpha.
  Parameter 𝒱 : ordType.

  Parameter Fresh : {fset 𝒱} -> 𝒱.

  Parameter HFresh : Fresh_correct Fresh.
End Alpha.

Module AlphaFacts (Import M : Alpha).
  #[local] Implicit Type Fresh : {fset 𝒱} -> 𝒱.

  #[local] Notation "x '∪' '{' y '}'" :=
    (x :|: fset1 y)
      (at level 52, format "x  '∪'  '{' y '}'")
    : fset_scope.

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

  Definition Tm X t : bool := FV t ⊆ X.

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
    introv.
    gen X. induction t; intros; simpl;
    ((rewrite fsubD1set fsetUC; destruct (IHt (X ∪ {s})) as [HX_s|HX_s]) ||
     (rewrite fsubUset; destruct (IHt1 X) as [H1|H1], (IHt2 X) as [H2|H2]) ||
     (rewrite fsub1set; destruct (s ∈ X) eqn:Hs));
    repeat constructor; auto;
    intros HX; inverts HX; auto.
    rewrite H1 // in Hs.
  Qed.

  Definition is_subset_of R X Y : bool :=
    (domm R ⊆ X) && (codomm R ⊆ Y).

  #[local] Notation "R '⊆' X '×' Y" := (is_subset_of R X Y) (at level 40, X at next level).

  Lemma is_subset_ofP : forall {R} {X} {Y}, reflect (forall x y, R x y -> x ∈ X /\ y ∈ Y) (is_subset_of R X Y).
  Proof.
    unfold is_subset_of.
    introv.
    apply Bool.iff_reflect.
    split; intros.
    - rewrite <- (rwP (@andP (domm R ⊆ X) (codomm R ⊆ Y))).
      split; apply (rwP fsubsetP); intros x HRx.
      + apply (rwP dommP) in HRx as [v HRx].
        eapply H. eauto.
      + apply (rwP codommP) in HRx as [v HRx].
        eapply H. eauto.
    - apply (rwP andP) in H as [HRX HRY].
      apply (rwP fsubsetP) in HRX, HRY.
      split.
      + apply HRX. apply (rwP dommP). eauto.
      + apply HRY. apply (rwP codommP). eauto.
  Qed.

  #[local] Notation partial_bijection := is_injective (only parsing).

  (** Page 3: "Given R a partial bijection as above and x, y ∈ 𝒱 we define the symmetric update of R as...." *)
  Definition update R x y : {fmap 𝒱 → 𝒱} :=
    unionm (remm (rem_valm R y) x) [fmap (x, y)].

  #[local] Notation "R '⦅' x ',' y '⦆'" :=
    (update R x y)
      (at level 0, format "R '⦅' x ',' y '⦆'").

  (** Page 3: "It is easy to see that R(x,y) is a partial bijection." *)
  Lemma partial_bijection_update :
    forall R x y,
      partial_bijection R ->
      partial_bijection R⦅x,y⦆.
  Proof.
    introv HRinj.
    apply (rwP injectivemP) in HRinj.
    rewrite <- (rwP (injectivemP (m := R⦅x,y⦆))). intros k1 Hk1 k2 Hks.
    apply (rwP dommP) in Hk1 as [v1 Hkv1].
    rewrite /update !unionmE /= !remmE !setmE !rem_valmE in Hkv1, Hks.
    destruct (k1 =P x); subst.
    - inverts Hkv1.
      destruct (k2 =P x); subst; auto.
      destruct (getm R k2) eqn:HRk2; rewrite ?HRk2 // in Hks.
      destruct (v1 =P s); subst; inverts Hks.
      exfalso. auto.
    - destruct (getm R k1) eqn:HRk1; rewrite ?HRk1 // in Hkv1, Hks.
      destruct (y =P s); subst; inverts Hkv1.
      destruct (k2 =P x); subst.
      * inverts Hks. exfalso. auto.
      * destruct (getm R k2) eqn:HRk2; rewrite ?HRk2 // in Hks.
        destruct (y =P s); subst; inverts Hks.
        apply HRinj.
        -- apply (rwP dommP). eauto.
        -- rewrite HRk1 //.
  Qed.

  Lemma domm_update :
    forall R x y,
      domm R⦅x,y⦆ ⊆ (domm R ∪ {x}).
  Proof.
    introv.
    apply (rwP fsubsetP). intros k HR'k.
    rewrite domm_union domm_rem in_fsetU in_fsetD in_fset1 in HR'k.
    rewrite in_fsetU in_fset1 orbC.
    destruct (k =P x); subst; auto.
    apply (rwP dommP).
    apply (rwP orP) in HR'k as [HR'k|Hk].
    - apply (rwP andP) in HR'k as [Hknx HR'k].
      apply (rwP dommP) in HR'k as [v HR'k].
      rewrite rem_valmE in HR'k.
      destruct (getm R k) eqn:HRk; eauto.
    - rewrite domm_set in_fsetU in_fset1 orbC domm0 /= in Hk.
      apply (rwP eqP) in Hk. subst. contradiction.
  Qed.

  Lemma codomm_update :
    forall R x y,
      codomm R⦅x,y⦆ ⊆ (codomm R ∪ {y}).
  Proof.
    introv.
    apply (rwP fsubsetP). intros v HvℛR'.
    apply (rwP codommP) in HvℛR' as [k HR'k].
    rewrite unionmE remmE rem_valmE setmE /= in HR'k.
    rewrite in_fsetU in_fset1 orbC.
    destruct (k =P x); subst.
    { inverts HR'k. rewrite eq_refl //. }
    destruct (getm R k) eqn:HRk; cycle 1.
    { inverts HR'k. }
    destruct (y =P s); subst; inverts HR'k.
    apply not_eq_sym, (introF eqP) in n0. rewrite n0.
    apply (rwP codommP). eauto.
  Qed.

  (** Page 3: "R(x,y) ... ∈ (X ∪ {x}) × ...." *)
  Lemma update_type :
    forall X Y R x y,
      R ⊆ X × Y ->
      R⦅x,y⦆ ⊆ (X ∪ {x}) × (Y ∪ {y}).
  Proof.
    introv HRtype.
    apply (rwP is_subset_ofP). intros x' y' HR'x'.
    rewrite !in_fsetU !in_fset1 ![_ || (_ == _)]orbC.
    rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in HR'x'.
    destruct (x' =P x); subst.
    { inverts HR'x'. rewrite eq_refl //. }
    destruct (getm R x') eqn:HRx'; cycle 1.
    { inverts HR'x'. }
    destruct (y =P s); subst; inverts HR'x'.
    apply not_eq_sym, (introF eqP) in n0.
    rewrite <- (rwP is_subset_ofP) in HRtype.
    apply HRtype in HRx' as [Hx'X Hy'Y].
    rewrite n0 Hx'X Hy'Y //.
  Qed.

  #[local] Reserved Notation "t '≡_α^' R u"
    (at level 40, R at level 0, format "t  '≡_α^' R  u").

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
    introv.
    destruct (t ≡_α^R u) eqn:Hα; constructor.
    - gen R u. induction t; intros;
      destruct u; inverts Hα as Hα; auto.
      apply (rwP andP) in Hα as []; auto.
    - introv Hα'.
      dependent induction Hα'; inverts Hα; auto.
      + rewrite H // in H1.
      + apply negbT, (rwP nandP) in H0 as [H|H]; apply negbTE in H; auto.
  Qed.

  (** Page 3: "We now define ≡α^R ⊆ Tm(X) × Tm(Y)." *)
  Lemma α_equivalent'_type :
    forall R t u,
      t ≡_α^R u ->
      t ∈ Tm (domm R) /\ u ∈ Tm (codomm R).
  Proof.
    rewrite /in_mem /= /Tm.
    introv Hα.
    gen R u. induction t; simpl; introv Hα;
    destruct u; inverts Hα.
    - apply IHt in H0 as [Httype Hutype]. apply (rwP fsubsetP) in Httype, Hutype.
      split; apply (rwP fsubsetP); intros x H;
      rewrite in_fsetD in_fset1 in H; apply (rwP andP) in H as [Hxneqs Hxtype]; apply negbTE in Hxneqs.
      + apply Httype, (rwP dommP) in Hxtype as [v HR'x].
        rewrite unionmE remmE rem_valmE setmE Hxneqs in HR'x.
        destruct (getm R x) eqn:HRx; cycle 1.
        { inverts HR'x. }
        destruct (s0 =P s1); subst; inverts HR'x.
        apply (rwP dommP). eauto.
      + apply Hutype, (rwP codommP) in Hxtype as [k HR'k].
        rewrite unionmE remmE rem_valmE setmE /= in HR'k.
        destruct (k =P s); subst; auto.
        { inverts HR'k. rewrite eq_refl // in Hxneqs. }
        destruct (getm R k) eqn:HRk; cycle 1.
        { inverts HR'k. }
        destruct (s0 =P s1); subst; inverts HR'k.
        apply (rwP codommP). eauto.
    - apply (rwP andP) in H0 as [Ht1 Ht2].
      apply IHt1 in Ht1 as [Ht1 Hu1]. apply IHt2 in Ht2 as [Ht2 Hu2].
      apply (rwP fsubsetP) in Ht1, Hu1, Ht2, Hu2.
      split; apply (rwP fsubsetP); introv H;
      rewrite in_fsetU in H; apply (rwP orP) in H as [Hxt1|Hxt2]; auto.
    - rewrite /in_mem /= /in_mem /= in H0. apply (rwP getmP) in H0.
      rewrite !fsub1set.
      split.
      + apply (rwP dommP). eauto.
      + apply (rwP codommP). eauto.
  Qed.

  (** TODO Formalize "Note that we cannot replace partial bijections by bijections..."? *)

  (** Page 3: "Given X, Y, Z ⊂fin 𝒱 we write 1X = ...." *)
  Definition identity : {fset 𝒱} -> {fmap 𝒱 → 𝒱} := mkfmapf id.

  Class Identity (A : Type) :=
    { identity' : forall X, A }.

  #[global] Hint Mode Identity ! : typeclass_instances.

  Arguments identity' _ : simpl never.

  #[local] Notation "'1__' X" := (identity' X) (at level 40, format "'1__' X").

  #[global] Instance fmap_𝒱_Identity : Identity {fmap 𝒱 → 𝒱} :=
    { identity' := identity }.

  #[global] Instance fmap_term_Identity : Identity {fmap 𝒱 → term} :=
    { identity' X := mapm variable (1__X : {fmap 𝒱 → 𝒱}) }.

  #[global] Instance fmap_to_Prop_Identity : Identity (𝒱 -> 𝒱 -> Prop) :=
    { identity' := identity }.

  (** Page 3: "1X ... ⊆ X × X." *)
  Lemma identity_type : forall X, (1__X : {fmap 𝒱 → 𝒱}) ⊆ X × X.
  Proof.
    introv. apply (rwP is_subset_ofP). introv Hxy.
    rewrite /identity' /= /fmap_to_Prop mkfmapfE in Hxy.
    destruct (x ∈ X) eqn:HxX; rewrite HxX in Hxy;
    inverts Hxy. auto.
  Qed.

  (** Page 3: "1X... obviously is a partial bijection." *)
  Lemma partial_bijection_identity : forall X, partial_bijection (1__X : {fmap 𝒱 → 𝒱}).
  Proof.
    intros.
    rewrite /partial_bijection /fmap_IsInjective /injective /identity' /fmap_𝒱_Identity /identity.
    rewrite <- (rwP injectivemP). intros x Hx x' Hxx'.
    apply (rwP dommP) in Hx as [v Hx].
    rewrite !mkfmapfE in Hx, Hxx'.
    destruct (x ∈ X) eqn:HxX; rewrite HxX in Hx, Hxx'; inverts Hx.
    destruct (x' ∈ X) eqn:Hx'X; rewrite Hx'X in Hxx'; inverts Hxx'.
    auto.
  Qed.

  (** Page 3: "Given R ⊆ X × Y and S ⊆ Y × Z we write...." *)
  Definition converse R : {fmap 𝒱 → 𝒱} := invm R.

  #[local] Notation "R 'ᵒ'" := (converse R) (at level 40).

  (** Page 3: "Both operations are closed under partial bijections." *)
  Lemma converse_closed_under_partial_bijection :
    forall R,
      partial_bijection R ->
      partial_bijection (R ᵒ).
  Proof.
    introv HRinj.
    apply (rwP injectivemP) in HRinj.
    simpl. rewrite <- (rwP injectivemP). intros x HR'x x' HR'x'.
    apply (rwP dommP) in HR'x as [v HR'x]. rewrite HR'x in HR'x'.
    symmetry in HR'x'. apply getm_inv in HR'x, HR'x'. rewrite HR'x in HR'x'. inverts HR'x'. auto.
  Qed.

  Lemma domm_converse :
    forall R,
      partial_bijection R ->
      domm (R ᵒ) = codomm R.
  Proof.
    introv HRinj.
    apply eq_fset. intros x.
    apply Bool.eq_iff_eq_true. split; introv H.
    - rewrite codomm_domm_invm //.
    - rewrite codomm_domm_invm // in H.
  Qed.

  Lemma codomm_converse :
    forall R,
      partial_bijection R ->
      codomm (R ᵒ) = domm R.
  Proof.
    introv HRinj.
    assert (partial_bijection (R ᵒ)) as HR'inj.
    { apply converse_closed_under_partial_bijection. auto. }
    apply eq_fset. intros x.
    apply Bool.eq_iff_eq_true. split; introv H.
    - rewrite codomm_domm_invm // in H.
      apply (rwP dommP) in H as [v HR'x].
      rewrite invmK in HR'x.
      + apply (rwP dommP). eauto.
      + apply (rwP injectivemP). auto.
    - rewrite codomm_domm_invm //.
      apply (rwP dommP).
      rewrite invmK.
      + apply (rwP dommP). eauto.
      + apply (rwP injectivemP). auto.
  Qed.

  (** Page 3: "Rᵒ ... ⊆ Y × X." *)
  Lemma converse_type :
    forall R X Y,
      R ⊆ X × Y ->
      R ᵒ ⊆ Y × X.
  Proof.
    introv HRtype.
    apply (rwP is_subset_ofP). intros y x HR'y.
    rewrite <- (rwP is_subset_ofP) in HRtype.
    apply and_comm, HRtype.
    apply getm_inv. auto.
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

  #[local] Notation "R ';;' S" := (compose R S) (at level 40, format "R ';;' S").

  Lemma domm_compose :
    forall R S,
      domm (R;;S) ⊆ domm R.
  Proof.
    introv.
    apply (rwP fsubsetP). introv HRSx.
    apply (rwP dommP) in HRSx as [v HRSx].
    rewrite mkfmapfpE in HRSx.
    destruct (x ∈ domm R) eqn:HRx; rewrite HRx // in HRSx.
  Qed.

  Lemma codomm_compose :
    forall R S,
      codomm (R;;S) ⊆ codomm S.
  Proof.
    introv.
    apply (rwP fsubsetP). introv HxℛRS.
    apply (rwP codommP) in HxℛRS as [k HRSx].
    rewrite mkfmapfpE in HRSx.
    destruct (k ∈ domm R) eqn:HRk; rewrite HRk // in HRSx.
    apply (rwP dommP) in HRk as [v HRk]. rewrite HRk in HRSx.
    apply (rwP codommP). eauto.
  Qed.

  (** Page 3: "R;S ... ⊆ X × Z." *)
  Lemma compose_type :
    forall R S X Y Z,
      R ⊆ X × Y ->
      S ⊆ Y × Z ->
      R;;S ⊆ X × Z.
  Proof.
    introv HRtype HStype.
    rewrite <- (rwP is_subset_ofP) in HRtype. rewrite <- (rwP is_subset_ofP) in HStype.
    apply (rwP is_subset_ofP). intros x z HRSx.
    rewrite /fmap_to_Prop mkfmapfpE in HRSx.
    destruct (x ∈ domm R) eqn:HRx; rewrite HRx // in HRSx.
    apply (rwP dommP) in HRx as [y HRx].
    rewrite HRx in HRSx. split.
    - eapply HRtype. eauto.
    - eapply HStype. eauto.
  Qed.

  (** Page 3: "Both operations are closed under partial bijections." *)
  Lemma compose_closed_under_partial_bijection :
    forall R S,
      partial_bijection R ->
      partial_bijection S ->
      partial_bijection (R;;S).
  Proof.
    unfold partial_bijection.
    introv HRinj HSinj.
    apply (rwP injectivemP) in HRinj, HSinj.
    simpl. rewrite <- (rwP injectivemP). intros x HRSx x' Hxx'.
    apply (rwP dommP) in HRSx as [v HRSx].
    rewrite !mkfmapfpE in HRSx, Hxx'.
    destruct (x ∈ domm R) eqn:HRx; rewrite HRx in HRSx, Hxx'; cycle 1.
    { inverts HRSx. }
    apply (rwP dommP) in HRx as [y HRx]. rewrite HRx in HRSx, Hxx'.
    rewrite HRSx in Hxx'.
    destruct (x' ∈ domm R) eqn:HRx'; rewrite HRx' in Hxx'; cycle 1.
    { inverts Hxx'. }
    apply (rwP dommP) in HRx' as [v' HRx']. rewrite HRx' -HRSx in Hxx'.
    apply HSinj in Hxx'; cycle 1.
    { apply (rwP dommP). eauto. }
    subst.
    rewrite -HRx in HRx'. apply HRinj in HRx'; auto.
    rewrite HRx in HRx'.
    apply (rwP dommP). eauto.
  Qed.

  (** Page 3: Lemma 1.1. *)
  Lemma update_identity : forall X x, (1__X) ⦅x,x⦆ = 1__(X ∪ {x}).
  Proof.
    introv.
    apply eq_fmap. intros k.
    rewrite unionmE mkfmapfE in_fsetU in_fset1 remmE rem_valmE /= setmE mkfmapfE.
    destruct (k =P x); subst.
    - rewrite orbT //.
    - destruct (k ∈ X) eqn:HkX; rewrite HkX.
      + replace (x == k) with false; auto.
        symmetry. apply Bool.not_true_iff_false. introv Hxk.
        apply (rwP eqP) in Hxk. auto.
      + rewrite emptymE //.
  Qed.

  (** Page 3: Lemma 1.2. *)
  Lemma update_converse :
    forall R x y,
      partial_bijection R ->
      R⦅x,y⦆ᵒ = R ᵒ⦅y,x⦆.
  Proof.
    introv HRinj.
    apply eq_fmap. intros k.
    rewrite /converse /update !unionmE !remmE !rem_valmE /= !setmE.
    destruct (k =P y); subst.
    - apply getm_inv. rewrite invmK.
      + rewrite unionmE remmE rem_valmE setmE eq_refl //.
      + intros k HR'k k' Hkk'.
        epose proof @partial_bijection_update _ _ _ HRinj as H. apply (rwP injectivemP) in H. apply H; eauto.
    - destruct (invm R k) eqn:HR'k; rewrite ?HR'k.
      + apply getm_inv in HR'k.
        destruct (x =P s); subst.
        * apply invm_None.
          { apply partial_bijection_update. auto. }
          rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros.
          rewrite unionmE remmE rem_valmE setmE.
          destruct (k' =P s); subst.
          -- apply Bool.negb_true_iff, Bool.not_true_iff_false. introv Hyk.
             apply (rwP eqP) in Hyk. inverts Hyk. auto.
          -- destruct (getm R k') eqn:HRk'; rewrite ?HRk'; auto.
             destruct (y =P s0); subst; auto.
             apply Bool.negb_true_iff, Bool.not_true_iff_false. introv Hs0k.
             apply (rwP eqP) in Hs0k. inverts Hs0k.
             apply n0. apply (rwP injectivemP) in HRinj. apply HRinj.
             ++ apply (rwP dommP). eauto.
             ++ rewrite HRk' //.
        * apply getm_inv. rewrite invmK; cycle 1.
          { intros k' HR'k' k'' Hk'k''.
            epose proof @partial_bijection_update _ _ _ HRinj as H. apply (rwP injectivemP) in H. apply H; eauto. }
          rewrite unionmE remmE rem_valmE setmE.
          replace (s == x) with false; cycle 1.
          { symmetry. apply Bool.not_true_iff_false. introv Hsx. apply (rwP eqP) in Hsx. subst. auto. }
          destruct (getm R s) eqn:HRs; rewrite HR'k.
          -- destruct (y =P s0); subst; inverts HR'k; auto. contradiction.
          -- discriminate.
      + apply invm_None in HR'k; auto.
        apply invm_None.
        { apply partial_bijection_update. auto. }
        rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros k'.
        rewrite unionmE remmE rem_valmE setmE.
        destruct (k' =P x); subst.
        * apply Bool.negb_true_iff, Bool.not_true_iff_false. introv Hyk. apply (rwP eqP) in Hyk. inverts Hyk. auto.
        * destruct (getm R k') eqn:HRk'; rewrite ?HRk' //.
          destruct (y =P s); subst; auto.
          rewrite <- (rwP (@codommPn _ _ R k)) in HR'k.
          apply Bool.negb_true_iff, Bool.not_true_iff_false. introv Hsk.
          apply (rwP eqP) in Hsk. inverts Hsk. pose proof (HR'k k') as HnRk'. rewrite HRk' eq_refl // in HnRk'.
  Qed.

  (** Page 3: Lemma 1.3. *)
  Lemma update_compose :
    forall R S x y z k v,
      getm (R⦅x,y⦆;;S⦅y,z⦆) k = Some v ->
      getm (R;;S)⦅x,z⦆ k = Some v.
  Proof.
    introv HR'S'.
    rewrite unionmE remmE rem_valmE setmE.
    destruct (k =P x); subst.
    - rewrite eq_refl /=. f_equal.
      rewrite mkfmapfpE in HR'S'.
      destruct (x ∈ domm (R⦅x,y⦆)) eqn:HR'x; rewrite HR'x // in HR'S'.
      apply (rwP dommP) in HR'x as [x' HR'x]. rewrite HR'x in HR'S'.
      rewrite !unionmE !remmE !rem_valmE !setmE !eq_refl /= in HR'x, HR'S'.
      inverts HR'x. rewrite eq_refl in HR'S'. inverts HR'S'. auto.
    - apply (introF eqP) in n. rewrite n mkfmapfpE.
      rewrite mkfmapfpE in HR'S'.
      destruct (k ∈ domm (R⦅x,y⦆)) eqn:HR'k; rewrite HR'k // in HR'S'.
      apply (rwP dommP) in HR'k as [k' HR'k].
      rewrite unionmE remmE rem_valmE setmE /= n in HR'k, HR'S'.
      destruct (getm R k) eqn:HRk; rewrite ?HRk in HR'k, HR'S'; cycle 1.
      { inverts HR'k. }
      destruct (y =P s); subst; inverts HR'k.
      rewrite /= unionmE remmE rem_valmE setmE in HR'S'.
      apply not_eq_sym, (introF (@eqP 𝒱 _ _)) in n0. rewrite n0 in HR'S'.
      destruct (getm S k') eqn:HSv'; rewrite ?HSk' // in HR'S'.
      destruct (z =P s); subst; inverts HR'S'.
      assert (exists v, getm R k = Some v) as H by eauto. apply (rwP dommP) in H. rewrite H.
      apply (introF eqP) in n1. rewrite n1 //.
  Qed.

  Lemma α_equivalent'_supermap :
    forall (R__sub R__super : {fmap 𝒱 → 𝒱}) t u,
      (forall (k : 𝒱) v, getm R__sub k = Some v -> getm R__super k = Some v) ->
      t ≡_α^R__sub u ->
      t ≡_α^R__super u.
  Proof.
    introv Hsub Hαsub.
    gen R__sub R__super u. induction t; intros;
    destruct u; inverts Hαsub as Hαsub.
    - apply IHt with (R__super := R__super⦅s,s0⦆) in Hαsub; cycle 1.
      { introv HRsub'k.
        rewrite unionmE remmE rem_valmE setmE /= in HRsub'k.
        rewrite unionmE remmE rem_valmE setmE /=.
        destruct (k =P s); subst; auto.
        destruct (getm R__sub k) eqn:HRsubk.
        + apply Hsub in HRsubk; rewrite HRsubk.
          destruct (s0 =P s1); inverts HRsub'k. auto.
        + inverts HRsub'k. }
      rewrite /= Hαsub //.
    - apply (rwP andP) in Hαsub as [Hαsub1 Hαsub2].
      apply IHt1 with (R__super := R__super) in Hαsub1; auto.
      apply IHt2 with (R__super := R__super) in Hαsub2; auto.
      rewrite /= Hαsub1 Hαsub2 //.
    - apply (rwP getmP), Hsub in Hαsub. apply (rwP getmP). auto.
  Qed.

  Lemma α_equivalent'_with_behaviorally_identical_maps :
    forall R S t u,
      (forall x y, R x y -> x ∈ FV t -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    introv HReqvS Htαu.
    gen R S u. induction t; introv HReqvS Htαu;
    destruct u; inverts Htαu.
    - apply IHt with (R := R⦅s,s0⦆); auto. introv HR'xy Hxt.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in HR'xy.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
      destruct (x =P s); subst; auto.
      destruct (getm R x) eqn:HRx; cycle 1.
      { inverts HR'xy. }
      destruct (s0 =P s1); subst; inverts HR'xy.
      apply HReqvS in HRx.
      + rewrite HRx. apply (introF eqP) in n0. rewrite n0 //.
      + rewrite /= in_fsetD in_fset1 Hxt andbT. apply (introF eqP) in n. rewrite n //.
    - apply (rwP andP) in H0 as [Hα1 Hα2].
      simpl. rewrite <- (rwP andP). split;
      (apply IHt1 with R + apply IHt2 with R); auto;
      introv HRxy Hx;
      apply HReqvS; auto;
      rewrite /= in_fsetU Hx ?orbT //.
    - apply (rwP getmP), HReqvS in H0.
      + apply (rwP getmP). rewrite H0 //.
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
    (odflt (variable _) a ≡_α^R odflt (variable _) b)
      (at level 40, R at level 0, format "a  '`≡_α^' R  b").

  (** Page 4: Proposition 2.1. *)
  Proposition α_equivalent'_identity :
    forall X t,
      t ∈ Tm X ->
      t ≡_α^(1__X) t.
  Proof.
    introv HtX.
    apply (rwP fsubsetP) in HtX.
    gen X. induction t; intros; simpl.
    - rewrite update_identity.
      apply IHt. introv Hxt.
      rewrite in_fsetU in_fset1 orbC.
      destruct (x =P s); subst; auto.
      apply (introF eqP) in n.
      apply HtX. rewrite /= in_fsetD in_fset1 n Hxt //.
    - rewrite <- (rwP andP). split;
      apply α_equivalent'_supermap with (R__sub := 1__X); auto; intros;
      (apply IHt1 || apply IHt2); introv Hx;
      apply HtX; rewrite /= in_fsetU Hx ?orbT //.
    - assert (s ∈ fset1 s) as Hss. { rewrite in_fset1 eq_refl //. }
      apply HtX in Hss.
      apply (rwP getmP). rewrite mkfmapfE Hss //.
  Qed.

  (** Page 4: Proposition 2.2. *)
  Proposition α_equivalent'_converse :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      u ≡_α^(R ᵒ) t.
  Proof.
    introv HRinj Hα.
    gen R u. induction t; introv HRinj Hα;
    destruct u; inverts Hα as Hα.
    - apply IHt in Hα.
      + rewrite /= -update_converse //.
      + apply partial_bijection_update. auto.
    - apply (rwP andP) in Hα as [Hα1 Hα2].
      apply IHt1 in Hα1; auto. apply IHt2 in Hα2; auto.
      rewrite /= Hα1 Hα2 //.
    - apply (rwP getmP) in Hα.
      apply (rwP getmP), getm_inv. rewrite invmK //.
      apply (rwP injectivemP). auto.
  Qed.

  Lemma converseK :
    forall R,
      partial_bijection R ->
      R ᵒ ᵒ = R.
  Proof.
    introv HRinj.
    apply eq_fmap. intros k.
    apply (rwP injectivemP) in HRinj.
    unfold "ᵒ". rewrite invmK //.
  Qed.

  Proposition α_equivalent'_converse' :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u = u ≡_α^(R ᵒ) t.
  Proof.
    introv HRinj.
    apply Bool.eq_iff_eq_true; split; introv Hα.
    - apply α_equivalent'_converse; auto.
    - apply α_equivalent'_converse in Hα.
      + rewrite converseK // in Hα.
      + apply converse_closed_under_partial_bijection. auto.
  Qed.

  (** Page 4: Proposition 2.3. *)
  Proposition α_equivalent'_compose :
    forall R S t u (v : term),
      t ≡_α^R u ->
      u ≡_α^S v ->
      t ≡_α^(R;;S) v.
  Proof.
    introv Htαu Huαv.
    gen u v R S. induction t; introv Htαu Huαv;
    destruct u, v; inverts Htαu as Htαu; inverts Huαv as Huαv.
    - apply IHt with (S := S⦅s0,s1⦆) (v := v) in Htαu; auto.
      apply α_equivalent'_supermap with (R__super := (R;;S)⦅s,s1⦆) in Htαu; cycle 1.
      { intros. eapply update_compose; eauto. }
      rewrite /= Htαu //.
    - apply (rwP andP) in Htαu as [Htαu1 Htαu2], Huαv as [Huαv1 Huαv2].
      apply IHt1 with (R := R) (S := S) (v := v1) in Htαu1; auto.
      apply IHt2 with (R := R) (S := S) (v := v2) in Htαu2; auto.
      rewrite /= Htαu1 Htαu2 //.
    - apply (rwP getmP) in Htαu, Huαv.
      apply (rwP getmP). rewrite /= mkfmapfpE.
      assert (exists v, getm R s = Some v) as HRs by eauto. apply (rwP dommP) in HRs. rewrite HRs Htαu //.
  Qed.

  Lemma α_equivalent'_maps_all_FV :
    forall R t u x,
      t ≡_α^R u ->
      x ∈ FV t ->
      exists y, getm R x = Some y /\ y ∈ FV u.
  Proof.
    introv Hα Hx.
    gen R u. induction t; introv Hα;
    destruct u; inverts Hα as Hα.
    - rewrite /= in_fsetD in_fset1 in Hx. apply (rwP andP) in Hx as [Hxns Hxt].
      pose proof Hα. apply IHt in Hα as (y & HR'x & Hyu); auto.
      rewrite unionmE remmE rem_valmE setmE /= in HR'x.
      destruct (x =P s); subst; auto.
      destruct (getm R x) eqn:HRx; cycle 1.
      { inverts HR'x. }
      destruct (s0 =P s1); subst; inverts HR'x.
      exists y. split; auto. rewrite /= in_fsetD in_fset1 Hyu //.
      apply not_eq_sym, (introF eqP) in n0. rewrite n0 //.
    - apply (rwP andP) in Hα as [Hα1 Hα2].
      rewrite /= in_fsetU in Hx. apply (rwP orP) in Hx as [Hx|Hx].
      + apply IHt1 with (u := u1) in Hα1 as (y & HRx & Hyu1); auto.
        exists y. rewrite in_fsetU Hyu1 //.
      + apply IHt2 with (u := u2) in Hα2 as (y & HRx & Hyu2); auto.
        exists y. rewrite in_fsetU Hyu2 orbT //.
    - apply (rwP getmP) in Hα.
      rewrite /= in_fset1 in Hx. apply (rwP eqP) in Hx. subst.
      exists s0. rewrite /= in_fset1 eq_refl //.
  Qed.

  Lemma α_equivalent'_maps_all_FV' :
    forall R t u y,
      partial_bijection R ->
      t ≡_α^R u ->
      y ∈ FV u ->
      exists x, getm R x = Some y /\ x ∈ FV t.
  Proof.
    introv HRinj Hα Hyu.
    apply α_equivalent'_converse in Hα; auto.
    pose proof α_equivalent'_maps_all_FV _ _ _ _ Hα Hyu as (x & HR'y & Hxt).
    apply getm_inv in HR'y. eauto.
  Qed.

  Lemma α_equivalent'_implies_related_FV :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      FV u = pimfset (getm R) (FV t).
  Proof.
    introv HRinj Hα.
    apply eq_fset. intros y.
    rewrite in_pimfset.
    symmetry.
    destruct (y ∈ FV u) eqn:Hxu.
    - eapply α_equivalent'_maps_all_FV' in Hxu as (x & HRx & Hxt); eauto.
      apply (rwP imfsetP). eauto.
    - apply Bool.not_true_iff_false. introv Hyt'.
      apply (rwP imfsetP) in Hyt' as [x Hxt HRx].
      eapply α_equivalent'_maps_all_FV in Hxt as (y' & H'Rx & Hy'u); eauto.
      rewrite H'Rx in HRx. inverts HRx.
      rewrite Hy'u // in Hxu.
  Qed.

  Lemma α_equivalent'_bijection_includes_all_FV :
    forall R t u,
      t ≡_α^R u ->
      t ∈ Tm (domm R).
  Proof.
    introv Hα.
    rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hxt.
    gen R u. induction t; introv Hα;
    destruct u; inverts Hα as Hα.
    - rewrite /= in_fsetD in_fset1 in Hxt. apply (rwP andP) in Hxt as [Hxns Hxt].
      cut (x ∈ domm R⦅s,s0⦆ = true).
      { introv HR'x.
        apply (rwP dommP) in HR'x as [v HR'x].
        rewrite unionmE remmE rem_valmE setmE /= in HR'x.
        destruct (x =P s); subst; auto.
        destruct (getm R x) eqn:HRx.
        - eapply (rwP dommP). eauto.
        - inverts HR'x. }
      eapply IHt; eauto.
    - apply (rwP andP) in Hα as [Hα1 Hα2].
      rewrite /= /in_mem /= in_fsetU in Hxt. apply (rwP orP) in Hxt as [Hx|Hx]; eauto.
    - apply (rwP getmP) in Hα.
      rewrite in_fset1 in Hxt. apply (rwP eqP) in Hxt. subst.
      apply (rwP dommP). eauto.
  Qed.

  Lemma α_equivalent'_bijection_includes_all_FV' :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u ->
      u ∈ Tm (codomm R).
  Proof.
    introv HRinj Hα.
    eapply α_equivalent'_converse in Hα; eauto.
    rewrite codomm_domm_invm //.
    eapply α_equivalent'_bijection_includes_all_FV; eauto.
  Qed.

  Lemma FV_respects_α_equivalence :
    forall t u,
      t ≡_α u ->
      FV u = FV t.
  Proof.
    introv Hα.
    replace (FV t) with (pimfset (getm (1__(FV t) : {fmap 𝒱 → 𝒱})) (FV t)); cycle 1.
    { apply eq_fset. intros x.
      rewrite in_pimfset.
      destruct (x ∈ FV t) eqn:Hxt.
      - apply (rwP imfsetP).
        exists x; auto.
        rewrite mkfmapfE Hxt //.
      - apply negbTE, (introN imfsetP). intros [y Hyt].
        rewrite mkfmapfE in H.
        rewrite Hyt in H. inverts H. rewrite Hyt // in Hxt. }
    eapply α_equivalent'_implies_related_FV; eauto.
    apply partial_bijection_identity.
  Qed.

  Lemma domm_identity : forall X, domm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    introv.
    apply eq_fset. intros x.
    destruct (x ∈ X) eqn:HxX.
    - apply (rwP dommP). exists x. rewrite mkfmapfE HxX //.
    - apply negbTE. apply (rwP dommPn). rewrite mkfmapfE HxX //.
  Qed.

  Lemma α_equivalent'_implies_α_equivalent :
    forall t u,
      t ≡_α u <-> exists X, t ≡_α^(1__X) u.
  Proof.
    introv.
    split; introv Hα; eauto.
    destruct Hα as [X Hα].
    apply α_equivalent'_with_behaviorally_identical_maps with (R := 1__X); auto.
    intros x y Hxy Hxt.
    rewrite /fmap_to_Prop mkfmapfE in Hxy.
    rewrite /fmap_to_Prop mkfmapfE Hxt.
    eapply α_equivalent'_bijection_includes_all_FV in Hα; eauto.
    rewrite domm_identity /= in Hα. apply (rwP fsubsetP) in Hα. apply Hα in Hxt. rewrite Hxt // in Hxy.
  Qed.

  Lemma compose_identity_right : forall R, R;;(1__(codomm R)) = R.
  Proof.
    introv.
    apply eq_fmap. intros x.
    rewrite mkfmapfpE.
    destruct (x ∈ domm R) eqn:HRx; rewrite HRx.
    - apply (rwP dommP) in HRx as [y HRx]. rewrite HRx mkfmapfE.
      destruct (y ∈ codomm R) eqn:HR'y; rewrite HR'y //.
      apply negbT in HR'y.
      rewrite <- (rwP (@codommPn _ 𝒱 _ _)) in HR'y.
      pose proof HR'y x as HRxny. rewrite HRx eq_refl // in HRxny.
    - apply negbT, (rwP dommPn) in HRx. auto.
  Qed.

  Lemma compose_identity_left : forall R, (1__(domm R));;R = R.
  Proof.
    introv.
    apply eq_fmap. intros x.
    rewrite mkfmapfpE mkfmapfE domm_mkfmapf in_fset.
    destruct (x ∈ domm R) eqn:HRx; rewrite HRx //.
    apply negbT, (rwP dommPn) in HRx. auto.
  Qed.

  Lemma codomm_identity : forall X, codomm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    introv.
    apply eq_fset. intros x.
    destruct (x ∈ X) eqn:HxX.
    - apply (rwP codommP). exists x. rewrite mkfmapfE HxX //.
    - apply negbTE. rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros y.
      apply (introN eqP). introv HXy.
      rewrite mkfmapfE in HXy.
      destruct (y ∈ X) eqn:HyX; rewrite HyX in HXy; inverts HXy.
      rewrite HyX // in HxX.
  Qed.

  Lemma compose_identity :
    forall X Y,
      (1__X);;(1__Y) = 1__(X ∩ Y).
  Proof.
    introv.
    apply eq_fmap. intros x.
    rewrite mkfmapfpE !mkfmapfE in_fsetI.
    destruct (x ∈ X) eqn:HxX; rewrite HxX;
    rewrite domm_identity HxX // mkfmapfE.
    destruct (x ∈ Y) eqn:HxY; rewrite HxY //.
  Qed.

  Lemma compose_identity' : forall X, (1__X);;(1__X) = 1__X.
  Proof.
    introv.
    pose proof codomm_identity X as Hℛ1.
    pose proof compose_identity_right (1__X) as Hℛ1r. rewrite Hℛ1 // in Hℛ1r.
  Qed.

  Lemma converse_identity : forall X, (1__X)ᵒ = 1__X.
  Proof.
    introv.
    apply eq_fmap. intros x.
    rewrite mkfmapfE.
    destruct (x ∈ X) eqn:HxX; rewrite HxX.
    - apply getm_inv. rewrite invmK.
      + rewrite mkfmapfE HxX //.
      + apply (rwP injectivemP). apply partial_bijection_identity.
    - apply invm_None.
      + apply partial_bijection_identity.
      + rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros x'.
        apply (introN eqP). introv Hxx'.
        rewrite mkfmapfE in Hxx'.
        destruct (x' ∈ X) eqn:Hx'X; rewrite Hx'X in Hxx'; inverts Hxx'.
        rewrite Hx'X // in HxX.
  Qed.

  (** Page 4: "≡α is... reflexive." *)
  Corollary α_equivalent_reflexive : forall t, t ≡_α t.
  Proof.
    introv. apply α_equivalent'_identity. rewrite /Tm /in_mem /= fsubsetxx //.
  Qed.

  (** Page 4: "≡α is... transitive." *)
  Corollary α_equivalent_transitive :
    forall t u (v : term),
      t ≡_α u ->
      u ≡_α v ->
      t ≡_α v.
  Proof.
    introv Htαu Huαv.
    pose proof α_equivalent'_compose _ _ _ _ _ Htαu Huαv as Htαv.
    rewrite compose_identity in Htαv.
    apply α_equivalent'_supermap with (R__sub := 1__(FV t ∩ FV u)); auto.
    intros k v' H1k.
    rewrite mkfmapfE in_fsetI in H1k.
    rewrite mkfmapfE.
    destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt //.
    destruct (k ∈ FV u) eqn:Hku; inverts H1k. auto.
  Qed.

  (** Page 4: "≡α is... symmetric." *)
  Corollary α_equivalent_symmetric :
    forall t u,
      t ≡_α u ->
      u ≡_α t.
  Proof.
    introv Hα.
    apply α_equivalent'_converse in Hα.
    - rewrite converse_identity in Hα.
      eapply α_equivalent'_implies_α_equivalent; eauto.
    - apply partial_bijection_identity.
  Qed.

  (** Page 4: Corollary 3. *)
  #[global] Instance α_equivalent_Equivalence : Equivalence α_equivalent.
  Proof.
    split; intros t.
    - apply α_equivalent_reflexive.
    - apply α_equivalent_symmetric.
    - apply α_equivalent_transitive.
  Qed.

  Add Parametric Relation : term α_equivalent
      reflexivity proved by α_equivalent_reflexive
      symmetry proved by α_equivalent_symmetric
      transitivity proved by α_equivalent_transitive
      as α_equivalent_rel.

  Add Parametric Morphism : FV
      with signature α_equivalent ==> eq as FV_morph.
  Proof.
    introv Hα. apply FV_respects_α_equivalence. symmetry. auto.
  Qed.

  (** Since Coq doesn't directly support quotient types, we're representing "Tm^α(X)" as "Tm(X)" and manually proving that functions respect "≡α". *)

  Implicit Types f g : {fmap 𝒱 → term}.

  (** Page 4: "Given a substitution f and x ∈ 𝒱, t ∈ Tm(Y) we define the update...." *)
  Definition update_substitution (A : Type) : {fmap 𝒱 → A} -> 𝒱 -> A -> {fmap 𝒱 → A} := @setm _ _.

  #[local] Notation "f '[' x ',' t ']'" :=
    (update_substitution f x t)
      (at level 10, x at next level, t at next level, format "f [ x ',' t ]").

  (** Page 4: "f[[x,t]] ∈ X ∪ {x} ⟶ ...." *)
  Lemma domm_update_substitution :
    forall f x t,
      domm (f[x,t]) = domm f ∪ {x}.
  Proof.
    introv.
    apply eq_fset. intros k.
    rewrite in_fsetU in_fset1.
    apply Bool.eq_iff_eq_true. split; introv Hk.
    - apply (rwP dommP) in Hk as [v Hf'k].
      rewrite setmE in Hf'k.
      destruct (k =P x); subst.
      { apply orbT. }
      rewrite orbF.
      apply (rwP dommP). eauto.
    - apply (rwP dommP).
      rewrite setmE.
      apply (rwP orP) in Hk as [Hfk|Hkx].
      + apply (rwP dommP) in Hfk as [v Hfk].
        destruct (k =P x); subst; eauto.
      + rewrite Hkx. eauto.
  Qed.

  Definition codomm_Tm_set f : {fset 𝒱} := ⋃_(i ∈ codomm f) (FV i).

  Lemma codomm_Tm_setP :
    forall {f} {x},
      reflect (exists t, x ∈ FV t /\ t ∈ codomm f) (x ∈ codomm_Tm_set f).
  Proof.
    introv.
    destruct (x ∈ codomm_Tm_set f) eqn:Hxℛf; constructor;
    rewrite /= /codomm_Tm_set in_bigcup in Hxℛf.
    - apply (rwP hasP) in Hxℛf as [t Hxℱf]. exists t. auto.
    - apply negbT, (rwP hasPn) in Hxℛf. intros (t & Hxt & Htℛf).
      apply Hxℛf in Htℛf. rewrite Hxt // in Htℛf.
  Qed.

  (** Page 4: "f[[x,t]] ∈ ... ⟶ Tm(Y)." *)
  Lemma codomm_update_substitution' :
    forall Y f x t,
      codomm_Tm_set f ⊆ Y ->
      t ∈ Tm Y ->
      codomm_Tm_set (f[x,t]) ⊆ Y.
  Proof.
    introv HℛfY HtY.
    apply (rwP fsubsetP) in HℛfY.
    apply (rwP fsubsetP). intros k Hℛf'k.
    apply (rwP codomm_Tm_setP) in Hℛf'k as (t' & Hkt' & Hℛf't').
    apply (rwP codommP) in Hℛf't' as [k' Hf'k'].
    rewrite setmE in Hf'k'.
    destruct (k' =P x); subst.
    { inverts Hf'k'. apply (rwP fsubsetP) in HtY. auto. }
    apply HℛfY, (rwP codomm_Tm_setP). exists t'. split; auto. apply (rwP codommP). eauto.
  Qed.

  #[local] Reserved Notation "'`⦇' f '⦈'" (format "'`⦇' f '⦈'").

  (** Page 4: "A substitution can be extended to a function on terms ⦇f⦈ ∈ Tm(X) ⟶ Tm(Y)...." *)
  Fixpoint lift_substitution' f Fresh t : term :=
    match t with
    | variable x => odflt t (getm f x)
    | application t u => application (`⦇f⦈ Fresh t) (`⦇f⦈ Fresh u)
    | abstraction x t =>
      let Y := codomm_Tm_set f in
      let z := Fresh Y in
      abstraction z (`⦇f[x,variable z]⦈ Fresh t)
    end

  where "'`⦇' f '⦈'" := (lift_substitution' f).

  Definition lift_substitution f : term -> term := `⦇f⦈ Fresh.

  #[local] Notation "'⦇' f '⦈'" := (lift_substitution f) (format "'⦇' f '⦈'").

  Lemma α_equivalent_update :
    forall R t u x y,
      x ∉ domm R ->
      y ∉ codomm R ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    introv HnRx HnR'y Hα.
    apply α_equivalent'_supermap with (R__sub := R); auto. introv HRk.
    apply (rwP dommPn) in HnRx.
    destruct (k =P x); subst.
    { rewrite HRk // in HnRx. }
    rewrite <- (rwP (@codommPn _ _ R y)) in HnR'y.
    destruct (y =P v); subst.
    { pose proof HnR'y k as HnRk. rewrite HRk eq_refl // in HnRk. }
    apply (introF eqP) in n, n0.
    rewrite unionmE remmE rem_valmE setmE n HRk n0 //.
  Qed.

  Lemma α_equivalent_update_reorder :
    forall R t u x y z z',
      z ∉ domm R ->
      z' ∉ codomm R ->
      t ≡_α^(R⦅x,y⦆) u ->
      t ≡_α^(R⦅z,z'⦆⦅x,y⦆) u.
  Proof.
    introv HnRz HnR'z' Hα.
    apply α_equivalent'_supermap with (R__sub := R⦅x,y⦆); auto. introv HR'k.
    rewrite unionmE remmE rem_valmE setmE /= in HR'k.
    repeat rewrite unionmE remmE rem_valmE setmE /=.
    destruct (k =P x); subst; auto.
    destruct (k =P z); subst.
    - destruct (getm R z) eqn:HRz; cycle 1.
      { inverts HR'k. }
      destruct (y =P s); subst; inverts HR'k.
      assert (z ∈ domm R) as H'Rz by (apply (rwP dommP); eauto). rewrite H'Rz // in HnRz.
    - destruct (getm R k) eqn:HRk; cycle 1.
      { inverts HR'k. }
      destruct (y =P s); subst; inverts HR'k.
      destruct (z' =P v); subst.
      { assert (v ∈ codomm R) as HR'v by (apply (rwP codommP); eauto). rewrite HR'v // in HnR'z'. }
      apply (introF eqP) in n1. rewrite /= n1 //.
  Qed.

  Lemma in_update :
    forall R x y z z',
      z ∉ domm R ->
      z' ∉ codomm R ->
      (x, y) ∈ R ->
      (x, y) ∈ R⦅z,z'⦆.
  Proof.
    introv HnRz HnR'z' HRx.
    apply (rwP getmP) in HRx.
    apply (rwP getmP).
    rewrite /update unionmE remmE rem_valmE setmE /= HRx.
    destruct (x =P z); subst.
    { assert (z ∈ domm R) as HRz by (apply (rwP dommP); eauto). rewrite HRz // in HnRz. }
    destruct (z' =P y); subst; auto.
    assert (y ∈ codomm R) as HR'y by (apply (rwP codommP); eauto). rewrite HR'y // in HnR'z'.
  Qed.

  Lemma update_repeat_noop :
    forall R x y,
      R⦅x,y⦆⦅x,y⦆ = R⦅x,y⦆.
  Proof.
    introv.
    apply eq_fmap. intros k.
    repeat rewrite !unionmE !remmE !rem_valmE !setmE /=.
    destruct (k =P x); subst; auto.
    destruct (getm R k) eqn:HRk; auto.
    destruct (y =P s); subst; auto.
    apply (introF eqP) in n0. rewrite /= n0 //.
  Qed.

  Lemma codomm_Tm_setPn :
    forall {f} {x},
      reflect (forall t, ~ (x ∈ FV t /\ t ∈ codomm f)) (x ∉ codomm_Tm_set f).
  Proof.
    introv.
    destruct (x ∉ codomm_Tm_set f) eqn:Hnℛf;
    rewrite /= /codomm_Tm_set in_bigcup in Hnℛf;
    constructor; introv H.
    - destruct H as [Hxt Htℛf].
      apply negbTE, Bool.not_true_iff_false in Hnℛf. apply Hnℛf.
      apply (rwP hasP). exists t; auto.
    - apply Bool.negb_false_iff, (rwP hasP) in Hnℛf as [t Htℛf].
      apply H with t. auto.
  Qed.

  Lemma α_equivalent'_with_behaviorally_identical_maps' :
    forall R S t u,
      (forall x y, R x y -> x ∈ FV t -> y ∈ FV u -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    introv HReqvS Hα.
    gen R S u. induction t; introv HReqvS Hα;
    destruct u; inverts Hα.
    - apply IHt with (R := R⦅s,s0⦆); auto. introv HR'x Hxt Hyu.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in HR'x.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
      destruct (x =P s); subst; auto.
      destruct (getm R x) eqn:HRx; cycle 1.
      { inverts HR'x. }
      destruct (s0 =P s1); subst; inverts HR'x.
      apply HReqvS in HRx.
      + rewrite HRx. apply (introF eqP) in n0. rewrite n0 //.
      + rewrite /= in_fsetD in_fset1 Hxt andbT. apply (introF eqP) in n. rewrite n //.
      + rewrite in_fsetD in_fset1 Hyu andbT. apply not_eq_sym, (introF eqP) in n0. rewrite n0 //.
    - apply (rwP andP) in H0 as [Hα1 Hα2].
      simpl. rewrite <- (rwP andP). split;
      (apply IHt1 with R + apply IHt2 with R); auto;
      introv HRx Hxt Hyu;
      apply HReqvS; auto;
      rewrite /= in_fsetU ?Hxt ?Hyu ?orbT //.
    - apply (rwP getmP), HReqvS in H0.
      + apply (rwP getmP). rewrite H0 //.
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
    introv HRtype HRinj HSinj HRα Hnzℛf Hnz'ℛg HR'w.
    rewrite /fmap_to_Prop /update unionmE remmE rem_valmE setmE /= in HR'w.
    rewrite /update_substitution /update !setmE.
    destruct (w =P x); subst.
    - inverts HR'w.
      rewrite !eq_refl.
      apply (rwP getmP).
      rewrite /= unionmE remmE rem_valmE eq_refl setmE eq_refl //.
    - destruct (getm R w) eqn:HRw; cycle 1.
      { inverts HR'w. }
      destruct (y =P s); subst; inverts HR'w.
      apply not_eq_sym, (introF eqP) in n0. rewrite n0.
      pose proof HRw as H'Rw. apply HRα in H'Rw. inverts H'Rw.
      rewrite <- (rwP is_subset_ofP) in HRtype.
      apply HRtype in HRw as [Hfw Hα].
      apply (rwP dommP) in Hfw as [t Hfw], Hα as [t' Hgw'].
      rewrite -> Hfw, Hgw' in *.
      apply α_equivalent'_with_behaviorally_identical_maps' with (R := S); auto. intros x' y' HSx' Hx't Hy't'.
      rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /=.
      destruct (x' =P z); subst.
      { rewrite <- (rwP codomm_Tm_setPn) in Hnzℛf.
        exfalso. apply Hnzℛf with t. split; auto.
        apply (rwP codommP). eauto. }
      rewrite HSx'.
      destruct (z' =P y'); subst; auto.
      rewrite <- (rwP codomm_Tm_setPn) in Hnz'ℛg.
      exfalso. apply Hnz'ℛg with t'. split; auto.
      apply (rwP codommP). eauto.
  Qed.

  Lemma subset_domm_substitution :
    forall f x t,
      domm f ⊆ domm (f[x,t]).
  Proof.
    introv.
    apply (rwP fsubsetP). intros x' Hfx'.
    apply (rwP dommP) in Hfx' as [t' Hfx'].
    apply (rwP dommP).
    rewrite setmE.
    destruct (x' =P x); subst; eauto.
  Qed.

  (** Page 4: Proposition 4. *)
  #[program] Proposition substitution'_preserves_α_congruence' :
    forall Fresh R S f g,
      Fresh_correct Fresh ->
      R ⊆ domm f × domm g ->
      partial_bijection R ->
      partial_bijection S ->
      (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
      forall t u, t ≡_α^R u -> `⦇f⦈ Fresh t ≡_α^S `⦇g⦈ Fresh u.
  Proof.
    introv HFresh HRtype HRinj HSinj HRα Hα.
    gen R S f g u. induction t; introv HRinj HSinj HRtype HRα Hα;
    destruct u; inverts Hα.
    - eapply IHt with (R := R⦅s,s0⦆); eauto.
      + apply partial_bijection_update. auto.
      + apply partial_bijection_update. auto.
      + rewrite !domm_set /=. apply (rwP is_subset_ofP). intros x y HR'x.
        rewrite /= !in_fsetU !in_fset1.
        rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in HR'x.
        destruct (x =P s); subst.
        { inverts HR'x. rewrite eq_refl //. }
        destruct (getm R x) eqn:HRx; cycle 1.
        { inverts HR'x. }
        destruct (s0 =P s1); subst; inverts HR'x.
        rewrite <- (rwP is_subset_ofP) in HRtype.
        apply HRtype in HRx as [Hnxs Hns0y]. simpl in *. rewrite Hnxs Hns0y orbT //.
      + introv HR'x. eapply lemma5; eauto; apply Fresh_correct.
    - apply (rwP andP) in H0 as [Hα1 Hα2].
      eapply IHt1 with (S := S) in Hα1; eauto.
      eapply IHt2 with (S := S) in Hα2; eauto.
      rewrite /= Hα1 Hα2 //.
    - apply (rwP getmP) in H0.
      pose proof H0 as HRs. apply HRα in HRs.
      rewrite <- (rwP is_subset_ofP) in HRtype.
      apply HRtype in H0 as [Hfs Hgs0].
      simpl in *. apply (rwP dommP) in Hfs as [v Hfs], Hgs0 as [v' Hgs0].
      rewrite -> Hfs, Hgs0 in *. auto.
  Qed.

  #[program] Proposition substitution_preserves_α_congruence' :
    forall R S f g,
      R ⊆ domm f × domm g ->
      partial_bijection R ->
      partial_bijection S ->
      (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
      forall t u, t ≡_α^R u -> ⦇f⦈ t ≡_α^S ⦇g⦈ u.
  Proof.
    introv HRtype HRinj HSinj HRα Hα.
    eapply substitution'_preserves_α_congruence'; eauto.
    apply HFresh.
  Qed.

  #[program] Corollary substitution'_preserves_α_congruence_identity :
    forall Fresh f g,
      Fresh_correct Fresh ->
      (forall x, x ∈ domm f ∩ domm g ->
            getm f x `≡_α^(1__(codomm_Tm_set f ∩ codomm_Tm_set g)) getm g x) ->
      forall t u, t ≡_α^(1__(domm f ∩ domm g)) u ->
             `⦇f⦈ Fresh t ≡_α^(1__(codomm_Tm_set f ∩ codomm_Tm_set g)) `⦇g⦈ Fresh u.
  Proof.
    introv HFresh Hα Htαu.
    eapply substitution'_preserves_α_congruence'; eauto;
    try apply partial_bijection_identity;
    try apply (rwP is_subset_ofP); intros x y Hxy;
    rewrite /fmap_to_Prop mkfmapfE in_fsetI in Hxy;
    destruct (x ∈ domm f) eqn:Hfx; inverts Hxy as Hxy;
    destruct (x ∈ domm g) eqn:Hgx; inverts Hxy as Hxy.
    - rewrite Hgx //.
    - apply Hα. rewrite /= in_fsetI Hgx Hfx //.
  Qed.

  #[program] Corollary substitution_preserves_α_congruence_identity :
    forall f g,
      (forall x, x ∈ domm f ∩ domm g ->
            getm f x `≡_α^(1__(codomm_Tm_set f ∩ codomm_Tm_set g)) getm g x) ->
      forall t u, t ≡_α^(1__(domm f ∩ domm g)) u ->
             ⦇f⦈ t ≡_α^(1__(codomm_Tm_set f ∩ codomm_Tm_set g)) ⦇g⦈ u.
  Proof.
    introv Hα Htαu.
    eapply substitution'_preserves_α_congruence_identity; eauto.
    apply HFresh.
  Qed.

  (** Page 5: "Clearly, the preservation property arises as a special case by setting R = 1X and S = 1Y." *)
  #[program] Theorem substitution'_preserves_α_congruence :
    forall Fresh f g,
      Fresh_correct Fresh ->
      (forall x, x ∈ domm f ∩ domm g ->
            getm f x `≡_α getm g x) ->
      forall t u, t ∈ Tm (domm f ∩ domm g) ->
             t ≡_α u ->
             `⦇f⦈ Fresh t ≡_α `⦇g⦈ Fresh u.
  Proof.
    introv HFresh Hα Hfgt Htαu.
    eapply α_equivalent'_implies_α_equivalent. exists (codomm_Tm_set f ∩ codomm_Tm_set g).
    apply substitution'_preserves_α_congruence_identity; auto.
    - introv Hfgx.
      pose proof Hfgx as H'fgx.
      rewrite in_fsetI in Hfgx. apply (rwP andP) in Hfgx as [Hfx Hgx].
      apply Hα in H'fgx.
      apply (rwP dommP) in Hfx as [y__f Hfx], Hgx as [y__g Hgx].
      rewrite Hfx Hgx /=. rewrite Hfx Hgx /= in H'fgx.
      apply α_equivalent'_supermap with (R__sub := 1__(FV y__f)); auto.
      introv Hkv.
      rewrite mkfmapfE in Hkv.
      destruct (k ∈ FV y__f) eqn:Hky__f; rewrite Hky__f in Hkv; inverts Hkv.
      rewrite mkfmapfE in_fsetI.
      assert (v ∈ codomm_Tm_set f) as Hℛfv.
      { apply (rwP codomm_Tm_setP). exists y__f. split; auto.
        apply (rwP codommP). eauto. }
      assert (v ∈ codomm_Tm_set g) as Hℛgv.
      { apply (rwP codomm_Tm_setP). exists y__g.
        apply FV_respects_α_equivalence in H'fgx.
        rewrite H'fgx. split; auto.
        apply (rwP codommP). eauto. }
      rewrite Hℛfv Hℛgv //.
    - apply α_equivalent'_supermap with (R__sub := 1__(FV t)); auto.
      introv Hkv.
      rewrite mkfmapfE in Hkv.
      destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt in Hkv; inverts Hkv.
      apply (rwP fsubsetP) in Hfgt. apply Hfgt in Hkt. rewrite mkfmapfE Hkt //.
  Qed.

  #[program] Theorem substitution_preserves_α_congruence :
    forall f g,
      (forall x, x ∈ domm f ∩ domm g ->
            getm f x `≡_α getm g x) ->
      forall t u, t ∈ Tm (domm f ∩ domm g) ->
             t ≡_α u ->
             ⦇f⦈ t ≡_α ⦇g⦈ u.
  Proof.
    introv Hα Hfgt Htαu.
    eapply substitution'_preserves_α_congruence; eauto.
    apply HFresh.
  Qed.

  (** Page 5: "A consequence of proposition 4 is that substitution is an operation on α-equivalence classes." *)
  Theorem lift_substitution'_respects_α_equivalence :
    forall Fresh f t u,
      Fresh_correct Fresh ->
      t ∈ Tm (domm f) ->
      t ≡_α u ->
      `⦇f⦈ Fresh t ≡_α `⦇f⦈ Fresh u.
  Proof.
    introv HFresh Hft Hα.
    eapply substitution'_preserves_α_congruence; eauto.
    - reflexivity.
    - rewrite fsetIid //.
  Qed.

  Theorem lift_substitution_respectsα_equivalence :
    forall f t u,
      t ∈ Tm (domm f) ->
      t ≡_α u ->
      ⦇f⦈ t ≡_α ⦇f⦈ u.
  Proof.
    introv Hft Hα.
    apply lift_substitution'_respects_α_equivalence; auto.
    apply HFresh.
  Qed.

  Lemma codomm_Tm_set_mapm_variable :
    forall R,
      codomm_Tm_set (mapm variable R) = codomm R.
  Proof.
    introv.
    apply eq_fset. intros t.
    apply Bool.eq_iff_eq_true. split; introv HR't.
    - apply (rwP codomm_Tm_setP) in HR't as (x & Hxt & HR'x).
      apply (rwP codommP) in HR'x as [k HR'k].
      rewrite mapmE in HR'k.
      destruct (getm R k) eqn:HRk; inverts HR'k.
      rewrite in_fset1 in Hxt. apply (rwP eqP) in Hxt. subst.
      apply (rwP codommP). eauto.
    - apply (rwP codommP) in HR't as [k HRk].
      apply (rwP codomm_Tm_setP). exists (variable t). split.
      + rewrite in_fset1 eq_refl //.
      + apply (rwP codommP). exists k. rewrite mapmE HRk //.
  Qed.

  (** Page 6: Lemma 7. *)
  Lemma lemma7' :
    forall Fresh (f : {fmap 𝒱 → 𝒱}) t,
      Fresh_correct Fresh ->
      partial_bijection f ->
      t ∈ Tm (domm f) ->
      `⦇mapm variable f⦈ Fresh t ≡_α^(f ᵒ) t.
  Proof.
    introv HFresh Hfinj Hft.
    apply (rwP fsubsetP) in Hft.
    gen f. induction t; introv Hfinj Hft; simpl in *.
    - rewrite /= /update_substitution -mapm_setm -/update_substitution -update_converse //.
      rewrite codomm_Tm_set_mapm_variable.
      replace (setm f s (Fresh0 (codomm f))) with (f⦅s,Fresh0 (codomm f)⦆); cycle 1.
      { apply eq_fmap. intros x.
        rewrite unionmE remmE rem_valmE !setmE /=.
        destruct (x =P s); subst; auto.
        destruct (getm f x) eqn:Hfx; auto.
        destruct (Fresh0 (codomm f) =P s0); subst; auto.
        assert (Fresh0 (codomm f) ∈ codomm f) as HFreshℛf. { apply (rwP codommP). eauto. }
        pose proof HFresh (codomm f) as HnFresh. rewrite HFreshℛf // in HnFresh. }
      apply IHt; auto.
      + apply partial_bijection_update. auto.
      + introv Hxt.
        apply (rwP dommP).
        rewrite unionmE remmE rem_valmE setmE /=.
        destruct (x =P s); subst; simpl; eauto.
        assert (x ∈ FV t :\ s) as Hxtns.
        { apply (introF eqP) in n. rewrite in_fsetD in_fset1 n Hxt //. }
        apply Hft, (rwP dommP) in Hxtns as [v Hfx]. rewrite Hfx /=.
        destruct (Fresh0 (codomm f) =P v); subst; simpl; eauto.
        assert (Fresh0 (codomm f) ∈ codomm f) as HFreshℛf. { apply (rwP codommP). eauto. }
        pose proof HFresh (codomm f) as HnFresh. rewrite HFreshℛf // in HnFresh.
    - rewrite <- (rwP andP). split.
      + apply IHt1; auto. introv Hxt1.
        apply Hft. rewrite in_fsetU Hxt1 //.
      + apply IHt2; auto. introv Hxt2.
        apply Hft. rewrite in_fsetU Hxt2 orbT //.
    - apply α_equivalent'_converse; auto.
      rewrite /= mapmE.
      assert (s ∈ fset1 s) as Hss. { rewrite in_fset1 eq_refl //. }
      apply Hft, (rwP dommP) in Hss as [v Hfs].
      rewrite Hfs /=. apply (rwP getmP). auto.
  Qed.

  Lemma lemma7 :
    forall (f : {fmap 𝒱 → 𝒱}) t,
      partial_bijection f ->
      t ∈ Tm (domm f) ->
      ⦇mapm variable f⦈ t ≡_α^(f ᵒ) t.
  Proof.
    introv Hfinj Hft.
    apply lemma7'; auto. apply HFresh.
  Qed.

  (** Page 6: "η(x) = x." *)
  Definition η__ X : {fmap 𝒱 → term} := 1__X.

  (** Page 6: "ηX ∈ X ⟶ ...." *)
  Lemma domm_η :
    forall X,
      domm (η__ X) = X.
  Proof.
    introv.
    rewrite domm_map. apply domm_identity.
  Qed.

  (** Page 6: "ηX ∈ ... ⟶ Tm^α(X)." *)
  Lemma codomm_Tm_set_η :
    forall X,
      codomm_Tm_set (η__ X) = X.
  Proof.
    introv.
    apply eq_fset. intros x.
    apply Bool.eq_iff_eq_true. split; introv HxX.
    - apply (rwP codomm_Tm_setP) in HxX as (t & Hxt & Hℛηt).
      apply (rwP codommP) in Hℛηt as [x' Hℛηt].
      rewrite mapmE mkfmapfE in Hℛηt.
      destruct (x' ∈ X) eqn:Hx'X; rewrite Hx'X in Hℛηt; inverts Hℛηt.
      rewrite in_fset1 in Hxt. apply (rwP eqP) in Hxt. subst. auto.
    - apply (rwP codomm_Tm_setP). exists (variable x). split.
      { rewrite /= in_fset1 eq_refl //. }
      apply (rwP codommP). exists x.
      rewrite mapmE mkfmapfE HxX //.
  Qed.

  Lemma update_substitution_overwrite :
    forall f x y y',
      f[x,variable y][x,variable y'] = f[x, variable y'].
  Proof.
    introv.
    apply eq_fmap. intros x'.
    rewrite !setmE.
    destruct (x' =P x); subst; auto.
  Qed.

  Lemma update_substitution_reorder :
    forall f x x' y y',
      x <> x' ->
      f[x,variable y][x',variable y'] = f[x',variable y'][x,variable y].
  Proof.
    introv Hnxx'.
    apply eq_fmap. intros z.
    rewrite !setmE.
    destruct (z =P x); subst; auto.
    apply (introF eqP) in Hnxx'. rewrite Hnxx' //.
  Qed.

  Lemma α_equivalent_update' :
    forall R t u x y,
      x ∉ FV t ->
      y ∉ FV u ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    introv Hnxt Hnyu Hα.
    apply α_equivalent'_with_behaviorally_identical_maps' with (R := R); auto. intros x' y' HRx' Hx't Hy'u.
    rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE.
    destruct (x' =P x); subst.
    { rewrite Hx't // in Hnxt. }
    rewrite HRx'.
    destruct (y =P y'); subst; auto.
    rewrite Hy'u // in Hnyu.
  Qed.

  Lemma FV_lift_substitution' :
    forall Fresh f t,
      Fresh_correct Fresh ->
      t ∈ Tm (domm f) ->
      FV (`⦇f⦈ Fresh t) = ⋃_(u ∈ pimfset (getm f) (FV t)) (FV u).
  Proof.
    introv HFresh Hft.
    apply (rwP fsubsetP) in Hft.
    apply eq_fset. intros x.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true.
    split; introv H.
    - apply (rwP hasP).
      gen f. induction t; intros; simpl in *.
      + rewrite in_fsetD in_fset1 in H. apply (rwP andP) in H as [HnxFresh Hℛfx].
        apply IHt in Hℛfx as [y Hℛfy Hxy].
        * apply (rwP pimfsetP) in Hℛfy as [k Hkt Hf'k].
          rewrite setmE in Hf'k.
          destruct (k =P s); subst.
          { inverts Hf'k. rewrite in_fset1 in Hxy. rewrite Hxy // in HnxFresh. }
          exists y; auto.
          apply (rwP pimfsetP). exists k; auto.
          apply (introF eqP) in n.
          rewrite in_fsetD in_fset1 n Hkt //.
        * intros y Hyt.
          rewrite domm_update_substitution in_fsetU in_fset1 orbC.
          destruct (y =P s); subst; auto.
          apply (introF eqP) in n.
          apply Hft. rewrite in_fsetD in_fset1 n Hyt //.
      + rewrite in_fsetU in H. apply (rwP orP) in H as [Hf'x|Hf'x].
        * apply IHt1 in Hf'x as [k Hf'k Hxk]; cycle 1.
          { intros k Hkt1. apply Hft. rewrite in_fsetU Hkt1 //. }
          apply (rwP pimfsetP) in Hf'k as [y Hyt1 Hfy].
          exists k; auto.
          apply (rwP pimfsetP). exists y; auto.
          rewrite in_fsetU Hyt1 //.
        * apply IHt2 in Hf'x as [k Hf'k Hxk]; cycle 1.
          { intros k Hkt2. apply Hft. rewrite in_fsetU Hkt2 orbT //. }
          apply (rwP pimfsetP) in Hf'k as [y Hyt2 Hfy].
          exists k; auto.
          apply (rwP pimfsetP). exists y; auto.
          rewrite in_fsetU Hyt2 orbT //.
      + assert (s ∈ fset1 s) as Hss. { rewrite in_fset1 eq_refl //. }
        apply Hft, (rwP dommP) in Hss as [v Hfs].
        exists v.
        * apply (rwP (@pimfsetP _ _ (getm f) (fset1 s) v)). exists s; auto.
          rewrite in_fset1 eq_refl //.
        * rewrite Hfs // in H.
    - apply (rwP hasP) in H as [t' Hft' Hxt'].
      apply (rwP pimfsetP) in Hft' as [x' Hx't Hfx'].
      gen f. induction t; introv Hftns Hfx'; simpl in *.
      + rewrite in_fsetD in_fset1 in Hx't. apply (rwP andP) in Hx't as [Hnx's Hx't].
        rewrite in_fsetD in_fset1.
        assert (x ∈ codomm_Tm_set f) as Hℛfx.
        { apply (rwP codomm_Tm_setP). exists t'. split; auto. apply (rwP codommP). eauto. }
        pose proof HFresh (codomm_Tm_set f) as HFreshℛf.
        destruct (x =P Fresh0 (codomm_Tm_set f)); subst.
        { rewrite Hℛfx // in HFreshℛf. }
        apply IHt; auto.
        * intros y Hyt.
          rewrite domm_set in_fsetU in_fset1.
          destruct (y =P s); subst; auto.
          apply (introF eqP) in n0.
          apply Hftns.
          rewrite in_fsetD in_fset1 n0 Hyt //.
        * apply negbTE in Hnx's. rewrite setmE Hnx's //.
      + rewrite in_fsetU.
        rewrite in_fsetU in Hx't.
        apply (rwP orP) in Hx't as [Hx't1|Hx't2].
        * eapply IHt1 in Hx't1; eauto.
          -- rewrite Hx't1 //.
          -- intros y Hyt1. apply Hftns. rewrite in_fsetU Hyt1 //.
        * eapply IHt2 in Hx't2; eauto.
          -- rewrite Hx't2 orbT //.
          -- intros y Hyt2. apply Hftns. rewrite in_fsetU Hyt2 orbT //.
      + rewrite in_fset1 in Hx't. apply (rwP eqP) in Hx't. subst.
        rewrite Hfx' //.
  Qed.

  Lemma FV_lift_substitution :
    forall f t,
      t ∈ Tm (domm f) ->
      FV (⦇f⦈ t) = ⋃_(u ∈ pimfset (getm f) (FV t)) (FV u).
  Proof.
    introv Htf.
    apply FV_lift_substitution'; auto. apply HFresh.
  Qed.

  (** Page 4: "⦇f⦈ ∈ Tm(X) ⟶ Tm(Y)." *)
  Lemma lift_substitution_type :
    forall f t,
      t ∈ Tm (domm f) ->
      ⦇f⦈ t ∈ Tm (codomm_Tm_set f).
  Proof.
    introv Hft.
    rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hf'x.
    rewrite FV_lift_substitution // in_bigcup in Hf'x. apply (rwP hasP) in Hf'x as [t' Hf't' Hxt'].
    apply (rwP pimfsetP) in Hf't' as [x' Hx't Hfx'].
    apply (rwP codomm_Tm_setP). exists t'. split; auto.
    apply (rwP codommP). eauto.
  Qed.

  #[program] Lemma lift_substitution'_indistinguishable_substitutions' :
    forall Fresh R f g t,
      Fresh_correct Fresh ->
      t ∈ Tm (domm f ∩ domm g) ->
      (forall x, x ∈ FV t -> getm f x `≡_α^R getm g x) ->
      `⦇f⦈ Fresh t ≡_α^R `⦇g⦈ Fresh t.
  Proof.
    introv HFresh Hfgt Hα.
    apply (rwP fsubsetP) in Hfgt.
    gen R f g. induction t; intros.
    - apply IHt; simpl; introv Hxt.
      + rewrite in_fsetI !domm_set !in_fsetU !in_fset1.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        assert (x ∈ FV t :\ s) as Hxtns. { rewrite in_fsetD in_fset1 n Hxt //. }
        apply Hfgt in Hxtns. rewrite /= in_fsetI in Hxtns. apply (rwP andP) in Hxtns as [Hfx Hgx].
        rewrite Hfx Hgx //.
      + rewrite !setmE.
        destruct (x =P s); subst.
        { apply (rwP getmP). rewrite /= unionmE remmE rem_valmE setmE eq_refl //. }
        apply (introF eqP) in n.
        assert (x ∈ FV t :\ s) as Hxtns. { rewrite in_fsetD in_fset1 n Hxt //. }
        pose proof Hxtns as H'xtns. apply Hα in H'xtns.
        apply Hfgt in Hxtns. rewrite in_fsetI in Hxtns. apply (rwP andP) in Hxtns as [Hfx Hgx].
        apply (rwP dommP) in Hfx as [t__f Hfx], Hgx as [t__g Hgx].
        apply α_equivalent_update'; eauto;
        apply negbT, Bool.not_true_iff_false; introv HFreshℛf;
        rewrite ?Hfx ?Hgx /= in HFreshℛf.
        * pose proof HFresh (codomm_Tm_set f) as HFreshf. rewrite <- (rwP codomm_Tm_setPn) in HFreshf.
          apply (HFreshf t__f). split; auto. apply (rwP codommP). eauto.
        * pose proof HFresh (codomm_Tm_set g) as HFreshg. rewrite <- (rwP codomm_Tm_setPn) in HFreshg.
          apply (HFreshg t__g). split; auto. apply (rwP codommP). eauto.
    - simpl. rewrite <- (rwP andP). split;
      (apply IHt1 || apply IHt2); introv Hxt;
      (apply Hfgt || apply Hα); rewrite /= in_fsetU Hxt ?orbT //.
    - apply Hα. rewrite /= in_fset1 eq_refl //.
  Qed.

  #[program] Lemma lift_substitution'_indistinguishable_substitutions :
    forall Fresh f g t,
      Fresh_correct Fresh ->
      t ∈ Tm (domm f ∩ domm g) ->
      (forall x, x ∈ FV t -> getm f x `≡_α getm g x) ->
      `⦇f⦈ Fresh t ≡_α `⦇g⦈ Fresh t.
  Proof.
    introv HFresh Hfgt Hα.
    apply lift_substitution'_indistinguishable_substitutions'; auto.
    introv Hxt.
    apply (rwP fsubsetP) in Hfgt.
    pose proof Hxt as H'xt. pose proof Hxt as H''xt. apply Hα in Hxt.
    apply Hfgt in H'xt. rewrite /= in_fsetI in H'xt. apply (rwP andP) in H'xt as [Hfx Hgx].
    apply (rwP dommP) in Hfx as [t__f Hfx].
    eapply α_equivalent'_supermap; cycle 1.
    { apply Hxt. }
    introv Hf'k.
    rewrite mkfmapfE Hfx in Hf'k. inverts Hf'k as Hf'k.
    destruct (k ∈ FV t__f) eqn:Hkt__f; rewrite Hkt__f in Hf'k; inverts Hf'k.
    rewrite mkfmapfE Hkt__f.
    cut (v ∈ FV (`⦇f⦈ Fresh0 t) : Prop). { introv Hf'v. rewrite Hf'v //. }
    rewrite FV_lift_substitution' //; cycle 1.
    { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros x' Hx't.
      apply Hfgt in Hx't. rewrite /= in_fsetI in Hx't. apply (rwP andP) in Hx't as [Hfx' Hgx']. auto. }
    rewrite in_bigcup. apply (rwP hasP). exists t__f; auto.
    apply (rwP pimfsetP). eauto.
  Qed.

  #[program] Lemma lift_substitution_indistinguishable_substitutions :
    forall f g t,
      t ∈ Tm (domm f ∩ domm g) ->
      (forall x, x ∈ FV t -> getm f x `≡_α getm g x) ->
      ⦇f⦈ t ≡_α ⦇g⦈ t.
  Proof.
    introv Hfgt Hα.
    apply lift_substitution'_indistinguishable_substitutions; auto. apply HFresh.
  Qed.

  (** Page 7: "We have to show ⦇f[[z0 = z1]]⦈ ∘ g[[x = z0]](v) ≡α (⦇f⦈ ∘ g)[[x = z1]](v)." *)
  #[program] Lemma lift_update_substitution'_compose_substitution_update :
    forall Fresh f g x z0 z1,
      Fresh_correct Fresh ->
      codomm_Tm_set g ⊆ domm f ->
      z1 ∉ codomm_Tm_set f ->
      z0 ∉ codomm_Tm_set g ->
      forall v, v ∈ (domm g ∪ {x}) ->
           getm (`⦇f[z0,variable z1]⦈ Fresh ∘ g[x,variable z0]) v `≡_α getm ((`⦇f⦈ Fresh ∘ g)[x,variable z1]) v.
  Proof.
    introv HFresh Hℛgf Hnℛfz1 Hnℛgz0 Hg'v.
    apply (rwP fsubsetP) in Hℛgf.
    rewrite !setmE !mapmE /= !setmE.
    rewrite in_fsetU in_fset1 in Hg'v. apply (rwP orP) in Hg'v as [Hgv|Hvx]; cycle 1.
    { rewrite Hvx /= setmE eq_refl. reflexivity. }
    destruct (v =P x); subst.
    { rewrite /= setmE eq_refl. reflexivity. }
    apply (rwP dommP) in Hgv as [t Hgv]. rewrite Hgv /=.
    apply lift_substitution'_indistinguishable_substitutions; auto.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros x' Hx't.
      rewrite domm_set in_fsetI in_fsetU in_fset1 orbC.
      destruct (x' ∈ domm f) eqn:Hfx'; auto.
      assert (x' ∈ codomm_Tm_set g) as Hℛgx'.
      { apply (rwP codomm_Tm_setP). exists t. split; auto. apply (rwP codommP). eauto. }
      apply Hℛgf in Hℛgx'. rewrite /= Hfx' // in Hℛgx'.
    - intros x' Hx't.
      rewrite setmE.
      destruct (x' =P z0); subst.
      + assert (z0 ∈ codomm_Tm_set g) as Hℛgz0.
        { apply (rwP codomm_Tm_setP). exists t. split; auto. apply (rwP codommP). eauto. }
        rewrite Hℛgz0 // in Hnℛgz0.
      + reflexivity.
  Qed.

  #[program] Lemma lift_update_substitution_compose_substitution_update :
    forall f g x z0 z1,
      codomm_Tm_set g ⊆ domm f ->
      z1 ∉ codomm_Tm_set f ->
      z0 ∉ codomm_Tm_set g ->
      forall v, v ∈ (domm g ∪ {x}) ->
           getm (⦇f[z0,variable z1]⦈ ∘ g[x,variable z0]) v `≡_α getm ((⦇f⦈ ∘ g)[x,variable z1]) v.
  Proof.
    introv Hℛgf Hnℛfz1 Hnℛgz0 Hg'v.
    apply lift_update_substitution'_compose_substitution_update; auto. apply HFresh.
  Qed.

  Lemma FV_lift_substitution'_η :
    forall Fresh X t,
      Fresh_correct Fresh ->
      t ∈ Tm X ->
      FV (`⦇η__ X⦈ Fresh t) = FV t.
  Proof.
    introv HFresh HtX.
    apply (rwP fsubsetP) in HtX.
    rewrite FV_lift_substitution'; auto; cycle 1.
    { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hxt.
      rewrite domm_map domm_mkfmapf in_fset. apply HtX. auto. }
    apply eq_fset. intros x.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true. split; introv Hxt.
    - apply (rwP hasP) in Hxt as [x' Hx't Hxx'].
      apply (rwP pimfsetP) in Hx't as [y Hyt Hηy].
      rewrite mapmE mkfmapfE in Hηy.
      destruct (y ∈ X) eqn:HyX; rewrite HyX in Hηy; inverts Hηy.
      rewrite in_fset1 in Hxx'. apply (rwP eqP) in Hxx'. subst. auto.
    - apply (rwP hasP). exists (variable x).
      + apply (rwP pimfsetP). exists x; auto.
        apply HtX in Hxt.
        rewrite mapmE mkfmapfE Hxt //.
      + rewrite in_fset1 eq_refl //.
  Qed.

  (** Page 6: Proposition 6.1. *)
  Proposition monad_substitution'1 :
    forall Fresh X t,
      Fresh_correct Fresh ->
      t ∈ Tm X ->
      `⦇η__ X⦈ Fresh t ≡_α t.
  Proof.
    introv HFresh HtX.
    apply (rwP fsubsetP) in HtX.
    transitivity (`⦇η__(FV t)⦈ Fresh0 t).
    { apply lift_substitution'_indistinguishable_substitutions; auto.
      - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hxt.
        rewrite in_fsetI !domm_map domm_mkfmapf domm_mkfmapf !in_fset Hxt andbT. auto.
      - introv Hxt.
        rewrite !mapmE !mkfmapfE Hxt. apply HtX in Hxt. rewrite Hxt. reflexivity. }
    rewrite /α_equivalent -converse_identity.
    rewrite FV_lift_substitution'_η //.
    apply lemma7'; auto.
    - apply partial_bijection_identity.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hxt. rewrite domm_mkfmapf in_fset Hxt //.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hxt. auto.
  Qed.

  Proposition monad_substitution1 :
    forall X t,
      t ∈ Tm X ->
      ⦇η__ X⦈ t ≡_α t.
  Proof.
    introv HtX.
    apply monad_substitution'1; auto. apply HFresh.
  Qed.

  (** Page 6: Proposition 6.2. *)
  #[program] Proposition monad_substitution2 :
    forall f x,
      x ∈ domm f ->
      getm (⦇f⦈ ∘ η__(domm f)) x `≡_α getm f x.
  Proof.
    introv Hfx. rewrite !mapmE mkfmapfE Hfx. reflexivity.
  Qed.

  #[program] Lemma codomm_Tm_set_mapm_lift_substitution' :
    forall Fresh f g,
      Fresh_correct Fresh ->
      codomm_Tm_set g ⊆ domm f ->
      codomm_Tm_set (mapm (`⦇f⦈ Fresh) g) = ⋃_(x ∈ codomm_Tm_set g) (FV (odflt (variable _) (getm f x))).
  Proof.
    introv HFresh Hfℛg.
    apply (rwP fsubsetP) in Hfℛg.
    apply eq_fset. intros x.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true. split; introv Hfgx.
    - apply (rwP codomm_Tm_setP) in Hfgx as (t & Hxt & Hfgt).
      apply (rwP codommP) in Hfgt as [t' Hfgt'].
      rewrite mapmE in Hfgt'.
      destruct (getm g t') eqn:Hgt'; inverts Hfgt'.
      rewrite FV_lift_substitution' in Hxt; auto; cycle 1.
      { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros x' Hx't0.
        apply Hfℛg, (rwP codomm_Tm_setP). exists t0. split; auto. apply (rwP codommP). eauto. }
      rewrite in_bigcup in Hxt. apply (rwP hasP) in Hxt as [x' Hfx' Hxx'].
      apply (rwP pimfsetP) in Hfx' as [y Hyt0 Hfy].
      apply (rwP hasP). exists y.
      { apply (rwP codomm_Tm_setP). exists t0. split; auto. apply (rwP codommP). eauto. }
      rewrite Hfy //.
    - apply (rwP hasP) in Hfgx as [x' Hℛgx' Hfx].
      pose proof Hℛgx' as H'ℛgx'. apply Hfℛg, (rwP dommP) in H'ℛgx' as [t Hfx'].
      rewrite Hfx' /= in Hfx.
      apply (rwP codomm_Tm_setP) in Hℛgx' as (t' & Hx't' & Hg't').
      apply (rwP codommP) in Hg't' as [y Hg'y].
      apply (rwP codomm_Tm_setP). exists (`⦇f⦈ Fresh0 t'). split.
      { rewrite FV_lift_substitution'; auto; cycle 1.
        { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros y' Hy't'.
          apply Hfℛg, (rwP codomm_Tm_setP). exists t'. split; auto. apply (rwP codommP). eauto. }
        rewrite /= in_bigcup. apply (rwP hasP). exists t; auto.
        apply (rwP pimfsetP). exists x'; auto. }
      apply (rwP codommP). exists y.
      rewrite mapmE Hg'y //.
  Qed.

  #[program] Lemma codomm_Tm_set_mapm_lift_substitution :
    forall f g,
      codomm_Tm_set g ⊆ domm f ->
      codomm_Tm_set (mapm ⦇f⦈ g) = ⋃_(x ∈ codomm_Tm_set g) (FV (odflt (variable _) (getm f x))).
  Proof.
    introv Hfℛg.
    apply codomm_Tm_set_mapm_lift_substitution'; auto. apply HFresh.
  Qed.

  (** Page 6: Proposition 6.3. *)
  Proposition monad_substitution'3 :
    forall Fresh f g t,
      Fresh_correct Fresh ->
      codomm_Tm_set g ⊆ domm f ->
      t ∈ Tm (domm g) ->
      (`⦇f⦈ Fresh ∘ `⦇g⦈ Fresh) t ≡_α `⦇`⦇f⦈ Fresh ∘ g⦈ Fresh t.
  Proof.
    introv HFresh Hfℛg Hgt.
    apply (rwP fsubsetP) in Hfℛg, Hgt.
    gen f g. induction t; intros.
    - set (z0 := Fresh0 (codomm_Tm_set g)).
      set (z1 := Fresh0 (codomm_Tm_set f)).
      set (X := FV (`⦇f[z0,variable z1]⦈ Fresh0 (`⦇g[s,variable z0]⦈ Fresh0 t))).
      assert (forall k v : 𝒱, getm (1__X) k = Some v -> getm (1__(X :\ z1 ∪ {z1})) k = Some v) as H.
      { introv Hkv.
        rewrite mkfmapfE in Hkv.
        rewrite mkfmapfE in_fsetU in_fsetD !in_fset1 orbC.
        destruct (k =P z1); subst; auto.
        destruct (z1 ∈ X) eqn:Hz1X; rewrite Hz1X in Hkv; inverts Hkv. auto. }
      transitivity (`⦇f⦈ Fresh0 (abstraction z0 (`⦇g[s,variable z0]⦈ Fresh0 t))).
      { rewrite /α_equivalent/= update_identity -/z0 -/z1 -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto.
        apply α_equivalent'_identity.
        rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hfgx. auto. }
      transitivity (abstraction z1 ((`⦇f[z0,variable z1]⦈ Fresh0 ∘ `⦇g[s,variable z0]⦈ Fresh0) t)).
      { rewrite /α_equivalent /= update_identity -/z0 -/z1 -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto.
        apply α_equivalent'_identity.
        rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hfgx. auto. }
      assert (`⦇f[z0,variable z1]⦈ Fresh0 (`⦇g[s,variable z0]⦈ Fresh0 t) ≡_α `⦇`⦇f[z0,variable z1]⦈ Fresh0 ∘ g[s,variable z0]⦈ Fresh0 t) as H'.
      { apply IHt; introv Hg'x;
        rewrite domm_set in_fsetU in_fset1.
        - destruct (x =P z0); subst; auto.
          apply (rwP codomm_Tm_setP) in Hg'x as (t' & Hxt' & Hg't').
          apply (rwP codommP) in Hg't' as [x' Hg't'].
          rewrite setmE in Hg't'.
          destruct (x' =P s); subst.
          { inverts Hg't'. rewrite in_fset1 in Hxt'. apply (rwP eqP) in Hxt'. subst. contradiction. }
          apply Hfℛg, (rwP codomm_Tm_setP). exists t'. split; auto.
          apply (rwP codommP). eauto.
        - destruct (x =P s); subst; auto.
          apply (introF eqP) in n.
          apply Hgt. rewrite /= in_fsetD in_fset1 n Hg'x //. }
      transitivity (abstraction z1 (`⦇`⦇f[z0,variable z1]⦈ Fresh0 ∘ g[s,variable z0]⦈ Fresh0 t)).
      { rewrite /α_equivalent /= update_identity -/z0 -/z1 -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto. }
      transitivity (abstraction z1 (`⦇(`⦇f⦈ Fresh0 ∘ g)[s,variable z1]⦈ Fresh0 t)).
      { apply FV_respects_α_equivalence in H'.
        rewrite /α_equivalent /= update_identity -/z0 -/z1 H' -/X.
        apply α_equivalent'_supermap with (R__sub := 1__X); auto.
        rewrite /X -H'.
        apply lift_substitution'_indistinguishable_substitutions; auto.
        - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hxt.
          rewrite in_fsetI domm_set !domm_map domm_set !in_fsetU in_fset1 Bool.andb_diag.
          destruct (x =P s); subst; auto.
          apply (introF eqP) in n.
          apply Hgt. rewrite /= in_fsetD in_fset1 n Hxt //.
        - introv Hxt.
          apply lift_update_substitution'_compose_substitution_update; auto; try apply HFresh.
          + apply (rwP fsubsetP). auto.
          + rewrite in_fsetU in_fset1 orbC.
            destruct (x =P s); subst; auto.
            apply (introF eqP) in n.
            apply Hgt. rewrite /= in_fsetD in_fset1 n Hxt //. }
      rewrite /α_equivalent /=.
      apply substitution'_preserves_α_congruence' with (R := 1__(FV t)); auto.
      { rewrite !domm_set !domm_map. apply (rwP is_subset_ofP). introv Hxy.
        split;
        rewrite /= !in_fsetU !in_fset1;
        rewrite /fmap_to_Prop mkfmapfE in Hxy;
        destruct (x ∈ FV t) eqn:Hxt; rewrite Hxt in Hxy; inverts Hxy;
        destruct (y =P s); subst; auto;
        apply (introF eqP) in n;
        apply Hgt; rewrite /= in_fsetD in_fset1 n Hxt //. }
      { apply partial_bijection_identity. }
      { apply partial_bijection_update, partial_bijection_identity. }
      { introv Hxx'.
        rewrite /fmap_to_Prop mkfmapfE in Hxx'.
        destruct (x ∈ FV t) eqn:Hxt; rewrite Hxt in Hxx'; inverts Hxx'.
        rewrite !setmE !mapmE.
        destruct (x' =P s); subst.
        { apply (rwP getmP). rewrite /= unionmE remmE rem_valmE setmE eq_refl //. }
        apply (introF eqP) in n.
        assert (x' ∈ FV t :\ s) as Hx'tns. { rewrite in_fsetD in_fset1 n Hxt //. }
        apply Hgt, (rwP dommP) in Hx'tns as [t' Hgx']. rewrite Hgx' /=.
        assert {subset FV t' <= codomm_Tm_set g} as Ht'ℛg.
        { introv Hxt'. apply (rwP codomm_Tm_setP). exists t'. split; auto. apply (rwP codommP). eauto. }
        assert {subset FV (`⦇f⦈ Fresh0 t') <= codomm_Tm_set (mapm (`⦇f⦈ Fresh0) g)} as Hf'ℛfg.
        { introv Hf'x.
          rewrite FV_lift_substitution' in Hf'x; auto; cycle 1.
          { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros y Hyt'. apply Hfℛg, Ht'ℛg, Hyt'. }
          rewrite in_bigcup in Hf'x. apply (rwP hasP) in Hf'x as [u Hf'u Hxu].
          apply (rwP pimfsetP) in Hf'u as [y Hyt' Hfy].
          rewrite /= codomm_Tm_set_mapm_lift_substitution'; auto; cycle 1.
          { apply (rwP fsubsetP). intros y' Hℛgy'. auto. }
          rewrite in_bigcup.
          apply (rwP hasP). exists y.
          { apply Ht'ℛg. auto. }
          rewrite /= Hfy //. }
        assert {subset FV (`⦇f⦈ Fresh0 t') <= codomm_Tm_set f} as Hfℛf.
        { introv Hf't'.
          rewrite FV_lift_substitution' in Hf't'; auto; cycle 1.
          { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros y Hyt'.
            apply Hfℛg, (rwP codomm_Tm_setP). exists t'. split; auto. apply (rwP codommP). eauto. }
          rewrite in_bigcup in Hf't'. apply (rwP hasP) in Hf't' as [y Hf'y' Hxy].
          apply (rwP pimfsetP) in Hf'y' as [y' Hy't' Hfy'].
          apply (rwP codomm_Tm_setP). exists y. split; auto. apply (rwP codommP). eauto. }
        assert (Fresh0 (codomm_Tm_set (mapm (`⦇f⦈ Fresh0) g)) ∉ FV (`⦇f⦈ Fresh0 t')) as Hℛfgnf'.
        { pose proof HFresh (codomm_Tm_set (mapm (`⦇f⦈ Fresh0) g)) as HnFreshℛfg.
          apply negbT, Bool.not_true_iff_false. introv HFreshℛfg.
          apply Hf'ℛfg in HFreshℛfg. rewrite HFreshℛfg // in HnFreshℛfg. }
        assert (z1 ∉ FV (`⦇f⦈ Fresh0 t')) as Hz1nf'.
        { subst z1.
          pose proof HFresh (codomm_Tm_set f) as HnFreshℛf.
          apply negbT, Bool.not_true_iff_false. introv HFreshℛf.
          apply Hfℛf in HFreshℛf. rewrite HFreshℛf // in HnFreshℛf. }
        apply α_equivalent_update'; auto.
        apply α_equivalent'_supermap with (R__sub := 1__(FV (`⦇f⦈ Fresh0 t'))); cycle 1.
        { apply α_equivalent_reflexive. }
        introv Hf'k.
        rewrite mkfmapfE in Hf'k.
        rewrite mkfmapfE in_fsetD in_fset1.
        destruct (k ∈ FV (`⦇f⦈ Fresh0 t')) eqn:H'f'k; rewrite H'f'k in Hf'k; inverts Hf'k.
        destruct (v =P z1); subst.
        { rewrite H'f'k // in Hz1nf'. }
        rewrite FV_lift_substitution'; auto; cycle 1.
        { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv H'xt.
          rewrite domm_set domm_map in_fsetU in_fset1.
          destruct (x =P s); subst; auto.
          apply (introF eqP) in n1.
          apply Hgt. rewrite in_fsetD in_fset1 n1 H'xt //. }
        rewrite in_bigcup /=.
        cut (has (fun i => v ∈ FV i)
                  (pimfset (getm ((mapm (`⦇f⦈ Fresh0) g)[s,variable z1])) (FV t)) : Prop).
        { introv Hfg'v. rewrite Hfg'v //. }
        apply (rwP hasP). exists (`⦇f⦈ Fresh0 t'); auto.
        rewrite <- (rwP (@pimfsetP _ _ (getm ((mapm (`⦇f⦈ Fresh0) g)[s,variable z1])) (FV t) (`⦇f⦈ Fresh0 t'))).
        exists x'; auto.
        rewrite setmE mapmE n Hgx' //. }
      apply α_equivalent'_identity.
      rewrite /Tm /in_mem /=. apply (rwP fsubsetP). introv Hxt. auto.
    - rewrite /α_equivalent /=. rewrite <- (rwP andP). split.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (`⦇f⦈ Fresh0 (`⦇g⦈ Fresh0 t1)))); cycle 1.
        { apply IHt1; auto. introv Hxt1. apply Hgt. rewrite in_fsetU Hxt1 //. }
        introv Hfg'k.
        rewrite mkfmapfE in Hfg'k.
        destruct (k ∈ FV (`⦇f⦈ Fresh0 (`⦇g⦈ Fresh0 t1))) eqn:H'fg'k; rewrite H'fg'k in Hfg'k; inverts Hfg'k.
        rewrite mkfmapfE in_fsetU H'fg'k //.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (`⦇f⦈ Fresh0 (`⦇g⦈ Fresh0 t2)))); cycle 1.
        { apply IHt2; auto. introv Hxt2. apply Hgt. rewrite in_fsetU Hxt2 orbT //. }
        introv Hfg'k.
        rewrite mkfmapfE in Hfg'k.
        destruct (k ∈ FV (`⦇f⦈ Fresh0 (`⦇g⦈ Fresh0 t2))) eqn:H'fg'k; rewrite H'fg'k in Hfg'k; inverts Hfg'k.
        rewrite mkfmapfE in_fsetU H'fg'k orbT //.
    - assert (s ∈ fset1 s) as Hss. { rewrite in_fset1 //. }
      apply Hgt, (rwP dommP) in Hss as [x Hgs]. rewrite /= mapmE Hgs. reflexivity.
  Qed.

  Proposition monad_substitution3 :
    forall f g t,
      codomm_Tm_set g ⊆ domm f ->
      t ∈ Tm (domm g) ->
      (⦇f⦈ ∘ ⦇g⦈) t ≡_α ⦇⦇f⦈ ∘ g⦈ t.
  Proof.
    introv Hfℛg Hgt.
    apply monad_substitution'3; auto. apply HFresh.
  Qed.

  Notation "t '`[' x '=' u ']' Fresh" :=
    (`⦇(1__(FV t))[x,u]⦈ Fresh t)
      (at level 10, x at next level, u at next level, format "t `[ x '=' u ] Fresh").

  Notation "t '[' x '=' u ']'" :=
    (t`[x=u]Fresh)
      (at level 10, x at next level, u at next level, format "t [ x '=' u ]").

  #[local] Notation "t '`[' x '⟵' u ']' Fresh" :=
    (t`[x=u]Fresh)
      (at level 10, x at next level, u at next level, format "t `[ x '⟵' u ] Fresh").

  #[local] Notation "t '[' x '⟵' u ']'" :=
    (t[x=u])
      (at level 10, x at next level, u at next level, format "t [ x '⟵' u ]").

  (** Page 5: "To show that substitution is well behaved, i.e. laws such as...." *)
  Lemma substitution'_law1 :
    forall Fresh t u x,
      Fresh_correct Fresh ->
      x ∉ FV t ->
      t`[x⟵u] Fresh ≡_α t.
  Proof.
    introv HFresh Hnxt.
    transitivity (`⦇η__(FV t)⦈ Fresh0 t).
    - apply lift_substitution'_indistinguishable_substitutions; auto.
      + rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros y Hyt.
        rewrite !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI in_fsetU !in_fset Hyt orbT //.
      + intros y Hyt.
        rewrite setmE mapmE.
        destruct (y =P x); subst.
        { rewrite Hyt // in Hnxt. }
        reflexivity.
    - apply monad_substitution'1; auto.
      rewrite /Tm /in_mem /= fsubsetxx //.
  Qed.

  Lemma substitution_law1 :
    forall t u x,
      x ∉ FV t ->
      t`[x⟵u] Fresh ≡_α t.
  Proof.
    introv Hnxt.
    apply substitution'_law1; auto. apply HFresh.
  Qed.

  Lemma codomm_update_substitution :
    forall f x t,
      codomm_Tm_set (f[x,t]) = codomm_Tm_set (remm f x) ∪ FV t.
  Proof.
    introv.
    apply eq_fset. intros k.
    rewrite in_fsetU.
    apply Bool.eq_iff_eq_true. split; introv Hf'k.
    - apply (rwP codomm_Tm_setP) in Hf'k as (t' & Hkt' & Hℛf't').
      apply (rwP codommP) in Hℛf't' as [k' Hf'k'].
      rewrite setmE in Hf'k'.
      destruct (k' =P x); subst.
      { inverts Hf'k'. rewrite Hkt' orbT //. }
      apply (rwP orP). left.
      apply (rwP codomm_Tm_setP). exists t'. split; auto.
      apply (rwP codommP). exists k'.
      apply (introF eqP) in n.
      rewrite remmE n Hf'k' //.
    - apply (rwP codomm_Tm_setP).
      apply (rwP orP) in Hf'k as [Hℛf'k|Hkt].
      + apply (rwP codomm_Tm_setP) in Hℛf'k as (t' & Hkt' & Hℛf't').
        apply (rwP codommP) in Hℛf't' as [k' Hℛf't'].
        rewrite remmE in Hℛf't'.
        destruct (k' =P x); subst.
        { inverts Hℛf't'. }
        exists t'. split; auto.
        apply (rwP codommP). exists k'.
        apply (introF eqP) in n.
        rewrite setmE n Hℛf't' //.
      + exists t. split; auto.
        apply (rwP codommP). exists x.
        rewrite setmE eq_refl //.
  Qed.

  Lemma domm_identity' :
    forall X,
      domm (1__X : {fmap 𝒱 → term}) = X.
  Proof.
    introv.
    rewrite domm_map domm_identity //.
  Qed.

  Lemma codomm_identity' :
    forall X,
      codomm (1__X : {fmap 𝒱 → term}) = variable @: X.
  Proof.
    introv.
    apply eq_fset. intros x.
    apply Bool.eq_iff_eq_true. split; introv HxX.
    - apply (rwP codommP) in HxX as [v HxX].
      rewrite mapmE mkfmapfE in HxX.
      apply (rwP imfsetP).
      destruct (v ∈ X) eqn:HvX; rewrite HvX in HxX; inverts HxX.
      eauto.
    - apply (rwP imfsetP) in HxX as [y HyX Hxy]. subst.
      apply (rwP codommP). exists y.
      rewrite mapmE mkfmapfE HyX //.
  Qed.

  Lemma FV_after_substitute' :
    forall Fresh t u x,
      Fresh_correct Fresh ->
      x ∈ FV t ->
      FV (t`[x⟵u]Fresh) = (FV t :\ x) ∪ FV u.
  Proof.
    introv HFresh Hxt.
    replace (FV t :\ x) with (codomm_Tm_set (remm (1__(FV t)) x)); cycle 1.
    { apply eq_fset. intros k.
      rewrite in_fsetD in_fset1.
      destruct (k =P x); subst.
      - apply negbTE, (rwP codomm_Tm_setPn). intros t' [Hxt' Htt'].
        apply (rwP codommP) in Htt' as [x' Hxx'].
        rewrite remmE mapmE mkfmapfE in Hxx'.
        destruct (x' =P x); subst.
        { inverts Hxx'. }
        destruct (x' ∈ FV t) eqn:Hx't; rewrite Hx't in Hxx'; inverts Hxx'.
        rewrite in_fset1 in Hxt'. apply (rwP eqP) in Hxt'. subst. auto.
      - destruct (k ∈ FV t) eqn:Hkt.
        + apply (rwP codomm_Tm_setP). exists (variable k). split.
          * rewrite in_fset1 eq_refl //.
          * apply (rwP codommP). exists k.
            apply (introF eqP) in n.
            rewrite remmE mapmE mkfmapfE n Hkt //.
        + apply negbTE, (rwP codomm_Tm_setPn). intros t' [Hkt' Htt'].
          apply (rwP codommP) in Htt' as [x' Hxx'].
          rewrite remmE mapmE mkfmapfE in Hxx'.
          destruct (x' =P x); subst.
          { inverts Hxx'. }
          destruct (x' ∈ FV t) eqn:Hx't; rewrite Hx't in Hxx'; inverts Hxx'.
          rewrite in_fset1 in Hkt'. apply (rwP eqP) in Hkt'. subst. rewrite Hx't // in Hkt. }
    rewrite FV_lift_substitution'; auto.
    - apply eq_fset. intros k.
      apply Bool.eq_iff_eq_true. split; introv Hk.
      + rewrite in_fsetU.
        rewrite in_bigcup in Hk. apply (rwP hasP) in Hk as [t' Htt' Hkt'].
        apply (rwP pimfsetP) in Htt' as [y Hyt Hty].
        rewrite setmE mapmE mkfmapfE in Hty.
        destruct (y =P x); subst.
        { inverts Hty. simpl in *. rewrite Hkt' orbT //. }
        rewrite Hyt in Hty. inverts Hty.
        rewrite in_fset1 in Hkt'. apply (rwP eqP) in Hkt'. subst.
        apply (rwP orP). left.
        apply (rwP codomm_Tm_setP). exists (variable y). split.
        * rewrite /= in_fset1 eq_refl //.
        * apply (rwP codommP). exists y.
          apply (introF eqP) in n.
          rewrite remmE mapmE mkfmapfE n Hyt //.
      + rewrite in_bigcup. apply (rwP hasP).
        rewrite in_fsetU in Hk. apply (rwP orP) in Hk as [Hkt|Hku].
        * apply (rwP codomm_Tm_setP) in Hkt as (t' & Hkt' & Htt').
          apply (rwP codommP) in Htt' as [y Hxy].
          rewrite remmE mapmE mkfmapfE in Hxy.
          destruct (y =P x); subst.
          { inverts Hxy. }
          destruct (y ∈ FV t) eqn:Hyt; rewrite Hyt in Hxy; inverts Hxy.
          rewrite in_fset1 in Hkt'. apply (rwP eqP) in Hkt'. subst.
          exists (variable y).
          -- apply (rwP pimfsetP). exists y; auto.
             apply (introF eqP) in n.
             rewrite setmE mapmE mkfmapfE n Hyt //.
          -- rewrite /= in_fset1 eq_refl //.
        * exists u; auto.
          apply (rwP pimfsetP). exists x; auto.
          rewrite setmE mapmE mkfmapfE eq_refl //.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros y Hyt.
      rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset Hyt orbT //.
  Qed.

  Lemma FV_after_substitute :
    forall t u x,
      x ∈ FV t ->
      FV (t[x⟵u]) = (FV t :\ x) ∪ FV u.
  Proof.
    introv Hxt.
    apply FV_after_substitute'; auto. apply HFresh.
  Qed.

  Lemma FV_noop_substitute' :
    forall Fresh t u x,
      Fresh_correct Fresh ->
      x ∉ FV t ->
      FV (t`[x⟵u]Fresh) = FV t.
  Proof.
    introv HFresh Hnxt.
    apply FV_respects_α_equivalence.
    symmetry. apply substitution'_law1; auto.
  Qed.

  Lemma FV_noop_substitute :
    forall t u x,
      x ∉ FV t ->
      FV (t[x⟵u]) = FV t.
  Proof.
    introv Hnxt.
    apply FV_noop_substitute'; auto. apply HFresh.
  Qed.

  Lemma domm_update_identity :
    forall t u x,
      domm ((1__(FV t))[x, u]) = FV t ∪ {x}.
  Proof.
    introv.
    rewrite domm_update_substitution domm_map domm_mkfmapf fsvalK //.
  Qed.

  Lemma codomm_Tm_set_update_identity :
    forall X u x,
      codomm_Tm_set ((1__X)[x, u]) = (X :\ x) ∪ FV u.
  Proof.
    introv.
    rewrite codomm_update_substitution. repeat f_equal.
    apply eq_fset. intros k.
    rewrite in_fsetD in_fset1.
    apply Bool.eq_iff_eq_true. split; introv Hxk.
    + apply (rwP codomm_Tm_setP) in Hxk as (y & Hky & Hxy).
      apply (rwP codommP) in Hxy as [v Hxy].
      rewrite remmE mapmE mkfmapfE in Hxy.
      destruct (v =P x); subst.
      { inverts Hxy. }
      destruct (v ∈ X) eqn:HvX; rewrite HvX in Hxy; inverts Hxy.
      rewrite in_fset1 in Hky. apply (rwP eqP) in Hky. subst.
      apply (introF eqP) in n.
      rewrite n HvX //.
    + apply (rwP andP) in Hxk as [Hknx HkX].
      apply (rwP codomm_Tm_setP). exists (variable k). split.
      * rewrite /= in_fset1 eq_refl //.
      * apply (rwP codommP). exists k.
        apply negbTE in Hknx.
        rewrite remmE mapmE mkfmapfE Hknx HkX //.
  Qed.

  (** Page 5: "To show that substitution is well behaved, i.e. laws such as...." *)
  Lemma substitution_law2 :
    forall t u (v : term) x y,
      x <> y ->
      x ∉ FV v -> (* See Exercise 2.2 in http://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/geuvers.pdf. *)
      t[x⟵u][y⟵v] ≡_α t[y⟵v][x⟵u[y⟵v]].
  Proof.
    introv Hxny Hxnv.
    symmetry.
    transitivity (⦇⦇(1__(FV(⦇(1__(FV t))[y,v]⦈ t)))[x,⦇(1__(FV u))[y,v]⦈ u]⦈ ∘ (1__(FV t))[y,v]⦈ t).
    { destruct (y ∈ FV t) eqn:Hyt. (* TODO Can we remove the [destruct]s of this form? *)
      - apply monad_substitution3; try rewrite /Tm /in_mem /=; apply (rwP fsubsetP); intros k Hkt;
        rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset.
        + rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1.
          destruct (k =P x); subst; auto.
          apply (rwP codomm_Tm_setP) in Hkt as (t' & Hkt' & Htt').
          apply (rwP codommP) in Htt' as [k' Htk'].
          rewrite setmE mapmE mkfmapfE in Htk'.
          destruct (k' =P y); subst.
          { inverts Htk'. rewrite Hkt' orbT //. }
          apply (introF eqP) in n0.
          destruct (k' ∈ FV t) eqn:Hk't; rewrite Hk't in Htk'; inverts Htk'.
          rewrite in_fset1 in Hkt'. apply (rwP eqP) in Hkt'. subst.
          rewrite n0 Hk't //.
        + rewrite Hkt orbT //.
      - transitivity (⦇(1__(FV(⦇(1__(FV t))[y,v]⦈ t)))[x,⦇(1__(FV u))[y,v]⦈ u]⦈ t).
        { apply lift_substitution_respectsα_equivalence.
          - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
            rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset Hkt orbT //.
          - apply substitution_law1. rewrite Hyt //. }
        apply lift_substitution_indistinguishable_substitutions.
        + rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
          rewrite !domm_set !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset !in_fset1 Hkt orbT andbT.
          destruct (k =P x); subst; auto.
          rewrite FV_noop_substitute //. rewrite Hyt //.
        + intros k Hkt.
          rewrite !setmE !mapmE !setmE !mapmE !mkfmapfE Hkt.
          destruct (k =P x); subst.
          { apply (introF eqP) in Hxny. rewrite /lift_substitution /= Hxny /= setmE mapmE eq_refl. reflexivity. }
          apply (introF eqP) in n.
          rewrite FV_noop_substitute; cycle 1.
          { rewrite Hyt //. }
          rewrite Hkt /=.
          destruct (k =P y); subst.
          { rewrite /= Hkt // in Hyt. }
          rewrite /lift_substitution /= setmE mapmE mkfmapfE n Hkt. reflexivity. }
    symmetry.
    transitivity (⦇⦇(1__(FV (⦇(1__(FV t))[x,u]⦈ t)))[y,v]⦈ ∘ (1__(FV t))[x,u]⦈ t).
    { destruct (x ∈ FV t) eqn:Hxt.
      - apply monad_substitution3; try rewrite /Tm /in_mem /=; apply (rwP fsubsetP); intros y' Hy't; rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset1 in_fset.
        + rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1.
          destruct (y' =P y); subst; auto.
          apply (rwP codomm_Tm_setP) in Hy't as (t' & Hy't' & Htt').
          apply (rwP codommP) in Htt' as [k Hkt].
          rewrite setmE mapmE mkfmapfE in Hkt.
          destruct (k =P x); subst.
          { inverts Hkt. rewrite Hy't' !orbT //. }
          apply (introF eqP) in n0.
          destruct (k ∈ FV t) eqn:H'kt; rewrite H'kt in Hkt; inverts Hkt.
          rewrite in_fset1 in Hy't'. apply (rwP eqP) in Hy't'. subst.
          rewrite n0 H'kt //.
        + rewrite Hy't orbT //.
      - transitivity (⦇(1__(FV (⦇(1__(FV t))[x,u]⦈ t)))[y,v]⦈ t).
        { apply lift_substitution_respectsα_equivalence; cycle 1.
          { apply substitution_law1. rewrite Hxt //. }
          rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
          rewrite domm_set domm_map domm_mkfmapf in_fsetU in_fset in_fset1 Hkt orbT //. }
        apply lift_substitution_indistinguishable_substitutions.
        + rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
          rewrite !domm_set !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset !in_fset1 Hkt orbT andbT FV_noop_substitute; cycle 1.
          { rewrite Hxt //. }
          destruct (k =P y); subst; auto.
        + intros k Hkt.
          rewrite !mapmE !setmE !mapmE !mkfmapfE Hkt.
          destruct (k =P y); subst.
          { apply not_eq_sym, (introF eqP) in Hxny. rewrite /lift_substitution Hxny /= setmE eq_refl. reflexivity. }
          apply (introF eqP) in n.
          destruct (k =P x); subst.
          { rewrite /= Hkt // in Hxt. }
          rewrite /lift_substitution /= setmE mapmE mkfmapfE n FV_noop_substitute; cycle 1.
          { rewrite Hxt //. }
          rewrite Hkt. reflexivity. }
    apply lift_substitution_indistinguishable_substitutions.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
      rewrite !domm_map !domm_set !domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset !in_fset1 Hkt !orbT //.
    - intros k Hkt.
      rewrite !mapmE !setmE !mapmE !mkfmapfE Hkt.
      destruct (k =P x); subst.
      + apply (introF eqP) in Hxny. rewrite /lift_substitution Hxny /= setmE mapmE mkfmapfE eq_refl /=.
        apply lift_substitution_indistinguishable_substitutions.
        * rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k H'kt.
          rewrite domm_set domm_map domm_set domm_map !domm_mkfmapf in_fsetI !in_fsetU !in_fset1 !in_fset H'kt orbT andbT.
          destruct (k =P y); subst; auto.
          rewrite /= FV_after_substitute // in_fsetU in_fsetD !in_fset1 H'kt !orbT //.
        * intros k Hku.
          rewrite !setmE !mapmE !mkfmapfE Hku.
          destruct (k =P y); subst.
          { reflexivity. }
          rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1 Hku orbT. reflexivity.
      + destruct (k =P y); subst.
        * rewrite /lift_substitution /= setmE mapmE eq_refl FV_after_substitute //.
          transitivity (⦇1__(FV v)⦈ v).
          { symmetry. apply monad_substitution1.
            rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k H'kt. auto. }
          apply lift_substitution_indistinguishable_substitutions.
          -- rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k H'kt.
             rewrite domm_set !domm_map !domm_mkfmapf in_fsetI in_fsetU in_fset in_fset in_fsetU in_fsetD !in_fset1 H'kt !orbT //.
          -- intros k Hkv.
             rewrite setmE !mapmE !mkfmapfE in_fsetU in_fsetD in_fset1 Hkv orbT.
             destruct (k =P x); subst.
             { rewrite Hkv // in Hxnv. }
             reflexivity.
        * apply (introF eqP) in n, n0.
          rewrite /lift_substitution /= !setmE !mapmE !mkfmapfE n n0.
          destruct (x ∈ FV t) eqn:Hxt.
          -- rewrite FV_after_substitute // in_fsetU in_fsetD in_fset1 Hkt andbT n /=.
             destruct (y ∈ FV t) eqn:Hyt.
             ++ rewrite FV_after_substitute // in_fsetU in_fsetD in_fset1 Hkt n0. reflexivity.
             ++ rewrite FV_noop_substitute; cycle 1.
                { rewrite Hyt //. }
                rewrite Hkt. reflexivity.
          -- rewrite FV_noop_substitute; cycle 1.
             { rewrite Hxt //. }
             rewrite Hkt.
             destruct (y ∈ FV t) eqn:Hyt.
             ++ rewrite FV_after_substitute // in_fsetU in_fsetD in_fset1 Hkt andbT n0. reflexivity.
             ++ rewrite FV_noop_substitute; cycle 1.
                { rewrite Hyt //. }
                rewrite Hkt. reflexivity.
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
    introv.
    gen n. induction dBt; simpl; intros; rewrite /in_mem /=.
    - destruct (IHdBt n.+1); repeat constructor.
      + rewrite addn1 //.
      + introv HndBt. apply n0. inverts HndBt as HndBt. rewrite addn1 // in HndBt.
    - destruct (IHdBt1 n); repeat constructor.
      + destruct (IHdBt2 n); repeat constructor; auto.
        introv HndBt1t2. apply n0. inverts HndBt1t2. auto.
      + introv HndBt1t2. inverts HndBt1t2. auto.
    - rewrite /nat_to_pred.
      gen n0. induction n; intros;
      destruct n0; repeat constructor; intros_all;
      try solve [inverts H; inverts H2].
      replace (n.+1 < n0.+1) with (n < n0) by auto.
      (pose proof (IHn n0) as Hn0); inverts Hn0; repeat constructor; auto.
      introv HSn0Sn1. inverts HSn0Sn1 as HSn0Sn1.
      rewrite /in_mem /= /nat_to_pred in HSn0Sn1.
      replace (n.+1 < n0.+1) with (n < n0) in HSn0Sn1 by auto.
      rewrite HSn0Sn1 // in H.
  Qed.

  Lemma de_Bruijn_Tm_subset :
    forall n n' dBt,
      n <= n' ->
      dBt ∈ Tm^db n ->
      dBt ∈ Tm^db n'.
  Proof.
    rewrite /in_mem /=.
    introv Hnn' HndBt.
    gen n n'. induction dBt; intros; simpl in *.
    - apply IHdBt with (n.+1); auto.
    - apply (rwP andP) in HndBt as [HndBt1 HndBt2].
      eapply IHdBt1 with (n' := n') in HndBt1; auto. eapply IHdBt2 with (n' := n') in HndBt2; auto.
      rewrite /in_mem /= HndBt1 HndBt2 //.
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
    introv Hnℛϕ. rewrite /codomm_𝐍 -maxE. apply maximum_correct. auto.
  Qed.

  Lemma domm_update_ϕ :
    forall ϕ x,
      domm (ϕ^+x) = domm ϕ ∪ {x}.
  Proof.
    introv.
    rewrite domm_set domm_map fsetUC //.
  Qed.

  Lemma codomm_𝐍_update_ϕ :
    forall ϕ x,
      codomm_𝐍 (ϕ^+x) <= S (codomm_𝐍 ϕ).
  Proof.
    unfold codomm_𝐍.
    introv.
    rewrite codomm_setmE remm_mapm codomm_mapm big_idem_fsetU1 /=; try apply maxnn.
    rewrite max0n big_idem_imfset /=; try apply maxnn.
    pose proof codomm_rem ϕ x as Hxℛϕ. apply (rwP fsubsetP), bigmax_subset in Hxℛϕ.
    change (\max_(i <- codomm (remm ϕ x)) i.+1 <= (\max_(i <- codomm ϕ) i).+1).
    apply leq_trans with ((\max_(i <- codomm (remm ϕ x)) i).+1); auto.
    apply S_bigmax.
  Qed.

  Lemma codomm_update_ϕ :
    forall ϕ x,
      {subset codomm (ϕ^+x) <= S (codomm_𝐍 ϕ)}.
  Proof.
    intros ? ? v Hvℛϕ'.
    apply (rwP codommP) in Hvℛϕ' as [k Hkϕ'].
    rewrite setmE mapmE in Hkϕ'.
    destruct (k =P x); subst.
    { inverts Hkϕ'. auto. }
    destruct (getm ϕ k) eqn:Hϕk; inverts Hkϕ'.
    apply ϕ_type. apply (rwP codommP). eauto.
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
    introv Hyϕ'.
    rewrite setmE mapmE.
    rewrite /= in_fsetU in_fset1 in Hyϕ'. apply (rwP orP) in Hyϕ' as [Hyϕ|Hyx].
    - destruct (y =P x); auto.
    - rewrite Hyx //.
  Qed.

  (** Page 8: "Note that ϕ^+x is an injection, if ϕ is." *)
  Lemma injective_update_ϕ :
    forall ϕ x,
      is_injective ϕ ->
      is_injective (ϕ^+x).
  Proof.
    introv Hϕinj.
    apply (rwP injectivemP) in Hϕinj.
    apply (rwP (@injectivemP _ _ (ϕ^+x))). intros k Hϕ'k k' Hkk'.
    apply (rwP dommP) in Hϕ'k as [v Hϕ'k].
    rewrite setmE mapmE in Hϕ'k.
    rewrite !setmE !mapmE in Hkk'.
    destruct (k =P x); subst.
    - inverts Hϕ'k.
      destruct (k' =P x); subst; auto.
      destruct (getm ϕ k') eqn:Hϕk'; inverts Hkk'.
    - destruct (k' =P x); subst;
      destruct (getm ϕ k) eqn:Hϕk; inverts Hϕ'k as Hϕ'k.
      { inverts Hkk'. }
      + destruct (getm ϕ k') eqn:Hϕk'; inverts Hkk'.
        rewrite -Hϕk' in Hϕk. apply Hϕinj in Hϕk; auto.
        rewrite Hϕk' in Hϕk. apply (rwP dommP). eauto.
  Qed.

  #[local] Reserved Notation "t '^' ϕ" (at level 30, ϕ at level 30, format "t '^' ϕ").

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
    introv Hϕt.
    apply (rwP fsubsetP) in Hϕt.
    gen ϕ. induction t; intros; simpl in *.
    - apply de_Bruijn_Tm_subset with (codomm_𝐍 (ϕ^+s)).
      + apply codomm_𝐍_update_ϕ.
      + apply IHt. intros x Hxt.
        rewrite domm_set domm_map in_fsetU in_fset1.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply Hϕt. rewrite in_fsetD in_fset1 n Hxt //.
    - apply (rwP (@andP (Tm^db _ _) (Tm^db _ _))). split;
      (apply IHt1 || apply IHt2); intros x Hxt;
      apply Hϕt; rewrite in_fsetU Hxt ?orbT //.
    - assert (s ∈ fset1 s) as Hss. { rewrite in_fset1 eq_refl //. }
      apply Hϕt, (rwP dommP) in Hss as [v Hss]. rewrite Hss.
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
    simpl. intros ? ? ? ? ? HRtype Hϕinj Hψinj HRϕψ x' y'.
    rewrite /fmap_to_Prop unionmE remmE rem_valmE !setmE !mapmE /=.
    split.
    - introv HR'x'.
      destruct (x' =P x); subst.
      { inverts HR'x'. rewrite eq_refl.
        split; auto. apply (rwP dommP). rewrite setmE mapmE eq_refl. eauto. }
      destruct (getm R x') eqn:HRx'; cycle 1.
      { inverts HR'x'. }
      destruct (y =P s); subst; inverts HR'x'.
      pose proof HRx' as H'Rx'.
      rewrite <- (rwP is_subset_ofP) in HRtype. apply HRtype in HRx' as [Hϕx' Hψy'].
      apply (rwP dommP) in Hϕx' as [n__ϕ Hϕx'].
      apply (rwP dommP) in Hψy' as [n__ψ Hψy'].
      apply not_eq_sym, (introF eqP) in n0.
      apply HRϕψ in H'Rx' as [H'ϕx' Hϕψ]. rewrite Hϕx' Hψy' in Hϕψ. inverts Hϕψ.
      rewrite Hϕx' Hψy' n0.
      split; auto.
      apply (rwP dommP). apply (introF eqP) in n. rewrite setmE mapmE n Hϕx' /=. eauto.
    - intros [Hϕ'x' Hϕψ].
      destruct (x' =P x); subst.
      + destruct (y' =P y); subst; auto.
        destruct (getm ψ y') eqn:Hψy'; inverts Hϕψ.
      + destruct (getm R x') eqn:HRx'.
        * pose proof HRx' as H'Rx'.
          rewrite <- (rwP is_subset_ofP) in HRtype.
          apply HRtype in HRx' as [Hϕx' Hψs].
          apply (rwP dommP) in Hϕx' as [v__ϕ Hϕx'].
          apply (rwP dommP) in Hψs as [v__ψ Hψs].
          rewrite Hϕx' in Hϕψ.
          destruct (y' =P y); subst.
          { inverts Hϕψ. }
          destruct (getm ψ y') eqn:Hψy'; inverts Hϕψ.
          assert (R x' y') as HRx'. { apply HRϕψ. rewrite Hϕx' Hψy' //. split; auto. apply (rwP dommP). eauto. }
          rewrite HRx' in H'Rx'. inverts H'Rx'.
          destruct (y =P s); subst; auto.
          contradiction.
        * destruct (getm ϕ x') eqn:Hϕx';
          destruct (y' =P y); subst; inverts Hϕψ as Hϕψ.
          -- destruct (getm ψ y') eqn:Hψy'; inverts Hϕψ.
             rewrite -Hψy' in Hϕx'.
             assert (x' ∈ domm ϕ) as H'ϕx'. { apply (rwP dommP). rewrite Hϕx' Hψy'. eauto. }
             assert (x' ∈ domm ϕ /\ getm ϕ x' = getm ψ y') as H by auto.
             apply HRϕψ in H. rewrite H // in HRx'.
          -- destruct (getm ψ y') eqn:Hψy'; inverts Hϕψ.
             rewrite -Hψy' in Hϕx'.
             apply (rwP dommP) in Hϕ'x' as [v Hϕ'x'].
             apply (introF eqP) in n.
             rewrite setmE mapmE n Hϕx' Hψy' // in Hϕ'x'.
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
    introv HRtype Hϕinj Hψinj HRϕψ Hϕt Hψu.
    apply (rwP fsubsetP) in Hϕt, Hψu.
    gen R ϕ ψ u. induction t; intros; split; intros;
    destruct u; inverts H; simpl in *.
    - f_equal.
      eapply IHt; eauto.
      + apply injective_update_ϕ. auto.
      + intros x Hxt.
        rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply Hϕt. rewrite in_fsetD in_fset1 n Hxt //.
      + rewrite !domm_update_ϕ. eapply update_type; eauto.
      + apply injective_update_ϕ. auto.
      + apply lemma9'; eauto.
      + intros x Hxu.
        rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s0); subst; auto.
        apply (introF eqP) in n.
        apply Hψu. rewrite in_fsetD in_fset1 n Hxu //.
    - eapply IHt in H1; eauto.
      + apply injective_update_ϕ. auto.
      + intros x Hxt.
        rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply Hϕt. rewrite in_fsetD in_fset1 n Hxt //.
      + rewrite !domm_update_ϕ. eapply update_type; eauto.
      + apply injective_update_ϕ. auto.
      + apply lemma9'; eauto.
      + intros x Hxu.
        rewrite domm_update_ϕ in_fsetU in_fset1 orbC.
        destruct (x =P s0); subst; auto.
        apply (introF eqP) in n.
        apply Hψu. rewrite in_fsetD in_fset1 n Hxu //.
    - apply (rwP andP) in H1 as [Hα1 Hα2].
      eapply IHt1 with (ϕ := ϕ) (ψ := ψ) in Hα1; cycle 1; intros_all; eauto.
      { apply Hϕt. rewrite in_fsetU H0 //. }
      { apply Hψu. rewrite in_fsetU H0 //. }
      eapply IHt2 with (ϕ := ϕ) (ψ := ψ) in Hα2; cycle 1; intros_all; eauto.
      { apply Hϕt. rewrite in_fsetU H0 orbT //. }
      { apply Hψu. rewrite in_fsetU H0 orbT //. }
      rewrite Hα1 Hα2 //.
    - eapply IHt1 in H1; cycle 1; intros_all; eauto.
      { apply Hϕt. rewrite in_fsetU H0 //. }
      { apply Hψu. rewrite in_fsetU H0 //. }
      eapply IHt2 in H2; cycle 1; intros_all; eauto.
      { apply Hϕt. rewrite in_fsetU H0 orbT //. }
      { apply Hψu. rewrite in_fsetU H0 orbT //. }
      rewrite H1 H2 //.
    - apply (rwP getmP) in H1.
      apply HRϕψ in H1 as [Hϕs Hϕψ].
      apply (rwP dommP) in Hϕs as [v Hϕs].
      rewrite Hϕs in Hϕψ. rewrite Hϕs -Hϕψ //.
    - rewrite <- (rwP getmP).
      assert (s ∈ fset1 s) as Hss. { rewrite in_fset1 //. }
      apply Hϕt, (rwP dommP) in Hss as [v Hϕs].
      assert (s0 ∈ fset1 s0) as Hs0s0. { rewrite in_fset1 //. }
      apply Hψu, (rwP dommP) in Hs0s0 as [v' Hψs0].
      rewrite Hϕs Hψs0 /= in H1. subst.
      apply HRϕψ. split.
      + apply (rwP dommP). eauto.
      + rewrite Hϕs Hψs0 //.
  Qed.

  Lemma identity_is_pullback :
    forall ϕ,
      is_injective ϕ ->
      is_pullback (1__(domm ϕ)) ϕ ϕ.
  Proof.
    introv Hϕinj.
    repeat (split; intros).
    - rewrite /fmap_to_Prop mkfmapfE in H.
      destruct (x ∈ domm ϕ) eqn:Hϕx; rewrite Hϕx in H; inverts H. auto.
    - rewrite /fmap_to_Prop mkfmapfE in H.
      destruct (x ∈ domm ϕ) eqn:Hϕx; rewrite Hϕx in H; inverts H. auto.
    - destruct H as [Hϕx Hϕxy].
      rewrite /fmap_to_Prop mkfmapfE Hϕx.
      apply (rwP injectivemP) in Hϕxy; auto. subst. auto.
  Qed.

  (** Page 7: Proposition 8. *)
  Proposition to_de_Bruijn_chooses_canonical_representations :
    forall t u ϕ,
      is_injective ϕ ->
      t ∈ Tm (domm ϕ) ->
      u ∈ Tm (domm ϕ) ->
      t ≡_α u <-> t^ϕ = u^ϕ.
  Proof.
    introv Hϕinj Htϕ Huϕ.
    split; introv H.
    - apply lemma9 with (R := 1__(domm ϕ)); auto.
      + apply identity_type.
      + apply identity_is_pullback. auto.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV t)); auto. introv Hkv.
        rewrite mkfmapfE in Hkv.
        destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt in Hkv; inverts Hkv.
        apply (rwP fsubsetP) in Htϕ.
        apply Htϕ in Hkt.
        rewrite mkfmapfE Hkt //.
    - eapply lemma9 with (R := 1__(domm ϕ)) in H; auto.
      + apply α_equivalent'_implies_α_equivalent. eauto.
      + apply identity_type.
      + apply identity_is_pullback. auto.
  Qed.

  #[local] Reserved Notation "'↑_' c '^' d dBt"
    (at level 40, c at level 0, d at level 0, format "'↑_' c '^' d  dBt").

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

  #[local] Notation "'↑^' d dBt" :=
    (↑_0^d dBt)
      (at level 40, d at level 0, format "'↑^' d  dBt").

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
    introv HdBtn.
    gen n c d. induction dBt; intros; repeat rewrite /in_mem /=.
    - eapply IHdBt in HdBtn; eauto.
    - apply (rwP andP) in HdBtn as [HdBt1n HdBt2n].
      rewrite <- (rwP (@andP (Tm^db (n + d) (↑_c^d dBt1)) (Tm^db (n + d) (↑_c^d dBt2)))).
      split; eauto.
    - rewrite /nat_to_pred.
      destruct (n < c) eqn:?.
      + rewrite ltn_addr //.
      + rewrite ltn_add2r //.
  Qed.

  #[local] Reserved Notation "'[' j '↦' s ']' dBt"
    (at level 40, j at level 200, s at level 200, format "[ j '↦' s ] dBt").

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
      introv Hbx. subst.
      pose proof HFV_distinct as H'FV_distinct.
      rewrite /= !mem_seq2 eq_refl andbF // in H'FV_distinct.
    Qed.

    Let Hay : a <> y.
    Proof.
      introv Hay. subst.
      pose proof HFV_distinct as H'FV_distinct.
      rewrite /= mem_seq3 eq_refl !orbT // in H'FV_distinct.
    Qed.

    Let Hby : b <> y.
    Proof.
      introv Hby. subst.
      pose proof HFV_distinct as H'FV_distinct.
      rewrite /= mem_seq2 eq_refl orbT andbF // in H'FV_distinct.
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
      rewrite !addn1 Hbx Hby Hϕ_b /= !setmE !mapmE eq_refl /identity' /= /identity' /=.
      destruct (a =P Fresh
                     (codomm_Tm_set
                        (((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                               (variable a)]) [x,
                                                                                               (variable
                                                                                                  (Fresh
                                                                                                     (codomm_Tm_set
                                                                                                        ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                                                                                                              (variable a)]))))]))).
      { pose proof HFresh
             (codomm_Tm_set
                        (((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                               (variable a)]) [x,
                                                                                               (variable
                                                                                                  (Fresh
                                                                                                     (codomm_Tm_set
                                                                                                        ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b,
                                                                                                                                                              (variable a)]))))])) as HFresh.
        rewrite -e /= in HFresh. rewrite <- (rwP codomm_Tm_setPn) in HFresh.
        exfalso. apply (HFresh (variable a)).
        split.
        { rewrite in_fset1 eq_refl //. }
        apply (rwP codommP). exists b.
        rewrite !setmE mapmE eq_refl Hbx //. }
      rewrite setmE mapmE.
      destruct
        (a =P Fresh
              (codomm_Tm_set ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b, (variable a)]))).
      { pose proof HFresh
             (codomm_Tm_set ((mapm variable (identity (b |: fset1 b :\ y :\ x))) [b, (variable a)])) as HFresh.
        rewrite -e in HFresh.
        rewrite <- (rwP codomm_Tm_setPn) in HFresh.
        exfalso. apply (HFresh (variable a)).
        split.
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
      rewrite !addn1 Hbx Hay Hby Hϕ_a Hϕ_b eq_refl /= !setmE !mapmE Hay !setmE !mapmE /identity' /= /identity' /=.
      set (m := (mapm variable (identity (b |: fset1 b :\ y :\ x)))[b,application (variable a) (abstraction y (variable a))]).
      destruct (a =P Fresh (codomm_Tm_set (m[x,variable (Fresh (codomm_Tm_set m))]))).
      { pose proof HFresh (codomm_Tm_set (m[x,variable (Fresh (codomm_Tm_set m))])) as HFresh.
        rewrite -e /= in HFresh. rewrite <- (rwP codomm_Tm_setPn) in HFresh.
        exfalso. apply (HFresh (application (variable a) (abstraction y (variable a)))). split.
        { rewrite in_fsetU in_fset1 eq_refl //. }
        apply (rwP codommP). exists b.
        rewrite !setmE mapmE Hbx eq_refl //. }
      rewrite !setmE !mapmE.
      destruct (a =P Fresh (codomm_Tm_set m)).
      { pose proof HFresh (codomm_Tm_set m) as HFresh.
        rewrite -e in HFresh.
        rewrite <- (rwP codomm_Tm_setPn) in HFresh.
        exfalso. apply (HFresh (application (variable a) (abstraction y (variable a)))). split.
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
    introv HdBtn HdBun Hjn.
    gen j n dBu. induction dBt; intros; simpl in *.
    - apply IHdBt; auto.
      + rewrite addn1 //.
      + apply TAPL_6_2_3 with (c := 0) (d := 1) in HdBun.
        rewrite addn1 // in HdBun.
    - apply (rwP andP) in HdBtn as [HdBt1n HdBt2n].
      eapply IHdBt1 with (dBu := dBu) in HdBt1n; eauto.
      eapply IHdBt2 with (dBu := dBu) in HdBt2n; eauto.
      rewrite /in_mem /= HdBt1n HdBt2n //.
    - destruct (n =P j); subst; auto.
  Qed.

  Lemma codomm_Tm_set_identity :
    forall X,
      codomm_Tm_set (1__X) = X.
  Proof.
    introv.
    apply eq_fset. intros x.
    apply Bool.eq_iff_eq_true. split; simpl; introv H.
    - apply (rwP codomm_Tm_setP) in H as (t & Hxt & HtX).
      apply (rwP codommP) in HtX as [y HtX].
      rewrite mapmE mkfmapfE in HtX.
      destruct (y ∈ X) eqn:HyX; rewrite HyX in HtX; inverts HtX.
      rewrite in_fset1 in Hxt. apply (rwP eqP) in Hxt. subst. auto.
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
    introv Hnyt.
    replace ((1__(FV t :\ x))⦅y,x⦆) with (((1__(FV t :\ x))⦅x,y⦆)ᵒ); cycle 1.
    { rewrite update_converse.
      - rewrite converse_identity //.
      - apply partial_bijection_identity. }
    simpl.
    replace ((1__(FV t))[x,variable y]) with (mapm variable ((1__(FV t))⦅x,y⦆)); cycle 1.
    { apply eq_fmap. intros k.
      rewrite setmE !mapmE mkfmapfE unionmE remmE rem_valmE setmE /= mkfmapfE.
      destruct (k =P x); subst; auto.
      destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt //.
      destruct (y =P k); subst; auto.
      rewrite Hkt // in Hnyt. }
    replace ((1__(FV t :\ x))⦅x,y⦆ᵒ) with ((1__(FV t))⦅x,y⦆ᵒ); cycle 1.
    { apply eq_fmap. intros k.
      rewrite !update_converse.
      - rewrite !unionmE !remmE !rem_valmE !setmE /=.
        destruct (k =P y); subst; auto.
        rewrite !converse_identity !mkfmapfE !in_fsetD !in_fset1.
        destruct (k =P x); subst; auto.
        destruct (x ∈ FV t) eqn:Hxt; rewrite Hxt // eq_refl //.
      - apply partial_bijection_identity.
      - apply partial_bijection_identity. }
    apply lemma7.
    - apply partial_bijection_update, partial_bijection_identity.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
      apply (rwP dommP).
      rewrite unionmE remmE rem_valmE setmE /= mkfmapfE.
      destruct (k =P x); subst; simpl; eauto.
      rewrite Hkt.
      destruct (y =P k); subst; simpl; eauto.
      rewrite Hkt // in Hnyt.
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
    introv Hϕinj Hϕ't Hϕ'u Hα.
    apply (rwP fsubsetP) in Hϕ't, Hϕ'u.
    apply lemma9 with (R := (1__(domm ϕ))⦅y,x⦆); auto.
    - rewrite !domm_set ![_ |: _]fsetUC. apply update_type. apply (rwP is_subset_ofP).
      intros k v Hϕk.
      rewrite /fmap_to_Prop mkfmapfE in Hϕk.
      destruct (k ∈ domm ϕ) eqn:H'ϕk; rewrite H'ϕk in Hϕk; inverts Hϕk.
      rewrite domm_map H'ϕk //.
    - apply injective_update_ϕ. auto.
    - apply injective_update_ϕ. auto.
    - eapply lemma9'; eauto.
      + apply identity_type.
      + eapply identity_is_pullback; eauto.
    - rewrite /Tm /in_mem domm_set domm_map /= fsetUC. apply (rwP fsubsetP). intros k Hkt. apply Hϕ't. auto.
    - rewrite /Tm /in_mem domm_set domm_map /= fsetUC. apply (rwP fsubsetP). intros k Hkt. apply Hϕ'u. auto.
  Qed.

  Lemma to_de_Bruijn_with_indistinguishable_ϕ :
    forall ϕ ψ t,
      (forall x, x ∈ FV t -> getm ϕ x = getm ψ x) ->
      t^ϕ = t^ψ.
  Proof.
    introv Hϕψ.
    gen ϕ ψ. induction t; intros; simpl in *; f_equal.
    - apply IHt. intros x Hxt.
      rewrite !setmE !mapmE.
      destruct (x =P s); subst; auto.
      f_equal.
      apply Hϕψ.
      apply (introF eqP) in n.
      rewrite in_fsetD Hxt in_fset1 n //.
    - apply IHt1. intros x Hxt1.
      apply Hϕψ.
      rewrite in_fsetU Hxt1 //.
    - apply IHt2. intros x Hxt2.
      apply Hϕψ.
      rewrite in_fsetU Hxt2 orbT //.
    - f_equal. apply Hϕψ. rewrite in_fset1 eq_refl //.
  Qed.

  Lemma update_ϕ_remm :
    forall ϕ x,
      (remm ϕ x)^+x = ϕ^+x.
  Proof.
    introv.
    apply eq_fmap. intros k.
    rewrite !setmE !mapmE remmE.
    destruct (k =P x); subst; auto.
  Qed.

  Lemma substitution_id :
    forall t x,
      t[x⟵variable x] ≡_α t.
  Proof.
    introv.
    destruct (x ∈ FV t) eqn:Hxt; cycle 1.
    { apply substitution_law1. rewrite Hxt //. }
    transitivity (⦇η__(FV t)⦈ t); cycle 1.
    { apply monad_substitution1. rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt. auto. }
    apply lift_substitution_indistinguishable_substitutions.
    - rewrite /in_mem /Tm /=. apply (rwP fsubsetP). intros k Hkt.
      rewrite in_fsetI !domm_set domm_map !domm_mkfmapf !in_fsetU !in_fset1 !in_fset orbC Hkt //.
    - intros k Hkt.
      rewrite setmE mapmE mkfmapfE Hkt.
      destruct (k =P x); subst; reflexivity.
  Qed.

  Lemma injective_remm_ϕ :
    forall ϕ x,
      is_injective ϕ ->
      is_injective (remm ϕ x).
  Proof.
    simpl. introv Hϕinj.
    rewrite <- (rwP injectivemP). intros k Hϕ'k v Hkv.
    rewrite domm_rem in_fsetD in_fset1 in Hϕ'k. apply (rwP andP) in Hϕ'k as [Hknx Hϕk].
    apply negbTE in Hknx.
    rewrite !remmE Hknx in Hkv.
    destruct (v =P x); subst.
    - apply (rwP dommP) in Hϕk as [v Hϕk]. rewrite Hϕk // in Hkv.
    - apply (rwP injectivemP) in Hϕinj. apply Hϕinj in Hkv; auto.
  Qed.

  Lemma substitution_as_update_ϕ :
    forall ϕ t x y,
      is_injective ϕ ->
      t ∈ Tm (domm ϕ) ->
      y ∉ FV t ->
      (t[x⟵variable y])^ϕ^+y = t^ϕ^+x.
  Proof.
    unfold Tm.
    introv Hϕinj Hϕt Hnyt.
    apply (rwP fsubsetP) in Hϕt.
    destruct (x =P y); subst.
    { apply to_de_Bruijn_chooses_canonical_representations.
      - apply injective_update_ϕ. auto.
      - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
        rewrite FV_noop_substitute // in Hkt.
        apply Hϕt in Hkt.
        rewrite domm_set domm_map in_fsetU in_fset1 orbC Hkt //.
      - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
        apply Hϕt in Hkt.
        rewrite domm_set domm_map in_fsetU in_fset1 orbC Hkt //.
      - apply substitution_id. }
    eapply update_as_update_ϕ; eauto.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
      rewrite in_fsetU in_fset1 orbC.
      destruct (k =P y); subst; auto.
      apply Hϕt.
      destruct (x ∈ FV t) eqn:Hxt.
      + rewrite FV_after_substitute // in_fsetU in_fsetD !in_fset1 in Hkt.
        apply (rwP orP) in Hkt as [H|Hky].
        * apply (rwP andP) in H as [Hknx Hkt]. auto.
        * apply (rwP eqP) in Hky. subst. contradiction.
      + rewrite FV_noop_substitute // Hxt // in Hkt.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
      apply Hϕt in Hkt.
      rewrite in_fsetU in_fset1 Hkt //.
    - apply α_equivalent'_supermap with (R__sub := (1__(FV t :\ x))⦅y,x⦆).
      + introv Ht'k.
        rewrite unionmE remmE rem_valmE setmE mkfmapfE in_fsetD in_fset1 /= in Ht'k.
        rewrite unionmE remmE rem_valmE setmE mkfmapfE /=.
        destruct (k =P y); subst; auto.
        destruct (k =P x); subst.
        { inverts Ht'k. }
        destruct (k ∈ FV t) eqn:Hkt; cycle 1.
        { inverts Ht'k. }
        simpl in *.
        destruct (x =P k); subst; inverts Ht'k.
        apply Hϕt in Hkt.
        apply not_eq_sym, (introF eqP) in n1.
        rewrite Hkt n1 //.
      + apply variable_substitution_as_α_equivalent'. auto.
  Qed.

  Lemma de_Bruijn_substitution_identity :
    forall dBt i,
      [i↦i]dBt = dBt.
  Proof.
    introv.
    gen i. induction dBt; intros;
    simpl; f_equal; auto.
    destruct (n =P i); subst; auto.
  Qed.

  Lemma substitution_noop_if_shadow :
    forall t u x,
      (abstraction x t)[x⟵u] ≡_α abstraction x t.
  Proof.
    introv.
    apply substitution_law1.
    rewrite /= in_fsetD in_fset1 eq_refl //.
  Qed.

  Lemma old_index_after_update_ϕ :
    forall ϕ x i,
      is_injective ϕ ->
      getm ϕ x = Some i ->
      forall y, ~ getm (ϕ^+x) y = Some (S i).
  Proof.
    introv Hϕinj Hϕx Hϕ'y.
    rewrite setmE mapmE in Hϕ'y.
    destruct (y =P x); subst.
    { inverts Hϕ'y. }
    destruct (getm ϕ y) eqn:Hϕy; inverts Hϕ'y.
    rewrite -Hϕy in Hϕx.
    apply (rwP injectivemP) in Hϕinj.
    apply Hϕinj in Hϕx; auto.
    apply (rwP dommP). exists i.
    rewrite Hϕx Hϕy //.
  Qed.

  Lemma noop_de_Bruijn_substitution :
    forall ϕ i t dBu,
      t ∈ Tm (domm ϕ) ->
      i ∉ codomm ϕ ->
      let dBt := t^ϕ in
      [i↦dBu]dBt = dBt.
  Proof.
    intros ? ? ? ? Hϕt Hnℛϕi ?.
    subst dBt.
    apply (rwP fsubsetP) in Hϕt.
    rewrite <- (rwP (@codommPn _ _ ϕ i)) in Hnℛϕi.
    gen ϕ i dBu. induction t; intros;
    simpl; f_equal.
    - apply IHt.
      { intros k Hϕ'k. rewrite domm_set domm_mapi in_fsetU in_fset1.
        destruct (k =P s); subst; auto.
        apply Hϕt.
        apply (introF eqP) in n.
        rewrite in_fsetD in_fset1 n Hϕ'k //. }
      intros k'.
      rewrite setmE mapmE addn1.
      destruct (k' =P s); subst; auto.
      destruct (getm ϕ k') eqn:Hϕk'; auto.
      pose proof Hnℛϕi k' as Hnϕk'. rewrite Hϕk' // in Hnϕk'.
    - apply IHt1; auto. intros k Hkt1.
      apply Hϕt. rewrite in_fsetU Hkt1 //.
    - apply IHt2; auto. intros k Hkt2.
      apply Hϕt. rewrite in_fsetU Hkt2 orbT //.
    - destruct (getm ϕ s) eqn:Hϕs.
      + pose proof Hnℛϕi s as Hnϕs. rewrite Hϕs in Hnϕs.
        apply negbTE in Hnϕs.
        cbn in *. rewrite Hnϕs //.
      + destruct i; auto.
        apply (rwP dommPn) in Hϕs.
        pose proof Hϕt s ltac:(rewrite /= in_fset1 eq_refl //) as H'ϕs.
        rewrite H'ϕs // in Hϕs.
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
    introv Hϕt.
    apply (rwP fsubsetP) in Hϕt.
    apply eq_fset. intros x.
    gen x ϕ. induction t; intros; simpl in *.
    - assert (t ∈ Tm (domm (ϕ^+s))) as Hϕ't.
      { rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
        rewrite domm_set domm_mapi in_fsetU in_fset1.
        destruct (k =P s); subst; auto.
        apply Hϕt.
        apply (introF eqP) in n.
        rewrite in_fsetD in_fset1 n Hkt //. }
      apply (rwP fsubsetP) in Hϕ't.
      pose proof (fun i => @IHt i _ Hϕ't) as IH't.
      apply Bool.eq_iff_eq_true. split; intro H.
      + apply (rwP pimfsetP).
        apply (rwP imfsetP) in H as [y Ht'y Hxy].
        rewrite !in_fsetD !in_fset1 in Ht'y.
        apply (rwP andP) in Ht'y as [HynZ Hyt'].
        destruct y.
        { inverts HynZ. }
        clear HynZ.
        simpl in Hxy. subst.
        pose proof IH't (y.+1) as IH'ty. rewrite Hyt' in IH'ty.
        symmetry in IH'ty. apply (rwP pimfsetP) in IH'ty as [x Hxt Hϕ'x].
        rewrite setmE mapmE in Hϕ'x.
        destruct (x =P s); subst.
        { inverts Hϕ'x. }
        apply (introF eqP) in n.
        assert (x ∈ domm ϕ) as Hϕx.
        { apply Hϕt. rewrite in_fsetD in_fset1 n Hxt //. }
        apply (rwP dommP) in Hϕx as [v Hϕx].
        rewrite Hϕx in Hϕ'x. inverts Hϕ'x.
        exists x; auto.
        rewrite in_fsetD in_fset1 n Hxt //.
      + apply (rwP pimfsetP) in H as [y Hytns Hϕy].
        rewrite in_fsetD in_fset1 in Hytns. apply (rwP andP) in Hytns as [Hyns Hyt].
        apply (rwP imfsetP).
        exists (x.+1); auto.
        rewrite !in_fsetD !in_fset1 (IH't (x.+1)) /=.
        apply (rwP pimfsetP). exists y; auto.
        apply negbTE in Hyns.
        rewrite setmE mapmE Hϕy Hyns //.
    - rewrite in_fsetU.
      apply Bool.eq_iff_eq_true. split; introv H.
      + apply (rwP pimfsetP).
        apply (rwP orP) in H as [Hxt1|Hxt2].
        * rewrite IHt1 in Hxt1.
          -- apply (rwP pimfsetP) in Hxt1 as [k Hkt1 Hϕk].
             exists k; auto. rewrite in_fsetU Hkt1 //.
          -- intros k Hkt. apply Hϕt. rewrite in_fsetU Hkt //.
        * rewrite IHt2 in Hxt2.
          -- apply (rwP pimfsetP) in Hxt2 as [k Hkt2 Hϕk].
             exists k; auto. rewrite in_fsetU Hkt2 orbT //.
          -- intros k Hkt. apply Hϕt. rewrite in_fsetU Hkt orbT //.
      + apply (rwP orP).
        apply (rwP pimfsetP) in H as [k Hkt1t2 Hϕk].
        rewrite in_fsetU in Hkt1t2. apply (rwP orP) in Hkt1t2 as [Hkt1|Hkt2].
        * left. rewrite IHt1.
          -- apply (rwP pimfsetP). eauto.
          -- intros k' Hk't1. apply Hϕt. rewrite in_fsetU Hk't1 //.
        * right. rewrite IHt2.
          -- apply (rwP pimfsetP). eauto.
          -- intros k' Hk't2. apply Hϕt. rewrite in_fsetU Hk't2 orbT //.
    - rewrite in_fset1.
      apply Bool.eq_iff_eq_true. split; intros H.
      + apply (rwP eqP) in H. subst.
        assert (s ∈ domm ϕ) as Hϕs. { apply Hϕt. rewrite in_fset1 eq_refl //. }
        apply (rwP dommP) in Hϕs as [v Hϕs].
        apply (rwP (@pimfsetP _ _ _ (fset1 s) _)). exists s.
        * rewrite in_fset1 eq_refl //.
        * rewrite Hϕs //.
      + apply (rwP (@pimfsetP _ _ _ (fset1 s) _)) in H as [k Hks Hϕk].
        rewrite in_fset1 in Hks. apply (rwP eqP) in Hks. subst.
        rewrite Hϕk eq_refl //.
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
    intros ? ? ? ? ? Hϕinj Htϕ Hϕx Hnxt ?.
    subst dBt.
    apply (rwP fsubsetP) in Htϕ.
    gen ϕ x i dBu. induction t; intros;
    simpl in *.
    - f_equal.
      rewrite in_fsetD in_fset1 negb_and negbK in Hnxt.
      destruct (x =P s); subst.
      + pose proof old_index_after_update_ϕ _ Hϕinj Hϕx as Hnϕ'y.
        apply noop_de_Bruijn_substitution.
        * rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros x Hxt.
          rewrite domm_set domm_mapi in_fsetU in_fset1.
          destruct (x =P s); subst; auto.
          apply (introF eqP) in n.
          apply Htϕ. rewrite in_fsetD in_fset1 n Hxt //.
        * rewrite <- (rwP (@codommPn _ _ (ϕ^+s) _)). intros k.
          apply negbT, Bool.not_true_iff_false. intros Hnϕ'k.
          apply (rwP eqP) in Hnϕ'k.
          apply Hnϕ'y with k. rewrite -addn1 //.
      + pose proof old_index_after_update_ϕ _ Hϕinj Hϕx as Hnϕ'y.
        erewrite IHt; eauto.
        * apply injective_update_ϕ. auto.
        * intros k Hkt.
          rewrite domm_set domm_mapi in_fsetU in_fset1.
          destruct (k =P s); subst; auto.
          apply (introF eqP) in n0.
          apply Htϕ. rewrite in_fsetD in_fset1 n0 Hkt //.
        * apply (introF eqP) in n.
          rewrite setmE mapmE n Hϕx /= addn1 //.
    - rewrite in_fsetU negb_or in Hnxt. apply (rwP andP) in Hnxt as [Hnxt1 Hnxt2].
      erewrite IHt1; cycle 1; eauto.
      { intros k Hkt1. apply Htϕ. rewrite in_fsetU Hkt1 //. }
      erewrite IHt2; cycle 1; eauto.
      intros k Hkt2. apply Htϕ. rewrite in_fsetU Hkt2 orbT //.
    - assert (s ∈ domm ϕ) as Hϕs. { apply Htϕ. rewrite in_fset1 eq_refl //. }
      apply (rwP dommP) in Hϕs as [v Hϕs]. rewrite Hϕs /=.
      destruct (v =P i); subst; auto.
      rewrite -Hϕs in Hϕx.
      apply (rwP injectivemP) in Hϕinj. apply Hϕinj in Hϕx.
      + subst. rewrite in_fset1 eq_refl // in Hnxt.
      + apply (rwP dommP). rewrite Hϕx. eauto.
  Qed.

  Lemma update_substitution_reorder' :
    forall f x x' t t',
      x <> x' ->
      f[x,t][x',t'] = f[x',t'][x,t].
  Proof.
    introv Hxnx'.
    apply eq_fmap. intros k.
    rewrite !setmE.
    destruct (k =P x); subst; auto.
    apply (introF eqP) in Hxnx'. rewrite Hxnx' //.
  Qed.

  (** Page 8: "I leave it to the reader to show that -^ϕ preserves substitution, i.e. it maps substitutions to named terms as given here to substitution on de Bruijn terms."

      This is the only main result not yet formalized.
   *)
  Lemma TAPL_6_2_8 :
    forall ϕ t u x,
      (FV t ∪ FV u ∪ {x}) ⊆ domm ϕ ->
      is_injective ϕ ->
      (t[x⟵u])^ϕ = [odflt 0 (getm ϕ x)↦u^ϕ](t^ϕ).
  Proof.
  Admitted.

  Fixpoint term_depth t : nat :=
    S match t with
      | variable _ => 0
      | application t u => maxn (term_depth t) (term_depth u)
      | abstraction _ t => term_depth t
      end.

  Lemma term_depth_respects_α_equivalent' :
    forall R t u,
      t ≡_α^R u ->
      term_depth t = term_depth u.
  Proof.
    introv Hα.
    gen R u. induction t; intros; destruct u; inverts Hα; simpl; eauto.
    f_equal.
    apply (rwP andP) in H0 as [Hα1 Hα2].
    rewrite (IHt1 _ _ Hα1) (IHt2 _ _ Hα2) //.
  Qed.

  Lemma term_depth_respects_α_equivalent :
    forall t u,
      t ≡_α u ->
      term_depth t = term_depth u.
  Proof.
    introv Hα.
    eapply term_depth_respects_α_equivalent'; eauto.
  Qed.

  Add Parametric Morphism : term_depth
      with signature α_equivalent ==> eq as term_depth_morph.
  Proof.
    apply term_depth_respects_α_equivalent.
  Qed.

  Implicit Type bound : {fset 𝒱}.

  Fixpoint has_shadowing' bound t : bool :=
    match t with
    | abstraction x t => (x ∈ bound) || has_shadowing' (bound ∪ {x}) t
    | application t1 t2 => has_shadowing' bound t1 || has_shadowing' bound t2
    | variable x => false
    end.

  Definition has_shadowing : term -> bool := has_shadowing' ∅.

  Lemma has_shadowing'_sub :
    forall bound__sub bound__super t,
      bound__sub ⊆ bound__super ->
      has_shadowing' bound__sub t ->
      has_shadowing' bound__super t.
  Proof.
    introv Hsub Ht.
    gen bound__sub bound__super. induction t; intros; simpl in *.
    - apply (rwP orP). apply (rwP orP) in Ht as [Ht|Ht].
      + apply (rwP fsubsetP) in Hsub. apply Hsub in Ht. auto.
      + right. apply IHt with (bound__sub := bound__sub ∪ {s}); auto. rewrite fsetSU //.
    - apply (rwP orP). apply (rwP orP) in Ht as [Ht|Ht]; eauto.
    - apply (rwP fsubsetP) in Hsub. auto.
  Qed.

  Fixpoint bound_variables t : {fset 𝒱} :=
    match t with
    | abstraction x t => bound_variables t ∪ {x}
    | application t1 t2 => bound_variables t1 ∪ bound_variables t2
    | variable _ => ∅
    end.

  Lemma has_shadowing'_fsetU :
    forall bound bound' t,
      fdisjoint bound' (bound_variables t) ->
      has_shadowing' bound t = has_shadowing' (bound ∪ bound') t.
  Proof.
    unfold has_shadowing.
    introv Hdisj.
    gen bound. induction t; intros; auto; simpl in *.
    - rewrite in_fsetU.
      destruct (s ∈ bound) eqn:Hsbound; auto; simpl.
      assert (s ∈ bound' = false) as Hsnbound'.
      { apply negbTE, (rwP negP). introv Hsnbound'.
        rewrite <- (rwP fdisjointP) in Hdisj.
        apply Hdisj in Hsnbound'.
        rewrite in_fsetU in_fset1 eq_refl orbT // in Hsnbound'. }
      rewrite Hsnbound' /=.
      rewrite IHt.
      + f_equal. rewrite fsetUC fsetUA. f_equal. rewrite fsetUC //.
      + rewrite fdisjointUr in Hdisj. apply (rwP andP) in Hdisj as [Hdisj _]. auto.
    - rewrite fdisjointUr in Hdisj. apply (rwP andP) in Hdisj as [Hdisj1 Hdisj2].
      rewrite IHt1 // IHt2 //.
  Qed.

  Fixpoint have_same_structure t u : bool :=
    match t, u with
    | abstraction _ t, abstraction _ u =>
        have_same_structure t u
    | application t1 t2, application u1 u2 =>
        have_same_structure t1 u1 && have_same_structure t2 u2
    | variable _, variable _ => true
    | _, _ => false
    end.

  Lemma have_same_structure_reflexive :
    forall t,
      have_same_structure t t.
  Proof.
    intros.
    induction t; simpl; auto. rewrite IHt1 IHt2 //.
  Qed.

  Lemma have_same_structure_symmetric :
    forall t u,
      have_same_structure t u ->
      have_same_structure u t.
  Proof.
    introv Htu.
    gen u. induction t; intros; destruct u; inverts Htu; simpl in *; auto.
    apply (rwP andP) in H0 as [Htu1 Htu2].
    apply IHt1 in Htu1. apply IHt2 in Htu2.
    rewrite Htu1 Htu2 //.
  Qed.

  Lemma have_same_structure_transitive :
    forall t u (v : term),
      have_same_structure t u ->
      have_same_structure u v ->
      have_same_structure t v.
  Proof.
    introv Htu Huv.
    gen u v. induction t; intros; destruct u, v; inverts Htu; inverts Huv; simpl in *; eauto.
    apply (rwP andP) in H0 as [Htu1 Htu2], H1 as [Huv1 Huv2].
    apply IHt1 in Huv1; auto.
    apply IHt2 in Huv2; auto.
    rewrite Huv1 Huv2 //.
  Qed.

  #[global] Instance have_same_structure_Equivalence : Equivalence have_same_structure.
  Proof.
    split; intros t.
    - apply have_same_structure_reflexive.
    - apply have_same_structure_symmetric.
    - apply have_same_structure_transitive.
  Qed.

  Definition preserves_structure f : Prop :=
    forall t, t ∈ codomm f -> exists x, t = variable x.

  Lemma identity_preserves_structure :
    forall X,
      preserves_structure (1__X).
  Proof.
    intros X t Htf.
    rewrite codomm_identity' in Htf.
    apply (rwP imfsetP) in Htf as [u Hu]. eauto.
  Qed.

  Lemma preserves_structure_update_substitution :
    forall f x y,
      preserves_structure f ->
      preserves_structure (f[x,variable y]).
  Proof.
    introv Hf Htf.
    apply (rwP codommP) in Htf as [k Hk].
    rewrite setmE in Hk.
    destruct (k =P x); subst.
    - inverts Hk. eauto.
    - apply Hf, (rwP codommP). eauto.
  Qed.

  Lemma preserves_structure_correct' :
    forall f g t u,
      FV t ⊆ domm f ->
      FV u ⊆ domm g ->
      preserves_structure f ->
      preserves_structure g ->
      have_same_structure t u ->
      have_same_structure (⦇f⦈ t) (⦇g⦈ u).
  Proof.
    introv Htf Hug Hf Hg Htu.
    gen f g u. induction t; intros; destruct u; inverts Htu; simpl in *.
    - apply (rwP fsubsetP) in Htf, Hug.
      apply IHt; auto.
      + apply (rwP fsubsetP).
        intros x Hxt.
        rewrite domm_set in_fsetU in_fset1.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply Htf.
        rewrite in_fsetD in_fset1 n Hxt //.
      + apply preserves_structure_update_substitution. auto.
      + apply preserves_structure_update_substitution. auto.
      + apply (rwP fsubsetP).
        intros x Hxu.
        rewrite domm_set in_fsetU in_fset1.
        destruct (x =P s0); subst; auto.
        apply (introF eqP) in n.
        apply Hug.
        rewrite in_fsetD in_fset1 n Hxu //.
    - apply (rwP andP) in H0 as [Htu1 Htu2].
      rewrite !fsubUset in Htf, Hug.
      apply (rwP andP) in Htf as [Ht1f Ht2f], Hug as [Hu1g Hu2g].
      rewrite -(rwP andP). fold (lift_substitution f) (lift_substitution g). auto.
    - rewrite !fsub1set in Htf, Hug.
      apply (rwP dommP) in Htf as [t Ht], Hug as [u Hu].
      rewrite /lift_substitution /= Ht Hu /=.
      assert (t ∈ codomm f) as Htf. { apply (rwP codommP). eauto. }
      apply Hf in Htf as [x Hx].
      assert (u ∈ codomm g) as Hug. { apply (rwP codommP). eauto. }
      apply Hg in Hug as [y Hy].
      subst. auto.
  Qed.

  Lemma α_equivalent'_implies_same_structure :
    forall R t u,
      t ≡_α^R u ->
      have_same_structure t u.
  Proof.
    introv Hα.
    gen R u. induction t; intros; destruct u; inverts Hα; simpl in *; eauto.
    apply (rwP andP) in H0 as [Htu1 Htu2].
    rewrite -(rwP andP). split; eauto.
  Qed.

  Lemma α_equivalent_implies_same_structure :
    forall t u,
      t ≡_α u ->
      have_same_structure t u.
  Proof.
    introv Hα.
    eapply α_equivalent'_implies_same_structure; eauto.
  Qed.

  Lemma preserves_structure_correct :
    forall f t,
      FV t ⊆ domm f ->
      preserves_structure f ->
      have_same_structure t (⦇f⦈ t).
  Proof.
    introv Htf Hf.
    transitivity (⦇1__(FV t)⦈ t).
    - apply α_equivalent_implies_same_structure. symmetry. apply monad_substitution1.
      rewrite /Tm /in_mem /= fsubsetxx //.
    - apply preserves_structure_correct'; auto.
      + apply (rwP fsubsetP). intros x Hxt. rewrite domm_identity' //.
      + apply identity_preserves_structure.
      + reflexivity.
  Qed.

  Lemma term_depth_lift_variable_substitution :
    forall f t,
      preserves_structure f ->
      term_depth (⦇f⦈ t) = term_depth t.
  Proof.
    introv Hf.
    gen f. induction t; intros; simpl in *; auto.
    - f_equal.
      apply IHt. intros u Hf'.
      apply (rwP codommP) in Hf' as [x Hx].
      rewrite setmE in Hx.
      destruct (x =P s); subst.
      + inverts Hx. eauto.
      + apply Hf, (rwP codommP). eauto.
    - fold (lift_substitution f). auto.
    - rewrite /lift_substitution /=.
      destruct (getm f s) eqn:Hfs; fold (lift_substitution f); auto.
      assert (t ∈ codomm f) as Hft. { apply (rwP codommP). eauto. }
      apply Hf in Hft as [x Ht]. subst. auto.
  Qed.

  Lemma has_shadowing'_overlap :
    forall bound t,
      ~ fdisjoint bound (bound_variables t) ->
      has_shadowing' bound t.
  Proof.
    introv Hdisj.
    apply (rwP negP) in Hdisj.
    gen bound. induction t; intros; simpl in *.
    - rewrite fdisjointUr fdisjoints1 negb_and negbK in Hdisj.
      apply (rwP orP) in Hdisj as [Hdisj|Hdisj].
      + apply IHt in Hdisj.
        erewrite has_shadowing'_sub; eauto.
        * rewrite orbT //.
        * rewrite fsubsetUl //.
      + rewrite Hdisj //.
    - rewrite fdisjointUr negb_and in Hdisj.
      apply (rwP orP) in Hdisj as [Hdisj|Hdisj].
      + apply IHt1 in Hdisj. rewrite Hdisj //.
      + apply IHt2 in Hdisj. rewrite Hdisj orbT //.
    - rewrite fdisjoints0 // in Hdisj.
  Qed.

  Lemma has_shadowing_only_with_extra_bound_variables :
    forall bound t,
      ~ has_shadowing t ->
      has_shadowing' bound t ->
      ~ fdisjoint bound (bound_variables t).
  Proof.
    unfold has_shadowing.
    introv Ht H Hdisj.
    rewrite -(rwP fdisjointP) in Hdisj.
    gen bound. induction t; intros; simpl in *; auto.
    - apply (rwP orP) in H as [H|H].
      { apply Hdisj in H. rewrite in_fsetU in_fset1 eq_refl orbT // in H. }
      destruct (s ∈ bound) eqn:Hs.
      { apply Hdisj in Hs. rewrite in_fsetU negb_or in_fset1 eq_refl andbF // in Hs. }
      rewrite fset0U in Ht.
      destruct (fdisjoint (fset1 s) (bound_variables t)) eqn:Hst.
      + apply has_shadowing'_fsetU with (bound := bound) in Hst.
        rewrite -Hst in H.
        assert (~ has_shadowing t) as Hnt.
        { introv Ht'. eapply has_shadowing'_sub in Ht'; eauto. rewrite fsub0set //. }
        eapply IHt in Hnt; eauto.
        introv Hx.
        apply Hdisj in Hx.
        rewrite in_fsetU in_fset1 negb_or in Hx.
        apply (rwP andP) in Hx as [Hxnt Hxns]. auto.
      + apply Ht, has_shadowing'_overlap. introv Hsnt. rewrite Hst // in Hsnt.
    - apply (rwP negP) in Ht.
      rewrite negb_or in Ht.
      apply (rwP andP) in Ht as [Ht1 Ht2].
      apply (rwP negP) in Ht1, Ht2.
      apply (rwP orP) in H as [H|H];
      (apply IHt1 with bound in Ht1 + apply IHt2 with bound in Ht2); auto;
      introv Hx;
      apply Hdisj in Hx; rewrite in_fsetU negb_or in Hx;
      apply (rwP andP) in Hx as [Hx1 Hx2]; auto.
  Qed.

  Lemma term_depth_ind :
    forall P : term -> Prop,
      (forall t, (forall u, term_depth u < term_depth t -> P u) -> P t) ->
      forall t, P t.
  Proof.
    introv H.
    assert (forall t u, term_depth u <= term_depth t -> P u) as IH.
    { introv H'.
      gen u. induction t; intros; simpl in *.
      - apply H; intros v Hv.
        apply IHt, leq_trans with (n := (term_depth u).-1);
        destruct (term_depth u) eqn:?; auto.
      - apply H; intros v Hv.
        rewrite -maxnSS leq_max in H'.
        apply (rwP orP) in H' as [H'|H'].
        + apply IHt1. apply leq_trans with (n := (term_depth u).-1);
          destruct (term_depth u) eqn:?; auto.
        + apply IHt2. apply leq_trans with (n := (term_depth u).-1);
          destruct (term_depth u) eqn:?; auto.
      - apply H. intros v Hv.
        destruct u.
        + repeat (destruct u; inverts H').
        + rewrite /= gtn_max in H'. apply (rwP andP) in H' as [Hu1 Hu2].
          rewrite /= ltnS leq_max in Hv.
          apply (rwP orP) in Hv as [Hv|Hv];
          destruct u1, u2; inverts Hu1; inverts Hu2.
        + destruct v; inverts Hv. }
    eauto.
  Qed.

  Lemma lift_substitution_cannot_decrease_term_depth :
    forall f t,
      t ∈ Tm (domm f) ->
      term_depth t <= term_depth (⦇f⦈ t).
  Proof.
    introv Htf.
    rewrite /Tm /in_mem /= in Htf. apply (rwP fsubsetP) in Htf.
    gen f. induction t; intros; simpl in *.
    - apply IHt. introv Hxt.
      rewrite domm_set in_fsetU in_fset1.
      destruct (x =P s); subst; auto.
      apply (introF eqP) in n.
      apply Htf.
      rewrite in_fsetD in_fset1 Hxt n //.
    - rewrite gtn_max !ltnS !leq_max.
      rewrite <- (rwP andP). split.
      + rewrite IHt1 //. introv Hx. apply Htf. rewrite in_fsetU Hx //.
      + rewrite IHt2 ?orbT //. introv Hx. apply Htf. rewrite in_fsetU Hx orbT //.
    - rewrite /lift_substitution /=.
      destruct (getm f s) eqn:Hfs; auto.
      destruct t; auto.
  Qed.

  Lemma variable_substitution'_as_α_equivalent'' :
    forall Fresh t x y,
      Fresh_correct Fresh ->
      y ∉ FV t ->
      t`[x⟵variable y]Fresh ≡_α^(1__(FV (t`[x⟵variable y]Fresh) :\ y))⦅y,x⦆ t.
  Proof.
    introv HFresh Hnyt.
    replace ((1__(FV (t`[x⟵variable y]Fresh0) :\ y))⦅y,x⦆) with (((1__(FV t))⦅x,y⦆)ᵒ); cycle 1.
    { rewrite update_converse.
      - rewrite converse_identity //.
        apply eq_fmap. intros k.
        rewrite !unionmE !remmE !rem_valmE !setmE !mkfmapfE /= !in_fsetD !in_fset1.
        destruct (x ∈ FV t) eqn:Hxt.
        + rewrite FV_after_substitute' // !in_fsetU !in_fsetD !in_fset1.
          destruct (k =P y); subst; auto.
          destruct (k =P x); subst.
          { rewrite Hxt eq_refl //. }
          destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt //.
        + rewrite FV_noop_substitute'; auto; cycle 1.
          { rewrite Hxt //. }
          destruct (k =P y); subst; auto.
      - apply partial_bijection_identity. }
    replace ((1__(FV t))[x,variable y]) with (mapm variable ((1__(FV t))⦅x,y⦆)); cycle 1.
    { apply eq_fmap. intros k.
      rewrite setmE !mapmE mkfmapfE unionmE remmE rem_valmE setmE /= mkfmapfE.
      destruct (k =P x); subst; auto.
      destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt //.
      destruct (y =P k); subst; auto.
      rewrite Hkt // in Hnyt. }
    apply lemma7'; auto.
    { apply partial_bijection_update, partial_bijection_identity. }
    rewrite /Tm /in_mem /mem /=. apply (rwP fsubsetP). intros k Hkt.
    apply (rwP dommP).
    rewrite unionmE remmE rem_valmE mkfmapfE setmE Hkt /=.
    destruct (k =P x); subst; simpl; eauto.
    destruct (y =P k); subst; simpl; eauto.
    rewrite Hkt // in Hnyt.
  Qed.

  Lemma variable_substitution_as_α_equivalent'' :
    forall t x y,
      y ∉ FV t ->
      t[x⟵variable y] ≡_α^(1__(FV (t[x⟵variable y]) :\ y))⦅y,x⦆ t.
  Proof.
    introv Hnyt.
    apply variable_substitution'_as_α_equivalent''; auto. apply HFresh.
  Qed.

  Lemma variable_substitution'_as_α_equivalent''' :
    forall Fresh t x y,
      Fresh_correct Fresh ->
      y ∉ FV t ->
      t`[x⟵variable y]Fresh ≡_α^(1__(FV (t`[x⟵variable y]Fresh)))⦅y,x⦆ t.
  Proof.
    introv HFresh Hnyt.
    apply α_equivalent'_supermap with (R__sub := (1__(FV (t`[x⟵variable y]Fresh0) :\ y))⦅y,x⦆); cycle 1.
    { apply variable_substitution'_as_α_equivalent''; auto. }
    introv Hkv.
    rewrite unionmE remmE rem_valmE setmE mkfmapfE /= in Hkv.
    rewrite unionmE remmE rem_valmE setmE mkfmapfE /=.
    destruct (k =P y); subst; auto.
    apply (introF eqP) in n.
    destruct (x ∈ FV t) eqn:Hxt.
    - rewrite FV_after_substitute' //.
      rewrite FV_after_substitute' // in Hkv.
      rewrite in_fsetD in_fsetU in_fsetD !in_fset1 n /= in Hkv.
      rewrite in_fsetU in_fsetD !in_fset1 orbC n /=.
      destruct (k =P x); subst; auto.
      destruct (k ∈ FV t) eqn:Hkt; auto.
    -  rewrite FV_noop_substitute' //; cycle 1. { rewrite Hxt //. }
      rewrite FV_noop_substitute' // in Hkv; cycle 1. { rewrite Hxt //. }
      rewrite in_fsetD in_fset1 n /= in Hkv.
      destruct (k ∈ FV t) eqn:Hkt; cycle 1.
      { inverts Hkv. }
      destruct (x =P k); subst.
      { inverts Hkv. }
      apply (introF eqP) in n0.
      rewrite Hkt n0 //.
  Qed.

  Lemma variable_substitution_as_α_equivalent''' :
    forall t x y,
      y ∉ FV t ->
      t`[x⟵variable y]Fresh ≡_α^(1__(FV (t`[x⟵variable y]Fresh)))⦅y,x⦆ t.
  Proof.
    introv Hnyt.
    apply variable_substitution'_as_α_equivalent'''; auto. apply HFresh.
  Qed.

  (* TODO Use throughout this file? *)
  (** See https://www.sciencedirect.com/science/article/pii/S1571066116300354. *)
  Definition α_compatible_predicate (P : term -> Prop) : Prop :=
    forall t u, t ≡_α u -> P t -> P u.

  (** See https://www.sciencedirect.com/science/article/pii/S1571066116300354. *)
  Theorem term_α_ind :
    forall P : term -> Prop,
      α_compatible_predicate P ->
      (forall x, P (variable x)) ->
      (forall t u, P t -> P u -> P (application t u)) ->
      (exists s : {fset 𝒱}, forall t x, x ∉ s -> P t -> P (abstraction x t)) ->
      forall t, P t.
  Proof.
    intros P HP Hvar Happ [s Habs] t.
    induction t using term_depth_ind; destruct t; auto.
    - pose proof HFresh (s ∪ FV t) as HFresh.
      rewrite in_fsetU negb_or in HFresh.
      apply (rwP andP) in HFresh as [HsFresh HtFresh].
      apply HP with (abstraction (Fresh (s ∪ FV t)) (t[s0⟵variable (Fresh (s ∪ FV t))])).
      + apply variable_substitution_as_α_equivalent''. auto.
      + apply Habs, H; auto.
        rewrite /= term_depth_lift_variable_substitution //.
        apply preserves_structure_update_substitution, identity_preserves_structure.
    - apply Happ; apply H; rewrite /= ltnS leq_max leqnn ?orbT //.
  Qed.

  #[local] Reserved Infix "=_α" (at level 40).

  Inductive trad_α : term -> term -> Prop :=
  | trad_α_var :
    forall x,
      variable x =_α variable x
  | trad_α_abs :
    forall x t u,
      t =_α u ->
      abstraction x t =_α abstraction x u
  | trad_α_app :
    forall t1 t2 u1 u2,
      t1 =_α u1 ->
      t2 =_α u2 ->
      application t1 t2 =_α application u1 u2
  | trad_α_renaming :
    forall v v' t,
      v' ∉ FV t ->
      abstraction v t =_α abstraction v' (t[v⟵variable v'])
  | trad_α_trans :
    forall t u (v : term),
      t =_α u -> u =_α v -> t =_α v

  where "x '=_α' y" := (trad_α x y).

  #[local] Hint Constructors trad_α : core.

  Lemma α_equivalent'_remove_noop_update' :
    forall R t u x y,
      x ∉ FV t ->
      y ∉ FV u ->
      t ≡_α^(R⦅x,y⦆) u ->
      t ≡_α^R u.
  Proof.
    introv HnRx HnR'y Hα.
    apply α_equivalent'_with_behaviorally_identical_maps with (R := R⦅x,y⦆); auto. intros x' y' HR'x' Hx't.
    rewrite /fmap_to_Prop unionmE remmE rem_valmE setmE /= in HR'x'.
    rewrite /fmap_to_Prop.
    destruct (x' =P x); subst.
    { rewrite Hx't // in HnRx. }
    destruct (getm R x') eqn:HRx'; auto.
    destruct (y =P s); subst; inverts HR'x'. auto.
  Qed.

  Lemma α_equivalent'_update_FV :
    forall R t u x y,
      partial_bijection R ->
      t ≡_α^(R⦅x,y⦆) u ->
      (x ∈ FV t) = (y ∈ FV u).
  Proof.
    introv HRinj Hα.
    apply α_equivalent'_implies_related_FV in Hα; cycle 1.
    { apply partial_bijection_update. auto. }
    rewrite {}Hα.
    destruct (x ∈ FV t) eqn:Hxt; symmetry.
    - apply (rwP pimfsetP). exists x; auto.
      rewrite unionmE remmE rem_valmE setmE eq_refl //.
    - apply negbTE, (introN pimfsetP). intros [k Hk].
      rewrite unionmE remmE rem_valmE setmE /= in H.
      destruct (k =P x); subst.
      { rewrite Hk // in Hxt. }
      destruct (getm R k) eqn:HRk.
      + destruct (y =P s); subst; inverts H. auto.
      + inverts H.
  Qed.

  Lemma α_equivalent'_remove_noop_update :
    forall R t u x y,
      partial_bijection R ->
      t ≡_α^(R⦅x,y⦆) u ->
      x ∉ FV t ->
      t ≡_α^R u.
  Proof.
    introv HRinj Hα HnRx.
    eapply α_equivalent'_remove_noop_update'; eauto.
    erewrite <- α_equivalent'_update_FV; eauto.
  Qed.

  Lemma α_equivalent_abstractions :
    forall x y t u,
      abstraction x t ≡_α abstraction y u ->
      t[x⟵variable y] ≡_α u.
  Proof.
    introv Hα.
    destruct (x =P y); subst; auto.
    { transitivity t.
      - rewrite substitution_id //.
      - rewrite /α_equivalent /= update_identity fsetU_after_fsetD in Hα.
        apply α_equivalent'_implies_α_equivalent. eauto. }
    apply not_eq_sym, (introF eqP) in n.
    assert (y ∉ FV t) as Hynt.
    { apply FV_respects_α_equivalence in Hα.
      cut (y ∉ FV t ∪ {x} = true).
      { intros H. rewrite in_fsetU in_fset1 negb_or in H.
        apply (rwP andP) in H as [Hynt Hynx]. auto. }
      simpl in Hα.
      rewrite -fsetU_after_fsetD -Hα in_fsetU in_fsetD !in_fset1 eq_refl n //. }
    destruct (x ∈ FV t) eqn:Hxt; cycle 1.
    - assert (y ∉ FV u) as Hynu.
      { rewrite /α_equivalent /= in Hα.
        apply α_equivalent'_implies_related_FV in Hα; cycle 1.
        { apply partial_bijection_update, partial_bijection_identity. }
        rewrite Hα.
        apply (introN pimfsetP). intros [z Hzt].
        rewrite unionmE remmE rem_valmE setmE mkfmapfE /= in_fsetD in_fset1 Hzt in H.
        destruct (z =P x); subst.
        { rewrite Hzt // in Hxt. }
        simpl in H.
        destruct (y =P z); subst; inverts H.
        rewrite Hzt // in Hynt. }
      transitivity t.
      { rewrite substitution_law1 // Hxt //. }
      rewrite /α_equivalent /= in Hα.
      apply α_equivalent'_remove_noop_update in Hα; auto; cycle 1.
      { apply partial_bijection_identity. }
      { rewrite Hxt //. }
      apply α_equivalent'_supermap with (R__sub := 1__(FV t :\ x)); auto. intros k v Hkv.
      rewrite mkfmapfE in_fsetD in_fset1 in Hkv.
      rewrite mkfmapfE.
      destruct (k =P x); subst; auto.
      rewrite Hxt in Hkv; inverts Hkv.
    - rewrite /α_equivalent /= in Hα.
      rewrite /α_equivalent FV_after_substitute //=.
      replace (1__(FV t :\ x ∪ {y}))
        with (((1__(FV t :\ x))⦅y,x⦆);;((1__(FV t :\ x))⦅x,y⦆)); cycle 1.
      { apply eq_fmap. intros k.
        rewrite mkfmapfpE domm_union domm_rem mkfmapfE in_fsetU domm_mkfmap mem_seq1 unionmE remmE rem_valmE mkfmapfE in_fsetU !in_fsetD !in_fset1 setmE /=.
        destruct (k =P y); subst.
        - rewrite /= orbT unionmE remmE rem_valmE setmE mkfmapfE in_fsetD in_fset1 eq_refl //.
        - destruct (k ∈ domm (rem_valm (1__(FV t :\ x)) x)) eqn:Hk'; rewrite Hk' /=.
          + destruct (k =P x); subst; auto.
            apply not_eq_sym, (introF eqP) in n0, n1.
            destruct (k ∈ FV t) eqn:Hkt; auto.
            rewrite /= n1 /= unionmE remmE rem_valmE setmE mkfmapfE in_fsetD in_fset1 /=.
            rewrite eq_sym in n1.
            rewrite n1 Hkt /= n0 //.
          + apply negbT, (rwP dommPn) in Hk'.
            rewrite rem_valmE mkfmapfE in_fsetD in_fset1 in Hk'.
            destruct (k =P x); subst; auto.
            apply not_eq_sym, (introF eqP) in n0, n1.
            destruct (k ∈ FV t) eqn:Hkt; auto.
            rewrite /= n1 // in Hk'. }
      apply α_equivalent'_compose with (u := t); auto.
      apply variable_substitution_as_α_equivalent'. auto.
  Qed.

  Lemma α_equivalent_applications :
    forall t1 t2 u1 u2,
      application t1 t2 ≡_α application u1 u2 ->
      t1 ≡_α u1 /\ t2 ≡_α u2.
  Proof.
    introv Hα.
    rewrite /α_equivalent /= in Hα.
    apply (rwP andP) in Hα as [Hα1 Hα2].
    split;
    eapply α_equivalent'_with_behaviorally_identical_maps; try apply Hα1; try apply Hα2;
    introv Hxy Hxt;
    rewrite /fmap_to_Prop mkfmapfE in_fsetU Hxt ?orbT in Hxy; inverts Hxy;
    rewrite /fmap_to_Prop mkfmapfE Hxt //.
  Qed.

  Lemma α_equivalent_variables :
    forall x y,
      variable x ≡_α variable y ->
      x = y.
  Proof.
    introv Hα.
    rewrite /α_equivalent /= in Hα.
    apply (rwP getmP) in Hα.
    rewrite mkfmapfE in_fset1 eq_refl in Hα.
    inverts Hα. auto.
  Qed.

  Theorem α_equivalent_correct :
    forall t u,
      t ≡_α u <-> t =_α u.
  Proof.
    introv.
    split; introv Hα.
    - gen u. induction t using term_depth_ind; intros; destruct t, u; inverts Hα; auto.
      + destruct (s =P s0); subst.
        { apply α_equivalent_abstractions in H1.
          constructor. apply H; auto.
          transitivity (t[s0⟵variable s0]); auto. symmetry. apply substitution_id. }
        apply not_eq_sym, (introF eqP) in n.
        assert (s0 ∉ FV t) as Hs0nt.
        { apply FV_respects_α_equivalence in H1. simpl in H1.
          cut (s0 ∉ FV t ∪ {s} = true).
          { intros Hgoal. rewrite in_fsetU in_fset1 negb_or in Hgoal.
            apply (rwP andP) in Hgoal as [Hs0nt Hs0ns]. auto. }
          rewrite -fsetU_after_fsetD -H1 in_fsetU in_fsetD !in_fset1 eq_refl n //. }
        apply α_equivalent_abstractions in H1.
        apply H in H1; cycle 1.
        { rewrite term_depth_lift_variable_substitution //.
          apply preserves_structure_update_substitution, identity_preserves_structure. }
        apply trad_α_trans with (abstraction s0 (t[s⟵variable s0])); auto.
      + apply α_equivalent_applications in H1 as [Ht Hu].
        constructor; apply H; auto;
        rewrite ltnS leq_max leqnn ?orbT //.
      + apply α_equivalent_variables in H1. subst. auto.
    - induction Hα; simpl.
      + reflexivity.
      + rewrite /α_equivalent /= update_identity fsetU_after_fsetD.
        apply α_equivalent'_supermap with (R__sub := 1__(FV t)); auto. introv Hkv.
        rewrite mkfmapfE in Hkv.
        rewrite mkfmapfE in_fsetU in_fset1.
        destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt // in Hkv.
      + rewrite /α_equivalent /=.
        rewrite <- (rwP andP).
        split;
        eapply α_equivalent'_supermap with (R__sub := 1__(FV _)); eauto; introv Hkv;
        rewrite mkfmapfE in Hkv;
        rewrite mkfmapfE in_fsetU;
        destruct (k ∈ FV t1) eqn:Hkt1, (k ∈ FV t2) eqn:Hkt2;
        rewrite ?Hkt1 ?Hkt2 // in Hkv.
      + destruct (v ∈ FV t) eqn:Hvt.
        * symmetry. rewrite /α_equivalent /=.
          rewrite FV_after_substitute // fsetD_after_fsetU.
          replace (FV t :\ v :\ v') with (FV t :\ v); cycle 1.
          { apply eq_fset. intros x.
            rewrite !in_fsetD !in_fset1.
            destruct (x =P v); subst.
            - rewrite andbF //.
            - destruct (x ∈ FV t) eqn:Hxt.
              + destruct (x =P v'); subst; auto.
                rewrite Hxt // in H.
              + destruct (x =P v'); subst; auto. }
          apply variable_substitution_as_α_equivalent'. auto.
        * transitivity (abstraction v' t);
          rewrite /α_equivalent /=.
          -- apply α_equivalent'_supermap with (R__sub := 1__(FV t)); cycle 1.
             { apply α_equivalent_reflexive. }
             intros k x Hkx.
             rewrite mkfmapfE in Hkx.
             rewrite unionmE remmE rem_valmE setmE mkfmapfE in_fsetD !in_fset1 /=.
             destruct (k =P v); subst.
             { rewrite Hvt // in Hkx. }
             destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt in Hkx; inverts Hkx.
             simpl.
             destruct (v' =P x); subst; auto.
             rewrite Hkt // in H.
          -- rewrite /α_equivalent /= update_identity fsetU_after_fsetD.
             apply α_equivalent'_supermap with (R__sub := 1__(FV t)); cycle 1.
             { apply α_equivalent_symmetric, substitution_law1. rewrite Hvt //. }
             intros k x Hkx.
             rewrite mkfmapfE in Hkx.
             rewrite mkfmapfE in_fsetU in_fset1.
             destruct (k ∈ FV t) eqn:Hkt; rewrite Hkt in Hkx; inverts Hkx.
             destruct (x =P v'); subst; auto.
      + transitivity u; auto.
  Qed.

  (* Defining a version with a non-Unicode name to make it easier to reference. *)
  Definition alpha_equivalent_correct :
    forall t u,
      t ≡_α u <-> t =_α u :=
    α_equivalent_correct.

  Lemma trad_α_reflexive :
    forall t, t =_α t.
  Proof.
    introv.
    apply α_equivalent_correct. reflexivity.
  Qed.

  Lemma trad_α_symmetric :
    forall t u,
      t =_α u ->
      u =_α t.
  Proof.
    intros t u Hα.
    apply α_equivalent_correct. symmetry. apply α_equivalent_correct. auto.
  Qed.

  Lemma FV_lift_substitution'_subset_codomm_Tm_set :
    forall Fresh f t,
      Fresh_correct Fresh ->
      FV t ⊆ domm f ->
      FV (`⦇f⦈ Fresh t) ⊆ codomm_Tm_set f.
  Proof.
    introv HFresh Htf.
    apply (rwP fsubsetP). introv Hxt.
    rewrite FV_lift_substitution' // in_bigcup in Hxt.
    apply (rwP hasP) in Hxt as [u Hu].
    apply (rwP pimfsetP) in Hu as [k Hk].
    apply (rwP codomm_Tm_setP).
    exists u. split; auto.
    apply (rwP codommP). eauto.
  Qed.

  Lemma FV_lift_substitution_subset_codomm_Tm_set :
    forall f t,
      FV t ⊆ domm f ->
      FV (⦇f⦈ t) ⊆ codomm_Tm_set f.
  Proof.
    introv Htf.
    apply FV_lift_substitution'_subset_codomm_Tm_set; auto. apply HFresh.
  Qed.

  Lemma lift_substitution'_disjoint_update_substitution :
    forall Fresh f x y t,
      Fresh_correct Fresh ->
      FV t ⊆ domm f ->
      getm f x = Some (variable x) ->
      x ∉ codomm_Tm_set (remm f x) ->
      y ∉ codomm_Tm_set f ->
      `⦇f[x,variable y]⦈ Fresh t ≡_α (`⦇f⦈ Fresh t)`[x⟵variable y]Fresh.
  Proof.
    introv HFresh Htf Hfx Hxnℛf Hynℛf.
    transitivity ((`⦇(1__(codomm_Tm_set f))[x,variable y]⦈ Fresh0 ∘ `⦇f⦈ Fresh0) t : term); cycle 1.
    { apply lift_substitution'_indistinguishable_substitutions; auto.
      { rewrite /Tm /in_mem /= !domm_update_substitution !domm_identity' fsubsetI !fsubsetU //.
        - rewrite fsubsetxx //.
        - rewrite FV_lift_substitution'_subset_codomm_Tm_set //. }
      intros z Hzft.
      rewrite /update_substitution !setmE !mapmE !mkfmapfE Hzft.
      destruct (z =P x); subst.
      { reflexivity. }
      pose proof @FV_lift_substitution'_subset_codomm_Tm_set Fresh0 f t HFresh Htf as Hft.
      apply (rwP fsubsetP) in Hft.
      apply Hft in Hzft. rewrite Hzft. reflexivity. }
    transitivity (`⦇`⦇(1__(codomm_Tm_set f))[x,variable y]⦈ Fresh0 ∘ f⦈ Fresh0 t : term); cycle 1.
     { symmetry. apply monad_substitution'3; auto.
      rewrite domm_update_substitution domm_identity' fsubsetU // fsubsetxx //. }
    apply lift_substitution'_indistinguishable_substitutions; auto.
    { rewrite /Tm /in_mem /= domm_map !domm_update_substitution fsubsetI fsubsetU Htf //. }
    intros z Hzt.
    rewrite /update_substitution mapmE setmE.
    destruct (z =P x); subst.
    { apply (rwP fsubsetP) in Htf. apply Htf, (rwP dommP) in Hzt as [u Hxu].
      rewrite Hxu in Hfx. inverts Hfx. rewrite Hxu /= setmE eq_refl. reflexivity. }
    destruct (getm f z) eqn:Hfz; cycle 1.
    { reflexivity. }
    transitivity (`⦇η__(FV t0)⦈ Fresh0 t0).
    { symmetry. apply monad_substitution'1; auto. rewrite /Tm /in_mem /= fsubsetxx //. }
    apply lift_substitution'_indistinguishable_substitutions; auto.
    - rewrite /Tm /in_mem /= domm_set !domm_map !domm_mkfmapf fsubsetI fsubsetU fsvalK.
      { rewrite fsubsetxx //. }
      apply (rwP orP). right.
      apply (rwP fsubsetP). intros k Hk.
      apply (rwP codomm_Tm_setP). exists t0. split; auto.
      apply (rwP codommP). eauto.
    - intros k Hk.
      rewrite setmE !mapmE !mkfmapfE Hk /=.
      destruct (k =P x); subst.
      { rewrite <- (rwP codomm_Tm_setPn) in Hxnℛf.
        exfalso. apply Hxnℛf with t0. split; auto.
        apply (rwP codommP). exists z.
        apply (introF eqP) in n.
        rewrite remmE n //. }
      assert (k ∈ codomm_Tm_set f) as Hkℛf.
      { apply (rwP codomm_Tm_setP). exists t0. split; auto. apply (rwP codommP). eauto. }
      rewrite Hkℛf /=. reflexivity.
  Qed.

  Lemma lift_substitution'_disjoint_update_substitution' :
    forall Fresh f x y t,
      Fresh_correct Fresh ->
      (FV t :\ x) ⊆ domm f ->
      x ∉ codomm_Tm_set f ->
      y ∉ codomm_Tm_set f ->
      x <> y ->
      `⦇f[x,variable y]⦈ Fresh t ≡_α (`⦇f[x,variable x]⦈ Fresh t)`[x⟵variable y]Fresh.
  Proof.
    introv HFresh Ht'f Hxnℛf Hynℛf Hxny.
    replace (f[x,variable y]) with (f[x,variable x][x,variable y]); cycle 1.
    { rewrite update_substitution_overwrite //. }
    apply lift_substitution'_disjoint_update_substitution; auto.
    - rewrite domm_update_substitution.
      apply (rwP fsubsetP). intros k Hkt.
      rewrite in_fsetU in_fset1 orbC.
      destruct (k =P x); subst; auto.
      apply (introF eqP) in n.
      apply (rwP fsubsetP) in Ht'f.
      apply Ht'f. rewrite in_fsetD in_fset1 n Hkt //.
    - rewrite setmE eq_refl //.
    - apply (rwP codomm_Tm_setPn). intros u [Hxu Hf'u].
      apply (rwP codommP) in Hf'u as [k Hf'k].
      rewrite remmE setmE in Hf'k.
      destruct (k =P x); subst.
      { inverts Hf'k. }
      rewrite <- (rwP codomm_Tm_setPn) in Hxnℛf.
      apply Hxnℛf with u. split; auto.
      apply (rwP codommP). eauto.
    - apply (rwP codomm_Tm_setPn). intros u [Hyu Hf'u].
      rewrite codomm_setmE in_fsetU in_fset1 in Hf'u.
      apply (rwP orP) in Hf'u as [Hu|Hf'u].
      + apply (rwP eqP) in Hu. subst.
        rewrite in_fset1 in Hyu. apply (rwP eqP) in Hyu. subst. auto.
      + apply (rwP codommP) in Hf'u as [k Hf'k].
        rewrite remmE in Hf'k.
        destruct (k =P x); subst.
        { inverts Hf'k. }
        rewrite <- (rwP codomm_Tm_setPn) in Hynℛf.
        apply Hynℛf with u. split; auto.
        apply (rwP codommP). eauto.
  Qed.

  Lemma lift_substitution_disjoint_update_substitution' :
    forall f x y t,
      (FV t :\ x) ⊆ domm f ->
      x ∉ codomm_Tm_set f ->
      y ∉ codomm_Tm_set f ->
      x <> y ->
      ⦇f[x,variable y]⦈ t ≡_α (⦇f[x,variable x]⦈ t)[x⟵variable y].
  Proof.
    introv Ht'f Hxnℛf Hynℛf Hxny.
    apply lift_substitution'_disjoint_update_substitution'; auto. apply HFresh.
  Qed.

  Lemma α_equivalent_abstractions_respects_α_equivalence :
    forall t u x,
      t ≡_α u ->
      abstraction x t ≡_α abstraction x u.
  Proof.
    introv Hα.
    apply α_equivalent_correct. constructor. apply α_equivalent_correct. auto.
  Qed.

  Lemma α_equivalent'_morphl :
    forall R t u u',
      t ≡_α u ->
      t ≡_α^R u' = u ≡_α^R u'.
  Proof.
    intros R.
    assert (forall t t' u, t ≡_α t' -> t ≡_α^R u -> t' ≡_α^R u) as H.
    { introv Hα' Hα.
      replace R with ((1__(domm R));;R); cycle 1.
      { apply compose_identity_left. }
      apply α_equivalent'_compose with (u := t); auto.
      apply α_equivalent'_supermap with (R__sub := 1__(FV t')).
      - introv Hkv.
        rewrite mkfmapfE in Hkv.
        rewrite mkfmapfE.
        destruct (k ∈ FV t') eqn:Hkt; rewrite Hkt in Hkv; inverts Hkv.
        apply α_equivalent'_bijection_includes_all_FV in Hα; auto.
        rewrite /Tm /in_mem /= in Hα. apply (rwP fsubsetP) in Hα.
        apply FV_respects_α_equivalence in Hα'. rewrite Hα' in Hkt.
        apply Hα in Hkt. rewrite Hkt //.
      - apply α_equivalent_symmetric. auto. }
    intros t t' Hα u.
    apply Bool.eq_iff_eq_true; split; introv Hα'; eapply H; eauto. symmetry. auto.
  Qed.

  Lemma α_equivalent'_morphr :
    forall R t u u',
      partial_bijection R ->
      u ≡_α u' ->
      t ≡_α^R u = t ≡_α^R u'.
  Proof.
    introv HRinj Hα'.
    apply Bool.eq_iff_eq_true. split; introv Hα;
    (apply α_equivalent_symmetric in Hα' + idtac);
    rewrite α_equivalent'_converse' //;
    erewrite α_equivalent'_morphl; eauto;
    apply α_equivalent'_converse; auto.
  Qed.

  Add Parametric Morphism R (HRinj : partial_bijection R) : (α_equivalent' R)
      with signature α_equivalent ==> α_equivalent ==> eq as α_equivalent'_morph.
  Proof.
    intros t u Hα t' u' Hα'.
    apply Bool.eq_iff_eq_true. split; introv Hαt'.
    - setoid_rewrite α_equivalent'_morphl with (u := t); auto; cycle 1.
      { symmetry. auto. }
      setoid_rewrite α_equivalent'_morphr with (t := t); eauto. symmetry. auto.
    - setoid_rewrite α_equivalent'_morphr with (t := t); eauto.
      setoid_rewrite α_equivalent'_morphl with (u := u); eauto.
  Qed.

  Lemma foo :
    forall Fresh R t u x y,
      Fresh_correct Fresh ->
      partial_bijection R ->
      getm R y = Some y ->
      y ∉ FV t ->
      t ≡_α^R⦅x,y⦆ u ->
      t`[x⟵variable y]Fresh ≡_α^R u.
  Proof.
    introv HFresh HRinj HRy Hynt Hα.
    destruct (x ∈ FV t) eqn:Hxt; cycle 1.
    { erewrite α_equivalent'_morphl with (u := t).
      - apply α_equivalent'_remove_noop_update with x y; auto.
        rewrite Hxt //.
      - apply substitution'_law1; auto. rewrite Hxt //. }
    apply α_equivalent'_supermap with (R__sub := (1__(FV (t`[x⟵variable y]Fresh0)))⦅y,x⦆;;R⦅x,y⦆).
    { introv Hkv.
      rewrite mkfmapfpE domm_union domm_set unionmE remmE rem_valmE setmE mkfmapfE !in_fsetU in_fset1 orbC domm0 in_fset0 orbF /= in Hkv.
      destruct (k =P y); subst.
      { rewrite /= unionmE remmE rem_valmE setmE eq_refl /= in Hkv. inverts Hkv. auto. }
      simpl in Hkv.
      destruct (k ∈ domm (remm (rem_valm (1__(FV (t`[x⟵variable y]Fresh0))) x) y)) eqn:Hk';
      rewrite Hk' // in Hkv.
      destruct (k ∈ FV (t`[x⟵variable y]Fresh0)) eqn:Hkt'; rewrite Hkt' // in Hkv.
      rewrite FV_after_substitute' // in Hkt'.
      destruct (x =P k); subst.
      { inverts Hkv. }
      apply not_eq_sym, (introF eqP) in n0.
      rewrite /= unionmE remmE rem_valmE setmE n0 in Hkv.
      destruct (getm R k) eqn:HRk; auto.
      destruct (y =P s); subst; auto.
      inverts Hkv. }
    apply α_equivalent'_compose with t; auto.
    apply variable_substitution'_as_α_equivalent'''; auto.
  Qed.

  Lemma lift_substitution'_abstractions_wedge :
    forall Fresh f t x y z,
      Fresh_correct Fresh ->
      FV t ⊆ (domm f ∪ {z}) ->
      x ∉ codomm_Tm_set f ->
      y ∉ codomm_Tm_set f ->
      abstraction x (`⦇f[z,variable x]⦈ Fresh t) ≡_α abstraction y (`⦇f[z,variable y]⦈ Fresh t).
  Proof.
    introv HFresh Htfz Hx Hy.
    destruct (x =P y); subst.
    { reflexivity. }
    rewrite /α_equivalent /=.
    apply (rwP fsubsetP) in Htfz.
    apply lift_substitution'_indistinguishable_substitutions'; auto.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
      rewrite in_fsetI !domm_update_substitution Bool.andb_diag Htfz //.
    - intros k Hkt.
      rewrite !setmE.
      pose proof Hkt as Hkt'.
      apply Htfz in Hkt.
      rewrite in_fsetU in_fset1 orbC in Hkt.
      destruct (k =P z); subst.
      { apply (rwP getmP).
        rewrite unionmE remmE rem_valmE setmE eq_refl //. }
      apply (introF eqP) in n0.
      apply (rwP dommP) in Hkt as [u Hfk].
      rewrite Hfk /=.
      assert (forall x, x ∉ codomm_Tm_set f -> x ∉ FV u) as Hnu.
      { intros x' Hx'.
        rewrite <- (rwP codomm_Tm_setPn) in Hx'.
        apply (rwP negP). introv Hx'u.
        apply Hx' with u. split; auto.
        apply (rwP codommP). eauto. }
      apply Hnu in Hx, Hy.
      apply α_equivalent_update'; auto.
      apply α_equivalent'_supermap with (R__sub := 1__(FV u)); cycle 1.
      { apply α_equivalent_reflexive. }
      intros k' v Hk'v.
      rewrite mkfmapfE in Hk'v.
      rewrite mkfmapfE in_fsetD in_fset1.
      destruct (k' ∈ FV u) eqn:Hk'u; rewrite Hk'u in Hk'v; inverts Hk'v.
      destruct (v =P x); subst.
      { rewrite Hk'u // in Hx. }
      destruct (v ∈ FV (`⦇f[z,variable x]⦈ Fresh0 t)) eqn:Hvf't; auto.
      rewrite FV_lift_substitution' // in Hvf't; cycle 1.
      { rewrite /Tm /in_mem /= domm_update_substitution. apply (rwP fsubsetP). auto. }
      rewrite in_bigcup in Hvf't.
      apply negbT in Hvf't. apply (rwP hasPn) in Hvf't.
      assert (u ∈ pimfset (getm (f[z,variable x])) (FV t)) as Hvnu.
      { apply (rwP pimfsetP). exists k; auto.
        rewrite setmE n0 //. }
      apply Hvf't in Hvnu. rewrite Hk'u // in Hvnu.
  Qed.

  Lemma lift_substitution'_independent_of_Fresh' :
    forall Fresh' f t,
      Fresh_correct Fresh' ->
      FV t ⊆ domm f ->
      `⦇f⦈ Fresh' t ≡_α ⦇f⦈ t.
  Proof.
    introv HFresh' Hft.
    gen t f. elim/term_depth_ind; intros; destruct t; simpl in *.
    - destruct (Fresh' (codomm_Tm_set f) =P Fresh (codomm_Tm_set f)).
      + rewrite e.
        apply α_equivalent_abstractions_respects_α_equivalence.
        apply H; auto.
        rewrite domm_update_substitution.
        rewrite <- (rwP fsubsetP). intros x Hx.
        rewrite in_fsetU in_fset1 orbC.
        destruct (x =P s); subst; auto.
        apply (introF eqP) in n.
        apply (rwP fsubsetP) in Hft.
        apply Hft. rewrite in_fsetD in_fset1 Hx n //.
      + assert (FV t ⊆ (domm f ∪ {s})) as Htfs.
        { apply (rwP fsubsetP) in Hft.
          rewrite <- (rwP fsubsetP). intros x Hxt.
          rewrite in_fsetU in_fset1 orbC.
          destruct (x =P s); subst; auto.
          apply (introF eqP) in n0.
          apply Hft. rewrite in_fsetD in_fset1 Hxt n0 //. }
        rewrite /lift_substitution /=.
        transitivity (abstraction (Fresh' (codomm_Tm_set f)) (⦇f[s,variable (Fresh' (codomm_Tm_set f))]⦈ t)).
        { apply α_equivalent_abstractions_respects_α_equivalence, H; auto.
          rewrite domm_update_substitution //. }
        apply lift_substitution'_abstractions_wedge; auto; apply HFresh.
    - rewrite /α_equivalent /=.
      rewrite <- (rwP andP). split.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (`⦇f⦈ Fresh' t1))).
        * introv Hkv.
          rewrite mkfmapfE in Hkv.
          rewrite mkfmapfE in_fsetU.
          destruct (k ∈ FV (`⦇f⦈ Fresh' t1)) eqn:Hkft; rewrite Hkft in Hkv; inverts Hkv. auto.
        * apply H.
          -- rewrite ltnS leq_max leqnn //.
          -- rewrite fsubUset in Hft. apply (rwP andP) in Hft as [Ht1f Ht2f]. auto.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (`⦇f⦈ Fresh' t2))).
        * introv Hkv.
          rewrite mkfmapfE in Hkv.
          rewrite mkfmapfE in_fsetU.
          destruct (k ∈ FV (`⦇f⦈ Fresh' t2)) eqn:Hkft; rewrite Hkft in Hkv; inverts Hkv. rewrite orbC //.
        * apply H.
          -- rewrite ltnS leq_max leqnn orbC //.
          -- rewrite fsubUset in Hft. apply (rwP andP) in Hft as [Ht1f Ht2f]. auto.
    - rewrite fsub1set in Hft.
      apply (rwP dommP) in Hft as [k Hk].
      rewrite /lift_substitution /= Hk. reflexivity.
  Qed.

  Lemma lift_substitution'_independent_of_Fresh :
    forall Fresh1 Fresh2 f t,
      Fresh_correct Fresh1 ->
      Fresh_correct Fresh2 ->
      FV t ⊆ domm f ->
      `⦇f⦈ Fresh1 t ≡_α `⦇f⦈ Fresh2 t.
  Proof.
    introv HFresh1 HFresh2 Hft.
    transitivity (⦇f⦈ t).
    { apply lift_substitution'_independent_of_Fresh'; auto. }
    symmetry. apply lift_substitution'_independent_of_Fresh'; auto.
  Qed.
End AlphaFacts.
