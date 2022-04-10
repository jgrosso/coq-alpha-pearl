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

  #[local] Notation "X '∪' '{' x '}'" :=
    (X :|: fset1 x)
      (at level 52, format "X  '∪'  '{' x '}'")
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

  Declare Scope term_scope.
  Bind Scope term_scope with term.
  Delimit Scope term_scope with term.
  #[local] Open Scope term_scope.

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

  Lemma updateE :
    forall R x y k,
      getm (R⦅x,y⦆) k =
        if k == x
        then Some y
        else match getm R k with
             | Some v' =>
                 if y == v' then None else Some v'
             | None => None
             end.
  Proof.
    introv.
    rewrite unionmE setmE remmE rem_valmE /=.
    destruct (k =P x); subst; auto.
    destruct (getm R k) eqn:HRk; auto.
    destruct (y =P s); subst; auto.
  Qed.

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
    rewrite !updateE in Hkv1, Hks.
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
    rewrite updateE in HR'k.
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
    rewrite /fmap_to_Prop updateE in HR'x'.
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

  Arguments α_equivalent'P {_ _ _}.

  (** Page 3: "We now define ≡α^R ⊆ Tm(X) × Tm(Y)." *)
  Lemma α_equivalent'_type :
    forall R X Y t u,
      R ⊆ X × Y ->
      t ≡_α^R u ->
      t ∈ Tm X /\ u ∈ Tm Y.
  Proof.
    rewrite /in_mem /= /Tm.
    introv HR Hα.
    rewrite /is_subset_of -!(rwP andP) in HR |- *. destruct HR as [HRX HRY].
    gen R X Y u. induction t; simpl; introv HRX HRY Hα;
    destruct u; inverts Hα.
    - apply IHt with (X := X ∪ {s}) (Y := Y ∪ {s0}) in H0 as [Httype Hutype].
      + rewrite fsetUC -fsubDset in Httype. rewrite fsetUC -fsubDset // in Hutype.
      + rewrite -(rwP fsubsetP). intros x H. rewrite in_fsetU in_fset1 orbC.
        apply (rwP dommP) in H as [y Hxy]. rewrite updateE in Hxy.
        destruct (x =P s); subst; auto.
        destruct (getm R x) eqn:HRx; cycle 1. { inverts Hxy. }
        apply (rwP fsubsetP) in HRX. apply HRX, (rwP dommP). eauto.
      + rewrite -(rwP fsubsetP). intros x H. rewrite in_fsetU in_fset1.
        apply (rwP codommP) in H as [y Hxy]. rewrite updateE in Hxy.
        destruct (y =P s); subst. { inverts Hxy. rewrite eq_refl orbC //. }
        destruct (getm R y) eqn:HRx; cycle 1. { inverts Hxy. }
        destruct (s0 =P s1); subst; inverts Hxy.
        apply (rwP orP). left.
        apply (rwP fsubsetP) in HRY. apply HRY, (rwP codommP). eauto.
    - apply (rwP andP) in H0 as [Ht1 Ht2].
      eapply IHt1 in Ht1 as [Ht1 Hu1]; eauto. eapply IHt2 in Ht2 as [Ht2 Hu2]; eauto.
      apply (rwP fsubsetP) in Ht1, Hu1, Ht2, Hu2.
      split; apply (rwP fsubsetP); introv H;
      rewrite in_fsetU in H; apply (rwP orP) in H as [Hxt1|Hxt2]; auto.
    - rewrite /in_mem /= /in_mem /= in H0. apply (rwP getmP) in H0.
      rewrite !fsub1set. split.
      + apply (rwP fsubsetP) in HRX. apply HRX, (rwP dommP). eauto.
      + apply (rwP fsubsetP) in HRY. apply HRY, (rwP codommP). eauto.
  Qed.

  (** TODO Formalize "Note that we cannot replace partial bijections by bijections..."? *)

  (** Page 3: "Given X, Y, Z ⊂fin 𝒱 we write 1X = ...." *)
  Definition identity : {fset 𝒱} -> {fmap 𝒱 → 𝒱} := mkfmapf id.

  Lemma identityE :
    forall X x,
      getm (identity X) x =
        if x ∈ X
        then Some x
        else None.
  Proof.
    introv.
    rewrite mkfmapfE.
    destruct (x ∈ X) eqn:HxX; rewrite HxX //.
  Qed.

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
    rewrite /identity' /= /fmap_to_Prop identityE in Hxy.
    destruct (x ∈ X) eqn:HxX; inverts Hxy. auto.
  Qed.

  (** Page 3: "1X... obviously is a partial bijection." *)
  Lemma partial_bijection_identity : forall X, partial_bijection (1__X : {fmap 𝒱 → 𝒱}).
  Proof.
    intros.
    rewrite /partial_bijection /fmap_IsInjective /injective /identity' /fmap_𝒱_Identity /identity.
    rewrite <- (rwP injectivemP). intros x Hx x' Hxx'.
    apply (rwP dommP) in Hx as [v Hx].
    rewrite !identityE in Hx, Hxx'.
    destruct (x ∈ X) eqn:HxX; inverts Hx.
    destruct (x' ∈ X) eqn:Hx'X; inverts Hxx'.
    auto.
  Qed.

  #[local] Hint Resolve partial_bijection_identity : core.

  (** Page 3: "Given R ⊆ X × Y and S ⊆ Y × Z we write Rᵒ...." *)
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

  (** Page 3: "Given R ⊆ X × Y and S ⊆ Y × Z we write... R; S...." *)
  Definition compose R S : {fmap 𝒱 → 𝒱} :=
    mkfmapfp
      (fun k =>
        match getm R k with
        | Some v => getm S v
        | None => None
        end)
      (domm R).

  #[local] Notation "R ';;' S" := (compose R S) (at level 40, format "R ';;' S").

  Lemma composeE :
    forall R S x,
      getm (R;;S) x =
        match getm R x with
        | Some x => getm S x
        | None => None
        end.
  Proof.
    introv.
    rewrite mkfmapfpE.
    destruct (x ∈ domm R) eqn:HRx; rewrite HRx //.
    apply negbT, (rwP dommPn) in HRx. rewrite HRx //.
  Qed.

  Lemma domm_compose :
    forall R S,
      domm (R;;S) ⊆ domm R.
  Proof.
    introv.
    apply (rwP fsubsetP). introv HRSx.
    apply (rwP dommP) in HRSx as [v HRSx].
    rewrite composeE in HRSx.
    destruct (x ∈ domm R) eqn:HRx.
    - apply (rwP dommP) in HRx as [v' HRx]. rewrite HRx // in HRSx.
    - apply negbT, (rwP dommPn) in HRx. rewrite HRx // in HRSx.
  Qed.

  Lemma codomm_compose :
    forall R S,
      codomm (R;;S) ⊆ codomm S.
  Proof.
    introv.
    apply (rwP fsubsetP). introv HxℛRS.
    apply (rwP codommP) in HxℛRS as [k HRSx].
    rewrite composeE in HRSx.
    destruct (getm R k) eqn:HRk.
    - apply (rwP codommP). eauto.
    - inverts HRSx.
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
    rewrite /fmap_to_Prop composeE in HRSx.
    destruct (getm R x) eqn:HRx; cycle 1.
    { inverts HRSx. }
    split.
    - eapply HRtype. eauto.
    - eapply HStype. eauto.
  Qed.

  (** Page 3: "The set of partial bijections is closed under both operations." *)
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
    rewrite composeE in HRSx, Hxx'.
    destruct (getm R x) eqn:HRx; cycle 1.
    { inverts HRSx. }
    rewrite HRSx composeE in Hxx'.
    destruct (getm R x') eqn:HRx'; cycle 1.
    { inverts Hxx'. }
    rewrite -HRSx in Hxx'.
    apply HSinj in Hxx'; cycle 1.
    { apply (rwP dommP). eauto. }
    subst.
    rewrite -HRx in HRx'. apply HRinj in HRx'; auto.
    rewrite HRx in HRx'.
    apply (rwP dommP). eauto.
  Qed.

  (** Page 3: Lemma 1.1. *)
  Lemma update_identity : forall X x, (1__X)⦅x,x⦆ = 1__(X ∪ {x}).
  Proof.
    introv.
    apply eq_fmap. intros k.
    rewrite updateE !identityE in_fsetU in_fset1 orbC.
    destruct (k =P x); subst; auto.
    destruct (k ∈ X) eqn:HkX; auto.
    apply not_eq_sym, (introF eqP) in n. rewrite n //.
  Qed.

  (** Page 3: Lemma 1.2. *)
  Lemma update_converse :
    forall R x y,
      partial_bijection R ->
      R⦅x,y⦆ᵒ = R ᵒ⦅y,x⦆.
  Proof.
    introv HRinj.
    apply eq_fmap. intros k.
    rewrite updateE /converse.
    destruct (k =P y); subst.
    - apply getm_inv. rewrite invmK.
      + rewrite updateE eq_refl //.
      + intros k HR'k k' Hkk'.
        epose proof @partial_bijection_update _ _ _ HRinj as H. apply (rwP injectivemP) in H. apply H; eauto.
    - destruct (invm R k) eqn:HR'k; rewrite ?HR'k.
      + apply getm_inv in HR'k.
        destruct (x =P s); subst.
        * apply invm_None.
          { apply partial_bijection_update. auto. }
          rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros.
          rewrite updateE.
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
          rewrite updateE.
          replace (s == x) with false; cycle 1.
          { symmetry. apply Bool.not_true_iff_false. introv Hsx. apply (rwP eqP) in Hsx. subst. auto. }
          destruct (getm R s) eqn:HRs; rewrite HR'k.
          -- destruct (y =P s0); subst; inverts HR'k; auto. contradiction.
          -- inverts HR'k.
      + apply invm_None in HR'k; auto.
        apply invm_None.
        { apply partial_bijection_update. auto. }
        rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros k'.
        rewrite updateE.
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
    forall R S x y z a b,
      (R⦅x,y⦆;;S⦅y,z⦆) a b ->
      ((R;;S)⦅x,z⦆) a b.
  Proof.
    introv HR'S'.
    cut ((a = x /\ z = b) \/ (x <> a /\ z <> b /\ (R;;S) a b)).
    { rewrite /fmap_to_Prop updateE.
      introv [[Haz Hzb]|(Hxa & Hzb & Hab)]; subst.
      - rewrite eq_refl //.
      - apply not_eq_sym in Hxa. apply (introF eqP) in Hxa, Hzb. rewrite Hxa Hab Hzb //. }
    cut (exists c, (a = x /\ y = c /\ z = b) \/ (x <> a /\ y <> c /\ z <> b /\ R a c /\ S c b)).
    { rewrite /fmap_to_Prop composeE.
      introv [c [(Haz & Hyc & Hzb)|(Hxz & Hyc & Hzb & Hac & Hcb)]]; subst; auto. rewrite Hac Hcb. auto. }
    { rewrite /fmap_to_Prop composeE updateE in HR'S'.
      destruct (a =P x); subst.
      { rewrite updateE eq_refl in HR'S'. inverts HR'S'. eauto. }
      destruct (getm R a) eqn:HRa; cycle 1.
      { inverts HR'S'. }
      destruct (y =P s); subst.
      { inverts HR'S'. }
      apply not_eq_sym in n0. apply (introF eqP) in n, n0. rewrite updateE n0 in HR'S'.
      destruct (getm S s) eqn:HSs; cycle 1.
      { inverts HR'S'. }
      destruct (z =P s0); subst; inverts HR'S'; eauto.
      apply (elimF eqP) in n, n0. exists s. right. repeat split; auto. }
  Qed.

  Lemma α_equivalent'_observably_equal :
    forall R S t u,
      (forall x y, x ∈ FV t -> R x y -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    introv HReqvS Htαu.
    gen R S u. induction t; introv HReqvS Htαu;
    destruct u; inverts Htαu.
    - apply IHt with (R := R⦅s,s0⦆); auto. introv Hxt HR'xy.
      rewrite /fmap_to_Prop updateE in HR'xy.
      rewrite /fmap_to_Prop updateE.
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
      rewrite /= in_fsetU HRxy ?orbT //.
    - apply (rwP getmP), HReqvS in H0.
      + apply (rwP getmP). rewrite H0 //.
      + rewrite /= in_fset1 eq_refl //.
  Qed.

  (** Page 4: "We now define ≡α = ≡α^1X." *)
  Definition α_equivalent t u := exists X, t ≡_α^(1__X) u.

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
      (apply IHt1 || apply IHt2); introv Hx;
      apply HtX; rewrite /= in_fsetU Hx ?orbT //.
    - assert (s ∈ fset1 s) as Hss. { rewrite in_fset1 eq_refl //. }
      apply HtX in Hss.
      apply (rwP getmP). rewrite identityE Hss //.
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
      apply α_equivalent'_observably_equal with (S := (R;;S)⦅s,s1⦆) in Htαu; cycle 1.
      { intros. eapply update_compose; eauto. }
      rewrite /= Htαu //.
    - apply (rwP andP) in Htαu as [Htαu1 Htαu2], Huαv as [Huαv1 Huαv2].
      apply IHt1 with (R := R) (S := S) (v := v1) in Htαu1; auto.
      apply IHt2 with (R := R) (S := S) (v := v2) in Htαu2; auto.
      rewrite /= Htαu1 Htαu2 //.
    - apply (rwP getmP) in Htαu, Huαv.
      apply (rwP getmP). rewrite /= composeE Htαu //.
  Qed.

  Lemma domm_identity : forall X, domm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    introv.
    apply eq_fset. intros x.
    destruct (x ∈ X) eqn:HxX.
    - apply (rwP dommP). exists x. rewrite identityE HxX //.
    - apply negbTE. apply (rwP dommPn). rewrite identityE HxX //.
  Qed.

  Lemma compose_identity_right : forall R, R;;(1__(codomm R)) = R.
  Proof.
    introv.
    apply eq_fmap. intros x.
    rewrite composeE.
    destruct (getm R x) eqn:HRx; auto.
    rewrite identityE.
    replace (s ∈ codomm R) with true; auto.
    symmetry. apply (rwP codommP). eauto.
  Qed.

  Lemma compose_identity_left : forall R, (1__(domm R));;R = R.
  Proof.
    introv.
    apply eq_fmap. intros x.
    rewrite composeE identityE.
    destruct (x ∈ domm R) eqn:HRx; auto.
    apply negbT, (rwP dommPn) in HRx. auto.
  Qed.

  Lemma codomm_identity : forall X, codomm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    introv.
    apply eq_fset. intros x.
    destruct (x ∈ X) eqn:HxX.
    - apply (rwP codommP). exists x. rewrite identityE HxX //.
    - apply negbTE. rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros y.
      apply (introN eqP). introv HXy.
      rewrite identityE in HXy.
      destruct (y ∈ X) eqn:HyX; inverts HXy.
      rewrite HyX // in HxX.
  Qed.

  Lemma compose_identity :
    forall X Y,
      (1__X);;(1__Y) = 1__(X ∩ Y).
  Proof.
    introv.
    apply eq_fmap. intros x.
    rewrite composeE !identityE in_fsetI.
    destruct (x ∈ X) eqn:HxX; auto.
    rewrite identityE //.
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
    rewrite identityE.
    destruct (x ∈ X) eqn:HxX.
    - apply getm_inv. rewrite invmK.
      + rewrite identityE HxX //.
      + apply (rwP injectivemP). apply partial_bijection_identity.
    - apply invm_None.
      + apply partial_bijection_identity.
      + rewrite <- (rwP (@codommPn _ 𝒱 _ _)). intros x'.
        apply (introN eqP). introv Hxx'.
        rewrite identityE in Hxx'.
        destruct (x' ∈ X) eqn:Hx'X; inverts Hxx'.
        rewrite Hx'X // in HxX.
  Qed.

  (** Page 4: "≡α is... reflexive." *)
  Corollary α_equivalent_reflexive : forall t, t ≡_α t.
  Proof.
    introv. exists (FV t). apply α_equivalent'_identity. rewrite /Tm /in_mem /= fsubsetxx //.
  Qed.

  (** Page 4: "≡α is... transitive." *)
  Corollary α_equivalent_transitive :
    forall t u (v : term),
      t ≡_α u ->
      u ≡_α v ->
      t ≡_α v.
  Proof.
    introv [X Htαu] [Y Huαv].
    pose proof α_equivalent'_compose _ _ _ _ _ Htαu Huαv as Htαv.
    exists (X ∩ Y). rewrite compose_identity // in Htαv.
  Qed.

  (** Page 4: "≡α is... symmetric." *)
  Corollary α_equivalent_symmetric :
    forall t u,
      t ≡_α u ->
      u ≡_α t.
  Proof.
    introv [X Hα].
    apply α_equivalent'_converse in Hα.
    - exists X. rewrite converse_identity // in Hα.
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

  (** Since Coq doesn't directly support quotient types, we're representing "Tm^α(X)" as "Tm(X)" and manually proving that functions respect "≡α". *)

  Declare Scope substitution_scope.
  Bind Scope substitution_scope with fmap_of'.
  Delimit Scope substitution_scope with substitution.
  #[local] Open Scope substitution_scope.

  Implicit Types f g : {fmap 𝒱 → term}.

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

  (** Page 4: "Given a substitution f and x ∈ 𝒱, t ∈ Tm(Y) we define the update...." *)
  Definition update_substitution (A : Type) : {fmap 𝒱 → A} -> 𝒱 -> A -> {fmap 𝒱 → A} := @setm _ _.

  #[local] Notation "f '[' x ',' t ']'" :=
    (update_substitution f x t)
      (at level 10, x at next level, t at next level, format "f [ x ',' t ]") :
      substitution_scope.

  (** Page 4: "f[[x,t]] ∈ X ∪ {x} ⟶ Y." *)
  Lemma update_substitution_type :
    forall Y f x t,
      let X := domm f in
      codomm_Tm_set f ⊆ Y ->
      t ∈ Tm Y ->
      domm (f[x,t]) = (X ∪ {x}) /\ codomm_Tm_set (f[x,t]) ⊆ Y.
  Proof.
    intros ? ? ? ? X HfY HtY.
    split.
    - apply eq_fset. intros k.
      rewrite in_fsetU in_fset1.
      apply Bool.eq_iff_eq_true. split; introv Hk.
      + apply (rwP dommP) in Hk as [v Hf'k].
        rewrite setmE in Hf'k.
        destruct (k =P x); subst.
        { apply orbT. }
        rewrite orbF.
        apply (rwP dommP). eauto.
      + apply (rwP dommP).
        rewrite setmE.
        apply (rwP orP) in Hk as [Hfk|Hkx].
        * apply (rwP dommP) in Hfk as [v Hfk].
          destruct (k =P x); subst; eauto.
        * rewrite Hkx. eauto.
    - rewrite -(rwP fsubsetP). intros y Hy.
      apply (rwP codomm_Tm_setP) in Hy as (u & Hyu & Huf).
      apply (rwP codommP) in Huf as [z Hz].
      rewrite setmE in Hz.
      destruct (z =P x); subst.
      { inverts Hz. rewrite /Tm /in_mem /= -(rwP fsubsetP) in HtY. apply HtY. auto. }
      apply (rwP fsubsetP) in HfY. apply HfY.
      apply (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto.
  Qed.

  #[local] Reserved Notation "'⦇' f '⦈'" (format "'⦇' f '⦈'").

  (** Page 4: "A substitution can be extended to a function on terms ⦇f⦈ ∈ Tm(X) ⟶ Tm(Y)...." *)
  Fixpoint lift_substitution f Fresh Y t : term :=
    match t with
    | variable x => odflt t (getm f x)
    | application t u => application (⦇f⦈ Fresh Y t) (⦇f⦈ Fresh Y u)
    | abstraction x t =>
      let z := Fresh Y in
      abstraction z (⦇f[x,variable z]⦈ Fresh (Y ∪ {z}) t)
    end

  where "'⦇' f '⦈'" := (lift_substitution f).

  Lemma α_equivalent_update :
    forall X Y R t u x y,
      R ⊆ X × Y ->
      x ∉ X ->
      y ∉ Y ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    introv HRtype HxnX HynY Hα.
    apply α_equivalent'_observably_equal with (R := R); auto. intros k v Hkt Hkv.
    apply (rwP andP) in HRtype as [HRX HRY].
    apply (rwP fsubsetP) in HRX, HRY.
    rewrite /fmap_to_Prop updateE.
    destruct (k =P x); subst.
    { exfalso. apply (rwP negP) in HxnX. apply HxnX, HRX, (rwP dommP). eauto. }
    rewrite Hkv.
    destruct (y =P v); subst; auto.
    exfalso. apply (rwP negP) in HynY. apply HynY, HRY, (rwP codommP). eauto.
  Qed.

  (** Page 5: Lemma 5. *)
  #[program] Lemma lemma5 :
    forall Y Y' R S f g,
      let X := domm f in
      let X' := domm g in
      R ⊆ X × X' ->
      S ⊆ Y × Y' ->
      partial_bijection R ->
      partial_bijection S ->
      codomm_Tm_set f ⊆ Y ->
      codomm_Tm_set g ⊆ Y' ->
      (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
      forall x y z z',
        z ∉ Y ->
        z' ∉ Y' ->
        forall w w' : 𝒱, R⦅x,y⦆ w w' -> getm (f[x,variable z]) w `≡_α^(S⦅z,z'⦆) getm (g[y,variable z']) w'.
  Proof.
    intros ? ? ? ? ? ? ? ? HRtype HStype HRinj HSinj HfY HgY' HRα ? ? ? ? HnzT Hnz'Y' ? ? HR'w.
    rewrite /fmap_to_Prop updateE in HR'w.
    rewrite !setmE.
    destruct (w =P x); subst.
    - inverts HR'w.
      rewrite !eq_refl.
      apply (rwP getmP).
      rewrite updateE eq_refl //.
    - destruct (getm R w) eqn:HRw; cycle 1.
      { inverts HR'w. }
      destruct (y =P s); subst; inverts HR'w.
      apply not_eq_sym, (introF eqP) in n0. rewrite n0.
      pose proof HRw as H'Rw. apply HRα in H'Rw. inverts H'Rw.
      rewrite <- (rwP is_subset_ofP) in HRtype.
      apply HRtype in HRw as [Hfw Hα].
      apply (rwP dommP) in Hfw as [t Hfw], Hα as [t' Hgw'].
      rewrite -> Hfw, Hgw' in *.
      eapply α_equivalent_update; eauto.
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

  Definition function_space_relation (X Y : Type) (f g : X -> Y) (R : X -> X -> bool) (S : Y -> Y -> bool) : Prop :=
    forall x x' : X, R x x' -> S (f x) (g x').

  Lemma codomm_Tm_set_update_substitution :
    forall Y f x y,
      codomm_Tm_set f ⊆ Y ->
      codomm_Tm_set (f[x,variable y]) ⊆ (Y ∪ {y}).
  Proof.
    intros.
    apply (rwP fsubsetP). intros z Hz.
    rewrite in_fsetU in_fset1 orbC.
    apply (rwP codomm_Tm_setP) in Hz as (t & Hzt & Htf).
    apply (rwP codommP) in Htf as [k Hk]. rewrite setmE in Hk.
    destruct (k =P x); subst. { inverts Hk. rewrite in_fset1 in Hzt. rewrite Hzt //. }
    destruct (z =P y); subst; auto.
    eapply (rwP fsubsetP); eauto.
    apply (rwP codomm_Tm_setP). exists t. split; auto. apply (rwP codommP). eauto.
  Qed.

  (** Page 4: Proposition 4. *)
  #[program] Proposition substitution_preserves_α_congruence' :
    forall Fresh Y Y' R S f g,
      Fresh_correct Fresh ->
      let X := domm f in
      let X' := domm g in
      R ⊆ X × X' ->
      S ⊆ Y × Y' ->
      codomm_Tm_set f ⊆ Y ->
      codomm_Tm_set g ⊆ Y' ->
      partial_bijection R ->
      partial_bijection S ->
      (forall x x', R x x' -> getm f x `≡_α^S getm g x') ->
      function_space_relation (⦇f⦈ Fresh Y) (⦇g⦈ Fresh Y') (α_equivalent' R) (α_equivalent' S).
  Proof.
    intros ? ? ? ? ? ? ? HFresh X X' HRtype HStype HfY HgY' HRinj HSinj HRα.
    intros t u Hα.
    apply (rwP α_equivalent'P) in Hα.
    dependent induction Hα generalizing f g X X' Y Y' S HRtype HStype HSinj HRα HfY HgY'.
    { apply (rwP getmP) in H.
      specialize HRα with x y.
      rewrite <- (rwP is_subset_ofP) in HRtype.
      pose proof H as HRx.
      apply HRα in H.
      apply HRtype in HRx as [Hfx Hgy].
      apply (rwP dommP) in Hfx as [x' Hx'], Hgy as [y' Hy'].
      simpl in *. rewrite -> Hx', -> Hy' in *. auto. }
    { rewrite /= -(rwP andP). auto. }
    assert (abstraction x t ≡_α^R abstraction y u) as H.
    { apply (rwP α_equivalent'P). auto. }
    set (z := Fresh0 Y). set (z' := Fresh0 Y').
    apply IHHα.
    - apply partial_bijection_update. auto.
    - rewrite !domm_set ![_ |: _]fsetUC. apply update_type. auto.
    - apply update_type. auto.
    - apply partial_bijection_update. auto.
    - apply lemma5 with Y Y'; auto; apply HFresh.
    - apply codomm_Tm_set_update_substitution. auto.
    - apply codomm_Tm_set_update_substitution. auto.
  Qed.

  (** Page 5: "We are now going to verify that substitution preserves α-congruence: If we have...." *)
  #[program] Theorem substitution_preserves_α_congruence :
    forall Y Fresh f g,
      let X := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y ->
      codomm_Tm_set g ⊆ Y ->
      domm g = X ->
      (forall x, x ∈ X ->
            getm f x `≡_α^(1__Y) getm g x) ->
      forall t u, t ∈ Tm X ->
             t ≡_α u ->
             ⦇f⦈ Fresh Y t ≡_α ⦇g⦈ Fresh Y u.
  Proof.
    intros ? ? ? ? ? HFresh HfY HgY HX Hα ? ? Hfgt [X' Htαu].
    exists Y.
    apply substitution_preserves_α_congruence' with (R := 1__X) (S := 1__Y); auto.
    - rewrite HX. apply identity_type.
    - apply identity_type.
    - introv Hfxx'.
      rewrite /fmap_to_Prop identityE in Hfxx'.
      destruct (x ∈ X) eqn:Hfx; inverts Hfxx'; auto.
    - apply α_equivalent'_observably_equal with (R := 1__X'); auto.
      introv Hxt Hxy.
      rewrite /fmap_to_Prop !identityE in Hxy |- *.
      destruct (x ∈ X') eqn:HxX'; inverts Hxy.
      rewrite /Tm /in_mem /= -(rwP fsubsetP) in Hfgt.
      apply Hfgt in Hxt. rewrite Hxt //.
  Qed.

  (** Page 5: "A consequence of proposition 4 is that substitution is an operation on α-equivalence classes." *)
  Theorem lift_substitution_respects_α_equivalence :
    forall Y Fresh f t u,
      let X := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y ->
      t ∈ Tm X ->
      t ≡_α u ->
      ⦇f⦈ Fresh Y t ≡_α ⦇f⦈ Fresh Y u.
  Proof.
    intros ? ? ? ? ? ? HFresh Hft HtX Hα.
    apply substitution_preserves_α_congruence; eauto.
    introv Hfx.
    apply (rwP dommP) in Hfx as [v Hv].
    rewrite Hv.
    apply α_equivalent'_identity.
    rewrite /Tm /in_mem /= -(rwP fsubsetP). intros y Hy.
    apply (rwP fsubsetP) in Hft. apply Hft.
    apply (rwP codomm_Tm_setP). exists v. split; auto.
    apply (rwP codommP). eauto.
  Qed.

  (** Page 6: Lemma 7. *)
  Lemma lemma7 :
    forall Y Fresh (f : {fmap 𝒱 → 𝒱}) t,
      let X := domm f in
      Fresh_correct Fresh ->
      partial_bijection f ->
      codomm f ⊆ Y ->
      t ∈ Tm X ->
      ⦇mapm variable f⦈ Fresh Y t ≡_α^(f ᵒ) t.
  Proof.
    intros ? ? ? ? ? HFresh Hfinj HfY HtX.
    apply (rwP fsubsetP) in HfY.
    gen Y f. induction t; intros ? ? ? Hfinj HfY HtX.
    - rename s into x.
      set (z := Fresh0 Y).
      rewrite /= /update_substitution -mapm_setm -/update_substitution -update_converse -/z //.
      replace (setm f x z) with (f⦅x,z⦆); cycle 1.
      { apply eq_fmap. intros y.
        rewrite updateE setmE /=.
        destruct (y =P x); subst; auto.
        destruct (getm f y) eqn:Hfy; auto.
        destruct (z =P s); subst; auto.
        assert (z ∈ Y) as HFreshY. { apply HfY, (rwP codommP). eauto. }
        pose proof HFresh Y as HnFresh. rewrite HFreshY // in HnFresh. }
      apply IHt; auto.
      + apply partial_bijection_update. auto.
      + intros s Hst.
        rewrite in_fsetU in_fset1 orbC.
        apply (rwP codommP) in Hst as [k Hk]. rewrite updateE in Hk.
        destruct (k =P x); subst. { inverts Hk. rewrite eq_refl //. }
        destruct (s =P z); subst; auto.
        apply HfY, (rwP codommP).
        destruct (getm f k) eqn:Hfk; cycle 1. { inverts Hk. }
        destruct (z =P s0); subst; inverts Hk. eauto.
      + rewrite /Tm /in_mem /= -(rwP fsubsetP). intros y Hy.
        apply (rwP dommP). rewrite updateE.
        destruct (y =P x); subst; eauto.
        assert (y ∈ FV t :\ x) as Hytnx.
        { apply (introF eqP) in n. rewrite in_fsetD in_fset1 n Hy //. }
        rewrite /Tm /in_mem /= -(rwP fsubsetP) in HtX.
        apply HtX in Hytnx.
        apply (rwP dommP) in Hytnx as [u Hu]. rewrite Hu.
        destruct (z =P u); subst; eauto.
        assert (z ∈ Y) as Hzy. { apply HfY, (rwP codommP). eauto. }
        pose proof HFresh Y as HnFresh. rewrite Hzy // in HnFresh.
    - rewrite /Tm /in_mem /= fsubUset -(rwP andP) in HtX. destruct HtX as [Ht1X Ht2X].
      rewrite /= -(rwP andP). split; auto.
    - rewrite /Tm /in_mem /= fsub1set in HtX. apply (rwP dommP) in HtX as [t Ht].
      rewrite /= mapmE Ht /= -(rwP getmP). apply getm_inv. rewrite invmK // (rwP injectivemP) //.
  Qed.

  (** Page 6: "η(x) = x." *)
  Definition η__ X : {fmap 𝒱 → term} := 1__X.

  Lemma ηE :
    forall X x,
      getm (η__ X) x =
        if x ∈ X
        then Some (variable x)
        else None.
  Proof.
    introv.
    rewrite mapmE identityE.
    destruct (x ∈ X) eqn:HxX; auto.
  Qed.

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
      rewrite mapmE identityE in Hℛηt.
      destruct (x' ∈ X) eqn:Hx'X; inverts Hℛηt.
      rewrite in_fset1 in Hxt. apply (rwP eqP) in Hxt. subst. auto.
    - apply (rwP codomm_Tm_setP). exists (variable x). split.
      { rewrite /= in_fset1 eq_refl //. }
      apply (rwP codommP). exists x.
      rewrite ηE HxX //.
  Qed.

  (** Page 4: Corollary 2. *)
  Lemma α_equivalent'_update :
    forall X Y R t u x y,
      R ⊆ X × Y ->
      t ∈ Tm X ->
      u ∈ Tm Y ->
      x ∉ X ->
      y ∉ Y ->
      t ≡_α^R u ->
      t ≡_α^(R⦅x,y⦆) u.
  Proof.
    introv HRtype HtX HuY HxnX HynY Hα.
    rewrite /Tm /in_mem /= -!(rwP fsubsetP) in HtX, HuY.
    apply α_equivalent'_observably_equal with (R := R); auto. intros x' y' Hx't HRx'y'.
    rewrite /fmap_to_Prop updateE in HRx'y' |- *.
    destruct (x' =P x); subst.
    { apply HtX in Hx't. rewrite Hx't // in HxnX. }
    rewrite HRx'y'.
    destruct (y =P y'); subst; auto.
    rewrite -(rwP andP) in HRtype. destruct HRtype as [HRX HRY].
    rewrite -(rwP fsubsetP) in HRY.
    assert (y' ∈ codomm R) as HRy'. { apply (rwP codommP). eauto. }
    apply HRY in HRy'. rewrite HRy' // in HynY.
  Qed.

  Lemma FV_lift_substitution :
    forall Fresh Y f t,
      let X := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y ->
      t ∈ Tm X ->
      FV (⦇f⦈ Fresh Y t) = ⋃_(u ∈ pimfset (getm f) (FV t)) (FV u).
  Proof.
    intros ? ? ? ? ? HFresh HfY HtX.
    apply (rwP fsubsetP) in HfY.
    apply eq_fset. intros x.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true.
    split; introv H.
    - apply (rwP hasP).
      gen f Y. induction t; intros; simpl in *.
      + rewrite in_fsetD in_fset1 in H. apply (rwP andP) in H as [HnxFresh Hℛfx].
        apply IHt in Hℛfx as [y Hℛfy Hxy]; auto.
        * apply (rwP pimfsetP) in Hℛfy as [k Hkt Hf'k].
          rewrite setmE in Hf'k.
          destruct (k =P s); subst.
          { inverts Hf'k. rewrite in_fset1 in Hxy. rewrite Hxy // in HnxFresh. }
          exists y; auto.
          apply (rwP pimfsetP). exists k; auto.
          apply (introF eqP) in n.
          rewrite in_fsetD in_fset1 n Hkt //.
        * rewrite /Tm /in_mem /= -(rwP fsubsetP). intros y Hy.
          apply (rwP dommP). rewrite setmE.
          rewrite /Tm /in_mem /= fsubDset -(rwP fsubsetP) in HtX.
          apply HtX in Hy. rewrite in_fsetU in_fset1 in Hy.
          destruct (y =P s); subst; eauto.
          apply (rwP dommP) in Hy as [u Hu]. eauto.
        * intros y Hyt.
          rewrite (rwP fsubsetP) in HfY.
          eapply (rwP fsubsetP); eauto.
          apply codomm_Tm_set_update_substitution. auto.
      + rewrite /Tm /in_mem /= fsubUset -(rwP andP) in HtX. destruct HtX as [Ht1X Ht2X].
        rewrite in_fsetU in H. apply (rwP orP) in H as [Hf'x|Hf'x].
        * apply IHt1 in Hf'x as [k Hf'k Hxk]; auto.
          apply (rwP pimfsetP) in Hf'k as [y Hyt1 Hfy].
          exists k; auto.
          apply (rwP pimfsetP). exists y; auto.
          rewrite in_fsetU Hyt1 //.
        * apply IHt2 in Hf'x as [k Hf'k Hxk]; auto.
          apply (rwP pimfsetP) in Hf'k as [y Hyt2 Hfy].
          exists k; auto.
          apply (rwP pimfsetP). exists y; auto.
          rewrite in_fsetU Hyt2 orbT //.
      + rewrite /Tm /in_mem /= fsub1set -(rwP dommP) in HtX. destruct HtX as [t Ht].
        rewrite Ht /= in H. exists t; auto.
        apply (rwP (@pimfsetP _ _ (getm f) (fset1 s) t)). exists s; auto. rewrite in_fset1 //.
    - apply (rwP hasP) in H as [t' Hft' Hxt'].
      apply (rwP pimfsetP) in Hft' as [x' Hx't Hfx'].
      rewrite /Tm /in_mem /= -(rwP fsubsetP) in HtX.
      gen Y f. induction t; intros ? ? ? HfY Ht'X Hfx'; simpl in *.
      + rewrite in_fsetD in_fset1 in Hx't. apply (rwP andP) in Hx't as [Hnx's Hx't].
        rewrite in_fsetD in_fset1.
        assert (x ∈ Y) as HxY.
        { apply HfY, (rwP codomm_Tm_setP). exists t'. split; auto. apply (rwP codommP). eauto. }
        pose proof HFresh Y as HFreshY.
        destruct (x =P Fresh0 Y); subst.
        { rewrite HxY // in HFreshY. }
        apply IHt; auto.
        * apply (rwP fsubsetP), codomm_Tm_set_update_substitution, (rwP fsubsetP). auto.
        * rewrite setmE. destruct (x' =P s); subst; auto. inverts Hnx's.
        * intros y Hy.
          rewrite domm_set in_fsetU in_fset1.
          destruct (y =P s); subst; auto.
          apply (introF eqP) in n0.
          assert (y ∈ FV t :\ s) as Hytns. { rewrite in_fsetD in_fset1 Hy n0 //. }
          apply Hfx' in Hytns. auto.
      + rewrite in_fsetU.
        rewrite in_fsetU in Hx't.
        rewrite (rwP fsubsetP) fsubUset -(rwP andP) in Hfx'. destruct Hfx' as [Ht1X Ht2X].
        apply (rwP orP) in Hx't as [Hx't1|Hx't2].
        * eapply IHt1 in HfY; auto.
          -- rewrite HfY //.
          -- apply (rwP fsubsetP). auto.
        * eapply IHt2 in HfY; auto.
          -- rewrite HfY orbC //.
          -- apply (rwP fsubsetP). auto.
      + rewrite in_fset1 in Hx't. apply (rwP eqP) in Hx't. subst.
        rewrite Ht'X //.
  Qed.

  (** Page 4: "⦇f⦈ ∈ Tm(X) ⟶ Tm(Y)." *)
  Lemma lift_substitution_type :
    forall Fresh Y f t,
      let X := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y ->
      t ∈ Tm X ->
      ⦇f⦈ Fresh Y t ∈ Tm Y.
  Proof.
    intros ? ? ? ? ? HFresh HfY HtX.
    rewrite /Tm /in_mem /=. rewrite -(rwP fsubsetP). introv Hf'x.
    rewrite FV_lift_substitution // in_bigcup in Hf'x. apply (rwP hasP) in Hf'x as [t' Hf't' Hxt'].
    apply (rwP pimfsetP) in Hf't' as [x' Hx't Hfx'].
    apply (rwP fsubsetP) in HfY.
    rewrite /Tm /in_mem /= in HtX. apply (rwP fsubsetP) in HtX.
    apply HfY, (rwP codomm_Tm_setP). exists t'. split; auto.
    apply (rwP codommP). eauto.
  Qed.

  (** Page 7: "We have to show ⦇f[[z0, z1]]⦈ ∘ g[[x, z0]](v) ≡α (⦇f⦈ ∘ g)[[x, z1]](v)." *)
  #[program] Lemma lift_update_substitution_compose_substitution_update :
    forall Fresh Z f g x z0 z1,
      let X := domm g in
      let Y := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Z ->
      codomm_Tm_set g ⊆ Y ->
      z0 ∉ Y ->
      z1 ∉ Z ->
      forall v, v ∈ (X ∪ {x}) ->
           getm (⦇f[z0,variable z1]⦈ Fresh (Z ∪ {z1}) ∘ g[x,variable z0]) v `≡_α^(1__(Z ∪ {z1})) getm ((⦇f⦈ Fresh Z ∘ g)[x,variable z1]) v.
  Proof.
    intros ? ? ? ? ? ? ? ? ? HFresh HfZ HgY Hz0Y Hz1Z ? HvXx.
    rewrite in_fsetU in_fset1 in HvXx.
    destruct (v =P x); subst.
    { apply (rwP eqP) in HvXx. subst. rewrite /= setmE mapmE setmE eq_refl /= setmE eq_refl /= -(rwP getmP) identityE in_fsetU in_fset1 orbC eq_refl //. }
    apply (introF eqP) in n.
    apply (rwP orP) in HvXx as [HvX | HvX]; cycle 1.
    { discriminate. }
    apply (rwP dommP) in HvX as [t Hgv].
    replace (getm (⦇f[z0,variable z1]⦈ Fresh0 (Z ∪ {z1}) ∘ g[x,variable z0]) v) with (omap (⦇f[z0,variable z1]⦈ Fresh0 (Z ∪ {z1})) (getm g v)); cycle 1.
    { rewrite mapmE setmE n Hgv //. }
    replace (getm ((⦇f⦈ Fresh0 Z ∘ g)[x,variable z1]) v) with (omap (⦇f⦈ Fresh0 Z) (getm g v)); cycle 1.
    { rewrite setmE mapmE n //. }
    rewrite Hgv /=.
    apply α_equivalent'_observably_equal with (R := 1__Z).
    { intros k v' Hk Hkv'.
      rewrite /fmap_to_Prop !identityE in_fsetU in Hkv' |- *.
      destruct (k ∈ Z) eqn:HkZ; inverts Hkv'; auto. }
    apply substitution_preserves_α_congruence' with (R := 1__Y); auto.
    - rewrite /is_subset_of domm_identity domm_set codomm_identity -(rwP andP). split.
      + apply fsubsetUr.
      + apply fsubsetxx.
    - apply (rwP is_subset_ofP). intros y z Hyz.
      rewrite /fmap_to_Prop identityE in Hyz.
      rewrite in_fsetU in_fset1.
      destruct (y ∈ Z) eqn:HZ; inverts Hyz; auto.
    - apply codomm_Tm_set_update_substitution. auto.
    - intros y z Hyz.
      rewrite /fmap_to_Prop identityE in Hyz.
      destruct (y ∈ Y) eqn:HyY; inverts Hyz; auto.
      rewrite setmE.
      destruct (z =P z0); subst.
      { rewrite HyY // in Hz0Y. }
      apply α_equivalent'_identity.
      apply (rwP dommP) in HyY as [u Hu].
      rewrite Hu /Tm /in_mem /=. apply (rwP fsubsetP). intros y Hy.
      apply (rwP fsubsetP) in HfZ. apply HfZ.
      apply (rwP codomm_Tm_setP). exists u. split; auto.
      apply (rwP codommP). eauto.
    - apply α_equivalent'_identity.
      rewrite /Tm /in_mem /=.
      eapply fsubset_trans with (codomm_Tm_set g); auto.
      rewrite -(rwP fsubsetP). intros y Hy.
      apply (rwP codomm_Tm_setP). exists t. split; auto.
      apply (rwP codommP). eauto.
  Qed.

  (** Page 6: Proposition 6.1. *)
  Proposition monad_substitution1 :
    forall Fresh X t,
      Fresh_correct Fresh ->
      t ∈ Tm X ->
      ⦇η__ X⦈ Fresh X t ≡_α t.
  Proof.
    introv HFresh HtX.
    exists X. replace (1__X) with ((1__X)ᵒ); cycle 1.
    { apply converse_identity. }
    apply lemma7; auto.
    - rewrite codomm_identity fsubsetxx //.
    - rewrite domm_identity //.
  Qed.

  (** Page 6: Proposition 6.2. *)
  #[program] Proposition monad_substitution2 :
    forall Fresh f x,
      let X := domm f in
      Fresh_correct Fresh ->
      x ∈ X ->
      getm (⦇f⦈ Fresh X ∘ η__ X) x `≡_α getm f x.
  Proof.
    intros ? ? ? ? HFresh Hfx. rewrite !mapmE identityE Hfx. reflexivity.
  Qed.

  Lemma abstraction_preserves_α_equivalent :
    forall t u x,
      t ≡_α u ->
      abstraction x t ≡_α abstraction x u.
  Proof.
    introv [X Hα].
    exists X. rewrite /= update_identity.
    apply α_equivalent'_observably_equal with (R := 1__X); auto. intros k v Hkt Hkv.
    rewrite /fmap_to_Prop !identityE in_fsetU in Hkv |- *.
    destruct (k ∈ X) eqn:Hkx; inverts Hkv; auto.
  Qed.

  (** Page 6: Proposition 6.3. *)
  Proposition monad_substitution3 :
    forall Fresh Z f g t,
      let X := domm g in
      let Y := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set g ⊆ Y ->
      codomm_Tm_set f ⊆ Z ->
      t ∈ Tm (domm g) ->
      (⦇f⦈ Fresh Z ∘ ⦇g⦈ Fresh Y) t ≡_α ⦇⦇f⦈ Fresh Z ∘ g⦈ Fresh Z t.
  Proof.
    intros ? ? ? ? ? X Y HFresh Hfℛg HℛfZ Hgt.
    gen Z f g. induction t; intros ? ? ? ? ? ? ? ?; cycle 1.
    { unfold Tm, in_mem in *. simpl in *.
      rewrite fsubUset -(rwP andP) in Hgt. destruct Hgt as [Ht1g Ht2g].
      apply IHt1 with (f := f) (Z := Z) in Ht1g as [X1 Ht1g]; eauto.
      apply IHt2 with (f := f) (Z := Z) in Ht2g as [X2 Ht2g]; eauto.
      exists (X1 ∪ X2). rewrite /= -(rwP andP). split.
      - apply α_equivalent'_observably_equal with (R := 1__X1); auto.
        intros k v Hk Hkv. rewrite !/fmap_to_Prop !identityE in Hkv |- *.
        destruct (k ∈ X1) eqn:HkX1; inverts Hkv. rewrite in_fsetU HkX1 //.
      - apply α_equivalent'_observably_equal with (R := 1__X2); auto.
        intros k v Hk Hkv. rewrite !/fmap_to_Prop !identityE in Hkv |- *.
        destruct (k ∈ X2) eqn:HkX2; inverts Hkv. rewrite in_fsetU HkX2 orbC //. }
    { rewrite /Tm /in_mem /= fsub1set in Hgt. apply (rwP dommP) in Hgt as [t Hgs].
      rewrite /= mapmE Hgs /=. reflexivity. }
    set (z0 := Fresh0 Y).
    set (z1 := Fresh0 Z).
    rename s into x, t into t'.
    set (t := abstraction x t').
    replace ((⦇f⦈ Fresh0 Z ∘ ⦇g⦈ Fresh0 Y) t)
      with (⦇f⦈ Fresh0 Z (abstraction z0 (⦇g[x,variable z0]⦈ Fresh0 (Y ∪ {z0}) t')))
      by auto.
    replace (⦇f⦈ Fresh0 Z (abstraction z0 (⦇g[x,variable z0]⦈ Fresh0 (Y ∪ {z0}) t')))
      with (abstraction z1 ((⦇f[z0,variable z1]⦈ Fresh0 (Z ∪ {z1}) ∘ ⦇g[x,variable z0]⦈ Fresh0 (Y ∪ {z0})) t'))
      by auto.
    replace (⦇⦇f⦈ Fresh0 Z ∘ g⦈ Fresh0 Z t)
      with (abstraction z1 (⦇(⦇f⦈ Fresh0 Z ∘ g)[x,variable z1]⦈ Fresh0 (Z ∪ {z1}) t'))
      by auto.
    transitivity (abstraction z1 (⦇⦇f[z0,variable z1]⦈ Fresh0 (Z ∪ {z1}) ∘ g[x,variable z0]⦈ Fresh0 (Z ∪ {z1}) t')).
    { unshelve epose proof @IHt (Z ∪ {z1}) (f[z0,variable z1]) _ (g[x,variable z0]) _ _ as [Z' Hα].
      { apply codomm_Tm_set_update_substitution. auto. }
      { apply fsubset_trans with (Y ∪ {z0}).
        - apply codomm_Tm_set_update_substitution. auto.
        - rewrite domm_set fsetUC fsubsetxx //. }
      { rewrite /Tm /in_mem /= in Hgt |- *. rewrite domm_set -fsubDset //. }
      rewrite /= domm_set [_ |: _]fsetUC in Hα.
      exists Z'. rewrite /= update_identity.
      apply α_equivalent'_observably_equal with (R := 1__Z'); auto. intros k v Hk Hkv.
      rewrite /fmap_to_Prop !identityE in_fsetU in_fset1 in Hkv |- *.
      destruct (k ∈ Z') eqn:HkZ'; inverts Hkv. auto. }
    apply abstraction_preserves_α_equivalent.
    exists (Z ∪ {z1}).
    apply substitution_preserves_α_congruence' with (R := 1__(X ∪ {x})); simpl; auto.
    - rewrite domm_map !domm_set domm_map fsetUC identity_type //.
    - apply identity_type.
    - rewrite <- (rwP fsubsetP). intros k Hk.
      apply (rwP codomm_Tm_setP) in Hk as (u & Hk & Hu).
      apply (rwP codommP) in Hu as [k' Hu].
      rewrite mapmE setmE in Hu.
      destruct (k' =P x); subst.
      { inverts Hu. rewrite setmE eq_refl in_fset1 in Hk. rewrite in_fsetU in_fset1 orbC Hk //. }
      destruct (getm g k') eqn:Hgk'; inverts Hu.
      eapply (rwP fsubsetP); cycle 1. { apply Hk. }
      rewrite <- (rwP fsubsetP). intros y Hy.
      simpl.
      pose proof lift_substitution_type (Z ∪ {z1}) (f[z0,variable z1]) t0 HFresh.
      rewrite /Tm /in_mem /= in H.
      eapply (rwP fsubsetP); cycle 1. { apply Hy. }
      apply H.
      + apply codomm_Tm_set_update_substitution. auto.
      + rewrite domm_set fsubsetU // -(rwP orP). right.
        apply fsubset_trans with (codomm_Tm_set g); auto.
        rewrite <- (rwP fsubsetP). intros z Hz.
        apply (rwP codomm_Tm_setP). exists t0. split; auto. apply (rwP codommP). eauto.
    - apply codomm_Tm_set_update_substitution.
      rewrite <- (rwP fsubsetP). intros k Hk.
      apply (rwP codomm_Tm_setP) in Hk as (u & Hk & Hu).
      apply (rwP codommP) in Hu as [k' Hu].
      rewrite mapmE in Hu.
      destruct (getm g k') eqn:Hgk'; inverts Hu.
      eapply (rwP fsubsetP); cycle 1. { apply Hk. }
      apply lift_substitution_type; auto.
      rewrite /Tm /in_mem /=. apply fsubset_trans with (codomm_Tm_set g); auto.
      rewrite <- (rwP fsubsetP). intros y Hy.
      apply (rwP codomm_Tm_setP). exists t0. split; auto. apply (rwP codommP). eauto.
    - apply partial_bijection_identity.
    - apply partial_bijection_identity.
    - intros y z Hyz.
      rewrite /fmap_to_Prop identityE in_fsetU in_fset1 in Hyz.
      destruct (y =P x); subst.
      + rewrite orbC in Hyz. inverts Hyz.
        apply lift_update_substitution_compose_substitution_update; auto.
        * apply HFresh.
        * apply HFresh.
        * rewrite in_fsetU in_fset1 orbC eq_refl //.
      + destruct (y ∈ X) eqn:HyX; inverts Hyz.
        apply lift_update_substitution_compose_substitution_update; auto.
        * apply HFresh.
        * apply HFresh.
        * rewrite in_fsetU -(rwP orP). auto.
    - apply α_equivalent'_identity. rewrite /Tm /in_mem /= fsubD1set fsetUC // in Hgt.
  Qed.

  Notation "t '[' x '=' u ']' Fresh ',' X" :=
    (⦇(1__X)[x,u]⦈ Fresh X t)
      (at level 10, x at next level, u at next level, format "t [ x '=' u ] Fresh ',' X") :
      term_scope.

  #[local] Notation "t '[' x '⟵' u ']' Fresh ',' X" :=
    (t[x=u]Fresh,X)
      (at level 10, x at next level, u at next level, format "t [ x '⟵' u ] Fresh ',' X") :
      term_scope.

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

  (** Page 5: "To show that substitution is well behaved, i.e. laws such as...." *)
  Lemma substitution_law1 :
    forall Fresh X t u x,
      Fresh_correct Fresh ->
      t ∈ Tm X ->
      u ∈ Tm X ->
      x ∉ X ->
      t[x⟵u]Fresh,X ≡_α t.
  Proof.
    introv HFresh HtXx HuX HnxX.
    transitivity (⦇η__ X⦈ Fresh0 X t).
    - exists X.
      apply (@substitution_preserves_α_congruence' Fresh0 X X (1__X) (1__X) ((1__X)[x,u]) (η__ X)); auto.
      + rewrite /is_subset_of domm_set domm_map !domm_identity codomm_identity fsubsetU // fsubsetxx // orbC //.
      + apply identity_type.
      + rewrite -(rwP fsubsetP). intros k Hk.
        apply (rwP codomm_Tm_setP) in Hk as (t' & Hkt' & Ht').
        apply (rwP codommP) in Ht' as [y Hy].
        rewrite setmE mapmE identityE in Hy.
        destruct (y =P x); subst.
        * inverts Hy. rewrite /Tm /in_mem /= -(rwP fsubsetP) in HuX. apply HuX. auto.
        * destruct (y ∈ X) eqn:HyX; inverts Hy.
          rewrite in_fset1 -(rwP eqP) in Hkt'. subst. auto.
      + rewrite codomm_Tm_set_η fsubsetxx //.
      + intros y z Hyz.
        rewrite /fmap_to_Prop identityE in Hyz.
        destruct (y ∈ X) eqn:HyX; inverts Hyz.
        rewrite setmE mapmE identityE HyX.
        destruct (z =P x); subst.
        * rewrite HyX // in HnxX.
        * rewrite /= -(rwP getmP) identityE HyX //.
      + apply α_equivalent'_identity. auto.
    - apply monad_substitution1; auto.
  Qed.

  (** Page 5: "To show that substitution is well behaved, i.e. laws such as...." *)
  Lemma substitution_law2 :
    forall Fresh X t u (v : term) x y,
      Fresh_correct Fresh ->
      t ∈ Tm (X ∪ {x} ∪ {y}) ->
      u ∈ Tm (X ∪ {y}) ->
      v ∈ Tm X ->
      x <> y ->
      x ∉ X -> (* See Exercise 2.2 in http://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/geuvers.pdf. *)
      y ∉ X ->
      t[x⟵u]Fresh,(X ∪ {y})[y⟵v]Fresh,X ≡_α t[y⟵v]Fresh,(X ∪ {x})[x⟵u[y⟵v]Fresh,X]Fresh,X.
  Proof.
    introv HFresh Ht Hu Hv Hxny HxnX HynX.
    rewrite /Tm /in_mem /= -!(rwP fsubsetP) in Hu, Hv.
    etransitivity.
    { applys_eq (@monad_substitution3 Fresh0 X ((1__X)[y,v]) ((1__(X ∪ {y}))[x,u]) t); auto.
      - rewrite domm_set [y |: _]fsetUC domm_η //.
      - rewrite domm_set domm_η codomm_update_substitution remmI.
        + rewrite codomm_Tm_set_η -(rwP fsubsetP). intros k Hk.
          rewrite in_fsetU orbC in Hk |- *. rewrite fsetUC.
          apply (rwP orP) in Hk as [Hk|Hk]; auto.
        + apply (introF eqP) in Hxny. rewrite domm_η in_fsetU in_fset1 negb_or HxnX Hxny //.
      - rewrite codomm_update_substitution remmI //; cycle 1.
        { rewrite domm_η //. }
        rewrite -(rwP fsubsetP). intros k Hk.
        rewrite codomm_Tm_set_η in_fsetU in Hk. apply (rwP orP) in Hk as [Hk|Hk]; auto.
      - rewrite domm_set domm_η fsetUC -fsetUA [y |: _]fsetUC fsetUA //. }
    symmetry. etransitivity.
    { applys_eq (@monad_substitution3 Fresh0 X ((1__X)[x,u[y⟵v]Fresh0,X]) ((1__(X ∪ {x}))[y,v]) t); auto.
      - rewrite domm_set [x |: _]fsetUC domm_η //.
      - rewrite domm_set domm_η codomm_update_substitution remmI.
        + rewrite codomm_Tm_set_η -(rwP fsubsetP). intros k Hk.
          rewrite !in_fsetU in_fset1 orbC in Hk |- *. rewrite -(rwP orP).
          repeat apply (rwP orP) in Hk as [Hk|Hk]; auto.
        + apply not_eq_sym, (introF eqP) in Hxny. rewrite domm_η in_fsetU in_fset1 negb_or HynX Hxny //.
      - rewrite codomm_update_substitution remmI //; cycle 1.
        { rewrite domm_η //. }
        rewrite -(rwP fsubsetP). intros k Hk.
        rewrite codomm_Tm_set_η FV_lift_substitution // in Hk.
        + rewrite in_fsetU in_bigcup in Hk. apply (rwP orP) in Hk as [Hk|Hk]; auto.
          apply (rwP hasP) in Hk as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
          rewrite setmE ηE in H0.
          destruct (k' =P y); subst.
          { inverts H0. auto. }
          destruct (k' ∈ X) eqn:Hk'X; inverts H0. rewrite in_fset1 -(rwP eqP) in H. subst. auto.
        + rewrite codomm_update_substitution remmI //; cycle 1.
          { rewrite domm_η //. }
          rewrite -(rwP fsubsetP). intros k' Hk'.
          rewrite codomm_Tm_set_η in_fsetU in Hk'. apply (rwP orP) in Hk' as [Hk'|Hk']; auto.
        + rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
      - rewrite domm_set domm_η fsetUC //. }
    apply substitution_preserves_α_congruence; auto.
    - rewrite -(rwP fsubsetP). intros k Hk.
      apply (rwP codomm_Tm_setP) in Hk as (t' & Hk & Ht').
      apply (rwP codommP) in Ht' as (k' & Hk').
      rewrite /= mapmE setmE ηE in Hk'.
      destruct (k' =P y); subst.
      + inverts Hk'.
        rewrite FV_lift_substitution // in Hk.
        * rewrite in_bigcup in Hk.
          apply (rwP hasP) in Hk as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
          rewrite setmE ηE in H0.
          destruct (k' =P x); subst; cycle 1.
          { destruct (k' ∈ X) eqn:Hk'X; inverts H0. rewrite in_fset1 -(rwP eqP) in H. subst. auto. }
          inverts H0.
          rewrite FV_lift_substitution // in H.
          -- rewrite in_bigcup in H.
             apply (rwP hasP) in H as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk].
             rewrite setmE ηE in H0.
             destruct (k' =P y); subst.
             { inverts H0. auto. }
             destruct (k' ∈ X) eqn:Hk'X; inverts H0.
             rewrite in_fset1 -(rwP eqP) in H. subst. auto.
          -- rewrite -(rwP fsubsetP). intros k' H'k'.
             apply (rwP codomm_Tm_setP) in H'k' as (t' & Hk & Ht').
             rewrite codomm_setmE in Ht'.
             rewrite in_fsetU in_fset1 in Ht'. apply (rwP orP) in Ht' as [Ht'|Ht'].
             { apply (rwP eqP) in Ht'. subst. auto. }
             rewrite remmI in Ht'; cycle 1.
             { rewrite domm_η //. }
             apply (rwP codommP) in Ht' as [k'' Hk''].
             rewrite ηE in Hk''.
             destruct (k'' ∈ X) eqn:Hk''X; inverts Hk''.
             rewrite in_fset1 -(rwP eqP) in Hk. subst. auto.
          -- rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
        * rewrite codomm_update_substitution remmI; cycle 1.
          { rewrite domm_η //. }
          rewrite fsubUset codomm_Tm_set_η fsubsetxx /= -(rwP fsubsetP). intros k' Hk'.
          -- rewrite FV_lift_substitution // in Hk'.
             ++ rewrite in_bigcup in Hk'.
                apply (rwP hasP) in Hk' as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k'' Hk''].
                rewrite setmE ηE in H0.
                destruct (k'' =P y); subst.
                { inverts H0. auto. }
                destruct (k'' ∈ X) eqn:Hk''X; inverts H0. rewrite in_fset1 -(rwP eqP) in H. subst. auto.
             ++ rewrite codomm_update_substitution remmI; cycle 1.
                { rewrite domm_η //. }
                rewrite fsubUset codomm_Tm_set_η fsubsetxx /= -(rwP fsubsetP) //.
             ++ rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
        * rewrite /Tm /in_mem /= domm_set domm_η fsetUC fsubsetU // -(rwP orP). left.
          rewrite -(rwP fsubsetP). auto.
      + rewrite in_fsetU in_fset1 in Hk'.
        destruct (k' ∈ X) eqn:Hk'X.
        * rewrite /= setmE ηE in Hk'.
          destruct (k' =P x); subst.
          { inverts Hk'. rewrite Hk'X // in HxnX. }
          rewrite Hk'X in Hk'. inverts Hk'. rewrite in_fset1 -(rwP eqP) in Hk. subst. auto.
        * destruct (k' =P x); subst; inverts Hk'.
          rewrite setmE eq_refl /= FV_lift_substitution // in Hk.
          -- rewrite in_bigcup in Hk.
             apply (rwP hasP) in Hk as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
             rewrite setmE ηE in H0.
             destruct (k' =P y); subst.
             { inverts H0. auto. }
             destruct (k' ∈ X) eqn:H'k'X; inverts H0. rewrite in_fset1 -(rwP eqP) in H. subst. auto.
          -- rewrite codomm_update_substitution remmI; cycle 1.
             { rewrite domm_η //. }
             rewrite codomm_Tm_set_η fsubUset // fsubsetxx // -(rwP fsubsetP) //.
          -- rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
    - rewrite -(rwP fsubsetP). intros k Hk.
      apply (rwP codomm_Tm_setP) in Hk as (t' & Hk & Ht').
      apply (rwP codommP) in Ht' as [k' Hk'].
      rewrite mapmE setmE ηE in_fsetU in_fset1 in Hk'.
      destruct (k' =P x); subst.
      + inverts Hk'. rewrite FV_lift_substitution // in Hk.
        * rewrite in_bigcup in Hk.
          apply (rwP hasP) in Hk as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
          rewrite setmE ηE in H0.
          destruct (k' =P y); subst.
          { inverts H0. auto. }
          destruct (k' ∈ X) eqn:Hk'X; inverts H0. rewrite in_fset1 -(rwP eqP) in H. subst. auto.
        * rewrite codomm_update_substitution remmI; cycle 1.
          { rewrite domm_η //. }
          rewrite codomm_Tm_set_η fsubUset // fsubsetxx // -(rwP fsubsetP) //.
        * rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
      + destruct (k' ∈ X) eqn:Hk'X.
        * rewrite /= setmE ηE Hk'X in Hk'.
          destruct (k' =P y); subst; inverts Hk'; auto.
          rewrite in_fset1 -(rwP eqP) in Hk. subst. auto.
        * destruct (k' =P y); subst; inverts Hk'.
          rewrite setmE ηE eq_refl in Hk. auto.
    - rewrite /= !domm_map !domm_set !domm_η. apply eq_fset. intros k.
      rewrite !in_fsetU !in_fset1.
      destruct (k =P x); subst.
      { rewrite ![_ || true]orbC //. }
      destruct (k ∈ X) eqn:HkX.
      { rewrite ![_ || true]orbC //. }
      rewrite /= ![_ || false]orbC //.
    - intros k Hk.
      rewrite !mapmE !setmE.
      apply not_eq_sym, (introF eqP) in Hxny.
      rewrite domm_map domm_set domm_η !in_fsetU !in_fset1 -!(rwP orP) in Hk.
      repeat destruct Hk as [Hk|Hk].
      + apply (rwP eqP) in Hk. subst.
        rewrite eq_refl Hxny /= ηE in_fsetU in_fset1 eq_refl orbC /= setmE ηE eq_refl /=.
        rewrite (rwP fsubsetP) in Hv.
        pose proof (substitution_law1 X v (u[y⟵v]Fresh0,X) x HFresh Hv) as [Y Hα]; auto.
        * rewrite /Tm /in_mem /= -(rwP fsubsetP). intros k Hk.
          rewrite FV_lift_substitution // in Hk.
          -- rewrite in_bigcup in Hk.
             apply (rwP hasP) in Hk as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
             rewrite setmE ηE in H0.
             destruct (k' =P y); subst.
             { inverts H0. rewrite -(rwP fsubsetP) in Hv. auto. }
             destruct (k' ∈ X) eqn:Hk'X; inverts H0. rewrite in_fset1 -(rwP eqP) in H. subst. auto.
          -- rewrite codomm_update_substitution remmI; cycle 1.
             { rewrite domm_η //. }
             rewrite codomm_Tm_set_η fsubUset // fsubsetxx //.
          -- rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
        * apply α_equivalent'_observably_equal with (R := 1__Y); auto. intros x' y' Hx' Hx'y'.
          rewrite /fmap_to_Prop !identityE in Hx'y' |- *.
          destruct (x' ∈ Y) eqn:Hx'Y; inverts Hx'y'.
          rewrite FV_lift_substitution // in Hx'.
          -- rewrite in_bigcup in Hx'.
             apply (rwP hasP) in Hx' as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
             rewrite setmE ηE in H0.
             destruct (k' =P x); subst.
             ++ inverts H0.
                rewrite FV_lift_substitution // in H.
                ** rewrite in_bigcup in H.
                   apply (rwP hasP) in H as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k'' Hk''].
                   rewrite setmE ηE in H0.
                   destruct (k'' =P y); subst.
                   { inverts H0. apply (rwP fsubsetP) in Hv. apply Hv in H. rewrite H //. }
                   destruct (k'' ∈ X) eqn:Hk''X; inverts H0.
                   rewrite in_fset1 -(rwP eqP) in H. subst. rewrite Hk''X //.
                ** rewrite codomm_update_substitution remmI; cycle 1.
                   { rewrite domm_η //. }
                   rewrite codomm_Tm_set_η fsubUset // fsubsetxx //.
                ** rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
             ++ destruct (k' ∈ X) eqn:Hk'X; inverts H0.
                rewrite in_fset1 -(rwP eqP) in H. subst. rewrite Hk'X //.
          -- rewrite codomm_update_substitution remmI; cycle 1.
             { rewrite domm_η //. }
             rewrite codomm_Tm_set_η fsubUset // fsubsetxx FV_lift_substitution //.
             ++ rewrite -(rwP fsubsetP). intros k Hk.
                rewrite in_bigcup in Hk.
                apply (rwP hasP) in Hk as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
                rewrite setmE ηE in H0.
                destruct (k' =P y); subst.
                { inverts H0. apply (rwP fsubsetP) in Hv. apply Hv, H. }
                destruct (k' ∈ X) eqn:Hk'X; inverts H0.
                rewrite in_fset1 -(rwP eqP) in H. subst. auto.
             ++ rewrite codomm_update_substitution remmI; cycle 1.
                { rewrite domm_η //. }
                rewrite codomm_Tm_set_η fsubUset // fsubsetxx //.
             ++ rewrite domm_set domm_η fsetUC -(rwP fsubsetP) //.
          -- rewrite domm_set domm_η fsetUC /Tm /in_mem /= fsubsetU // Hv //.
      + destruct (k =P y); subst.
        { rewrite Hk // in HynX. }
        destruct (k =P x); subst.
        { rewrite Hk // in HxnX. }
        apply (introF eqP) in n, n0.
        rewrite !ηE !in_fsetU Hk /= !setmE !ηE n n0 Hk /= -(rwP getmP) identityE Hk //.
      + rewrite eq_sym in Hxny.
        rewrite -(rwP eqP) in Hk. subst.
        rewrite eq_refl /= Hxny /= ηE in_fsetU in_fset1 eq_refl orbC /= !setmE eq_refl /=.
        apply α_equivalent'_identity. rewrite /Tm /in_mem /= FV_lift_substitution //.
        * rewrite -(rwP fsubsetP). intros k Hk.
          rewrite in_bigcup in Hk.
          apply (rwP hasP) in Hk as [t' Ht']. apply (rwP pimfsetP) in Ht' as [k' Hk'].
          rewrite setmE ηE in H0.
          destruct (k' =P y); subst.
          { inverts H0. auto. }
          destruct (k' ∈ X) eqn:Hk'X; inverts H0.
          rewrite in_fset1 -(rwP eqP) in H. subst. auto.
        * rewrite codomm_update_substitution remmI; cycle 1.
          { rewrite domm_η //. }
          rewrite codomm_Tm_set_η fsubUset // fsubsetxx -(rwP fsubsetP) //.
        * rewrite domm_set domm_η fsetUC /Tm /in_mem /= -(rwP fsubsetP) //.
    - rewrite domm_map domm_set domm_η fsetUC //.
    - reflexivity.
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
    rewrite /fmap_to_Prop updateE !setmE !mapmE /=.
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
    - rewrite /fmap_to_Prop identityE in H.
      destruct (x ∈ domm ϕ) eqn:Hϕx; inverts H. auto.
    - rewrite /fmap_to_Prop identityE in H.
      destruct (x ∈ domm ϕ) eqn:Hϕx; inverts H. auto.
    - destruct H as [Hϕx Hϕxy].
      rewrite /fmap_to_Prop identityE Hϕx.
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
      + destruct H as [X H].
        apply α_equivalent'_observably_equal with (R := 1__X); auto.
        intros k v Hk Hkv.
        rewrite /fmap_to_Prop identityE in Hkv.
        destruct (k ∈ X) eqn:Hkt; inverts Hkv.
        apply (rwP fsubsetP) in Htϕ.
        apply Htϕ in Hk.
        rewrite /fmap_to_Prop identityE Hk //.
    - eapply lemma9 with (R := 1__(domm ϕ)) in H; auto.
      + exists (domm ϕ). auto.
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
      rewrite ηE in HtX.
      destruct (y ∈ X) eqn:HyX; inverts HtX.
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
      rewrite setmE mapmE updateE ηE.
      destruct (k =P x); subst; auto.
      rewrite identityE.
      destruct (k ∈ FV t) eqn:Hkt; auto.
      destruct (y =P k); subst; auto.
      rewrite Hkt // in Hnyt. }
    replace ((1__(FV t :\ x))⦅x,y⦆ᵒ) with ((1__(FV t))⦅x,y⦆ᵒ); cycle 1.
    { apply eq_fmap. intros k.
      rewrite !update_converse.
      - rewrite !updateE.
        destruct (k =P y); subst; auto.
        rewrite !converse_identity !identityE !in_fsetD !in_fset1.
        destruct (k =P x); subst; auto.
        destruct (x ∈ FV t) eqn:Hxt; auto. rewrite eq_refl //.
      - apply partial_bijection_identity.
      - apply partial_bijection_identity. }
    apply lemma7.
    - apply partial_bijection_update, partial_bijection_identity.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
      apply (rwP dommP).
      rewrite updateE identityE.
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
      rewrite /fmap_to_Prop identityE in Hϕk.
      destruct (k ∈ domm ϕ) eqn:H'ϕk; inverts Hϕk.
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
      rewrite setmE ηE Hkt.
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
        rewrite /fmap_to_Prop updateE identityE in_fsetD in_fset1 /= in Ht'k.
        rewrite /fmap_to_Prop updateE identityE.
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

  Lemma noop_de_Bruijn_substitution :
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

  Lemma variable_substitution_as_α_equivalent'' :
    forall Fresh t x y,
      Fresh_correct Fresh ->
      y ∉ FV t ->
      t[x⟵variable y]Fresh ≡_α^(1__(FV (t[x⟵variable y]Fresh) :\ y))⦅y,x⦆ t.
  Proof.
    introv HFresh Hnyt.
    replace ((1__(FV (t[x⟵variable y]Fresh0) :\ y))⦅y,x⦆) with (((1__(FV t))⦅x,y⦆)ᵒ); cycle 1.
    { rewrite update_converse.
      - rewrite converse_identity //.
        apply eq_fmap. intros k.
        rewrite !updateE !identityE /= !in_fsetD !in_fset1.
        destruct (x ∈ FV t) eqn:Hxt.
        + rewrite FV_after_substitute' // !in_fsetU !in_fsetD !in_fset1.
          destruct (k =P y); subst; auto.
          destruct (k =P x); subst.
          { rewrite Hxt eq_refl //. }
          destruct (k ∈ FV t) eqn:Hkt; auto.
        + rewrite FV_noop_substitute'; auto; cycle 1.
          { rewrite Hxt //. }
          destruct (k =P y); subst; auto.
      - apply partial_bijection_identity. }
    replace ((1__(FV t))[x,variable y]) with (mapm variable ((1__(FV t))⦅x,y⦆)); cycle 1.
    { apply eq_fmap. intros k.
      rewrite /fmap_to_Prop setmE !ηE mapmE updateE identityE.
      destruct (k =P x); subst; auto.
      destruct (k ∈ FV t) eqn:Hkt; auto.
      destruct (y =P k); subst; auto.
      rewrite Hkt // in Hnyt. }
    apply lemma7'; auto.
    { apply partial_bijection_update, partial_bijection_identity. }
    rewrite /Tm /in_mem /mem /=. apply (rwP fsubsetP). intros k Hkt.
    apply (rwP dommP).
    rewrite updateE identityE Hkt /=.
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
    apply variable_substitution_as_α_equivalent''; auto. apply HFresh.
  Qed.

  Lemma variable_substitution_as_α_equivalent''' :
    forall Fresh t x y,
      Fresh_correct Fresh ->
      y ∉ FV t ->
      t[x⟵variable y]Fresh ≡_α^(1__(FV (t[x⟵variable y]Fresh)))⦅y,x⦆ t.
  Proof.
    introv HFresh Hnyt.
    apply α_equivalent'_supermap with (R__sub := (1__(FV (t[x⟵variable y]Fresh0) :\ y))⦅y,x⦆); cycle 1.
    { apply variable_substitution_as_α_equivalent''; auto. }
    introv Hkv.
    rewrite /fmap_to_Prop updateE identityE in Hkv.
    rewrite /fmap_to_Prop updateE identityE.
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
      destruct (k ∈ FV t) eqn:Hkt; auto.
  Qed.

  Lemma variable_substitution_as_α_equivalent''' :
    forall t x y,
      y ∉ FV t ->
      t[x⟵variable y]Fresh ≡_α^(1__(FV (t[x⟵variable y]Fresh)))⦅y,x⦆ t.
  Proof.
    introv Hnyt.
    apply variable_substitution_as_α_equivalent'''; auto. apply HFresh.
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
    rewrite /fmap_to_Prop updateE in HR'x'.
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
      rewrite updateE eq_refl //.
    - apply negbTE, (introN pimfsetP). intros [k Hk].
      rewrite updateE in H.
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
        rewrite updateE identityE in_fsetD in_fset1 in H.
        destruct (z =P x); subst.
        { rewrite Hzt // in Hxt. }
        rewrite Hzt /= in H.
        destruct (y =P z); subst; inverts H; auto. }
      transitivity t.
      { rewrite substitution_law1 // Hxt //. }
      rewrite /α_equivalent /= in Hα.
      apply α_equivalent'_remove_noop_update in Hα; auto; cycle 1.
      { apply partial_bijection_identity. }
      { rewrite Hxt //. }
      apply α_equivalent'_supermap with (R__sub := 1__(FV t :\ x)); auto. intros k v Hkv.
      rewrite /fmap_to_Prop identityE in_fsetD in_fset1 in Hkv.
      rewrite /fmap_to_Prop identityE.
      destruct (k =P x); subst; auto.
      rewrite Hxt in Hkv; inverts Hkv.
    - rewrite /α_equivalent /= in Hα.
      rewrite /α_equivalent FV_after_substitute //=.
      replace (1__(FV t :\ x ∪ {y}))
        with (((1__(FV t :\ x))⦅y,x⦆);;((1__(FV t :\ x))⦅x,y⦆)); cycle 1.
      { apply eq_fmap. intros k.
        rewrite composeE updateE !identityE in_fsetU !in_fsetD !in_fset1 /=.
        destruct (k =P y); subst.
        { rewrite /= orbT updateE identityE in_fsetD in_fset1 eq_refl //. }
        apply not_eq_sym, (introF eqP) in n0.
        destruct (k =P x); subst; auto.
        apply not_eq_sym, (introF eqP) in n1.
        destruct (k ∈ FV t) eqn:Hkt; auto.
        rewrite /= n1 updateE identityE in_fsetD in_fset1 eq_sym/n1 n1 Hkt /= n0 //. }
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
    rewrite /fmap_to_Prop identityE in_fsetU Hxt ?orbT in Hxy; inverts Hxy;
    rewrite /fmap_to_Prop identityE Hxt //.
  Qed.

  Lemma α_equivalent_variables :
    forall x y,
      variable x ≡_α variable y ->
      x = y.
  Proof.
    introv Hα.
    rewrite /α_equivalent /= in Hα.
    apply (rwP getmP) in Hα.
    rewrite identityE in_fset1 eq_refl in Hα.
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
        rewrite /fmap_to_Prop identityE in Hkv.
        rewrite /fmap_to_Prop identityE in_fsetU in_fset1.
        destruct (k ∈ FV t) eqn:Hkt; inverts Hkv; auto.
      + rewrite /α_equivalent /=.
        rewrite <- (rwP andP).
        split;
        eapply α_equivalent'_supermap with (R__sub := 1__(FV _)); eauto; introv Hkv;
        rewrite /fmap_to_Prop identityE in Hkv;
        rewrite /fmap_to_Prop identityE in_fsetU;
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
             { reflexivity. }
             intros k x Hkx.
             rewrite /fmap_to_Prop identityE in Hkx.
             rewrite /fmap_to_Prop updateE identityE in_fsetD !in_fset1 /=.
             destruct (k =P v); subst.
             { rewrite Hvt // in Hkx. }
             destruct (k ∈ FV t) eqn:Hkt; inverts Hkx.
             simpl.
             destruct (v' =P x); subst; auto.
             rewrite Hkt // in H.
          -- rewrite /α_equivalent /= update_identity fsetU_after_fsetD.
             apply α_equivalent'_supermap with (R__sub := 1__(FV t)); cycle 1.
             { apply α_equivalent_symmetric, substitution_law1. rewrite Hvt //. }
             intros k x Hkx.
             rewrite /fmap_to_Prop identityE in Hkx.
             rewrite /fmap_to_Prop identityE in_fsetU in_fset1.
             destruct (k ∈ FV t) eqn:Hkt; inverts Hkx.
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

  Lemma FV_lift_substitution_subset_codomm_Tm_set :
    forall Fresh f t,
      Fresh_correct Fresh ->
      FV t ⊆ domm f ->
      FV (⦇f⦈ Fresh t) ⊆ codomm_Tm_set f.
  Proof.
    introv HFresh Htf.
    apply (rwP fsubsetP). introv Hxt.
    rewrite FV_lift_substitution // in_bigcup in Hxt.
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
    apply FV_lift_substitution_subset_codomm_Tm_set; auto. apply HFresh.
  Qed.

  Lemma lift_substitution_disjoint_update_substitution :
    forall Fresh f x y t,
      Fresh_correct Fresh ->
      FV t ⊆ domm f ->
      getm f x = Some (variable x) ->
      x ∉ codomm_Tm_set (remm f x) ->
      y ∉ codomm_Tm_set f ->
      ⦇f[x,variable y]⦈ Fresh t ≡_α (⦇f⦈ Fresh t)[x⟵variable y]Fresh.
  Proof.
    introv HFresh Htf Hfx Hxnℛf Hynℛf.
    transitivity ((⦇(1__(codomm_Tm_set f))[x,variable y]⦈ Fresh0 ∘ ⦇f⦈ Fresh0) t : term); cycle 1.
    { apply lift_substitution_indistinguishable_substitutions; auto.
      { rewrite /Tm /in_mem /= !domm_update_substitution !domm_identity' fsubsetI !fsubsetU //.
        - rewrite fsubsetxx //.
        - rewrite FV_lift_substitution_subset_codomm_Tm_set //. }
      intros z Hzft.
      rewrite /update_substitution !setmE !ηE Hzft.
      destruct (z =P x); subst.
      { reflexivity. }
      pose proof @FV_lift_substitution_subset_codomm_Tm_set Fresh0 f t HFresh Htf as Hft.
      apply (rwP fsubsetP) in Hft.
      apply Hft in Hzft. rewrite Hzft. reflexivity. }
    transitivity (⦇⦇(1__(codomm_Tm_set f))[x,variable y]⦈ Fresh0 ∘ f⦈ Fresh0 t : term); cycle 1.
     { symmetry. apply monad_substitution3; auto.
      rewrite domm_update_substitution domm_identity' fsubsetU // fsubsetxx //. }
    apply lift_substitution_indistinguishable_substitutions; auto.
    { rewrite /Tm /in_mem /= domm_map !domm_update_substitution fsubsetI fsubsetU Htf //. }
    intros z Hzt.
    rewrite /update_substitution mapmE setmE.
    destruct (z =P x); subst.
    { apply (rwP fsubsetP) in Htf. apply Htf, (rwP dommP) in Hzt as [u Hxu].
      rewrite Hxu in Hfx. inverts Hfx. rewrite Hxu /= setmE eq_refl. reflexivity. }
    destruct (getm f z) eqn:Hfz; cycle 1.
    { reflexivity. }
    transitivity (⦇η__(FV t0)⦈ Fresh0 t0).
    { symmetry. apply monad_substitution1; auto. rewrite /Tm /in_mem /= fsubsetxx //. }
    apply lift_substitution_indistinguishable_substitutions; auto.
    - rewrite /Tm /in_mem /= domm_set !domm_map !domm_mkfmapf fsubsetI fsubsetU fsvalK.
      { rewrite fsubsetxx //. }
      apply (rwP orP). right.
      apply (rwP fsubsetP). intros k Hk.
      apply (rwP codomm_Tm_setP). exists t0. split; auto.
      apply (rwP codommP). eauto.
    - intros k Hk.
      rewrite setmE !mapmE !identityE Hk /=.
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

  Lemma lift_substitution_disjoint_update_substitution :
    forall Fresh f x y t,
      Fresh_correct Fresh ->
      (FV t :\ x) ⊆ domm f ->
      x ∉ codomm_Tm_set f ->
      y ∉ codomm_Tm_set f ->
      x <> y ->
      ⦇f[x,variable y]⦈ Fresh t ≡_α (⦇f[x,variable x]⦈ Fresh t)[x⟵variable y]Fresh.
  Proof.
    introv HFresh Ht'f Hxnℛf Hynℛf Hxny.
    replace (f[x,variable y]) with (f[x,variable x][x,variable y]); cycle 1.
    { rewrite update_substitution_overwrite //. }
    apply lift_substitution_disjoint_update_substitution; auto.
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

  Lemma lift_substitution_disjoint_update_substitution :
    forall f x y t,
      (FV t :\ x) ⊆ domm f ->
      x ∉ codomm_Tm_set f ->
      y ∉ codomm_Tm_set f ->
      x <> y ->
      ⦇f[x,variable y]⦈ t ≡_α (⦇f[x,variable x]⦈ t)[x⟵variable y].
  Proof.
    introv Ht'f Hxnℛf Hynℛf Hxny.
    apply lift_substitution_disjoint_update_substitution; auto. apply HFresh.
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
        rewrite /fmap_to_Prop identityE in Hkv.
        rewrite /fmap_to_Prop identityE.
        destruct (k ∈ FV t') eqn:Hkt; inverts Hkv.
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
      t[x⟵variable y]Fresh ≡_α^R u.
  Proof.
    introv HFresh HRinj HRy Hynt Hα.
    destruct (x ∈ FV t) eqn:Hxt; cycle 1.
    { erewrite α_equivalent'_morphl with (u := t).
      - apply α_equivalent'_remove_noop_update with x y; auto.
        rewrite Hxt //.
      - apply substitution_law1; auto. rewrite Hxt //. }
    apply α_equivalent'_supermap with (R__sub := (1__(FV (t[x⟵variable y]Fresh0)))⦅y,x⦆;;R⦅x,y⦆).
    { introv Hkv.
      rewrite /fmap_to_Prop composeE updateE identityE in Hkv.
      destruct (k =P y); subst.
      { rewrite updateE eq_refl /= in Hkv. inverts Hkv. auto. }
      destruct (k ∈ FV (t[x⟵variable y]Fresh0)) eqn:Hkt'; cycle 1.
      { inverts Hkv. }
      rewrite FV_after_substitute' // in Hkt'.
      destruct (x =P k); subst.
      { inverts Hkv. }
      apply not_eq_sym, (introF eqP) in n0.
      rewrite /= updateE n0 in Hkv.
      destruct (getm R k) eqn:HRk; cycle 1.
      { inverts Hkv. }
      destruct (y =P s); subst; inverts Hkv. auto. }
    apply α_equivalent'_compose with t; auto.
    apply variable_substitution_as_α_equivalent'''; auto.
  Qed.

  Lemma lift_substitution_abstractions_wedge :
    forall Fresh f t x y z,
      Fresh_correct Fresh ->
      FV t ⊆ (domm f ∪ {z}) ->
      x ∉ codomm_Tm_set f ->
      y ∉ codomm_Tm_set f ->
      abstraction x (⦇f[z,variable x]⦈ Fresh t) ≡_α abstraction y (⦇f[z,variable y]⦈ Fresh t).
  Proof.
    introv HFresh Htfz Hx Hy.
    destruct (x =P y); subst.
    { reflexivity. }
    rewrite /α_equivalent /=.
    apply (rwP fsubsetP) in Htfz.
    apply lift_substitution_indistinguishable_substitutions'; auto.
    - rewrite /Tm /in_mem /=. apply (rwP fsubsetP). intros k Hkt.
      rewrite in_fsetI !domm_update_substitution Bool.andb_diag Htfz //.
    - intros k Hkt.
      rewrite !setmE.
      pose proof Hkt as Hkt'.
      apply Htfz in Hkt.
      rewrite in_fsetU in_fset1 orbC in Hkt.
      destruct (k =P z); subst.
      { apply (rwP getmP). rewrite updateE eq_refl //. }
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
      { reflexivity. }
      intros k' v Hk'v.
      rewrite /fmap_to_Prop identityE in Hk'v.
      rewrite /fmap_to_Prop identityE in_fsetD in_fset1.
      destruct (k' ∈ FV u) eqn:Hk'u; inverts Hk'v.
      destruct (v =P x); subst.
      { rewrite Hk'u // in Hx. }
      destruct (v ∈ FV (⦇f[z,variable x]⦈ Fresh0 t)) eqn:Hvf't; auto.
      rewrite FV_lift_substitution // in Hvf't; cycle 1.
      { rewrite /Tm /in_mem /= domm_update_substitution. apply (rwP fsubsetP). auto. }
      rewrite in_bigcup in Hvf't.
      apply negbT in Hvf't. apply (rwP hasPn) in Hvf't.
      assert (u ∈ pimfset (getm (f[z,variable x])) (FV t)) as Hvnu.
      { apply (rwP pimfsetP). exists k; auto.
        rewrite setmE n0 //. }
      apply Hvf't in Hvnu. rewrite Hk'u // in Hvnu.
  Qed.

  Lemma lift_substitution_independent_of_Fresh' :
    forall Fresh' f t,
      Fresh_correct Fresh' ->
      FV t ⊆ domm f ->
      ⦇f⦈ Fresh' t ≡_α ⦇f⦈ t.
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
        apply lift_substitution_abstractions_wedge; auto; apply HFresh.
    - rewrite /α_equivalent /=.
      rewrite <- (rwP andP). split.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (⦇f⦈ Fresh' t1))).
        * introv Hkv.
          rewrite /fmap_to_Prop identityE in Hkv.
          rewrite /fmap_to_Prop identityE in_fsetU.
          destruct (k ∈ FV (⦇f⦈ Fresh' t1)) eqn:Hkft; inverts Hkv. auto.
        * apply H.
          -- rewrite ltnS leq_max leqnn //.
          -- rewrite fsubUset in Hft. apply (rwP andP) in Hft as [Ht1f Ht2f]. auto.
      + apply α_equivalent'_supermap with (R__sub := 1__(FV (⦇f⦈ Fresh' t2))).
        * introv Hkv.
          rewrite /fmap_to_Prop identityE in Hkv.
          rewrite /fmap_to_Prop identityE in_fsetU.
          destruct (k ∈ FV (⦇f⦈ Fresh' t2)) eqn:Hkft; inverts Hkv. rewrite orbC //.
        * apply H.
          -- rewrite ltnS leq_max leqnn orbC //.
          -- rewrite fsubUset in Hft. apply (rwP andP) in Hft as [Ht1f Ht2f]. auto.
    - rewrite fsub1set in Hft.
      apply (rwP dommP) in Hft as [k Hk].
      rewrite /lift_substitution /= Hk. reflexivity.
  Qed.

  Lemma lift_substitution_independent_of_Fresh :
    forall Fresh1 Fresh2 f t,
      Fresh_correct Fresh1 ->
      Fresh_correct Fresh2 ->
      FV t ⊆ domm f ->
      ⦇f⦈ Fresh1 t ≡_α ⦇f⦈ Fresh2 t.
  Proof.
    introv HFresh1 HFresh2 Hft.
    transitivity (⦇f⦈ t).
    { apply lift_substitution_independent_of_Fresh'; auto. }
    symmetry. apply lift_substitution_independent_of_Fresh'; auto.
  Qed.
End AlphaFacts.
