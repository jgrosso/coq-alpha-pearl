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
From AlphaPearl Require Import Alpha Util.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

Obligation Tactic := program_simpl.

#[local] Open Scope fset_scope.

Module AlphaPaperFacts (Import M : Alpha).
  #[local] Implicit Type Fresh : {fset 𝒱} -> 𝒱.

  #[local] Notation "X '∪' '{' x '}'" :=
    (X :|: fset1 x)
      (at level 52, format "X  '∪'  '{' x '}'")
    : fset_scope.

  Canonical term_indType := IndType term [indDef for term_rect].

  Canonical term_eqType := EqType term [derive eqMixin for term].

  Canonical term_choiceType := ChoiceType term [derive choiceMixin for term].

  Canonical term_ordType := OrdType term [derive ordMixin for term].

  #[local] Open Scope term_scope.

  Implicit Types (W X Y Z : {fset 𝒱}) (t u : term) (v w x y z : 𝒱) (R S : {fmap 𝒱 → 𝒱}).

  #[local] Notation FV := free_variables.

  Definition Tm X t : bool := FV t ⊆ X.

  Ltac by_cases'' go_hyps go_goal go_overall depth :=
    match number_to_nat depth with
    | 0 => idtac "by_cases: Recursion limit reached!"; match goal with | |- ?g => idtac g end
    | S ?depth =>
        try (progress (repeat intro; subst; simpl in *; auto;
                       go_hyps ltac:(idtac); go_goal ltac:(idtac);
                       go_overall ltac:(idtac);
                       try discriminate; try contradiction);
             by_cases'' ltac:(go_hyps) ltac:(go_goal) ltac:(go_overall) depth)
    end.

  Ltac by_cases' go_hyps go_goal go_overall :=
    by_cases'' ltac:(go_hyps) ltac:(go_goal) ltac:(go_overall) 100; eauto.

  Ltac by_cases_hyps1 cont :=
    lazymatch goal with
    | H : exists _, _                                        |- _ => destruct H
    | H1 : is_true ?b, H2 : is_true (negb ?b)           |- _ => rewrite H1 // in H2
    | H1 : is_true ?b, H2 : ?b = false                  |- _ => rewrite H1 // in H2
    | H1 : ?x = Some _, H2 : ?x = None                  |- _ => rewrite H1 // in H2
    | H : ex2 _ _                                       |- _ => destruct H
    | H : is_true (has _ _)                             |- _ => apply (rwP hasP) in H as []
    | H : ?b = true                                     |- _ => fold (is_true b) in H
    | H : Some ?x = Some ?y                             |- _ => inverts H
    | H : ?H1 <-> ?H2                                     |- _ => unfold iff in H
    | H : ?H1 /\ ?H2                                     |- _ => destruct H
    | H : ?H1 \/ ?H2                                     |- _ => destruct H
    | H : is_true (?b1 && ?b2)                          |- _ => apply (rwP andP) in H
    | H : ?b1 && ?b2 = false                            |- _ => apply Bool.andb_false_iff in H
    | H : is_true (?b1 || ?b2)                           |- _ => apply (rwP orP) in H
    | H : ?b1 || ?b2 = false                             |- _ => apply Bool.orb_false_iff in H
    | H : is_true (?x ∈ domm ?f)                        |- _ => apply (rwP dommP) in H as []
    | H : is_true (?x ∉ FSet.fsval (domm ?f))           |- _ => apply (rwP dommPn) in H
    | H : (?x ∈ _) = false                              |- _ => apply negbT in H
    | H : is_true (?x ∈ codomm ?f)                      |- _ => apply (rwP codommP) in H as []
    | H : is_true (?x ∉ codomm ?f)                      |- _ => rewrite -(rwP codommPn) in H
    | H : context [ ?X ∪ ?Y ⊆ ?Z ]                      |- _ => rewrite fsubUset in H
    | H : context [ ?X ∪ {?x} ]                         |- _ => rewrite [X ∪ {x}]fsetUC in H
    | H : context [ {subset ?X ∪ ?Y <= ?Z} ]             |- _ => rewrite (rwP fsubsetP) fsubUset in H
    | H : context [ fset1 ?x ⊆ ?X ]                     |- _ => rewrite fsub1set in H
    | H : is_true (?x ∈ FSet.fsval (pimfset ?f [:: ?s])) |- _ => rewrite -(rwP (@pimfsetP _ _ _ (fset1 s) _)) in H
    | H : is_true (?x ∈ FSet.fsval (pimfset ?f ?X))     |- _ => rewrite -(rwP pimfsetP) in H
    | H : is_true (?x ∈ ⋃_(_ ∈ _) _)                     |- _ => rewrite in_bigcup in H
    | H : is_true (injectivem ?m)                       |- _ => rewrite -(rwP injectivemP) in H
    | H : is_true (?X ⊆ ?Y)                             |- _ => rewrite -(rwP fsubsetP) in H
    | H : context [ ?x ∈ ?Y ∪ ?Z ]                      |- _ => rewrite in_fsetU in H
    | H : context [ ?x ∈ ?Z :\: ?y ]                    |- _ => rewrite in_fsetD in H
    | H : context [ ?x ∈ fset1 ?y ]                     |- _ => rewrite in_fset1 in H
    | H : context [ ?t ∈ Tm ?X ]                        |- _ => rewrite /Tm /in_mem in H
    | H : context [ ?x == ?x ]                          |- _ => rewrite eq_refl in H
    | H : context [ ?x == ?y ]                          |- _ => destruct (x =P y)
    | H : context [ ?x || true ]                         |- _ => rewrite orbT in H
    | H : context [ ?x || false ]                        |- _ => rewrite orbF in H
    | H : context [ ?x && true ]                        |- _ => rewrite andbT in H
    | H : context [ ?x && false ]                       |- _ => rewrite andbF in H
    | H : context [ getm (setm ?f ?x ?t) ?y ]           |- _ => rewrite setmE in H
    | H : context [ getm (mapm ?f ?X) ?y ]              |- _ => rewrite mapmE in H
    | H : context [ getm (remm ?f ?x) ?y ]              |- _ => rewrite remmE in H
    | H : context [ domm (setm ?f ?x ?t) ]              |- _ => rewrite domm_set in H
    | H : context [ domm (mapm ?f ?X) ]                 |- _ => rewrite domm_map in H
    | H : context [ getm (mkfmapf _ _) _ ]              |- _ => rewrite mkfmapfE in H
    | H : context [ domm (mkfmapf ?f ?m) ]              |- _ => rewrite domm_mkfmapf in H
    | H : context [ getm (mkfmapfp _ _) _ ]             |- _ => rewrite mkfmapfpE in H
    | H : context [ fmap_to_Prop ]                      |- _ => unfold fmap_to_Prop in H
    | H : context [ omap ?f (getm ?m ?x) = _ ]          |- _ => destruct (getm m x) eqn:?
    | H : context [ _ = omap ?f (getm ?m ?x) ]          |- _ => destruct (getm m x) eqn:?
    | X : {fset _}, H : context [ fset ?X ]             |- _ => rewrite fsvalK in H
    | x := ?y                                           |- _ => subst x
    |   H1 : getm ?f ?x = ?y
      , H2 : context [ getm ?f ?x ]
      |- _
      => rewrite H1 in H2
    |   H : context [ match getm ?f ?x with
                      | Some _ => _
                      | None => _
                      end ]
        |- _
        => let H' := fresh in
          destruct (getm f x) eqn:H'; rewrite ?H' in H
    |   H1 : Fresh_correct ?Fresh
      , H2 : is_true (?Fresh ?Y ∈ ?Y)
      |- _
      => specialize (H1 Y); rewrite H2 // in H1
    |   H1 : {in domm ?f, injective (getm ?f)}
      , H2 : getm (invm ?f) ?x = Some ?y
      |- _
      => apply getm_inv in H2
    |   H : context [ match ?b with
                      | true => _
                      | false => _
                      end ]
        |- _
        => let H' := fresh in
          destruct b eqn:H'; rewrite ?H' in H
    | H : is_true ((?x, ?y) ∈ ?R)                       |- _ =>
        match type of R with
        | {fmap _ → _} => apply (rwP getmP) in H
        | {fmap _ -> _} => apply (rwP getmP) in H
        end
      end || cont.

  Ltac by_cases_goal1 cont :=
    lazymatch goal with
    | |- ?x = true                                     => change (is_true x)
    | |- ?H1 <-> ?H2                                     => unfold iff
    | |- is_true false \/ ?H                            => right
    | |- ?H \/ is_true false                            => left
    | |- ?H1 /\ ?H2                                     => split
    | |- is_true (?b1 && ?b2)                          => rewrite -(rwP andP)
    | |- ?b1 && ?b2 = false                            => apply Bool.andb_false_iff
    | |- is_true (?b1 || ?b2)                           => rewrite -(rwP orP)
    | |- ?b1 || ?b2 = false                             => apply Bool.orb_false_iff
    | |- is_true (?X ⊆ ?Y)                             => rewrite -(rwP fsubsetP)
    | |- is_true (injectivem ?m)                       => rewrite -(rwP injectivemP)
    | |- is_true (?x ∈ FSet.fsval (pimfset ?f [:: ?y])) => rewrite -(rwP (@pimfsetP _ _ _ (fset1 y) _))
    | |- is_true (?x ∈ FSet.fsval (pimfset ?f ?X))     => rewrite -(rwP pimfsetP)
    | |- is_true (?x ∈ ⋃_(_ ∈ _) _)                     => rewrite in_bigcup
    | |- is_true (has _ _)                             => apply (rwP hasP)
    | |- context [ ?x ∈ ?Y ∪ ?z ]                      => rewrite in_fsetU
    | |- context [ ?X ∪ {?x} ]                         => rewrite [X ∪ {x}]fsetUC
    | |- context [ ?x ∈ ?Z :\: ?y ]                    => rewrite in_fsetD
    | |- context [ ?x ∈ fset1 ?y ]                     => rewrite in_fset1
    | |- context [ ?t ∈ Tm ?X ]                        => rewrite /Tm /in_mem
    | |- context [ ?x == ?x ]                          => rewrite eq_refl
    | |- context [ ?x == ?y ]                          => destruct (x =P y)
    | |- context [ fmap_to_Prop ]                      => unfold fmap_to_Prop
    | |- context [ ?x || true ]                         => rewrite orbT
    | |- context [ ?x || false ]                        => rewrite orbF
    | |- context [ ?x && true ]                        => rewrite andbT
    | |- context [ ?x && false ]                       => rewrite andbF
    | |- context [ getm (setm ?f ?x ?t) ?y ]           => rewrite setmE
    | |- context [ getm (mapm ?f ?X) ?y ]              => rewrite mapmE
    | |- context [ getm (remm ?f ?x) ?y ]              => rewrite remmE
    | |- context [ domm (setm ?f ?x ?t) ]              => rewrite domm_set
    | |- context [ domm (mapm ?f ?X) ]                 => rewrite domm_map
    | |- context [ getm (mkfmapf _ _) _ ]              => rewrite mkfmapfE
    | |- context [ domm (mkfmapf ?f ?m) ]              => rewrite domm_mkfmapf
    | |- context [ getm (mkfmapfp _ _) _ ]             => rewrite mkfmapfpE
    | |- is_true (?x ∈ domm ?f)                        => apply (rwP dommP)
    | |- is_true (?x ∉ domm ?f)                        => apply (rwP dommPn)
    | |- is_true (?x ∈ codomm ?f)                      => apply (rwP codommP)
    | |- is_true (?x ∉ codomm ?f)                      => rewrite -(rwP codommPn)
    | X : {fset _} |- context [ fset ?X ]              => rewrite fsvalK
    | |- omap ?f (getm ?m ?x) = _                      => destruct (getm m x) eqn:?
    | |- _ = omap ?f (getm ?m ?x)                      => destruct (getm m x) eqn:?
    | |- context [ match getm ?f ?x with
                  | Some _ => _
                  | None => _
                  end ]
      => destruct (getm f x) eqn:?
    | |- context [ match ?b with
                | true => _
                | false => _
                end ]
      => destruct b eqn:?
    | |- is_true ((?x, ?y) ∈ ?R) =>
        match type of R with
        | {fmap _ → _} => apply (rwP getmP)
        | {fmap _ -> _} => apply (rwP getmP)
        end
    | |- ?X = ?Y =>
        match type of X with
        | {fmap _ → _} => apply eq_fmap; intro
        | {fmap _ -> _} => apply eq_fmap; intro
        | {fset _}     => apply eq_fset; intro; apply Bool.eq_iff_eq_true
        end
    end || cont.

  Ltac by_cases_overall1 cont :=
    lazymatch goal with
    | H : getm ?R ?x = ?y   |- context [ getm ?R ?x ] => rewrite H
    | H : getm ?f ?x = ?y   |- context [ getm ?f ?x ] => rewrite H
    | H : is_true (?x ∈ ?X) |- context [ ?x ∈ ?X ]    => rewrite H
    |   H1 : is_true (?x ∈ FV ?t)
      , H2 : getm ?f ?y = Some ?t
      |- exists t, is_true (?x ∈ FV t) /\ is_true (t ∈ codomm ?f)
      => exists t
    end || cont.

  Ltac by_cases := by_cases' by_cases_hyps1 by_cases_goal1 by_cases_overall1.

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
    by_cases.
    - eapply H; eauto.
    - apply (H x0 x), H0.
    - apply H. by_cases.
    - apply H1. by_cases.
  Qed.

  Ltac by_cases_hyps2 cont := by_cases_hyps1
    ltac:(lazymatch goal with
          | H : context [ ?R ⊆ ?X × ?Y ] |- _ => unfold is_subset_of in H
          end || cont).

  Ltac by_cases_goal2 cont := by_cases_goal1
    ltac:(lazymatch goal with
          | |- context [ ?R ⊆ ?X × ?Y ] => unfold is_subset_of
          end || cont).

  Ltac by_cases_overall2 := by_cases_overall1.

  Ltac by_cases ::= by_cases' by_cases_hyps2 by_cases_goal2 by_cases_overall2.

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
    rewrite unionmE setmE remmE rem_valmE /=. by_cases.
  Qed.

  Ltac by_cases_hyps3 cont := by_cases_hyps2
    ltac:(lazymatch goal with
          | H : context [ getm (?R⦅?x,?y⦆) ?z ] |- _ => rewrite updateE in H
          end || cont).

  Ltac by_cases_goal3 cont := by_cases_goal2
    ltac:(lazymatch goal with
          | |- context [ getm (?R⦅?x,?y⦆) ?z ] => rewrite updateE
          end || cont).

  Ltac by_cases_overall3 := by_cases_overall2.

  Ltac by_cases ::= by_cases' by_cases_hyps3 by_cases_goal3 by_cases_overall3.

  (** Page 3: "It is easy to see that R(x,y) is a partial bijection." *)
  Lemma partial_bijection_update :
    forall R x y,
      partial_bijection R ->
      partial_bijection R⦅x,y⦆.
  Proof.
    by_cases. rewrite -H1 in H2. apply H in H2; by_cases.
  Qed.

  (** Page 3: "R(x,y) ... ∈ (X ∪ {x}) × ...." *)
  Lemma update_type :
    forall X Y R x y,
      R ⊆ X × Y ->
      R⦅x,y⦆ ⊆ (X ∪ {x}) × (Y ∪ {y}).
  Proof.
    by_cases.
    - apply H. by_cases.
    - apply H0. by_cases.
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

    Inductive α_equivalent'' : {fmap 𝒱 → 𝒱} -> term -> term -> Prop :=
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
      destruct u; inverts Hα as Hα; by_cases.
    - introv Hα'.
      dependent induction Hα'; inverts Hα; by_cases.
  Qed.

  Arguments α_equivalent'P {_ _ _}.

  (** Page 3: "We now define ≡α^R ⊆ Tm(X) × Tm(Y)." *)
  Lemma α_equivalent'_type :
    forall R X Y t u,
      R ⊆ X × Y ->
      t ≡_α^R u ->
      t ∈ Tm X /\ u ∈ Tm Y.
  Proof.
    introv HR Hα.
    gen R X Y u. induction t; intros;
    destruct u; inverts Hα; by_cases.
    - apply IHt with (X := X ∪ {s}) (Y := Y ∪ {s0}) in H0 as [Httype Hutype]; by_cases.
      + assert (x ∈ s |: X); by_cases.
      + apply H1. by_cases.
      + apply H2. by_cases.
    - apply IHt with (X := X ∪ {s}) (Y := Y ∪ {s0}) in H0 as [Httype Hutype]; by_cases.
      + assert (x ∈ s0 |: Y); by_cases.
      + apply H1. by_cases.
      + apply H2. by_cases.
    - apply IHt1 with (X := X) (Y := Y) in H; by_cases.
    - apply IHt2 with (X := X) (Y := Y) in H0; by_cases.
    - apply IHt1 with (X := X) (Y := Y) in H; by_cases.
    - apply IHt2 with (X := X) (Y := Y) in H0; by_cases.
    - apply H1. by_cases.
    - apply H2. by_cases.
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
  Proof. rewrite /identity. by_cases. Qed.

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

  Lemma domm_identity : forall X, domm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    by_cases.
    - rewrite /identity' /= /identity /= in H. by_cases.
    - exists x. rewrite /identity' /= /identity /=. by_cases.
  Qed.

  Lemma codomm_identity : forall X, codomm (1__X : {fmap 𝒱 → 𝒱}) = X.
  Proof.
    by_cases.
    - rewrite /identity' /= /identity /= in H. by_cases.
    - exists x. rewrite /identity' /= /identity /=. by_cases.
  Qed.

  Ltac by_cases_hyps4 cont := by_cases_hyps3
    ltac:(lazymatch goal with
          | H : context [ domm (1__?X) ]    |- _ => rewrite ?domm_map domm_identity in H
          | H : context [ getm (1__?X) ?y ] |- _ => rewrite ?mapmE identityE in H
          | H : context [ codomm (1__?X) ]  |- _ => rewrite ?codomm_identity in H
          end || cont).

  Ltac by_cases_goal4 cont := by_cases_goal3
    ltac:(lazymatch goal with
          | |- context [ getm (1__?X) ?y ] => rewrite ?mapmE identityE
          | |- context [ domm (1__?X) ]    => rewrite ?domm_map domm_identity
          | |- context [ codomm (1__?X) ]  => rewrite ?codomm_identity
          end || cont).

  Ltac by_cases_overall4 := by_cases_overall3.

  Ltac by_cases ::= by_cases' by_cases_hyps4 by_cases_goal4 by_cases_overall4.

  (** Page 3: "1X ... ⊆ X × X." *)
  Lemma identity_type : forall X, (1__X : {fmap 𝒱 → 𝒱}) ⊆ X × X.
  Proof. by_cases. Qed.

  (** Page 3: "1X... obviously is a partial bijection." *)
  Lemma partial_bijection_identity : forall X, partial_bijection (1__X : {fmap 𝒱 → 𝒱}).
  Proof. by_cases. Qed.

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
    by_cases. symmetry in H1. apply getm_inv in H0, H1. by_cases.
  Qed.

  #[local] Hint Resolve converse_closed_under_partial_bijection : core.

  Lemma codomm_converse :
    forall R,
      partial_bijection R ->
      codomm (R ᵒ) = domm R.
  Proof.
    unfold converse. by_cases.
    exists x0. apply getm_inv. rewrite invmK //.
  Qed.

  (** Page 3: "Rᵒ ... ⊆ Y × X." *)
  Lemma converse_type :
    forall R X Y,
      R ⊆ X × Y ->
      R ᵒ ⊆ Y × X.
  Proof.
    unfold converse. by_cases. apply getm_inv in H1. apply H. by_cases.
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
  Proof. unfold compose. by_cases. Qed.

  Lemma converse_identity : forall X, (1__X)ᵒ = 1__X.
  Proof.
    unfold converse. by_cases.
    - apply getm_inv. rewrite invmK; by_cases.
    - apply invm_None; by_cases.
  Qed.

  Ltac by_cases_hyps5 cont := by_cases_hyps4
    ltac:(lazymatch goal with
          | H : context [ getm (?R;;?S) ?x ] |- _ => rewrite composeE in H
          | H : context [ (1__?X)ᵒ ]         |- _ => rewrite converse_identity in H
          end || cont).

  Ltac by_cases_goal5 cont := by_cases_goal4
    ltac:(lazymatch goal with
          | |- context [ getm (?R;;?S) ?x ] => rewrite composeE
          | |- context [ (1__?X)ᵒ ]         => rewrite converse_identity
          end || cont).

  Ltac by_cases_overall5 := by_cases_overall4.

  Ltac by_cases ::= by_cases' by_cases_hyps5 by_cases_goal5 by_cases_overall5.

  (** Page 3: "R;S ... ⊆ X × Z." *)
  Lemma compose_type :
    forall R S X Y Z,
      R ⊆ X × Y ->
      S ⊆ Y × Z ->
      R;;S ⊆ X × Z.
  Proof.
    by_cases.
    - apply H. by_cases.
    - apply H1. by_cases.
  Qed.

  (** Page 3: "The set of partial bijections is closed under both operations." *)
  Lemma compose_closed_under_partial_bijection :
    forall R S,
      partial_bijection R ->
      partial_bijection S ->
      partial_bijection (R;;S).
  Proof.
    by_cases.
    rewrite -H1 in H2. apply H0 in H2; by_cases.
    rewrite -H4 in H3. apply H in H3; by_cases.
  Qed.

  (** Page 3: Lemma 1.1. *)
  Lemma update_identity : forall X x, (1__X)⦅x,x⦆ = 1__(X ∪ {x}).
  Proof. by_cases. Qed.

  (** Page 3: Lemma 1.2. *)
  Lemma update_converse :
    forall R x y,
      partial_bijection R ->
      R⦅x,y⦆ᵒ = R ᵒ⦅y,x⦆.
  Proof.
    unfold converse. by_cases;
    (apply getm_inv; rewrite invmK) || apply invm_None; by_cases.
    - rewrite -H2 in H1. apply H in H1; by_cases.
    - rewrite -H2 in H1. apply H in H1; by_cases.
    - rewrite -H0 in Heqo. apply H in Heqo; by_cases.
    - rewrite -H2 in H1. apply H in H1; by_cases.
    - rewrite -H2 in H1. apply H in H1; by_cases.
    - apply invm_None in Heqo; by_cases. Set Printing Coercions. lazymatch goal with
            | H : is_true (_ ∉ codomm _)                      |- _ => rewrite -(rwP codommPn) in H

      end.
    - apply getm_inv.
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

  Ltac by_cases_hyps7 cont := by_cases_hyps5
    ltac:(lazymatch goal with
          | H : is_true (?x ∈ codomm_Tm_set ?f) |- _ => apply (rwP codomm_Tm_setP) in H as (? & ? & ?)
          | H : is_true (?x ∉ codomm_Tm_set ?f) |- _ => apply (rwP codomm_Tm_setPn) in H
          | H : (?x ∈ codomm_Tm_set ?f) = false |- _ => apply negbT in H
          end || cont).

  Ltac by_cases ::= by_cases' by_cases_hyps7 by_cases_goal5 by_cases_overall5.

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
    subst X. split; by_cases. apply HfY. by_cases.
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
    apply (rwP negP) in HxnX, HynY.
    by_cases; exfalso; [apply HxnX, H|apply HynY, H0]; by_cases.
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
    by_cases; destruct (getm R w) eqn:HRw; by_cases.
    eapply α_equivalent_update; by_cases.
  Qed.

  Definition function_space_relation (X Y : Type) (f g : X -> Y) (R : X -> X -> bool) (S : Y -> Y -> bool) : Prop :=
    forall x x' : X, R x x' -> S (f x) (g x').

  Lemma codomm_Tm_set_update_substitution :
    forall Y f x y,
      codomm_Tm_set f ⊆ Y ->
      codomm_Tm_set (f[x,variable y]) ⊆ (Y ∪ {y}).
  Proof. by_cases. apply H. by_cases. Qed.

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
    - by_cases.
    - introv H.
      assert (x' ∈ domm f) as Hfx' by by_cases. specialize (Hα x' Hfx'). by_cases.
    - apply α_equivalent'_observably_equal with (R := 1__X'); by_cases. apply Hfgt in H. by_cases.
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
    introv Hfx. apply α_equivalent'_identity.
    by_cases. apply Hft. by_cases.
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
      { by_cases. destruct (getm f x0) eqn:Hfx; by_cases.
        assert (Fresh0 Y ∈ Y) as HzY. { apply HfY. by_cases. } by_cases. }
      apply IHt; auto.
      + apply partial_bijection_update. auto.
      + by_cases. apply HfY. by_cases.
      + by_cases.
        * assert (Fresh0 Y ∈ Y) as HzY. { apply HfY. by_cases. } by_cases.
        * assert (x0 ∈ FV t :\ x) as Hx0 by by_cases. apply HtX in Hx0. by_cases.
    - by_cases;
      [apply IHt1|apply IHt2]; by_cases;
      assert (x ∈ FV t1 ∪ FV t2) as HX by by_cases; apply HtX in HX; by_cases.
    - by_cases. apply getm_inv. by_cases. rewrite invmK // (rwP injectivemP) //.
  Qed.

  Notation "t '[' x '=' u ']' Fresh ',' X" :=
    (⦇(1__X)[x,u]⦈ Fresh X t)
      (at level 10, x at next level, u at next level, format "t [ x '=' u ] Fresh ',' X") :
      term_scope.

  #[local] Notation "t '[' x '⟵' u ']' Fresh ',' X" :=
    (t[x=u]Fresh,X)
      (at level 10, x at next level, u at next level, format "t [ x '⟵' u ] Fresh ',' X") :
      term_scope.

  Corollary variable_substitution_as_α_equivalent' :
    forall Fresh X t x y,
      Fresh_correct Fresh ->
      t ∈ Tm (X ∪ {x}) ->
      x ∉ X ->
      y ∉ X ->
      t[x⟵variable y]Fresh,(X ∪ {y}) ≡_α^((1__X)⦅y,x⦆) t.
  Proof.
    introv HFresh HtXx HxnX HynX.
    assert (t[x⟵variable y]Fresh0,(X ∪ {y}) ≡_α^(1__(X ∪ {y})) ⦇mapm variable ((1__X)⦅x,y⦆)⦈ Fresh0 (X ∪ {y}) t).
    { apply substitution_preserves_α_congruence' with (R := 1__(X ∪ {x})); by_cases.
      apply α_equivalent'_identity. by_cases. }
    replace ((1__X)⦅y,x⦆) with (1__(X ∪ {y});;(((1__X)⦅x,y⦆)ᵒ)) by by_cases.
    eapply α_equivalent'_compose; eauto.
    apply lemma7; by_cases. apply HtXx in H0. by_cases.
  Qed.

  (** Page 6: "η(x) = x." *)
  Definition η__ X : {fmap 𝒱 → term} := 1__X.

  Arguments η__ / X.

  Lemma ηE :
    forall X x,
      getm (η__ X) x =
        if x ∈ X
        then Some (variable x)
        else None.
  Proof. by_cases. Qed.

  (** Page 6: "ηX ∈ X ⟶ ...." *)
  Lemma domm_η :
    forall X,
      domm (η__ X) = X.
  Proof. by_cases. Qed.

  (** Page 6: "ηX ∈ ... ⟶ Tm^α(X)." *)
  Lemma codomm_Tm_set_η :
    forall X,
      codomm_Tm_set (η__ X) = X.
  Proof.
    by_cases.
    apply Bool.eq_iff_eq_true; by_cases. exists (variable x). by_cases. exists x. by_cases.
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
    apply α_equivalent'_observably_equal with (R := R); by_cases.
    - apply HtX in H. by_cases.
    - cut (y0 ∈ Y : Prop); by_cases. apply H2. by_cases.
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
    apply eq_fset. intros x.
    rewrite in_bigcup.
    apply Bool.eq_iff_eq_true.
    split; introv H; gen Y f;
    induction t; by_cases.
    - apply IHt in H0; by_cases.
      + exists x0; by_cases. exists x1; by_cases.
      + apply HfY. by_cases.
      + assert (x0 ∈ FV t :\ s) by by_cases. apply HtX in H2. by_cases.
    - apply IHt1 in H; by_cases. exists x0; by_cases. exists x1; by_cases.
    - apply IHt2 in H; by_cases. exists x0; by_cases. exists x1; by_cases.
    - exists x0; by_cases. exists s; by_cases.
    - assert (Fresh0 Y ∈ Y). { apply HfY. by_cases. } by_cases.
    - apply IHt; by_cases.
      + apply HfY. by_cases.
      + assert (x2 ∈ FV t :\ s) by by_cases. apply HtX in H4. by_cases.
      + exists x0; by_cases. exists x1; by_cases.
    - left. apply IHt1; by_cases. exists x0; by_cases.
    - right. apply IHt2; by_cases. exists x0; by_cases.
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
    intros ? ? ? ? ? HFresh HfY HtX. rewrite /Tm /in_mem /=. apply (rwP fsubsetP).
    rewrite FV_lift_substitution //; by_cases. apply HfY. by_cases.
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
    intros ? ? ? ? ? ? ? ? ? HFresh HfZ HgY Hz0Y Hz1Z ? HvXx. by_cases.
    apply (introF eqP) in n.
    apply α_equivalent'_observably_equal with (R := 1__Z); by_cases.
    apply substitution_preserves_α_congruence' with (R := 1__(domm f)); by_cases.
    - apply HfZ. by_cases.
    - apply α_equivalent'_identity; by_cases. apply HfZ. by_cases.
    - apply α_equivalent'_identity; by_cases. apply (rwP dommP), HgY. by_cases.
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
    apply lemma7; by_cases.
  Qed.

  (** Page 6: Proposition 6.2. *)
  #[program] Proposition monad_substitution2 :
    forall Fresh f x,
      let X := domm f in
      Fresh_correct Fresh ->
      x ∈ X ->
      getm (⦇f⦈ Fresh X ∘ η__ X) x `≡_α getm f x.
  Proof. by_cases. reflexivity. Qed.

  Lemma abstraction_preserves_α_equivalent :
    forall t u x,
      t ≡_α u ->
      abstraction x t ≡_α abstraction x u.
  Proof.
    introv [X Hα].
    exists X. simpl.
    apply α_equivalent'_observably_equal with (R := 1__X); by_cases.
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
      - apply α_equivalent'_observably_equal with (R := 1__X1); by_cases.
      - apply α_equivalent'_observably_equal with (R := 1__X2); by_cases. }
    { by_cases. reflexivity. }
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
    { unshelve epose proof @IHt (Z ∪ {z1}) (f[z0,variable z1]) _ (g[x,variable z0]) _ _ as [Z' Hα]; by_cases.
      { apply HℛfZ. by_cases. }
      { apply (rwP dommP), Hfℛg. by_cases. }
      { assert (x0 ∈ FV t' :\ x) by by_cases. apply Hgt in H0. by_cases. }
      exists Z'. rewrite /= update_identity.
      apply α_equivalent'_observably_equal with (R := 1__Z'); by_cases. }
    apply abstraction_preserves_α_equivalent.
    exists (Z ∪ {z1}).
    apply substitution_preserves_α_congruence' with (R := 1__(X ∪ {x})); try solve [by_cases].
    - by_cases. rewrite FV_lift_substitution in H; by_cases.
      + apply HℛfZ. by_cases.
      + apply HℛfZ. by_cases.
      + apply (rwP dommP), Hfℛg. by_cases.
    - by_cases. rewrite FV_lift_substitution in H; by_cases.
      + apply HℛfZ. by_cases.
      + apply (rwP dommP), Hfℛg. by_cases.
    - introv H.
      replace x' with x0 by by_cases.
      apply lift_update_substitution_compose_substitution_update; by_cases;
      apply (rwP dommPn); by_cases.
    - apply α_equivalent'_identity; by_cases. apply (rwP dommP), Hgt. by_cases.
  Qed.

  Lemma codomm_update_substitution :
    forall f x t,
      codomm_Tm_set (f[x,t]) = codomm_Tm_set (remm f x) ∪ FV t.
  Proof.
    by_cases.
    apply Bool.eq_iff_eq_true. by_cases.
    - left. by_cases. exists x1. by_cases. exists x2. by_cases.
    - exists x1. by_cases. exists x2. by_cases.
    - exists t. by_cases. exists x. by_cases.
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
      apply (@substitution_preserves_α_congruence' Fresh0 X X (1__X) (1__X) ((1__X)[x,u]) (η__ X)); by_cases.
      apply α_equivalent'_identity. by_cases.
    - apply monad_substitution1; by_cases.
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
    { applys_eq (@monad_substitution3 Fresh0 X ((1__X)[y,v]) ((1__(X ∪ {y}))[x,u]) t); by_cases.
      - cut (x0 ∈ y |: X : Prop); by_cases.
      - cut (x0 ∈ y |: (x |: X) : Prop); by_cases. }
    symmetry. etransitivity.
    { applys_eq (@monad_substitution3 Fresh0 X ((1__X)[x,u[y⟵v]Fresh0,X]) ((1__(X ∪ {x}))[y,v]) t); by_cases.
      rewrite FV_lift_substitution in H; by_cases. }
    apply substitution_preserves_α_congruence; by_cases.
    - rewrite FV_lift_substitution in H; by_cases.
      + rewrite FV_lift_substitution in H1; by_cases.
      + rewrite FV_lift_substitution in H; by_cases.
    - rewrite FV_lift_substitution in H; by_cases.
    - rewrite FV_lift_substitution in H; by_cases.
    - by_cases.
      pose proof (substitution_law1 X v (u[y⟵v]Fresh0,X) x HFresh) as [Y Hα]; by_cases.
      { rewrite FV_lift_substitution in H; by_cases. }
      apply α_equivalent'_observably_equal with (R := 1__Y); by_cases.
      rewrite FV_lift_substitution in H; by_cases.
      + rewrite FV_lift_substitution in H1; by_cases. apply Hv in H3. by_cases.
      + rewrite FV_lift_substitution in H; by_cases.
    - apply α_equivalent'_identity; by_cases.
      rewrite FV_lift_substitution in H; by_cases.
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
    rewrite setmE mapmE. by_cases.
  Qed.

  (** Page 8: "Note that ϕ^+x is an injection, if ϕ is." *)
  Lemma injective_update_ϕ :
    forall ϕ x,
      is_injective ϕ ->
      is_injective (ϕ^+x).
  Proof.
    introv Hϕinj. by_cases.
    rewrite !setmE !mapmE in H, H0. by_cases.
    apply Hϕinj; by_cases.
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
        rewrite domm_set domm_map. by_cases. apply (rwP dommP), Hϕt. by_cases.
    - apply (rwP (@andP (Tm^db _ _) (Tm^db _ _))). split;
      (apply IHt1 || apply IHt2); intros x Hxt;
      apply Hϕt; rewrite in_fsetU Hxt ?orbT //.
    - assert (s ∈ fset1 s) as Hss by by_cases.
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
      by_cases;
      rewrite setmE mapmE. by_cases.
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

  Lemma α_equivalent'_respects_α_equivalence_l :
    forall R t t' u,
      partial_bijection R ->
      t ≡_α t' ->
      t ≡_α^R u ->
      t' ≡_α^R u.
  Proof.
    introv HR Hα Hα'.
    symmetry in Hα. destruct Hα as [X Hα].
    apply α_equivalent'_observably_equal with (R := (1__X);;R).
    { rewrite /fmap_to_Prop. introv Hx Hxy.
      rewrite composeE identityE in Hxy.
      destruct (x ∈ X) eqn:HxX; auto. inverts Hxy. }
    eapply α_equivalent'_compose; eauto.
  Qed.

  Lemma α_equivalent'_respects_α_equivalence_r :
    forall R t u u',
      partial_bijection R ->
      u ≡_α u' ->
      t ≡_α^R u ->
      t ≡_α^R u'.
  Proof.
    introv HR [X Hα] Hα'.
    apply α_equivalent'_converse in Hα'; auto.
    pose proof converse_closed_under_partial_bijection HR as HR'.
    rewrite -(@converseK R) //. apply α_equivalent'_converse; auto.
    eapply α_equivalent'_respects_α_equivalence_l; unfold α_equivalent; eauto.
  Qed.

  Add Parametric Morphism R (HRinj : partial_bijection R) : (α_equivalent' R)
      with signature α_equivalent ==> α_equivalent ==> eq as α_equivalent'_morph.
  Proof.
    intros x x' Hαx y y' Hαy.
    apply Bool.eq_iff_eq_true; split; intros H;
    (symmetry in Hαx, Hαy + idtac);
    eapply α_equivalent'_respects_α_equivalence_l; eauto;
    eapply α_equivalent'_respects_α_equivalence_r; eauto.
  Qed.

  Module A := AlphaFacts M.

  (* Using a non-Unicode name to make it easier to reference in prose. *)
  Lemma alpha_equivalent_adapter :
    forall t u,
      t ≡_α u <-> A.α_equivalent t u.
  Proof.
    intros.
    unfold "≡_α".
    split; introv Hα; eauto.
    destruct Hα as [X Hα].
    apply A.α_equivalent'_implies_α_equivalent; eauto.
  Qed.

  (* Using a non-Unicode name to make it easier to reference in prose. *)
  Theorem alpha_equivalent_correct :
    forall t u,
      t ≡_α u <-> A.trad_α t u.
  Proof.
    intros.
    rewrite alpha_equivalent_adapter. apply A.α_equivalent_correct.
  Qed.

  Lemma lift_substitution_independent_of_codomm_subset :
    forall Fresh Y__sub Y__super f t,
      let X := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y__sub ->
      Y__sub ⊆ Y__super ->
      t ∈ Tm X ->
      ⦇f⦈ Fresh Y__sub t ≡_α ⦇f⦈ Fresh Y__super t.
  Proof.
    introv HFresh HfY__sub HfY__super HtX.
    gen f Y__sub Y__super. induction t; intros; simpl.
    - symmetry.
      exists Y__sub. rewrite /= -converse_identity -update_converse //.
      set (R := ((1__Y__sub)⦅Fresh0 Y__sub,Fresh0 Y__super⦆)).
      assert (is_injective R) as HRinj.
      { apply partial_bijection_update, partial_bijection_identity. }
      assert (Y__sub ∪ {Fresh0 Y__sub} = domm R) as HR.
      { apply eq_fset. intros x. rewrite !in_fsetU in_fset1 orbC.
        apply Bool.eq_iff_eq_true. split; intros H.
        - apply (rwP dommP). rewrite updateE identityE.
          apply (rwP orP) in H as [Hx | H].
          { apply (rwP eqP) in Hx. subst. rewrite eq_refl. eauto. }
          destruct (x == Fresh0 Y__sub) eqn:Hx; eauto.
          rewrite H.
          destruct (Fresh0 Y__super =P x); subst; eauto.
          rewrite -(rwP fsubsetP) in HfY__super. apply HfY__super in H.
          pose proof HFresh Y__super as HFreshY__super. rewrite H // in HFreshY__super.
        - apply (rwP dommP) in H as [y Hy].
          rewrite updateE identityE in Hy.
          destruct (x =P Fresh0 Y__sub); subst; auto.
          destruct (x ∈ Y__sub) eqn:HxY__sub; inverts Hy; auto. }
      assert (⦇f[s,variable (Fresh0 Y__super)]⦈ Fresh0 (Y__super ∪ {Fresh0 Y__super}) t ≡_α ⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t)).
      { etransitivity; cycle 1.
        { symmetry.
          replace
            (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t))
            with ((⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) ∘ ⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub})) t : term); auto.
          rewrite HR. replace (domm R) with (domm (mapm variable R)); cycle 1. { rewrite domm_map //. }
          apply monad_substitution3; auto.
          - rewrite domm_map -HR codomm_update_substitution fsubUset // andbC -(rwP andP) /= fsub1set. split; intros.
            { rewrite in_fsetU in_fset1 eq_refl orbC //. }
            rewrite -(rwP fsubsetP). intros x Hx.
            apply (rwP codomm_Tm_setP) in Hx as (u & Hx & Hu). apply (rwP codommP) in Hu as (y & Hy).
            rewrite remmE in Hy.
            destruct (y =P s); subst. { inverts Hy. }
            rewrite -(rwP fsubsetP) in HfY__sub.
            rewrite in_fsetU -(rwP orP). left.
            apply HfY__sub, (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto.
          - rewrite -(rwP fsubsetP). intros x Hx.
            rewrite in_fsetU in_fset1.
            apply (rwP codomm_Tm_setP) in Hx as (u & Hx & Hu). apply (rwP codommP) in Hu as (y & Hy).
            rewrite mapmE updateE identityE in Hy.
            destruct (y =P Fresh0 Y__sub); subst.
            { inverts Hy. rewrite in_fset1 -(rwP eqP) in Hx. subst. rewrite orbC eq_refl //. }
            destruct (y ∈ Y__sub) eqn:Hysub; cycle 1. { inverts Hy. }
            destruct (Fresh0 Y__super =P y); subst; inverts Hy.
            rewrite in_fset1 -(rwP eqP) in Hx. subst. rewrite Hysub //.
          - rewrite domm_set.
            rewrite /Tm /in_mem /= -!(rwP fsubsetP) in HtX |- *. intros x Hx.
            rewrite in_fsetU in_fset1.
            destruct (x =P s); subst; auto. apply (introF eqP) in n.
            apply HtX. rewrite in_fsetD in_fset1 Hx n //. }
        simpl.
        transitivity (⦇f[s,variable (Fresh0 Y__super)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) t); cycle 1.
        { apply substitution_preserves_α_congruence; auto.
          - rewrite -(rwP fsubsetP). intros x Hx.
            rewrite in_fsetU in_fset1.
            apply (rwP codomm_Tm_setP) in Hx as (u & Hx & Hu). apply (rwP codommP) in Hu as [y Hy].
            rewrite setmE in Hy.
            destruct (y =P s); subst.
            { inverts Hy. rewrite in_fset1 -(rwP eqP) in Hx. subst. rewrite eq_refl orbC //. }
            rewrite -(rwP fsubsetP) in HfY__sub.
            apply (rwP orP). left.
            apply HfY__sub, (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto.
          - rewrite -(rwP fsubsetP). intros x Hx.
            rewrite in_fsetU in_fset1.
            apply (rwP codomm_Tm_setP) in Hx as (u & Hx & Hu). apply (rwP codommP) in Hu as [y Hy].
            rewrite mapmE setmE in Hy. destruct (y =P s); subst.
            + inverts Hy. rewrite mapmE in Hx.
              assert (Fresh0 Y__sub ∈ domm R) as HY__sub. { rewrite -HR in_fsetU in_fset1 orbC eq_refl //. }
              apply (rwP dommP) in HY__sub as [y Hy].
              rewrite Hy /= in_fset1 -(rwP eqP) in Hx. subst.
              rewrite /R updateE eq_refl in Hy. inverts Hy. rewrite eq_refl orbC //.
            + destruct (getm f y) eqn:Hfy; inverts Hy.
              rewrite FV_lift_substitution // in Hx.
              * rewrite in_bigcup in Hx. apply (rwP hasP) in Hx as [].
                apply (rwP pimfsetP) in H as []. rewrite mapmE in H1.
                destruct (getm R x1) eqn:HRx1; inverts H1.
                rewrite /= in_fset1 -(rwP eqP) in H0. subst.
                rewrite /R updateE identityE in HRx1.
                destruct (x1 == Fresh0 Y__sub) eqn:Hx1. { inverts HRx1. rewrite eq_refl orbC //. }
                destruct (x1 ∈ Y__sub) eqn:Hx1Y__sub; cycle 1. { inverts HRx1. }
                destruct (Fresh0 Y__super =P x1); subst; inverts HRx1. rewrite Hx1Y__sub //.
              * rewrite -(rwP fsubsetP). intros z Hz.
                rewrite in_fsetU in_fset1.
                apply (rwP codomm_Tm_setP) in Hz as (u & Hz & Hu). apply (rwP codommP) in Hu as [z' Hu].
                rewrite mapmE in Hu.
                destruct (getm R z') eqn:HRz'; inverts Hu.
                rewrite in_fset1 -(rwP eqP) in Hz. subst.
                rewrite /R updateE identityE in HRz'.
                destruct (z' =P Fresh0 Y__sub); subst. { inverts HRz'. rewrite eq_refl orbC //. }
                destruct (z' ∈ Y__sub) eqn:Hz'Y__sub; cycle 1. { inverts HRz'. }
                destruct (Fresh0 Y__super =P z'); subst; inverts HRz'. rewrite Hz'Y__sub //.
              * rewrite domm_map /Tm /in_mem /= -(rwP fsubsetP). intros z Hz.
                apply (rwP dommP). rewrite updateE identityE.
                destruct (z =P Fresh0 Y__sub); subst; eauto.
                assert (z ∈ codomm_Tm_set f) as Hzf.
                { apply (rwP codomm_Tm_setP). exists t0. split; auto. apply (rwP codommP). eauto. }
                rewrite -!(rwP fsubsetP) in HfY__sub, HfY__super.
                apply HfY__sub in Hzf. rewrite Hzf.
                destruct (Fresh0 Y__super =P z); subst; eauto.
                apply HfY__super in Hzf. pose proof HFresh Y__super as H. rewrite Hzf // in H.
          - rewrite domm_map !domm_set //.
          - intros x Hx.
            rewrite mapmE !setmE.
            rewrite domm_set in_fsetU in_fset1 in Hx.
            destruct (x =P s); subst.
            + rewrite /= mapmE.
              assert (Fresh0 Y__sub ∈ domm R) as HY__sub. { rewrite -HR in_fsetU in_fset1 eq_refl orbC //. }
              apply (rwP dommP) in HY__sub as [u Hu]. rewrite Hu.
              rewrite /R updateE identityE eq_refl in Hu. inverts Hu.
              rewrite -(rwP getmP) identityE in_fsetU in_fset1 orbC eq_refl //.
            + apply (rwP dommP) in Hx as [u Hu]. rewrite Hu /=.
              assert (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u ≡_α u) as Hα.
              { transitivity (⦇η__(Y__sub ∪ {Fresh0 Y__super})⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u).
                { exists Y__sub. eapply substitution_preserves_α_congruence'; auto.
                  - rewrite /is_subset_of domm_η domm_identity codomm_identity domm_map -(rwP andP).
                    instantiate (1 := Y__sub).
                    split.
                    + rewrite -HR fsubsetU // fsubsetxx //.
                    + rewrite fsubsetU // fsubsetxx //.
                  - rewrite /is_subset_of domm_identity codomm_identity fsubsetU // fsubsetxx //.
                  - rewrite -(rwP fsubsetP). intros y Hy.
                    apply (rwP codomm_Tm_setP) in Hy as (v & Hv & Hy). apply (rwP codommP) in Hy as (z & Hz).
                    rewrite mapmE in Hz.
                    rewrite in_fsetU in_fset1.
                    destruct (getm R z) eqn:HRz; inverts Hz.
                    rewrite in_fset1 -(rwP eqP) in Hv. subst.
                    rewrite updateE identityE in HRz.
                    destruct (z == Fresh0 Y__sub) eqn:Hz. { inverts HRz. rewrite eq_refl orbC //. }
                    destruct (z ∈ Y__sub) eqn:HzY__sub; cycle 1. { inverts HRz. }
                    destruct (Fresh0 Y__super =P z); subst; inverts HRz. rewrite HzY__sub //.
                  - rewrite -(rwP fsubsetP). intros y Hy. rewrite codomm_Tm_set_η // in Hy.
                  - intros x' y' Hx'y.
                    rewrite /fmap_to_Prop identityE in Hx'y.
                    destruct (x' ∈ Y__sub) eqn:Hx'Y__sub; inverts Hx'y.
                    rewrite -(rwP fsubsetP) in HfY__sub.
                    assert (y' ∈ domm R) as Hy'R. { rewrite -HR in_fsetU Hx'Y__sub //. }
                    apply (rwP dommP) in Hy'R as [v Hv].
                    rewrite mapmE Hv ηE /= in_fsetU Hx'Y__sub -(rwP getmP) identityE.
                    rewrite /R updateE identityE Hx'Y__sub in Hv.
                    destruct (y' =P Fresh0 Y__sub); subst.
                    { inverts Hv. pose proof HFresh Y__sub as HY__sub. rewrite Hx'Y__sub // in HY__sub. }
                    destruct (Fresh0 Y__super =P y'); inverts Hv. rewrite Hx'Y__sub //.
                  - apply α_equivalent'_identity. rewrite /Tm /in_mem /= -(rwP fsubsetP). intros y Hy.
                    rewrite -(rwP fsubsetP) in HfY__sub.
                    apply HfY__sub, (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto. }
                apply monad_substitution1; auto.
                rewrite /Tm /in_mem /= -(rwP fsubsetP). intros y Hy.
                apply (rwP fsubsetP) in HfY__sub.
                rewrite in_fsetU -(rwP orP). left.
                apply HfY__sub, (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto. }
              symmetry in Hα.
              rewrite (@α_equivalent'_morph (1__(Y__sub ∪ {Fresh0 Y__super})) _ u (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u) Hα (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u) (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u)) //.
              * apply α_equivalent'_identity. rewrite /Tm /in_mem /= -(rwP fsubsetP). intros y Hy.
                rewrite FV_lift_substitution // in Hy.
                -- rewrite in_bigcup in Hy. apply (rwP hasP) in Hy as [t' Ht'].
                   apply (rwP pimfsetP) in Ht' as [y' Hy'].
                   rewrite in_fsetU in_fset1.
                   rewrite mapmE updateE identityE in H0.
                   destruct (y' =P Fresh0 Y__sub).
                   { inverts H0. subst. rewrite in_fset1 -(rwP eqP) in H. subst. rewrite eq_refl orbC //. }
                   destruct (y' ∈ Y__sub) eqn:HY__sub; cycle 1. { inverts H0. }
                   destruct (Fresh0 Y__super =P y'); inverts H0.
                   rewrite in_fset1 -(rwP eqP) in H. subst. rewrite HY__sub //.
                -- rewrite -(rwP fsubsetP). intros z Hz.
                   rewrite in_fsetU in_fset1.
                   apply (rwP codomm_Tm_setP) in Hz as (u' & Hz & Hu').
                   apply (rwP codommP) in Hu' as [v' Hv'].
                   rewrite mapmE updateE identityE in Hv'.
                   destruct (v' =P Fresh0 Y__sub).
                   { inverts Hv'. rewrite in_fset1 -(rwP eqP) in Hz. subst. rewrite eq_refl orbC //. }
                   destruct (v' ∈ Y__sub) eqn:Hv'Y__sub; cycle 1. { inverts Hv'. }
                   destruct (Fresh0 Y__super =P v'); inverts Hv'.
                   rewrite in_fset1 -(rwP eqP) in Hz. subst. rewrite Hv'Y__sub //.
                -- rewrite /Tm /in_mem /= domm_map -(rwP fsubsetP). intros z Hz.
                   apply (rwP dommP). exists z. rewrite updateE identityE.
                   assert (z ∈ codomm_Tm_set f) as Hfz.
                   { apply (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto. }
                   rewrite -!(rwP fsubsetP) in HfY__sub, HfY__super. apply HfY__sub in Hfz.
                   destruct (z =P Fresh0 Y__sub); subst.
                   ++ pose proof HFresh Y__sub as HY__sub. rewrite Hfz // in HY__sub.
                   ++ rewrite Hfz. destruct (Fresh0 Y__super =P z); subst; auto.
                      apply HfY__super in Hfz. pose proof HFresh Y__super as HY__super. rewrite Hfz // in HY__super.
              * reflexivity.
          - rewrite domm_set.
            rewrite /Tm /in_mem /= -!(rwP fsubsetP) in HtX |- *. intros x Hx.
            rewrite in_fsetU in_fset1. destruct (x =P s); subst; auto. apply (introF eqP) in n.
            apply HtX. rewrite in_fsetD in_fset1 Hx n //.
          - reflexivity. }
        symmetry.
        apply IHt; auto.
        - rewrite domm_set.
          rewrite /Tm /in_mem /= -!(rwP fsubsetP) in HtX |- *. intros x Hx.
          rewrite in_fsetU in_fset1. destruct (x =P s); subst; auto. apply (introF eqP) in n.
          apply HtX. rewrite in_fsetD in_fset1 Hx n //.
        - rewrite -(rwP fsubsetP). intros x Hx.
          rewrite in_fsetU in_fset1.
          apply (rwP codomm_Tm_setP) in Hx as (u & Hx & Hu). apply (rwP codommP) in Hu as [y Hy].
          rewrite setmE in Hy.
          destruct (y =P s); subst.
          { inverts Hy. rewrite in_fset1 -(rwP eqP) in Hx. subst. rewrite eq_refl orbC //. }
          rewrite -(rwP fsubsetP) in HfY__sub.
          apply (rwP orP). left.
          apply HfY__sub, (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto.
        - rewrite -(rwP fsubsetP). intros x Hx.
          rewrite !in_fsetU !in_fset1 -!(rwP orP) in Hx |- *.
          destruct Hx as [HX | Hx]; auto.
          rewrite -(rwP fsubsetP) in HfY__super. left. apply HfY__super. auto. }
      rewrite (@α_equivalent'_morph (R ᵒ) _ _ (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t)) H (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t)); cycle 1.
      { apply converse_closed_under_partial_bijection. auto. }
      { reflexivity. }
      apply lemma7; auto.
      + rewrite -(rwP fsubsetP). intros x Hx.
        apply (rwP codommP) in Hx as [v Hv].
        rewrite updateE identityE in Hv.
        rewrite in_fsetU in_fset1.
        destruct (v =P Fresh0 Y__sub); subst. { inverts Hv. rewrite eq_refl orbC //. }
        destruct (v ∈ Y__sub) eqn:HvY__sub; cycle 1. { inverts Hv. }
        destruct (Fresh0 Y__super =P v); subst; inverts Hv. rewrite HvY__sub //.
      + rewrite /Tm /in_mem /= -HR FV_lift_substitution // -(rwP fsubsetP); intros x Hx.
        * rewrite in_fsetU in_fset1.
           rewrite in_bigcup in Hx. apply (rwP hasP) in Hx as [y Hy].
           apply (rwP pimfsetP) in Hy as [u Hu].
           rewrite setmE in H1.
           destruct (u =P s); subst.
           -- inverts H1. rewrite in_fset1 -(rwP eqP) in H0. subst. rewrite eq_refl orbC //.
           -- assert (x ∈ codomm_Tm_set f) as Hfx.
             { apply (rwP codomm_Tm_setP). exists y. split; auto. apply (rwP codommP). eauto. }
             rewrite -(rwP fsubsetP) in HfY__sub. apply HfY__sub in Hfx. rewrite Hfx //.
        * apply (rwP codomm_Tm_setP) in Hx as (u & Hx & Hu). apply (rwP codommP) in Hu as [y Hy].
          rewrite setmE in Hy.
          rewrite in_fsetU in_fset1.
          destruct (y =P s); subst.
          -- inverts Hy. rewrite in_fset1 -(rwP eqP) in Hx. subst. rewrite eq_refl orbC //.
          -- assert (x ∈ codomm_Tm_set f) as Hfx.
             { apply (rwP codomm_Tm_setP). exists u. split; auto. apply (rwP codommP). eauto. }
             rewrite -(rwP fsubsetP) in HfY__sub. apply HfY__sub in Hfx. rewrite Hfx //.
        * rewrite /Tm /in_mem /= fsubDset -(rwP fsubsetP) in HtX. rewrite domm_set HtX //.
    - exists Y__super.
      rewrite /Tm /in_mem /= in HtX |- *.
      rewrite fsubUset // in HtX. apply (rwP andP) in HtX as [Ht1 Ht2].
      rewrite /= -(rwP andP). split.
      + rewrite (@α_equivalent'_morph (1__(Y__super)) _ _ (⦇f⦈ Fresh0 Y__super t1) _ _ (⦇f⦈ Fresh0 Y__super t1)) //.
        * apply α_equivalent'_identity, lift_substitution_type; auto. apply fsubset_trans with Y__sub; auto.
        * apply IHt1; auto.
        * reflexivity.
      + rewrite (@α_equivalent'_morph (1__(Y__super)) _ _ (⦇f⦈ Fresh0 Y__super t2) _ _ (⦇f⦈ Fresh0 Y__super t2)) //.
        * apply α_equivalent'_identity, lift_substitution_type; auto. apply fsubset_trans with Y__sub; auto.
        * apply IHt2; auto.
        * reflexivity.
    - reflexivity.
  Qed.

  Lemma lift_substitution_independent_of_codomm :
    forall Fresh Y1 Y2 f t,
      let X := domm f in
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y1 ->
      codomm_Tm_set f ⊆ Y2 ->
      t ∈ Tm X ->
      ⦇f⦈ Fresh Y1 t ≡_α ⦇f⦈ Fresh Y2 t.
  Proof.
    introv HFresh HfY1 HfY2 Htx.
    transitivity (⦇f⦈ Fresh0 (codomm_Tm_set f) t).
    - symmetry. apply lift_substitution_independent_of_codomm_subset; auto. rewrite fsubsetxx //.
    - apply lift_substitution_independent_of_codomm_subset; auto. rewrite fsubsetxx //.
  Qed.

  Lemma application_preserves_α_equivalent :
    forall t t' u u',
      t ≡_α t' ->
      u ≡_α u' ->
      application t u ≡_α application t' u'.
  Proof.
    introv [X Ht] [Y Hu].
    exists (X ∪ Y).
    rewrite /= -(rwP andP). split.
    - apply α_equivalent'_observably_equal with (R := 1__X); auto. intros k v Hkt Hkv.
      rewrite /fmap_to_Prop !identityE in_fsetU in Hkv |- *.
      destruct (k ∈ X) eqn:Hkx; inverts Hkv; auto.
    - apply α_equivalent'_observably_equal with (R := 1__Y); auto. intros k v Hkt Hkv.
      rewrite /fmap_to_Prop !identityE in_fsetU in Hkv |- *.
      destruct (k ∈ Y) eqn:Hky; inverts Hkv; rewrite orbC //.
  Qed.

  Lemma lift_substitution_adapter' :
    forall Fresh Y f t,
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y ->
      FV t ⊆ domm f ->
      ⦇f⦈ Fresh (codomm_Tm_set f) t ≡_α A.lift_substitution' f Fresh t.
  Proof.
    introv HFresh HfY HtX.
    rewrite -(rwP fsubsetP) in HtX.
    gen f Y. induction t; intros; simpl; f_equal; eauto.
    - apply abstraction_preserves_α_equivalent.
      etransitivity; cycle 1.
      { eapply IHt, fsubsetxx. intros x Hx.
        rewrite domm_set in_fsetU in_fset1.
        destruct (x =P s); subst; auto. apply (introF eqP) in n.
        apply HtX. rewrite in_fsetD in_fset1 Hx n //. }
      apply lift_substitution_independent_of_codomm; auto.
      + apply codomm_Tm_set_update_substitution, fsubsetxx.
      + apply fsubsetxx.
      + rewrite /Tm /in_mem /= domm_set -(rwP fsubsetP). intros x Hx.
        rewrite in_fsetU in_fset1.
        destruct (x =P s); subst; auto. apply (introF eqP) in n.
        apply HtX. rewrite in_fsetD in_fset1 Hx n //.
    - apply application_preserves_α_equivalent.
      + simpl in HtX. eapply IHt1; eauto. intros x Hx.
        apply HtX. rewrite in_fsetU Hx //.
      + simpl in HtX. eapply IHt2; eauto. intros x Hx.
        apply HtX. rewrite in_fsetU Hx orbC //.
    - reflexivity.
  Qed.

  Lemma lift_substitution_adapter :
    forall Fresh Y f t,
      Fresh_correct Fresh ->
      codomm_Tm_set f ⊆ Y ->
      FV t ⊆ domm f ->
      ⦇f⦈ Fresh Y t ≡_α A.lift_substitution' f Fresh t.
  Proof.
    introv HFresh HfY Ht.
    transitivity (⦇f⦈ Fresh0 (codomm_Tm_set f) t).
    - apply lift_substitution_independent_of_codomm; auto. apply fsubsetxx.
    - eapply lift_substitution_adapter'; eauto.
  Qed.

  Lemma lift_substitution_independent_of_Fresh :
    forall Fresh1 Fresh2 Y f t,
      Fresh_correct Fresh1 ->
      Fresh_correct Fresh2 ->
      codomm_Tm_set f ⊆ Y ->
      FV t ⊆ domm f ->
      ⦇f⦈ Fresh1 Y t ≡_α ⦇f⦈ Fresh2 Y t.
  Proof.
    introv HFresh1 HFresh2 HfY Htf.
    transitivity (A.lift_substitution' f Fresh1 t);
    rewrite lift_substitution_adapter //;
    apply alpha_equivalent_adapter, A.lift_substitution'_independent_of_Fresh; auto.
  Qed.
End AlphaPaperFacts.
