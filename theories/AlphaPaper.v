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
From HB Require Import structures.
From mathcomp Require Import bigop choice eqtype seq ssrbool ssrfun ssrnat.
From deriving Require Import deriving.
From extructures Require Import fmap fset ord.
From Equations Require Import Equations Signature.
From AlphaPearl Require Import Alpha Util.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".
Unset Printing Implicit Defensive.

#[local] Obligation Tactic := program_simpl.

#[local] Open Scope fset_scope.

Module AlphaPaperFacts (Import M : Alpha).
  Implicit Type Fresh : {fset 𝒱} -> 𝒱.

  #[local] Notation "X '∪' '{' x '}'" :=
    (X :|: fset1 x)
      (at level 52, format "X  '∪'  '{' x '}'")
    : fset_scope.

  (** We need to define a total order on terms in order to use them as elements of finite sets. *)
  Definition term_indDef := [indDef for term_rect].
  Canonical term_indType := IndType term term_indDef.
  Definition term_hasDecEq := [derive hasDecEq for term].
  HB.instance Definition _ := term_hasDecEq.
  Definition term_hasChoice := [derive hasChoice for term].
  HB.instance Definition _ := term_hasChoice.
  Definition term_hasOrd := [derive hasOrd for term].
  HB.instance Definition _ := term_hasOrd.

  #[local] Open Scope term_scope.

  Implicit Types (W X Y Z : {fset 𝒱}) (t u : term) (v w x y z : 𝒱) (R S : {fmap 𝒱 → 𝒱}).

  #[local] Notation FV := free_variables.

  Definition Tm X t : bool := FV t ⊆ X.

  (* See https://stackoverflow.com/a/51568428/2391244. *)
  Ltac by_cases_hook0 := idtac.
  Ltac by_cases_hook := by_cases_hook0.

  Ltac by_cases_loop depth :=
    match number_to_nat depth with
    | 0 => idtac "by_cases: Recursion limit reached!"
    | S ?depth =>
        try (progress (repeat intro; subst; simpl in *; auto;
                     by_cases_hook;
                     try discriminate; try contradiction);
             by_cases_loop depth)
    end.

  Ltac by_cases' depth :=
    by_cases_loop ltac:(depth); eauto.

  Ltac by_cases := by_cases' 100.

  Ltac by_cases_hook1 :=
    lazymatch goal with
    | H : exists _, _ |- _ => destruct H
    | H1 : is_true ?b, H2 : is_true (negb ?b) |- _ => rewrite [b]H1 // in H2
    | H1 : is_true ?b, H2 : ?b = false |- _ => rewrite [b]H1 // in H2
    | H1 : ?x = Some ?y, H2 : ?x = None |- _ => rewrite [x]H1 // in H2
    | H : ex2 ?H1 ?H2 |- _ => destruct H
    | H : is_true (has ?f ?s) |- _ => apply (rwP hasP) in H as []
    | H : has ?f ?s = false |- _ => apply negbT, (rwP hasPn) in H
    | H : ?b = true |- _ => fold (is_true b) in H
    | H : Some ?x = Some ?y |- _ => inverts H
    | H : Some ?x = getm ?m ?y |- _ => symmetry in H
    | H : None = getm ?m ?x |- _ => symmetry in H
    | H : ?H1 <-> ?H2 |- _ => unfold iff in H
    | H : ?H1 /\ ?H2 |- _ => destruct H
    | H : ?H1 \/ ?H2 |- _ => destruct H
    | H : is_true (?b1 && ?b2) |- _ => apply (rwP andP) in H
    | H : ?b1 && ?b2 = false |- _ => apply Bool.andb_false_iff in H
    | H : is_true (?b1 || ?b2) |- _ => apply (rwP orP) in H
    | H : ?b1 || ?b2 = false |- _ => apply Bool.orb_false_iff in H
    | H : is_true (?x ∈ domm ?f) |- _ => apply (rwP dommP) in H as []
    | H : is_true (?x ∉ domm ?f) |- _ => apply (rwP dommPn) in H
    | H : is_true (?x ∉ FSet.fsval (domm ?f)) |- _ => apply (rwP dommPn) in H
    | H : is_true (?x ∈ codomm ?f) |- _ => apply (rwP codommP) in H as []
    | H : is_true (?x ∉ codomm ?f) |- _ => rewrite -(rwP codommPn) in H
    | H : context [ ?X ∪ ?Y ⊆ ?Z ] |- _ => rewrite [X ∪ Y ⊆ Z]fsubUset in H
    | H : {subset ?X ∪ ?Y <= ?Z} |- _ => rewrite (rwP fsubsetP) fsubUset in H
    | H : context [ ?X ∪ {?x} ] |- _ => rewrite [X ∪ {x}]fsetUC in H
    | H : context [ fset1 ?x ⊆ ?X ] |- _ => rewrite [fset1 x ⊆ X]fsub1set in H
    | H : is_true (?x ∈ FSet.fsval (pimfset ?f [:: ?s])) |- _ => rewrite -(rwP (@pimfsetP _ _ _ (fset1 s) _)) in H
    | H : is_true (?x ∈ FSet.fsval (pimfset ?f ?s)) |- _ => rewrite -(rwP pimfsetP) in H
    | H : context [ _ ∈ ⋃_(_ ∈ _) _ ] |- _ => rewrite in_bigcup in H
    | H : is_true (_ ∉ ⋃_(_ ∈ _) _) |- _ => apply negbTE in H
    | H : is_true (injectivem ?m) |- _ => rewrite -(rwP injectivemP) in H
    | H : is_true (?X ⊆ ?Y) |- _ => rewrite -(rwP fsubsetP) in H
    | H : context [ ?x ∈ ?X ∪ ?Y ] |- _ => rewrite [x ∈ X ∪ Y]in_fsetU in H
    | H : context [ ?x ∈ ?X ∩ ?Y ] |- _ => rewrite [x ∈ X ∩ Y]in_fsetI in H
    | H : context [ ?x ∈ ?X :\: ?Y ] |- _ => rewrite [x ∈ X :\: Y]in_fsetD in H
    | H : context [ ?x ∈ fset1 ?y ] |- _ => rewrite [x ∈ fset1 y]in_fset1 in H
    | H : context [ ?x ∈ Tm ?y ] |- _ => rewrite /Tm /in_mem /= in H
    | H : context [ ?x == ?x ] |- _ => rewrite [x == x]eq_refl in H
    | H : context [ ?x == ?y ] |- _ => destruct (x =P y)
    | H : context [ ?b || true ] |- _ => rewrite [b || true]orbT in H
    | H : context [ ?b || false ] |- _ => rewrite [b || false]orbF in H
    | H : context [ ?b && true ] |- _ => rewrite [b && true]andbT in H
    | H : context [ ?b && false ] |- _ => rewrite [b && false]andbF in H
    | H : context [ getm (setm ?m ?x ?y) ?z ] |- _ => rewrite [getm (setm m x y) z]setmE in H
    | H : context [ getm (mapm ?f ?m) ?x ] |- _ => rewrite [getm (mapm f m) x]mapmE in H
    | H : context [ getm (remm ?m ?x) ?y ] |- _ => rewrite [getm (remm m x) y]remmE in H
    | H : context [ getm (mkfmapf ?f ?m) ?x ] |- _ => rewrite [getm (mkfmapf f m) x]mkfmapfE in H
    | H : context [ getm (mkfmapfp ?f ?m) ?x ] |- _ => rewrite [getm (mkfmapfp f m) x]mkfmapfpE in H
    | H : context [ domm (setm ?m ?x ?y) ] |- _ => rewrite [domm (setm m x y)]domm_set in H
    | H : context [ domm (mapm ?f ?m) ] |- _ => rewrite [domm (mapm f m)]domm_map in H
    | H : context [ domm (mkfmapf ?f ?m) ] |- _ => rewrite [domm (mkfmapf f m)]domm_mkfmapf in H
    | H : context [ fmap_to_Prop ] |- _ => unfold fmap_to_Prop in H
    | H : context [ omap ?f (getm ?m ?x) = ?y ] |- _ => destruct (getm m x) eqn:?
    | H : context [ ?y = omap ?f (getm ?m ?x) ] |- _ => destruct (getm m x) eqn:?
    | X : {fset ?T}, H : context [ fset ?X ] |- _ => rewrite [fset X]fsvalK in H
    | H : (?x ∈ ?X) = false |- _ => apply negbT in H
    | x := _ |- _ => subst x
    |   H1 : ?f ?x = ?y
      , H2 : forall x, is_true (?f x != ?y)
      |- _
      => specialize (H2 x)
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
      , H2 : getm (invm ?f) _ = Some _
      |- _
      => apply getm_inv in H2
    |   H1 : {in domm ?f, injective (getm ?f)}
      , H2 : context [ invm (invm ?f) ]
      |- _
      => rewrite invmK in H2
    |   H : context [ match ?b with
                      | true => _
                      | false => _
                      end ]
        |- _
        => let H' := fresh in
          destruct b eqn:H'; rewrite ?H' in H
    | H : is_true ((?x, ?y) ∈ ?R) |- _ =>
        match type of R with
        | {fmap _ → _} => apply (rwP getmP) in H
        | {fmap _ -> _} => apply (rwP getmP) in H
        end
    | |- ?x = true => change (is_true x)
    | |- Some ?x = Some ?y => f_equal
    | |- ?H1 <-> ?H2 => unfold iff
    | |- is_true false \/ ?b => right
    | |- ?b \/ is_true false => left
    | |- ?b1 /\ ?b2 => split
    | |- is_true (?b1 && ?b2) => rewrite -(rwP andP)
    | |- is_true (?b1 || ?b2) => rewrite -(rwP orP)
    | |- ?b1 && ?b2 = false => apply Bool.andb_false_iff
    | |- ?b1 || ?b2 = false => apply Bool.orb_false_iff
    | |- is_true (?X ⊆ ?Y) => rewrite -(rwP fsubsetP)
    | |- is_true (injectivem ?f) => rewrite -(rwP injectivemP)
    | |- is_true (?x ∈ FSet.fsval (pimfset ?f [:: ?s])) => rewrite -(rwP (@pimfsetP _ _ _ (fset1 s) _))
    | |- is_true (?x ∈ FSet.fsval (pimfset ?f ?s)) => rewrite -(rwP pimfsetP)
    | |- context [ _ ∈ ⋃_(_ ∈ _) _ ] => rewrite in_bigcup
    | |- is_true (has ?f ?s) => apply (rwP hasP)
    | |- context [ ?x ∈ ?X ∪ ?Y ] => rewrite [x ∈ X ∪ Y]in_fsetU
    | |- context [ ?x ∈ ?X ∩ ?Y ] => rewrite [x ∈ X ∩ Y]in_fsetI
    | |- context [ ?x ∈ fset1 ?y ] => rewrite [x ∈ fset1 y]in_fset1
    | |- context [ ?x ∈ ?X :\: ?Y ] => rewrite [x ∈ X :\: Y]in_fsetD
    | |- context [ ?X ∪ {?x} ] => rewrite [X ∪ {x}]fsetUC
    | |- context [ ?x ∈ Tm ?X ] => rewrite /Tm /in_mem /=
    | |- context [ ?x == ?x ] => rewrite [x == x]eq_refl
    | |- context [ ?x == ?y ] => destruct (x =P y)
    | |- context [ fmap_to_Prop ] => unfold fmap_to_Prop
    | |- context [ ?b || true ] => rewrite [b || true]orbT
    | |- context [ ?b || false ] => rewrite [b || false]orbF
    | |- context [ ?b && true ] => rewrite [b && true]andbT
    | |- context [ ?b && false ] => rewrite [b && false]andbF
    | |- context [ getm (setm ?m ?x ?y) ?z ]  => rewrite [getm (setm m x y) z]setmE
    | |- context [ getm (mapm ?f ?m) ?x ] => rewrite [getm (mapm f m) x]mapmE
    | |- context [ getm (remm ?m ?x) ?y ] => rewrite [getm (remm m x) y]remmE
    | |- context [ getm (mkfmapf ?f ?m) ?x ] => rewrite [getm (mkfmapf f m) x]mkfmapfE
    | |- context [ getm (mkfmapfp ?f ?m) ?x ] => rewrite [getm (mkfmapfp f m) x]mkfmapfpE
    | |- context [ domm (setm ?m ?x ?y) ] => rewrite [domm (setm m x y)]domm_set
    | |- context [ domm (mapm ?f ?m) ] => rewrite [domm (mapm f m)]domm_map
    | |- context [ domm (mkfmapf ?f ?m) ] => rewrite [domm (mkfmapf f m)]domm_mkfmapf
    | |- is_true (?x ∈ domm ?f) => apply (rwP dommP)
    | |- is_true (?x ∉ domm ?f) => apply (rwP dommPn)
    | |- is_true (?x ∈ codomm ?f) => rewrite -(rwP codommP)
    | |- is_true (?x ∉ codomm ?f) => rewrite -(rwP codommPn)
    | X : {fset ?T} |- context [ fset ?X ] => rewrite [fset X]fsvalK
    | |- omap ?f (getm ?m ?x) = _  => destruct (getm m x) eqn:?
    | |- ?y = omap ?f (getm ?m ?x) => destruct (getm m x) eqn:?
    |   H1 : getm ?f ?x = ?y
      |- context [ getm ?f ?x ]
      => rewrite H1
    | |- context [ match getm ?f ?x with
                  | Some _ => _
                  | None => _
                  end ]
      => destruct (getm f x) eqn:?
    |   H : {in domm ?f, injective (getm ?f)}
      |- context [ invm (invm ?f) ]
      => rewrite invmK
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
    | H : getm ?R ?x = ?y |- context [ getm ?R ?x ] => rewrite H
    | H : getm ?f ?x = ?y |- context [ getm ?f ?x ] => rewrite H
    | H : is_true (?x ∈ ?X) |- context [ ?x ∈ ?X ] => rewrite H
    |   H1 : is_true (?x ∈ FV ?t)
      , H2 : getm ?f ?y = Some ?t
      |- exists t, is_true (?x ∈ FV t) /\ is_true (t ∈ codomm ?f)
      => exists t
    |   H1 : {in domm ?f, injective (getm ?f)}
      , H2 : getm ?f ?x = ?z
      , H3 : getm ?f ?y = ?z
      |- ?x = ?y
      => apply H1
    | |- ?X = ?Y =>
        match type of X with
        | {fmap _ → _} => apply eq_fmap; intro
        | {fmap _ -> _} => apply eq_fmap; intro
        | {fset _} => apply eq_fset; intro; apply Bool.eq_iff_eq_true
        end
    end || by_cases_hook0.
  Ltac by_cases_hook ::= by_cases_hook1.

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

  Ltac by_cases_hook2 :=
    lazymatch goal with
    | H : context [ ?R ⊆ ?X × ?Y ] |- _ => unfold is_subset_of in H
    | |- context [ ?R ⊆ ?X × ?Y ] => unfold is_subset_of
    end || by_cases_hook1.
  Ltac by_cases_hook ::= by_cases_hook2.

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

  Ltac by_cases_hook3 :=
    lazymatch goal with
    | H : context [ getm (?R⦅?x,?y⦆) ?z ] |- _ => rewrite [getm (R⦅x,y⦆) z]updateE in H
    | |- context [ getm (?R⦅?x,?y⦆) ?z ] => rewrite [getm (R⦅x,y⦆) z]updateE
    end || by_cases_hook2.
  Ltac by_cases_hook ::= by_cases_hook3.

  (** Page 3: "It is easy to see that R(x,y) is a partial bijection." *)
  Lemma partial_bijection_update :
    forall R x y,
      partial_bijection R ->
      partial_bijection R⦅x,y⦆.
  Proof. by_cases.
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
      + apply H. by_cases.
      + apply H1. by_cases.
    - apply IHt with (X := X ∪ {s}) (Y := Y ∪ {s0}) in H0 as [Httype Hutype]; by_cases.
      + assert (x ∈ s0 |: Y); by_cases.
      + apply H. by_cases.
      + apply H1. by_cases.
    - apply IHt1 with (X := X) (Y := Y) in H; by_cases.
    - apply IHt2 with (X := X) (Y := Y) in H0; by_cases.
    - apply IHt1 with (X := X) (Y := Y) in H; by_cases.
    - apply IHt2 with (X := X) (Y := Y) in H0; by_cases.
    - apply H. by_cases.
    - apply H1. by_cases.
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

  Ltac by_cases_hook4 :=
    lazymatch goal with
    | H : context [ getm (1__?X) ?x ] |- _ => rewrite ?[getm (1__X) x]mapmE [getm (1__X) x]identityE in H
    | |- context [ getm (1__?X) ?x ] => rewrite ?[getm (1__X) x]mapmE [getm (1__X) x]identityE
    | H : context [ domm (1__?X) ] |- _ => rewrite ?[domm (1__X)]domm_map [domm (1__X)]domm_identity in H
    | |- context [ domm (1__?X) ] => rewrite ?[domm (1__X)]domm_map [domm (1__X)]domm_identity
    | H : context [ codomm (1__?X) ] |- _ => rewrite ?[codomm (1__X)]codomm_identity in H
    | |- context [ codomm (1__?X) ] => rewrite ?[codomm (1__X)]codomm_identity
    end || by_cases_hook3.
  Ltac by_cases_hook ::= by_cases_hook4.

  (** Page 3: "1X ... ⊆ X × X." *)
  Lemma identity_type : forall X, (1__X : {fmap 𝒱 → 𝒱}) ⊆ X × X.
  Proof. by_cases. Qed.

  (** Page 3: "1X... obviously is a partial bijection." *)
  Lemma partial_bijection_identity : forall X, partial_bijection (1__X : {fmap 𝒱 → 𝒱}).
  Proof. by_cases. Qed.

  #[local] Hint Resolve partial_bijection_identity : core.

  (** Page 3: "Given R ⊆ X × Y and S ⊆ Y × Z we write Rᵒ...." *)
  #[local] Notation "R 'ᵒ'" := (invm R) (at level 40).

  (** Page 3: "Both operations are closed under partial bijections." *)
  Lemma converse_closed_under_partial_bijection :
    forall R,
      partial_bijection R ->
      partial_bijection (R ᵒ).
  Proof. by_cases. Qed.

  #[local] Hint Resolve converse_closed_under_partial_bijection : core.

  Lemma codomm_converse :
    forall R,
      partial_bijection R ->
      codomm (R ᵒ) = domm R.
  Proof.
    by_cases. exists x0. apply getm_inv. rewrite invmK //.
  Qed.

  (** Page 3: "Rᵒ ... ⊆ Y × X." *)
  Lemma converse_type :
    forall R X Y,
      R ⊆ X × Y ->
      R ᵒ ⊆ Y × X.
  Proof.
    by_cases. apply getm_inv in H1. apply H. by_cases.
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
    by_cases.
    - apply getm_inv. rewrite invmK; by_cases.
    - apply invm_None; by_cases.
  Qed.

  Ltac by_cases_hook5 :=
    lazymatch goal with
    | H : context [ getm (?X;;?Y) ?x ] |- _ => rewrite [getm (X;;Y) x]composeE in H
    | |- context [ getm (?X;;?Y) ?x ] => rewrite [getm (X;;Y) x]composeE
    | H : context [ (1__?X)ᵒ ] |- _ => rewrite [(1__X)ᵒ]converse_identity in H
    | |- context [ (1__?X)ᵒ ] => rewrite [(1__X)ᵒ]converse_identity
    end || by_cases_hook4.
  Ltac by_cases_hook ::= by_cases_hook5.

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
    by_cases. apply H; by_cases.
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
    by_cases;
    (apply getm_inv; rewrite invmK) || apply invm_None; by_cases.
    - rewrite -H0 in Heqo. apply H in Heqo; by_cases.
    - apply invm_None in Heqo; by_cases.
  Qed.

  (** Page 3: Lemma 1.3. *)
  Lemma update_compose :
    forall R S x y z a b,
      (R⦅x,y⦆;;S⦅y,z⦆) a b ->
      ((R;;S)⦅x,z⦆) a b.
  Proof.
    introv HR'S'.
    cut ((a = x /\ z = b) \/ (x <> a /\ z <> b /\ (R;;S) a b)). { by_cases. }
    cut (exists c, (a = x /\ y = c /\ z = b) \/ (x <> a /\ y <> c /\ z <> b /\ R a c /\ S c b)). { by_cases. }
    by_cases. exists s. right. by_cases.
  Qed.

  Ltac by_cases_hook6 :=
    lazymatch goal with
    | H : context [ (1__?X)⦅?x,?x⦆ ] |- _ => rewrite [(1__X)⦅x,x⦆]update_identity in H
    | |- context [ (1__?X)⦅?x,?x⦆ ] => rewrite [(1__X)⦅x,x⦆]update_identity
    | H : context [ (?R⦅?x,?y⦆)ᵒ ] |- _ => rewrite [(R⦅x,y⦆)ᵒ]update_converse in H
    | |- context [ (?R⦅?x,?y⦆)ᵒ ] => rewrite [(R⦅x,y⦆)ᵒ]update_converse
    end || by_cases_hook5.
  Ltac by_cases_hook ::= by_cases_hook6.

  Lemma α_equivalent'_observably_equal :
    forall R S t u,
      (forall x y, x ∈ FV t -> R x y -> S x y) ->
      t ≡_α^R u ->
      t ≡_α^S u.
  Proof.
    introv HReqvS Htαu.
    gen R S u. induction t; introv HReqvS Htαu;
    destruct u; inverts Htαu; by_cases.
    - apply IHt with (R := R⦅s,s0⦆); by_cases; apply HReqvS in H2; by_cases.
    - apply IHt1 with (R := R); by_cases. apply HReqvS; by_cases.
    - apply IHt2 with (R := R); by_cases. apply HReqvS; by_cases.
    - apply HReqvS; by_cases.
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
    gen X. induction t; by_cases;
    (apply IHt || apply IHt1 || apply IHt2); by_cases; apply HtX; by_cases.
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
    destruct u; inverts Hα as Hα; by_cases.
    - apply IHt in Hα; by_cases.
    - apply IHt1; by_cases.
    - apply IHt2; by_cases.
    - apply getm_inv. rewrite invmK; by_cases.
  Qed.

  Proposition α_equivalent'_converse' :
    forall R t u,
      partial_bijection R ->
      t ≡_α^R u = u ≡_α^(R ᵒ) t.
  Proof.
    introv HRinj.
    apply Bool.eq_iff_eq_true; split; introv Hα.
    - apply α_equivalent'_converse; auto.
    - apply α_equivalent'_converse in Hα; by_cases.
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
    destruct u, v; inverts Htαu as Htαu; inverts Huαv as Huαv;
    by_cases.
    apply IHt with (S := S⦅s0,s1⦆) (v := v) in Htαu; by_cases.
    apply α_equivalent'_observably_equal with (S := (R;;S)⦅s,s1⦆) in Htαu; by_cases.
  Qed.

  Lemma compose_identity :
    forall X Y,
      (1__X);;(1__Y) = 1__(X ∩ Y).
  Proof. by_cases. Qed.

  (** Page 4: "≡α is... reflexive." *)
  Corollary α_equivalent_reflexive : forall t, t ≡_α t.
  Proof.
    introv. exists (FV t). apply α_equivalent'_identity. by_cases.
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
    - exists X. by_cases.
    - by_cases.
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
    rewrite /= /codomm_Tm_set in Hxℛf; by_cases.
    cut (is_true false); auto. specialize (Hxℛf x0). rewrite H in Hxℛf. apply Hxℛf. by_cases.
    rewrite -(rwP codommP). by_cases.
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

  Ltac by_cases_hook7 :=
    lazymatch goal with
    | H : is_true (?x ∈ codomm_Tm_set ?f) |- _ => apply (rwP codomm_Tm_setP) in H as (? & ? & ?)
    | |- is_true (?x ∈ codomm_Tm_set ?f) => rewrite -(rwP codomm_Tm_setP)
    | H : is_true (?x ∉ codomm_Tm_set ?f) |- _ => apply (rwP codomm_Tm_setPn) in H
    | |- is_true (?x ∉ codomm_Tm_set ?f) => apply (rwP codomm_Tm_setPn)
    | H : (?x ∈ codomm_Tm_set ?f) = false |- _ => apply negbT in H
    | |- (?x ∈ codomm_Tm_set ?f) = false => apply negbT
    end || by_cases_hook6.
  Ltac by_cases_hook ::= by_cases_hook7.

  (** Page 4: "Given a substitution f and x ∈ 𝒱, t ∈ Tm(Y) we define the update...." *)
  #[local] Notation "f '[' x ',' t ']'" :=
    (setm f x t)
      (at level 10, x at next level, t at next level, format "f [ x ',' t ]") :
      substitution_scope.

  (** Page 4: "f[[x,t]] ∈ X ∪ {x} ⟶ Y." *)
  Lemma update_substitution_type :
    forall Y f x t,
      let X := domm f in
      codomm_Tm_set f ⊆ Y ->
      t ∈ Tm Y ->
      domm (f[x,t]) = (X ∪ {x}) /\ codomm_Tm_set (f[x,t]) ⊆ Y.
  Proof. by_cases. apply H. by_cases. Qed.

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
    apply α_equivalent'_observably_equal with (R := R); by_cases.
    - assert (x ∈ X); by_cases. apply H1. by_cases.
    - assert (x0 ∈ X); assert (y0 ∈ Y); by_cases; apply H2; by_cases.
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
      apply HRtype in HRx as [Hfx Hgy]. by_cases. }
    { rewrite /= -(rwP andP). auto. }
    assert (abstraction x t ≡_α^R abstraction y u) as H.
    { apply (rwP α_equivalent'P). auto. }
    set (z := Fresh0 Y). set (z' := Fresh0 Y').
    apply IHHα.
    - by_cases.
    - by_cases; apply (rwP dommP).
      + apply H2. by_cases.
      + apply H3. by_cases.
    - by_cases.
      + apply H0. by_cases.
      + apply H1. by_cases.
    - by_cases.
    - apply lemma5 with Y Y'; by_cases.
    - by_cases. apply HfY. by_cases.
    - by_cases. apply HgY'. by_cases.
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
    apply substitution_preserves_α_congruence' with (R := 1__X) (S := 1__Y); by_cases.
    - apply (rwP dommP). rewrite HX. by_cases.
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
      rewrite /= -mapm_setm -update_converse -/z //.
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
    - by_cases. apply getm_inv. by_cases.
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
    by_cases. exists (variable x). by_cases. exists x. by_cases.
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
    - assert (y0 ∈ codomm R : Prop) by by_cases. apply H2 in H3. by_cases.
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
    exists X. replace (1__X) with ((1__X)ᵒ : {fmap 𝒱 → 𝒱}); cycle 1.
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
      - cut (x0 ∈ y |: (x |: X) : Prop); by_cases. }
    symmetry. etransitivity.
    { applys_eq (@monad_substitution3 Fresh0 X ((1__X)[x,u[y⟵v]Fresh0,X]) ((1__(X ∪ {x}))[y,v]) t); by_cases.
      rewrite FV_lift_substitution in H; by_cases. }
    apply substitution_preserves_α_congruence; by_cases.
    - rewrite FV_lift_substitution in H; by_cases.
      + rewrite FV_lift_substitution in H0; by_cases.
      + rewrite FV_lift_substitution in H; by_cases.
    - rewrite FV_lift_substitution in H; by_cases.
    - rewrite FV_lift_substitution in H; by_cases.
    - pose proof (substitution_law1 X v (u[y⟵v]Fresh0,X) x HFresh) as [Y Hα]; by_cases.
      { rewrite FV_lift_substitution in H; by_cases. }
      apply α_equivalent'_observably_equal with (R := 1__Y); by_cases.
      rewrite FV_lift_substitution in H; by_cases.
      + rewrite FV_lift_substitution in H0; by_cases. assert (y0 ∈ X); by_cases.
      + rewrite FV_lift_substitution in H; by_cases.
    - apply α_equivalent'_identity. by_cases.
      rewrite FV_lift_substitution in H; by_cases.
    - reflexivity.
  Qed.

  (** Page 7: "A monad gives rise to its Kleisli-category...." *)

  (** TODO Explicitly formalize the resulting Kliesli-category? *)

  Implicit Types (c d i j m n : nat) (ϕ ψ : {fmap 𝒱 → nat}).

  Definition nat_to_pred n i : bool := i < n.

  (** Page 7: "Here we identify n ∈ Nat with the set {i ∈ Nat | i < n}." *)
  Canonical nat_predType := PredType nat_to_pred.

  Lemma nat_to_pred_S :
    forall i n,
      i ∈ n <-> S i ∈ S n.
  Proof. by_cases. Qed.

  Inductive de_Bruijn_term : Type :=
  | de_Bruijn_abstraction : de_Bruijn_term -> de_Bruijn_term
  | de_Bruijn_application : de_Bruijn_term -> de_Bruijn_term -> de_Bruijn_term
  | de_Bruijn_variable : nat -> de_Bruijn_term.

  Definition de_Bruijn_term_indDef := [indDef for de_Bruijn_term_rect].
  Canonical de_Bruijn_term_indType := IndType de_Bruijn_term de_Bruijn_term_indDef.
  Definition de_Bruijn_term_hasDecEq := [derive hasDecEq for de_Bruijn_term].
  HB.instance Definition _ := de_Bruijn_term_hasDecEq.
  Definition de_Bruijn_term_hasChoice := [derive hasChoice for de_Bruijn_term].
  HB.instance Definition _ := de_Bruijn_term_hasChoice.
  Definition de_Bruijn_term_hasOrd := [derive hasOrd for de_Bruijn_term].
  HB.instance Definition _ := de_Bruijn_term_hasOrd.

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

  Lemma de_Bruijn_TmP : forall {n dBt}, reflect (in_de_Bruijn_Tm n dBt) (dBt ∈ Tm^db n).
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

  Lemma update_ϕE :
    forall ϕ x y,
      getm (ϕ^+x) y =
        if x == y
        then Some 0
        else omap S (getm ϕ y).
  Proof. unfold update_ϕ. by_cases. Qed.

  Ltac by_cases_hook8 :=
    lazymatch goal with
    | H : context [ getm (update_ϕ ?m ?x) ?y] |- _ => rewrite [getm (update_ϕ m x) y]update_ϕE in H
    | |- context [ getm (update_ϕ ?m ?x) ?y] => rewrite [getm (update_ϕ m x) y]update_ϕE
    end || by_cases_hook7.
  Ltac by_cases_hook ::= by_cases_hook8.

  Definition codomm_𝐍 {A : ordType} (ϕ : {fmap A → nat}) : nat :=
    S (\max_(i <- codomm ϕ) i).

  (* TODO Better name than "index"? *)
  Fixpoint de_Bruijn_index (dBt : de_Bruijn_term) : nat :=
    match dBt with
    | de_Bruijn_variable x          => S x
    | de_Bruijn_application dBt dBu => max (de_Bruijn_index dBt) (de_Bruijn_index dBu)
    | de_Bruijn_abstraction dBt     => (de_Bruijn_index dBt).-1
    end.

  Lemma de_Bruijn_index_sufficient :
    forall dBt,
      dBt ∈ Tm^db (de_Bruijn_index dBt).
  Proof.
    induction dBt; repeat rewrite /in_mem /=; by_cases.
    - apply de_Bruijn_Tm_subset with (de_Bruijn_index dBt); by_cases.
      apply leqSpred.
    - apply de_Bruijn_Tm_subset with (de_Bruijn_index dBt1); by_cases.
      rewrite maxn_max leq_maxl //.
    - apply de_Bruijn_Tm_subset with (de_Bruijn_index dBt2); by_cases.
      rewrite maxn_max leq_maxr //.
    - rewrite /nat_to_pred //.
  Qed.

  Lemma de_Bruijn_index_minimal :
    forall n dBt,
      dBt ∈ Tm^db n ->
      de_Bruijn_index dBt <= n.
  Proof.
    intros.
    gen n. induction dBt; by_cases.
    - apply IHdBt in H.
      rewrite /leq -predn_sub -subnS //.
    - rewrite /in_mem /= -(rwP andP) in H. destruct H as [H1 H2].
      apply IHdBt1 in H1. apply IHdBt2 in H2.
      rewrite maxn_max geq_max H1 H2 //.
  Qed.

  Definition codomm_de_Bruijn_index {A : ordType} (ϕ : {fmap A → de_Bruijn_term}) : nat :=
    \max_(dBt <- codomm ϕ) de_Bruijn_index dBt.

  Lemma ϕ_type :
    forall ϕ n,
      n ∈ codomm ϕ ->
      n ∈ codomm_𝐍 ϕ.
  Proof.
    introv Hnℛϕ. rewrite /codomm_𝐍 -maxE. apply maximum_correct. auto.
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
    by_cases. apply ϕ_type. by_cases.
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
    rewrite /Tm /in_mem /=.
    introv Hϕt.
    gen ϕ. induction t; by_cases.
    - apply de_Bruijn_Tm_subset with (codomm_𝐍 (ϕ^+s)).
      + apply codomm_𝐍_update_ϕ.
      + apply IHt. by_cases.
        assert (x ∈ FV t :\ s) by by_cases.
        apply Hϕt in H0. by_cases.
    - apply IHt1. by_cases.
    - apply IHt2. by_cases.
    - apply ϕ_type. by_cases.
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
    by_cases.
    - assert (x0 ∈ domm R) by by_cases. apply H in H4. by_cases.
    - apply H2 in H5. by_cases.
    - assert (y0 ∈ codomm R) by by_cases. apply H3 in H4. by_cases.
    - assert (x0 ∈ domm R) by by_cases. apply H in H4. by_cases.
    - assert (R x0 y0). { apply H2. by_cases. } by_cases.
    - assert (R x0 y0). { apply H2. by_cases. } by_cases.
    - assert (R x0 y0). { apply H2. by_cases. } by_cases.
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
    destruct u; inverts H; by_cases.
    - f_equal. apply IHt with (R⦅s,s0⦆); try solve [by_cases].
      + by_cases. assert (x ∈ FV t :\ s) by by_cases. apply Hϕt in H3. by_cases.
      + by_cases.
        * assert (x ∈ domm R) by by_cases. apply H in H2. by_cases.
        * assert (x ∈ codomm R) by by_cases. apply H0 in H2. by_cases.
      + apply lemma9'; by_cases.
      + by_cases. assert (x ∈ FV u :\ s0) by by_cases. apply Hψu in H3. by_cases.
    - apply IHt with (R⦅s,s0⦆) (ϕ^+s) (ψ^+s0) u in H1; try solve [by_cases].
      + by_cases. assert (x ∈ FV t :\ s) by by_cases. apply Hϕt in H4. by_cases.
      + by_cases.
        * assert (x ∈ domm R) by by_cases. apply H in H3. by_cases.
        * assert (x ∈ codomm R) by by_cases. apply H0 in H3. by_cases.
      + apply lemma9'; by_cases.
      + by_cases. assert (x ∈ FV u :\ s0) by by_cases. apply Hψu in H4. by_cases.
    - f_equal.
      + apply IHt1 with R; by_cases.
      + apply IHt2 with R; by_cases.
    - apply IHt1 with R ϕ ψ u1 in H1; by_cases.
    - apply IHt2 with R ϕ ψ u2 in H2; by_cases.
    - apply HRϕψ in H1. by_cases.
    - assert (s ∈ fset1 s) by by_cases. apply Hϕt in H2. by_cases.
      assert (s0 ∈ fset1 s0) by by_cases. apply Hψu in H1. by_cases.
      apply HRϕψ. by_cases.
  Qed.

  (** Page 7: Proposition 8. *)
  Proposition to_de_Bruijn_chooses_canonical_representations :
    forall t u ϕ,
      is_injective ϕ ->
      t ∈ Tm (domm ϕ) ->
      u ∈ Tm (domm ϕ) ->
      t ≡_α u <-> t^ϕ = u^ϕ.
  Proof.
    by_cases.
    - destruct H2 as [X Hα]. apply lemma9 with (R := 1__(domm ϕ)); by_cases.
      apply α_equivalent'_observably_equal with (R := 1__X); by_cases.
      apply H0 in H2. by_cases.
    - apply lemma9 with (R := 1__(domm ϕ)) in H2; by_cases. exists (domm ϕ). by_cases.
  Qed.

  Module DeBruijn.
    Record Subst (m n : nat) : Type :=
      mkSubst
        { Subst_map : {fmap nat → de_Bruijn_term}
        ; Subst_domm := domm Subst_map
        ; Subst_domm_cond :
          forall i, i ∈ n <-> i ∈ Subst_domm
        ; Subst_codomm := codomm Subst_map
        ; Subst_codomm_cond :
          forall dBt,
            dBt ∈ Subst_codomm ->
            dBt ∈ Tm^db m
        }.

    #[program] Definition Subst_getm {m n} (ts : Subst m n) i (Hi : i ∈ n) : de_Bruijn_term :=
      match getm (Subst_map ts) i with
      | None   => _
      | Some x => x
      end.
    Next Obligation.
      apply Subst_domm_cond with (n := n) (s := ts) in Hi.
      symmetry in Heq_anonymous. apply (rwP dommPn) in Heq_anonymous.
      rewrite Hi // in Heq_anonymous.
    Qed.

    Lemma getm_to_Subst_getm :
      forall m n (ts : Subst m n) i (Hi : i ∈ n) dBt,
        getm (Subst_map ts) i = Some dBt ->
        Subst_getm ts i Hi = dBt.
    Proof.
      intros.
      rewrite /Subst_getm.
      remember (Subst_getm_obligation_1 _ _ _) as Htemp. clear HeqHtemp. gen Htemp.
      rewrite /= H //.
    Qed.

    Lemma Z_in_nonempty_Subst_domm :
      forall m n (ts : Subst m n) i,
        i ∈ Subst_domm ts ->
        0 ∈ Subst_domm ts.
    Proof.
      intros.
      rewrite -Subst_domm_cond. rewrite -Subst_domm_cond in H.
      destruct n; auto.
    Qed.

    Fixpoint wk_var i (x : nat) : nat :=
      match i, x with
      | 0,   _   => S x
      | S i, 0   => 0
      | S i, S x => S (wk_var i x)
      end.

    Lemma wk_var_lt :
      forall i (x : nat),
        wk_var i x <= S x.
    Proof. intros. gen i. induction x; destruct i; by_cases. Qed.

    Fixpoint wk i dBt : de_Bruijn_term :=
      match dBt with
      | de_Bruijn_variable x          => de_Bruijn_variable (wk_var i x)
      | de_Bruijn_application dBt dBu => de_Bruijn_application (wk i dBt) (wk i dBu)
      | de_Bruijn_abstraction dBt     => de_Bruijn_abstraction (wk (S i) dBt)
      end.

    Lemma wk_range :
      forall i n dBt,
        dBt ∈ Tm^db n ->
        wk i dBt ∈ Tm^db (S n).
    Proof.
      intros.
      gen i n. induction dBt; by_cases;
      rewrite /in_mem /=; rewrite /in_mem /= in H; by_cases.
      rewrite /in_mem /= /nat_to_pred.
      apply leq_trans with (S (S n)); auto.
      apply wk_var_lt.
    Qed.

    #[program] Definition ext {m n} (ts : Subst m n) : Subst (S m) (S n) :=
      {| Subst_map :=
          setm
            (mkfmapfp
               (fun i => omap (wk 0) (getm (Subst_map ts) (i.-1)))
               (map S (Subst_domm ts)))
            0
            (de_Bruijn_variable 0)
      |}.
    Next Obligation.
      rewrite domm_set domm_mkfmapfp in_fsetU1.
      destruct i.
      - by_cases.
      - split; by_cases.
        + rewrite (Subst_domm_cond ts) /Subst_domm in H.
          rewrite in_fset mem_filter /= map_f; by_cases.
        + rewrite in_fset mem_filter /= in H; by_cases.
          assert (i ∈ Subst_domm ts).
          { unfold Subst_domm. by_cases.
            destruct (getm (Subst_map ts) i) eqn:Hi; by_cases. }
          rewrite -nat_to_pred_S (Subst_domm_cond ts) //.
    Qed.
    Next Obligation.
      apply (rwP codommP) in H as [i Hi].
      rewrite setmE in Hi.
      destruct i; by_cases.
      rewrite map_f in H.
      - assert (d ∈ Subst_codomm ts) as Hd by (unfold Subst_codomm; by_cases).
        apply Subst_codomm_cond in Hd.
        apply wk_range. auto.
      - rewrite -(rwP dommP). by_cases.
    Qed.

    Lemma extZE' :
      forall m n (ts : Subst (S m) n),
        getm (Subst_map (ext ts)) 0 = Some (de_Bruijn_variable 0).
    Proof. by_cases. Qed.

    Lemma extZE :
      forall m n (ts : Subst (S m) n),
        Subst_getm (ext ts) 0 (ltn0Sn _) = 0.
    Proof.
      intros.
      apply getm_to_Subst_getm. rewrite extZE' //.
    Qed.

    Lemma extSE' :
      forall m n (ts : Subst m n) i,
        getm (Subst_map (ext ts)) (S i) = omap (wk 0) (getm (Subst_map ts) i).
    Proof.
      by_cases.
      rewrite map_f // /Subst_domm -(rwP dommP) in Heqb. by_cases.
    Qed.

    Lemma extSE :
      forall m n (ts : Subst m n) i (Hi1 Hi2 : i ∈ n),
        Subst_getm (ext ts) (S i) Hi1 = wk 0 (Subst_getm ts i Hi2).
    Proof.
      intros.
      apply getm_to_Subst_getm. rewrite extSE'.
      rewrite (Subst_domm_cond ts) /= in Hi1.
      apply (rwP dommP) in Hi1 as [dBt HdBt].
      rewrite HdBt.
      apply getm_to_Subst_getm with (Hi := Hi2) in HdBt.
      rewrite HdBt //.
    Qed.

    #[program] Fixpoint subst {m n} (ts : Subst m n) dBt (HdBt : dBt ∈ Tm^db n) : de_Bruijn_term :=
      match dBt with
      | de_Bruijn_variable x          => Subst_getm ts x _
      | de_Bruijn_application dBt dBu => de_Bruijn_application (subst ts dBt HdBt) (subst ts dBu HdBt)
      | de_Bruijn_abstraction dBt     => de_Bruijn_abstraction (subst (ext ts) dBt _)
      end.
    Next Obligation.
      by_cases. symmetry. change (dBt ∈ Tm^db n).
      rewrite /in_mem /= in HdBt. by_cases.
    Qed.
    Next Obligation.
      by_cases. symmetry. change (dBu ∈ Tm^db n).
      rewrite /in_mem /= in HdBt. by_cases.
    Qed.

    Lemma subst_range :
      forall m n (ts : Subst m n) dBt (HdBt : dBt ∈ Tm^db n),
        subst ts dBt HdBt ∈ Tm^db m.
    Proof.
      intros.
      gen m n. induction dBt; by_cases;
      rewrite /in_mem /=; by_cases.
      pose proof HdBt as HdBt'.
      rewrite /in_mem /= in HdBt'.
      apply Subst_domm_cond with (s := ts) in HdBt'.
      unfold Subst_domm in HdBt'. by_cases.
      rewrite (getm_to_Subst_getm ts n HdBt H).
      apply Subst_codomm_cond with (s := ts).
      unfold Subst_codomm. by_cases.
    Qed.

    Definition update_ϕ' ϕ z i : {fmap 𝒱 → nat} :=
      setm (mapm (wk_var i) ϕ) z i.

    #[local] Notation "ϕ '^+[' z ',' i ']'" := (update_ϕ' ϕ z i) (at level 0).

    Lemma update_ϕ'E :
      forall ϕ z i y,
        getm (update_ϕ' ϕ z i) y =
          if y == z
          then Some i
          else omap (wk_var i) (getm ϕ y).
    Proof. unfold update_ϕ'. by_cases. Qed.

    Ltac by_cases_hook9 :=
      lazymatch goal with
      | H : context [ getm (update_ϕ' ?m ?x ?i) ?y] |- _ => rewrite [getm (update_ϕ' m x i) y]update_ϕ'E in H
      | |- context [ getm (update_ϕ' ?m ?x ?i) ?y] => rewrite [getm (update_ϕ' m x i) y]update_ϕ'E
      end || by_cases_hook8.
    Ltac by_cases_hook ::= by_cases_hook9.

    Lemma update_ϕ_shadow :
      forall ϕ x,
        getm (ϕ^+x) x = Some 0.
    Proof. intros. rewrite update_ϕE eq_refl //. Qed.

    Lemma update_ϕ_as_update_ϕ' :
      forall ϕ x,
        ϕ^+x = ϕ^+[x,0].
    Proof. by_cases. Qed.

    Lemma wk_var_noop :
      forall i j,
        j < i ->
        wk_var i j = j.
    Proof.
      intros.
      gen i. induction j; destruct i; by_cases.
    Qed.

    Lemma wk_var_inc :
      forall i j,
        i <= j ->
        wk_var i j = S j.
    Proof. induction i; destruct j; by_cases. Qed.

    Lemma wk_swap :
      forall dBt i j,
        i <= j ->
        wk i (wk j dBt) = wk (S j) (wk i dBt).
    Proof.
      induction dBt; intros; simpl; f_equal; by_cases.
      gen n j. induction i; destruct n, j; by_cases.
    Qed.

    Definition Lift ϕ t := to_de_Bruijn t ϕ.

    Lemma Lift_observably_equal :
      forall t ϕ ψ,
        FV t ⊆ (domm ϕ ∩ domm ψ) ->
        (forall x, x ∈ FV t -> getm ϕ x = getm ψ x) ->
        t^ϕ = t^ψ.
    Proof.
      induction t; intros; simpl; f_equal; by_cases.
      - apply IHt; by_cases;
        assert (x ∈ domm ϕ ∩ domm ψ) as Hx by (apply H; by_cases); by_cases.
        f_equal.
        cut (Some x1 = Some x0). { by_cases. }
        rewrite -Heqo -Heqo0.
        apply H0. by_cases.
      - apply IHt1; by_cases.
        assert (x ∈ domm ϕ ∩ domm ψ) as Hx by (apply H; by_cases); by_cases.
        cut (Some x1 = Some x0). { by_cases. }
        rewrite -H3 -H4.
        apply H0. by_cases.
      - apply IHt2; by_cases.
        assert (x ∈ domm ϕ ∩ domm ψ) as Hx by (apply H1; by_cases); by_cases.
        cut (Some x1 = Some x0). { by_cases. }
        rewrite -H3 -H4.
        apply H0. by_cases.
      - cut (Some x0 = Some x). { by_cases. }
        rewrite -H -H1.
        apply H0. by_cases.
    Qed.

    Lemma wk_var_swap :
      forall i j n,
        i <= j ->
        wk_var i (wk_var j n) = wk_var (S j) (wk_var i n).
    Proof. induction i; destruct j, n; by_cases. Qed.

    Lemma update_ϕ'_shadow :
      forall ϕ x i,
        ϕ^+[x,i]^+x = wk_var (S i) ∘ ϕ^+x.
    Proof.
      by_cases.
      destruct (getm ϕ x0) eqn:H; by_cases.
    Qed.

    Lemma update_ϕ'_swap :
      forall ϕ x y i j,
        y ∉ domm ϕ ->
        j < i ->
        x <> y ->
        ϕ^+[y,i]^+[x,j] = ϕ^+[x,j]^+[y,S i].
    Proof.
      intros.
      apply eq_fmap. intros z.
      rewrite !update_ϕ'E.
      destruct (z =P x); subst.
      - destruct (x =P y); subst; by_cases.
        destruct j; by_cases.
        rewrite wk_var_noop; by_cases.
      - destruct (z =P y); subst; by_cases.
        + apply wk_var_inc. auto.
        + destruct (getm ϕ z); by_cases.
          destruct j, n1; by_cases.
          * rewrite wk_var_noop //. destruct i; by_cases.
          * destruct i; by_cases.
            rewrite wk_var_swap; auto.
    Qed.

    Lemma Lift_wk_var :
      forall t ϕ x i j,
        let Y := domm ϕ in
        t ∈ Tm (Y ∪ {x}) ->
        j < i ->
        t^(wk_var i ∘ ϕ^+[x,j]) = wk i (t^(ϕ^+[x,j])).
    Proof.
      induction t; intros; simpl; f_equal; by_cases.
      - rewrite -IHt; by_cases; cycle 1.
        { assert (x0 ∈ x |: domm ϕ) as Hϕx by (apply H; by_cases). by_cases. }
        apply Lift_observably_equal; by_cases;
        assert (x0 ∈ x |: domm ϕ) as Hϕx by (apply H; by_cases); by_cases.
      - rewrite IHt1; by_cases.
      - rewrite IHt2; by_cases.
    Qed.

    Lemma Lift_wk' :
      forall t ψ z i,
        let Y := domm ψ in
        z ∉ Y ->
        t ∈ Tm Y ->
        t^(ψ^+[z,i]) = wk i (t^ψ).
    Proof.
      induction t; intros; simpl; cycle 1.
      - f_equal;
        apply IHt1 + apply IHt2;
        apply negbTE in H; by_cases.
      - by_cases.
      - f_equal.
        destruct (z =P s); subst; by_cases.
        + rewrite update_ϕ'_shadow Lift_wk_var; by_cases.
          assert (x ∈ domm ψ) by (apply H0; by_cases). by_cases.
        + rewrite -(IHt (ψ^+s) z (S i)); by_cases; cycle 1.
          { assert (x ∈ domm ψ) by (apply H0; by_cases). by_cases. }
          apply Lift_observably_equal; by_cases;
          assert (x ∈ domm ψ) by (apply H0; by_cases); by_cases.
    Qed.

    Lemma Lift_wk :
      forall t ψ z,
        let Y := domm ψ in
        z ∉ Y ->
        t ∈ Tm Y ->
        Lift (ψ^+z) t = wk 0 (Lift ψ t).
    Proof. intros. rewrite /Lift update_ϕ_as_update_ϕ' Lift_wk' //. Qed.

    Lemma Lift_ext :
      forall m n f ϕ ψ (g : Subst m n) x y,
        let X := domm f in
        let Y := domm ψ in
        domm ϕ = X ->
        codomm_Tm_set f ⊆ Y ->
        codomm_𝐍 ϕ <= n ->
        codomm_𝐍 ψ <= m ->
        (forall x, x ∈ X -> obind (getm (Subst_map g)) (getm ϕ x) = omap (Lift ψ) (getm f x)) ->
        y ∉ Y ->
        forall z, z ∈ X ∪ {x} -> omap (Lift (ψ^+y)) (getm (f[x,variable y]) z) = obind (getm (Subst_map (ext g))) (getm (ϕ^+x) z).
    Proof.
      intros m n f ϕ ψ g x y X Y HX HY Hm Hn H Hy z Hz.
      destruct (z =P x); subst.
      { by_cases. }
      replace (omap (Lift (ψ^+y)) ((f[x,variable y]) z)) with (omap (Lift (ψ^+y)) (getm f z)) by by_cases.
      replace (obind (getm (Subst_map (ext g))) (getm (ϕ^+x) z)) with (obind (getm (Subst_map (ext g))) (omap S (getm ϕ z))) by by_cases.
      replace (obind (getm (Subst_map (ext g))) (omap S (getm ϕ z))) with (omap (wk 0) (obind (getm (Subst_map g)) (getm ϕ z))); cycle 1.
      { assert (z ∈ domm ϕ) as Hzϕ. { rewrite HX. by_cases. }
        by_cases.
        rewrite map_f // in Heqb.
        rewrite /Subst_domm -(rwP dommP). by_cases. }
      replace (omap (wk 0) (obind (getm (Subst_map g)) (getm ϕ z))) with (omap (wk 0 ∘ Lift ψ) (getm f z)); cycle 1.
      { rewrite H; by_cases. }
      cut (is_true (z ∈ domm f)); by_cases.
      apply Lift_wk. { by_cases. }
      cut (is_true (x1 ∈ Tm (codomm_Tm_set f))); by_cases.
    Qed.

    (** Page 8: "I leave it to the reader to show that -^ϕ preserves substitution...." *)
    Lemma Lift_preserves_subst' :
      forall t f ϕ ψ m n (g : Subst m n),
        let X := domm f in
        let Y := domm ψ in
        Fresh_correct Fresh ->
        domm ϕ = X ->
        codomm_Tm_set f ⊆ Y ->
        codomm_𝐍 ϕ <= n ->
        codomm_𝐍 ψ <= m ->
        (forall x, x ∈ X -> obind (getm (Subst_map g)) (getm ϕ x) = omap (Lift ψ) (getm f x)) ->
        t ∈ Tm X ->
        forall (Ht : t^ϕ ∈ Tm^db n),
        subst g (t^ϕ) Ht = (⦇f⦈ Fresh Y t)^ψ.
    Proof.
      induction t; intros; simpl; f_equal; try solve [by_cases]; cycle 1.
      - apply IHt1; by_cases.
      - apply IHt2; by_cases.
      - by_cases.
        assert (mapm (getm (Subst_map g)) ϕ s = mapm (Some ∘ Lift ψ) f s).
        { rewrite !mapmE [omap (Some ∘ Lift ψ) (getm f s)]omap_comp /= -H4; by_cases.
          rewrite /in_mem /= (Subst_domm_cond g) in Ht.
          apply (rwP dommPn) in Heqo0. rewrite Ht // in Heqo0. }
        rewrite !mapmE in H6. by_cases.
        apply getm_to_Subst_getm. by_cases.
      - pose (z := Fresh Y). fold z.
        rewrite (IHt (f[s,variable z]) (ϕ^+s) (ψ^+z) _ _ (ext g)) //; cycle -1.
        { by_cases.
          cut (is_true (x ∈ domm f)). { by_cases. }
          apply H5. by_cases. }
        { repeat f_equal. by_cases. }
        { by_cases.
          - cut (is_true (x ∈ domm f)). { by_cases. }
            rewrite -H0. by_cases.
          - cut (is_true (x ∈ domm ϕ)). { by_cases. }
            rewrite H0. by_cases. }
        { rewrite codomm_update_substitution. by_cases.
          cut (is_true (x ∈ domm ψ)). { by_cases. }
          apply H1. by_cases. }
        { apply leq_trans with (S (codomm_𝐍 ϕ)); auto. apply codomm_𝐍_update_ϕ. }
        { apply leq_trans with (S (codomm_𝐍 ψ)); auto. apply codomm_𝐍_update_ϕ. }
        symmetry.
        apply Lift_ext; by_cases.
    Qed.

    #[program] Definition LiftPreservesSubst : Type :=
      forall t f ϕ ψ m n (g : Subst m n),
        let X := domm f in
        let Y := domm ψ in
        Fresh_correct Fresh ->
        forall (HϕX : domm ϕ = X),
        codomm_Tm_set f ⊆ Y ->
        forall (Hϕn : codomm_𝐍 ϕ <= n),
        codomm_𝐍 ψ <= m ->
        (forall x, x ∈ X -> obind (getm (Subst_map g)) (getm ϕ x) = omap (Lift ψ) (getm f x)) ->
        forall (HtX : t ∈ Tm X),
        subst g (t^ϕ) _ = (⦇f⦈ Fresh Y t)^ψ.
    Next Obligation.
      apply de_Bruijn_Tm_subset with (codomm_𝐍 ϕ); auto.
      apply to_de_Bruijn_type.
      rewrite HϕX //.
    Qed.

    Lemma Lift_preserves_subst : LiftPreservesSubst.
    Proof.
      unfold LiftPreservesSubst. intros.
      apply Lift_preserves_subst'; auto.
    Qed.
  End DeBruijn.

  Lemma α_equivalent'_respects_α_equivalence_l :
    forall R t t' u,
      partial_bijection R ->
      t ≡_α t' ->
      t ≡_α^R u ->
      t' ≡_α^R u.
  Proof.
    introv HR Hα Hα'.
    symmetry in Hα. destruct Hα as [X Hα].
    apply α_equivalent'_observably_equal with (R := (1__X);;R); by_cases.
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
    rewrite -(@invmK _ _ R).
    - apply α_equivalent'_converse; auto.
      eapply α_equivalent'_respects_α_equivalence_l; unfold α_equivalent; eauto.
    - by_cases.
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
      assert (Y__sub ∪ {Fresh0 Y__sub} = domm R) as HR.
      { by_cases. apply HfY__super in Heqb. by_cases. }
      assert (⦇f[s,variable (Fresh0 Y__super)]⦈ Fresh0 (Y__super ∪ {Fresh0 Y__super}) t ≡_α ⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t)).
      { etransitivity; cycle 1.
        { symmetry.
          replace
            (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t))
            with ((⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) ∘ ⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub})) t : term); auto.
          rewrite HR. replace (domm R) with (domm (mapm variable R)) by by_cases.
          apply monad_substitution3; by_cases.
          - apply HfY__super in Heqb. by_cases.
          - assert (x ∈ codomm_Tm_set f) by by_cases. apply HfY__sub in H1. by_cases.
          - assert (x ∈ FV t :\ s) by by_cases. apply HtX in H0. by_cases. }
        simpl.
        transitivity (⦇f[s,variable (Fresh0 Y__super)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) t); cycle 1.
        { apply substitution_preserves_α_congruence; auto.
          - by_cases. apply HfY__sub. by_cases.
          - by_cases. rewrite FV_lift_substitution in H; by_cases.
            + apply HfY__super in Heqb. by_cases.
            + assert (x0 ∈ codomm_Tm_set f) by by_cases. apply HfY__sub in H0. by_cases.
          - by_cases.
          - intros x Hx.
            rewrite mapmE !setmE.
            rewrite domm_set in_fsetU in_fset1 in Hx.
            destruct (x =P s); subst. { by_cases. }
            apply (rwP dommP) in Hx as [u Hu]. rewrite Hu /=.
            assert (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u ≡_α u) as Hα.
            { transitivity (⦇η__(Y__sub ∪ {Fresh0 Y__super})⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u).
              { exists Y__sub. eapply substitution_preserves_α_congruence'; auto.
                - rewrite /is_subset_of domm_η domm_identity codomm_identity domm_map -(rwP andP).
                  rewrite -HR. by_cases.
                - by_cases.
                - by_cases.
                - by_cases.
                - by_cases.
                - apply α_equivalent'_identity. by_cases. apply HfY__sub. by_cases. }
              apply monad_substitution1; by_cases.
              apply HfY__sub. by_cases. }
            symmetry in Hα.
            rewrite (@α_equivalent'_morph (1__(Y__sub ∪ {Fresh0 Y__super})) _ u (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u) Hα (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u) (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) u)) //.
            + apply α_equivalent'_identity. by_cases.
              rewrite FV_lift_substitution // in H; by_cases.
              * apply HfY__super in Heqb. by_cases.
              * assert (x1 ∈ codomm_Tm_set f) by by_cases. apply HfY__sub in H0. by_cases.
            + reflexivity.
          - by_cases. apply (rwP dommP), HtX. by_cases.
          - reflexivity. }
        symmetry.
        apply IHt; by_cases.
        - apply (rwP dommP), HtX. by_cases.
        - apply HfY__sub. by_cases. }
      rewrite (@α_equivalent'_morph (R ᵒ) _ _ (⦇mapm variable R⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__super}) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t)) H (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t) (⦇f[s,variable (Fresh0 Y__sub)]⦈ Fresh0 (Y__sub ∪ {Fresh0 Y__sub}) t)); cycle 1.
      { by_cases. }
      { reflexivity. }
      apply lemma7; by_cases.
      + apply HfY__super in Heqb. by_cases.
      + rewrite FV_lift_substitution in H0; by_cases.
        * assert (x ∈ codomm_Tm_set f) by by_cases. apply HfY__sub in H3. by_cases.
        * apply HfY__sub. by_cases.
        * apply (rwP dommP), HtX. by_cases.
    - exists Y__super. by_cases.
      + rewrite (@α_equivalent'_morph (1__(Y__super)) _ _ (⦇f⦈ Fresh0 Y__super t1) _ _ (⦇f⦈ Fresh0 Y__super t1)) //.
        * apply α_equivalent'_identity, lift_substitution_type; by_cases.
        * apply IHt1; by_cases.
        * reflexivity.
      + rewrite (@α_equivalent'_morph (1__(Y__super)) _ _ (⦇f⦈ Fresh0 Y__super t2) _ _ (⦇f⦈ Fresh0 Y__super t2)) //.
        * apply α_equivalent'_identity, lift_substitution_type; by_cases.
        * apply IHt2; by_cases.
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
    - symmetry. apply lift_substitution_independent_of_codomm_subset; by_cases.
    - apply lift_substitution_independent_of_codomm_subset; by_cases.
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
    - apply α_equivalent'_observably_equal with (R := 1__X); by_cases.
    - apply α_equivalent'_observably_equal with (R := 1__Y); by_cases.
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
    - unfold A.update_substitution.
      apply abstraction_preserves_α_equivalent.
      etransitivity; cycle 1.
      { eapply IHt, fsubsetxx. by_cases. apply (rwP dommP), HtX. by_cases. }
      apply lift_substitution_independent_of_codomm; by_cases. apply (rwP dommP), HtX. by_cases.
    - apply application_preserves_α_equivalent; by_cases.
      + eapply IHt1; by_cases.
      + eapply IHt2; by_cases.
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
