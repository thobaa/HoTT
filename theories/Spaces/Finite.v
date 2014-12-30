(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations EquivalenceVarieties UnivalenceImpliesFunext.
Require Import hit.Truncations.
Import TrM.
Require Import Peano.           (** From modified Coq stdlib *)

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Finite sets *)

(** ** Canonical finite sets *)

Fixpoint Fin (n : nat) : Type
  := match n with
       | 0 => Empty
       | S n => Fin n + Unit
     end.

Global Instance decidablepaths_fin (n : nat)
: DecidablePaths (Fin n).
Proof.
  induction n as [|n IHn]; simpl; exact _.
Defined.

Global Instance contr_fin1 : Contr (Fin 1).
Proof.
  refine (contr_equiv' Unit (equiv_inverse (sum_empty_l Unit))).
Defined.

Definition fin_empty (n : nat) (f : Fin n -> Empty) : n = 0.
Proof.
  destruct n; [ reflexivity | ].
  elim (f (inr tt)).
Defined.

(** ** Transposition equivalences *)

(** *** Swap the last two elements. *)
Definition fin_transpose_last_two (n : nat)
: Fin n.+2 <~> Fin n.+2
  := (equiv_compose'
        (equiv_inverse (equiv_sum_assoc _ _ _))
     (equiv_compose'
        (equiv_functor_sum' (equiv_idmap _)
                            (equiv_sum_symm _ _))
        (equiv_sum_assoc _ _ _))).

Arguments fin_transpose_last_two : simpl nomatch.

Definition fin_transpose_last_two_last (n : nat)
: fin_transpose_last_two n (inr tt) = (inl (inr tt))
  := 1.

Definition fin_transpose_last_two_nextlast (n : nat)
: fin_transpose_last_two n (inl (inr tt)) = (inr tt)
  := 1.

Definition fin_transpose_last_two_rest (n : nat) (k : Fin n)
: fin_transpose_last_two n (inl (inl k)) = (inl (inl k))
  := 1.

(** *** Swap the last element with [k]. *)

Fixpoint fin_transpose_last_with (n : nat) (k : Fin n.+1)
: Fin n.+1 <~> Fin n.+1.
Proof.
  destruct k as [k|].
  - destruct n as [|n IH].
    + elim k.
    + destruct k as [k|].
      * refine (equiv_compose'
                  (fin_transpose_last_two n)
                  (equiv_compose' _ (fin_transpose_last_two n))).
        refine (equiv_functor_sum'
                  (fin_transpose_last_with n (inl k))
                  (equiv_idmap Unit)).
      * apply fin_transpose_last_two.
  - exact (equiv_idmap _).
Defined.

Arguments fin_transpose_last_with : simpl nomatch.

Definition fin_transpose_last_with_last (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k (inr tt) = k.
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    + elim k.
    + destruct k as [k|].
      * simpl. rewrite IH; reflexivity.
      * simpl. apply ap, ap, path_contr.
  - (** For some reason [simpl] won't simplify this until [n] is destructed. *)
    destruct n; simpl.
    all:apply ap, path_contr.
Qed.

Definition fin_transpose_last_with_with (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k k = inr tt.
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    + elim k.
    + destruct k as [|k]; simpl.
      * rewrite IH; reflexivity.
      * apply ap, path_contr.
  - destruct n; simpl.
    all:apply ap, path_contr.
Qed.

Definition fin_transpose_last_with_rest (n : nat)
           (k : Fin n.+1) (l : Fin n)
           (notk : k <> inl l)
: fin_transpose_last_with n k (inl l) = (inl l).
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    1:elim k.
    destruct k as [k|]; simpl.
    { destruct l as [l|]; simpl.
      - rewrite IH.
        + reflexivity.
        + exact (fun p => notk (ap inl p)).
      - reflexivity. }
    { destruct l as [l|]; simpl.
      - reflexivity.
      - elim (notk (ap inl (ap inr (path_unit _ _)))). }
  - destruct n; reflexivity.
Qed.

Definition fin_transpose_last_with_last_other (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n (inr tt) k = k.
Proof.
  destruct n; reflexivity.
Qed.

Definition fin_transpose_last_with_invol (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k o fin_transpose_last_with n k == idmap.
Proof.
  intros l.
  destruct l as [l|[]].
  - destruct k as [k|[]].
    { destruct (dec_paths k l) as [p|p].
      - rewrite p.
        rewrite fin_transpose_last_with_with.
        apply fin_transpose_last_with_last.
      - rewrite fin_transpose_last_with_rest;
          try apply fin_transpose_last_with_rest;
          exact (fun q => p (path_sum_inl _ q)). }
    + rewrite fin_transpose_last_with_last_other.
      apply fin_transpose_last_with_last_other.
  - rewrite fin_transpose_last_with_last.
    apply fin_transpose_last_with_with.
Qed.

(** ** Equivalences between canonical finite sets *)

(** To give an equivalence [Fin n.+1 <~> Fin m.+1] is equivalent to giving an element of [Fin m.+1] (the image of the last element) together with an equivalence [Fin n <~> Fin m].  More specifically, any such equivalence can be decomposed uniquely as a last-element transposition followed by an equivalence fixing the last element.  *)

(** Here is the uncurried map that constructs an equivalence [Fin n.+1 <~> Fin m.+1]. *)
Definition fin_equiv (n m : nat)
           (k : Fin m.+1) (e : Fin n <~> Fin m)
: Fin n.+1 <~> Fin m.+1
  := (equiv_compose'
        (fin_transpose_last_with m k)
        (equiv_functor_sum' e (equiv_idmap Unit))).

(** Here is the curried version that we will prove to be an equivalence. *)
Definition fin_equiv' (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) -> (Fin n.+1 <~> Fin m.+1)
  := fun ke => fin_equiv n m (fst ke) (snd ke).

(** We construct its inverse and the two homotopies first as versions using homotopies without funext (similar to [ExtendableAlong]), then apply funext at the end. *)
Definition fin_equiv_hfiber (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: { kf : (Fin m.+1) * (Fin n <~> Fin m) & fin_equiv' n m kf == e }.
Proof.
  simpl in e.
  refine (equiv_sigma_prod _ _).
  recall (e (inr tt)) as y eqn p.
  assert (p' := (moveL_equiv_V _ _ p)^).
  exists y.
  destruct y as [y|[]].
  + refine (equiv_unfunctor_sum_l
              (equiv_compose'
                 (fin_transpose_last_with m (inl y))
                 e)
              _ _ ; _).
    { intros a. ev_equiv.
      assert (q : inl y <> e (inl a))
        by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^ @ p^))).
      set (z := e (inl a)) in *.
      destruct z as [z|[]].
      - rewrite fin_transpose_last_with_rest;
        try exact tt; try assumption.
      - rewrite fin_transpose_last_with_last; exact tt. }
    { intros []. ev_equiv.
      rewrite p.
      rewrite fin_transpose_last_with_with; exact tt. }
    intros x. unfold fst, snd; ev_equiv. simpl.
    destruct x as [x|[]]; simpl.
    * rewrite unfunctor_sum_l_beta.
      apply fin_transpose_last_with_invol.
    * refine (fin_transpose_last_with_last _ _ @ p^).
  + refine (equiv_unfunctor_sum_l e _ _ ; _).
    { intros a.
      destruct (is_inl_or_is_inr (e (inl a))) as [l|r].
      - exact l.
      - assert (q := inr_un_inr (e (inl a)) r).
        apply moveR_equiv_V in q.
        assert (s := q^ @ ap (e^-1 o inr) (path_unit _ _) @ p').
        elim (inl_ne_inr _ _ s). }
    { intros []; exact (p^ # tt). }
    intros x. unfold fst, snd; ev_equiv. simpl.
    destruct x as [a|[]].
    * rewrite fin_transpose_last_with_last_other.
      apply unfunctor_sum_l_beta.
    * simpl.
      rewrite fin_transpose_last_with_last.
      symmetry; apply p.
Qed.

Definition fin_equiv_inv (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: (Fin m.+1) * (Fin n <~> Fin m)
  := (fin_equiv_hfiber n m e).1.

Definition fin_equiv_issect (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: fin_equiv' n m (fin_equiv_inv n m e) == e
  := (fin_equiv_hfiber n m e).2.

Definition fin_equiv_inj_fst (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (k = l).
Proof.
  intros p.
  refine (_ @ p (inr tt) @ _); simpl;
  rewrite fin_transpose_last_with_last; reflexivity.
Qed.

Definition fin_equiv_inj_snd (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (e == f).
Proof.
  intros p.
  intros x. assert (q := p (inr tt)); simpl in q.
  rewrite !fin_transpose_last_with_last in q.
  rewrite <- q in p; clear q l.
  exact (path_sum_inl _
           (equiv_inj (fin_transpose_last_with m k) (p (inl x)))).
Qed.

(** Now it's time for funext. *)
Global Instance isequiv_fin_equiv `{Funext} (n m : nat)
: IsEquiv (fin_equiv' n m).
Proof.
  refine (isequiv_pathsplit 0 _); split.
  - intros e; exists (fin_equiv_inv n m e).
    apply path_equiv, path_arrow, fin_equiv_issect.
  - intros [k e] [l f]; simpl.
    refine (_ , fun _ _ => tt).
    intros p; refine (_ ; path_ishprop _ _).
    apply (ap equiv_fun) in p.
    apply ap10 in p.
    apply path_prod'.
    + refine (fin_equiv_inj_fst n m k l e f p).
    + apply path_equiv, path_arrow.
      refine (fin_equiv_inj_snd n m k l e f p).
Qed.

Definition equiv_fin_equiv `{Funext} (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) <~> (Fin n.+1 <~> Fin m.+1)
  := BuildEquiv _ _ (fin_equiv' n m) _.

(** In particuar, this implies that if two canonical finite sets are equivalent, then their cardinalities are equal. *)
Definition nat_eq_fin_equiv (n m : nat)
: (Fin n <~> Fin m) -> (n = m).
Proof.
  revert m; induction n as [|n IHn]; induction m as [|m IHm]; intros e.
  - exact idpath.
  - elim (e^-1 (inr tt)).
  - elim (e (inr tt)).
  - refine (ap S (IHn m _)).
    exact (snd (fin_equiv_inv n m e)).
Qed.

(** ** General finite sets *)

(** *** Definition and basic properties *)

Class Finite (X : Type) :=
  { fcard : nat ;
    merely_equiv_fin : merely (X <~> Fin fcard) }.

Arguments fcard X {_}.
Arguments merely_equiv_fin X {_}.

Definition issig_finite X
: { n : nat & merely (X <~> Fin n) } <~> Finite X.
Proof.
  issig (@Build_Finite X) (@fcard X) (@merely_equiv_fin X).
Defined.

Global Instance ishprop_finite X
: IsHProp (Finite X).
Proof.
  refine (trunc_equiv' _ (issig_finite X)).
  apply ishprop_sigma_disjoint; intros n m Hn Hm.
  strip_truncations.
  refine (nat_eq_fin_equiv n m (equiv_compose' Hm (equiv_inverse Hn))).
Defined.

Global Instance decidablepaths_finite `{Funext} X `{Finite X}
: DecidablePaths X.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (decidablepaths_equiv _ e^-1 _).
Defined.

Definition finite_equiv X {Y} (e : X -> Y) `{IsEquiv X Y e}
: Finite X -> Finite Y.
Proof.
  intros ?.
  refine (Build_Finite Y (fcard X) _).
  assert (f := merely_equiv_fin X); strip_truncations.
  apply tr.
  exact (equiv_compose f e^-1).
Defined.

Definition finite_equiv' X {Y} (e : X <~> Y)
: Finite X -> Finite Y
  := finite_equiv X e.

Definition fcard_equiv {X Y} (e : X -> Y) `{IsEquiv X Y e}
           `{Finite X} `{Finite Y}
: fcard X = fcard Y.
Proof.
  transitivity (@fcard Y (finite_equiv X e _)).
  - reflexivity.
  - exact (ap (@fcard Y) (path_ishprop _ _)).
Defined.

Definition fcard_equiv' {X Y} (e : X <~> Y)
           `{Finite X} `{Finite Y}
: fcard X = fcard Y
  := fcard_equiv e.

(** *** Simple examples of finite sets *)

Global Instance finite_fin n : Finite (Fin n)
  := Build_Finite _ n (tr (equiv_idmap _)).

Global Instance finite_empty : Finite Empty
  := finite_fin 0.

Global Instance finite_unit : Finite Unit.
Proof.
  refine (finite_equiv' (Fin 1) _ _); simpl.
  apply sum_empty_l.
Defined.

Global Instance finite_contr X `{Contr X} : Finite X
  := finite_equiv Unit equiv_contr_unit^-1 _.

Global Instance finite_decidable_hprop X `{IsHProp X} `{Decidable X}
: Finite X.
Proof.
  destruct (dec X) as [x|nx].
  - assert (Contr X) by exact (contr_inhabited_hprop X x).
    exact _.
  - refine (finite_equiv Empty nx^-1 _).
Defined.

Global Instance finite_paths {X} `{Finite X} (x y : X)
: Finite (x = y).
Proof.
  (** If we assume [Funext], then typeclass inference produces this automatically, since [X] has decidable equality and (hence) is a set, so [x=y] is a decidable.  But we can also deduce it without funext, since [Finite] is an hprop even without funext. *)
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _ (ap e)^-1 _).
Defined.

Global Instance finite_succ X `{Finite X} : Finite (X + Unit).
Proof.
  refine (Build_Finite _ (fcard X).+1 _).
  pose proof (merely_equiv_fin X).
  strip_truncations; apply tr.
  refine (equiv_functor_sum' _ (equiv_idmap _)); assumption.
Defined.  

Definition fcard_succ X `{Finite X}
: fcard (X + Unit) = (fcard X).+1
  := 1.  

(** *** Induction over finite sets *)

(** Most concrete applications of this don't actually require univalence, but the general version does.  For this reason the general statement is less useful than it might be. *)
Definition finite_ind_hprop `{Univalence}
           (P : forall X, Finite X -> Type)
           `{forall X (fX:Finite X), IsHProp (P X _)}
           (f0 : P Empty _)
           (fs : forall X (fX:Finite X), P X _ -> P (X + Unit)%type _)
           (X : Type) `{Finite X}
: P X _.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  assert (p := transportD Finite P (path_universe e^-1) _).
  refine (transport (P X) (path_ishprop _ _) (p _)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact f0.
  - refine (transport (P (Fin n.+1)) (path_ishprop _ _) (fs _ _ IH)).
Defined.

(** *** The finite axiom of choice *)

Definition finite_choice {X} `{Finite X} (P : X -> Type)
: (forall x, merely (P x)) -> merely (forall x, P x).
Proof.
  intros f.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  set (P' := P o e^-1).
  assert (f' := (fun x => f (e^-1 x)) : forall x, merely (P' x)).
  refine (Trunc_functor (X := forall x:Fin (fcard X), P' x) -1 _ _).
  - intros g x; exact (eissect e x # g (e x)).
  - clearbody P'; clear f P e.
    generalize dependent (fcard X); intros n P f.
    induction n as [|n IH].
    + exact (tr (Empty_ind P)).
    + specialize (IH (P o inl) (f o inl)).
      assert (e := f (inr tt)).
      strip_truncations.
      exact (tr (sum_ind P IH (Unit_ind e))).
Defined.

(** *** Constructions on finite sets *)

(** Finite sets are closed under sums, products, function spaces, and equivalence spaces.  There are multiple choices we could make in proving these facts.  Since we know what the cardinalities ought to be in all cases (since we know how to add, multiply, exponentiate, and take factorials of natural numbers), we could specify those off the bat, and then reduce to the case of canonical finite sets.  However, it's more amusing to instead prove finiteness of these constructions by "finite-set induction", and then *deduce* that their cardinalities are given to the corresponding operations on natural numbers (because they satisfy the same recurrences). *)

Global Instance finite_sum X Y `{Finite X} `{Finite Y}
: Finite (X + Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (finite_equiv _ (functor_sum idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (finite_equiv _ (sum_empty_r X)^-1 _).
  - refine (finite_equiv _ (equiv_sum_assoc X _ Unit) _).
Defined.

(** The cardinality function [fcard] actually computes: *)
Goal fcard (Fin 3 + Fin 4) = 7.
  reflexivity.
Abort.

Definition fcard_sum X Y `{Finite X} `{Finite Y}
: fcard (X + Y) = fcard X + fcard Y.
Proof.
  refine (_ @ nat_plus_comm _ _).
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (fcard_equiv' (equiv_functor_sum' (equiv_idmap X) e) @ _).
  refine (_ @ ap (fun y => y + fcard X) (fcard_equiv e^-1)).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (sum_empty_r X)^-1).
  - refine (fcard_equiv (equiv_sum_assoc _ _ _)^-1 @ _).
    exact (ap S IH).
Defined.

Global Instance finite_prod X Y `{Finite X} `{Finite Y}
: Finite (X * Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (finite_equiv _ (functor_prod idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (finite_equiv _ (prod_empty_r X)^-1 _).
  - refine (finite_equiv _ (sum_distrib_l X _ Unit)^-1 (finite_sum _ _)).
    refine (finite_equiv _ (prod_unit_r X)^-1 _).
Defined.

Definition fcard_prod X Y `{Finite X} `{Finite Y}
: fcard (X * Y) = fcard X * fcard Y.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv' (equiv_functor_prod' e (equiv_idmap Y)) @ _).
  refine (_ @ ap (fun x => x * fcard Y) (fcard_equiv e^-1)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (prod_empty_l Y)).
  - refine (fcard_equiv (sum_distrib_r Y (Fin n) Unit) @ _).
    refine (fcard_sum _ _ @ _).
    simpl.
    refine (_ @ nat_plus_comm _ _).
    refine (ap011 plus _ _).
    + apply IH.
    + apply fcard_equiv', prod_unit_l.
  Defined.

Global Instance finite_arrow `{Funext} X Y `{Finite X} `{Finite Y}
: Finite (X -> Y).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _ (functor_arrow e idmap) _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact _.
  - refine (finite_equiv _ (equiv_sum_ind (fun (_:Fin n.+1) => Y)) _).
    apply finite_prod; try assumption.
    refine (finite_equiv _ (@Unit_ind (fun (_:Unit) => Y)) _).
Defined.

Definition fcard_arrow `{Funext} X Y `{Finite X} `{Finite Y}
: fcard (X -> Y) = nat_exp (fcard Y) (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv (functor_arrow e idmap)^-1 @ _).
  refine (_ @ ap (fun x => nat_exp (fcard Y) x) (fcard_equiv e)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_sum_ind (fun (_:Fin n.+1) => Y))^-1 @ _).
    refine (fcard_prod _ _ @ _).
    apply (ap011 mult).
    + assumption.
    + refine (fcard_equiv (@Unit_ind (fun (_:Unit) => Y))^-1).
Defined.

(** [fcard] still computes, despite the funext: *)
Goal forall fs:Funext, fcard (Fin 3 -> Fin 4) = 64.
  reflexivity.
Abort.

Global Instance finite_aut `{Funext} X `{Finite X}
: Finite (X <~> X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _
            (equiv_functor_equiv (equiv_inverse e) (equiv_inverse e)) _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact _.
  - refine (finite_equiv _ (equiv_fin_equiv n n) _).
Defined.

Definition fcard_aut `{Funext} X `{Finite X}
: fcard (X <~> X) = factorial (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv
            (equiv_functor_equiv (equiv_inverse e) (equiv_inverse e))^-1 @ _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_fin_equiv n n)^-1 @ _).
    refine (fcard_prod _ _ @ _).
    apply ap011.
    + reflexivity.
    + assumption.
Defined.

(** [fcard] still computes: *)
Goal forall fs:Funext, fcard (Fin 4 <~> Fin 4) = 24.
  reflexivity.
Abort.

(** ** Finite sums of natural numbers *)

(** Perhaps slightly less obviously, finite sets are also closed under sigmas. *)

Global Instance finite_sigma {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: Finite { x:X & Y x }.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv' _
            (equiv_functor_sigma (equiv_inverse e)
                                 (fun x (y:Y (e^-1 x)) => y)) _).
  set (Y' := Y o e^-1).
  assert (forall x, Finite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (fcard X); intros n Y' ?.
  induction n as [|n IH].
  - refine (finite_equiv Empty pr1^-1 _).
  - refine (finite_equiv _ (equiv_sigma_sum (Fin n) Unit Y')^-1 _).
    apply finite_sum.
    + apply IH; exact _.
    + refine (finite_equiv _ (equiv_contr_sigma _)^-1 _).
Defined.

(** Amusingly, this automatically gives us a way to add up a family of natural numbers indexed by any finite set.  (We could of course also define such an operation directly, probably using [merely_ind_hset].) *)

Definition finplus {X} `{Finite X} (f : X -> nat) : nat
  := fcard { x:X & Fin (f x) }.

Definition fcard_sigma {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: fcard { x:X & Y x } = finplus (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g.
  strip_truncations.
  unfold finplus.
  refine (fcard_equiv' (equiv_functor_sigma' (equiv_idmap X) g)).
Defined.

(** The sum of a finite constant family is the product by its cardinality. *)
Definition finplus_const X `{Finite X} n
: finplus (fun x:X => n) = fcard X * n.
Proof.
  transitivity (fcard (X * Fin n)).
  - exact (fcard_equiv' (equiv_sigma_prod0 X (Fin n))).
  - exact (fcard_prod X (Fin n)).
Defined.

(** By the way, closure under sigmas and paths also implies closure under hfibers. *)
Global Instance finite_hfiber {X Y} (f : X -> Y) (y : Y)
       `{Finite X} `{Finite Y}
: Finite (hfiber f y).
Proof.
  exact _.
Defined.

(** Therefore, the cardinality of the domain of a map between finite sets is the sum of the cardinalities of its hfibers. *)
Definition fcard_domain {X Y} (f : X -> Y) `{Finite X} `{Finite Y}
: fcard X = finplus (fun y => fcard (hfiber f y)).
Proof.
  refine (_ @ fcard_sigma (hfiber f)).
  refine (fcard_equiv' (equiv_fibration_replacement f)).
Defined.
