(* -*- mode: coq; mode: visual-line -*- *)

(** * Liftings and Liftable maps *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp EquivalenceVarieties.
Require Import HoTT.Tactics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** These are the duals of extensions and extendable maps; they are interesting and useful for the same reasons in dual situations. *)

Section Liftings.

  Definition LiftingAlong {A : Type} {B C : A -> Type}
             (f : forall a, B a -> C a) (d : forall a, C a)
    := { s : forall a, B a & forall a, f a (s a) = d a }.
  (** [LiftingAlong] takes 5 universe parameters:
      - the size of A
      - the size of B
      - the size of C
      - >= max(A,B)
      - >= max(A,C).
    The following [Check] verifies that this is in fact the case. *)
  Check LiftingAlong@{a b p m n}.
  (** If necessary, we could coalesce the latter two with a universe annotation, but that would make the definition harder to read. *)

  (** Here is the iterated version. *)

  Fixpoint LiftableAlong (n : nat)
           {A : Type@{i}} {B : A -> Type@{j}} {C : A -> Type@{k}}
           (f : forall a, B a -> C a)
  : Type@{l}
    := match n with
         | 0 => Unit@{l}
         | S n => (forall (g : forall a, C a),
                     LiftingAlong@{i j k l l} f g) *
                  forall (h k : forall a, B a),
                    LiftableAlong n (fun (a:A) (p : h a = k a) => ap (f a) p)
       end.
  Set Printing Universes.
  (** [LiftableAlong] takes 4 universe parameters:
      - size of A
      - size of B
      - size of C
      - size of result (>= A,B,C) *)
  Check LiftableAlong@{a b c r}.

(*
  Definition equiv_extendable_pathsplit `{Funext} (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n f C
    <~> PathSplit n (fun (g : forall b, C b) => g oD f).
  Proof.
    generalize dependent C; simple_induction n n IHn; intros C.
    1:apply equiv_idmap.
    apply equiv_functor_prod'; simpl.
    - refine (equiv_functor_forall' (equiv_idmap _) _); intros g; simpl.
      refine (equiv_functor_sigma' (equiv_idmap _) _); intros rec.
      apply equiv_path_forall.
    - refine (equiv_functor_forall' (equiv_idmap _) _); intros h.
      refine (equiv_functor_forall' (equiv_idmap _) _); intros k; simpl.
      refine (equiv_compose' _ (IHn (fun b => h b = k b))).
      apply equiv_inverse.
      refine (equiv_functor_pathsplit n _ _
               (equiv_apD10 _ _ _) (equiv_apD10 _ _ _) _).
      intros []; reflexivity.
  Defined.

  Definition isequiv_extendable `{Funext} (n : nat)
             {A B : Type} {C : B -> Type} {f : A -> B}
  : ExtendableAlong n.+2 f C
    -> IsEquiv (fun g => g oD f)
    := isequiv_pathsplit n o (equiv_extendable_pathsplit n.+2 C f).

  Global Instance ishprop_extendable `{Funext} (n : nat)
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ExtendableAlong n.+2 f C).
  Proof.
    refine (trunc_equiv' _ (equiv_inverse (equiv_extendable_pathsplit n.+2 C f))).
  Defined.

  Definition equiv_extendable_isequiv `{Funext} (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n.+2 f C
    <~> IsEquiv (fun (g : forall b, C b) => g oD f).
  Proof.
    etransitivity.
    - apply equiv_extendable_pathsplit.
    - apply equiv_pathsplit_isequiv.
  Defined.

  (** Postcomposition with a known equivalence.  Note that this does not require funext to define, although showing that it is an equivalence would require funext. *)
  Definition extendable_postcompose' (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b <~> D b)
  : ExtendableAlong n f C -> ExtendableAlong n f D.
  Proof.
    generalize dependent C; revert D.
    simple_induction n n IH; intros C D g; simpl.
    1:apply idmap.
    refine (functor_prod _ _).
    - refine (functor_forall (functor_forall idmap
                                             (fun a => (g (f a))^-1)) _);
      intros h; simpl.
      refine (functor_sigma (functor_forall idmap g) _); intros k.
      refine (functor_forall idmap _);
        intros a; unfold functor_arrow, functor_forall, composeD; simpl.
      apply moveR_equiv_M.
    - refine (functor_forall (functor_forall idmap (fun b => (g b)^-1)) _);
      intros h.
      refine (functor_forall (functor_forall idmap (fun b => (g b)^-1)) _);
        intros k; simpl; unfold functor_forall.
      refine (IH _ _ _); intros b.
      apply equiv_inverse, equiv_ap; exact _.
  Defined.

  Definition extendable_postcompose (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ExtendableAlong n f C -> ExtendableAlong n f D
    := extendable_postcompose' n C D f (fun b => BuildEquiv _ _ (g b) _).

  (** Composition of the maps we extend along.  This also does not require funext. *)
  Definition extendable_compose (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n g P -> ExtendableAlong n f (fun b => P (g b)) -> ExtendableAlong n (g o f) P.
  Proof.
    revert P; simple_induction n n IHn; intros P extg extf; [ exact tt | split ].
    - intros h.
      exists ((fst extg (fst extf h).1).1); intros a.
      refine ((fst extg (fst extf h).1).2 (f a) @ _).
      exact ((fst extf h).2 a).
    - intros h k.
      apply IHn.
      + exact (snd extg h k).
      + exact (snd extf (h oD g) (k oD g)).
  Defined.

  (** And cancellation *)
  Definition cancelL_extendable (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n g P -> ExtendableAlong n (g o f) P -> ExtendableAlong n f (fun b => P (g b)).
  Proof.
    revert P; simple_induction n n IHn; intros P extg extgf; [ exact tt | split ].
    - intros h.
      exists ((fst extgf h).1 oD g); intros a.
      exact ((fst extgf h).2 a).
    - intros h k.
      pose (h' := (fst extg h).1).
      pose (k' := (fst extg k).1).
      refine (extendable_postcompose' n (fun b => h' (g b) = k' (g b)) (fun b => h b = k b) f _ _).
      + intros b.
        exact (equiv_concat_lr ((fst extg h).2 b)^ ((fst extg k).2 b)).
      + apply (IHn (fun c => h' c = k' c) (snd extg h' k') (snd extgf h' k')).
  Defined.

  Definition cancelR_extendable (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n.+1 f (fun b => P (g b)) -> ExtendableAlong n (g o f) P -> ExtendableAlong n g P.
  Proof.
    revert P; simple_induction n n IHn; intros P extf extgf; [ exact tt | split ].
    - intros h.
      exists ((fst extgf (h oD f)).1); intros b.
      refine ((fst (snd extf ((fst extgf (h oD f)).1 oD g) h) _).1 b); intros a.
      apply ((fst extgf (h oD f)).2).
    - intros h k.
      apply IHn.
      + apply (snd extf (h oD g) (k oD g)).
      + apply (snd extgf h k).
  Defined.

  (** And transfer across homotopies *)
  Definition extendable_homotopic (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B) {g : A -> B} (p : f == g)
  : ExtendableAlong n f C -> ExtendableAlong n g C.
  Proof.
    revert C; simple_induction n n IHn; intros C extf; [ exact tt | split ].
    - intros h.
      exists ((fst extf (fun a => (p a)^ # h a)).1); intros a.
      refine ((apD ((fst extf (fun a => (p a)^ # h a)).1) (p a))^ @ _).
      apply moveR_transport_p.
      exact ((fst extf (fun a => (p a)^ # h a)).2 a).
    - intros h k.
      apply IHn, (snd extf h k).
  Defined.

  (** We can extend along equivalences *)
  Definition extendable_equiv (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B) `{IsEquiv _ _ f}
  : ExtendableAlong n f C.
  Proof.
    revert C; simple_induction n n IHn; intros C; [ exact tt | split ].
    - intros h.
      exists (fun b => eisretr f b # h (f^-1 b)); intros a.
      refine (transport2 C (eisadj f a) _ @ _).
      refine ((transport_compose C f _ _)^ @ _).
      exact (apD h (eissect f a)).
    - intros h k.
      apply IHn.
  Defined.

  (** And into contractible types *)
  Definition extendable_contr (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
             `{forall b, Contr (C b)}
  : ExtendableAlong n f C.
  Proof.
    generalize dependent C; simple_induction n n IHn;
      intros C ?; [ exact tt | split ].
    - intros h.
      exists (fun _ => center _); intros a.
      apply contr.
    - intros h k.
      apply IHn; exact _.
  Defined.

  (** This is inherited by types of homotopies. *)
  Definition extendable_homotopy (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
             (h k : forall b, C b)
  : ExtendableAlong n.+1 f C -> ExtendableAlong n f (fun b => h b = k b).
  Proof.
    revert C h k; simple_induction n n IHn;
      intros C h k ext; [exact tt | split].
    - intros p.
      exact (fst (snd ext h k) p).
    - intros p q.
      apply IHn, ext.
  Defined.
*)

  (** And the oo-version. *)

  Definition ooLiftableAlong
             {A : Type@{i}} {B : A -> Type@{j}} {C : A -> Type@{k}}
             (f : forall a, B a -> C a)
  : Type@{l}
    := forall n, LiftableAlong@{i j k l} n f.
  (** Universe parameters are the same as for [LiftableAlong]. *)
  Check ooLiftableAlong@{a b c r}.

(*
  Definition isequiv_ooextendable `{Funext}
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C -> IsEquiv (fun g => g oD f)
    := fun ps => isequiv_extendable 0 (ps 2).

  Definition equiv_ooextendable_pathsplit `{Funext}
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C <~>
    ooPathSplit (fun (g : forall b, C b) => g oD f).
  Proof.
    refine (equiv_functor_forall' (equiv_idmap _) _); intros n.
    apply equiv_extendable_pathsplit.
  Defined.

  Global Instance ishprop_ooextendable `{Funext}
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ooExtendableAlong f C).
  Proof.
    refine (trunc_equiv _ (equiv_ooextendable_pathsplit C f)^-1).
  Defined.

  Definition equiv_ooextendable_isequiv `{Funext}
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C
    <~> IsEquiv (fun (g : forall b, C b) => g oD f).
  Proof.
    eapply equiv_compose'.
    - apply equiv_oopathsplit_isequiv.
    - apply equiv_ooextendable_pathsplit.
  Defined.

  Definition ooextendable_postcompose
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ooExtendableAlong f C -> ooExtendableAlong f D
    := fun ppp n => extendable_postcompose n C D f g (ppp n).

  Definition ooextendable_compose
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong f (fun b => P (g b)) -> ooExtendableAlong (g o f) P
    := fun extg extf n => extendable_compose n P f g (extg n) (extf n).

  Definition cancelL_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong (g o f) P -> ooExtendableAlong f (fun b => P (g b))
  := fun extg extgf n => cancelL_extendable n P f g (extg n) (extgf n).

  Definition cancelR_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong f (fun b => P (g b)) -> ooExtendableAlong (g o f) P -> ooExtendableAlong g P
    := fun extf extgf n => cancelR_extendable n P f g (extf n.+1) (extgf n).

  Definition ooextendable_homotopic
             {A B : Type} (C : B -> Type) (f : A -> B) {g : A -> B} (p : f == g)
  : ooExtendableAlong f C -> ooExtendableAlong g C
    := fun extf n => extendable_homotopic n C f p (extf n).

  Definition ooextendable_equiv
             {A B : Type} (C : B -> Type) (f : A -> B) `{IsEquiv _ _ f}
  : ooExtendableAlong f C
  := fun n => extendable_equiv n C f.

  Definition ooextendable_contr
             {A B : Type} (C : B -> Type) (f : A -> B)
             `{forall b, Contr (C b)}
  : ooExtendableAlong f C
  := fun n => extendable_contr n C f.

  Definition ooextendable_homotopy
             {A B : Type} (C : B -> Type) (f : A -> B)
             (h k : forall b, C b)
  : ooExtendableAlong f C -> ooExtendableAlong f (fun b => h b = k b).
  Proof.
    intros ext n; apply extendable_homotopy, ext.
  Defined.

  (** Extendability of a family [C] along a map [f] can be detected by extendability of the constant family [C b] along the projection from the corresponding fiber of [f] to [Unit].  Note that this is *not* an if-and-only-if; the hypothesis can be genuinely stronger than the conclusion. *)
  Definition ooextendable_isnull_fibers {A B} (f : A -> B) (C : B -> Type)
  : (forall b, ooExtendableAlong (@const (hfiber f b) Unit tt)
                                 (fun _ => C b))
    -> ooExtendableAlong f C.
  Proof.
    intros orth n; revert C orth.
    induction n as [|n IHn]; intros C orth; [exact tt | split].
    - intros g.
      exists (fun b => (fst (orth b 1%nat) (fun x => x.2 # g x.1)).1 tt).
      intros a.
      rewrite (path_unit tt (const tt a)).
      exact ((fst (orth (f a) 1%nat) _).2 (a ; 1)).
    - intros h k.
      apply IHn; intros b.
      apply ooextendable_homotopy, orth.
  Defined.
*)

End Liftings.
