Add LoadPath "..".
Require Export Homotopy ReflectiveSubfibration.

(** We now add to the notion of a reflective subfibration one further
   axiom, which ensures that it is determined by a (pullback-stable)
   factorization system (E,M).

   Semantically, the necessary axiom is that the right class M
   (namely, the maps which lie in the reflective subcategory of the
   slice over their codomain) is closed under composition.  We express
   that internally, in the language which appears to be talking about
   a mere reflective subcategory, as follows.
   *)

Class factsys (in_rsc : Type -> Type) {is_rsf : rsf in_rsc} := {
  sum_in_rsc : forall X (P : X -> Type),
    in_rsc X -> (forall x, in_rsc (P x)) -> in_rsc (sigT P)
  }.

Section FactorizationSystem1.

  Context {in_rsc : Type -> Type}.
  Context {is_rsf : rsf in_rsc}.
  Context {is_factsys : factsys in_rsc}.
  Existing Instance is_rsf.
  Existing Instance is_factsys.

  Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc exp_in_rsc sum_in_rsc.

  (** A few immediate consequences that are useful. *)

  Definition is_contr_in_rsc A : in_rsc A -> in_rsc (is_contr A).
  Proof.
    unfold is_contr; auto.
  Defined.

  Hint Resolve is_contr_in_rsc.

  Definition is_equiv_in_rsc A B (f:A->B) :
    in_rsc A -> in_rsc B -> in_rsc (is_equiv f).
  Proof.
    unfold is_equiv, is_contr, hfiber.
    auto 7.
  Defined.

  Hint Resolve is_equiv_in_rsc.
  
  Definition equiv_in_rsc A B :
    in_rsc A -> in_rsc B -> in_rsc (A <~> B).
  Proof.
    unfold equiv; auto.
  Defined.

  Hint Resolve equiv_in_rsc.

  Definition is_hlevel_in_rsc (n:nat) :
    forall A, in_rsc A -> in_rsc (is_hlevel n A).
  Proof.
    induction n; [ simpl; auto | simpl; auto using IHn ].
  Defined.

  Hint Resolve is_hlevel_in_rsc.

  (** The most important consequence of this axiom (and one which is,
     as we will see, equivalent to it) is that we have a *dependent*
     version of factorization (and hence of functoriality). *)

  Section DependentFactor.

    Hypothesis X : Type.
    Hypothesis P : reflect X -> Type.
    Hypothesis Pr : forall x, in_rsc (P x).
    Hypothesis f : forall x, P (to_reflect X x).

    Let fdep (x:X) : sigT P := (to_reflect X x; f x).

    Let rfdep : reflect X -> sigT P.
    Proof.
      apply reflect_factor; auto.
    Defined.

    Let rfdep_factors (x:X) : rfdep (to_reflect X x) == fdep x.
    Proof.
      apply @reflect_factor_factors with (f := fdep).
    Defined.

    Let rfdep_section (rx : reflect X) : pr1 (rfdep rx) == rx.
    Proof.
      path_via (reflect_factor (reflect_in_rsc X) (pr1 o fdep) rx).
      apply reflect_factoriality_pre.
      unfold compose; simpl.
      apply @reflect_factor_unfactors with (f := idmap (reflect X)).
    Defined.

    Let rfdep_section_factors (x:X) :
      rfdep_section (to_reflect X x) == map pr1 (rfdep_factors x).
    Proof.
      unfold rfdep_factors, rfdep_section.
      apply @concat with (y := reflect_factoriality_pre
        (sum_in_rsc (reflect X) P (reflect_in_rsc X) Pr)
        (reflect_in_rsc X) pr1 fdep (to_reflect X x)
        @
        reflect_factor_factors (reflect_in_rsc X)
        (idmap _ o to_reflect X) x).
      apply whisker_left.
      apply reflect_factor_factunfact.
      unfold compose, idmap.
      apply @reflect_factoriality_pre_factors with
        (f := fdep).
    Defined.

    Definition reflect_factor_dep : (forall rx, P rx).
    Proof.
      intros rx.
      apply (transport (rfdep_section rx)).
      exact (pr2 (rfdep rx)).
    Defined.

    Definition reflect_factor_dep_factors (x:X) :
      reflect_factor_dep (to_reflect X x) == f x.
    Proof.
      unfold reflect_factor_dep.
      path_via (transport (map pr1 (rfdep_factors x))
        (pr2 (rfdep (to_reflect X x)))).
      apply happly, map, rfdep_section_factors.
      apply fiber_path with (p := rfdep_factors x).
    Defined.

  End DependentFactor.
  
  Definition reflect_functor_dep {X} {P : reflect X -> Type}
    : (forall x, P (to_reflect X x)) -> (forall rx, reflect (P rx)).
  Proof.
    intros f.
    apply reflect_factor_dep with (X := X).
    intros rx; apply reflect_in_rsc.
    intros x; apply to_reflect; auto.
  Defined.

End FactorizationSystem1.

(** We now prove that dependent elimination, with its computation
   rule, can be used as part of the definition.  In this presentation,
   [reflect X] looks very much like an inductive type generated by a
   constructor [to_reflect : X -> reflect X] together with a vague
   property of "reflectedness".  It can also be described as a sort of
   "higher modality" which acts on types in addition to propositions.

   For good measure, we also exploit the fact that [in_rsc] can be
   recovered, up to equivalence, from [reflect] and [to_reflect].  We
   do, however, need to assert separately that the reflector takes
   values in the subcategory, and that the subcategory is closed under
   path-spaces.  (Any chance those hypotheses can be eliminated?)
   *)

Section Modality.

  Hypothesis modal : Type -> Type.

  Hypothesis to_modal : forall X, X -> modal X.

  Definition is_modal X := is_equiv (to_modal X).

  Hypothesis modal_is_modal : forall X, is_modal (modal X).

  Hypothesis paths_are_modal : forall X (x0 x1 : X),
    is_modal X -> is_modal (x0 == x1).

  Hypothesis modal_rect : forall X (P : modal X -> Type),
    (forall mx, is_equiv (to_modal (P mx))) ->
    (forall x, P (to_modal X x)) -> (forall mx, P mx).

  Hypothesis modal_rect_compute : forall X (P : modal X -> Type)
    (Pm : forall mx, is_equiv (to_modal (P mx))) (f : forall x, P (to_modal X x)),
    (forall x, modal_rect X P Pm f (to_modal X x) == f x).

  Program Instance modal_rsf : rsf (is_modal).
  Next Obligation.
    intros; apply is_equiv_is_prop.
  Defined.
  Next Obligation.
    exact modal.
  Defined.
  Next Obligation.
    intros X. unfold modal_rsf_obligation_2.
    apply modal_is_modal.
  Defined.
  Next Obligation.
    intros X x.
    unfold modal_rsf_obligation_2.
    exact (to_modal X x).
  Defined.
  Next Obligation.
    intros X Y Ym.
    unfold modal_rsf_obligation_2, modal_rsf_obligation_4.
    apply hequiv_is_equiv with
      (g := modal_rect X (fun _ => Y) (fun _ => Ym)).
    intros f. apply funext; intros x. unfold compose.
    apply modal_rect_compute with (P := (fun _ : modal X => Y)).
    intros g. apply funext; intros x.  unfold compose.
    pattern x. apply modal_rect.
    intros mx; apply paths_are_modal; assumption.
    intros x'.
    apply modal_rect_compute with
      (P := (fun _ : modal X => Y))
      (f := (fun x0 : X => g (to_modal X x0))).
  Defined.

End Modality.

(** Now we define some tactics to work automatically with
   [reflect_factor_dep] and [reflect_factor_dep_factors].

   The following tactic takes as one argument a hypothesis of type
   [reflect X] and applies [reflect_factor_dep] to change that
   hypothesis into one of type [X].  Of course, this requires the goal
   to be [in_rsc].  The tactic tries to prove this with [auto], which
   should succeed in most cases if the appropriate facts are in the
   hint database.  *)

Ltac unreflect A :=
  generalize dependent A;
  intros A;
  pattern A;
  apply reflect_factor_dep;
  [ auto | clear A; intro A].

(* A helper tactic for the next one. *)

Ltac unreflect_compute_in s :=
  match s with
    | appcontext cxt [ reflect_factor_dep ?X0 ?P0 ?Pr0 ?f0 (to_reflect _ ?x0) ] =>
      let h := fresh in
        set (h := f0);
        let mid := context cxt[h x0] in
          path_via' mid;
          [ repeat apply_happly;
            apply @reflect_factor_dep_factors with
              (X := X0) (P := P0) (Pr := Pr0) (f := f0) (x := x0)
            | unfold h; clear h ]
  end.

(** The following tactic looks for places in the goal (assumed to be an
   equality/path type) where it can apply [reflect_factor_dep_factors],
   and does so.

   A good practice is to whenever you define a new term using
   [unreflect], immediately prove a lemma using [unreflect_compute]
   saying what it evaluates to when applied to inputs in the image of
   [to_reflect].  It is usually much easier to prove these lemmas
   piecemeal, one for each new operation, and then assemble them later
   when needed. *)

Ltac unreflect_compute :=
  repeat (
    match goal with
      |- ?s == ?t => first [ unreflect_compute_in s | unreflect_compute_in t ]
    end
  ); auto.

(** Now we return to proving general properties of a factorization system. *)

Section FactorizationSystem2.

  Context {in_rsc : Type -> Type}.
  Context {is_rsf : rsf in_rsc}.
  Context {is_factsys : factsys in_rsc}.
  Existing Instance is_rsf.
  Existing Instance is_factsys.

  Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc exp_in_rsc sum_in_rsc.
  Hint Resolve is_contr_in_rsc is_equiv_in_rsc equiv_in_rsc is_hlevel_in_rsc.

  (** The reflector preserves h-propositions. *)

  Definition reflect_preserves_props A : is_prop A -> is_prop (reflect A).
  Proof.
    intros Ap; apply allpath_prop; intros x y.
    unreflect x; unreflect y.
    apply map, prop_path; assumption.
  Defined.

  (** Over a base object that is in the subcategory, the "fiberwise
     reflection" is equivalent to reflecting the total space. *)

  Section ReflectFiberwise.

    Hypothesis X : Type.
    Hypothesis P : X -> Type.
    Hypothesis Xr : in_rsc X.

    Let rf1 : {x:X & reflect (P x)} -> (reflect (sigT P)).
    Proof.
      intros [x p]; unreflect p.
      exact (to_reflect _ (x;p)).
    Defined.

    Let rf1_compute (x:X) (p:P x) :
      rf1 (x ; to_reflect _ p) == to_reflect _ (x ; p).
    Proof.
      unfold rf1; unreflect_compute.
    Defined.

    Let rf2 : (reflect (sigT P)) -> {x:X & reflect (P x)}.
    Proof.
      intros xp; unreflect xp; destruct xp as [x p].
      exact (x ; to_reflect _ p).
    Defined.

    Let rf2_compute (xp : sigT P) :
      rf2 (to_reflect _ xp) == (pr1 xp ; to_reflect _ (pr2 xp)).
    Proof.
      unfold rf2; unreflect_compute.
      destruct xp; auto.
    Defined.

    Definition reflect_functor_fiberwise  :
      {x:X & reflect (P x)} <~> (reflect (sigT P)).
    Proof.
      exists rf1.
      apply hequiv_is_equiv with (g := rf2).
      intros rx; unreflect rx.
      destruct rx as [x p].
      path_via (rf1 (x ; to_reflect _ p)).
      apply rf2_compute.
      intros [x p]; unreflect p.
      path_via (rf2 (to_reflect _ (x ; p))).
      apply rf2_compute.
    Defined.

  End ReflectFiberwise.

  (** Now we define the two classes in the factorization system. *)

  (** A map is in M if all its homotopy fibers are in the subcategory. *)
  Definition in_M {X Y} (f : X -> Y) : Type
    := forall y, in_rsc {x:X & f x == y}.

  (** A map is in E if all its homotopy fibers become contractible upon
     reflection into the subcategory. *)
  Definition in_E {X Y} (f : X -> Y) : Type
    := forall y, is_contr (reflect {x:X & f x == y}).

  Definition Mmap X Y := { f : X -> Y & in_M f }.
  Definition Mmap_coerce_to_function X Y (f : Mmap X Y) : (X -> Y) := projT1 f.
  Coercion Mmap_coerce_to_function : Mmap >-> Funclass.

  Definition Emap X Y := { f : X -> Y & in_E f }.
  Definition Emap_coerce_to_function X Y (f : Emap X Y) : (X -> Y) := projT1 f.
  Coercion Emap_coerce_to_function : Emap >-> Funclass.

  (** Any equivalence is in E. *)
  Definition equiv_Emap {X Y} (f : X <~> Y) : Emap X Y.
  Proof.
    exists f.
    intros y.
    apply contr_equiv_contr with unit.
    apply @equiv_compose with (reflect unit).
    apply in_rsc_reflect_equiv. auto.
    apply reflect_functor_equiv.
    apply equiv_inverse, contr_equiv_unit.
    apply (pr2 f). auto.
  Defined.

  (** Likewise, any equivalence is in M. *)
  Definition equiv_Mmap {X Y} (f : X <~> Y) : Mmap X Y.
  Proof.
    exists f.
    intros y.
    apply @transport with (P := in_rsc) (x := unit).
    apply opposite, equiv_to_path, contr_equiv_unit.
    apply (pr2 f).
    auto.
  Defined.

  (** Any map between objects in the subcategory is in M. *)
  Definition map_in_rsc_in_M {X Y} (f : X -> Y) :
    in_rsc X -> in_rsc Y -> in_M f.
  Proof.
    intros Xr Yr y.
    auto.
  Defined.

  Definition map_in_rsc_Mmap {X Y} (f : X -> Y) (Xr : in_rsc X) (Yr : in_rsc Y)
    : Mmap X Y
    := (existT in_M f (map_in_rsc_in_M f Xr Yr)).

  (** A map that is inverted by the reflector, and whose codomain is
     in the subcategory, belongs to E.  (It is not true, in this
     generality, that *any* map inverted by the reflector is in E.)
     That is equivalent to the factorization system being reflective.
     *)
  Section InvertedInE.

    Hypothesis X Y : Type.
    Hypothesis Yr : in_rsc Y.
    Hypothesis f : X -> Y.
    Hypothesis rfeq : is_equiv (reflect_factor Yr f).

    Let Pf := {y:Y & {x:X & f x == y}}.
    Let XtoPf := fibration_replacement_equiv X Y f : equiv X Pf.
    Let PftoY := pr1 : Pf -> Y.

    Let PftoYeq : is_equiv (reflect_factor Yr PftoY).
    Proof.
      apply @equiv_cancel_right with
        (A := reflect X)
        (f := reflect_functor_equiv XtoPf).
      assert (cf : PftoY o XtoPf == f).
      apply funext. unfold PftoY, XtoPf. intros x.
      apply fibration_replacement_factors.
      assert (rcf : reflect_factor Yr PftoY o reflect_functor_equiv XtoPf
        == reflect_factor Yr f).
      path_via (reflect_factor Yr (PftoY o XtoPf)).
      apply funext.  intros rx.
      path_via (reflect_factor Yr PftoY (reflect_functor XtoPf rx)).
      apply reflect_factoriality_post.
      apply (transport (!rcf)).
      assumption.
    Defined.

    Let Qf := {y:Y & reflect {x:X & f x == y}}.

    Let QftoYeq : equiv Qf Y.
    Proof.
      apply @equiv_compose with (B := reflect Pf).
      apply reflect_functor_fiberwise. auto.
      exists (reflect_factor Yr PftoY). auto.
    Defined.

    Let QftoYispr1 (z : Qf) : QftoYeq z == pr1 z.
    Proof.
      destruct z as [y xp].
      unreflect xp.
      simpl. unfold compose.
      path_via (reflect_factor Yr PftoY (to_reflect _ (y ; xp))).
      unreflect_compute.
      apply reflect_factor_factors.
    Defined.
    
    Definition inverted_to_rsc_in_E : in_E f.
    Proof.
      set (hfcontr := pr2 QftoYeq).
      unfold in_E.
      intros y.
      assert (fibeq : reflect {x : X & f x == y} == hfiber (pr1 QftoYeq) y).
      unfold hfiber.
      path_via ({x : Qf & pr1 x == y}).
      apply equiv_to_path.
      unfold Qf, QftoYeq.
      apply hfiber_fibration with
        (P := fun y' => reflect { x:X & f x == y' })
        (x := y).
      apply funext. intros q.
      apply @map with (f := (fun r => r == y)).
      apply opposite, QftoYispr1.
      apply (transport (!fibeq)).
      apply hfcontr.
      (* Oh noes!  Universe inconsistency! *)
    Defined.

  End InvertedInE.

  (** In particular, the unit of the reflector is always in E. *)
  Definition to_reflect_in_E X : in_E (to_reflect X).
  Proof.
    apply inverted_to_rsc_in_E with
      (Y := reflect X)
      (Yr := reflect_in_rsc X).
    assert (p : @id (reflect X) == reflect_factor (reflect_in_rsc X) (to_reflect X)).
    path_via (reflect_factor (reflect_in_rsc X) ((@id (reflect X) o to_reflect X))).
    apply opposite.  apply funext.  intros x. apply reflect_factor_unfactors.
    apply funext; intros x; auto.
    apply (transport p).
    apply (pr2 (idequiv _)).
  Defined.

  Definition to_reflect_Emap X :=
    existT in_E (to_reflect X) (to_reflect_in_E X).

  (** E and M are homotopy orthogonal to each other. *)
  Section EMOrth.

    (** A commutative square with an E on the left and an M on the right. *)
    Context {X Y Z W : Type}.
    Hypothesis e : Emap X Y.
    Hypothesis m : Mmap Z W.
    Hypothesis f : X -> Z.
    Hypothesis g : Y -> W.

    Definition square_lift :=
      { h : Y -> Z &
        { lower : forall y, m (h y) == g y &
          forall x, h (e x) == f x }}.

    Definition square_lift_to_square :
      square_lift -> (forall x, m (f x) == g (e x)).
    Proof.
      intros [h [lower upper]] x.
      path_via (m (h (e x))).
    Defined.

    Section AssumeS.

      Hypothesis s : forall x, m (f x) == g (e x).

      (** We construct a lift simultaneously with a homotopy in the lower
         triangle. *)

      Let EMlift_tot (y:Y) : {z:Z & m z == g y}.
      Proof.
        set (xp := pr1 (pr2 e y)).
        unreflect xp.
        intros; apply (pr2 m).
        destruct xp as [x p].
        exists (f x).
        path_via (g (e x)).
      Defined.

      Definition EMlift (y:Y) : Z := pr1 (EMlift_tot y).

      Definition EMlift_lowertri (y:Y) : m (EMlift y) == g y :=
        pr2 (EMlift_tot y).

      (** Then we extract the upper triangle simultaneously with a proof
         that the two triangles compose to the given square. *)

      Let EMlift_uppertri_plus (x : X) :
        EMlift_tot (e x) == (f x ; s x).
      Proof.
        unfold EMlift_tot.
        path_via (reflect_factor_dep
          {x0 : X & pr1 e x0 == e x}
          (fun _ => {z : Z & m z == g (e x)})
          (fun _ => pr2 m (g (e x)))
          (fun xp => let (x0, p0) := xp in (f x0 ; s x0 @ map g p0))
          (to_reflect _ (x ; idpath (e x)))).
        apply contr_path.  apply (pr2 e).
        unreflect_compute.
        apply map.
        cancel_units.
      Defined.

      Definition EMlift_uppertri (x:X) : EMlift (e x) == f x :=
        base_path (EMlift_uppertri_plus x).

      Definition EMlift_square : square_lift :=
        (EMlift ; ( EMlift_lowertri ; EMlift_uppertri )).

      Definition EMlift_lifts : square_lift_to_square EMlift_square == s.
      Proof.
        unfold square_lift_to_square, EMlift_square.
        apply funext_dep; intros x.
        path_via (transport
          (base_path (EMlift_uppertri_plus x))
          (pr2 (EMlift_tot (e x)))).
        path_via (transport
          (P := fun w => w == g (e x))
          (x := m (pr1 (EMlift_tot (e x))))
          (y := m (pr1 (f x ; s x)))
          (map m (base_path (EMlift_uppertri_plus x)))
          (pr2 (EMlift_tot (e x)))).
        do_opposite_map.
        apply opposite, trans_is_concat_opp.
        apply opposite.
        apply @map_trans with (P := fun w => w == g (e x)).
        exact (fiber_path (EMlift_uppertri_plus x)).
      Defined.

    End AssumeS.

    (** So far we have just shown that a lift exists.  We should really prove
       that it is unique, and in fact homotopy unique (i.e. the space
       of such lifts is contractible).  But we won't. *)

  End EMOrth.

  (** Orthogonality lets us prove easily that E-maps are inverted by
     the reflector.  (Again, the converse is not true in this generality.) *)
  Section EInverted.

    Hypothesis (X Y:Type) (f : Emap X Y).

    Let rfm : Mmap (reflect X) (reflect Y) :=
      (map_in_rsc_Mmap (reflect_functor f) (reflect_in_rsc X) (reflect_in_rsc Y)).

    Let invert : reflect Y -> reflect X.
    Proof.
      apply @reflect_factor with (X:=Y). auto.
      apply @EMlift with (e := f) (m := rfm)
        (f := to_reflect X) (g := to_reflect Y).
      intros x.
      path_via (reflect_functor f (to_reflect X x)).
      apply reflect_naturality.
    Defined.

    Definition E_inverted : is_equiv (reflect_functor f).
    Proof.
      apply hequiv_is_equiv with invert.
      intros y; unreflect y.
      unfold invert.
      path_via (rfm
        (EMlift f rfm (to_reflect X) (to_reflect Y)
           (fun x : X =>
            map (reflect_functor f) (map (to_reflect X) (idpath x)) @
            reflect_naturality f x) y)).
      apply reflect_factor_factors.
      apply @EMlift_lowertri with
        (e := f)
        (m := rfm)
        (f := to_reflect X)
        (g := to_reflect Y).
      intros x; unreflect x.
      path_via (invert (to_reflect Y (f x))).
      apply reflect_naturality.
      unfold invert.
      path_via ((EMlift f rfm (to_reflect X) (to_reflect Y)
        (fun x0 : X =>
         map (reflect_functor f) (map (to_reflect X) (idpath x0)) @
         reflect_naturality f x0)) (f x)).
      apply reflect_factor_factors.
      apply EMlift_uppertri.
    Defined.

    Definition invert_E : reflect X <~> reflect Y
      := (reflect_functor f ; E_inverted).

  End EInverted.

  (** In particular, if an E-map has target in the subcategory, then
     its factorization is an equivalence. *)
  Definition Emap_invert_factor (X Y:Type) (f : Emap X Y) :
    in_rsc Y -> (reflect X <~> Y).
  Proof.
    intros Yr.
    exists (reflect_factor Yr f).
    apply equiv_cancel_left with (g := in_rsc_reflect_equiv Y Yr).
    apply @transport with (x := reflect_functor f).
    simpl. apply opposite, reflect_factor_functor.
    apply E_inverted.
  Defined.

  (** In particular, that means that given an E-map between any two
     objects, one reflects to a point iff the other does. *)
  Definition Emap_punctual_codomain X Y : Emap X Y ->
    is_contr (reflect X) -> is_contr (reflect Y).
  Proof.
    intros f Xc.
    apply contr_equiv_contr with (A := reflect X).
    apply invert_E; auto.
    auto.
  Defined.

  Definition Emap_punctual_domain X Y : Emap X Y ->
    is_contr (reflect Y) -> is_contr (reflect X).
  Proof.
    intros f Yc.
    apply contr_equiv_contr with (A := reflect Y).
    apply equiv_inverse, invert_E; auto.
    auto.
  Defined.

  (** Therefore, if f is in E, then so is the induced map from the
     homotopy fiber of (g o f) to the homotopy fiber of g. *)
  Definition fibermap_in_E {X Y Z} (f : Emap X Y) (g : Y -> Z) (z : Z) :
    in_E (composite_fiber_map f g z).
  Proof.
    intros [y' p].
    apply @contr_equiv_contr with (reflect {x:X & f x == y'}).
    apply reflect_functor_equiv.
    apply equiv_inverse, fiber_of_fibers.
    apply (pr2 f).
  Defined.

  (** This lets us show that E-maps compose. *)
  Definition Emap_compose {X Y Z} (f : Emap X Y) (g : Emap Y Z) :
    Emap X Z.
  Proof.
    exists (g o f).
    intros z.
    apply Emap_punctual_domain with
      (Y := {y:Y & g y == z}).
    exists (composite_fiber_map f g z).
    apply fibermap_in_E.
    apply (pr2 g).
  Defined.

  (** And cancel on one side. *)
  Definition Emap_cancel_right {X Y Z} (f : Emap X Y) (g : Y -> Z) :
    in_E (g o f) -> in_E g.
  Proof.
    intros gine.
    intros z.
    apply Emap_punctual_codomain with
      (X := {x:X & g (f x) == z}).
    exists (composite_fiber_map f g z).
    apply fibermap_in_E.
    apply gine.
  Defined.

  (** And over a base map in E, if all fiber maps are in E, so is the
     map on total spaces.  *)
  Section EMapFiber.

    Hypotheses A B C D : Type.
    Hypotheses (f:A->B) (g : C -> D) (h:A->C) (k : Emap B D).
    Hypothesis s:forall a, k (f a) == g (h a).

    Hypothesis fibfge : forall b, in_E (square_fiber_map f g h k s b).

    Theorem total_map_ine : in_E h.
    Proof.
      intros c.
      assert (fibhke : in_E (square_fiber_map h k f g (fun a => !s a) c)).
      intros [b p].
      set (eq := three_by_three A B C D f g h k s b c p).
      apply (contr_equiv_contr _ _ (reflect_functor_equiv eq)).
      apply fibfge.
      apply Emap_punctual_domain with
        (Y := {b:B & k b == g c}).
      exists (square_fiber_map h k f g (fun a : A => !s a) c).
      assumption.
      apply (pr2 k).
    Defined.

  End EMapFiber.

  (** The same thing, for maps given as fibrations. *)
  Section EMapFiberFibrations.

    Hypothesis A B : Type.
    Hypothesis (P : A -> Type) (Q : B -> Type).
    Hypothesis f : Emap A B.
    Hypothesis g : forall x, Emap (P x) (Q (f x)).

    Theorem total_emap_fib : Emap (sigT P) (sigT Q).
    Proof.
      exists (total_map f g).
      intros [b q].
      set (eq := three_by_three_fib _ _ _ _ f g b q).
      apply (contr_equiv_contr _ _ (reflect_functor_equiv eq)).
      apply Emap_punctual_domain with (Y := {a:A & f a == b}).
      exists pr1.
      intros [a s].
      set (eq2 := hfiber_fibration {x:A & f x == b}
        (fun xs => let (x, s0) := xs in {p : P x & transport s0 ((g x) p) == q})
        (a;s)). simpl in eq2.
      apply (contr_equiv_contr _ _ (reflect_functor_equiv eq2)).
      apply contr_equiv_contr with
        (reflect {p : P a & g a p == transport (!s) q}).
      apply reflect_functor_equiv.
      assert (te : forall p:P a,
        ((g a) p == transport (!s) q) <~> (transport s ((g a) p) == q)).
      intros p.
      apply equiv_inverse, transport_adjoint.
      apply total_equiv with te.
      intros p; apply (pr2 (te p)).
      apply (pr2 (g a)).
      apply (pr2 f).
    Defined.

  End EMapFiberFibrations.

  (** Every morphism factors as an E followed by an M. *)
  Section EMFactor.

    Hypothesis X Y : Type.
    Hypothesis f : X -> Y.

    (* The intermediate object we factor through. *)
    Let Z := {y:Y & reflect {x:X & f x == y}}.

    (* The E part *)
    Let e (x:X) : Z :=
      existT (fun y => reflect {x:X & f x == y}) (f x)
      (to_reflect _ (x ; idpath _)).

    (* The M part *)
    Let m : Z -> Y := pr1.

    (* We identify the fiber of e as something more manageable.
       Probably univalence is not necessary for this proof, but it
       makes it easier.  *)
    Let efiber_ident (z : Z) : {x : X & e x == z} ==
      { hf : {x:X & f x == pr1 z} & to_reflect _ hf == pr2 z }.
    Proof.
      destruct z as [y rxp].
      path_via ({x:X & {p : f x == y &
        (transport (P := fun y' => reflect {x':X & f x' == y'}) p
          (to_reflect _ (existT (fun x' => f x' == f x) x (idpath (f x))))
          == rxp)}}).
      apply funext. intros x.
      apply equiv_to_path, total_paths_equiv.
      path_via ({x:X & {p : f x == y &
        (to_reflect _ (existT (fun x' => f x' == y) x p)) == rxp}}).
      apply funext. intros x.
      apply map.
      apply funext. intros p.
      apply @map with (f := fun t => t == rxp).
      apply opposite.
      path_via (to_reflect {x' : X & f x' == y}
        (x ; (transport (P := fun y => f x == y) p (idpath (f x))))).
      apply opposite.
      path_via (idpath (f x) @ p).
      apply @trans_is_concat.
      apply @trans_map with    
        (P := fun (y:Y) => f x == y)
        (Q := fun (y:Y) => reflect {x0:X & f x0 == y})
        (f := fun (y:Y) (r:f x == y) =>
          to_reflect {x0:X & f x0 == y} (x ; r)).
      apply equiv_to_path.
      apply total_assoc_sum with
        (P := fun x => f x == y)
        (Q := fun xp => to_reflect {x' : X & f x' == y} xp == rxp).
    Defined.

    (* The factorization. *)
    Definition EM_factor :
      {Z:Type & {e : Emap X Z & {m : Mmap Z Y & m o e == f}}}.
    Proof.
      exists Z.
      assert (einE : in_E e).
      unfold in_E. intros z.
      apply (transport (P := fun T => is_contr (reflect T)) (!efiber_ident z)).
      destruct z as [y rxp]. simpl.
      apply to_reflect_in_E.
      exists (e ; einE).
      assert (minM: in_M m).
      unfold in_M, m.
      intros y.
      set (q := equiv_to_path
        (hfiber_fibration _ (fun y => reflect {x:X & f x == y}) y)).
      apply (transport (P := in_rsc) q). auto.
      exists (m ; minM).
      apply funext. intros x. unfold m, e; simpl. auto.
    Defined.

  End EMFactor.

End FactorizationSystem2.