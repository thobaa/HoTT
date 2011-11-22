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

Section FactorizationSystem.

  Context {in_rsc : Type -> Type}.
  Context {is_rsf : rsf in_rsc}.
  Context {is_factsys : factsys in_rsc}.
  Existing Instance is_rsf.
  Existing Instance is_factsys.

  Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc exp_in_rsc sum_in_rsc.

  (** We begin with some consequences of this axiom that are still
     expressed in the language of a mere reflective subcategory. 

     First, we can generalize the factorization and functoriality
     properties to the dependent context. *)

  Section DependentFactor.

    Hypothesis X : Type.
    Hypothesis P : reflect X -> Type.
    Hypothesis Pr : forall x, in_rsc (P x).
    Hypothesis f : forall x, P (map_to_reflect X x).

    Let rfdepmap : reflect X -> sigT P.
    Proof.
      intros x.
      apply (inverse (in_rsc_reflect_equiv (sigT P)
        (sum_in_rsc _ P (reflect_in_rsc X) Pr))).
      generalize dependent x.
      apply reflect_functor.
      intros x. exists (map_to_reflect X x). exact (f x).
    Defined.

    Definition reflect_factor_dep : (forall rx, P rx).
    Proof.
      intros rx.
      assert (p : pr1 (rfdepmap rx) == rx).
      unfold rfdepmap.
      path_via (inverse (in_rsc_reflect_equiv (reflect X) (reflect_in_rsc X))
        (reflect_functor pr1
          (reflect_functor (fun x : X => (map_to_reflect X x ; f x)) rx))).
      apply reflect_inverse_naturality.
      equiv_moveright.
      path_via (reflect_functor
        (pr1 o (fun x : X => (map_to_reflect X x ; f x))) rx).
      apply reflect_functoriality.
      path_via (reflect_functor (map_to_reflect X) rx).
      apply @reflect_wellpointed with (X := X).
      apply (transport p).
      exact (pr2 (rfdepmap rx)).
    Defined.

  End DependentFactor.
  
  Definition reflect_functor_dep {X} {P : reflect X -> Type}
    : (forall x, P (map_to_reflect X x)) -> (forall rx, reflect (P rx)).
  Proof.
    intros f.
    apply reflect_factor_dep with (X := X).
    intros rx; apply reflect_in_rsc.
    intros x; apply map_to_reflect; auto.
  Defined.

  (** We can now prove that the reflector preserves finite products. *)

  Section PreservesProducts.
    
    Hypotheses X Y : Type.

    Let reflect_prod_cmp (rxy : reflect (X * Y)) : reflect X * reflect Y
      := (reflect_functor (@fst X Y) rxy, reflect_functor (@snd X Y) rxy).

    Let reflect_prod_map_back (rxry : reflect X * reflect Y)
      : reflect (X * Y)
      := (reflect_factor (reflect_in_rsc (X * Y))
        (fun x : X =>
          reflect_factor (reflect_in_rsc (X * Y))
          (fun y : Y => map_to_reflect (X * Y) (x, y))
          (snd rxry)) (fst rxry)).

    (** Note that [reflect_prod_map_back] could have been defined
       without [sum_in_rsc].  However, it seems that in order to prove
       that it is an inverse to [reflect_prod_cmp], we need dependent
       factorization.  This is similar to the fact that uniqueness of
       recursively defined functions is only provable with a dependent
       eliminator. *)

    (* This proof should be simpler than it is. *)
    Definition reflect_prod_pres : reflect (X * Y) <~> reflect X * reflect Y.
    Proof.
      exists reflect_prod_cmp.
      apply hequiv_is_equiv with (g := reflect_prod_map_back).
      intros [rx ry].
      unfold reflect_prod_cmp, reflect_prod_map_back. simpl.
      generalize dependent ry.
      apply reflect_factor_dep with (X := Y). auto.
      intros y.
      generalize dependent rx.
      apply reflect_factor_dep with (X := X). auto.
      intros x.
      apply prod_path.
      path_via (reflect_functor (@fst X Y)
        (reflect_factor (reflect_in_rsc (X * Y))
          (fun x0 : X =>
            map_to_reflect (X * Y) (x0, y))
          (map_to_reflect X x))).
      apply happly, map, funext. intro x'.
      apply @reflect_factor_factors with 
        (f := fun y0 => map_to_reflect (X * Y) (x', y0)).
      path_via (reflect_functor (@fst X Y)
        (map_to_reflect (X * Y) (x,y))).
      apply @reflect_factor_factors with 
        (f := fun x0 => map_to_reflect (X * Y) (x0, y)).
      apply reflect_naturality.
      path_via (reflect_functor (@snd X Y)
        (reflect_factor (reflect_in_rsc (X * Y))
          (fun x0 : X =>
            map_to_reflect (X * Y) (x0, y))
          (map_to_reflect X x))).
      apply happly, map, funext. intro x'.
      apply @reflect_factor_factors with 
        (f := fun y0 => map_to_reflect (X * Y) (x', y0)).
      path_via (reflect_functor (@snd X Y)
        (map_to_reflect (X * Y) (x,y))).
      apply @reflect_factor_factors with 
        (f := fun x0 => map_to_reflect (X * Y) (x0, y)).
      apply reflect_naturality.
      apply reflect_factor_dep with (X := (X * Y)%type). auto.
      intros [x y].
      unfold reflect_prod_cmp, reflect_prod_map_back. simpl.
      path_via (reflect_factor (reflect_in_rsc (X * Y))
        (fun x0 : X =>
          reflect_factor (reflect_in_rsc (X * Y))
          (fun y0 : Y => map_to_reflect (X * Y) (x0, y0))
          (map_to_reflect Y y))
        (reflect_functor (@fst X Y) (map_to_reflect (X * Y) (x, y)))).
      apply happly, map, funext. intro x'. apply map.
      apply reflect_naturality.
      path_via ( reflect_factor (reflect_in_rsc (X * Y))
        (fun x0 : X => map_to_reflect (X * Y) (x0, y))
        (reflect_functor (@fst X Y) (map_to_reflect (X * Y) (x, y)))).
      apply happly, map, funext. intro x'.
      apply reflect_factor_factors with
        (f := fun y0 : Y => map_to_reflect (X * Y) (x', y0)).
      path_via (reflect_factor (reflect_in_rsc (X * Y))
        ((fun x0 : X => map_to_reflect (X * Y) (x0, y)) o
          (@fst X Y)) (map_to_reflect (X * Y) (x, y))).
      apply reflect_factoriality2.
      path_via (reflect_factor (reflect_in_rsc (X * Y))
        (fun xy : X * Y => map_to_reflect (X * Y) (fst xy, y))
        (map_to_reflect (X * Y) (x, y))).
      apply reflect_factor_factors with
        (f := (fun xy : X * Y => map_to_reflect (X * Y) (fst xy, y))).
    Defined.
    
  End PreservesProducts.

  (** Next, we prove that over a base object that is in the
     subcategory, the "fiberwise reflection" is equivalent to
     reflecting the total space. *)

  Section ReflectFiberwise.

    Hypothesis X : Type.
    Hypothesis P : X -> Type.
    Hypothesis Xr : in_rsc X.

    Let rf1 : {x:X & reflect (P x)} -> (reflect (sigT P)).
    Proof.
      intros [x rp].
      generalize dependent rp.
      apply reflect_functor.
      intros p; exists x; exact p.
    Defined.

    Let rf2 : (reflect (sigT P)) -> {x:X & reflect (P x)}.
    Proof.
      apply reflect_factor.
      apply sum_in_rsc; [assumption | auto].
      intros [x p]; exists x; apply map_to_reflect; assumption.
    Defined.

    (* This proof is far too messy. *)
    Definition reflect_functor_fiberwise  :
      {x:X & reflect (P x)} <~> (reflect (sigT P)).
    Proof.
      exists rf1.
      apply hequiv_is_equiv with (g := rf2).
      intros rx.
      apply reflect_factor_dep with
        (X := sigT P) (P := fun rx => rf1 (rf2 rx) == rx).
      auto.
      intros [x p].
      unfold rf1, rf2.
      assert (H0 :  reflect_factor
       (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0)))
       (fun X0 : sigT P =>
        match X0 return {x0 : X & reflect (P x0)} with
        | (x0 ; p0) => (x0 ; map_to_reflect (P x0) p0)
        end) (map_to_reflect (sigT P) (x ; p))
       == (x ; map_to_reflect (P x) p)).
      apply @reflect_factor_factors with
        (f := (fun X0 : sigT P =>
          match X0 return {x0 : X & reflect (P x0)} with
            | (x0 ; p0) => (x0 ; map_to_reflect (P x0) p0)
          end))
        (x := (x ; p)).
      set (H1 := map (fun z:{x0:X & reflect (P x0)} =>
        match z return (reflect (sigT P))
          with
          | (x0 ; rp) => reflect_functor (fun p0 : P x0 => (x0 ; p0)) rp
        end) H0).
      simpl in H1.
      path_via (match
       (fun X0 : sigT P =>
        match X0 return {x0 : X & reflect (P x0)} with
        | (x0 ; p0) => (x0 ; map_to_reflect (P x0) p0)
        end) (x ; p) return (reflect (sigT P))
                  with
                  | (x0 ; rp) => reflect_functor (fun p0 : P x0 => (x0 ; p0)) rp
                end).
      apply reflect_naturality.

      intros [x rp].
      unfold rf1, rf2.
      path_via (reflect_factor
        (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0)))
        ((fun X0 : sigT P => let (x0, p) := X0 in
          (existT (fun x' => reflect (P x')) x0 (map_to_reflect (P x0) p)))
        o (fun p : P x => (x ; p))) rp).
      apply reflect_factoriality2.
      path_via (reflect_factor
        (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0)))
        (fun p : P x =>
          (existT (fun x' => reflect (P x')) x (map_to_reflect (P x) p))) rp).
      apply reflect_factor_unfactors.
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
  Definition equiv_in_E {X Y} (f : X -> Y) : is_equiv f -> in_E f.
  Proof.
    intros feq y.
    apply contr_equiv_contr with unit.
    apply @equiv_compose with (reflect unit).
    apply in_rsc_reflect_equiv. auto.
    apply reflect_functor_equiv.
    apply equiv_inverse, contr_equiv_unit.
    apply feq. auto.
  Defined.

  (** Likewise, any equivalence is in M. *)
  Definition equiv_in_M {X Y} (f : X -> Y) : is_equiv f -> in_M f.
  Proof.
    intros feq y.
    apply @transport with (P := in_rsc) (x := unit).
    apply opposite, equiv_to_path, contr_equiv_unit, feq.
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

  Hint Resolve @equiv_in_E @equiv_in_M @map_in_rsc_in_M.

  (** A map that is inverted by the reflector, and whose codomain is
     in the subcategory, belongs to E.  (It is not true, in this
     generality, that *any* map inverted by the reflector is in E.)
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
      apply reflect_factoriality2.
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
      destruct z as [y rxp].
      unfold QftoYeq. simpl.
      path_via (reflect_factor Yr PftoY
    ((fun X0 : {x : Y & reflect {x0 : X & f x0 == x}} =>
       let (x, rp) return (reflect {y':Y & {x':X & f x' == y'}}) := X0 in
       reflect_functor (fun p : {x0 : X & f x0 == x} => (x ; p)) rp)
     (existT (fun y' =>  reflect {x:X & f x == y'}) y rxp))).
      path_via (reflect_factor Yr (PftoY o
        (fun p : {x0 : X & f x0 == y} => (y ; p))) rxp).
      apply @reflect_factoriality2.
      unfold PftoY.
      path_via (reflect_factor Yr (fun _ => y) rxp).
      apply reflect_factor_constant.
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
  Definition map_to_reflect_in_E X : in_E (map_to_reflect X).
  Proof.
    apply inverted_to_rsc_in_E with
      (Y := reflect X)
      (Yr := reflect_in_rsc X).
    assert (p : @id (reflect X) == reflect_factor (reflect_in_rsc X) (map_to_reflect X)).
    path_via (reflect_factor (reflect_in_rsc X) ((@id (reflect X) o map_to_reflect X))).
    apply opposite.  apply funext.  intros x. apply reflect_factor_unfactors.
    apply funext; intros x; auto.
    apply (transport p).
    apply (pr2 (idequiv _)).
  Defined.

  Definition Emap_to_reflect X :=
    existT in_E (map_to_reflect X) (map_to_reflect_in_E X).

  (** E and M are homotopy orthogonal to each other. *)
  Section EMOrth.

    (** A commutative square with an E on the left and an M on the right. *)
    Hypotheses X Y Z W : Type.
    Hypothesis e : Emap X Y.
    Hypothesis m : Mmap Z W.
    Hypothesis f : X -> Z.
    Hypothesis g : Y -> W.
    Hypothesis s : forall x, m (f x) == g (e x).

    (** We construct a lift simultaneously with a homotopy in the lower
       triangle. *)

    Definition EMlift_tot (y:Y) : {z:Z & m z == g y} :=
      reflect_factor (pr2 m (g y))
        (fun X0 : {x : X & e x == y} =>
          let (x,p) := X0 in (f x ; s x @ map g p)) (pr1 (pr2 e y)).

    Definition EMlift (y:Y) : Z :=
      pr1 (EMlift_tot y).

    Definition EMlift_lowertri (y:Y) : m (EMlift y) == g y :=
      pr2 (EMlift_tot y).
    
    (** Then we extract the upper triangle simultaneously with a proof
       that the two triangles compose to the given square. *)

    Definition EMlift_uppertri_plus (x : X) :
      EMlift_tot (e x) == (f x ; s x).
    Proof.
      unfold EMlift_tot.
      path_via (reflect_factor (pr2 m (g (e x)))
          (fun X0 : {x0 : X & e x0 == e x} =>
            let (x0, p) := X0 in (f x0 ; s x0 @ map g p)) 
          (map_to_reflect _ (x ; idpath (e x)))).
      apply opposite, (pr2 (pr2 e (e x))).
      unfold reflect_factor.
      path_via (reflection_equiv {x0 : X & e x0 == e x}
       {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x)))
      ((reflection_equiv {x0 : X & e x0 == e x}
         {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x))) ^-1)
        (fun X0 : {x0 : X & e x0 == e x} =>
         let (x0, p) := X0 in (f x0 ; s x0 @ map g p)))
        (x ; idpath (e x))).
      path_via (existT (fun z => m z == g (e x))
        (f x) (s x @ map g (idpath (e x)))).
      assert (H : reflection_equiv {x0 : X & e x0 == e x}
       {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x)))
      ((reflection_equiv {x0 : X & e x0 == e x}
         {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x))) ^-1)
        (fun X0 : {x0 : X & e x0 == e x} =>
         let (x0, p) := X0 in (f x0 ; s x0 @ map g p)))
      == (fun X0 : {x0 : X & e x0 == e x} =>
         let (x0, p) := X0 in (f x0 ; s x0 @ map g p))).
      apply inverse_is_section.
      apply (happly H).
    Defined.

    Definition EMlift_uppertri (x:X) : EMlift (e x) == f x :=
      base_path (EMlift_uppertri_plus x).

    Definition EMlift_square (x:X) :
      !map m (EMlift_uppertri x) @ EMlift_lowertri (e x) == s x.
    Proof.
      path_via (transport
        (base_path (EMlift_uppertri_plus x))
        (pr2 (EMlift_tot (e x)))).
      path_via (transport
        (P := fun w => w == g (e x))
        (x := m (pr1 (EMlift_tot (e x))))
        (y := m (pr1 (f x ; s x)))
        (map m (base_path (EMlift_uppertri_plus x)))
        (pr2 (EMlift_tot (e x)))).
      apply opposite, trans_is_concat_opp.
      apply opposite.
      apply @map_trans with (P := fun w => w == g (e x)).
      exact (fiber_path (EMlift_uppertri_plus x)).
    Defined.

    (** So far we have just shown that a lift exists.  We should prove
       that it is unique, and in fact homotopy unique (i.e. the space
       of such lifts is contractible).  But we won't. *)

  End EMOrth.

  Implicit Arguments EMlift [X Y Z W].

  (** Orthogonality lets us prove easily that E-maps are inverted by
     the reflector.  (Again, the converse is not true in this generality.) *)
  Section EInverted.

    Hypothesis (X Y:Type) (f : Emap X Y).

    Let rfm : Mmap (reflect X) (reflect Y) :=
      (map_in_rsc_Mmap (reflect_functor f) (reflect_in_rsc X) (reflect_in_rsc Y)).

    Let invert : reflect Y -> reflect X.
    Proof.
      apply @reflect_factor with (X:=Y). auto.
      apply EMlift with (e := f) (m := rfm)
        (f := map_to_reflect X) (g := map_to_reflect Y).
      intros x.
      path_via (reflect_functor f (map_to_reflect X x)).
      apply reflect_naturality.
    Defined.

    Definition E_inverted : is_equiv (reflect_functor f).
    Proof.
      apply hequiv_is_equiv with invert.
      apply reflect_factor_dep with (X := Y). auto.
      intros y.
      unfold invert.
      path_via (rfm
        (EMlift f rfm (map_to_reflect X) (map_to_reflect Y)
           (fun x : X =>
            map (reflect_functor f) (map (map_to_reflect X) (idpath x)) @
            reflect_naturality f x) y)).
      apply reflect_factor_factors.
      apply EMlift_lowertri with
        (e := f)
        (m := rfm)
        (f := map_to_reflect X)
        (g := map_to_reflect Y).
      apply reflect_factor_dep with (X := X). auto.
      intros x.
      path_via (invert (map_to_reflect Y (f x))).
      apply reflect_naturality.
      unfold invert.
      path_via ((EMlift f rfm (map_to_reflect X) (map_to_reflect Y)
        (fun x0 : X =>
         map (reflect_functor f) (map (map_to_reflect X) (idpath x0)) @
         reflect_naturality f x0)) (f x)).
      apply reflect_factor_factors.
      apply EMlift_uppertri.
    Defined.

    Definition invert_E : reflect X <~> reflect Y
      := (reflect_functor f ; E_inverted).

  End EInverted.

  (** In particular, that means that given an E-map between any two
     objects, one reflects to a point iff the other does. *)
  Definition Emap_punctual_codomain {X Y} : Emap X Y ->
    is_contr (reflect X) -> is_contr (reflect Y).
  Proof.
    intros f Xc.
    apply contr_equiv_contr with (A := reflect X).
    apply invert_E; auto.
    auto.
  Defined.

  Definition Emap_punctual_domain {X Y} : Emap X Y ->
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
    apply @Emap_punctual_domain with
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
    apply @Emap_punctual_codomain with
      (X := {x:X & g (f x) == z}).
    exists (composite_fiber_map f g z).
    apply fibermap_in_E.
    apply gine.
  Defined.
  
  (** Every morphism factors as an E followed by an M. *)
  Section EMFactor.

    Hypothesis X Y : Type.
    Hypothesis f : X -> Y.

    (* The intermediate object we factor through. *)
    Let Z := {y:Y & reflect {x:X & f x == y}}.

    (* The E part *)
    Let e (x:X) : Z :=
      existT (fun y => reflect {x:X & f x == y}) (f x)
      (map_to_reflect _ (x ; idpath _)).

    (* The M part *)
    Let m : Z -> Y := pr1.

    (* We identify the fiber of e as something more manageable.
       Probably univalence is not necessary for this proof, but it
       makes it easier.  *)
    Let efiber_ident (z : Z) : {x : X & e x == z} ==
      { hf : {x:X & f x == pr1 z} & map_to_reflect _ hf == pr2 z }.
    Proof.
      destruct z as [y rxp].
      path_via ({x:X & {p : f x == y &
        (transport (P := fun y' => reflect {x':X & f x' == y'}) p
          (map_to_reflect _ (existT (fun x' => f x' == f x) x (idpath (f x))))
          == rxp)}}).
      apply funext. intros x.
      apply equiv_to_path, total_paths_equiv.
      path_via ({x:X & {p : f x == y &
        (map_to_reflect _ (existT (fun x' => f x' == y) x p)) == rxp}}).
      apply funext. intros x.
      apply map.
      apply funext. intros p.
      apply @map with (f := fun t => t == rxp).
      apply opposite.
      path_via (map_to_reflect {x' : X & f x' == y}
        (x ; (transport (P := fun y => f x == y) p (idpath (f x))))).
      apply opposite.
      path_via (idpath (f x) @ p).
      apply @trans_is_concat.
      apply @trans_map with    
        (P := fun (y:Y) => f x == y)
        (Q := fun (y:Y) => reflect {x0:X & f x0 == y})
        (f := fun (y:Y) (r:f x == y) =>
          map_to_reflect {x0:X & f x0 == y} (x ; r)).
      apply equiv_to_path.
      apply total_assoc_sum with
        (P := fun x => f x == y)
        (Q := fun xp => map_to_reflect {x' : X & f x' == y} xp == rxp).
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
      apply map_to_reflect_in_E.
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

End FactorizationSystem.
