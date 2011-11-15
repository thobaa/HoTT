Require Import Homotopy.

Section ReflectiveSubcategory.

  Hypothesis in_rsc : Type -> Type.

  Hypothesis in_rsc_prop : forall X, is_prop (in_rsc X).

  Hypothesis reflect : Type -> Type.

  Hypothesis reflect_in_rsc : forall X, in_rsc (reflect X).

  Hint Resolve reflect_in_rsc.

  Hypothesis map_to_reflect : forall X, X -> reflect X.

  Hypothesis reflect_is_reflection : forall X Y, in_rsc Y ->
    is_equiv (fun f: reflect X -> Y => f ○ map_to_reflect X).

  (* Package up that equivalence as an 'equiv' object. *)
  Definition reflection_equiv : forall X Y, in_rsc Y ->
    equiv (reflect X -> Y) (X -> Y).
  Proof.
    intros X Y P.
    apply tpair with (fun f: reflect X -> Y => f ○ map_to_reflect X).
    apply reflect_is_reflection.
    assumption.
  Defined.

  (* A name for its inverse, which does factorization of maps through
     the unit of the reflection. *)
  Definition reflect_factor {X Y} (Yr : in_rsc Y) : (X -> Y) -> (reflect X -> Y) :=
    inverse (reflection_equiv X Y Yr).

  (* The reflector is a functor. *)
  Definition reflect_functor {X Y} : (X -> Y) -> (reflect X -> reflect Y).
  Proof.
    intros f.
    apply reflect_factor.
    auto.
    exact (compose (map_to_reflect _) f).
  Defined.

  (* The unit of the reflection is a natural transformation. *)
  Definition reflect_naturality {X Y} (f : X -> Y) (x:X) :
    reflect_functor f (map_to_reflect X x) ~~> map_to_reflect Y (f x).
  Proof.
    assert (p : reflect_functor f ○ map_to_reflect X ~~> map_to_reflect Y ○ f).
    unfold reflect_functor, reflect_factor.
    apply inverse_is_section with
      (w := reflection_equiv X (reflect Y) (reflect_in_rsc Y))
      (y :=  (map_to_reflect Y ○ f)).
    apply (happly p).
  Defined.

  (* If the unit at X is an equivalence, then X is in the subcategory. *)
  Lemma reflect_equiv_in_rsc X : is_equiv (map_to_reflect X) -> in_rsc X.
    intros H.
    set (eqvpath := equiv_to_path (tpair (map_to_reflect X) H)).
    apply @transport with (P := in_rsc) (x := reflect X).
    exact (!eqvpath).
    apply reflect_in_rsc.
  Defined.

  (* In fact, it suffices for the unit at X merely to have a retraction. *)
  Lemma reflect_retract_in_rsc X (r : reflect X -> X) :
    (forall x, r (map_to_reflect X x) ~~> x) -> in_rsc X.
  Proof.
    intros h.
    apply reflect_equiv_in_rsc.
    apply hequiv_is_equiv with (g := r).
    intros y.
    assert (p : map_to_reflect X ○ r ~~> @id (reflect X)).
    apply equiv_injective with
      (w := reflection_equiv X (reflect X) (reflect_in_rsc X)).
    simpl.
    path_via (map_to_reflect X ○ (@id X)).
    path_via (map_to_reflect X ○ (r ○ map_to_reflect X)).
    apply funext.
    exact h.
    exact (happly p y).
    assumption.
  Defined.

  (* If X is in the subcategory, then the unit is an equivalence. *)
  Lemma in_rsc_reflect_equiv X : in_rsc X -> (equiv X (reflect X)).
  Proof.
    intros H.
    exists (map_to_reflect X).
    apply hequiv_is_equiv with (g := reflect_factor H (@id X)).
    intros y.
    unfold reflect_factor.
    assert (p : map_to_reflect X ○ ((reflection_equiv X X H ⁻¹) (@id X))
      ~~> @id (reflect X)).
    apply equiv_injective with
      (w := reflection_equiv X (reflect X) (reflect_in_rsc X)).
    simpl.
    path_via (map_to_reflect X ○ (@id X)).
    path_via (map_to_reflect X ○ ((reflection_equiv X X H ⁻¹) (@id X) ○ map_to_reflect X)).
    exact (inverse_is_section (reflection_equiv X X H) (@id X)).
    exact (happly p y).
    intros x.
    exact (happly (inverse_is_section (reflection_equiv X X H) (@id X)) x).
  Defined.

  (* The terminal object is in the subcategory. *)
  Definition unit_in_rsc : in_rsc unit.
  Proof.
    apply reflect_retract_in_rsc with (r := fun x => tt).
    intros x; induction x; auto.
  Defined.

  (* The subcategory is closed under path spaces. *)
  Section PathSpaces.

    Hypothesis X:Type.
    Hypothesis X_in_rsc : in_rsc X.
    Hypotheses x0 x1:X.

    Lemma path_map_back : reflect (x0 ~~> x1) -> (x0 ~~> x1).
    Proof.
      intros rl.
      assert (p : (fun _:reflect (x0 ~~> x1) => x0) ~~> (fun _ => x1)).
      apply ((equiv_map_equiv (reflection_equiv (x0 ~~> x1) X X_in_rsc))⁻¹).
      unfold reflection_equiv; simpl.
      apply funext; intro l.
      unfold compose.
      assumption.
      apply (happly p).
      assumption.
    Defined.

    Definition path_in_rsc : in_rsc (x0 ~~> x1).
    Proof.
      apply reflect_retract_in_rsc with (r := path_map_back).
      intros x.
      unfold path_map_back.
      path_via
      (happly
        (map (fun f' => f' ○ (map_to_reflect _))
          ((equiv_map_equiv (reflection_equiv (x0 ~~> x1) X X_in_rsc) ⁻¹)
            (@funext _ _
              ((fun _ => x0) ○ map_to_reflect _)
              ((fun _ => x1) ○ map_to_reflect _)
              (fun l : x0 ~~> x1 => l)))) x).
      apply opposite, map_precompose.
      path_via
      (happly
        (equiv_map_equiv (reflection_equiv (x0 ~~> x1) X X_in_rsc)
          ((equiv_map_equiv (reflection_equiv (x0 ~~> x1) X X_in_rsc) ⁻¹)
            (@funext _ _
              ((fun _ => x0) ○ map_to_reflect _)
              ((fun _ => x1) ○ map_to_reflect _)
              (fun l : x0 ~~> x1 => l)))) x).
    (* Apparently the cancel_inverses tactic is insufficiently smart. *)
      cancel_inverses.
      apply map with (f := fun g => happly g x).
      cancel_inverses.
      unfold funext.
      apply strong_funext_compute with
        (f := ((fun _ => x0) ○ map_to_reflect _))
        (g := ((fun _ => x1) ○ map_to_reflect _)).
    Defined.

  End PathSpaces.

  (* The subcategory is closed under binary products. *)
  Section Products.

    Hypotheses X Y : Type.
    Hypothesis Xr : in_rsc X.
    Hypothesis Yr : in_rsc Y.

    Definition prod_map_back : reflect (X * Y) -> X * Y.
    Proof.
      intros rxy.
      split.
      apply (inverse (in_rsc_reflect_equiv X Xr)).
      generalize dependent rxy.
      apply reflect_functor, fst.
      apply (inverse (in_rsc_reflect_equiv Y Yr)).
      generalize dependent rxy.
      apply reflect_functor, snd.
    Defined.

    Definition prod_path (x x' : X) (y y' : Y) :
      (x ~~> x') -> (y ~~> y') -> ((x,y) ~~> (x',y')).
    Proof.
      path_induction.
    Defined.

    Definition prod_in_rsc : in_rsc (X * Y).
    Proof.
      apply reflect_retract_in_rsc with (r := prod_map_back).
      intros xy. destruct xy.
      unfold prod_map_back.
      apply prod_path.
      equiv_moveright.
      path_via (map_to_reflect X (fst (x,y))).
      apply reflect_naturality.
      equiv_moveright.
      path_via (map_to_reflect Y (snd (x,y))).
      apply reflect_naturality.
    Defined.

  End Products.

  (* The subcategory is a local exponential ideal.  This is a little
     surprising, since in general not every reflective subcategory has
     this property, but it follows because our reflective subcategory
     is "internally" so. *)
  Section ExponentialIdeal.

    Hypothesis X : Type.
    Hypothesis P : X -> Type.
    Hypothesis Pr : forall x, in_rsc (P x).

    Lemma exp_map_back : reflect (forall x, P x) -> forall x, P x.
    Proof.
      intros rf x.
      apply (inverse (in_rsc_reflect_equiv (P x) (Pr x))).
      generalize dependent rf.
      apply reflect_functor.
      intros f.
      apply f.
    Defined.

    Definition exp_in_rsc : in_rsc (forall x, P x).
    Proof.
      apply reflect_retract_in_rsc with (r := exp_map_back).
      intros f.
      apply funext_dep. intros x.
      unfold exp_map_back.
      equiv_moveright.
      simpl.
      apply @reflect_naturality with (f := (fun g => g x)).
    Defined.

  End ExponentialIdeal.

  (* As a consequence of the foregoing, the reflector preserves finite
     products. *)
  Section PreservesProducts.
    
    Hypotheses X Y : Type.

    Definition reflect_prod_cmp (rxy : reflect (X * Y)) : reflect X * reflect Y
      := (reflect_functor (@fst X Y) rxy, reflect_functor (@snd X Y) rxy).

    Definition reflect_prod_map_back : reflect X * reflect Y -> reflect (X * Y).
    Proof.
      intros [rx ry].
      generalize dependent ry.
      apply @reflect_factor with (X := X).
      apply exp_in_rsc.
      intros; apply reflect_in_rsc.
      intros x ry.
      apply @reflect_factor with (X := Y).
      apply reflect_in_rsc.
      intros y.
      apply map_to_reflect.
      exact ((x,y)).
      assumption. assumption.
    Defined.

    Definition reflect_prod_pres : is_equiv reflect_prod_cmp.
    Proof.
      apply hequiv_is_equiv with (g := reflect_prod_map_back).
      intros [rx ry].
      unfold reflect_prod_cmp, reflect_prod_map_back.
      apply prod_path.
      (* To be completed... *)
    Admitted.
    
  End PreservesProducts.

End ReflectiveSubcategory.
