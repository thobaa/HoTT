Add LoadPath "..".
Require Import Homotopy.

(** The following typeclass axiomatizes the notion of a reflective
   subfibration, meaning a reflective subcategory of each slice
   category, such that pullback preserves the subcategories and
   commutes with the reflector.

   Note that on the surface, it appears to describe merely a
   reflective *subcategory*, but since "everything is internal",
   semantically it automatically gives a whole reflective
   subfibration.  In particular, the corresponding subcategory of the
   slice over X is the maps whose homotopy fibers are (internally) all
   in the subcategory.
*)

Class rsf (in_rsc : Type -> Type) := {
  in_rsc_prop : forall X, is_prop (in_rsc X)
  ; reflect : Type -> Type
  ; reflect_in_rsc : forall X, in_rsc (reflect X)
  ; to_reflect : forall X, X -> reflect X
  ; reflect_is_reflection : forall X Y, in_rsc Y ->
    is_equiv (fun f: reflect X -> Y => f o to_reflect X)
  }.

(** Since we work with a lot of paths between functions, we define a
   variant of [path_simplify] which also applies [happly] and
   [happly_dep]. *)

Ltac fpath_simplify :=
  repeat progress first [
      apply whisker_left
    | apply whisker_right
    | apply @map
    | apply_happly
  ]; auto with path_hints.

Ltac fpath_simplify' lem :=
  repeat progress first [
      apply lem
    | apply opposite; apply lem
    | apply whisker_left
    | apply whisker_right
    | apply @map
    | apply_happly
  ]; auto with path_hints.

(** And corresponding versions of [path_via], [path_using], and
   [path_change].  It would be nice if we could teach all the other
   tactics from "Paths.v" to use [fpath_using] instead of
   [path_using], but I don't know how to do that. *)

Ltac fpath_via mid :=
  apply @concat with (y := mid); fpath_simplify.

Ltac fpath_using mid lem :=
  apply @concat with (y := mid); fpath_simplify' lem.

Ltac fpath_change mid :=
  match goal with
    |- ?source == ?target =>
      first [ change (source == mid) | change (mid == target) ]
  end; fpath_simplify.

(** The above tactics are used when we want to change the goal into a
   path between functions.  Here are versions that do the reverse,
   using funext. *)

Ltac apath_simplify name :=
  repeat progress first [
      apply whisker_left
    | apply whisker_right
    | apply @map
    | apply funext; let x := fresh name in intros x
    | apply funext_dep; let x := fresh name in intros x
  ]; auto with path_hints.

Ltac apath_simplify' name lem :=
  repeat progress first [
      apply lem
    | apply opposite; apply lem
    | apply whisker_left
    | apply whisker_right
    | apply @map
    | apply funext; let x := fresh name in intros x
    | apply funext_dep; let x := fresh name in intros x
  ]; auto with path_hints.

Ltac apath_via mid name :=
  apply @concat with (y := mid); apath_simplify name.

Ltac apath_using mid name lem :=
  apply @concat with (y := mid); apath_simplify' name lem.

Ltac apath_change mid name :=
  match goal with
    |- ?source == ?target =>
      first [ change (source == mid) | change (mid == target) ]
  end; apath_simplify name.

(** And tactics that do both.  These are dangerous, because
   [apply_happly] and [apply funext] can go into a loop.  They should
   only be called when you are positive that [lem] will solve the
   goal.  *)

Ltac spath_simplify' name lem :=
  repeat progress first [
      apply lem
    | apply opposite; apply lem
    | apply whisker_left
    | apply whisker_right
    | apply @map
    | apply_happly
    | apply funext; let x := fresh name in intros x
    | apply funext_dep; let x := fresh name in intros x
  ]; auto with path_hints.

Ltac spath_using mid name lem :=
  apply @concat with (y := mid); spath_simplify' name lem.



(** Package up the factorization equivalence as an 'equiv' object. *)
Definition reflection_equiv {in_rsc : Type -> Type} {is_rsf : rsf (in_rsc)}
  : forall X Y, in_rsc Y -> (reflect X -> Y) <~> (X -> Y).
Proof.
  intros X Y P.
  apply existT with (fun f: reflect X -> Y => f o to_reflect X).
  apply reflect_is_reflection.
  assumption.
Defined.

(** Tactics which implement and unimplement the above operation. *)

Ltac find_refleqv_with Yr :=
  match goal with
    | in_rsc : Type -> Type,
      is_rsf : rsf ?in_rsc
      |- appcontext cxt [ ?f (@to_reflect ?in_rsc ?is_rsf ?X ?x) ] =>
      match (type of f) with
        | (reflect X) -> ?Y =>
          let new := context cxt [ @reflection_equiv in_rsc is_rsf X Y Yr f x ] in
            change new; fpath_simplify
      end
    | in_rsc : Type -> Type,
      is_rsf : rsf ?in_rsc
      |- appcontext cxt [ ?f o (@to_reflect ?in_rsc ?is_rsf ?X) ] =>
      match (type of f) with
        | (reflect X) -> ?Y =>
          let new := context cxt [ @reflection_equiv in_rsc is_rsf X Y Yr f ] in
            change new; fpath_simplify
      end
    | in_rsc : Type -> Type,
      is_rsf : rsf ?in_rsc
      |- appcontext cxt [ (?g o ?f) o (@to_reflect ?in_rsc ?is_rsf ?X) ] =>
      match (type of f) with
        | (reflect X) -> ?Y =>
          let new := context cxt [ g o @reflection_equiv in_rsc is_rsf X Y Yr f ] in
            change new; fpath_simplify
      end
  end.

Ltac find_refleqv :=
  match goal with
    in_rsc : Type -> Type,
    is_rsf : rsf ?in_rsc
    |- appcontext cxt [ @reflection_equiv ?in_rsc ?is_rsf ?X ?Y ?Yr ] =>
      find_refleqv_with Yr
  end; try cancel_inverses.

(** We now prove a number of properties of such a reflective
   subfibration.  In this file, we state all of them as if we were
   talking merely about a reflective subcategory.  By interpretation
   in arbitrary contexts, this implies the corresponding results for
   the entire subfibration. *)

(** Let's work in a section to simplify our hypotheses. *)
Section ReflectiveSubfibration.

  Context {in_rsc : Type -> Type}.
  Context {is_rsf : rsf (in_rsc)}.
  Existing Instance is_rsf.

  Hint Resolve reflect_in_rsc.

  (** A name for the inverse of [reflection_equiv], which does
     factorization of maps through the unit of the reflection. *)
  Definition reflect_factor {X Y} (Yr : in_rsc Y) : (X -> Y) -> (reflect X -> Y) :=
    reflection_equiv X Y Yr ^-1.

  (** And its basic properties. *)
  Definition reflect_factor_factors {X Y} (Yr : in_rsc Y) (f : X -> Y) (x : X) :
    reflect_factor Yr f (to_reflect X x) == f x.
  Proof.
    unfold reflect_factor; find_refleqv.
  Defined.

  Definition reflect_factor_unfactors {X Y} (Yr : in_rsc Y)
    (f : reflect X -> Y) (rx : reflect X) :
    reflect_factor Yr (f o to_reflect X) rx == f rx.
  Proof.
    unfold reflect_factor; find_refleqv.
  Defined.

  Definition reflect_factor_factunfact {X Y} (Yr : in_rsc Y)
    (f : reflect X -> Y) (x : X) :
    reflect_factor_unfactors Yr f (to_reflect X x) ==
    reflect_factor_factors Yr (f o to_reflect X) x.
  Proof.
    unfold reflect_factor_unfactors, reflect_factor_factors.
    cancel_units; fpath_simplify.
    fpath_via (happly (map (reflection_equiv X Y Yr)
      (inverse_is_retraction (reflection_equiv X Y Yr) f))
    x).
    unfold happly.
    undo_compose_map.
    apply @inverse_triangle with
      (w := (reflection_equiv X Y Yr))
      (x := f).
  Defined.

  Definition reflect_factor_constant {X Y} (Yr : in_rsc Y) (y : Y) (rx : reflect X) :
    reflect_factor Yr (fun _ => y) rx == y.
  Proof.
    unfold reflect_factor.
    apply @happly with (g := fun _ => y).
    equiv_moveright.
    fpath_simplify.
  Defined.

  (** The reflector is a functor. *)
  Definition reflect_functor {X Y} : (X -> Y) -> (reflect X -> reflect Y).
  Proof.
    intros f.
    apply reflect_factor.
    auto.
    exact (compose (to_reflect _) f).
  Defined.

  (** The functor action behaves as you would expect on factorizations. *)
  Definition reflect_factor_functor {X Y} (f : X -> Y) (Yr : in_rsc Y) : 
    to_reflect Y o reflect_factor Yr f == reflect_functor f.
  Proof.
    unfold reflect_functor, reflect_factor.
    apply equiv_injective with
      (w := reflection_equiv X (reflect Y) (reflect_in_rsc Y)).
    simpl.
    repeat find_refleqv.
  Defined.

  (** The following lemmas are all manifestations of functoriality. *)

  Definition reflect_factoriality_pre {X Y Z} (Yr : in_rsc Y) (Zr : in_rsc Z)
    (g : Y -> Z) (f : X -> Y) (rx : reflect X) :
    g (reflect_factor Yr f rx) == reflect_factor Zr (g o f) rx.
  Proof.
    unfold reflect_factor; fpath_simplify.
    apply @equiv_map_inv with (f := reflection_equiv X Z Zr).
    cancel_inverses.
    path_change ((g o (reflection_equiv X Y Yr ^-1) f) o to_reflect X).
    path_change (g o ((reflection_equiv X Y Yr ^-1) f o to_reflect X)).
    find_refleqv.
  Defined.

  Definition reflect_factoriality_post {X Y Z} (Zr : in_rsc Z)
    (g : Y -> Z) (f : X -> Y) (rx : reflect X) :
    reflect_factor Zr g (reflect_functor f rx) == reflect_factor Zr (g o f) rx.
  Proof.
    path_via ((reflection_equiv X Z Zr ^-1)
      (reflect_factor Zr g o (to_reflect Y o f)) rx).
    unfold reflect_functor, reflect_factor.
    apply reflect_factoriality_pre.
    apply happly.
    apply map.
    path_change ((reflect_factor Zr g o to_reflect Y) o f).
    apply @map with (f := fun g' => g' o f).
    unfold reflect_factor; find_refleqv.
  Defined.

  Definition reflect_functoriality {X Y Z} (g : Y -> Z) (f : X -> Y) (rx : reflect X) :
    reflect_functor g (reflect_functor f rx) == reflect_functor (g o f) rx.
  Proof.
    apply @reflect_factoriality_post.
  Defined.

  Definition reflect_functoriality_id {X} (rx : reflect X) :
    reflect_functor (@id X) rx == rx.
  Proof.
    unfold reflect_functor.
    path_via (reflect_factor (reflect_in_rsc X) (@id (reflect X) o to_reflect X) rx).
    apply reflect_factor_unfactors.
  Defined.

  (** A sort of functoriality for the functoriality. *)

  Definition reflect_factoriality_pre_factors  {X Y Z} (Yr : in_rsc Y) (Zr : in_rsc Z)
    (g : Y -> Z) (f : X -> Y) (x : X) :
    reflect_factoriality_pre Yr Zr g f (to_reflect X x) @
    reflect_factor_factors Zr (g o f) x ==
    map g (reflect_factor_factors Yr f x).
  Proof.
    unfold reflect_factoriality_pre, reflect_factor_factors.
    cancel_units; try fpath_simplify.
    set (q := happly (inverse_is_section (reflection_equiv X Z Zr) (g o f)) x).
    path_via ((happly
      (equiv_map_equiv (reflection_equiv X Z Zr)
        (equiv_map_equiv
          (x := (g o (reflection_equiv X Y Yr ^-1) f))
          (reflection_equiv X Z Zr) ^-1
          (map (compose g) (inverse_is_section (reflection_equiv X Y Yr) f) @
            !inverse_is_section (reflection_equiv X Z Zr) (g o f)))) x) @ q).
    apply opposite.
    refine (map_precompose _ _ (to_reflect X)
      (equiv_map_inv (reflection_equiv X Z Zr)
          (x := (g o (reflection_equiv X Y Yr ^-1) f))
        (map (compose g) (inverse_is_section (reflection_equiv X Y Yr) f) @
         !inverse_is_section (reflection_equiv X Z Zr) (g o f)))
      x).
    fpath_via (happly (map (compose g) (inverse_is_section (reflection_equiv X Y Yr) f) @
      !inverse_is_section (reflection_equiv X Z Zr) (g o f)) x @ q).
    cancel_inverses.
    unfold happly, q; clear q.
    path_via (map (fun h : X -> Z => h x)
      ((map (compose g) (inverse_is_section (reflection_equiv X Y Yr) f) @
        !inverse_is_section (reflection_equiv X Z Zr) (g o f)) @ 
      (inverse_is_section (reflection_equiv X Z Zr) (g o f)))).
    apply opposite.
    apply concat_map with (f := fun h => h x).
    path_via (map (fun h => h x)
      (map (compose g) (inverse_is_section (reflection_equiv X Y Yr) f))).
    cancel_opposites.
    undo_compose_map.
  Defined.

  (** The reflection is also a 2-functor. *)
  Definition reflect_2functor {X Y} (f g : X -> Y) (p : forall x, f x == g x) :
    forall rx : reflect X, reflect_functor f rx == reflect_functor g rx.
  Proof.
    intros rx; apply happly.
    apply map.
    apply funext. assumption.
  Defined.

  (** The reflector preserves equivalences *)
  Definition reflect_preserves_equiv {X Y} (f : X -> Y) :
    is_equiv f -> is_equiv (reflect_functor f).
  Proof.
    intros H.
    set (feq := (f ; H) : equiv X Y).
    apply hequiv_is_equiv with (g := reflect_functor (inverse feq)).
    intros ry.
    path_via (reflect_functor (feq o inverse feq) ry).
    apply reflect_functoriality.
    spath_using (reflect_functor (@id Y) ry) Z @inverse_is_section.
    apply reflect_functoriality_id.
    intros rx.
    path_via (reflect_functor (inverse feq o feq) rx).
    apply reflect_functoriality.
    spath_using (reflect_functor (@id X) rx) Z @inverse_is_retraction.
    apply reflect_functoriality_id.
  Defined.

  Definition reflect_functor_equiv {X Y} (f : X <~> Y) :
    reflect X <~> reflect Y.
  Proof.
    exists (reflect_functor f).
    apply reflect_preserves_equiv.
    apply (pr2 f).
  Defined.

  (** The unit of the reflection is a natural transformation. *)
  Definition reflect_naturality {X Y} (f : X -> Y) (x:X) :
    reflect_functor f (to_reflect X x) == to_reflect Y (f x).
  Proof.
    assert (p : reflect_functor f o to_reflect X == to_reflect Y o f).
    unfold reflect_functor, reflect_factor.
    path_via (reflection_equiv X (reflect Y) (reflect_in_rsc Y)
      ((reflection_equiv X (reflect Y) (reflect_in_rsc Y) ^-1)
        (to_reflect Y o f))).
    apply inverse_is_section with
      (w := reflection_equiv X (reflect Y) (reflect_in_rsc Y))
      (y :=  (to_reflect Y o f)).
    apply (happly p).
  Defined.

  (** The reflector is a well-pointed endofunctor. *)
  Definition reflect_wellpointed {X} (rx : reflect X) :
    reflect_functor (to_reflect X) rx == to_reflect (reflect X) rx.
  Proof.
    apply happly.
    apply equiv_injective with
      (w := reflection_equiv X (reflect (reflect X)) (reflect_in_rsc (reflect X))).
    apply funext. intros x.
    unfold reflection_equiv. simpl.
    apply @reflect_naturality with (f := to_reflect X) (x := x).
  Defined.
    
  (** If the unit at X is an equivalence, then X is in the subcategory. *)
  Definition reflect_equiv_in_rsc X : is_equiv (to_reflect X) -> in_rsc X.
    intros H.
    apply @transport with (P := in_rsc) (x := reflect X).
    exact (!equiv_to_path (to_reflect X ; H)).
    apply reflect_in_rsc.
  Defined.

  (** In fact, it suffices for the unit at X merely to have a retraction. *)
  Definition reflect_retract_in_rsc X (r : reflect X -> X) :
    (forall x, r (to_reflect X x) == x) -> in_rsc X.
  Proof.
    intros h.
    apply reflect_equiv_in_rsc.
    apply hequiv_is_equiv with (g := r).
    intros y.
    path_change (@id _ y).
    apply_happly.
    apply equiv_injective with
      (w := reflection_equiv X (reflect X) (reflect_in_rsc X)).
    simpl.
    path_change (to_reflect X o (@id X)).
    path_change (to_reflect X o (r o to_reflect X)).
    apply funext; exact h.
    assumption.
  Defined.

  (** If X is in the subcategory, then the unit is an equivalence. *)
  Definition in_rsc_reflect_equiv X : in_rsc X -> (equiv X (reflect X)).
  Proof.
    intros H.
    exists (to_reflect X).
    apply hequiv_is_equiv with (g := reflect_factor H (@id X)).
    intros y.
    unfold reflect_factor.
    path_change (@id _ y); apply_happly.
    apply equiv_injective with
      (w := reflection_equiv X (reflect X) (reflect_in_rsc X)).
    simpl.
    path_change (to_reflect X o (@id X)).
    path_change (to_reflect X o ((reflection_equiv X X H ^-1) (@id X) o to_reflect X)).
    exact (inverse_is_section (reflection_equiv X X H) (@id X)).
    exact (happly (inverse_is_section (reflection_equiv X X H) (@id X))).
  Defined.

  (** The unit is inverted by the reflector. *)
  Definition reflect_to_reflect_equiv {X} :
    is_equiv (reflect_functor (to_reflect X)).
  Proof.
    assert (p : reflect_functor (to_reflect X) == to_reflect (reflect X)).
    apply funext.  intros x. apply reflect_wellpointed.
    apply (transport (!p)).
    change (is_equiv (pr1 (in_rsc_reflect_equiv (reflect X) (reflect_in_rsc X)))).
    apply (pr2 (in_rsc_reflect_equiv (reflect X) (reflect_in_rsc X))).
  Defined.

  (** The inverse of the unit, when it exists, is also natural. *)
  Definition reflect_inverse_naturality {X Y} (Xr : in_rsc X) (Yr : in_rsc Y)
    (f : X -> Y) (rx : reflect X) :
    f (inverse (in_rsc_reflect_equiv X Xr) rx) ==
    (inverse (in_rsc_reflect_equiv Y Yr) (reflect_functor f rx)).
  Proof.
    equiv_moveleft.
    path_via (reflect_functor f
      (in_rsc_reflect_equiv X Xr
        (inverse (in_rsc_reflect_equiv X Xr) rx))).
    apply opposite.
    apply @reflect_naturality.
    cancel_inverses.
  Defined.

  (** The terminal object is in the subcategory. *)
  Definition unit_in_rsc : in_rsc unit.
  Proof.
    apply reflect_retract_in_rsc with (r := fun x => tt).
    intros x; induction x; auto.
  Defined.

  Hint Resolve unit_in_rsc.

  (** The subcategory is closed under path spaces. *)
  Section PathSpaces.

    Hypothesis X:Type.
    Hypothesis X_in_rsc : in_rsc X.
    Hypotheses x0 x1:X.

    Let path_map_back : reflect (x0 == x1) -> (x0 == x1).
    Proof.
      intros rl.
      assert (p : (fun _:reflect (x0 == x1) => x0) == (fun _ => x1)).
      apply ((equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc))^-1).
      unfold reflection_equiv; simpl.
      apply funext; intro l.
      unfold compose.
      assumption.
      apply (happly p).
      assumption.
    Defined.

    Definition path_in_rsc : in_rsc (x0 == x1).
    Proof.
      apply reflect_retract_in_rsc with (r := path_map_back).
      intros x.
      unfold path_map_back.
      path_via
      (happly
        (map (fun f' => f' o (to_reflect _))
          ((equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc) ^-1)
            (@funext _ _
              ((fun _ => x0) o to_reflect _)
              ((fun _ => x1) o to_reflect _)
              (fun l : x0 == x1 => l)))) x).
      apply opposite, map_precompose.
      path_via
      (happly
        (equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc)
          ((equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc) ^-1)
            (@funext _ _
              ((fun _ => x0) o to_reflect _)
              ((fun _ => x1) o to_reflect _)
              (fun l : x0 == x1 => l)))) x).
    (* Here is where it would be nice to teach [cancel_inverses] to
       use [fpath_using]. *)
      cancel_inverses; fpath_simplify; cancel_inverses.
      unfold funext.
      apply strong_funext_compute with
        (f := ((fun _ => x0) o to_reflect _))
        (g := ((fun _ => x1) o to_reflect _)).
    Defined.

  End PathSpaces.

  Hint Resolve path_in_rsc.

  (** The subcategory is closed under binary products. *)
  Section Products.

    Hypotheses X Y : Type.
    Hypothesis Xr : in_rsc X.
    Hypothesis Yr : in_rsc Y.

    Let prod_map_back : reflect (X * Y) -> X * Y.
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

    Definition prod_in_rsc : in_rsc (X * Y).
    Proof.
      apply reflect_retract_in_rsc with (r := prod_map_back).
      intros xy. destruct xy.
      unfold prod_map_back.
      apply prod_path.
      equiv_moveright.
      path_via (to_reflect X (fst (x,y))).
      apply reflect_naturality.
      equiv_moveright.
      path_via (to_reflect Y (snd (x,y))).
      apply reflect_naturality.
    Defined.

  End Products.

  Hint Resolve prod_in_rsc.

  (** The subcategory is a local exponential ideal.  This is a little
     surprising, since in general not every reflective subcategory has
     this property.  Thus, here is the first place we see that being a
     reflective *subfibration* has implications even for the
     underlying reflective subcategory.
     *)
  Section ExponentialIdeal.

    Hypothesis X : Type.
    Hypothesis P : X -> Type.
    Hypothesis Pr : forall x, in_rsc (P x).

    Let exp_map_back : reflect (forall x, P x) -> forall x, P x.
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

  Hint Resolve exp_in_rsc.

  (** This allows us to extend functoriality to multiple variables. *)

  Definition reflect_factor2 {X Y Z} : in_rsc Z ->
    (X -> Y -> Z) -> (reflect X -> reflect Y -> Z).
  Proof.
    intros Zr f rx.
    apply reflect_factor. auto.
    apply @reflect_factor with (X := X); auto.
  Defined.

  Definition reflect_functor2 {X Y Z} :
    (X -> Y -> Z) -> (reflect X -> reflect Y -> reflect Z).
  Proof.
    intros f rx ry.
    apply @reflect_factor2 with X Y; auto.
    intros x y; apply to_reflect; apply f; auto.
  Defined.

  (** Naturality of [to_reflect] for two variables. *)

  Definition reflect_naturality2 X Y Z (x:X) (y:Y) (f:X->Y->Z) :
    reflect_functor2 f (to_reflect X x) (to_reflect Y y)
    == to_reflect Z (f x y).
  Proof.
    unfold reflect_functor2, reflect_factor2.
    fpath_via ((reflect_factor (reflect_in_rsc Z)
      (fun y0 => to_reflect Z (f x y0))) (to_reflect Y y)).
    apply reflect_factor_factors.
    apply @reflect_factor_factors with
      (f := (fun y0 : Y => to_reflect Z (f x y0))).
  Defined.

  (** And to prove that the reflector preserves finite products. *)
  Section PreservesProducts.

    Hypotheses A B : Type.

    (* We show that maps [reflect A * reflect B -> C], for [C] in the
       subcategory, are equivalent to maps [A * B -> C].  By the
       Yoneda lemma, this allows us to construct an equivalence
       between [reflect A * reflect B] and [reflect (A*B)].

       However, for this to work we have to know that the first
       equivalence is natural in C.  Since the equivalence is a
       composite of a sequence of equivalences, it is easiest to carry
       through the naturality one step at a time as we construct it.
       We also want to know that this equivalence is actually given by
       composing with the maps [A -> reflect A] and [B -> reflect B],
       so we carry that through as well.  Hence the rather unwieldy
       type of the following lemma.
       *)

    Let refeq_twovar_all :
      { e : forall C (Cr : in_rsc C), (reflect A * reflect B -> C) <~> (A * B -> C) &
        ((forall C Cr f a b, e C Cr f (a,b) == f (to_reflect A a, to_reflect B b)) *
        (forall C Cr D Dr f (g:C->D), g o (e C Cr f) == e D Dr (g o f)))%type }.
    Proof with (intros; simpl; auto).
    (* reflect A -> reflect B -> C *)
      set (e1 := fun C => curry_equiv (reflect A) (reflect B) C).
      assert (v1 : forall C f ra rb, e1 C f ra rb == f (ra,rb))...
      assert (n1 : forall C D f (g:C->D), (fun a => g o ((e1 C f) a)) == e1 D (g o f))...
      (* A -> reflect B -> C *)
      set (e2 := fun C (Cr:in_rsc C) => reflection_equiv A (reflect B -> C)
        (exp_in_rsc _ _ (fun _ => Cr))).
      assert (v2 : forall C Cr f a rb, e2 C Cr f a rb == f (to_reflect A a) rb)...
      assert (n2 : forall C Cr D Dr f (g:C->D), (fun a => g o ((e2 C Cr f) a)) == e2 D Dr (fun ra => g o (f ra)))...
      (* reflect B -> A -> C *)
      set (e3 := fun C => flip_equiv A (reflect B) C).
      assert (v3 : forall C f a rb, e3 C f rb a == f a rb)...
      assert (n3 : forall C D f (g:C->D), (fun a => g o ((e3 C f) a)) == e3 D (fun a => g o (f a)))...
      (* B -> A -> C *)
      set (e4 := fun C (Cr:in_rsc C) => reflection_equiv B (A -> C)
        (exp_in_rsc _ _ (fun _ => Cr))).
      assert (v4 : forall C Cr f b a, e4 C Cr f b a == f (to_reflect B b) a)...
      assert (n4 : forall C Cr D Dr f (g:C->D), (fun b => g o ((e4 C Cr f) b)) == e4 D Dr (fun rb => g o (f rb)))...
      (* A -> B -> C *)
      set (e5 := fun C => flip_equiv B A C).
      assert (v5 : forall C f a b, e5 C f a b == f b a)...
      assert (n5 : forall C D f (g:C->D), (fun a => g o ((e5 C f) a)) == e5 D (fun a => g o (f a)))...
      (* A * B -> C *)
      set (e6 := fun C => equiv_inverse (curry_equiv A B C)).
      assert (v6 : forall C f a b, e6 C f (a,b) == f a b)...
      assert (n6 : forall C D f (g:C->D), g o (e6 C f) == e6 D (fun a => (g o (f a))))...
      exists (fun C Cr =>
        (equiv_compose (e1 C)
          (equiv_compose (e2 C Cr)
            (equiv_compose (e3 C)
              (equiv_compose (e4 C Cr)
                (equiv_compose (e5 C) (e6 C))))))).
      split; intros.
      path_change (e6 C (e5 C (e4 C Cr (e3 C (e2 C Cr (e1 C f))))) (a,b)).
      path_change (g o (e6 C (e5 C (e4 C Cr (e3 C (e2 C Cr (e1 C f))))))).
    Defined.

    Definition reflection_equiv_twovar := pr1 refeq_twovar_all.
    Let refeq_twovar_eval := fst (pr2 refeq_twovar_all).
    Let refeq_twovar_natural := snd (pr2 refeq_twovar_all).

    Definition reflect_factor_twovar {C} (Cr : in_rsc C) :
      (A * B -> C) -> (reflect A * reflect B -> C)
      := reflection_equiv_twovar C Cr ^-1.

    Definition reflect_factoriality_pre_twovar {C D} (Cr : in_rsc C) (Dr : in_rsc D)
      (f : A * B -> C) (g : C -> D) :
      g o reflect_factor_twovar Cr f == reflect_factor_twovar Dr (g o f).
    Proof.
      unfold reflect_factor_twovar.
      equiv_moveleft.
      path_change (g o (reflection_equiv_twovar C Cr ((reflection_equiv_twovar C Cr ^-1) f))).
      apply inverse_is_section.
    Defined.

    Definition reflect_product_equiv : reflect (A * B) <~> reflect A * reflect B.
    Proof.
      exists (reflect_factor
        (prod_in_rsc (reflect A) (reflect B) (reflect_in_rsc A) (reflect_in_rsc B))
        (fun ab => (to_reflect A (fst ab), to_reflect B (snd ab)))).
      apply @hequiv_is_equiv with
        (g := reflect_factor_twovar (reflect_in_rsc (A*B)) (to_reflect (A*B))).
      apply happly.
      path_via 
      (reflect_factor_twovar (prod_in_rsc _ _ (reflect_in_rsc A) (reflect_in_rsc B))
        ((reflect_factor (prod_in_rsc (reflect A) (reflect B) (reflect_in_rsc A)
          (reflect_in_rsc B))
        (fun ab : A * B =>
          (to_reflect A (fst ab), to_reflect B (snd ab))))
        o (to_reflect (A * B)))).
      apply reflect_factoriality_pre_twovar.
      unfold compose.
      unfold reflect_factor_twovar.
      equiv_moveright.
      apply funext; intros [a b].
      path_via (to_reflect A a, to_reflect B b).
      path_change ((fun ab : A * B =>
      (to_reflect A (fst ab), to_reflect B (snd ab))) (a,b)).
      apply reflect_factor_factors with (x := (a,b)).
      (* other direction *)
      apply happly.
      apply equiv_injective with
        (w := reflection_equiv (A*B) (reflect (A*B)) (reflect_in_rsc (A*B))).
      unfold reflection_equiv. simpl.
      apply funext; intros [a b].
      unfold compose; simpl.
      path_via (reflect_factor_twovar (reflect_in_rsc (A * B)) (to_reflect (A * B))
        ((fun ab : A * B =>
         (to_reflect A (fst ab), to_reflect B (snd ab))) (a,b))).
      apply reflect_factor_factors with (x := (a,b)).
      simpl.
      unfold reflect_factor_twovar.
      path_via (reflection_equiv_twovar (reflect (A * B)) (reflect_in_rsc (A * B))
        ((reflection_equiv_twovar (reflect (A * B)) (reflect_in_rsc (A * B)) ^-1)
          (to_reflect (A * B))) (a,b)).
      apply happly, inverse_is_section.
    Defined.

  End PreservesProducts.

  (** We also have dependent factorization (a "dependent eliminator"),
     if we are eliminating into a dependent type whose total space is
     in the subcategory.  We call this "weak dependent factor" since
     it is much less useful than the strong consequence which holds
     for a stable factorization system, in which only the fibers of
     the target are required (a priori) to lie in the subcategory.  *)

  Section DependentFactor.

    Hypothesis X : Type.
    Hypothesis P : reflect X -> Type.
    Hypothesis Pr : in_rsc (sigT P).
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
        Pr
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

    Definition reflect_factor_weakdep : (forall rx, P rx).
    Proof.
      intros rx.
      apply (transport (rfdep_section rx)).
      exact (pr2 (rfdep rx)).
    Defined.

    Definition reflect_factor_weakdep_factors (x:X) :
      reflect_factor_weakdep (to_reflect X x) == f x.
    Proof.
      unfold reflect_factor_weakdep.
      fpath_via (transport (map pr1 (rfdep_factors x))
        (pr2 (rfdep (to_reflect X x)))).
      apply fiber_path with (p := rfdep_factors x).
    Defined.

  End DependentFactor.

End ReflectiveSubfibration.
