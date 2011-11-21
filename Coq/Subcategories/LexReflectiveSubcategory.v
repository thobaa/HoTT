Add LoadPath "..".
Require Export Homotopy ReflectiveSubfibration StableFactorizationSystem.

(** Finally, we add to the notion of a stable factorization system a
   final axiom which ensures that it is determined by the underlying
   reflective subcategory, i.e. that it is a "reflective factorization
   system".  At last we have an axiomatization of nothing more than a
   reflective subcategory.  However, it turns out to always be a
   left-exact reflective subcategory, because everything must be
   pullback-stable. *)

Class lexrsc (in_rsc : Type -> Type) {is_rsf : rsf in_rsc}
  {is_factsys : factsys in_rsc} := {
    rsc_reflective_fs : forall X Y (f : X -> Y) (y : Y),
      is_contr (reflect X) -> is_contr (reflect Y) ->
      is_contr (reflect {x:X & f x == y})
  }.

Section LexReflective.

  Hypothesis in_rsc : Type -> Type.
  Hypothesis is_rsf : rsf in_rsc.
  Hypothesis is_factsys : factsys in_rsc.
  Hypothesis is_lexrsc : lexrsc in_rsc.
  Existing Instance is_rsf.
  Existing Instance is_factsys.
  Existing Instance is_lexrsc.

  Hint Resolve reflect_in_rsc unit_in_rsc path_in_rsc sum_in_rsc.

  (** First, we prove the missing part of the 2-out-of-3 property for E-maps. *)
  Definition Emap_cancel_left {X Y Z} (f : X -> Y) (g : Emap Y Z) :
    in_E (g o f) -> in_E f.
  Proof.
    intros gfine y.
    apply contr_equiv_contr with
      (reflect {z : {x : X & g (f x) == g y} &
        composite_fiber_map f g (g y) z == (y ; idpath (g y))}).
    apply reflect_functor_equiv.
    apply fiber_of_fibers.
    apply rsc_reflective_fs.
    apply gfine.
    apply (pr2 g).
  Defined.

  (** Now we can finally show that any map inverted by the reflector is
     in E. *)
  Definition inverted_in_E {X Y} (f : X -> Y) :
    is_equiv (reflect_functor f) -> in_E f.
  Proof.
    intros H.
    apply Emap_cancel_left with (g := Emap_to_reflect Y).
    apply @transport with
      (P := fun g:X -> reflect Y => in_E g)
      (x := (reflect_functor f) o (map_to_reflect X)).
    apply funext. intros x.
    path_via ((map_to_reflect Y o f) x).
    apply reflect_naturality.
    exact (pr2 (Emap_compose (Emap_to_reflect X)
      ((reflect_functor f) ; equiv_in_E (reflect_functor f) H))).
  Defined.
  
  (** The reflector preserves homotopy fibers. *)
  Section ReflectFibers.

    Hypotheses (X Y : Type) (f : X -> Y) (y:Y).

    Let fibmap : Emap {x:X & f x == y}
      {rx:reflect X & reflect_functor f rx == map_to_reflect Y y}.
    Proof.
      exists (square_fiber_map f (reflect_functor f)
        (map_to_reflect X) (map_to_reflect Y)
        (fun x => !reflect_naturality f x) y).
      intros [rx p].
      apply @transport with (P := fun T => is_contr (reflect T))
        (x := {z : {x:X & map_to_reflect X x == rx} &
          square_fiber_map (map_to_reflect X) (map_to_reflect Y)
           f (reflect_functor f)
           (fun x => !!reflect_naturality f x) rx z
           == (existT
             (fun y' => map_to_reflect Y y' == reflect_functor f rx)
             y (!p))}).
      apply opposite, equiv_to_path.
      apply @transport with (y := p) (x := !(!p))
        (P := fun q => {x : {x : X & f x == y} &
          square_fiber_map f (reflect_functor f) (map_to_reflect X)
          (map_to_reflect Y) (fun x0 : X => !reflect_naturality f x0) y x ==
          (rx ; q)} <~>
        {z : {x : X & map_to_reflect X x == rx} &
          square_fiber_map (map_to_reflect X) (map_to_reflect Y) f
          (reflect_functor f) (fun x : X => !(!reflect_naturality f x)) rx z ==
          (y ; !p)}).
      do_opposite_opposite.
      apply three_by_three with
        (f := f)
        (g := reflect_functor f)
        (h := map_to_reflect X)
        (k := map_to_reflect Y)
        (s := fun x => !reflect_naturality f x)
        (b := y)
        (c := rx)
        (d := !p).
      apply rsc_reflective_fs.
      apply map_to_reflect_in_E.
      apply map_to_reflect_in_E.
    Defined.

    Let tg_in_rsc : in_rsc {rx:reflect X &
      reflect_functor f rx == map_to_reflect Y y}.
    Proof.
      auto.
    Defined.

    Let rfibmap : reflect{x:X & f x == y} ->
      {rx:reflect X & reflect_functor f rx == map_to_reflect Y y}
      := reflect_factor tg_in_rsc fibmap.

    Definition reflect_preserves_fibers :
      reflect {x:X & f x == y}
      <~>
      {rx:reflect X & reflect_functor f rx == map_to_reflect Y y}.
    Proof.
      exists rfibmap.
      apply @equiv_cancel_left with
        (C := reflect {rx:reflect X & reflect_functor f rx == map_to_reflect Y y})
        (g := in_rsc_reflect_equiv
          {rx:reflect X & reflect_functor f rx == map_to_reflect Y y} tg_in_rsc).
      unfold rfibmap.
      apply @transport with (P := is_equiv) (x := reflect_functor fibmap).
      apply opposite.
      path_via (map_to_reflect
        {rx : reflect X & reflect_functor f rx == map_to_reflect Y y}
        o reflect_factor tg_in_rsc fibmap).
      apply reflect_factor_functor.
      apply E_inverted.
    Defined.
    
  End ReflectFibers.

  (** We should be able to use this to prove that it preserves all
     finite limits. *)

End LexReflective.

Implicit Arguments Emap_cancel_left [[in_rsc] [is_rsf] [is_factsys] [is_lexrsc] [X] [Y] [Z]].
Implicit Arguments inverted_in_E [[in_rsc] [is_rsf] [is_factsys] [is_lexrsc] [X] [Y]].
Implicit Arguments reflect_preserves_fibers [[in_rsc] [is_rsf] [is_factsys] [is_lexrsc]].
