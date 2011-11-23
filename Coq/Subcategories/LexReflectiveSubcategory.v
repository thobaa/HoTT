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

  Context {in_rsc : Type -> Type}.
  Context {is_rsf : rsf in_rsc}.
  Context {is_factsys : factsys in_rsc}.
  Context {is_lexrsc : lexrsc in_rsc}.
  Existing Instance is_rsf.
  Existing Instance is_factsys.
  Existing Instance is_lexrsc.

  Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc exp_in_rsc sum_in_rsc.

  (** A version of the additional axiom for fibrations. *)
  Definition rsc_reflective_fs_fib X (P: X -> Type) (x:X) :
    is_contr (reflect X) -> is_contr (reflect (sigT P)) -> is_contr (reflect (P x)).
  Proof.
    intros rx rt.
    apply (contr_equiv_contr _ _
      (reflect_functor_equiv (equiv_inverse (hfiber_fibration X P x)))).
    apply rsc_reflective_fs; auto.
  Defined.

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
      (equiv_Emap ((reflect_functor f) ; H)))).
  Defined.

  (** And that over a base map in E, if the map on total spaces is in
     E, so are all fiber maps.  *)
  Section EMapBase.

    Hypotheses A B C D : Type.
    Hypotheses (f : A -> B) (g : C -> D) (h : Emap A C) (k : Emap B D).
    Hypothesis s:forall a, k (f a) == g (h a).

    Hypothesis b:B.

    Theorem fiber_map_ine : in_E (square_fiber_map f g h k s b).
    Proof.
      intros [c p].
      set (eq := three_by_three A B C D f g h k s b c (!p)).
      apply @transport with (x := !!p) (y := p).
      apply opposite_opposite.
      apply (contr_equiv_contr _ _ (equiv_inverse (reflect_functor_equiv eq))).
      apply rsc_reflective_fs.
      apply (pr2 h).
      apply (pr2 k).
    Defined.

  End EMapBase.

  (** The same thing, for maps given as fibrations. *)
  Section EMapBaseFibrations.

    Hypothesis A B : Type.
    Hypothesis (P : A -> Type) (Q : B -> Type).
    Hypothesis f : Emap A B.
    Hypothesis g : forall x, P x -> Q (f x).
    Hypothesis tot_ine : in_E (total_map f g).

    Theorem fiber_map_ine_fib (x:A) : in_E (g x).
    Proof.
      intros q.
      set (e := rsc_reflective_fs_fib
        ({a:A & f a == f x})
        (fun xs:{a:A & f a == f x} =>
          let (x,s) := xs in { p:P x & transport s (g x p) == q })
        ((x;idpath (f x)))).
      simpl in e. apply e.
      apply (pr2 f).
      apply contr_equiv_contr with
        (A := reflect { xp : sigT P & total_map f g xp == (f x;q) }).
      apply equiv_inverse, reflect_functor_equiv, three_by_three_fib.
      apply tot_ine.
    Defined.

  End EMapBaseFibrations.

  (** The reflector preserves homotopy fibers. *)
  Section ReflectFibers.

    Hypotheses (X Y : Type) (f : X -> Y) (y:Y).

    Definition reflect_fiber_emap : Emap {x:X & f x == y}
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

    Definition reflect_fiber_equiv :
      reflect {x:X & f x == y} <~>
      {rx:reflect X & reflect_functor f rx == map_to_reflect Y y}
      := invert_E_factor _ _ reflect_fiber_emap tg_in_rsc.

  End ReflectFibers.

  (** The reflector preserves homotopy pullbacks. *)
  Section ReflectPullbacks.

    Hypotheses A B C : Type.
    Hypotheses (f : A -> C) (g : B -> C).

    Let pb := {a:A & {b:B & g b == f a}}.
    Let rpb := {ra : reflect A & {rb : reflect B &
      reflect_functor g rb == reflect_functor f ra}}.

    Definition reflect_pullback_emap : Emap pb rpb.
    Proof.
      apply @total_emap_fib with (f := Emap_to_reflect A). auto.
      intros a.
      set (fc := reflect_fiber_emap B C g (f a)).
      apply (Emap_compose fc).
      apply equiv_Emap. simpl.
      set (cer := fun rb => concat_equiv_right
        (reflect_functor g rb) _ _ (!reflect_naturality f a)).
      apply total_equiv with (g := cer).
      intros x; apply (pr2 (cer x)).
    Defined.

    Let tg_in_rsc : in_rsc rpb.
    Proof.
      unfold rpb; auto.
    Defined.

    Definition reflect_pullback_equiv : reflect pb <~> rpb
      := invert_E_factor _ _ reflect_pullback_emap tg_in_rsc.

  End ReflectPullbacks.

End LexReflective.
