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
    apply Emap_cancel_left with (g := to_reflect_Emap Y).
    apply @transport with
      (P := fun g:X -> reflect Y => in_E g)
      (x := (reflect_functor f) o (to_reflect X)).
    apply funext. intros x.
    path_via ((to_reflect Y o f) x).
    apply reflect_naturality.
    exact (pr2 (Emap_compose (to_reflect_Emap X)
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
      {rx:reflect X & reflect_functor f rx == to_reflect Y y}.
    Proof.
      exists (square_fiber_map f (reflect_functor f)
        (to_reflect X) (to_reflect Y)
        (fun x => !reflect_naturality f x) y).
      intros [rx p].
      apply contr_equiv_contr with
        (A := reflect {z : {x:X & to_reflect X x == rx} &
          square_fiber_map (to_reflect X) (to_reflect Y)
           f (reflect_functor f)
           (fun x => !!reflect_naturality f x) rx z
           == (existT
             (fun y' => to_reflect Y y' == reflect_functor f rx)
             y (!p))}).
      apply reflect_functor_equiv.
      apply equiv_inverse.
      apply @transport with (y := p) (x := !(!p))
        (P := fun q => {x : {x : X & f x == y} &
          square_fiber_map f (reflect_functor f) (to_reflect X)
          (to_reflect Y) (fun x0 : X => !reflect_naturality f x0) y x ==
          (rx ; q)} <~>
        {z : {x : X & to_reflect X x == rx} &
          square_fiber_map (to_reflect X) (to_reflect Y) f
          (reflect_functor f) (fun x : X => !(!reflect_naturality f x)) rx z ==
          (y ; !p)}).
      do_opposite_opposite.
      apply three_by_three with
        (f := f)
        (g := reflect_functor f)
        (h := to_reflect X)
        (k := to_reflect Y)
        (s := fun x => !reflect_naturality f x)
        (b := y)
        (c := rx)
        (d := !p).
      apply rsc_reflective_fs.
      apply to_reflect_in_E.
      apply to_reflect_in_E.
    Defined.

    Let tg_in_rsc : in_rsc {rx:reflect X &
      reflect_functor f rx == to_reflect Y y}.
    Proof.
      auto.
    Defined.

    Definition reflect_fiber_equiv :
      reflect {x:X & f x == y} <~>
      {rx:reflect X & reflect_functor f rx == to_reflect Y y}
      := Emap_invert_factor _ _ reflect_fiber_emap tg_in_rsc.

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
      apply @total_emap_fib with (f := to_reflect_Emap A). auto.
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
      := Emap_invert_factor _ _ reflect_pullback_emap tg_in_rsc.

  End ReflectPullbacks.

  (** The classifier of objects in the subcategory *)

  Definition Rsctype := { A : Type & in_rsc A }.

  Definition rsctype_coerce_to_type : Rsctype -> Type := pr1.
  Coercion rsctype_coerce_to_type : Rsctype >-> Sortclass.

  Definition every_rsctype_in_rsc (A : Rsctype) : in_rsc A.
  Proof.
    exact (pr2 A).
  Defined.
  
  Hint Resolve every_rsctype_in_rsc.

  Definition rsctype_paths (A B : Rsctype) :
    (pr1 A) == (pr1 B) -> A == B.
  Proof.
    intros p; apply total_path with p.
    apply prop_path, in_rsc_prop.
  Defined.

  (** We now prove that [Rsctype] itself lies in the subcategory.  To
     do this, we show that any map into it can be extended along any
     E-map.  Applied to [to_reflect Rsctype] this will show the
     desired result (using [reflect_retract_in_rsc]). *)

  Section RsctypeExtend.

    Hypothesis A B : Type.
    Hypothesis e : Emap A B.
    Hypothesis P : A -> Rsctype.

    Close Scope nat_scope.      (* So we can use [*] for cartesian products. *)

    (** The extension is easy to define. *)
    Definition rscfib_Emap_extend : B -> Rsctype.
    Proof.
      intros b.
      exists (reflect {a:A & (e a == b) * (P a)}).
      auto.
    Defined.

    (** The tricky part is proving that it *is* an extension,
       i.e. that when restricted back along [e] it yields something
       equivalent to [P] again.  We do this by showing that the
       following map is an equivalence for all [a]. *)

    Let extend_cmp a : P a -> rscfib_Emap_extend (e a).
    Proof.
      intros p.
      unfold rscfib_Emap_extend, rsctype_coerce_to_type; simpl.
      apply to_reflect.
      exists a. exact (idpath (e a), p).
    Defined.

    (** We will show that [extend_cmp] is an equivalence by showing
       that it is [in_E]; this suffices because its domain and
       codomain are both [in_rsc].

       In turn, we will show it to be [in_E] by showing that its
       induced map on total spaces lies [in_E].  Here is that map; it
       goes from the total space of [P] to the total space of the
       _pullback_ of [rscfib_Emap_extend] from [B] to [A].  *)

    Let extend_cmp_tot := total_map (idmap A) extend_cmp
      : sigT P -> {a:A & rscfib_Emap_extend (e a)}.

    (** We will show that [extend_cmp_tot] lies in E by left
       cancellation, composing with maps to the total space of
       [rscfib_Emap_extend] itself.  Here is the first of these. *)

    Let extend_next1 : Emap {a:A & rscfib_Emap_extend (e a)} (sigT rscfib_Emap_extend).
    Proof.
      apply total_emap_fib with (f := e).
      intros; apply idEmap.
    Defined.

    (** The second of these is the composite of two maps, where the
       intermediate type is the total space of which
       [rscfib_Emap_extend] is the fiberwise reflection.  The map from
       [sigT P] to this total space is actually already an
       equivalence; here it is and its inverse.
       *)

    Let extend_next2a1 : (sigT P) -> {b:B & {a:A & (e a == b) * P a}}.
    Proof.
      intros [a p]; exists (e a); exists a; split; [exact (idpath (e a)) | assumption].
    Defined.

    Let extend_next2a2 : {b:B & {a:A & (e a == b) * P a}} -> (sigT P).
    Proof.
      intros [b [a [q p]]]; exists a; assumption.
    Defined.

    Let extend_next2a : Emap (sigT P) {b:B & {a:A & (e a == b) * P a}}.
    Proof.
      apply equiv_Emap.
      exists extend_next2a1.
      apply @hequiv_is_equiv with (g := extend_next2a2).
      intros [b [a [q p]]]; simpl.
      (* boring manipulation... *)
      apply total_path with q. simpl.
      apply (concat (trans_sum B A (fun b' a' => (e a' == b') * P a')
        (e a) b q a (idpath (e a), p))).
      apply total_path with (idpath a). simpl.
      path_via (transport q (idpath (e a)), transport (P := fun _ => P a) q p).
      refine (trans_prod _ (fun b' => e a == b') (fun _:B => P a) _ _ _ _ _).
      apply prod_path.
      path_via (idpath (e a) @ q).
      apply trans_is_concat.
      apply trans_trivial.
      intros [x p]; simpl; auto.
    Defined.

    (** Now we compose this equivalence with its fiberwise reflection. *)

    Let extend_next2 : Emap (sigT P) (sigT rscfib_Emap_extend).
    Proof.
      apply @Emap_compose with (Y := {b:B & {a:A & (e a == b) * P a}}).
      auto.
      apply extend_next2a.
      apply total_emap_fib with (f := idEmap B).
      intros b.
      exists (to_reflect _).
      refine (to_reflect_in_E _).
    Defined.

    (** And prove that [extend_cmp_tot] actually does factor the one
       through the other. *)

    Let extend_next_composite :
      extend_next1 o extend_cmp_tot == extend_next2.
    Proof.
      apply funext; intros [a p].
      unfold extend_next1, extend_cmp_tot, extend_next2. simpl.
      unfold total_map, idmap, compose.
      auto.
    Defined.

    (** Finally, we can put it all together, as promised. *)

    Definition rscfib_Emap_extend_compute a : rscfib_Emap_extend (e a) == P a.
    Proof.
      apply opposite, rsctype_paths, equiv_to_path; simpl.
      exists (extend_cmp a).
      apply in_rsc_in_E_is_equiv.
      apply (pr2 (P a)). auto.
      assert (ectinE : in_E extend_cmp_tot).
      apply Emap_cancel_left with (g := extend_next1).
      refine (@transport _ _ _ _ (!extend_next_composite) _).
      apply (pr2 extend_next2).
      refine (fiber_map_ine_fib _ _ _ _ (idEmap A) extend_cmp ectinE a).
    Defined.

  End RsctypeExtend.

  Theorem rsctype_in_rsc : in_rsc Rsctype.
  Proof.
    apply reflect_retract_in_rsc with (rscfib_Emap_extend
      Rsctype (reflect Rsctype) (to_reflect_Emap Rsctype) (idmap _)).
    apply (rscfib_Emap_extend_compute
      Rsctype (reflect Rsctype) (to_reflect_Emap Rsctype) (idmap _)).
  Defined.

End LexReflective.
