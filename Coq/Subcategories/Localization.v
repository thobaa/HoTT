Add LoadPath "..".
Require Export Homotopy Subtopos.

Section Localization.

  Context {I : Type}.
  Context {S T : I -> Type}.
  Hypothesis f : forall i, S i -> T i.

  Definition is_local Z := forall i, is_equiv (fun g : T i -> Z => g o f i).

  Definition local_equiv Z (Zl : is_local Z) i :
    (T i -> Z) <~> (S i -> Z)
    := (fun g : T i -> Z => g o f i ; Zl i).

  (** The definition of localization as a higher inductive type would be

     Inductive localize X :=
     | to_local : X -> localize X
     | local_extend : forall (i:I) (h : S i -> localize X),
         T i -> localize X
     | local_extension : forall (i:I) (h : S i -> localize X) (s : S i),
         local_extend i h (f i s) == h s
     | local_unextension : forall (i:I) (g : T i -> localize X) (t : T i),
         local_extend i (g o f i) t == g t
     | local_triangle : forall (i:I) (g : T i -> localize X) (s : S i),
         local_unextension i g (f i s) == local_extension i (g o f i) s.

     The idea is to specify exactly all the data necessary in order to
     make [localize X] be [f]-local.
     *)

  Axiom localize : Type -> Type.

  Section LocalizationAxioms.

    Context {X : Type}.

    Axiom to_local : X -> localize X.

    Axiom local_extend : forall (i:I) (h : S i -> localize X),
      T i -> localize X.

    Axiom local_extension : forall (i:I) (h : S i -> localize X) (s : S i),
      local_extend i h (f i s) == h s.

    Axiom local_unextension : forall (i:I) (g : T i -> localize X) (t : T i),
      local_extend i (g o f i) t == g t.

    Axiom local_triangle : forall (i:I) (g : T i -> localize X) (s : S i),
      local_unextension i g (f i s) == local_extension i (g o f i) s.
  
    Context {P : localize X -> Type}.

    Axiom localize_rect : forall
      (dto_local : forall x:X, P (to_local x))
      (dlocal_extend : forall (i:I) (h : S i -> localize X)
        (dh : forall s, P (h s)) (t : T i),
        P (local_extend i h t))
      (dlocal_extension : forall (i:I) (h : S i -> localize X)
        (dh : forall s, P (h s)) (s : S i),
        transport (local_extension i h s)
        (dlocal_extend i h dh (f i s))
        == dh s)
      (dlocal_unextension : forall (i:I) (g : T i -> localize X)
        (dg : forall t, P (g t)) (t : T i),
        transport (local_unextension i g t)
        (dlocal_extend i (g o f i) (fun s => dg (f i s)) t)
        == dg t)
      (dlocal_triangle : forall (i:I) (g : T i -> localize X)
        (dg : forall t, P (g t)) (s : S i),
        dlocal_unextension i g dg (f i s)
        ==
        (map (fun p =>
          transport p
          (dlocal_extend i (g o f i) (fun s => dg (f i s)) (f i s)))
        (local_triangle i g s))
        @
        dlocal_extension i (g o f i) (fun s => dg (f i s)) s)
      (lx : localize X), P lx.

    (* We had to put all of the d... hypotheses explicitly into the
       type of [localize_rect], otherwise it wouldn't get generalized
       with respect to them (since its type doesn't depend on them).
       But now we can assert them as hypotheses, to simplify the
       statements of the computation rules. *)

    Hypothesis dto_local : forall x:X, P (to_local x).

    Hypothesis dlocal_extend : forall (i:I) (h : S i -> localize X)
      (dh : forall s, P (h s)) (t : T i),
      P (local_extend i h t).

    Hypothesis dlocal_extension : forall (i:I) (h : S i -> localize X)
      (dh : forall s, P (h s)) (s : S i),
      transport
      (local_extension i h s)
      (dlocal_extend i h dh (f i s))
      ==
      dh s.

    Hypothesis dlocal_unextension : forall (i:I) (g : T i -> localize X)
      (dg : forall t, P (g t)) (t : T i),
      transport
      (local_unextension i g t)
      (dlocal_extend i (g o f i) (fun s => dg (f i s)) t)
      ==
      dg t.

    Hypothesis dlocal_triangle : forall (i:I) (g : T i -> localize X)
      (dg : forall t, P (g t)) (s : S i),
      dlocal_unextension i g dg (f i s)
      ==
      trans2 (local_triangle i g s)
        (dlocal_extend i (g o f i) (fun s => dg (f i s)) (f i s))
      @
      dlocal_extension i (g o f i) (fun s => dg (f i s)) s.

    Let my_rect := localize_rect dto_local dlocal_extend dlocal_extension dlocal_unextension dlocal_triangle.

    Axiom to_local_compute :
      forall (x:X),
        my_rect (to_local x) ==
        dto_local x.

    (** The following four axioms are actually completely unnecessary
       (fortunately!).  Since together, the last four constructors of
       [localize] inhabit an h-proposition, their actual values make
       no difference, only the fact that they exist.  However, for
       completeness, we state them anyway; the reader may verify by
       commenting them out that they are never actually used.  *)

    Axiom local_extend_compute :
      forall (i:I) (h : S i -> localize X) (t : T i),
        my_rect (local_extend i h t) ==
        dlocal_extend i h (fun s => my_rect (h s)) t.

    Axiom local_extension_compute :
      forall (i:I) (h : S i -> localize X) (s : S i),
        map_dep my_rect (local_extension i h s)
        ==
        map (transport (local_extension i h s))
        (local_extend_compute i h (f i s))
        @
        dlocal_extension i h (fun s => my_rect (h s)) s.
        
    Axiom local_unextension_compute :
      forall (i:I) (g : T i -> localize X) (t : T i),
        map_dep my_rect (local_unextension i g t)
        ==
        map (transport (local_unextension i g t))
        (local_extend_compute i (g o f i) t)
        @
        dlocal_unextension i g (fun t => my_rect (g t)) t.

    Axiom local_triangle_compute :
      forall (i:I) (g : T i -> localize X) (s : S i),
        map2_dep my_rect (local_triangle i g s)
        ==
        local_unextension_compute i g (f i s)
        @
        whisker_left
        (map (transport (local_unextension i g (f i s)))
          (local_extend_compute i (g o f i) (f i s)))
        (dlocal_triangle i g (fun t => my_rect (g t)) s)
        @
        !concat_associativity _ _ _ _ _
        (map (transport (local_unextension i g (f i s)))
          (local_extend_compute i (g o f i) (f i s)))
        (trans2 (local_triangle i g s)
          (dlocal_extend i (g o f i) (fun s0 => my_rect (g (f i s0))) (f i s)))
        (dlocal_extension i (g o f i) (fun s0 => my_rect (g (f i s0))) s)
        @
        whisker_right
        (dlocal_extension i (g o f i) (fun s0 => my_rect (g (f i s0))) s)
        (trans2_naturality (local_triangle i g s)
          (local_extend_compute i (g o f i) (f i s)))
        @
        concat_associativity _ _ _ _ _
        (trans2 (local_triangle i g s)
          (my_rect (local_extend i (g o f i) (f i s))))
        (map (transport (local_extension i (g o f i) s))
          (local_extend_compute i (g o f i) (f i s)))
        (dlocal_extension i (g o f i) (fun s0 => my_rect (g (f i s0))) s)
        @
        whisker_left
        (trans2 (local_triangle i g s)
          (my_rect (local_extend i (g o f i) (f i s))))
        (! local_extension_compute i (g o f i) s).

  End LocalizationAxioms.

  (* These tactics really should be globally defined. *)

  Ltac local_compute_in s := 
    match s with
      | appcontext cxt [ (@localize_rect ?X0 ?P0 ?f1 ?f2 ?f3 ?f4 ?f5 (to_local ?x0)) ] =>
        let h := fresh in
          set (h := f1);
            let mid := context cxt[h x0] in
              path_via' mid;
              first [
                repeat apply_happly;
                refine (@to_local_compute X0 P0 h f2 f3 f4 f5 x0)
              | repeat apply_happly;
                apply opposite;
                refine (@to_local_compute X0 P0 h f2 f3 f4 f5 x0)
              | unfold h; clear h ]
    end.

  Ltac local_compute :=
    try (
      match goal with
        |- ?s == ?t => first [ local_compute_in s | local_compute_in t ]
      end
    ); auto.

  (** It's easy to prove that a localization is local. *)

  Lemma localize_is_local X : is_local (localize X).
  Proof.
    intros i.
    apply @hequiv_is_equiv with (g := local_extend i).
    intros h. apply funext; intros s; unfold compose; simpl.
    apply local_extension.
    intros g; apply funext; intros t.
    apply local_unextension.
  Defined.

  (** For anything more than this, we need to reformulate the
     eliminator in a more useful way.  The new eliminator
     [localize_rect'] defined below says that we can define a section
     of a fibration [P] over [localize X] if

     (1) we are given a section of [P] restricted along [to_local], and

     (2) for any [i] and any [g : T i -> localize X], precomposing
     with [f i] induces an equivalence between sections of [P] over
     [g] and sections of [P] over [g o f i].

     In particular, this includes the obvious desirable non-dependent
     eliminator, which says that if [Y] is local, then any [X -> Y]
     can be extended to [localize X].  (We will state this as
     [local_factor] below.)  The hypothesis of the dependent version
     sort of says that "[P] is local over [localize X]".  Note that it
     is *not* the same as saying that all the fibers of [P] are local.
     *)

  Section LocalizeRect'.

    Context {X : Type}.
    Context {P : localize X -> Type}.
    Hypothesis k : forall x, P (to_local x).
    Hypothesis IH : forall (i:I) (g : T i -> localize X), is_equiv (fun g':forall t:T i, P (g t) => (fun s:S i => g' (f i s))).

    Let IHe i g : (forall t, P (g t)) <~> (forall s, P (g (f i s)))
      := (fun g' s => g' (f i s) ; IH i g).

    Program Definition localize_rect' : forall lx, P lx
        := @localize_rect X P k _ _ _ _.
    Next Obligation.
      intros.
      revert t.
      apply (IHe i (local_extend i h) ^-1).
      intros s.
      apply @transport with (x := h s).
      apply opposite, local_extension.
      apply dh.
    Defined.
    Next Obligation.
      intros.
      unfold localize_rect'_obligation_1.
      set (H := (fun s0 : S i => transport (!local_extension i h s0) (dh s0))).
      path_change (transport (local_extension i h s)
        ((IHe i (local_extend i h)) ((IHe i (local_extend i h) ^-1) H) s)).
      fpath_via (transport (local_extension i h s) (H s)).
      apply inverse_is_section.
      apply trans_trans_opp.
    Defined.
    Next Obligation.
      intros.
      unfold localize_rect'_obligation_1.
      spath_using (transport (local_unextension i g t)
        ((IHe i (local_extend i (g o f i)) ^-1)
          (fun s : S i =>
            transport (!local_unextension i g (f i s)) (dg (f i s))) t))
      s (@local_triangle).
      set (H := fun t => transport (!local_unextension i g t) (dg t)).
      path_change (transport (local_unextension i g t)
        ((IHe i (local_extend i (g o f i)) ^-1)
          (IHe i (local_extend i (g o f i)) H)
          t)).
      fpath_using (transport (local_unextension i g t) (H t)) @inverse_is_retraction.
      apply trans_trans_opp.
    Defined.
    Next Obligation.
      intros.
      unfold localize_rect'_obligation_1.
      unfold localize_rect'_obligation_2.
      unfold localize_rect'_obligation_3.
      set (le := local_extend i (g o f i)).
      set (len := local_extension i (g o f i) s).
      set (ulen := local_unextension i g (f i s)).
      set (lt := local_triangle i g s : ulen == len).
      match goal with
        |- ?source == ?a2 @ ?b2 =>
          path_change (trans2 lt ((IHe i le ^-1)
            (fun s0 : S i =>
              transport (!local_extension i (g o f i) s0) (dg (f i s0)))
            (f i s)) @ b2)
      end.
      associate_left.
      match goal with
        |- ?source ==
          (trans2 lt ?a2 @ map (transport len) ?b2) @ ?c2 =>
          path_via ((map (transport ulen) b2 @ trans2 lt (
            transport (!len) (dg (f i s)))) @ c2)
      end.

      assert (K :
        happly_dep
        (map (IHe i le ^-1)
          (funext_dep (fun s0:S i => trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0)))))
        (f i s)
        @
        happly_dep (inverse_is_section (IHe i le)
          (fun s0 : S i => transport (!local_unextension i g (f i s0)) (dg (f i s0)))) s
        @
        trans2 (opposite2 lt) (dg (f i s))
        ==
        (happly_dep
          (inverse_is_section (IHe i le)
            (fun s0 : S i =>
              transport (!local_extension i (g o f i) s0) (dg (f i s0)))) s)
      ).
      match goal with
        |- (?a1 @ ?b1) @ ?c1 == ?target =>
          path_via ((happly_dep
            (map (IHe i le)
              (map (IHe i le ^-1)
            (funext_dep
            (fun s0 : S i =>
             trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0))))))
            s @ b1) @ c1)
      end.
      apply opposite.
      apply map_precompose_dep with
        (p := (map (IHe i le ^-1)
        (funext_dep
           (fun s0 : S i =>
            trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0))))))
        (h := f i) (a := s).
      (* If only [undo_compose_map] could call [fpath_using]. *)
      undo_compose_map.
      fpath_simplify' compose_map.
      path_via (happly_dep
        ((map (IHe i le o (IHe i le ^-1))
         (funext_dep
            (fun s0 : S i =>
             trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0)))))
        @
        (inverse_is_section (IHe i le)
         (fun s0 : S i =>
          transport (!local_unextension i g (f i s0)) (dg (f i s0))))) s
        @ trans2 (opposite2 lt) (dg (f i s))).
      apply opposite.
      apply happly_dep_concat with
        (p := (map (IHe i le o (IHe i le ^-1))
        (funext_dep
           (fun s0 : S i =>
            trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0))))))
        (q := (inverse_is_section (IHe i le)
        (fun s0 : S i =>
         transport (!local_unextension i g (f i s0)) (dg (f i s0)))))
        (x := s).
      fpath_via (happly_dep
        (inverse_is_section (IHe i le)
         (fun s0 : S i =>
          transport (!local_extension i (g o f i) s0) (dg (f i s0))) @
       funext_dep
         (fun s0 : S i =>
          trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0)))) s
        @  trans2 (opposite2 lt) (dg (f i s))).
      refine (homotopy_naturality_toid _
        (IHe i le o (IHe i le ^-1))
        (inverse_is_section (IHe i le)) _ _ _).
      path_via ((happly_dep
        (inverse_is_section (IHe i le)
          (fun s0 : S i =>
            transport (!local_extension i (g o f i) s0) (dg (f i s0)))) s
          @ happly_dep (funext_dep
            (fun s0 : S i =>
              trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0)))) s)
        @ trans2 (opposite2 lt) (dg (f i s))).
      apply happly_dep_concat with
        (p := (inverse_is_section (IHe i le)
        (fun s0 : S i =>
         transport (!local_extension i (g o f i) s0) (dg (f i s0)))))
        (q := (funext_dep
        (fun s0 : S i =>
         trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0)))))
        (x := s).
      associate_right.
      apply whisker_left_toid.
      set (H := (fun s0 : S i =>
         trans2 (opposite2 (!local_triangle i g s0)) (dg (f i s0)))).
      path_via (H s @ trans2 (opposite2 lt) (dg (f i s))).
      apply funext_dep_compute with (p := H) (x := s).
      unfold H; clear H.
      moveright_onright. cancel_units. fold lt.

      fpath_using (trans2 (!opposite2 lt) (dg (f i s))) @trans2_opp.
      apply opposite2_opposite.

      apply (fun p => concat p
         (whisker_right
           (trans_trans_opp len (dg (f i s)))
           (whisker_right
             (trans2 lt (transport (!len) (dg (f i s))))
             (map2 (transport ulen) K)))).
      clear K.
      do_concat_map.
      associate_right.
      match goal with
        |- ?source == ?a2 @ (?b2 @ ?c2) =>
          path_via (a2 @ (b2 @ trans_trans_opp ulen (dg (f i s))))
      end.
      2:associate_left; refine (trans_trans_opp2 _ _ _ _ ulen len lt (dg (f i s))).
      associate_left.
      undo_concat_map.
      match goal with
        |- ?source == ?a2 @ ?b2 => 
          fpath_via (a2 @
            happly_dep
            (map (IHe i le) (inverse_is_retraction (IHe i le)
              (fun t0 => transport (!local_unextension i g t0) (dg t0)))) s)
      end.
      2:apply inverse_triangle with
        (w := IHe i le)
        (x := (fun t0 : T i => transport (!local_unextension i g t0) (dg t0))).
      match goal with
        |- ?source == ?a2 @ ?b2 => 
          spath_using (a2 @ happly_dep
            (inverse_is_retraction (IHe i le)
              (fun t0 : T i => transport (!local_unextension i g t0) (dg t0)))
            (f i s))
          s' @trans2_is_happly
      end.
      apply opposite.
      apply map_precompose_dep with
        (p := (inverse_is_retraction (IHe i le)
          (fun t0 : T i => transport (!local_unextension i g t0) (dg t0))))
        (h := f i)
        (a := s).
    Defined.

    (** And the computation rule for our new eliminator. *)

    Lemma localize_rect'_compute (x : X) :
      localize_rect' (to_local x) == k x.
    Proof.
      unfold localize_rect'.
      local_compute.
    Defined.

  End LocalizeRect'.

  (** Now we define the non-dependent eliminator, which is
     factorization of maps into a local object. *)

  Section LocalizeFactor.

    Context {X Y : Type}.
    Hypothesis Yl : is_local Y.

    Definition localize_factor (k : X -> Y) : (localize X -> Y).
    Proof.
      apply localize_rect'. auto.
      intros; apply Yl.
    Defined.

    Definition localize_factor_factors (k : X -> Y) (x:X) :
      localize_factor k (to_local x) == k x.
    Proof.
      unfold localize_factor.
      apply @localize_rect'_compute with (P := fun _ => Y).
    Defined.
  
    Program Definition localize_factor_unfactors (k : localize X -> Y)
      : forall lx, localize_factor (k o to_local) lx == k lx
      :=  @localize_rect' X
      (fun lx => localize_factor (k o to_local) lx == k lx)
      (@localize_rect'_compute X (fun _ => Y) _ _)
      (fun i g => hequiv_is_equiv _ _ _ _).
    Next Obligation.
      intros k i g IH t.
      change ((localize_factor (k o to_local) o g) t == (k o g) t).
      apply happly.
      apply (equiv_map_equiv (local_equiv Y Yl i) ^-1).
      apply funext. intros s.
      unfold local_equiv; simpl. apply IH.
    Defined.
    Next Obligation.
      intros k i g IH.
      unfold localize_factor_unfactors_obligation_1.
      apply funext_dep. intros s.
      set (eqm := (@equiv_map_equiv _ _
          (localize_factor (k o @to_local X) o g) (k o g) 
          (local_equiv Y Yl i))).
      apply (concat (!map_precompose _ _ (f i) 
        (eqm ^-1 (funext (fun s0 : S i => IH s0))) s)).
      change (happly (eqm (eqm ^-1 (funext (fun s0 : S i => IH s0)))) s == IH s).
      apply_happly.
      path_via (happly (funext (fun s0 => IH s0))).
      apply inverse_is_section.
      apath_using (happly (funext IH)) s' @funext_compute.
    Defined.
    Next Obligation.
      intros k i g IH.
      unfold localize_factor_unfactors_obligation_1.
      apply funext_dep; intros t.
      set (eqm := (@equiv_map_equiv _ _
          (localize_factor (k o @to_local X) o g) (k o g) 
          (local_equiv Y Yl i))).
      fpath_via (happly (eqm ^-1
        (funext (fun s => happly (funext IH) (f i s)))) t).
      apply funext_dep; intros s.
      apply opposite, funext_compute with (p := IH).
      apath_via (happly (eqm ^-1 (funext (fun s =>
        happly (map (local_equiv Y Yl i) (funext IH)) s)))) s.
      refine (!map_precompose _ _ _ (funext IH) s).
      fpath_via (happly (eqm ^-1 (eqm (funext IH))) s).
      unfold eqm, equiv_map_equiv, equiv_coerce_to_function. simpl.
      path_via (funext (happly
        (map (fun g0 : T i -> Y => g0 o f i) (funext IH)))).
      path_change ((strong_funext_equiv _ _ ^-1)
        ((strong_funext_equiv _ _)
          (map (fun g0 : T i -> Y => g0 o f i) (funext IH)))).
      apply inverse_is_retraction.
      path_via (happly (funext IH)).
      apply inverse_is_retraction.
      apply funext_dep; intros t';
        apply funext_compute with (p := IH) (x := t').
    Defined.

  End LocalizeFactor.

  (** The universal property of localization.  *)

  Lemma localize_is_localization X Y : is_local Y ->
    is_equiv (fun k : localize X -> Y => k o to_local).
  Proof.
    intros Yl.
    apply hequiv_is_equiv with (g := localize_factor Yl).
    intros k; apply funext; intros x; unfold compose; simpl.
    apply localize_factor_factors.
    intros k; apply funext; intros lx; unfold compose; simpl.
    apply localize_factor_unfactors.
  Defined.

  (** Therefore, local objects form a reflective subfibration. *)

  Global Instance local_is_rsf : rsf is_local := {
    reflect := localize
    ; reflect_in_rsc := localize_is_local
    ; to_reflect := @to_local
    ; reflect_is_reflection := localize_is_localization
  }.
  Proof.
    intros; unfold is_local; apply forall_isprop;
      intros; apply is_equiv_is_prop.
  Defined.

End Localization. 

(** Conversely, modulo size issues, every reflective subfibration is a
   localization. *)

Section RscIsLocalization.

  Context {in_rsc : Type -> Type} {is_rsf : rsf in_rsc}.
  Existing Instance is_rsf.

  Let I := Type.
  Let S (i:I) := i.
  Let T (i:I) := reflect i.
  Let f (i:I) := to_reflect i.

  Theorem rsc_is_localization A : in_rsc A <~> is_local f A.
  Proof.
    apply prop_iff_equiv; try apply in_rsc_prop.
    intros Ar i.
    apply reflect_is_reflection; auto.
    intros Al.
    apply reflect_retract_in_rsc with
      (r := local_equiv f A Al A ^-1 (idmap A)).
    intros x.
    change ((local_equiv f A Al A) ((local_equiv f A Al A ^-1) (idmap A)) x == idmap A x).
    apply happly.
    apply inverse_is_section.
  Defined.

End RscIsLocalization.

(** If all the types [T i] are [unit], then the reflective
   subfibration is actually a factorization system. *)

Section LocalizationFactsys.

  Context {I : Type}.
  Hypothesis S : I -> Type.
  Let T := fun _:I => unit.
  Let f (i:I) (s:S i) := tt.

  Program Definition sum_is_local (X : Type) (P : X -> Type)
    (Xl : is_local f X) (Pl : forall x, is_local f (P x)) :
    is_local f (sigT P)
      := fun i => hequiv_is_equiv _ _
        (fun g => funext (fun s => total_path _ _ _ _ _ _))
        (fun g => funext (fun s => total_path _ _ _ _ _ _)).
  Next Obligation.
    intros X P Xl Pl i g u. clear u.
    exists (local_equiv f X Xl i ^-1 (pr1 o g) tt).
    apply (local_equiv f (P _) (Pl _) i ^-1).
    intros s.
    apply @transport with
      (P := P)
      (x := pr1 (g s)).
    exact (!happly (inverse_is_section (local_equiv f X Xl i) (pr1 o g)) s).
    exact (pr2 (g s)).
    constructor.
  Defined.
  Next Obligation.
    intros X P Xl Pl i g s. unfold sum_is_local_obligation_1.
    unfold compose; simpl.
    change ((local_equiv f X Xl i) ((local_equiv f X Xl i ^-1)
      (fun x : S i => (pr1 o g) x)) s == (pr1 o g) s).
    apply happly, inverse_is_section.
  Defined.
  Next Obligation.
    intros X P Xl Pl i g s.
    unfold sum_is_local_obligation_1.
    unfold sum_is_local_obligation_2.
    simpl.
    set (H := (fun s0 : S i =>
         transport
           (!happly (inverse_is_section (local_equiv f X Xl i) (pr1 o g)) s0)
           (pr2 (g s0)))).
    path_via (transport
      (happly (inverse_is_section (local_equiv f X Xl i) (pr1 o g)) s)
      (H s)).
    path_change ((local_equiv f (P ((local_equiv f X Xl i ^-1) (pr1 o g) tt))
      (Pl ((local_equiv f X Xl i ^-1) (pr1 o g) tt)) i)
    ((local_equiv f (P ((local_equiv f X Xl i ^-1) (pr1 o g) tt))
      (Pl ((local_equiv f X Xl i ^-1) (pr1 o g) tt)) i ^-1) H) s).
    apply_happly; apply inverse_is_section.
    apply trans_trans_opp.
  Defined.
  Next Obligation.
    intros X P Xl Pl i g u. unfold sum_is_local_obligation_1. simpl.
    destruct u.
    change ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt == (pr1 o g) tt).
    apply_happly.
    apply inverse_is_retraction.
  Defined.
  Next Obligation.
    intros X P Xl Pl i g u.
    unfold sum_is_local_obligation_1.
    unfold sum_is_local_obligation_4.
    simpl.
    destruct u.
    change (transport
     (happly (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g)) tt)
     ((local_equiv f (P ((local_equiv f X Xl i ^-1)
       ((local_equiv f X Xl i) (pr1 o g)) tt))
         (Pl ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         i ^-1)
        (fun s : S i =>
         transport
           (!happly (inverse_is_section (local_equiv f X Xl i)
             ((local_equiv f X Xl i) (pr1 o g))) s)
           (pr2 ((g o f i) s))) tt) == pr2 (g tt)).
    path_via (transport
     (happly (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g)) tt)
     ((local_equiv f
         (P ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         (Pl ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         i ^-1)
        (fun s : S i =>
         transport
           (!happly
             (map (local_equiv f X Xl i)
               (inverse_is_retraction (local_equiv f X Xl i)
                  (pr1 o g))) s)
           (pr2 ((g o f i) s))) tt)).
    spath_simplify' Z @inverse_triangle.
    path_via (transport
     (happly (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g)) tt)
     ((local_equiv f
         (P ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         (Pl ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         i ^-1)
        (fun s : S i =>
         transport
           (!happly
             (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g)) (f i s))
           (pr2 ((g o f i) s))) tt)).
    spath_simplify' s @map_precompose.
    apply map_precompose with (h := f i)
      (p := (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g)))
      (a := s).
    set (H := (fun u : unit =>
      match u with tt =>
         transport
           (!happly (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g))
               tt) (pr2 (g tt)) end)).
    path_change (transport
     (happly (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g)) tt)
     ((local_equiv f
         (P ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         (Pl ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         i ^-1)
        (local_equiv f
         (P ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         (Pl ((local_equiv f X Xl i ^-1) ((local_equiv f X Xl i) (pr1 o g)) tt))
         i H) tt)).
    path_via (transport
     (happly (inverse_is_retraction (local_equiv f X Xl i) (pr1 o g)) tt)
     (H tt)).
    apply_happly; apply inverse_is_retraction.
    apply trans_trans_opp.
  Defined.

  Global Instance local_is_factsys : factsys (is_local f) := {
    sum_in_rsc := sum_is_local
  }.

  (** When we localize at a family of maps of this sort, we are
     effectively localizing at the fibration from [S] to [I], and also
     all of its pullbacks. *)

  Program Definition local_inverts_fib A :
    (is_local f A) <~>
    forall J (n : J -> I), is_equiv (fun g:J->A => g o pr1 : sigT (S o n) -> A)
    := prop_iff_equiv _ _ _ _
       (fun Al J n => hequiv_is_equiv _ _ _ _)
       _.
  Next Obligation.
    intros; apply in_rsc_prop.
  Defined.
  Next Obligation.
    intros;
      apply forall_isprop; intros; apply forall_isprop; intros;
      apply is_equiv_is_prop.
  Defined.
  Next Obligation.
    intros A Al J n h j.
    refine (local_equiv f A Al (n j) ^-1 _ tt).
    intros s; apply h; exists j; exact s.
  Defined.
  Next Obligation.
    intros A Al J n g; unfold local_inverts_fib_obligation_1.
    apply funext; intros [j s]. unfold compose; simpl.
    set (gj := fun s0 : S (n j) => g (existT (S o n) j s0)).
    change ((local_equiv f A Al (n j)) ((local_equiv f A Al (n j) ^-1) gj) s == gj s).
    apply_happly. apply inverse_is_section.
  Defined.
  Next Obligation.
    intros A Al J n h; unfold local_inverts_fib_obligation_1.
    apply funext; intros j. unfold compose; simpl.
    change ((local_equiv f A Al (n j) ^-1) ((local_equiv f A Al (n j)) (fun _:unit => h j)) tt == (fun _:unit => h j) tt).
    apply_happly; apply inverse_is_retraction.
  Defined.
  Next Obligation.
    intros A H i.
    set (H1 := ((fun g : unit -> A => g o pr1) ; (H unit (fun _ => i)))
      : (unit -> A) <~> (sigT (fun _:unit => S i) -> A)).
    set (m := fun s: S i => (existT (fun _ => S i) tt s)).
    assert (meq : is_equiv m).
    apply hequiv_is_equiv with
      (g := fun us:sigT (fun _:unit => S i) => let (_,s) return S i := us in s).
    intros [u s]; destruct u; unfold m; auto.
    intros s; unfold m; auto.
    set (H2 := precomp_equiv _ _ A (m; meq)).
    set (K := equiv_compose H1 H2).
    apply @transport with (x := pr1 K).
    2:apply (pr2 K).
    apply funext; intros g. apply funext; intros s.
    simpl. unfold compose. unfold m, f. auto.
  Defined.

End LocalizationFactsys.

(** Conversely, modulo size issues, every stable factorization system
   is a localization at such a class of maps. *)

Section FactsysIsLocalization.

  Context {in_rsc : Type -> Type} {is_rsf : rsf in_rsc} {is_factsys : factsys in_rsc}.
  Existing Instance is_rsf.
  Existing Instance is_factsys.

  Let I := sigT reflect.
  Let S (i:I) := hfiber (to_reflect (pr1 i)) (pr2 i).
  Let T := fun _:I => unit.
  Let f (i:I) (s:S i) := tt.

  Theorem factsys_is_localization A : in_rsc A <~> is_local f A.
  Proof.
    apply prop_iff_equiv; try apply in_rsc_prop.
    intros Ar i.
    unfold f, compose; simpl.
    set (H1 := reflection_equiv (S i) A Ar).
    set (H2 := precomp_equiv _ _ A
      (contr_equiv_unit (reflect (S i))
      (to_reflect_in_E (pr1 i) (pr2 i)))).
    apply (pr2 (equiv_compose H2 H1)).
    intros Al.
    apply (rsc_is_localization A ^-1).
    intros B.
    set (H1 := precomp_equiv _ _ A
      (fibration_replacement_equiv B (reflect B) (to_reflect B))).
    set (H2eq := local_inverts_fib S A Al (reflect B)
      (fun rb => (B ; rb))).
    set (H2 := ((fun g : reflect B -> A => g o pr1) ; H2eq) : equiv _ _).
    change (is_equiv (equiv_compose H2 H1)).
    apply (pr2 (equiv_compose H2 H1)).
  Defined.

End FactsysIsLocalization.

(** Unfortunately, we don't seem to have such a nice characterization
   of left exact localizations. *)
