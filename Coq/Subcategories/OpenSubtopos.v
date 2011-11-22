Add LoadPath "..".
Require Import Homotopy ReflectiveSubfibration StableFactorizationSystem LexReflectiveSubcategory.

(** We prove that any proposition [U] determines an *open subtopos*: a
   lex-reflective subcategory whose objects are those [X] such that
   the canonical map [X -> (U -> X)] is an equivalence.  *)

Section OpenSubtopos.

  Hypothesis U : Type.
  Hypothesis U_is_prop : is_prop U.

  Definition oU A := U -> A.
  Definition map_to_oU A (x:A) := (fun _:U => x).

  Definition in_oU A := is_equiv (map_to_oU A).

  Global Instance oU_is_rsf : rsf in_oU := {
    in_rsc_prop A := is_equiv_is_prop (map_to_oU A)
    ; reflect A := U -> A
    ; map_to_reflect A := map_to_oU A
  }.
  Proof.
  (* reflect_in_rsc *)
    intros A.
    unfold in_oU, map_to_oU.
    apply hequiv_is_equiv with (fun a => fun u => a u u).
    intros a.
    apply funext.  intros u1. apply funext. intros u2.
    apply happly. apply map. apply prop_path; auto.
    intros a. apply funext. intros u. auto.
  (* reflect_is_reflection *)
    intros A B Bu. unfold map_to_oU.
    set (etab := (map_to_oU B ; Bu) : B <~> (U -> B)).
    apply hequiv_is_equiv with
      (fun g => (etab ^-1) o (fun f:U->A => fun u:U => g (f u))).
    intros g.
    apply funext.  intro a. unfold compose.
    equiv_moveright.
    unfold etab, map_to_oU. simpl. auto.
    intros f.
    apply funext.  intro h. unfold compose.
    equiv_moveright.
    unfold etab, map_to_oU. simpl.
    apply funext.  intro u. apply map. apply funext. intro u'.
    apply map. apply prop_path; auto.
  Defined.

  Let in_oU_reflect_equiv A (Au : in_oU A) : (A <~> (U -> A))
    := (map_to_oU A ; Au).
    
  Let in_oU_eval_inverse A (Au : in_oU A) (u:U) (f:U->A) :
    (in_oU_reflect_equiv A Au ^-1) f == f u.
  Proof.
    equiv_moveright.
    unfold in_oU_reflect_equiv, map_to_oU. simpl.
    apply funext; intro u'.
    apply map, prop_path; auto.
  Defined.

  Section Factsys.

    Hypotheses (X:Type) (P : X -> Type).
    Hypotheses Xu : in_oU X.
    Hypotheses Pu : forall x, in_oU (P x).

    Let Xe := in_oU_reflect_equiv X Xu.

    Let sum_map_back : (U -> sigT P) -> sigT P.
    Proof.
      intros f.
      set (x := (Xe ^-1) (pr1 o f)).
      exists x.
      set (Pex := in_oU_reflect_equiv (P x) (Pu x)).
      apply (Pex ^-1).
      intros u.
      set (x' := pr1 (f u)).
      apply @transport with (x := x').
      unfold x.
      unfold Xe, x'.
      apply opposite, in_oU_eval_inverse with (f := pr1 o f).
      exact (pr2 (f u)).
    Defined.

    Let sum_path (f:U->sigT P) (u:U) : (Xe ^-1) (pr1 o f) == pr1 (f u)
      := in_oU_eval_inverse X Xu u (pr1 o f).

    Let sum_path2 (xp : sigT P) : (Xe ^-1) (pr1 o (fun _:U => xp)) == pr1 xp.
    Proof.
      equiv_moveright.
      apply funext; intro u.
      unfold Xe, compose. simpl. unfold map_to_oU.
      auto.
    Defined.

    (* This proof is surprisingly tricky. *)
    Definition sum_in_oU : in_oU (sigT P).
    Proof.
      apply hequiv_is_equiv with (sum_map_back).
      intros f.
      apply funext. intros u.
      unfold map_to_oU, sum_map_back.
      apply total_path with (sum_path f u).
      simpl.
      set (g := (fun u0 : U =>
         transport (!in_oU_eval_inverse X Xu u0 (pr1 o f)) (pr2 (f u0)))).
      path_via (transport (sum_path f u) (g u)).
      unfold g, sum_path; simpl.
      set (s := in_oU_eval_inverse X Xu u (pr1 o f)).
      path_via (transport (!s @ s) (pr2 (f u))).
      apply opposite, trans_concat.
      path_via (transport (idpath _) (pr2 (f u))).
      apply happly, map. cancel_opposites.

      intros [x p].
      unfold map_to_oU, sum_map_back. simpl.
      apply total_path with (sum_path2 (x;p)). simpl.
      path_via (transport (sum_path2 (x;p)) (transport (!sum_path2 (x;p)) p)).
      equiv_moveright.
      apply funext; intro u. simpl.
      unfold map_to_oU; simpl.
      apply happly, map.
      apply opposite2.
      unfold sum_path2. simpl.
      unfold in_oU_eval_inverse.
      fold Xe. unfold compose. simpl.
      apply whisker_right.
      repeat apply map. apply funext; intro u'.
      apply constmap_map.
      path_via (transport (!sum_path2 (x;p) @ sum_path2 (x;p)) p).
      apply opposite, trans_concat.
      path_via (transport (idpath _) p).
      apply happly, map; cancel_opposites.
    Defined.

  End Factsys.

  Global Instance oU_is_factsys : factsys in_oU := {
    sum_in_rsc := sum_in_oU
  }.

  Theorem oU_reflective_fs X Y (f : X -> Y) (y : Y) :
    is_contr (U -> X) -> is_contr (U -> Y) ->
    is_contr (U -> {x:X & f x == y}).
  Proof.
    intros [x cx] [y' cy].
    exists (fun u => (existT (fun x' => f x' == y)
      (x u) (happly (cy (f o x)) u @ !happly (cy (fun _ => y)) u))).
    intros g.
    apply funext. intros u.
    assert (Xc : is_prop X).
    apply allpath_prop; intros x1 x2.
    apply @happly with (A := U) (x := u) (f := fun _ => x1) (g := fun _ => x2).
    path_via x.
    assert (Yc : is_prop Y).
    apply allpath_prop; intros y1 y2.
    apply @happly with (A := U) (x := u) (f := fun _ => y1) (g := fun _ => y2).
    path_via y'.
    apply total_path with (prop_path Xc (pr1 (g u)) (x u)).
    simpl.
    apply contr_path.
    apply Yc.
  Defined.

  Global Instance oU_is_lexrsc : lexrsc in_oU := {
    rsc_reflective_fs := oU_reflective_fs
  }.

End OpenSubtopos.
