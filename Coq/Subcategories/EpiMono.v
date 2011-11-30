Add LoadPath "..".
Require Import Homotopy ReflectiveSubfibration StableFactorizationSystem.
Add LoadPath "../HIT".
Require Import IsInhab.

(** As an example of a stable factorization system which is not
   reflective (i.e. does not arise from a lex reflective subcategory),
   we have

   M = monomorphisms
   E = effective epimorphisms

   The corresponding internal reflective subcategory is the category
   of h-propositions, and the reflector is [is_inhab].  Note that
   [is_inhab] does not preserve homotopy fibers or pullbacks in
   general.
   *)

Instance prop_is_rsf : rsf is_prop := {
  in_rsc_prop X := isprop_isprop
  ; reflect X := is_inhab X
  ; to_reflect X := inhab
}.
Proof.
  apply is_inhab_is_prop.
  intros X Y Yp.
  assert (g : (X -> Y) -> (is_inhab X -> Y)).
  intros f x.
  apply @is_inhab_rect_nondep with (A := X).
  auto.
  apply Yp.
  auto.
  apply @hequiv_is_equiv with g;
  intros f; apply funext; intros x; apply Yp.
Defined.

Instance prop_is_factsys : factsys is_prop := {
  sum_in_rsc := sum_isprop
}.

(* Another approach to the proof, making use of modalities.  This is
   interesting because it shows that the *dependent* eliminator of
   [is_inhab] is essentially the same as the dependent factorization
   for a modality. *)

Section PropViaModal.

  Let modal := is_inhab.
  Let to_modal := @inhab.

  Let is_modal' := is_modal modal to_modal.

  Let modal_is_modal : forall X, is_modal' (modal X).
  Proof.
    intros X; unfold is_modal', is_modal.
    apply prop_inhab_is_equiv, is_inhab_is_prop.
  Defined.

  Let paths_are_modal : forall X (x0 x1 : X),
    is_modal' X -> is_modal' (x0 == x1).
  Proof.
    intros; apply prop_inhab_is_equiv.
    apply hlevel_succ; unfold is_hlevel.
    apply (prop_inhab_equiv _ ^-1); auto.
  Defined.

  Let modal_rect : forall X (P : modal X -> Type),
    (forall mx, is_equiv (to_modal (P mx))) ->
    (forall x, P (to_modal X x)) -> (forall mx, P mx).
  Proof.
    intros; apply is_inhab_rect;
      [ auto | intros; apply prop_path, (prop_inhab_equiv _ ^-1); auto ].
  Defined.

  Let modal_rect_compute : forall X (P : modal X -> Type)
    (Pm : forall mx, is_equiv (to_modal (P mx))) (f : forall x, P (to_modal X x)),
    (forall x, modal_rect X P Pm f (to_modal X x) == f x).
  Proof.
    intros; apply prop_path, (prop_inhab_equiv _ ^-1); auto.
  Defined.

  Instance prop'_is_rsf : rsf (is_modal is_inhab (@inhab))
  := (modal_rsf modal to_modal
    modal_is_modal paths_are_modal
    modal_rect modal_rect_compute).

  Instance prop'_is_factsys : factsys (is_modal is_inhab (@inhab))
    := (modal_factsys modal to_modal
      modal_is_modal paths_are_modal
      modal_rect modal_rect_compute).

End PropViaModal.
