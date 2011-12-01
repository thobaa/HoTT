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

  Let paths_are_props : forall X (x0 x1 : X),
    is_prop X -> is_prop (x0 == x1).
  Proof.
    intros X x0 x1 Xp; apply hlevel_succ; unfold is_hlevel; apply Xp.
  Defined.

  Let modal_rect : forall X (P : is_inhab X -> Type),
    (forall mx, is_prop (P mx)) ->
    (forall x, P (inhab x)) -> (forall mx, P mx).
  Proof.
    intros; apply is_inhab_rect;
      [ auto | intros; apply prop_path; auto ].
  Defined.

  Let modal_rect_compute : forall X (P : is_inhab X -> Type)
    (Pm : forall mx, is_prop (P mx)) (f : forall x, P (inhab x)),
    (forall x, modal_rect X P Pm f (inhab x) == f x).
  Proof.
    intros; apply prop_path; auto.
  Defined.

  Instance prop_is_rsf' : rsf is_prop
  := (modal_rsf is_prop (@isprop_isprop) is_inhab (@inhab)
    is_inhab_is_prop paths_are_props modal_rect modal_rect_compute).

  Instance prop_is_factsys' : @factsys is_prop prop_is_rsf'
    := (modal_factsys is_prop (@isprop_isprop) is_inhab (@inhab)
    is_inhab_is_prop paths_are_props modal_rect modal_rect_compute).

End PropViaModal.
