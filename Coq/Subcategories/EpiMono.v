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
  ; map_to_reflect X := inhab
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
  apply @hequiv_is_equiv with g.
  intros f; apply funext; intros x; apply Yp.
  intros f; apply funext; intros x; apply Yp.
Defined.

Definition sum_prop_is_prop X (P : X -> Type) :
  is_prop X -> (forall x, is_prop (P x)) -> is_prop (sigT P).
Proof.
  intros Xp Pp.
  apply allpath_prop.
  intros [x p] [y q].
  apply total_path with (prop_path Xp x y).
  apply prop_path, Pp.
Defined.

Instance prop_is_factsys : factsys is_prop := {
  sum_in_rsc := sum_prop_is_prop
}.
