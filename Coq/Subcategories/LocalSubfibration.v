Add LoadPath "..".
Add LoadPath "../HIT".
Require Import Homotopy ReflectiveSubfibration IsInhab.

(** We prove that any reflective subfibration axiomatized in this way
   is *local*, in the sense that the property of belonging to it
   descends along effective epimorphisms (defined as morphisms whose
   [is_inhab]-image is their whole codomain, i.e. morphisms each of
   whose homotopy fibers is inhabited). *)

Section LocalSubfibration.

  Context {in_rsc : Type -> Type}.
  Context {is_rsf : rsf in_rsc}.
  Existing Instance is_rsf.

  Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc exp_in_rsc.

  Hypothesis A B : Type.
  Hypothesis f : A -> B.
  Hypothesis P : B -> Type.
  Hypothesis f_ee : forall b, is_inhab {x:A & f x == b}.
  Hypothesis Pf_in_rsc : forall a, in_rsc (P (f a)).

  Theorem rsc_is_local (b:B) : in_rsc (P b).
  Proof.
    apply @is_inhab_rect_nondep with (A := {x:A & f x == b}).
    intros [x p].
    apply @transport with (P := fun x => in_rsc (P x)) (x := f x); auto.
    apply prop_path, in_rsc_prop.
    apply f_ee.
  Defined.

End LocalSubfibration.
