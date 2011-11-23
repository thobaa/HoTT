Add LoadPath "..".
Add LoadPath "../HIT".
Require Import Homotopy ReflectiveSubfibration IsInhab.

(** We prove that any reflective subfibration axiomatized in this way
   is *local*, in the sense that the property of belonging to it
   descends along effective epimorphisms (defined as morphisms whose
   [is_inhab]-image is their whole codomain, i.e. morphisms each of
   whose homotopy fibers is inhabited).  Thus, it is a stack for the 
   "regular toplogy".

   Similarly, and even more trivially, it is a stack for the extensive
   topology, and even the "indexed-extensive topology".
   *)

Section LocalSubfibration.

  Context {in_rsc : Type -> Type}.
  Context {is_rsf : rsf in_rsc}.
  Existing Instance is_rsf.

  Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc exp_in_rsc.

  Section EffEpi.

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

  End EffEpi.

  Section BinaryCoproduct.

    Hypothesis A B : Type.
    Hypothesis P : A+B -> Type.
    Hypothesis Pa_in_rsc : forall a, in_rsc (P (inl _ a)).
    Hypothesis Pb_in_rsc : forall b, in_rsc (P (inr _ b)).

    Theorem rsc_is_extensive_binary (ab : A+B) : in_rsc (P ab).
    Proof.
      destruct ab; auto.
    Defined.

  End BinaryCoproduct.

  Theorem rsc_is_extensive_nullary (P : Empty_set -> Type) (x:Empty_set) : in_rsc (P x).
  Proof.
    induction x.
  Defined.

  Section IndexedCoproduct.

    Hypothesis A : Type.
    Hypothesis B : A -> Type.
    Hypothesis P : sigT B -> Type.
    Hypothesis Pb_in_rsc : forall a b, in_rsc (P (a ; b)).

    Theorem rsc_is_extensive_indexed (ab:sigT B) : in_rsc (P ab).
    Proof.
      destruct ab.
      auto.
    Defined.

  End IndexedCoproduct.

End LocalSubfibration.

