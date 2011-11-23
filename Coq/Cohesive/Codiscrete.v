Add LoadPath "..".
Add LoadPath "../Subcategories".
Require Import Homotopy Subtopos.

(** We begin the axiomatization of cohesive toposes with the
   codiscrete objects and their reflector $\sharp$. *)

Axiom is_codiscrete : Type -> Type.

Axiom codiscrete_is_rsf : rsf is_codiscrete.
Existing Instance codiscrete_is_rsf.
Axiom codiscrete_is_factsys : factsys is_codiscrete.
Existing Instance codiscrete_is_factsys.
Axiom codiscrete_is_lexrsc : lexrsc is_codiscrete.
Existing Instance codiscrete_is_lexrsc.

Hint Resolve reflect_in_rsc unit_in_rsc path_in_rsc sum_in_rsc.

(* To avoid Unicode symbols, in Coq we write [#] rather than $\sharp$. *)
Notation sharp := reflect.
Notation "#  X" := (reflect X) (at level 50).
(** printing # $\sharp$ *)
Notation sharp_functor := reflect_functor.
Notation "##  x" := (map_to_reflect _ x) (at level 50).
(** printing ## $\sharp$ *)

(** How to escape from #Type. *)

Definition escape (sA : # Type) : Type :=
  { psA : # {A:Type & A} & sharp_functor pr1 psA == sA }.

Theorem escape_is_codiscrete sA : is_codiscrete (escape sA).
Proof.
  unfold escape. auto.
Defined.

Hint Resolve escape_is_codiscrete.

Theorem escape_is_sharp A : # A <~> escape (## A).
Proof.
  apply @equiv_compose with (B := # {T:{B:Type & B} & pr1 T == A}).
  apply reflect_functor_equiv.
  apply hfiber_fibration with (X := Type) (P := fun T => T).
  apply reflect_preserves_fibers.
Defined.

Theorem sharp_escape_is_sharp (sA : # Type) :
  sharp_functor sharp sA == ## (escape sA).
Proof.
  generalize dependent sA.
  apply reflect_factor_dep with (X := Type). auto.
  intros A.
  path_via (## (# A)).
  apply reflect_naturality.
  apply equiv_to_path, escape_is_sharp.
Defined.
