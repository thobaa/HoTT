Add LoadPath "..".
Require Import Homotopy Subtopos Codiscrete.

(** In this file we axiomatize the internal structure making a topos
   into a local topos over some base topos.  This entails a subtopos
   of codiscrete objects, together with a coreflective subcategory of
   "discrete objects" which is equivalent to the category of
   codiscrete objects in a structure-respecting way.

   Since a coreflective subcategory cannot be axiomatized directly, we
   use the "external" approach and axiomatize it using operations on
   [#Type].

   As with codiscretes, we use a module type for discretes, which
   extends that for codiscretes.  An importer of this file wanting to
   work axiomatically with a local topos structure can simply say

     Declare Module Disc: Discrete.
     Import Disc.
   
   *)

Module Type Discrete.

Declare Module Codisc : Codiscrete.
Export Codisc.

(** First we assume a codiscrete subobject of [#Type]. *)
Axiom is_discrete : # Type -> Type.
Axiom is_discrete_is_prop : forall A, is_prop (is_discrete A).
Axiom is_discrete_is_codiscrete : forall A, is_codiscrete (is_discrete A).

(** Now an operation called [flat] mapping [#Type] into that subobject. *)

Axiom flat : # Type -> # Type.
Notation "♭ X" := (flat X) (at level 51, right associativity).
Axiom flat_is_discrete : forall A, is_discrete (♭ A).

Hint Resolve flat_is_discrete.

(** Every type [A] comes with a map from [flat A].  We have to express
   this using the external hom. *)

Axiom from_flat : forall A, ♭ A ^-> A.
Notation "$ x" := (from_flat _ x) (at level 51, right associativity).

(** This map is a coreflection. *)

Axiom flat_is_coreflection : forall A B, is_discrete A ->
  is_equiv (fun f : A ^-> ♭ B => (from_flat B) ^o f).

Definition flat_coreflection_equiv A B (Ad : is_discrete A)
  : (A ^-> ♭B) <~> (A ^-> B)
  := (fun f : A ^-> ♭ B => (from_flat B) ^o f ;
    flat_is_coreflection A B Ad).

Definition flat_factor {A B} (Ad : is_discrete A) :=
  flat_coreflection_equiv A B Ad ^-1.

(** The discrete objects are closed under finite limits. *)

Axiom unit_is_discrete : is_discrete eunit.

Axiom pullback_is_discrete : forall A B C (f : A ^-> C) (g : B ^-> C),
  is_discrete A -> is_discrete B -> is_discrete C ->
  is_discrete (ipullback f g).

(** It follows, in particular, that they are also closed under
   products. *)

Definition product_is_discrete A B : is_discrete A -> is_discrete B ->
  is_discrete (A #* B).
Proof.
  intros Ad Bd.
  assert (H: is_discrete (ipullback (eto_unit A) (eto_unit B))).
  apply pullback_is_discrete; auto. apply unit_is_discrete.
  exact (transport (ipullback_over_unit A B) H).
Defined.

Hint Resolve unit_is_discrete pullback_is_discrete product_is_discrete.

(** The following axioms say that the categories of discrete and
   codiscrete objects are equivalent, and that their inclusions into
   the category of types respect that equivalence. *)

Axiom flat_sharp_is_equiv : forall (A : #Type),
  eis_equiv (flat_factor (flat_is_discrete A)
    ((eto_sharp A) ^o (from_flat A))).

Axiom sharp_flat_is_equiv : forall (A : #Type),
  eis_equiv (esharp_factor (esharp_is_codiscrete A)
    ((eto_sharp A) ^o (from_flat A))).

(** This should imply that an object is discrete if and only if it is
   co-orthogonal to all Emaps (maps inverted by sharp).  Moreover, if
   we were instead to take this as a *definition* of "discrete", then
   [flat_sharp_is_equiv] and [sharp_flat_is_equiv] should be provable.
   *)

End Discrete.
