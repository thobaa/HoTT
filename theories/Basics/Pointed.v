(* -*- mode: coq; mode: visual-line -*- *)
(** * Pointed Types *)

Require Import Overture PathGroupoids.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
Generalizable Variables A B f.

(** ** Constructions of pointed types *)

(** Any contratible type is pointed. *)
Global Instance ispointed_contr `{Contr A} : IsPointed A := center A.

(** A pi type with a pointed target is pointed. *)
Global Instance ispointed_forall `{H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a)
  := fun a => point (B a).

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A cartesian product of pointed types is pointed. *)
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(** ** Loop spaces *)

(** The type [x = x] is pointed. *)
Global Instance ispointed_loop_space A (a : A) : IsPointed (a = a) := idpath.

(** We can build an iterated loop space *)
Definition loopspace (A : PointedType) : PointedType :=
  Build_PointedType (point A = point A) idpath.

Fixpoint iterated_loopspace (n : nat) (A : Type) `{H : IsPointed A} {struct n} : PointedType
  := match n with
       | O => Build_PointedType A (@point A H)
       | S p => iterated_loopspace p (point A = point A)
     end.

(** ** Pointed functions *)

Record PointedMap (A B : PointedType) :=
  { pointed_fun : A -> B ;
    ispointed_fun : pointed_fun (point A) = point B }.

Arguments ispointed_fun {A B} f : rename.

Coercion pointed_fun : PointedMap >-> Funclass.

Definition loopspace_functor {A B : PointedType} (f : PointedMap A B)
: PointedMap (loopspace A) (loopspace B).
Proof.
  refine (Build_PointedMap (loopspace A) (loopspace B)
            (fun p => (ispointed_fun f)^ @ (ap f p @ ispointed_fun f)) _).
  apply moveR_Vp; simpl.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.
