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
    point_eq : pointed_fun (point A) = point B }.

Arguments point_eq {A B} f : rename.

Coercion pointed_fun : PointedMap >-> Funclass.

Definition loopspace_functor {A B : PointedType} (f : PointedMap A B)
: PointedMap (loopspace A) (loopspace B).
Proof.
  refine (Build_PointedMap (loopspace A) (loopspace B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  apply moveR_Vp; simpl.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition pointedmap_compose {A B C : PointedType}
           (g : PointedMap B C) (f : PointedMap A B)
: PointedMap A C
  := Build_PointedMap A C (g o f)
                      (ap g (point_eq f) @ point_eq g).

(** ** Pointed homotopies *)

Record PointedHomotopy {A B : PointedType} (f g : PointedMap A B) :=
  { pointed_htpy : f == g ;
    point_htpy : point_eq f = pointed_htpy (point A) @ point_eq g }.

Arguments point_htpy {A B f g} p : rename.

Coercion pointed_htpy : PointedHomotopy >-> pointwise_paths.

(** Functoriality of loop spaces *)

Definition loopspace_functor_compose {A B C : PointedType}
           (g : PointedMap B C) (f : PointedMap A B)
: PointedHomotopy (loopspace_functor (pointedmap_compose g f))
                  (pointedmap_compose (loopspace_functor g) (loopspace_functor f)).
Proof.
  refine (Build_PointedHomotopy _ _
            (loopspace_functor (pointedmap_compose g f))
            (pointedmap_compose (loopspace_functor g) (loopspace_functor f))
            _ _).
  - simpl; intros p.
    rewrite (ap_compose f g), !ap_pp, ap_V, !inv_pp, !concat_pp_p.
    reflexivity.
  - simpl.
    (** Augh! *)
Abort.

(** Let's just do the unpointed version for now *)
Definition loopspace_functor_compose {A B C : PointedType}
           (g : PointedMap B C) (f : PointedMap A B)
: (loopspace_functor (pointedmap_compose g f))
  == (pointedmap_compose (loopspace_functor g) (loopspace_functor f)).
Proof.
  simpl; intros p.
  rewrite (ap_compose f g), !ap_pp, ap_V, !inv_pp, !concat_pp_p.
  reflexivity.
Defined.
