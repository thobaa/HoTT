(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import types.Empty types.Sum.
Require Import hit.Truncations.
Open Scope equiv_scope.

(** * HProp Logic

This file is called `Logic.HPropLogic` rather than `Logic.HProp` since in the latter case, `Import HProp` would find it instead of the desired `HoTT.HProp` in the root theories directory. *)

(** ** True *)

Global Notation htrue := Unit (only parsing).

(** ** False *)

Global Notation hfalse := Empty (only parsing).

Definition hfalse_elim (Q : Type) `{IsHProp Q}
: hfalse -> Q
:= Empty_rect (fun _ => Q).

(** ** Negation *)

Global Notation hnot := not (only parsing).

(** ** Disjunction *)

Definition hor (P Q : Type) : Type := merely (P + Q).
Global Notation "P \/ Q" := (hor P Q) (at level 85, right associativity) : type_scope.

Definition hor_inl {P Q} (p : P) : P \/ Q
  := (tr (inl p)).

Definition hor_inr {P Q} (q : Q) : P \/ Q
  := (tr (inr q)).
  
Definition hor_elim {P Q R} `{IsHProp R}
: (P -> R) -> (Q -> R) -> (P \/ Q -> R).
Proof.
  intros p q.
  apply Trunc_rect; try exact _.
  apply sum_rect; assumption.
Defined.

(** ** Existential quantification *)

Definition hex {A : Type} (P : A -> Type) : Type
  := merely { a : A & P a }.

(** The following notation allows us to write [hexists (x:A), P x] rather than [hex (fun (x:A) => P x)]. *)
Global Notation "'hexists' x .. y , p"
  := (hex (fun x => .. (hex (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity)
  : type_scope.

Definition hexist A P (a : A) (p :  P a) : hexists x, P x
  := tr (a ; p).

Definition hexists_elim (A : Type) (P : A -> Type)
           (Q : Type) `{IsHProp Q}
: (forall a, P a -> Q) -> (hexists x, P x) -> Q
    := fun f => Trunc_rect_nondep (sig_rect (fun _ => Q) f).
