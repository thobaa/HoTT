(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Liftings.
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Comodalities *)

Module Type TypeM.
  Parameter X : Type.
End TypeM.

Module Type Subuniverse (XM : TypeM).
  (** Is there any way to make this an "external" hprop? *)
  Parameter inF : hProp.
End Subuniverse.

Module Type Coreflector (F : Subuniverse) (XM : TypeM).
  Parameter FX : Type.
  Module FM := F XM.
  Parameter F_inF : FM.inF.
(** How to express the universal property? *)
End Coreflector.

(** I guess we can just partially apply it and say [Coreflector F] rather than needing to wrap it again. *)
Module Type Comodality (F : Subuniverse).
  Declare Module coreflector : Coreflector F.
End Comodality.

Declare Module F : Subuniverse.
Declare Module FC : Comodality F.

Module natM : TypeM.
  Definition X := nat.
End natM.

Module Fnat := F natM.


Check Fnat.inF.
