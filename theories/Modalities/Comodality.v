(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Liftings.
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Comodalities *)

(** We use parametrized module types.  Since the documentation on modules is poor, we include a brief introduction to parametrized module types.  A parametrized module

<<
Module foo (X : Bar) : Foo.
  ...
End foo.
>>

is a *function* from [Bar]s to [Foo]s, the module version of [(fun X => ...) : Bar -> Foo].  A parametrized module *type*, on the other hand

<<
Module Type Foo (X : Bar).
  ...
End Foo.
>>

is a "dependent module type", i.e. a function from [Bar]s to module-types.  Thus, if we apply it to an argument, we obtain an ordinary module type that can then be implemented:

<<
Module bar : Bar.
  ...
End bar.

Module foo : Foo bar.
  ...
End foo.
>>

A dependent module type also gives rise to a "universally quantified module type", a sort of module version of [(forall x:Bar, Foo x)].  We can implement this, essentially defining a "dependently type module function", as follows:

<<
Module allfoo (X : Bar) : Foo X.
  ...
End allfoo.
>>

We can also hypothesize a dependently typed module function, but confusingly the [forall] operation on modules is silent: the way to say [(forall x:Bar, Foo x)] in a hypothesis is to just say [Foo], unapplied.  Thus, we could say

<<
Module Baz (foo : Foo).
  Module bar : Bar.
    ...
  End bar.
  Module foobar : foo bar.
  ...
End Baz.
>>

Given this, you might think that an alternative way to define [allfoo] would begin

<<
Module allfoo : Foo.
>>

and Coq does accept such a statement, but unfortunately there doesn't seem to be a way to complete it.
*)

(** We begin by defining some module types that wrap ordinary types, functions, and statements about them, turning them from internal statements about inhabitants of the universe to external statements about closed types. *)

(** An instantiation of [TypeM] is a closed type, i.e. a type in the empty context. *)
Module Type TypeM.
  Parameter ty : Type.
End TypeM.

(** Similarly, an instantiation of [FunctionM XM YM] is a function [XM.ty -> YM.ty] in the empty context. *)
Module Type FunctionM (XM YM : TypeM).
  Parameter fn : XM.ty -> YM.ty.
End FunctionM.

(** This is a bit confusing: [Subuniverse] is the dependent module-type [fun (_:TypeM) => hProp)].  Thus, an instantiation of [Subuniverse XM] is just a single (closed) [hProp].  However, generally what will want is instead to instantiate the corresponding dependent module-function type [forall (X:TypeM), Subuniverse M], i.e. the module version of [TypeM -> hProp].  As discussed above, this is hypothesized with [F : Subuniverse]; thus it is an operation taking each closed type [X] to a closed [hProp] (namely [(F X).inF]), representing the predicate that [X] lies in the subuniverse.

Ideally, we would like this to be an *external* predicate on closed types rather than an operation assigning an internal predicate to each of them, but there doesn't seem to be any way to do that.  Fortunately, for comodalities we can always internalize the "in the subuniverse" predicate, by defining [inF] to be [IsEquiv fromF]. *)
Module Type Subuniverse (XM : TypeM).
  Parameter inF : hProp.
End Subuniverse.

(** This one we generally apply to three arguments and then universally quantify.  That is, an instantiation of [LiftableM F YM ZM fM] is an operation taking every closed type [XM] to a proof that if [XM.ty] lies in [F], then maps out of [XM.ty] are [ooLiftableAlong] [fM.fn].

Note that the hypothesis that [XM.ty] lies in [F] is again internal rather than external; as before this is obtainable from an internal definition of [inF] as [IsEquiv fromF]. *)
Module Type LiftableM (F : Subuniverse)
       (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (XM : TypeM).
  Module in_XM := F XM.
  Parameter lift : in_XM.inF -> ooLiftableAlong (fun (_:XM.ty) => fM.fn).
End LiftableM.

(** Finally we are ready to define a comodality.  Again we usually use this partially applied; given [F : Subuniverse], an instantiation of [Comodality F] is an operation taking each closed type [XM : TypeM] to another closed type [tyM] that lies in [F] (i.e. we have an inhabitant of [(F tyM).inF]) together with a closed function [fromM] from [tyM] to [XM], such that for any other closed type, if it lies in the subuniverse then maps out of it are [ooLiftableAlong] [fromM]. *)
Module Type Comodality (F : Subuniverse) (XM : TypeM).
  (** The coreflection of [X] *)
  Declare Module tyM : TypeM.

  (** The coreflection lies in the subuniverse. *)
  Module in_tyM := F tyM.
  Parameter F_inF : in_tyM.inF.
  
  (** The coreflection counit map from [FX] to [X] *)
  Declare Module fromM : FunctionM tyM XM.

  (** The universal property *)
  Declare Module liftM : LiftableM F tyM XM fromM.

End Comodality.
