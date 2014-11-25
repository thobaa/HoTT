(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
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

(Given this, you might think that an alternative way to define [allfoo] would begin [Module allfoo : Foo.].  Coq does accept such a statement, but unfortunately there doesn't seem to be a way to complete it.) *)

(** We begin by defining some module types that wrap ordinary types, functions, and statements about them, turning them from internal statements about inhabitants of the universe to external statements about closed types. *)

(** An instantiation of [TypeM] is a closed type, i.e. a type in the empty context. *)
Module Type TypeM.
  (** Unfortunately, due to the way polymorphic module types work, a parameter [ty : Type] can only be instantiated by a closed type that lives in _every_ universe.  In particular, we wouldn't be able to instantiate it by [Type].  We work around this by declaring [ty] to have type [Type2]; this enables us to instantiate it by [Type] once, as long as we don't demand that that [Type] also contain some smaller universe.  It seems unlikely that we would need that, but if we ever do, we could always come back here and change [Type2] to [Type3]. *)
  Parameter ty : Type2.
End TypeM.

(** For example, we have the unit type. *)
Module UnitM <: TypeM.
  (** We have to give the [: Type2] annotation for it to be sufficiently polymorphic (at least in Coq trunk). *)
  Definition ty : Type2@{j i} := Unit@{j}.
End UnitM.

(** And the empty type. *)
Module EmptyM <: TypeM.
  Definition ty : Type2@{j i} := Empty@{j}.
End EmptyM.

(** And, as promised, the smallest (non-[Set]) universe. *)
Module Type1M <: TypeM.
  (** Confusingly, although the universe annotation on [Unit] and [Empty] specifies the universe *in* which they live, the universe annotation on [Type1] specifies the universe that it *is*, which must be smaller than the one in which it lives. *)
  Definition ty : Type2@{j i} := Type1@{i}.
End Type1M.

(** Similarly, an instantiation of [FunctionM XM YM] is a function [XM.ty -> YM.ty] in the empty context. *)
Module Type FunctionM (XM YM : TypeM).
  Parameter fn : XM.ty -> YM.ty.
End FunctionM.

(** And likewise for homotopies in the empty context. *)
Module Type HomotopyM (XM YM : TypeM) (fM gM : FunctionM XM YM).
  Parameter htpy : fM.fn == gM.fn.
End HomotopyM.

(** Composition of closed functions. *)
Module ComposeM (XM YM ZM : TypeM)
       (gM : FunctionM YM ZM) (fM : FunctionM XM YM)
       <: FunctionM XM ZM.
  Definition fn := gM.fn o fM.fn.
End ComposeM.

(** And postcomposition of a closed homotopy by a closed function.  At one point I thought we would need this, but we don't actually seem to. *)
Module ApM (XM YM ZM : TypeM)
       (hM : FunctionM YM ZM) (fM gM : FunctionM XM YM)
       (pM : HomotopyM XM YM fM gM).
  Module hfM := ComposeM XM YM ZM hM fM.
  Module hgM := ComposeM XM YM ZM hM gM.
  Module htpyM <: HomotopyM XM ZM hfM hgM.
    Definition htpy x := ap hM.fn (pM.htpy x).
  End htpyM.
End ApM.

(** The next definition is a bit confusing: [Subuniverse] is the dependent module-type [fun (_:TypeM) => hProp].  Thus, an instantiation of [Subuniverse XM] is just a single (closed) [hProp].  However, generally what will want is instead to instantiate the corresponding dependent module-function type [forall (X:TypeM), Subuniverse M], i.e. the module version of [TypeM -> hProp].  As discussed above, this is hypothesized with [F : Subuniverse]; thus it is an operation taking each closed type [X] to a closed [hProp] (namely [(F X).inF]), representing the predicate that [X] lies in the subuniverse.

Ideally, we would like this to be an *external* predicate on closed types rather than an operation assigning an internal predicate to each of them, but there doesn't seem to be any way to do that.  Fortunately, for comodalities we can always internalize the "in the subuniverse" predicate, by defining [inF] to be [IsEquiv fromF]. *)
Module Type Subuniverse (XM : TypeM).
  (** I *think* this is ensuring that [inF], like [TypeM.ty], can be an hprop living in the second universe. *)
  Parameter inF : (TruncType@{i} -1 : Type2@{j i}).
End Subuniverse.

(** We can, however, assert that a closed type is "closedly" in the subuniverse. *)
Module Type InFM (F : Subuniverse) (XM : TypeM).
  Module FXM := F XM.
  Parameter in_ty : FXM.inF.
End InFM.

(** Next we have to express the universal property; we need a way to say that postcomposition with a map is an equivalence.  We will use a "liftable" style dual to the notion of [ExtendableAlong] used for reflective subuniverses.  However, all the liftings have to act only on closed types and functions, because in models the universal property is not internalizable.  Unfortunately, this means that we cannot describe an "[oo]" sort of liftability, since we can't define a module type by [nat]-recursion.  Thus, we will restrict ourselves to 2-liftability, which is usually enough; if we ever need 3-liftability then we can either simply add it here or assume [Funext].

Note that the hypothesis that [XM.ty] lies in [F] is again internal rather than external.  This is again obtainable from an internal definition of [inF] as [IsEquiv fromF].

We will generally apply these modules to four arguments, namely the subuniverse, a type, its coreflection, and the counit map, and then assert them universally quantified over the remaining data, giving the universal property of the counit. *)
Module Type CorecM (F : Subuniverse)
       (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (XM : TypeM) (FXM : InFM F XM)
       (gM : FunctionM XM ZM).
  Parameter lift_fn : XM.ty -> YM.ty.
  Parameter comp : fM.fn o lift_fn == gM.fn.
End CorecM.

Module Type CoindpathsM (F : Subuniverse)
       (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (XM : TypeM) (FXM : InFM F XM)
       (hM kM : FunctionM XM YM).
  (** All intermediate modules have to be given names, so in order to hypothesize a closed homotopy from [f o h] to [f o k], we have to give names to those [FunctionM]s. *)
  Module domM := ComposeM XM YM ZM fM hM.
  Module codM := ComposeM XM YM ZM fM kM.
  Declare Module lift_htpyM (pM : HomotopyM XM ZM domM codM)
    : HomotopyM XM YM hM kM.
  Module lift_htpy_compM (pM : HomotopyM XM ZM domM codM).
    Module liftedM := lift_htpyM pM.
    Parameter comp : forall x:XM.ty, ap fM.fn (liftedM.htpy x) = pM.htpy x.
  End lift_htpy_compM.
End CoindpathsM.

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
  Declare Module corecM : CorecM F tyM XM fromM.
  Declare Module coindpathsM : CoindpathsM F tyM XM fromM.

End Comodality.

Module Comodality_Theory (F : Subuniverse) (C : Comodality F).
  
  (** Let's see if we can actually extract what we've asserted.  Here's a type in the empty context. *)
  Axiom X : Type.
  Module XM <: TypeM.
    Definition ty : Type2 := X.
  End XM.

  (** Here's the data about its coreflection. *)
  Module CXM := C XM.

  (** Let's assert that [Empty] lies in the subuniverse (we ought to be able to prove that). *)
  Declare Module FEmptyM : InFM F EmptyM.

  (** Here's the coreflected (closed) type. *)
  Module flatXM := CXM.tyM.

  (** Now let's consider the unique map from [Empty] to [flatX], which of course also lives in the empty context. *)
  Module Empty_recM <: FunctionM EmptyM flatXM.
    (** These universe annotations are apparently necessary to get it accepted, as is writing [EmptyM.ty] instead of just [Empty]. *)
    Definition fn : EmptyM.ty@{j i} -> flatXM.ty@{j i} := @Empty_rec flatXM.ty.
  End Empty_recM.

  (** Let's consider two copies of this map, compose them both with the counit [flatX -> X], consider the trivial homotopy between them, and try to lift it along the counit by the universal property.  Here's the module that contains data about liftings of such homotopies. *)
  Module Coindpaths_Empty := CXM.coindpathsM EmptyM FEmptyM Empty_recM Empty_recM.

  (** We have to declare the homotopy we want to lift as living in the empty context. *)
  Module myhM <: HomotopyM EmptyM XM Coindpaths_Empty.domM Coindpaths_Empty.codM.
    (** Coq trunk accepts this, although the pinned version gets an "index out of bounds" anomaly. *)
    Definition htpy : Coindpaths_Empty.domM.fn@{j i} == Coindpaths_Empty.codM.fn@{j i}
      := fun (x:EmptyM.ty@{j i}) => Empty_ind@{j j} (fun x => Coindpaths_Empty.domM.fn x = Coindpaths_Empty.codM.fn x) x.
  End myhM.

  (** Now we can declare the module that contains data about the lift of this *particular* homotopy. *)
  Module Coindpaths_Empty_lhcM := Coindpaths_Empty.lift_htpy_compM myhM.

  (** Finally, here is the computation rule for that lift. *)
  Print Coindpaths_Empty_lhcM.comp.

  (** Whew!  Is this really worth it?  *)

End Comodality_Theory.
