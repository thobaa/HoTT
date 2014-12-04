(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.

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

(** We begin by defining some module types that wrap ordinary types, functions, and statements about them, turning them from internal statements about inhabitants of the universe to external statements about closed types.  In general, we adopt the convention that a suffix of [M] means a module or module type wrapper, which has a field [m] that indicates the actual object under consideration.  Of course, no such module should be [Import]ed; the [m] fields should always be used dot-qualified.  *)

(** An instantiation of [TypeM] is a closed type, i.e. a type in the empty context. *)
Module Type TypeM.
  (** Unfortunately, due to the way polymorphic module types work, a parameter [m : Type] can only be instantiated by a closed type that lives in _every_ universe.  In particular, we wouldn't be able to instantiate it by [Type].  We sort-of work around this by declaring [m] to have type [Type2]; this enables us to instantiate it by [Type] once, as long as we don't demand that that [Type] also contain some smaller universe.  It seems unlikely that we would need that, but if we ever do, we could always come back here and change [Type2] to [Type3]. *)
  Parameter m : Type2.
End TypeM.

(** For example, we have the unit type. *)
Module UnitM <: TypeM.
  (** We have to give the [: Type2] annotation for it to be sufficiently polymorphic (at least in Coq trunk). *)
  Definition m : Type2@{j i} := Unit@{j}.
End UnitM.

(** And the empty type. *)
Module EmptyM <: TypeM.
  Definition m : Type2@{j i} := Empty@{j}.
End EmptyM.

(** And, as promised, the smallest (non-[Set]) universe. *)
Module Type1M <: TypeM.
  (** Confusingly, although the universe annotation on [Unit] and [Empty] specifies the universe *in* which they live, the universe annotation on [Type1] specifies the universe that it *is*, which must be smaller than the one in which it lives. *)
  Definition m : Type2@{j i} := Type1@{i}.
End Type1M.

(** Similarly, an instantiation of [FunctionM XM YM] is a function [XM.ty -> YM.ty] in the empty context. *)
Module Type FunctionM (XM YM : TypeM).
  Parameter m : XM.m -> YM.m.
End FunctionM.

(** And likewise for homotopies in the empty context. *)
Module Type HomotopyM (XM YM : TypeM) (fM gM : FunctionM XM YM).
  Parameter m : fM.m == gM.m.
End HomotopyM.

(** And equivalences *)
Module Type EquivM (XM YM : TypeM).
  Parameter m : XM.m <~> YM.m.
End EquivM.

(** And sections *)
Module Type SectM (XM YM : TypeM) (sM : FunctionM XM YM) (rM : FunctionM YM XM).
  Parameter m : Sect sM.m rM.m.
End SectM.

(** Composition of closed functions. *)
Module ComposeM (XM YM ZM : TypeM)
       (gM : FunctionM YM ZM) (fM : FunctionM XM YM)
       <: FunctionM XM ZM.
  Definition m := gM.m o fM.m.
End ComposeM.

(** And postcomposition of a closed homotopy by a closed function.  At one point I thought we would need this, but we don't actually seem to. *)
Module ApM (XM YM ZM : TypeM)
       (hM : FunctionM YM ZM) (fM gM : FunctionM XM YM)
       (pM : HomotopyM XM YM fM gM).
  Module hfM := ComposeM XM YM ZM hM fM.
  Module hgM := ComposeM XM YM ZM hM gM.
  Module hpM <: HomotopyM XM ZM hfM hgM.
    Definition m x := ap hM.m (pM.m x).
  End hpM.
End ApM.

(** The next definition is a bit confusing: [Subuniverse] is the dependent module-type [fun (_:TypeM) => hProp].  Thus, an instantiation of [Subuniverse XM] is just a single (closed) [hProp].  However, generally what will want is instead to instantiate the corresponding dependent module-function type [forall (X:TypeM), Subuniverse M], i.e. the module version of [TypeM -> hProp].  As discussed above, this is hypothesized with [F : Subuniverse]; thus it is an operation taking each closed type [X : TypeM] to a closed [hProp] representing the predicate that [X] lies in the subuniverse.  This closed [hProp] is morally [(F X).m], although in practice we have to access it by declaring [Module FXM := F X.] and then calling [FXM.m].

Ideally, we would like this to be an *external* predicate on closed types rather than an operation assigning an internal predicate to each of them, but there doesn't seem to be any way to do that.  Fortunately, for comodalities we can always internalize the "in the subuniverse" predicate to be [IsEquiv fromF]. *)
Module Type Subuniverse (XM : TypeM).
  (** I *think* this is ensuring that [m], like [TypeM.m], can be an hprop living in the second universe. *)
  Parameter m : (TruncType@{i} -1 : Type2@{j i}).
End Subuniverse.

(** However if we are given a closed type, we can assert that it is "closedly" in the subuniverse.*)
Module Type InM (InF : Subuniverse) (XM : TypeM).
  Module InF_XM := InF XM.
  Parameter m : InF_XM.m.
End InM.
(** The rule that all modules must be defined at top level means we need names for more things than one might expect.  Specifically, for modules [InF : Subuniverse] and [XM : TypeM], we have the following:

1. The module [InF XM], which a module wrapper whose field [m] is an hprop that is an *assertion* that [X] lies in the subuniverse [F].  When we need a name for this module (which we do whenever we want to extract its field), we will call it [InF_XM].

2. The module type [InM InF XM], which is a module *type* wrapper whose implementations are closed witnesses that [X] lies in [F].  We don't usually need a special name for this module type.

3. A proven or assumed implementation of [InM InF XM], which is a module wrapper around a closed witness that [X] lies in [F].  When we need a name for such a module, we will call it [isinF_XM]. *)

(** Next we have to express the universal property; we need a way to say that postcomposition with a map is an equivalence.  We will use a "liftable" style, dual to the notion of [ExtendableAlong] used for reflective subuniverses.  However, all the liftings have to act only on closed types and functions, because in models the universal property is not internalizable.  Unfortunately, this means that we cannot describe an "[oo]" sort of liftability, since we can't define a module type by [nat]-recursion.  Thus, we will restrict ourselves to 2-liftability, which is usually enough; if we ever need 3-liftability then we can either simply add it here or assume [Funext].

Note that the hypothesis that [XM.m] lies in [F] is again internal rather than external.  This is again obtainable from an internal definition as [IsEquiv fromF].

We will generally apply these modules to four arguments, namely the subuniverse, a type, its coreflection, and the counit map, and then assert them universally quantified over the remaining data, giving the universal property of the counit. *)
Module Type CorecM (F : Subuniverse)
       (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (XM : TypeM) (isinF_XM : InM F XM)
       (gM : FunctionM XM ZM).
  Parameter m : XM.m -> YM.m.
  (** This wrapper module contains two data, of which one is the lift and the other its computation law.  Rather than force ourselves to define two separate wrappers, we denote the latter one by [m_beta]. *)
  Parameter m_beta : fM.m o m == gM.m.
End CorecM.

Module Type CoindpathsM (F : Subuniverse)
       (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (XM : TypeM) (isinF_XM : InM F XM)
       (hM kM : FunctionM XM YM).
  (** All intermediate modules have to be given names, so in order to hypothesize a closed homotopy from [f o h] to [f o k], we have to give names to those [FunctionM]s. *)
  Module fhM := ComposeM XM YM ZM fM hM.
  Module fkM := ComposeM XM YM ZM fM kM.
  (** The module name [mM] means that this module is the "content" of the wrapper [CoindpathsM], but that it itself has to be a module because it needs to take an extra module parameter. *)
  Declare Module mM (pM : HomotopyM XM ZM fhM fkM)
    : HomotopyM XM YM hM kM.
  (** Again, we include the computation law in the same module wrapper. *)
  Module m_betaM (pM : HomotopyM XM ZM fhM fkM).
    Module liftM := mM pM.
    Parameter m : forall x:XM.m, ap fM.m (liftM.m x) = pM.m x.
  End m_betaM.
End CoindpathsM.

(** Finally we are ready to define a comodality.  Again we usually use this partially applied; given [F : Subuniverse], an instantiation of [Comodality F] is an operation taking each closed type [XM : TypeM] to another closed type [mM] that lies in [F] together with a closed function [fromM] from [mM] to [XM], such that for any other closed type, if it lies in the subuniverse then maps out of it are [LiftableAlong] [fromM]. *)
Module Type Comodality (InF : Subuniverse) (XM : TypeM).
  (** We might include [InF] as part of the data of [Comodality], but we want to be able to specify what it is in some cases.  For instance, it might be a wrapper around [In O] for some (monadic) modality [O]. *)

  (** The coreflection of [X].  Thinking of the subuniverse as its coreflector operation on types, we call this [m] as the "content" of the wrapper. *)
  Parameter m : Type2.
  Module mM <: TypeM.
    Definition m := m.
  End mM.

  (** The coreflection lies in the subuniverse. *)
  Declare Module isinF_mM : InM InF mM.
  
  (** The coreflection counit map from [FX] to [X] *)
  Parameter from : m -> XM.m.
  Module fromM <: FunctionM mM XM.
    Definition m := from.
  End fromM.

  (** The universal property *)
  Declare Module corecM : CorecM InF mM XM fromM.
  Declare Module coindpathsM : CoindpathsM InF mM XM fromM.

  (** Finally, we assert repleteness.  For technical reasons, it is easier to assert this in the following form: any type equivalent to [F X] lies in [F].  We will be able to show that if [X] lies in [F], then [from F X] is an equivalence; thus any type equivalent to a type in [F] will also be equivalent to one of the form [F X] and this can be applied. *)
  Declare Module repleteM (YM : TypeM) (EM : EquivM mM YM) : InM InF YM.

End Comodality.

Module Comodality_Theory (InF : Subuniverse) (F : Comodality InF).
  
  (** If [from F X] admits a section, then [X] lies in [F]. *)
  Module inF_from_F_section_M (XM : TypeM).
    Module FXM := F XM.
    Module mM (sM : FunctionM XM FXM.mM) (HM : SectM XM FXM.mM sM FXM.fromM).

      (** Boilerplate *)
      Module s_o_from_M <: FunctionM FXM.mM FXM.mM
        := ComposeM FXM.mM XM FXM.mM sM FXM.fromM.
      Module idmap_FXM <: FunctionM FXM.mM FXM.mM.
        Definition m : FXM.mM.m -> FXM.mM.m := idmap.
      End idmap_FXM.

      (** We intend to apply [coindpaths] to show that the composite of [s] and [from F X] in the other order is also the identity.  The following sort of boilerplate will be required whenever we apply [coindpaths]. *)
      Module coindpaths_retr_M
        := FXM.coindpathsM FXM.mM FXM.isinF_mM s_o_from_M idmap_FXM.
      Module coindpaths_retr_p_M
      : HomotopyM FXM.mM XM coindpaths_retr_M.fhM coindpaths_retr_M.fkM.
        Definition m : FXM.fromM.m o sM.m o FXM.fromM.m == FXM.fromM.m.
          intros x; unfold compose.
          exact (HM.m (FXM.fromM.m x)).
        Defined.
      End coindpaths_retr_p_M.
      Module coindpaths_retr_M_mM := coindpaths_retr_M.mM coindpaths_retr_p_M.

      (** Using this, we can show that [X] is equivalent to [F X]. *)
      Module equiv_fromF_M : EquivM FXM.mM XM.
        Definition m : FXM.mM.m <~> XM.m.
        Proof.
          (** Needs coq trunk *)
          refine (equiv_adjointify FXM.from sM.m HM.m _).
          apply (coindpaths_retr_M_mM.m).
        Defined.
      End equiv_fromF_M.

      (** Finally, we apply repleteness to this equivalence. *)
      Module mM : InM InF XM := FXM.repleteM XM equiv_fromF_M.
    End mM.
  End inF_from_F_section_M.

  (** Using this, we can show that [Empty] lies in [F]. *)
  Module isinF_Empty_M.
    Module fsEM := inF_from_F_section_M EmptyM.
    Module sM : FunctionM EmptyM fsEM.FXM.mM.
      (** Need universe annotations to keep the right amount of polymorphism. *)
      Definition m : EmptyM.m@{i j} -> fsEM.FXM.mM.m@{i j} := Empty_rec@{i i} _.
    End sM.
    Module HM : SectM EmptyM fsEM.FXM.mM sM fsEM.FXM.fromM.
      Definition m : Sect sM.m fsEM.FXM.fromM.m := Empty_ind _.
    End HM.
    Module mM := fsEM.mM sM HM.
  End isinF_Empty_M.
  (** We give the final result a more descriptive toplevel name. *)
  Module isinF_EmptyM : InM InF EmptyM := isinF_Empty_M.mM.mM.

End Comodality_Theory.
