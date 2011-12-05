Add LoadPath "..".
Require Import Homotopy Subtopos.

(** In this file we assume a lex-reflective subcategory, regarded as a
   category of "codiscrete objects" representing an "external world".
   We show how to "externalize" everything internal to the type theory
   and reason about the category "from the outside".

   It would be better to do this with typeclasses as well, but the
   notation is getting fairly unwieldy, and we are rarely interested
   in more than one structure of local topos.  Thus we use axioms.
   *)

Axiom is_codiscrete : Type -> Type.

Axiom codiscrete_is_rsf : rsf is_codiscrete.
Existing Instance codiscrete_is_rsf.
Axiom codiscrete_is_factsys : factsys is_codiscrete.
Existing Instance codiscrete_is_factsys.
Axiom codiscrete_is_lexrsc : lexrsc is_codiscrete.
Existing Instance codiscrete_is_lexrsc.

(* These hints apply only to the instance is_codiscrete. *)
Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc sum_in_rsc exp_in_rsc.
Hint Resolve is_contr_in_rsc is_equiv_in_rsc equiv_in_rsc is_hlevel_in_rsc.

(** To simplify the notation, we will write the reflector as $\sharp$. *)

(* To avoid Unicode symbols, in Coq we write [#] rather than $\sharp$. *)
Notation sharp := (@reflect is_codiscrete codiscrete_is_rsf).
Notation sharp_functor := (@reflect_functor is_codiscrete codiscrete_is_rsf).
Notation "# X" := (@reflect is_codiscrete codiscrete_is_rsf X) (at level 36, right associativity).
(** printing # $\sharp$ *)

(** The central object of study for us is [# Type], which is the
   "externalization" of [Type].  By the (many-variable) functoriality
   of [sharp], any operation on types can be "externalized" to an
   operation on terms of type [# Type].
   
   In order to then say things about these operations, we need to
   further "escape" from [# Type]; this is what the following function
   does. *)

Definition escape (A : # Type) : Type :=
  { B : # {X:Type & X} & sharp_functor pr1 B == A }.

(** A notation for escaping (think of it as pointing to the escape route). *)
Notation "^ A" := (escape A) (at level 36, right associativity).

(** Escaping comes at a cost, however: we always end up as codiscrete. *)
Theorem escape_is_codiscrete A : is_codiscrete (^ A).
Proof.
  unfold escape. auto.
Defined.

Hint Resolve escape_is_codiscrete.

(** We write the image of a type [X] in [# Type] as [[X]], and think
   of it as a "name" for [X]. *)

Notation "[ x ]" := (@to_reflect is_codiscrete codiscrete_is_rsf _ x) (at level 36, no associativity).

(** When we escape the name of [A], we end up with [#A]. *)
Theorem escape_compute A : ^[A] <~> #A.
Proof.
  unfold escape.
  apply @equiv_compose with (B := # {T:{B:Type & B} & pr1 T == A}).
  apply equiv_inverse, reflect_fiber_equiv.
  apply reflect_functor_equiv.
  apply equiv_inverse; apply hfiber_fibration with (X := Type) (P := fun T => T).
Defined.

(** It follows that the name of an escaped name is equivalent to the
   action of [sharp] on names. *)

Notation esharp := (sharp_functor sharp).
Notation "[#] X" := (esharp X) (at level 36, right associativity).
(** printing [#] $[\sharp]$ *)

Definition esharp_compute A : [#] [A] == [#A].
Proof.
  apply reflect_naturality.
Defined.

Theorem name_escape_compute (A : # Type) :
  [^A] == [#] A.
Proof.
  unreflect A.
  path_via ([#A]).
  apply equiv_to_path, escape_compute.
  apply opposite, reflect_naturality.
Defined.

(** Any operation prefixed by an 'i' or a symbol $\sharp$ denotes an
   operation on names, generally obtained by functoriality.  When
   the prefix changes to an 'e' or a symbol [^], it refers to the
   escaped version thereof.
   *)

(** We begin with the internal- and external-homs. *)

Definition ihom : # Type -> # Type -> # Type :=
  reflect_functor2 (fun A B => A -> B).

Notation "A  #->  B" := (ihom A B) (at level 90, right associativity).

Definition ihom_compute A B : ([A] #-> [B]) == [A -> B].
Proof.
  apply reflect_naturality2.
Defined.

Definition ehom : # Type -> # Type -> Type :=
  fun A B => ^ (A #-> B).

Notation "A  ^->  B" := (ehom A B) (at level 90, right associativity). 

Definition ehom_is_codiscrete A B : is_codiscrete (A ^-> B)
  := escape_is_codiscrete (A #-> B).

Hint Resolve ehom_is_codiscrete.

Definition ehom_compute {A B : Type} : ([A] ^-> [B]) <~> # (A -> B).
Proof.
  apply @equiv_compose with (^[A -> B]).
  unfold ehom.
  apply path_to_equiv, map.
  apply reflect_naturality2.
  apply escape_compute.
Defined.

(** The inverse of [ehom_compute] gives us a way to "externalize"
   any internal function [f : A -> B].  First we take its name [[f]]
   in [#(A -> B)], then pass backwards across [ehom_compute] to get
   a term of type [[A] ^-> [B]].  We write this as [[[f]]]. *)

Notation "[[ f ]]" := (ehom_compute ^-1 ([f])) (at level 36, no associativity).

(** The following tactic applies [ehom_compute] to a hypothesis,
   modifying the other hypotheses and conclusion as necessary. *)

Ltac ehom_compute f :=
  let f' := fresh f in
    first [
      (* This works if nothing else depends on [f]. *)
      set (f' := ehom_compute f);
        clearbody f'; clear f
      |
      (* Otherwise, we need to transport along [ehom_compute]. *)
        generalize dependent f; intros f;
          set (f' := ehom_compute f);
            pattern f;
              apply @transport with (x := ehom_compute ^-1 f');
                [ apply inverse_is_retraction
                  | clearbody f'; clear f ]
    ];
    rename f' into f.

(** Similarly, for undoing it. *)

Ltac ehom_uncompute f :=
  let f' := fresh f in
    first [
      (* This works if nothing else depends on [f]. *)
      set (f' := ehom_compute f);
        clearbody f'; clear f
      |
      (* Otherwise, we need to transport along [ehom_compute]. *)
        generalize dependent f; intros f;
          set (f' := ehom_compute f);
            pattern f;
              apply @transport with (x := ehom_compute f');
                [ apply inverse_is_section
                  | clearbody f'; clear f ]
    ];
    rename f' into f.

(** This tactic first applies [ehom_compute] to a hypothesis if it
   is relevant, then calls [unreflect]. *)

Ltac unsharp f :=
  try (match (type of f) with
         [ ?A ] ^-> [ ?B ] => ehom_compute f
       end);
  unreflect f.

(** Similarly, this acts on the goal. *)

Ltac unsharp_goal :=
  try (match goal with
         | |- [ ?A ] ^-> [ ?B ] => apply (ehom_compute ^-1)
       end);
  apply (to_reflect).

(** A quick bludgeon which unsharps all relevant hypotheses. *)

Ltac sharp_induction :=
  repeat (match goal with
            | x : # ?A |- _ => unsharp x; intros
            | x : [ ?A ] ^-> [ ?B ] |- _ => unsharp x; intros
          end).

(** Similarly, we define a version of [unreflect_compute] which also
   acts on ehoms. *)

Ltac sharp_compute_in s :=
  match s with
    | appcontext cxt [ reflect_factor_dep ?X0 ?P0 ?Pr0 ?f0 (to_reflect _ ?x0) ] =>
      let h := fresh in
        set (h := f0);
          let mid := context cxt[h x0] in
            path_via' mid;
            [ repeat progress first [
              apply @reflect_factor_dep_factors with
                (X := X0) (P := P0) (Pr := Pr0) (f := f0) (x := x0)
              | apply_happly ]
              | unfold h; clear h ]
    | context cxt [(@equiv_coerce_to_function _ _ (@ehom_compute _ _)
      (inverse (@ehom_compute _ _) ?f))] =>
    let mid := context cxt [ f ] in
      let x := fresh in spath_using mid x inverse_is_section
      (* Now we do a version of the tactic path_using that also calls apply_happly. *)
(*      apply @concat with (y := mid);
        repeat progress first [
          apply inverse_is_section
          | apply opposite; apply inverse_is_section
          | apply whisker_left
          | apply whisker_right
          | apply @map
          | apply_happly
          | apply funext; let x := fresh in intros x
        ]; auto with path_hints*)
  end.

Ltac sharp_compute :=
  repeat (
    match goal with
      |- ?s == ?t => first [ sharp_compute_in s | sharp_compute_in t ]
    end
  ); auto.

(** How to compose maps externally. *)

Definition sharp_compose {A B C} : #(B->C) -> #(A->B) -> #(A->C).
Proof.
  apply reflect_functor2.
  apply compose.
Defined.

Notation "g #o f" := (sharp_compose g f) (left associativity, at level 37).

Definition sharp_compose_compute A B C (f:A->B) (g:B->C) :
  [g] #o [f] == [g o f].
Proof.
  apply reflect_naturality2.
Defined.

Definition ecompose {A B C : # Type} : (B ^-> C) -> (A ^-> B) -> (A ^-> C).
Proof.
  intros g f.
  sharp_induction.
  unsharp_goal.
  exact (g o f).
Defined.

Notation "g ^o f" := (ecompose g f) (left associativity, at level 37).

Definition ecompose_compute A B C (f : A -> B) (g : B -> C) :
  [[g]] ^o [[f]] == [[g o f]].
Proof.
  unfold ecompose.
  sharp_compute.
Defined.

Definition ecompose_associative A B C D (f : A ^-> B) (g : B ^-> C) (h : C ^-> D) :
  h ^o (g ^o f) == (h ^o g) ^o f.
Proof.
  sharp_induction.
  path_via ([[h]] ^o [[g o f]]).
  apply ecompose_compute.
  path_via ([[h o (g o f)]]).
  apply ecompose_compute.
  path_via ([[h o g]] ^o [[f]]).
  path_via ([[(h o g) o f]]).
  apply opposite, ecompose_compute.
  apply happly, map, opposite, ecompose_compute.
Defined.

(** Constant maps *)

Definition econst (A : #Type) (B : Type) (b:B) : A ^-> [B].
Proof.
  sharp_induction; unsharp_goal.
  exact (fun _:A => b).
Defined.

Definition econst_compute A B (b:B) :
  econst ([A]) B b == [[fun _:A => b]].
Proof.
  unfold econst.
  sharp_compute.
Defined.

(** Identity maps *)

Definition eidmap (A : #Type) : A ^-> A.
Proof.
  sharp_induction; unsharp_goal.
  exact (fun x => x).
Defined.

Definition eidmap_compute A : eidmap ([A]) == [[idmap A]].
Proof.
  unfold eidmap.
  sharp_compute.
Defined.

(** The external terminal object is [[unit]]. *)

Definition eunit : # Type := to_reflect Type unit.

Definition eunit_terminal (A : #Type) : is_contr (A ^-> eunit).
Proof.
  unsharp A.
  apply contr_equiv_contr with (A := #(A->unit)).
  apply equiv_inverse, ehom_compute.
  apply contr_equiv_contr with (A := #unit).
  apply reflect_functor_equiv.
  apply equiv_inverse, contr_equiv_unit.
  apply weak_funext; auto.
  apply contr_equiv_contr with (A := unit).
  apply in_rsc_reflect_equiv; auto.
  auto.
Defined.

Definition eto_unit A : A ^-> eunit
  := econst A unit tt.

(** Products, externally. *)

Open Scope type_scope.

Definition iprod : # Type -> # Type -> # Type :=
  reflect_functor2 (fun A B => A * B).

Notation "A #* B" := (iprod A B) (left associativity, at level 40).

Definition iprod_compute A B : ([A] #* [B]) == [A * B].
Proof.
  unfold iprod; apply reflect_naturality2.
Defined.

Definition iprod_escape A B : ^(A #* B) <~> (^A) * (^B).
Proof.
  sharp_induction.
  apply @equiv_compose with (B := ^[A * B]).
  apply path_to_equiv, map, iprod_compute.
  apply @equiv_compose with (B := #(A * B)).
  apply escape_compute.
  apply @equiv_compose with (B := #A * #B).
  apply reflect_product_equiv.
  apply product_equiv; apply equiv_inverse, escape_compute.
Defined.

(* Probably the following two theorems should prove naturality in T at
   the same time. *)

Definition iprod_equiv A B T :
  (T #-> A) #* (T #-> B) == (T #-> A #* B).
Proof.
  sharp_induction.
  path_using ([T] #-> [A * B]) iprod_compute.
  path_using ([T -> A * B]) ihom_compute.
  path_using (([T] #-> [A]) #* [T -> B]) ihom_compute.
  path_via ([T -> A] #* [T -> B]).
  apply happly, map, ihom_compute.
  path_using ([(T -> A) * (T -> B)]) iprod_compute.
  apply equiv_to_path, prod_equiv.
Defined.

Definition eprod_equiv A B T :
  (T ^-> A) * (T ^-> B) <~> (T ^-> A #* B).
Proof.
  unfold ehom.
  apply @equiv_compose with (^((T #-> A) #* (T #-> B))).
  apply equiv_inverse, iprod_escape.
  apply path_to_equiv, map.
  apply iprod_equiv.
Defined.

Definition efst {A B} : (A #* B) ^-> A :=
  fst ((eprod_equiv A B (A #* B) ^-1) (eidmap _)).

Definition esnd {A B} : (A #* B) ^-> B :=
  snd ((eprod_equiv A B (A #* B) ^-1) (eidmap _)).

(** Pullbacks, externally. *)

Definition ipullback {A B C : #Type} :
  (A ^-> C) -> (B ^-> C) -> #Type.
Proof.
  intros f g.
  sharp_induction; unsharp_goal.
  exact ({x:A & {y:B & f x == g y}}).
Defined.

Definition ipullback_compute A B C (f:A->C) (g:B->C) :
  ipullback ([[f]]) ([[g]]) == [ {x:A & {y:B & f x == g y}} ].
Proof.
  unfold ipullback.
  sharp_compute.
Defined.

Definition ipullback_over_unit A B :
  ipullback (eto_unit A) (eto_unit B) == A #* B.
Proof.
  sharp_induction.
  path_via ([A*B]).
  unfold eto_unit.
  path_via (ipullback (ehom_compute ^-1 ([fun _:A => tt]))
    (ehom_compute ^-1 ([fun _:B => tt]))).
  path_via (ipullback (ehom_compute ^-1 ([fun _:A => tt]))
    (econst ([B]) unit tt)).
  apply @happly with
    (f := ipullback (econst ([A]) unit tt))
    (g := ipullback ((ehom_compute ^-1) ([fun _ : A => tt]))).
  apply map.
  apply econst_compute.
  apply econst_compute.
  path_via ([{x:A & {y:B & tt == tt}}]).
  apply ipullback_compute.
  apply equiv_to_path.
  apply pullback_over_contr, unit_contr.
  apply opposite, reflect_naturality2.
Defined.

(** External versions of all the usual propositions. *)

Definition iis_equiv {A B} : (A ^-> B) -> #Type.
Proof.
  intros f; sharp_induction; unsharp_goal.
  exact (is_equiv f).
Defined.

Definition eis_equiv {A B} (f : A ^-> B) : Type
  := ^(iis_equiv f).

Definition eis_equiv_is_codiscrete A B (f : A ^-> B) :
  is_codiscrete (eis_equiv f).
Proof.
  apply escape_is_codiscrete.
Defined.

Hint Resolve eis_equiv_is_codiscrete.

Definition eis_equiv_compute {A B} (f : A -> B) :
  eis_equiv ([[f]]) <~> #(is_equiv f).
Proof.
  unfold eis_equiv, iis_equiv.
  apply @equiv_compose with (^[is_equiv f]).
  apply path_to_equiv, map; sharp_compute.
  apply escape_compute.
Defined.

Definition iis_codiscrete (A : #Type) : #Type.
Proof.
  sharp_induction; unsharp_goal.
  exact (is_codiscrete A).
Defined.

Definition eis_codiscrete A : Type
  := ^(iis_codiscrete A).

Definition eis_codiscrete_is_codiscrete A :
  is_codiscrete (eis_codiscrete A).
Proof.
  apply escape_is_codiscrete.
Defined.

Hint Resolve eis_codiscrete_is_codiscrete.

Definition eis_codiscrete_compute {A} :
  eis_codiscrete ([A]) <~> #(is_codiscrete A).
Proof.
  unfold eis_codiscrete, iis_codiscrete.
  apply @equiv_compose with (^[is_codiscrete A]).
  apply path_to_equiv, map; sharp_compute.
  apply escape_compute.
Defined.

Definition eis_codiscrete_is_prop A : is_prop (eis_codiscrete A).
Proof.
  unsharp A.
  intros B; apply is_hlevel_in_rsc.
  apply eis_codiscrete_is_codiscrete.
  apply @transport with (x := #(is_codiscrete A)).
  apply opposite, equiv_to_path, eis_codiscrete_compute.
  apply reflect_preserves_props, in_rsc_prop.
Defined.

Definition is_codiscrete_eis_codiscrete {A} :
  is_codiscrete A -> eis_codiscrete ([A]).
Proof.
  intros Ac.
  apply (eis_codiscrete_compute ^-1).
  apply to_reflect; assumption.
Defined.

Definition is_codiscrete_eis_codiscrete_compute {A} (Ac : is_codiscrete A) :
  eis_codiscrete_compute (is_codiscrete_eis_codiscrete Ac) == [Ac].
Proof.
  (* Cheating... *)
  apply prop_path.
  apply reflect_preserves_props, in_rsc_prop.
Defined.

Definition esharp_is_codiscrete A : eis_codiscrete ([#]A).
Proof.
  unsharp A.
  apply @transport with (x := [#A]).
  apply opposite, reflect_naturality.
  unfold eis_codiscrete, iis_codiscrete.
  apply (transport (!reflect_factor_dep_factors
    Type (fun _ : #Type => #Type)
    (fun _ : #Type => reflect_in_rsc Type)
    (fun A0 : Type => [is_codiscrete A0]) (#A))).
  apply (escape_compute _ ^-1).
  unsharp_goal.
  apply reflect_in_rsc.
Defined.

Definition esharp_is_codiscrete_compute A :
  esharp_is_codiscrete ([A]) ==
  transport (P := eis_codiscrete) (!esharp_compute A) (is_codiscrete_eis_codiscrete (reflect_in_rsc A)).
Proof.
  (* Cheating... *)
  apply prop_path, eis_codiscrete_is_prop.
Defined.

(** The unit of the reflection, externally. *)

Definition eto_sharp A : (A ^-> [#] A).
Proof.
  unsharp A.
  apply (transport (P := ehom ([A])) (!esharp_compute A)).
  unsharp_goal.
  apply to_reflect.
Defined.

Definition eto_sharp_compute A :
  eto_sharp ([A]) ==
  transport (P := ehom ([A])) (!esharp_compute A) ([[to_reflect A]]).
Proof.
  unfold eto_sharp.
  sharp_compute.
Defined.

(** The factorization for the reflection, externally. *)

Definition esharp_factor {A B} : eis_codiscrete B ->
  (A ^-> B) -> ([#]A ^-> B).
Proof.
  intros Bc f.
  sharp_induction.
  apply (transport (P := fun z => z ^-> [B]) (!esharp_compute A)).
  set (Bc' := eis_codiscrete_compute Bc).
  unsharp Bc'.
  unsharp_goal.
  apply reflect_factor; assumption.
Defined.

Definition esharp_factor_compute A B (f:A->B) (Bc : is_codiscrete B) :
  esharp_factor (is_codiscrete_eis_codiscrete Bc) ([[f]]) ==
  transport (P := fun z => z ^-> [B]) (!esharp_compute A) ([[reflect_factor Bc f]]).
Proof.
  unfold esharp_factor.
  sharp_compute.
  apply map.
  path_via (reflect_factor_dep (is_codiscrete B)
    (fun _ : #is_codiscrete B => [#A] ^-> [B])
    (fun _ : #is_codiscrete B => ehom_is_codiscrete ([#A]) ([B]))
    (fun Bc' : is_codiscrete B => [[reflect_factor Bc' f]])
    ([Bc])).
  apply is_codiscrete_eis_codiscrete_compute.
  sharp_compute.
Defined.

Definition esharp_factoriality_pre A B C (f : A ^-> B) (g : B ^-> C)
  (Bc : eis_codiscrete B) (Cc : eis_codiscrete C) :
  esharp_factor Cc (g ^o f) == g ^o esharp_factor Bc f.
Proof.
  sharp_induction.
  set (Bc' := eis_codiscrete_compute Bc).
  unsharp Bc'.
  set (Cc' := eis_codiscrete_compute Cc).
  unsharp Cc'.
  path_via ([[g]] ^o esharp_factor (is_codiscrete_eis_codiscrete Bc') ([[f]])).
  2:apply happly, map.
  2:apply prop_path, eis_codiscrete_is_prop.
  path_via (esharp_factor (is_codiscrete_eis_codiscrete Cc') ([[g]] ^o [[f]])).
  apply happly, map. 
  apply prop_path, eis_codiscrete_is_prop.
  path_via ([[g]] ^o
    (transport (P := fun z => z ^-> [B]) (!esharp_compute A) ([[ reflect_factor Bc' f ]]))).
  2:apply opposite, esharp_factor_compute.
  path_via (transport (P := fun z => z ^-> [C]) (!esharp_compute A)
    ([[g]] ^o [[ reflect_factor Bc' f ]])).
  2:apply opposite.
  2:apply @trans_map with (f := fun A => @ecompose A _ _ ([[g]])).
  path_via (esharp_factor (is_codiscrete_eis_codiscrete Cc') ([[g o f]])).
  apply ecompose_compute.
  path_via (transport (P := fun z => z ^-> [C]) (!esharp_compute A)
    ([[ reflect_factor Cc' (g o f) ]])).
  apply esharp_factor_compute.
  path_via ([[ g o reflect_factor Bc' f]]).
  apply funext; intros x; apply opposite, reflect_factoriality_pre.
  apply opposite, ecompose_compute.
Defined.

(** The functoriality of the factorization, externally. *)

Definition esharp_functor {A B} : (A ^-> B) -> ([#]A ^-> [#]B).
Proof.
  intros f.
  apply @esharp_factor with (A := A) (B := [#]B).
  apply esharp_is_codiscrete.
  apply @ecompose with (B := B).
  apply eto_sharp.
  assumption.
Defined.

Definition esharp_functor_compute A B (f : A -> B) :
  (esharp_functor ([[f]])) ==
  (transport (P := fun z => [#][A] ^-> z) (!esharp_compute B)
    (transport (P := fun z => z ^-> [#B]) (!esharp_compute A)
      ([[sharp_functor f]]))).
Proof.
    (* This proof could seriously benefit from the ability to use [rewrite]! *)
  unfold esharp_functor.
  path_via (esharp_factor
    (transport (P := eis_codiscrete) (!esharp_compute B) (is_codiscrete_eis_codiscrete (reflect_in_rsc B)))
    (eto_sharp ([B]) ^o [[f]])).
  apply happly, map.
  apply esharp_is_codiscrete_compute.
  path_via ( esharp_factor
    (transport (!esharp_compute B)
      (is_codiscrete_eis_codiscrete (reflect_in_rsc B)))
    (transport (P := ehom ([B])) (!esharp_compute B) ([[to_reflect B]]) ^o [[f]])).
  apply happly, map. apply eto_sharp_compute.
  path_via ( esharp_factor
    (transport (!esharp_compute B)
      (is_codiscrete_eis_codiscrete (reflect_in_rsc B)))
    (transport (!esharp_compute B) ([[to_reflect B]] ^o [[f]]))).
  apply @trans_map with
    (P := fun z => [B] ^-> z)
    (f := fun _ g => g ^o ([[f]])).
  path_via (transport (!esharp_compute B)
    (esharp_factor
      (is_codiscrete_eis_codiscrete (reflect_in_rsc B))
      ([[to_reflect B]] ^o [[f]]))).
  apply trans_map2.
  path_via (esharp_factor (is_codiscrete_eis_codiscrete (reflect_in_rsc B))
    ([[to_reflect B o f]])).
  apply ecompose_compute.
  apply esharp_factor_compute.
Defined.
