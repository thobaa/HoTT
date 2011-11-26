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

(* These hints apply only to the instance is_codicrete. *)
Hint Resolve reflect_in_rsc unit_in_rsc prod_in_rsc path_in_rsc sum_in_rsc exp_in_rsc.
Hint Resolve is_contr_in_rsc is_equiv_in_rsc equiv_in_rsc is_hlevel_in_rsc.

(* To avoid Unicode symbols, in Coq we write [#] rather than $\sharp$. *)
Notation sharp := (@reflect is_codiscrete codiscrete_is_rsf).
Notation "# X" := (@reflect is_codiscrete codiscrete_is_rsf X) (at level 36, right associativity).
(** printing # $\sharp$ *)
Notation sharp_functor := (@reflect_functor is_codiscrete codiscrete_is_rsf).
Notation "% x" := (@map_to_reflect is_codiscrete codiscrete_is_rsf _ x) (at level 36, right associativity).

(** How to escape from #Type. *)

Definition escape (A : # Type) : Type :=
  { psA : # {A:Type & A} & sharp_functor pr1 psA == A }.

Notation "^ A" := (escape A) (at level 36, right associativity).

Theorem escape_is_codiscrete A : is_codiscrete (^ A).
Proof.
  unfold escape. auto.
Defined.

Hint Resolve escape_is_codiscrete.

Theorem escape_is_sharp A : #A <~> ^%A.
Proof.
  apply @equiv_compose with (B := # {T:{B:Type & B} & pr1 T == A}).
  apply reflect_functor_equiv.
  apply hfiber_fibration with (X := Type) (P := fun T => T).
  apply reflect_fiber_equiv.
Defined.

Theorem sharp_escape_is_sharp (A : # Type) :
  sharp_functor sharp A == %^A.
Proof.
  unreflect A.
  path_via (%#A).
  apply reflect_naturality.
  apply equiv_to_path, escape_is_sharp.
Defined.

(** The internal- and external-homs, from an external point of view. *)

Definition ihom : # Type -> # Type -> # Type :=
  reflect_functor2 (fun A B => A -> B).

Notation "A  #->  B" := (ihom A B) (at level 90, right associativity).

Definition ihom_sharp A B : (%A #-> %B) == %(A -> B).
Proof.
  apply reflect_naturality2.
Defined.

Definition ehom : # Type -> # Type -> Type :=
  fun A B => ^ (A #-> B).

Notation "A  ^->  B" := (ehom A B) (at level 90, right associativity). 

Definition ehom_is_codiscrete A B : is_codiscrete (A ^-> B)
  := escape_is_codiscrete (A #-> B).

Hint Resolve ehom_is_codiscrete.

Definition ehom_sharp {A B : Type} : (%A ^-> %B) <~> # (A -> B).
Proof.
  apply @equiv_compose with (^%(A -> B)).
  unfold ehom.
  apply path_to_equiv, map.
  apply reflect_naturality2.
  apply equiv_inverse, escape_is_sharp.
Defined.

Ltac ehom_to_sharp f :=
  let f' := fresh f in
    set (f' := ehom_sharp f);
    first [
      clearbody f'; clear f
      |
      pattern f;
      apply @transport with (x := ehom_sharp ^-1 f');
      [ apply inverse_is_retraction
        | clearbody f'; clear f ]
    ];
    rename f' into f.

Ltac sharp_to_ehom f :=
  let f' := fresh f in
    set (f' := ehom_sharp ^-1 f);
    clearbody f';
    clear f;
    rename f' into f.

(* Versions 1 of these tactics. *)

Ltac unsharp f :=
  try (match (type of f) with
         %(?A) ^-> %(?B) => ehom_to_sharp f
       end);
  unreflect f.

Ltac unsharp_goal :=
  try (match goal with
         | |- %(?A) ^-> %(?B) => apply (ehom_sharp ^-1)
       end);
  apply (map_to_reflect).

(** How to compose maps externally. *)

Definition sharp_compose {A B C} : #(B->C) -> #(A->B) -> #(A->C).
Proof.
  apply reflect_functor2.
  apply compose.
Defined.

Notation "g #o f" := (sharp_compose g f) (left associativity, at level 37).

Definition sharp_compose_composes A B C (f:A->B) (g:B->C) :
  (%g) #o (%f) == % (g o f).
Proof.
  apply reflect_naturality2.
Defined.

Definition ecompose {A B C : # Type} : (B ^-> C) -> (A ^-> B) -> (A ^-> C).
Proof.
  unsharp A; unsharp B; unsharp C.
  intros g f.
  unsharp f; unsharp g.
  unsharp_goal.
  exact (g o f).
Defined.

Notation "g ^o f" := (ecompose g f) (left associativity, at level 37).

(** Constant maps *)

Definition econst (A : #Type) (B : Type) (b:B) : A ^-> %B.
Proof.
  unsharp A.
  unsharp_goal.
  exact (fun _:A => b).
Defined.

Definition econst_sharp A B (b:B) :
  econst (%A) B b == ehom_sharp ^-1 (%(fun _:A => b)).
Proof.
  equiv_moveleft.
  unfold econst.
  set (H := (fun A0 : Type => (ehom_sharp ^-1) (%(fun _ : A0 => b)))).
  path_via (ehom_sharp (H A)).
  apply @reflect_factor_dep_factors with
    (P := (fun r : #Type => r ^-> %B))
    (x := A).
  unfold H; clear H.
  apply inverse_is_section.
Defined.

(** Identity maps *)

Definition eid (A : #Type) : A ^-> A.
Proof.
  unsharp A.
  unsharp_goal.
  exact (fun x => x).
Defined.

(** The external terminal object is [%unit]. *)

Definition sharp_unit : # Type := map_to_reflect Type unit.

Definition sharp_unit_terminal (A : #Type) : is_contr (A ^-> sharp_unit).
Proof.
  unsharp A. 
  apply contr_equiv_contr with (A := #(A->unit)).
  apply equiv_inverse, ehom_sharp.
  apply contr_equiv_contr with (A := #unit).
  apply reflect_functor_equiv.
  apply equiv_inverse, contr_equiv_unit.
  apply weak_funext; auto.
  apply contr_equiv_contr with (A := unit).
  apply in_rsc_reflect_equiv; auto.
  auto.
Defined.

Definition eto_unit A : A ^-> sharp_unit
  := econst A unit tt.

(** Products, externally. *)

Open Scope type_scope.

Definition iprod : # Type -> # Type -> # Type :=
  reflect_functor2 (fun A B => A * B).

Notation "A #* B" := (iprod A B) (left associativity, at level 40).

Definition iprod_sharp A B : (%A #* %B) == %(A * B).
Proof.
  unfold iprod; apply reflect_naturality2.
Defined.

Definition escape_iprod A B : ^(A #* B) <~> (^A) * (^B).
Proof.
  unsharp A; unsharp B.
  apply @equiv_compose with (B := ^%(A * B)).
  apply path_to_equiv, map, iprod_sharp.
  apply @equiv_compose with (B := #(A * B)).
  apply equiv_inverse, escape_is_sharp.
  apply @equiv_compose with (B := #A * #B).
  apply reflect_product_equiv.
  apply product_equiv; apply escape_is_sharp.
Defined.

(* Probably the following two theorems should prove naturality in T at
   the same time. *)

Definition iprod_equiv A B T :
  (T #-> A) #* (T #-> B) == (T #-> A #* B).
Proof.
  unsharp A; unsharp B; unsharp T.
  path_via (%T #-> %(A * B)).
  path_via (%(T -> A * B)).
  path_via (%(T -> A) #* %(T -> B)).
  path_via ((%T #-> %A) #* %(T -> B)).
  apply ihom_sharp.
  apply happly, map, ihom_sharp.
  path_via (%((T -> A) * (T -> B))).
  apply iprod_sharp.
  apply equiv_to_path.
  apply prod_equiv.
  apply opposite, ihom_sharp.
  apply opposite, iprod_sharp.
Defined.

Definition eprod_equiv A B T :
  (T ^-> A) * (T ^-> B) <~> (T ^-> A #* B).
Proof.
  unfold ehom.
  apply @equiv_compose with (^((T #-> A) #* (T #-> B))).
  apply equiv_inverse, escape_iprod.
  apply path_to_equiv, map.
  apply iprod_equiv.
Defined.

Definition efst {A B} : (A #* B) ^-> A :=
  fst ((eprod_equiv A B (A #* B) ^-1) (eid _)).

Definition esnd {A B} : (A #* B) ^-> B :=
  snd ((eprod_equiv A B (A #* B) ^-1) (eid _)).

(** Pullbacks, externally. *)

Definition ipullback {A B C : #Type} :
  (A ^-> C) -> (B ^-> C) -> #Type.
Proof.
  unsharp A; unsharp B; unsharp C.
  intros f g.
  unsharp f; unsharp g.
  exact (%{x:A & {y:B & f x == g y}}).
Defined.

(* We need some better tactics for this sort of proof. *)
Definition ipullback_sharp A B C (f:A->C) (g:B->C) :
  ipullback (ehom_sharp ^-1 (%f)) (ehom_sharp ^-1 (%g))
  ==
  %{x:A & {y:B & f x == g y}}.
Proof.
  unfold ipullback.
  path_via ((fun A0 : Type =>
      reflect_factor_dep Type
        (fun r : #Type => (%A0 ^-> %C) -> (r ^-> %C) -> #Type)
        (fun x : #Type =>
         exp_in_rsc (%A0 ^-> %C) (fun _ : %A0 ^-> %C => (x ^-> %C) -> #Type)
           (fun _ : %A0 ^-> %C =>
            exp_in_rsc (x ^-> %C) (fun _ : x ^-> %C => #Type)
              (fun _ : x ^-> %C => reflect_in_rsc Type)))
        (fun B0 : Type =>
         reflect_factor_dep Type
           (fun r : #Type => (%A0 ^-> r) -> (%B0 ^-> r) -> #Type)
           (fun x : #Type =>
            exp_in_rsc (%A0 ^-> x)
              (fun _ : %A0 ^-> x => (%B0 ^-> x) -> #Type)
              (fun _ : %A0 ^-> x =>
               exp_in_rsc (%B0 ^-> x) (fun _ : %B0 ^-> x => #Type)
                 (fun _ : %B0 ^-> x => reflect_in_rsc Type)))
           (fun (C0 : Type) (f0 : %A0 ^-> %C0) (g0 : %B0 ^-> %C0) =>
            reflect_factor_dep (A0 -> C0) (fun _ : #(A0 -> C0) => #Type)
              (fun _ : #(A0 -> C0) => reflect_in_rsc Type)
              (fun f1 : A0 -> C0 =>
               reflect_factor_dep (B0 -> C0) (fun _ : #(B0 -> C0) => #Type)
                 (fun _ : #(B0 -> C0) => reflect_in_rsc Type)
                 (fun g1 : B0 -> C0 => %{x : A0 & {y : B0 & f1 x == g1 y}})
                 (ehom_sharp g0)) (ehom_sharp f0)) 
           (%C)) (%B)) A ((ehom_sharp ^-1) (%f)) 
     ((ehom_sharp ^-1) (%g))).
  apply_happly. apply_happly.
  apply @reflect_factor_dep_factors with
    (P := (fun r : #Type => (r ^-> %C) -> (%B ^-> %C) -> #Type))
    (x := A).
  path_via ((fun B0 : Type =>
      reflect_factor_dep Type
        (fun r : #Type => (%A ^-> r) -> (%B0 ^-> r) -> #Type)
        (fun x : #Type =>
         exp_in_rsc (%A ^-> x) (fun _ : %A ^-> x => (%B0 ^-> x) -> #Type)
           (fun _ : %A ^-> x =>
            exp_in_rsc (%B0 ^-> x) (fun _ : %B0 ^-> x => #Type)
              (fun _ : %B0 ^-> x => reflect_in_rsc Type)))
        (fun (C0 : Type) (f0 : %A ^-> %C0) (g0 : %B0 ^-> %C0) =>
         reflect_factor_dep (A -> C0) (fun _ : #(A -> C0) => #Type)
           (fun _ : #(A -> C0) => reflect_in_rsc Type)
           (fun f1 : A -> C0 =>
            reflect_factor_dep (B0 -> C0) (fun _ : #(B0 -> C0) => #Type)
              (fun _ : #(B0 -> C0) => reflect_in_rsc Type)
              (fun g1 : B0 -> C0 => %{x : A & {y : B0 & f1 x == g1 y}})
              (ehom_sharp g0)) (ehom_sharp f0)) (%C)) B
  ((ehom_sharp ^-1) (%f)) ((ehom_sharp ^-1) (%g))).
  apply_happly. apply_happly.
  apply @reflect_factor_dep_factors with
    (P := (fun r : #Type => (%A ^-> %C) -> (r ^-> %C) -> #Type))
    (x := B).
  set (H := (fun (C0 : Type) (f0 : %A ^-> %C0) (g0 : %B ^-> %C0) =>
      reflect_factor_dep (A -> C0) (fun _ : #(A -> C0) => #Type)
        (fun _ : #(A -> C0) => reflect_in_rsc Type)
        (fun f1 : A -> C0 =>
         reflect_factor_dep (B -> C0) (fun _ : #(B -> C0) => #Type)
           (fun _ : #(B -> C0) => reflect_in_rsc Type)
           (fun g1 : B -> C0 => %{x : A & {y : B & f1 x == g1 y}})
           (ehom_sharp g0)) (ehom_sharp f0))).
  path_via (H C ((ehom_sharp ^-1) (%f)) ((ehom_sharp ^-1) (%g))).
  apply @happly with (g := H C ((ehom_sharp ^-1) (%f))).
  apply @happly with (g := H C).
  apply @reflect_factor_dep_factors with
    (P := (fun r : #Type => (%A ^-> r) -> (%B ^-> r) -> #Type))
    (x := C).
  unfold H; clear H.
  path_via ( reflect_factor_dep (A -> C) (fun _ : #(A -> C) => #Type)
     (fun _ : #(A -> C) => reflect_in_rsc Type)
     (fun f1 : A -> C =>
      reflect_factor_dep (B -> C) (fun _ : #(B -> C) => #Type)
        (fun _ : #(B -> C) => reflect_in_rsc Type)
        (fun g1 : B -> C => %{x : A & {y : B & f1 x == g1 y}})
        (ehom_sharp ((ehom_sharp ^-1) (%g)))) (%f)).
  apply inverse_is_section.
  path_via ((fun f1 : A -> C =>
      reflect_factor_dep (B -> C) (fun _ : #(B -> C) => #Type)
        (fun _ : #(B -> C) => reflect_in_rsc Type)
        (fun g1 : B -> C => %{x : A & {y : B & f1 x == g1 y}})
        (ehom_sharp ((ehom_sharp ^-1) (%g)))) f).
  apply @reflect_factor_dep_factors with
    (P := (fun _ : #(A -> C) => #Type))
    (x := f).
  path_via (reflect_factor_dep (B -> C) (fun _ : #(B -> C) => #Type)
     (fun _ : #(B -> C) => reflect_in_rsc Type)
     (fun g1 : B -> C => %{x : A & {y : B & f x == g1 y}})
     (%g)).
  apply inverse_is_section.
  apply @reflect_factor_dep_factors with
    (P := (fun _ : #(B -> C) => #Type))
    (x := g).
Defined.

Definition ipullback_over_unit A B :
  ipullback (eto_unit A) (eto_unit B) == A #* B.
Proof.
  unsharp A; unsharp B.
  path_via (%(A*B)).
  unfold eto_unit.
  path_via (ipullback (ehom_sharp ^-1 (%(fun _:A => tt)))
    (ehom_sharp ^-1 (%(fun _:B => tt)))).
  path_via (ipullback (ehom_sharp ^-1 (%(fun _:A => tt)))
    (econst (%B) unit tt)).
  apply @happly with
    (f := ipullback (econst (%A) unit tt))
    (g := ipullback ((ehom_sharp ^-1) (%(fun _ : A => tt)))).
  apply map.
  apply econst_sharp.
  apply econst_sharp.
  path_via (%{x:A & {y:B & tt == tt}}).
  apply ipullback_sharp.
  apply equiv_to_path.
  apply pullback_over_contr, unit_contr.
  apply opposite, reflect_naturality2.
Defined.
