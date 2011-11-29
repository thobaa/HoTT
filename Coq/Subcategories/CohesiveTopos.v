Add LoadPath "..".
Require Import Homotopy Subtopos Codiscrete LocalTopos.

(** In this file we build on the internal axiomatization of a local
   topos to make it into a cohesive topos.  This means that the
   discrete objects should also be a *reflective* subcategory, and
   that the reflector should preserve finite products.

   As with everything to do with discrete objects, we need to work
   externally.
   *)

Axiom pi : # Type -> # Type.

Axiom pi_is_discrete : forall A, is_discrete (pi A).

Hint Resolve pi_is_discrete.

Axiom to_pi : forall A, A ^-> pi A.

Axiom pi_is_reflection : forall A B, is_discrete B ->
  is_equiv (fun f : pi A ^-> B => f ^o (to_pi A)).

Definition pi_reflection_equiv A B (Bd : is_discrete B) :
  (pi A ^-> B) <~> (A ^-> B) :=
  (fun f : pi A ^-> B => f ^o (to_pi A) ; pi_is_reflection A B Bd).

Definition pi_factor {A B} (Bd : is_discrete B) : (A ^-> B) -> (pi A ^-> B) :=
  pi_reflection_equiv A B Bd ^-1.

Definition pi_functor {A B} (f : A ^-> B) : (pi A ^-> pi B) :=
  pi_factor (pi_is_discrete B) (to_pi B ^o f).

Axiom pi_preserves_unit : eis_equiv (to_pi eunit).

Definition pi_prod_cmp A B : pi (A #* B) ^-> pi A #* pi B.
Proof.
  sharp_induction.
  apply @transport with
    (P := fun z => pi z ^-> pi ([A]) #* pi ([B]))
    (x := [A * B]).
  apply opposite, iprod_compute.
  apply eprod_equiv.
  split; apply pi_functor; unsharp_goal.
  apply fst. apply snd.
Defined.

Axiom pi_preserves_products : forall A B,
  eis_equiv (pi_prod_cmp A B).
