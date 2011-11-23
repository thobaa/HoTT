Require Import Paths Equivalences UsefulEquivalences Funext UnivalenceAxiom.

(** Currying and uncurrying are equivalences. *)

Definition curry_equiv A B C : (A * B -> C) <~> (A -> B -> C).
Proof.
  exists (fun f => fun a b => f (a,b)).
  apply hequiv_is_equiv with (fun g => fun x => g (fst x) (snd x)).
  intro f; apply funext; intro a; apply funext; intro b; auto.
  intro g; apply funext; intros [a b]; auto.
Defined.

Definition arg_comm_equiv A B C : (A -> B -> C) <~> (B -> A -> C).
Proof.
  exists (fun f => fun b a => f a b).
  apply hequiv_is_equiv with (fun g => fun a b => g b a).
  intro g; apply funext; intro a; apply funext; intro b; auto.
  intro f; apply funext; intro b; apply funext; intro a; auto.
Defined.
