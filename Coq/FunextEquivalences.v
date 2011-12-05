Require Import Paths Equivalences UsefulEquivalences Funext UnivalenceAxiom.

(** This file defines some useful equivalences that require functional
   extensionality, usually involving equivalences between function
   spaces. *)

(** Currying and uncurrying are equivalences. *)

Definition curry_equiv A B C : (A * B -> C) <~> (A -> B -> C).
Proof.
  exists (fun f => fun a b => f (a,b)).
  apply hequiv_is_equiv with (fun g => fun x => g (fst x) (snd x)).
  intro f; apply funext; intro a; apply funext; intro b; auto.
  intro g; apply funext; intros [a b]; auto.
Defined.

(** Flipping the arguments of a two-variable function is an equivalence. *)

Definition flip_equiv A B C : (A -> B -> C) <~> (B -> A -> C).
Proof.
  exists (fun f => fun b a => f a b).
  apply hequiv_is_equiv with (fun g => fun a b => g b a).
  intro g; apply funext; intro a; apply funext; intro b; auto.
  intro f; apply funext; intro b; apply funext; intro a; auto.
Defined.

(** Pre- and post-composing by an equivalence is an equivalence. *)

Lemma precomp_equiv A B C (g : A <~> B) : (B -> C) <~> (A -> C).
Proof.
  exists (fun h => h o g).
  apply @hequiv_is_equiv with (g := fun k => k o (g ^-1));
    intros k; apply funext; intros a; unfold compose; simpl; apply map.
  apply inverse_is_retraction.
  apply inverse_is_section.
Defined.

Lemma postcomp_equiv A B C (g : B <~> C) : (A -> B) <~> (A -> C).
Proof.
  exists (fun h => g o h).
  apply @hequiv_is_equiv with (g := fun k => (g ^-1) o k);
    intros k; apply funext; intros a; unfold compose; simpl.
  apply inverse_is_section.
  apply inverse_is_retraction.
Defined.

(** Cartesian products have the correct universal property. *)

Lemma prod_equiv A B T :
  (T -> A) * (T -> B) <~> (T -> A * B).
Proof.
  exists (fun fg => fun t => (fst fg t, snd fg t)).
  apply @hequiv_is_equiv with
    (fun h => (fun t => fst (h t), fun t => snd (h t))).
  intros h; apply funext; intros t; simpl.
  destruct (h t) as [a b]; auto.
  intros [f g]; apply prod_path; apply funext; intros t; auto.
Defined.

