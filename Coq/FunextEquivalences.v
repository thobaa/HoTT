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

Lemma postcomp_equiv_dep A P Q (g : forall a:A, P a <~> Q a) :
  (forall a, P a) <~> (forall a, Q a).
Proof.
  exists (fun f a => g a (f a)).
  apply @hequiv_is_equiv with (g := fun k a => (g a ^-1) (k a));
    intros k; apply funext_dep; intros a; unfold compose; simpl.
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

(** Given an iterated fibration, to give a section of the composite
   fibration is equivalent to giving a section of the first fibration and
   a section over that of the second.  *)

Lemma section_total_equiv A (P : A -> Type) (Q : forall a, P a -> Type) :
  (forall a, sigT (Q a)) <~> {s : forall a, P a & forall a, Q a (s a) }.
Proof.
  exists (fun f => (existT (fun s => forall a, Q a (s a))
    (fun a => pr1 (f a)) (fun a => pr2 (f a)))).
  apply hequiv_is_equiv with
    (g := fun sr:{s : forall a, P a & forall a, Q a (s a) } =>
      let (s,r) := sr in (fun a => existT (Q a) (s a) (r a))).
  intros [s r].
  set (p := funext_dep (f := eta_dep s) (g := s) (fun a => idpath (s a))).
  apply total_path with p; simpl.
  apply funext_dep; intros a.
  apply (concat (trans_map p
    (fun s' (r': forall a, Q a (s' a)) => r' a) (eta_dep r))).
  path_via (transport (happly_dep p a) (eta_dep r a)).
  unfold happly_dep.
  apply @map_trans with (f := fun h : forall a' : A, P a' => h a).
  path_via (transport (idpath (s a)) (eta_dep r a)).
  apply happly, map.
  apply funext_dep_compute with
    (f := eta_dep s) (g := s) (p := fun a' : A => idpath (s a')).
  intros f.
  apply funext_dep; intros a.
  destruct (f a); auto.
Defined.
