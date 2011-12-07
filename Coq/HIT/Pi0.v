Add LoadPath "..".
Require Import Homotopy.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** The definition of [pi0], the 0-truncation.  Here is what it would
   look like if Coq supported higher inductive types natively:

   Inductive pi0 (A : Type) : Type :=
   | cpnt : A -> pi0 A
   | pi0_axiomK : forall (x : pi0 A) (l : x == x), l == idpath x.

   Strictly speaking, we should phrase the second constructor in terms
   of a function [Circle -> pi0 A] instead of a point [x] and a loop
   [l] in order to match the syntax of inductive types, but we know
   that a map out of a circle is equivalent to a point and a loop.
*)

Axiom pi0 : forall (A : Type), Type.

Axiom cpnt : forall {A : Type}, A -> pi0 A.

Axiom pi0_axiomK : forall {A : Type} (x : pi0 A) (l : x == x), l == idpath x.

Axiom pi0_rect : forall {A : Type} {P : pi0 A -> Type}
  (dcpnt : forall (x : A), P (cpnt x))
  (daxiomK : forall (x : pi0 A) (l : x == x) (z : P x) (dl : transport l z == z),
    dl == map (fun p: x == x => transport p z) (pi0_axiomK x l)),
  forall (x : pi0 A), P x.

Axiom pi0_compute_cpnt : forall {A : Type} {P : pi0 A -> Type}
  (dcpnt : forall (x : A), P (cpnt x))
  (daxiomK : forall (x : pi0 A) (l : x == x) (z : P x) (dl : transport l z == z),
    dl == map (fun p: x == x => transport p z) (pi0_axiomK x l))
  (a : A),
  pi0_rect dcpnt daxiomK (cpnt a) == dcpnt a.

Definition map2_dep_loop {X : Type} {P : X -> Type} {x : X} {l : x == x}
  (f : forall x, P x) (s : l == idpath x) :
  map_dep f l ==  trans2 s (f x).
Proof.
  intros X P x l f s.
  match goal with |- _ == ?t => path_via (t @ map_dep f (idpath x)) end.
  apply map2_dep.
Defined.

Axiom pi0_compute_axiomK : forall {A : Type} {P : pi0 A -> Type}
  (dcpnt : forall (x : A), P (cpnt x))
  (daxiomK : forall (x : pi0 A) (l : x == x) (z : P x) (dl : transport l z == z),
    dl == map (fun p: x == x => transport p z) (pi0_axiomK x l))
  (x : pi0 A) (l : x == x),
  map2_dep_loop (pi0_rect dcpnt daxiomK) (pi0_axiomK x l)
  == daxiomK x l (pi0_rect dcpnt daxiomK x) (map_dep (pi0_rect dcpnt daxiomK) l).

(** The non-dependent eliminator. *)

Definition pi0_rect_nondep {A B : Type}
  (dcpnt' : A -> B)
  (daxiomK' : forall (z : B) (dl : z == z), dl == idpath z) :
  pi0 A -> B.
Proof.
  intros A B dcpnt' daxiomK'.
  apply pi0_rect.
  exact dcpnt'.
  intros x l z dl.
  apply concat_cancel_left with (p := !trans_trivial l z).
  path_via (idpath z).
Defined.

Definition pi0_compute_cpnt_nondep {A B : Type}
  (dcpnt' : A -> B)
  (daxiomK' : forall (z : B) (dl : z == z), dl == idpath z)
  (a : A) :
  pi0_rect_nondep dcpnt' daxiomK' (cpnt a) == dcpnt' a.
Proof.
  intros A B dcpnt' daxiomK' a.
  unfold pi0_rect_nondep.
  apply @pi0_compute_cpnt with (P := fun a => B).
Defined.

Definition pi0_compute_axiomK_nondep  {A B : Type}
  (dcpnt' : A -> B)
  (daxiomK' : forall (z : B) (dl : z == z), dl == idpath z)
  (x : pi0 A) (l : x == x) :
  map2 (pi0_rect_nondep dcpnt' daxiomK') (pi0_axiomK x l)
  == daxiomK' (pi0_rect_nondep dcpnt' daxiomK' x) (map (pi0_rect_nondep dcpnt' daxiomK') l).
Proof.
  intros.
  apply contr_path.
  apply (axiomK_implies_isset daxiomK'
    (pi0_rect_nondep dcpnt' daxiomK' x) (pi0_rect_nondep dcpnt' daxiomK' x)).
Defined.

(* The above proof is arguably cheating; the "real" proof should make
   use of [pi0_compute_axiomK].  However, this proof is *homotopic*
   to that proof, since both are inhabitants of a contractible type,
   so since the axioms are only given up to homotopy anyway it
   shouldn't matter.  And trying to write down the "real" proof is
   pretty horrific; just the *type* of the lemma [map2_dep_trivial]
   that seems to be needed is longer than this proof in its
   entirety!

Lemma homotopy_naturality_toconst {A B} (f : A -> B) (z : B)
  (p : forall x, f x == z) (x y : A) (q : x == y) :
  map f q @ p y == p x.
Proof.
  path_induction.
  cancel_units.
Defined.

Lemma map2_dep_trivial {A B : Type} {x y : A} {p q : x == y}
  (f : A -> B) (s : p == q) :
  map2_dep f s ==
  map_dep_trivial f p @
  (!(homotopy_naturality_toconst
    (fun p => transport (P := fun a => B) p (f x)) (f x)
    (fun p => trans_trivial p (f x)) p q s)
    @@ map2 f s)
  @ concat_associativity _  _ _ _ _  _ _ _
  @ whisker_left (map (fun p : x == y => transport (P := fun a => B) p (f x)) s) (!map_dep_trivial f q).
Proof.
  path_induction.
Defined.

*)

(** [pi0 A] is a set. *)

Theorem pi0_is_set (A : Type) : is_set (pi0 A).
Proof.
  intro A.
  apply axiomK_implies_isset.
  intros x y.
  apply pi0_axiomK.
Defined.

(** And if [A] was already a set, then [pi0 A] is equivalent to it. *)

Theorem set_pi0_is_equiv (A : Type) :
  is_set A -> is_equiv (@cpnt A).
Proof.
  intros A H.
  set (inv := pi0_rect_nondep (idmap A) (isset_implies_axiomK H)).
  apply hequiv_is_equiv with (g := inv).
  apply pi0_rect.
  intro x.
  apply map.
  apply pi0_compute_cpnt_nondep.
  intros x l p dl.
  apply contr_path.
  apply (pi0_is_set A _ x (transport (P := fun x => cpnt (inv x) == x) l p) p).
  intro x.
  apply pi0_compute_cpnt_nondep.
Defined.
