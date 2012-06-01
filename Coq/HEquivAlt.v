Require Export Paths Fibrations Contractible Equivalences.
Close Scope nat_scope.

(* Homotopy equivalence data. *)

Definition hequiv {A B} (f : A -> B) :=
  { g : B -> A & (forall y, (f (g y)) == y) * (forall x, (g (f x)) == x) }.

(* The 2-out-of-3 property for homotopy equivalences. *)

Theorem hequiv_compose {A B C} (f : A -> B) (g : B -> C) :
  hequiv f -> hequiv g -> hequiv (g o f).
Proof.
  intros [finv [fs fr]] [ginv [gs gr]].
  exists (finv o ginv). split.
  intros y;  unfold compose; path_via (g (ginv y)).
  intros x;  unfold compose; path_via (finv (f x)).
Defined.

Theorem hequiv_cancel_right {A B C} (f : A -> B) (g : B -> C) :
  hequiv f -> hequiv (g o f) -> hequiv g.
Proof.
  intros [finv [fs fr]] [gfinv [gfs gfr]].
  exists (f o gfinv); split.
  intros y; apply gfs.
  intros x; unfold compose; path_via (f (gfinv (g (f (finv x))))).
  path_via (f (finv x)). apply gfr.
Defined.

Theorem hequiv_cancel_left {A B C} (f : A -> B) (g : B -> C) :
  hequiv g -> hequiv (g o f) -> hequiv f.
Proof.
  intros [ginv [gs gr]] [gfinv [gfs gfr]].
  exists (gfinv o g); split.
  intros y; unfold compose; path_via (ginv (g (f (gfinv (g y))))).
  path_via' (ginv (g y)).
  apply map; apply gfs. apply gr.
  intros x; apply gfr.
Defined.

(* Any equivalence is a homotopy equivalence. *)

Definition equiv_hequiv {A B} (f : A <~> B) : hequiv f
  := (inverse f; (inverse_is_section f, inverse_is_retraction f)).

(* A fibration which is a homotopy equivalence has contractible fibers. *)

Lemma hequiv_fibration_fibcontr {A} (P : A -> Type) :
  hequiv (@projT1 A P) -> forall x, is_contr (P x).
Proof.
  intros [g [gs gr]].
  (* First we transport to get a section. *)
  set (h := fun x => transport (gs x) (pr2 (g x))).
  (* That section is also a homotopy retraction. *)
  assert (hr : forall y, (pr1 y ; h (pr1 y)) == y).
  intros y; path_via (g (pr1 y)). apply opposite.
  refine (total_path _ _ _ (pr1 y;h(pr1 y)) (gs (pr1 y)) _); auto.
  (* Now we do an easy sort of adjointification. *)
  intros x; exists (h x).
  intros y; apply opposite.
  path_via (transport (map pr1 (hr (x;y))) (h x)).
  apply opposite, map_dep.
  apply (fiber_path (hr (x;y))).
Defined.

(* Any homotopy equivalence is an equivalence. *)

Theorem hequiv_to_equiv {A B} (f : A -> B) : hequiv f -> is_equiv f.
Proof.
  intros fh.
  (* We apply the previous lemma to the fibration replacing f. *)
  unfold is_equiv; apply hequiv_fibration_fibcontr with (P := hfiber f).
  (* Since f is a homotopy equivalence, so is it... *)
  refine (@hequiv_cancel_right A _ B (fun x => (f x;(x;idpath (f x)))) _ _ _).
  2:apply fh.
  (* ...as long as it factors through f via a homotopy equivalence. *)
  exists (fun y:sigT (hfiber f) => pr1 (pr2 y)); split; auto.
  intros [y [x p]]; simpl.
  apply total_path with p. simpl.
  path_via (existT (fun x' => f x' == y) x (transport p (idpath (f x)))).
  refine (trans_sum _ _ _ _ _ _ _ _).
  path_via (idpath (f x) @ p).
  apply trans_is_concat.
Defined.

(* Of course, the 2-out-of-3 property for equivalences follows. *)

Corollary equiv_compose' {A B C} (f : A <~> B) (g : B <~> C) : (A <~> C).
Proof.
  exists (g o f).
  apply hequiv_to_equiv, hequiv_compose; apply equiv_hequiv.
Defined.

Corollary equiv_cancel_right' {A B C} (f : A <~> B) (g : B -> C) :
  is_equiv (g o f) -> is_equiv g.
Proof.
  intros gfe; apply hequiv_to_equiv.
  apply hequiv_cancel_right with f;
    [ apply equiv_hequiv | exact (equiv_hequiv (g o f; gfe)) ].
Defined.

Corollary equiv_cancel_left' {A B C} (f : A -> B) (g : B <~> C) :
  is_equiv (g o f) -> is_equiv f.
Proof.
  intros gfe; apply hequiv_to_equiv.
  apply hequiv_cancel_left with g;
    [ apply equiv_hequiv | exact (equiv_hequiv (g o f; gfe)) ].
Defined.
