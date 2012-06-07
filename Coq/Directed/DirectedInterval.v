Add LoadPath "..".
Require Import Homotopy Nat.
Require Import Fin SimplexCategory.

Open Scope type_scope.

(* We axiomatize a 0-truncated total order with distinct endpoints,
   such as is present in the $(\infty,1)$-topos of simplicial objects
   in any other $(\infty,1)$-topos.  In particular, this occurs in the
   $(\infty,1)$-topos of simplicial $\infty$-groupoids. *)

(* The total order. *)
Axiom I : Type.
Axiom I_is_set : is_set I.

(* The order relation *)
Axiom Ile : I -> I -> Type.
Axiom Ile_is_prop : forall x y, is_prop (Ile x y).

(* It is a total order *)
Axiom Ile_refl : forall x, Ile x x.
Hint Resolve Ile_refl.
Axiom Ile_trans : forall x y z, Ile x y -> Ile y z -> Ile x z.
Axiom Ile_antisym : forall x y, Ile x y -> Ile y x -> x == y.

(* I haven't found a need for this yet, so we may as well not pull in
   IsInhab just to state it. *)
(* Axiom Ile_total : forall x y, is_inhab ((Ile x y) + (Ile y x)). *)

(* The endpoints *)
Axiom bot top : I.
Axiom bot_ne_top : (bot == top) -> Empty_set.
Axiom bot_Ile : forall x, Ile bot x.
Axiom Ile_top : forall x, Ile x top.
Hint Resolve bot_Ile Ile_top.

(* We now define the standard cubes and simplices.  A point of the
   n-cube is an n-tuple of elements of [I], and it lies in the
   n-simplex just when it is nondecreasing.  We represent cubes with
   nested cartesian products with the nesting in the opposite order
   from the usual one, because it matches the traditional numbering of
   vertices in the n-simplex better. *)

Fixpoint cube (n : nat) : Type :=
  match n with
    | 0 => unit
    | S n' => (cube n' * I)
  end.

Fixpoint follows {n} (x:I) : cube n -> Type :=
  match n with
    | 0 => fun _ => unit
    | S n' => fun s => let (s',y) := s in (Ile y x)
  end.

Fixpoint is_simplex {n} : cube n -> Type :=
  match n with
    | 0 => fun _ => unit
    | S n' => fun s => let (s',x) := s in is_simplex s' * follows x s'
  end.

Definition simplex n := sigT (@is_simplex n).

(* Every simplex is 0-truncated (a set). *)

Lemma cube_is_set n : is_set (cube n).
Proof.
  induction n.
  apply hlevel_succ, hlevel_succ, unit_contr.
  apply prod_hlevel; [ apply IHn | apply I_is_set ].
Defined.

Lemma follows_is_prop n x (s : cube n) : is_prop (follows x s).
Proof.
  induction n.
  apply hlevel_succ, unit_contr.
  destruct s as [y s'].
  apply Ile_is_prop.
Defined.

Lemma is_simplex_is_prop n (s : cube n) : is_prop (is_simplex s).
Proof.
  induction n.
  apply hlevel_succ, unit_contr.
  destruct s as [s' x].
  apply prod_hlevel; [ apply IHn | apply follows_is_prop ].
Defined.

Lemma simplex_is_set n : is_set (simplex n).
Proof.
  apply total_hlevel.
  apply cube_is_set.
  intros; apply hlevel_succ, is_simplex_is_prop.
Defined.

(* This tactic proves that two points of a simplex are equal by
   proving that their underlying points of a cube are equal. *)

Ltac simplex_eq :=
  match goal with
    | |- @paths (simplex ?n) ?x ?y =>
      let H := fresh in
        cut (pr1 x == pr1 y);
          [ intros H;
            apply total_path with H;
            apply prop_path, is_simplex_is_prop
          | simpl ]
  end.

(* The 0-simplex is contractible. *)

Definition simplex0_contr : is_contr (simplex 0).
Proof.
  unfold simplex.
  apply total_hlevel with (n := 0).
  unfold is_hlevel, cube; apply unit_contr.
  intros x; unfold is_hlevel, is_simplex; apply unit_contr.
Defined.

(* The 1-simplex is equivalent to the total order [I]. *)

Definition I_simplex1_equiv : I <~> simplex 1.
Proof.
  apply @equiv_compose with (B := unit * I).
  apply prod_unit_left_equiv.
  apply equiv_inverse; exists pr1.
  intros s.
  change (is_hlevel 0 (hfiber (@projT1 (cube 1) is_simplex) s)).
  apply @hlevel_equiv with (A := is_simplex (s : cube 1)).
  apply hfiber_fibration.
  destruct s as [t x].
  apply prod_hlevel; apply unit_contr.
Defined.

(* The top element follows anything *)

Definition top_follows n (s : cube n) : follows top s.
Proof.
  induction n.
  exact tt.
  destruct s as [s' x].
  apply Ile_top.
Defined.

(* The last vertex of a simplex consists of copies of [top]. *)

Fixpoint alltop' n : cube n :=
  match n with
    | 0 => tt
    | S n' => (alltop' n' , top)
  end.

Lemma alltop_is_simplex n : is_simplex (alltop' n).
Proof.
  induction n.
  exact tt.
  split; [ apply IHn | apply top_follows ].
Defined.

Definition alltop n : simplex n := (alltop' n ; alltop_is_simplex n).

(* The first vertex of a simplex consists of copies of [bot]. *)

Fixpoint allbot' n : cube n :=
  match n with
    | 0 => tt
    | S n' => (allbot' n' , bot)
  end.

Lemma bot_follows_allbot n : follows bot (allbot' n).
Proof.
  induction n.
  exact tt.
  simpl; auto.
Defined.

Lemma allbot_is_simplex n : is_simplex (allbot' n).
Proof.
  induction n.
  exact tt.
  split; [ apply IHn | apply bot_follows_allbot ].
Defined.

Definition allbot n : simplex n := (allbot' n ; allbot_is_simplex n).

(* Anything follows the first vertex. *)

Definition follows_allbot n x : follows x (allbot' n).
Proof.
  induction n.
  exact tt.
  simpl; auto.
Defined.

(* Following is covariant in [Ile]. *)

Definition Ile_follows n x y (s : cube n) :
  follows x s -> Ile x y -> follows y s.
Proof.
  induction n.
  intros; exact tt.
  intros p l. destruct s as [s' z].
  apply Ile_trans with x; assumption.
Defined.


(* Now we define the action of the simplicial operators on the
   standard cubes and simplices.  This is where it is convenient to
   represent simplicial operators as maps of total order with side
   basepoints, because the action on standard simplices is just given
   by precomposition with such maps.

   For technical reasons (specifically, to deal with the fact that
   [sop_left] mixes basepoints with non-basepoints), the following
   operation is parametrized by a "pseudo-top element" [top']. *)

Fixpoint sop_cube' {n m} (top':I) (d : sop n m) (x : cube n) : cube m :=
  match d in sop n m return (I -> cube n -> cube m) with
    | sop_to0 n =>
      fun _ _ => tt
    | sop_right n m d =>
      fun top' x => (sop_cube' top' d x, top')
    | sop_left0 m =>
      fun _ _ => allbot' (S m)
    | sop_left n m d =>
      fun top' x => match x with (s,y) => sop_cube' y d s end
  end top' x.

Definition sop_cube {n m} (d : sop n m) (x : cube n) :=
  sop_cube' top d x.

(* This tactic does one step of simplification of [sop_cube']. *)
Ltac do_sop :=
  unfold sop_cube;
  match goal with
    | |- context cxt [ sop_cube' ?top' sop_to0 ?x ] =>
      let next := context cxt [ tt ] in
        change next
    | |- context cxt [ sop_cube' ?top' (sop_right ?d) ?x ] =>
      let next := context cxt [ (sop_cube' top' d x , top') ] in
        change next
    | |- context cxt [ sop_cube' ?top' (@sop_left0 ?m) ?x ] =>
      let next := context cxt [ allbot' (S m) ] in
        change next
    | |- context cxt [ sop_cube' ?top' (sop_left ?d) (?s , ?y) ] =>
      let next := context cxt [ sop_cube' y d s ] in
        change next
    | |- context cxt [ sop_cube' ?top' (sop_left ?d) ?x ] =>
      let next := context cxt [ match x with (s,y) => sop_cube' y d s end ] in
        change next
    | _ => idtac
  end;
  simpl;
  match goal with
    | |- (?a, ?x) == (?b, ?x) =>
      apply map with (f := fun a => (a,x))
    | _ => idtac
  end;
  auto.

(* We observe that when the pseudo-top [top'] is actually [bot], then
   this action preserves the first vertex [allbot']. *)

Lemma sop_cube_allbot n m (d : sop n m) :
  sop_cube' bot d (allbot' n) == allbot' m.
Proof.
  induction d; do_sop.
Defined.

(* Now we have to show that this operation, defined on cubes, takes
   simplices into simplices. *)

Definition sop_cube'_simplex n m (top':I) (d : sop n m) (x : cube n)
  (xs : is_simplex x) (p : follows top' x) :
  (is_simplex (sop_cube' top' d x) * follows top' (sop_cube' top' d x)).
Proof.
  revert top' x xs p.
  induction d; intros; split.
  (* collapse to [0] *)
  exact tt.
  exact tt.
  (* the first one is the supplied [top']. *)
  split; apply IHd; assumption.
  simpl; apply Ile_refl.
  (* everything is bot *)
  apply allbot_is_simplex.
  apply follows_allbot.
  (* the first one is duplicated *)
  destruct x as [s y]; destruct xs as [ss yp].
  apply IHd; [ apply ss | apply yp ].
  destruct x as [s y]; destruct xs as [ss yp].
  apply Ile_follows with y; [ apply (IHd y s ss yp) | apply p ].
Defined.

Definition sop_simplex {n m} (d : sop n m) (x : simplex n) : simplex m.
Proof.
  refine (sop_cube d (pr1 x) ; _).
  intros; apply sop_cube'_simplex; [ apply (pr2 x) | apply top_follows ].
Defined.

(* Now we are ready to evaluate some specific simplicial operators.
   First we do the identity. *)

Definition id_sop_simplex n x : sop_simplex (id_sop n) x == x.
Proof.
  destruct x as [x is].
  simplex_eq.
  unfold sop_cube; set (top' := top); clearbody top'; revert top'.
  induction n; destruct x as [s x]; destruct is as [is fx]; simpl; auto.
  intros top'; repeat do_sop.
Defined.

(* We evaluate the first vertex to allbot. *)

Definition vertex0_is_allbot n :
  sop_simplex (vertex fzero) (tt;tt) == allbot n.
Proof.
  simplex_eq.
  induction n; auto.
Defined.

(* Similarly, we evaluate the last vertex to alltop. *)

Definition vertexn_is_alltop n :
  sop_simplex (vertex (from_nat n)) (tt;tt) == alltop n.
Proof.
  simplex_eq.
  induction n; auto.
  simpl; destruct n; do_vertex; do_sop.
Defined.

(* Unsurprisingly, the collapsing operator [sop_allleft] always produces [allbot]. *)

Definition sop_allleft_is_allbot' n m (s : cube n) top' :
  sop_cube' top' (sop_allleft n m) s == allbot' m.
Proof.
  revert top'.
  destruct m. auto.
  induction n as [|n]. auto.
  intros top'.
  destruct s as [s x].
  path_change (sop_cube' x (sop_allleft n (S m)) s).
Defined.

Definition sop_alleft_is_allbot n m (s : simplex n) :
  sop_simplex (sop_allleft n m) s == allbot m.
Proof.
  simplex_eq.
  apply sop_allleft_is_allbot'.
Defined.


(* The action of simplicial operators is functorial. *)

(* This lemma uses two copies of [m] with and an equality [m == m'],
   to enable us to do a nested induction on both [d] and [e]. *)
Lemma sop_compose_functoriality' n m m' p (q : m == m')
  (d : sop n m) (e : sop m' p) (s : cube n) (top' : I) :
  sop_cube' top' e (transport q (sop_cube' top' d s))
  == sop_cube' top' (sop_compose e (transport q d)) s.
Proof.
  revert top' n m q d s.
  induction e as [m' | m' p_minus_one e' | p_minus_one | m'_minus_one p_minus_one e'];
    intros top' n m q d s.
  (* Case: p=0 *)
  apply idpath.
  (* Case: e sends the last point of [p] to the right, and does [e'] on the rest. *)
  induction q as [m].
  do_sop.
  apply (IHe' top' n m (idpath m)).
  (* Case: e collapses everything in p to the left. *)
  apply opposite, sop_allleft_is_allbot'.
  (* Case: e doesn't hit the last point of [m], and does [e'] onto the rest. *)
  (* Here we go into a nested induction, but first we need to
     generalize the conclusion slightly. *)
  pose (top'' := top').
  path_change (sop_cube' top'' (sop_left e')
     (transport q (sop_cube' top' d s))).
  do_sop_compose.
  clearbody top''.
  revert top' top''.
  induction d as [n | n m d' | m | n_minus_one m d' ];
    intros top' top'';
    try (set (q' := transport (P := fun k => m == match k with 0 => m | S l => l end)
        q (idpath m));
      set (Sqq := prop_path (nat_is_set _ _) (map S q') q);
      pattern q; apply (transport Sqq); clear Sqq;
      clearbody q'; simpl in q'; induction q' as [m]; simpl).
  (* Subcase: Sm=0 (impossible) *)
  apply False_rect.
  exact (transport (P := fun m => match m with 0 => unit | S _ => False end ) q tt).
  (* Subcase: d sends the last point of [m] to the right, and does [d'] on the rest. *)
  apply (IHe' top' n m (idpath m)).
  (* Subcase: d collapses everything in m to the left. *)
  path_change (allbot' (S p_minus_one)).
  apply sop_cube_allbot.
  (* Subcase: d doesn't hit the last point of [n], and does [d'] onto the rest. *)
  destruct s as [s x].
  path_change (sop_cube' top' (sop_left e') (sop_cube' x d' s)).
  apply (IHd' (idpath (S m))).
Defined.

Theorem sop_compose_functoriality n m p
  (d : sop n m) (e : sop m p) (s : simplex n)
  : sop_simplex e (sop_simplex d s) == sop_simplex (sop_compose e d) s.
Proof.
  simplex_eq.
  unfold sop_cube.
  refine (sop_compose_functoriality' _ _ _ _ (idpath _) d e (pr1 s) top).
(* We make this opaque so that Coq doesn't try to unfold it.  It
   doesn't matter what it computes to, since all simplices are sets. *)
Qed.
