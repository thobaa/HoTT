Require Import Homotopy.

Section ReflectiveSubcategory.

  Hypothesis in_rsc : Type -> Type.

  Hypothesis in_rsc_prop : forall X, is_prop (in_rsc X).

  Hypothesis reflect : Type -> Type.

  Hypothesis reflect_in_rsc : forall X, in_rsc (reflect X).

  Hypothesis map_to_reflect : forall X, X -> reflect X.

  Hypothesis reflect_is_reflection : forall X Y, in_rsc Y ->
    is_equiv (fun f: reflect X -> Y => f ○ map_to_reflect X).

  Definition reflection_equiv : forall X Y, in_rsc Y ->
    equiv (reflect X -> Y) (X -> Y).
  Proof.
    intros X Y P.
    apply tpair with (fun f: reflect X -> Y => f ○ map_to_reflect X).
    apply reflect_is_reflection.
    assumption.
  Defined.

  Definition reflect_functor : forall X Y, (X -> Y) -> (reflect X -> reflect Y).
  Proof.
    intros X Y f.
    apply ((reflection_equiv X (reflect Y) (reflect_in_rsc Y))⁻¹).
    apply @compose with (B:=Y).
    apply map_to_reflect.
    assumption.
  Defined.

  Lemma reflect_equiv_in_rsc : forall X, is_equiv (map_to_reflect X) -> in_rsc X.
    intros X H.
    set (eqvpath := equiv_to_path (tpair (map_to_reflect X) H)).
    apply @transport with (P := in_rsc) (x := reflect X).
    exact (!eqvpath).
    apply reflect_in_rsc.
  Defined.

  Definition unit_in_rsc : in_rsc unit.
  Proof.
    apply reflect_equiv_in_rsc.
    apply hequiv_is_equiv with (g:= fun x => tt).
    assert (p: (fun x => map_to_reflect unit tt) ~~> @id (reflect unit)).
    apply equiv_injective with
      (w := reflection_equiv unit (reflect unit) (reflect_in_rsc unit)).
    unfold reflection_equiv.
    simpl.
    apply funext.
    intro x.
    induction x.
    auto.
    apply (happly p).
    intros x; induction x; auto.
  Defined.

  Hypothesis X:Type.
  Hypothesis X_in_rsc : in_rsc X.
  Hypothesis x₀:X.

  Lemma loop_map_back : reflect (x₀ ~~> x₀) -> (x₀ ~~> x₀).
  Proof.
    intros rl.
    assert (p : (fun _:reflect (x₀ ~~> x₀) => x₀) ~~> (fun _:reflect (x₀ ~~> x₀) => x₀)).
    apply ((equiv_map_equiv (reflection_equiv (x₀ ~~> x₀) X X_in_rsc))⁻¹).
    unfold reflection_equiv.
    simpl.
    apply funext.
    intro l.
    unfold compose.
    assumption.
    apply (happly p).
    assumption.
  Defined.

  Lemma map_compose A B C (f : B -> C) (g : B -> C) (h : A -> B)
    (p : f ~~> g) (a : A) :
    happly (map (fun f' => f' ○ h) p) a ~~> happly p (h a).
  Proof.
    path_induction.
  Defined.

  Lemma loop_map_back_retraction (x : x₀ ~~> x₀) :
    loop_map_back (map_to_reflect (x₀ ~~> x₀) x) ~~> x.
  Proof.
    unfold loop_map_back.
    path_via
    (happly
      (map (fun f' => f' ○ (map_to_reflect _))
        ((equiv_map_equiv (reflection_equiv (x₀ ~~> x₀) X X_in_rsc) ⁻¹)
          (funext
            ((fun _ => x₀) ○ map_to_reflect _)
            ((fun _ => x₀) ○ map_to_reflect _)
            (fun l : x₀ ~~> x₀ => l)))) x).
    apply opposite, map_compose.
    path_via
    (happly
      (equiv_map_equiv (reflection_equiv (x₀ ~~> x₀) X X_in_rsc)
        ((equiv_map_equiv (reflection_equiv (x₀ ~~> x₀) X X_in_rsc) ⁻¹)
          (funext
            ((fun _ => x₀) ○ map_to_reflect (x₀ ~~> x₀))
            ((fun _ => x₀) ○ map_to_reflect (x₀ ~~> x₀))
            (fun l : x₀ ~~> x₀ => l)))) x).
    (* Apparently the cancel_inverses tactic is insufficiently smart. *)
    cancel_inverses.
    apply map with (f := fun g => happly g x).
    cancel_inverses.
    unfold funext.
    apply strong_funext_compute with
      (f := ((fun _ => x₀) ○ map_to_reflect (x₀ ~~> x₀)))
      (g := ((fun _ => x₀) ○ map_to_reflect (x₀ ~~> x₀))).
  Defined.

  Definition loop_in_rsc : in_rsc (x₀ ~~> x₀).
  Proof.
    apply reflect_equiv_in_rsc.
    apply hequiv_is_equiv with (g:=loop_map_back).
    assert (p : map_to_reflect _ ○ loop_map_back ~~> @id _).
    apply equiv_injective with
      (w := (reflection_equiv (x₀ ~~> x₀) (reflect (x₀ ~~> x₀)) (reflect_in_rsc _))).
    unfold reflection_equiv. simpl.
    apply funext. intros x.
    unfold compose; simpl. unfold id.
    apply map.
    apply loop_map_back_retraction.
    apply (happly p).
    apply loop_map_back_retraction.
  Defined.

End ReflectiveSubcategory.


