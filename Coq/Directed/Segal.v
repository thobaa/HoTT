Add LoadPath "..".
Require Import Homotopy Nat.
Require Import Fin SimplexCategory DirectedInterval.

Open Scope type_scope.

(* In this file we treat types as "directed spaces" or "category-like
   structures", building up to the definitions of Segal types and Rezk
   types ("categories"). *)

(* Simplices with given start and end points. *)

Definition simplices {A} n (a b : A) : Type :=
  { s : simplex n -> A &
    (a == s (sop_simplex (vertex fzero) (tt;tt))) *
    (s (sop_simplex (vertex (from_nat n)) (tt;tt)) == b) }.

(* Single morphisms. *)

Definition hom {A} (a b : A) : Type := simplices 1 a b.

(* A necklace having a given strand type, in a type [A], is a list of
   simplices, of the specified dimensions, which meet at their
   first+last vertices. *)

Fixpoint necklaces {A} {n k} (st : strand_type n k) (a b : A) : Type :=
  match st in strand_type n k with
    | stnil => a == b
    | stcons n' k' i st' => 
      { c : A & simplices (to_nat i) a c * necklaces st' c b}
  end.

(* Composable strings *)

Definition string {A} n := @necklaces A n n (id_strand n).

(* For any strand type [st], every simplex of dimension [n] has an
   underlying necklace of type [st]. *)

Definition neck_spine {A} {n k} (st : strand_type n k) (a b : A) :
  simplices n a b -> necklaces st a b.
Proof.
  revert a b.
  induction st as [|n' k' i st']; intros a b.
  (* Case: stnil *)  
  exact (fun s => fst (pr2 s) @ snd (pr2 s)).
  (* Case: stcons *)
  intros s.
  (* The break-point *)
  exists (pr1 s (sop_simplex (vertex i) (tt;tt))); split; simpl.
  (* The simplex before the break-point (the bead) *)
  exists (pr1 s o sop_simplex (bead i)); split; unfold compose; simpl.
  (* The bead simplex has the correct start-point [a] *)
  path_via (pr1 s (sop_simplex (vertex fzero) (tt;tt)));
  [ apply (fst (pr2 s))
  | path_via (sop_simplex (sop_compose (bead i) (vertex fzero)) (tt;tt));
    [ apply happly, map, opposite, bead_vertex_first
    | apply opposite, sop_compose_functoriality]].
  (* The bead simplex has the correct end-point (the break-point) *)
  apply map;
  path_via (sop_simplex
    (sop_compose (bead i) (vertex (from_nat (to_nat i)))) (tt;tt));
  [ apply sop_compose_functoriality
  | apply happly, map, bead_vertex_last].
  (* The necklace after the break-point (arising from the cobead) *)
  apply IHst'.
  exists (pr1 s o sop_simplex (cobead i)); split; unfold compose; simpl.
  (* The cobead necklace has the correct start-point (the break-point) *)
  apply map;
  path_via (sop_simplex (sop_compose (cobead i) (vertex fzero)) (tt;tt));
  [ apply happly, map, cobead_vertex_first
  | apply opposite, sop_compose_functoriality].
  (* The cobead necklace has the correct end-point [b] *)
  path_via (pr1 s (sop_simplex
    (vertex (from_nat n')) (tt ; tt)));
  [ path_via (sop_simplex
    (sop_compose (cobead i) (vertex (from_nat (co_to_nat i)))) (tt;tt));
    [ apply sop_compose_functoriality
    | apply happly, map, cobead_vertex_last ]
  | apply (snd (pr2 s))].
Defined.

(* In particular, any simplex has a spine. *)

Definition spine {A} {n : nat} (a b : A) (s : simplices n a b) : string n a b.
Proof.
  apply neck_spine; auto.
Defined.

(* Any strand inclusion acts on simplices with fixed endpoints. *)

Section StrandOf.

  Context {A:Type} {n k:nat} (st : strand_type n k).

  Definition strand_of_ga :
    sop_simplex (vertex fzero) (tt ; tt) ==
    sop_simplex (strand st) (sop_simplex (vertex fzero) (tt ; tt)).
  Proof.
    path_via (sop_simplex (sop_compose (strand st) (vertex fzero)) (tt;tt)).
    apply happly, map, opposite.
    path_change (vertex (strand_psum st fzero)); apply strand_vertex.
    apply opposite, sop_compose_functoriality.
  Qed.

  Definition strand_of_gb :
    sop_simplex (strand st) (sop_simplex (vertex (from_nat k)) (tt ; tt)) ==
    sop_simplex (vertex (from_nat n)) (tt ; tt).
  Proof.
    path_via (sop_simplex (sop_compose (strand st) (vertex (from_nat k))) (tt;tt)).
    apply sop_compose_functoriality.
    apply happly, map.
    path_via (vertex (strand_psum st (from_nat k))).
    apply strand_vertex.
    apply strand_psum_total.
  Qed.

  Definition strand_of {a b : A} (s : simplices n a b) : simplices k a b
    := ((pr1 s) o sop_simplex (strand st) ;
      (fst (pr2 s) @ map (pr1 s) strand_of_ga ,
        map (pr1 s) strand_of_gb @ snd (pr2 s))).

End StrandOf.

(* In particular, we have the diagonal of a simplex. *)

Definition diagonal {A} {n : nat} {a b : A} (s : simplices n a b) : hom a b
  := strand_of (stcons (from_nat n) (stnil' n)) s.

(* Segal types *)

(* [spine 0] and [spine 1] are always equivalences. *)

Theorem spine0_is_equiv A a b : is_equiv (@spine A 0 a b).
Proof.
  unfold spine, simplices, neck_spine; simpl.
  set (atos := (fun a => fun (x:simplex 0) => a) : A -> (simplex 0 -> A)).
  assert (atoseq : is_equiv atos).
  apply hequiv_is_equiv with (g := fun f => f (tt;tt)).
  intros h; unfold atos; apply funext; intros [x is].
  destruct x; destruct is; auto.
  intros x; unfold atos; auto.
  set (Q := fun (s:simplex 0 -> A) =>
    (a == s (sop_simplex (vertex fzero) (tt ; tt))) *
    (s (sop_simplex (vertex fzero) (tt ; tt)) == b)).
  change (is_equiv (fun s : sigT Q =>  fst (pr2 s) @ snd (pr2 s))).
  set (f := total_map atos (fun x : A => idmap (Q (atos x)))).
  set (feq := pullback_total_is_equiv Q (atos;atoseq): is_equiv f).
  apply @equiv_cancel_right with (f := (f;feq)).
  unfold compose, Q, atos; simpl.
  clear feq; clear atoseq.
  refine (@transport _ is_equiv (fun x => fst (pr2 x) @ snd (pr2 x)) _ _ _).
  apply funext; intros [x [p q]]; auto.
  clear f; clear Q; clear atos.
  refine (hequiv_is_equiv _ (fun r => (a;(idpath a,r))) _ _).
  path_induction.
  intros [x [p q]]; path_induction.
Defined.

Definition pm_paths_rect A (a:A) (P : forall b, (a==b) -> Type) :
  P a (idpath a) -> forall b p, P b p.
Proof.
  path_induction.
Defined.

Definition copm_paths_rect A (a:A) (P : forall b, (b==a) -> Type) :
  P a (idpath a) -> forall b p, P b p.
Proof.
  path_induction.
Defined.

Lemma paths_rect_idpath A (a b : A) (p : a == b) :
  paths_rect A (fun x y _ => x == y) (fun x => idpath x) a b p == p.
Proof.
  path_induction.
Defined.

Program Definition spine1_is_equiv A a b : is_equiv (@spine A 1 a b)
  := hequiv_is_equiv _ _ _ _.
Next Obligation.
  intros A a b [c [[s [p q]] r]].
  exists s; split; try assumption.
  path_via c; auto.
Defined.
Next Obligation.
  intros A a b [c [[s [p q]] r]].
  simpl in *.
  induction r as [b].
  cancel_units.
  generalize dependent b.
  apply pm_paths_rect.
  generalize dependent a.
  apply copm_paths_rect.
  unfold spine. simpl.
  match goal with | |- ?a == ?b =>
    refine (total_path _ _ a b (idpath _) _)
  end.
  simpl.
  set (u := (@sop_simplex 0 1 (vertex (@fzero 1)) (tt ; tt))).
  set (v := (@sop_simplex 0 1 (vertex (fsucc (@fzero 0))) (tt ; tt))).
  apply prod_path; simpl.
  (* first half *)
  match goal with | |- ?a == ?b =>
    refine (total_path _ _ a b
      (@funext _ _ (s o sop_simplex (bead (fsucc fzero))) s
        (fun x => map s (id_sop_simplex 1 x)))
      _)
  end.
  simpl.
  refine (concat (trans_prod _ _ _ _ _ _ _ _) _).
  apply prod_path; simpl.
  (* first quarter *)
  refine (concat (map_trans _ (fun s' => s' u) _ _ ) _).
  match goal with | |- transport ?p ?x == ?y =>
    path_via (transport (map s (id_sop_simplex 1 u)) x)
  end.
  apply happly, map.
  refine (funext_compute (fun x => map s (id_sop_simplex 1 x)) _).
  match goal with | |- transport ?p (paths_rect _ _ _ _ _ ?q) == ?y =>
    path_via (transport p q);
    [ apply paths_rect_idpath
      | path_via (q @ p) ]
  end.
  undo_concat_map.
  path_via (map s (idpath u)).
  apply prop_path; refine (simplex_is_set 1 _ _).
  (* second quarter *) 
  refine (concat (map_trans (fun a : A => a == s v)
    (fun s' => s'
      (* for some reason, writing [v] here doesn't work. *)
      (sop_simplex (vertex (fsucc (@fzero 0))) (tt ; tt))
    ) _ _ ) _).
  match goal with | |- transport ?p ?x == ?y =>
    path_via (transport (P := fun a : A => a == s v)
      (map s (id_sop_simplex 1 v)) x)
  end.
  apply happly, map.
  refine (funext_compute (fun x => map s (id_sop_simplex 1 x)) _).
  match goal with | |- transport ?p ?q == ?y =>
    path_via (q @ p)
  end.
  undo_concat_map.
  path_via (map s (idpath v)).
  apply prop_path; refine (simplex_is_set 1 _ _).
  (* second half *)
  cancel_units.
  undo_concat_map.
  path_via (map s (idpath v)).
  apply prop_path; refine (simplex_is_set 1 _ _).
Defined.
Next Obligation.
  intros A a b [s [p q]].
  simpl in *.
  generalize dependent b.
  apply pm_paths_rect.
  generalize dependent a.
  apply copm_paths_rect.
  match goal with | |- ?a == ?b =>
    refine (total_path _ _ a b
      (@funext _ _ (s o sop_simplex (bead (fsucc fzero))) s
        (fun x => map s (id_sop_simplex 1 x)))
      _)
  end. simpl.
  set (u := (@sop_simplex 0 1 (vertex (@fzero 1)) (tt ; tt))).
  set (v := (@sop_simplex 0 1 (vertex (fsucc (@fzero 0))) (tt ; tt))).
  refine (concat (trans_prod _ _ _ _ _ _ _ _) _).
  apply prod_path; simpl.
  (* first half *)
  refine (concat (map_trans _ (fun s' => s' u) _ _ ) _).
  match goal with | |- transport ?p ?x == ?y =>
    path_via (transport (map s (id_sop_simplex 1 u)) x)
  end.
  apply happly, map.
  refine (funext_compute (fun x => map s (id_sop_simplex 1 x)) _).
  match goal with | |- transport ?p (paths_rect _ _ _ _ _ ?q) == ?y =>
    path_via (transport p q);
    [ apply paths_rect_idpath
      | path_via (q @ p) ]
  end.
  undo_concat_map.
  path_via (map s (idpath u)).
  apply prop_path; refine (simplex_is_set 1 _ _).
  (* second half *)
  refine (concat (map_trans (fun a : A => a == s v)
    (fun s' => s'
      (* for some reason, writing [v] here doesn't work. *)
      (sop_simplex (vertex (fsucc (@fzero 0))) (tt ; tt))
    ) _ _ ) _).
  match goal with | |- transport ?p ?x == ?y =>
    path_via (transport (P := fun a : A => a == s v)
      (map s (id_sop_simplex 1 v)) x)
  end.
  apply happly, map.
  refine (funext_compute (fun x => map s (id_sop_simplex 1 x)) _).
  match goal with | |- transport ?p ?q == ?y =>
    path_via (q @ p)
  end.
  cancel_units.
  undo_concat_map.
  path_via (map s (idpath v)).
  apply prop_path; refine (simplex_is_set 1 _ _).
Defined.

(* Thus, there is some redundancy in this definition (we actually only
   need to assert it for n > 1). *)

Class segal (A : Type) := {
  segal_is_equiv : forall (n:nat) (a b : A), is_equiv (@spine A n a b)
}.

Lemma is_segal_is_prop A : is_prop (segal A).
Proof.
  apply allpath_prop.
  intros s1 s2.
  destruct s1 as [s1], s2 as [s2].
  apply map.
  repeat (apply funext_dep; let H := fresh in intros H).
  apply prop_path, iscontr_isprop.
Defined.

Section SegalType.

  Context {A : Type} {As : segal A}.
  Existing Instance As.

  Definition segal_spine_equiv n (a b : A) :
    simplices n a b <~> string n a b
    := (spine a b ; segal_is_equiv n a b).

  (* n-ary composition in a Segal type *)

  Definition scompn {n} {a b : A} : string n a b -> hom a b.
  Proof.
    intros s.
    apply (@diagonal _ n).
    apply (segal_spine_equiv n _ _ ^-1).
    assumption.
  Defined.

  Definition scomp {a b c : A} : hom b c -> hom a b -> hom a c.
  Proof.
    intros g f.
    apply (@scompn 2).
    exact (b ; (f , (c ; (g , idpath c)))).
  Defined.

  (* Identities in a Segal type *)

  Definition sid (a : A) : hom a a.
  Proof.
    exists ((fun _ => a) o sop_simplex (@sop_to0 1));
      unfold compose; split; auto.
  Defined.

  (* We need associativity and unitality for these operations.  These
     should be derivable from the Segal condition using simplicial
     operators on 2- and 3-simplices, but all approaches I've tried so
     far are technically extremely messy, so I haven't managed to push
     any of them through all the way. *)

  Definition scomp_idright {a b : A} (f : hom a b) :
    scomp f (sid a) == f.
  Admitted.

  Definition scomp_idleft {a b : A} (f : hom a b) :
    scomp (sid b) f == f.
  Admitted.

  Definition scomp_assoc {a b c d : A} (f : hom a b) (g : hom b c) (h : hom c d) :
    scomp h (scomp g f) == scomp (scomp h g) f.
  Admitted.

  (* Internal equivalences in a Segal type, defined as h-isomorphisms. *)

  Definition sis_equiv {a b : A} (f : hom a b)
    := {g : hom b a & scomp g f == sid a} *
    {h : hom b a & scomp f h == sid b}.

  Definition sequiv (a b : A) := {f : hom a b & sis_equiv f}.

  (* Composing with an internal equivalence is an external equivalence. *)

  Lemma spostcomp_equiv_is_equiv {a b c : A} (f : hom b c) (feq : sis_equiv f) :
    is_equiv (fun g : hom a b => scomp f g).
  Proof.
    destruct feq as [[g r] [h s]].
    apply hiso_to_equiv; split.
    exists (fun k => scomp g k); intros k.
    refine (concat (scomp_assoc _ _ _) _).
    refine (concat _ (scomp_idleft k)).
    apply happly, map, r.
    exists (fun k => scomp h k); intros k.
    refine (concat (scomp_assoc _ _ _) _).
    refine (concat _ (scomp_idleft k)).
    apply happly, map, s.
  Defined.

  Lemma sprecomp_equiv_is_equiv {a b c : A} (f : hom a b) (feq : sis_equiv f) :
    is_equiv (fun g : hom b c => scomp g f).
  Proof.
    destruct feq as [[g r] [h s]].
    apply hiso_to_equiv; split.
    exists (fun k => scomp k h); intros k.
    refine (concat (!scomp_assoc _ _ _) _).
    refine (concat _ (scomp_idright k)).
    apply map, s.
    exists (fun k => scomp k g); intros k.
    refine (concat (!scomp_assoc _ _ _) _).
    refine (concat _ (scomp_idright k)).
    apply map, r.
  Defined.

  (* Being an internal equivalence is an (external) h-prop. *)

  Lemma sis_equiv_is_prop (a b : A) (f : hom a b) : is_prop (sis_equiv f).
  Proof.
    apply allpath_prop.
    intros [[g1 r1] [h1 s1]] [[g2 r2] [h2 s2]].
    apply prod_path; apply contr_path.
    refine (sprecomp_equiv_is_equiv f ((g1;r1),(h1;s1)) (sid a)).
    refine (spostcomp_equiv_is_equiv f ((g1;r1),(h1;s1)) (sid b)).
  Defined.

  (* The identity is an internal equivalence *)

  Definition sid_sis_equiv (a : A) : sis_equiv (sid a)
    := ((sid a ; scomp_idleft (sid a)),(sid a ; scomp_idleft (sid a))).

  Definition sid_equiv (a : A) : sequiv a a
    := (sid a ; sid_sis_equiv a).

  (* The internal version of [path_to_equiv] in a Segal type. *)

  Definition spath_to_equiv (a b : A) : (a == b) -> sequiv a b.
  Proof.
    intros p; induction p; apply sid_equiv.
  Defined.

End SegalType.

(* The Rezk-completeness condition on a Segal type is like an internal
   version of the univalence axiom.
   *)

Class rezk (A : Type) {is_segal : segal A}:= {
  rezk_is_equiv : forall (a b:A), is_equiv (spath_to_equiv a b)
}.
