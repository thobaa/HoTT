(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext.
Require Import Modalities.Modality.
Require Import hit.Truncations hit.Connectedness hit.quotient.
Import TrM.
Require Import Spaces.Finite.
Require Import Peano.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Groups *)

(** ** Definition *)

Record Group :=
  { classifying_space : PointedType ;
    isconn_classifying_space : IsConnected 0 classifying_space
    (** ; istrunc_classifying_space : IsTrunc 1 classifying_space *)
  }.

Global Existing Instance isconn_classifying_space.
(** Global Existing Instance istrunc_classifying_space. *)

Local Notation B := classifying_space.

Definition group_set (G : Group) : Type
  := point (B G) = point (B G).

Coercion group_set : Group >-> Sortclass.

Definition group_loopspace (X : PointedType) (** `{IsTrunc 1 X} *)
: Group.
Proof.
  refine (Build_Group
            (Build_PointedType
               { x:X & merely (x = point X) }
               ( point X ; tr 1 ))
               _ (** _ *)); try exact _.
  refine (conn_pointed_type (point _)); try exact _.
  apply BuildIsSurjection; simpl; intros [x p].
  strip_truncations; apply tr; exists tt.
  apply path_sigma_hprop; simpl.
  exact (p^).
Defined.

Definition loopspace_group (X : PointedType) (** `{IsTrunc 1 X} *)
: loopspace X <~> group_loopspace X.
Proof.
  unfold loopspace, group_set. simpl.
  exact (equiv_path_sigma_hprop (point X ; tr 1) (point X ; tr 1)).
Defined.            

(** ** Homomorphisms *)

Definition GroupHom (G H : Group) :=
  PointedMap (B G) (B H).

Definition grouphom_fun {G H} (phi : GroupHom G H) : G -> H
  := loopspace_functor phi.

Coercion grouphom_fun : GroupHom >-> Funclass.

Definition group_loopspace_functor
           {X Y : PointedType} (f : PointedMap X Y)
           (** `{IsTrunc 1 X} `{IsTrunc 1 Y} *)
: GroupHom (group_loopspace X) (group_loopspace Y).
Proof.
  refine (Build_PointedMap _ _ _ _); simpl.
  - intros [x p].
    exists (f x).
    strip_truncations; apply tr.
    exact (ap f p @ point_eq f).
  - apply path_sigma_hprop; simpl.
    apply point_eq.
Defined.

Definition loopspace_functor_group
           {X Y : PointedType} (f : PointedMap X Y)
           (** `{IsTrunc 1 X} `{IsTrunc 1 Y} *)
: loopspace_functor (group_loopspace_functor f)
  o loopspace_group X
  == loopspace_group Y
     o loopspace_functor f.
Proof.
  intros x; simpl.
  apply (equiv_inj (path_sigma_hprop _ _)^-1).
  simpl.
  unfold pr1_path; rewrite !ap_pp.
  rewrite ap_V, !ap_pr1_path_sigma_hprop.
  apply whiskerL, whiskerR.
  transitivity (ap (fun X0 : {x0 : X & merely (x0 = point X)} => f X0.1)
                   (path_sigma_hprop (point X; tr 1) (point X; tr 1) x)).
  - match goal with
        |- ap ?f (ap ?g ?p) = ?z =>
        symmetry; refine (ap_compose g f p)
    end.
  - rewrite ap_compose; apply ap.
    apply ap_pr1_path_sigma_hprop.
Qed.

Definition grouphom_compose {G H K : Group}
           (psi : GroupHom H K) (phi : GroupHom G H)
: GroupHom G K
  := pointedmap_compose psi phi.

Definition group_loopspace_functor_compose
           {X Y Z : PointedType}
           (psi : PointedMap Y Z) (phi : PointedMap X Y)
           (** `{IsTrunc 1 X} `{IsTrunc 1 Y} `{IsTrunc 1 Z} *)
: grouphom_compose (group_loopspace_functor psi)
                   (group_loopspace_functor phi)
  == group_loopspace_functor (pointedmap_compose psi phi).
Proof.
  intros g.
  unfold grouphom_fun, grouphom_compose.
  refine (loopspace_functor_compose _ _ g @ _).
  pose (p := eisretr (loopspace_group X) g).
  change (loopspace_functor (group_loopspace_functor psi)
            (loopspace_functor (group_loopspace_functor phi) g)
          = loopspace_functor (group_loopspace_functor
                                 (pointedmap_compose psi phi)) g).
  rewrite <- p.
  rewrite !loopspace_functor_group.
  apply ap.
  symmetry; apply loopspace_functor_compose.
Qed.

Definition grouphom_idmap (G : Group) : GroupHom G G
  := pointedmap_idmap (B G).

Definition group_loopspace_functor_idmap
           {X : PointedType} (** `{IsTrunc 1 X} *)
: grouphom_idmap (group_loopspace X)
  == group_loopspace_functor (pointedmap_idmap X).
Proof.
  intros g.
  unfold grouphom_fun, grouphom_idmap.
  assert (p := eisretr (loopspace_group X) g).
  rewrite <- p.
  rewrite !loopspace_functor_group.
  rewrite loopspace_functor_idmap.
  simpl. apply ap.
  rewrite concat_p1, concat_1p, ap_idmap.
  reflexivity.
Qed.

Definition group_loopspace_2functor
           {X Y : PointedType} {phi psi : PointedMap X Y}
           (theta : PointedHomotopy phi psi)
            (** `{IsTrunc 1 X}  `{IsTrunc 1 Y} *)
: (group_loopspace_functor phi) == (group_loopspace_functor psi).
Proof.
  intros g.
  assert (p := eisretr (loopspace_group X) g).
  rewrite <- p.
  unfold grouphom_fun.
  rewrite !loopspace_functor_group.
  apply ap.
  apply loopspace_2functor; assumption.
Defined.

(** The following tactic often allows us to "pretend" that phi preserves basepoints strictly. *)
Ltac grouphom_reduce :=
  unfold grouphom_fun; simpl;
  repeat match goal with
           | [ G : Group |- _ ] => destruct G as [G ?]
           | [ X : PointedType |- _ ] => destruct X as [X ?]
           | [ phi : GroupHom ?G ?H |- _ ] => destruct phi as [phi ?]
         end;
  simpl in *; unfold point in *;
  path_induction; simpl;
  try rewrite !concat_p1;
  try rewrite !concat_1p.

Definition compose_grouphom {G H K : Group}
           (psi : GroupHom H K) (phi : GroupHom G H)
: grouphom_compose psi phi == psi o phi.
Proof.
  intros g; grouphom_reduce.
  exact (ap_compose phi psi g).
Defined.

Definition idmap_grouphom (G : Group)
: grouphom_idmap G == idmap.
Proof.
  intros g; grouphom_reduce.
  exact (ap_idmap g).
Defined.  

Definition grouphom_pp {G H} (phi : GroupHom G H) (g1 g2 : G)
: phi (g1 @ g2) = phi g1 @ phi g2.
Proof.
  grouphom_reduce.
  exact (ap_pp phi g1 g2).
Defined.

Definition grouphom_V {G H} (phi : GroupHom G H) (g : G)
: phi g^ = (phi g)^.
Proof.
  grouphom_reduce.
  exact (ap_V phi g).
Defined.

Definition grouphom_1 {G H} (phi : GroupHom G H)
: phi 1 = 1.
Proof.
  grouphom_reduce.
  reflexivity.
Defined.

Definition grouphom_pp_p {G H} (phi : GroupHom G H) (g1 g2 g3 : G)
: grouphom_pp phi (g1 @ g2) g3
  @ whiskerR (grouphom_pp phi g1 g2) (phi g3)
  @ concat_pp_p (phi g1) (phi g2) (phi g3)
  = ap phi (concat_pp_p g1 g2 g3)
    @ grouphom_pp phi g1 (g2 @ g3)
    @ whiskerL (phi g1) (grouphom_pp phi g2 g3).
Proof.
  grouphom_reduce.
  (** The [match]es have gone away, so this would actually be manageable except for the [concat_p1]s and [concat_1p]s.  So in a world where [concat] was strictly unital on *both* sides, we could prove higher coherences just as easily like this. *)
Abort.

(** ** Subgroups *)

Section Subgroups.
  Context `{ua : Univalence}.
  Context (G H : Group) (incl : GroupHom H G) `{IsEmbedding incl}.

  Definition in_coset : G -> G -> Type
    := fun g1 g2 => hfiber incl (g1 @ g2^).

  Global Instance ishprop_in_coset : is_mere_relation G in_coset.
  Proof.
    exact _.
  Defined.

  Global Instance reflexive_coset : Reflexive in_coset.
  Proof.
    intros g.
    exact (1 ; grouphom_1 incl @ (concat_pV g)^).
  Defined.

  Global Instance symmetric_coset : Symmetric in_coset.
  Proof.
    intros g1 g2 [h p].
    exists (h^).
    refine (grouphom_V incl h @ inverse2 p @ inv_pp _ _ @ whiskerR (inv_V _) _).
  Defined.

  Global Instance transitive_coset : Transitive in_coset.
  Proof.
    intros g1 g2 g3 [h1 p1] [h2 p2].
    exists (h1 @ h2).
    refine (grouphom_pp incl h1 h2 @ (p1 @@ p2) @ concat_p_pp _ _ _ @ whiskerR (concat_pV_p _ _) _).
  Defined.

  Definition equiv_coset_subgroup `{IsHSet G} (g : G)
  : { g' : G & in_coset g g'} <~> H.
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - intros [? [h ?]]; exact h.
    - intros h; exists (incl h^ @ g); exists h; simpl.
      abstract (rewrite inv_pp, grouphom_V, inv_V, concat_p_Vp; reflexivity).
    - intros h; reflexivity.
    - intros [g' [h p]].
      refine (path_sigma' _ _ _).
      + rewrite grouphom_V.
        apply moveR_Vp, moveL_pM.
        exact (p^).
      + unfold in_coset, hfiber. rewrite transport_sigma; simpl.
        apply path_sigma_hprop; simpl.
        apply transport_const.
  Qed.

  Definition cosets := quotient in_coset.

  Context `{Finite G} `{Finite H}.

  Global Instance decidable_in_coset (g1 g2 : G)
  : Decidable (in_coset g1 g2).
  Proof.
    by apply decidable_image_finite.
  Defined.
    
  Global Instance finite_cosets : Finite cosets.
  Proof.
    exact _.
  Defined.

  Definition lagrange : fcard G = fcard cosets * fcard H.
  Proof.
    refine (fcard_quotient in_coset @ _ @ finplus_const cosets (fcard H)).
    apply ap, path_arrow; intros z; simpl.
    refine (Trunc_rec _ (center (merely (hfiber (class_of in_coset) z)))).
    intros [g p]; rewrite <- p; exact (fcard_equiv' (equiv_coset_subgroup g)).
  Qed.

End Subgroups.

Section Surjections.

  Context `{fs : Funext}.
  Context {G H : Group} (sur : GroupHom G H) `{IsSurjection sur}.

  (** The real [kernel] should be be another [Group], of course. *)
  Definition kernel_set := hfiber sur 1.

  Definition merely_equiv_fiber_kernel `{IsHSet H} (h : H)
  : merely (hfiber sur h <~> kernel_set).
  Proof.
    assert (x := center (merely (hfiber sur h))).
    strip_truncations; destruct x as [g p]; apply tr.
    refine (equiv_adjointify _ _ _ _).
    - intros [g' p']. exists (g @ g'^).
      refine (grouphom_pp _ _ _ @ (p @@ (grouphom_V _ _ @ inverse2 p')) @ concat_pV _).
    - intros [g' p']. exists (g'^ @ g).
      refine (grouphom_pp _ _ _ @ (grouphom_V _ _ @ inverse2 p' @@ p) @ concat_1p _).
    - intros [g' p']. apply path_sigma_hprop; simpl.
      rewrite inv_pp, concat_p_Vp, inv_V; reflexivity.
    - intros [g' p']. apply path_sigma_hprop; simpl.
      rewrite inv_pp, inv_V, concat_pV_p; reflexivity.
  Qed.

  Context `{Finite G} `{Finite H}.

  Definition fcard_fiber_kernel (h : H)
  : fcard (hfiber sur h) = fcard kernel_set.
  Proof.
    assert (e := merely_equiv_fiber_kernel h).
    strip_truncations.
    exact (fcard_equiv' e).
  Defined.

  Definition fcard_group_surj
  : fcard G = fcard H * fcard kernel_set.
  Proof.
    refine (fcard_domain sur @ _ @ finplus_const H (fcard kernel_set)).
    apply ap, path_arrow; intros h; apply fcard_fiber_kernel.
  Defined.
    
End Surjections.
