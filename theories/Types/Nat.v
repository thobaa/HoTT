(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers *)

Require Import HoTT.Basics.
Require Import Types.Unit Types.Empty Types.Sigma.
Require Import Peano.           (** From modified Coq stdlib *)

Local Open Scope equiv_scope.
Local Open Scope path_scope.


Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.

(** ** Paths *)

Fixpoint code_nat (n m : nat)
  := match n, m with
       | 0, 0 => Unit
       | S n, S m => code_nat n m
       | _ , _ => Empty
     end.

Fixpoint idcode_nat (n : nat) : code_nat n n
  := match n with
       | 0 => tt
       | S n => idcode_nat n
     end.

Definition path_nat (n m : nat)
: code_nat n m <~> (n = m).
Proof.
  refine (equiv_adjointify _ _ _ _).
  - revert m; induction n as [|n IHn]; induction m as [|m IHm].
    + intros; exact idpath.
    + intros e; elim e.
    + intros e; elim e.
    + intros c; exact (ap S (IHn m c)).
  - intros p.
    exact (transport (fun m' => code_nat n m') p (idcode_nat n)).
  - intros p. destruct p; simpl.
    induction n as [|n IHn]; simpl.
    + reflexivity.
    + exact (ap (ap S) IHn).
  - revert m; induction n as [|n IHn]; induction m as [|m IHm];
      simpl; intros c.
    + apply path_unit.
    + elim c.
    + elim c.
    + refine ((transport_compose _ S _ _)^ @ IHn m c).
Defined.

Definition nat_S_inj {n m : nat}
: (S n = S m) -> (n = m)
  := path_nat n m o (path_nat (S n) (S m))^-1.

Global Instance hset_nat : IsHSet nat.
Proof.
  intros n m.
  refine (trunc_equiv' (n := -1) (code_nat n m) (path_nat n m)).
  revert m; induction n as [|n IHn]; induction m as [|m IHm];
    exact _.
Defined.  
  
Global Instance decidablepaths_nat : DecidablePaths nat.
Proof.
  intros n; induction n as [|n IHn]; intros m; induction m as [|m IHm].
  - exact (inl idpath).
  - exact (inr (path_nat _ _)^-1).
  - exact (inr (path_nat _ _)^-1).
  - destruct (IHn m) as [p|np].
    + exact (inl (ap S p)).
    + apply inr; intros p; apply np.
      exact (nat_S_inj p).
Defined.

(** ** Arithmetic *)

Lemma nat_plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; apply ap; assumption.
Qed.

Lemma nat_plus_n_Sm : forall n m:nat, (n + m).+1 = n + m.+1.
Proof.
  intros n m; induction n; simpl.
  - reflexivity.
  - apply ap; assumption.
Qed.

Definition nat_plus_comm (n m : nat) : n + m = m + n.
Proof.
  revert m; induction n as [|n IH]; intros m; simpl.
  - refine (nat_plus_n_O m).
  - transitivity (m + n).+1.
    + apply ap, IH.
    + apply nat_plus_n_Sm.
Qed.

Definition nat_plus_assoc (a b c : nat)
: a + (b + c) = (a + b) + c.
Proof.
  induction a as [|a IH].
  - reflexivity.
  - simpl. apply ap, IH.
Defined.

Definition nat_plus_cancel (a b c : nat)
: a + b = a + c -> b = c.
Proof.
  induction a as [|a IH].
  - exact idmap.
  - intros p; apply IH; exact (nat_S_inj p).
Defined.

Definition nat_distrib (a b c : nat)
: a * (b + c) = a * b + a * c.
Proof.
  induction a as [|a IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    rewrite !nat_plus_assoc.
    apply (ap (fun x => x + a*c)).
    rewrite <- !nat_plus_assoc.
    apply (ap (fun x => b + x)).
    apply nat_plus_comm.
Defined.

Definition lt : nat -> nat -> Type
  := fun n m => { p : nat & p.+1 + n = m }.

Notation "n < m" := (lt n m).

Global Instance ishprop_le n m : IsHProp (n < m).
Proof.
  apply hprop_allpath. intros [p p'] [q q'].
  apply path_sigma_hprop.
  refine (nat_plus_cancel n p q _).
  refine (nat_plus_comm _ _ @ _ @ nat_plus_comm _ _).
  exact (nat_S_inj (p' @ q'^)).
Defined.

Definition nat_trichotomy n m
: (n < m) + (n = m) + (m < n).
Proof.
  revert m; induction n as [|n IHn].
  { destruct m as [|m].
    + apply inl, inr; reflexivity.
    + apply inl, inl.
      exists m. symmetry; apply nat_plus_n_O. }
  { intros m; induction m as [|m IHm].
    + apply inr.
      exists n. symmetry; apply nat_plus_n_O.
    + destruct IHm as [[p|p]|p].
      * apply inl, inl.
        exists (p.1.+1); simpl.
        apply ap, p.2.
      * apply inl, inl.
        exists O.
        apply ap, p.
      * destruct (IHn m) as [[q|q]|q].
        - apply inl, inl.
          exists q.1.
          refine (nat_plus_comm _ _ @ _); simpl.
          apply ap. refine (nat_plus_comm _ _ @ q.2).
        - apply inl, inr, ap, q.
        - apply inr.
          exists q.1.
          refine (nat_plus_comm _ _ @ _); simpl.
          apply ap. refine (nat_plus_comm _ _ @ q.2). }
Defined.

Definition nat_mult_cancel (a b c : nat)
: (a.+1 * b = a.+1 * c) -> (b = c).
Proof.
  intros p.
  destruct (nat_trichotomy b c) as [[[d q]|q]|[d q]];
    [ apply Empty_rec | exact q | apply Empty_rec ].
  - pose (q' := ap (mult a.+1) q).
    rewrite nat_distrib in q'.
    pose (q'' := nat_plus_comm _ _ @ q' @ p^ @ nat_plus_n_O _).
    apply nat_plus_cancel in q''. simpl in q''.
    exact ((path_nat _ _)^-1 q'').
  - pose (q' := ap (mult a.+1) q).
    rewrite nat_distrib in q'.
    pose (q'' := nat_plus_comm _ _ @ q' @ p @ nat_plus_n_O _).
    apply nat_plus_cancel in q''. simpl in q''.
    exact ((path_nat _ _)^-1 q'').
Defined.

(** ** Exponentiation *)

Fixpoint nat_exp (n m : nat) : nat
  := match m with
       | 0 => 1
       | S m => nat_exp n m * n
     end.

Notation "x ^ y" := (nat_exp x y) : nat_scope.

(** ** Factorials *)

Fixpoint factorial (n : nat) : nat
  := match n with
       | 0 => 1
       | S n => S n * factorial n
     end.