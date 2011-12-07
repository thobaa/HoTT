Add LoadPath "..".
Require Import Homotopy Pi0.

Fixpoint pi (n : nat) : forall (X : Type) (x0 : X), Type :=
  match n with
    | 0 => fun X _ => pi0 X
    | S n' => fun _ x0 => pi n' (x0 == x0) (idpath x0)
  end.

Definition pi1 := pi 1.

Definition pi2 := pi 2.

Theorem pi_is_set (n : nat) (X : Type) (x0 : X) : is_set (pi n X x0).
Proof.
  revert X x0.
  induction n.
  intros.
  apply pi0_is_set.
  intros.
  apply IHn.
Defined.
