Add LoadPath "..".
Require Import Homotopy.

(** The natural numbers are a set. *)

Theorem nat_decidable : decidable_paths nat.
Proof.
  intros n; induction n.
  intro m; induction m.
  left; auto.
  right. intro H.
  exact (transport (P := fun n => match n with 0 => unit | S _ => Empty_set end) H tt).
  intro m; induction m.
  right. intro H.
  exact (transport (P := fun n => match n with 0 => Empty_set | S _ => unit end) H tt).
  destruct (IHn m) as [p | e].
  left; apply map; assumption.
  right. intro H. apply e.
  exact (transport (P := fun k => n == match k with 0 => n | S l => l end) H (idpath n)).
Defined.

Theorem nat_is_set : is_set nat.
Proof.
  apply decidable_isset.
  apply nat_decidable.
Defined.
