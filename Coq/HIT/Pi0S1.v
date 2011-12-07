Add LoadPath "..".
Require Import Homotopy Circle Pi0.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

Theorem pi0_circle_iscontr : is_contr (pi0 circle).
Proof.
  exists (cpnt base).
  apply pi0_rect.
  apply circle_rect with (pt := map cpnt (idpath base)).
  path_via (transport (P := fun x => x == cpnt base) (map cpnt loop) (map cpnt (idpath base))).
  apply map_trans with (P := fun x => x == cpnt base).
  path_via (!map cpnt loop @ map cpnt (idpath base)).
  apply trans_is_concat_opp.
  apply pi0_is_set.
  intros.
  apply contr_path.
  apply pi0_is_set.
Defined.
