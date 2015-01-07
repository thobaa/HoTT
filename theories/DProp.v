(* -*- mode: coq; mode: visual-line -*-  *)

(** * Decidable hprops *)

Require Import HoTT.Basics HoTT.Types.
Require Import TruncType HProp UnivalenceImpliesFunext.
Require Import hit.Truncations.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** ** Definitions *)

Record DProp :=
  { dprop_hprop : hProp ;
    dec_dprop : Decidable dprop_hprop
  }.

Coercion dprop_hprop : DProp >-> hProp.
Global Existing Instance dec_dprop.

Definition True : DProp
  := Build_DProp Unit_hp (inl tt).

Definition False : DProp
  := Build_DProp False_hp (inr idmap).

Definition dprop_to_bool (P : DProp) : Bool
  := if dec P then true else false.

Coercion dprop_to_bool : DProp >-> Bool.

(** ** Truncation *)

Definition issig_dprop
  : { X : hProp & Decidable X } <~> DProp.
Proof.
  issig Build_DProp dprop_hprop dec_dprop.
Defined.

Global Instance ishset_dprop `{Univalence} : IsHSet DProp.
Proof.
  refine (trunc_equiv' _ issig_dprop).
Defined.

(** ** Operations *)

(** We define the logical operations on decidable hprops to be the operations on ordinary hprops, with decidability carrying over. *)

Definition dand (b1 b2 : DProp) : DProp.
Proof.
  refine (Build_DProp (BuildhProp (b1 * b2)) _).
  1:exact _.
  destruct (dec b1) as [x1|y1]; destruct (dec b2) as [x2|y2].
  - exact (inl (x1,x2)).
  - apply inr; intros [_ x2]; exact (y2 x2).
  - apply inr; intros [x1 _]; exact (y1 x1).
  - apply inr; intros [x1 _]; exact (y1 x1).
Defined.

Definition dor (b1 b2 : DProp) : DProp.
Proof.
  refine (Build_DProp (BuildhProp (hor b1 b2)) _).
  1:exact _.
  destruct (dec b1) as [x1|y1].
  - exact (inl (tr (inl x1))).
  - destruct (dec b2) as [x2|y2].
    + exact (inl (tr (inr x2))).
    + apply inr; intros z; strip_truncations.
      destruct z as [x1|x2].
      * exact (y1 x1).
      * exact (y2 x2).
Defined.

Definition dneg `{Funext} (b : DProp) : DProp.
Proof.
  refine (Build_DProp (BuildhProp (~b)) _).
  1:exact _.
  destruct (dec b) as [x|y].
  - apply inr; intros nx; exact (nx x).
  - exact (inl y).
Defined.

Definition dimpl `{Funext} (b1 b2 : DProp) : DProp.
Proof.
  refine (Build_DProp (BuildhProp (b1 -> b2)) _).
  1:exact _.
  destruct (dec b2) as [x2|y2].
  - exact (inl (fun _ => x2)).
  - destruct (dec b1) as [x1|y1].
    + apply inr; intros f.
      exact (y2 (f x1)).
    + apply inl; intros x1.
      elim (y1 x1).
Defined.

Infix "&&" := dand : dprop_scope.
Infix "||" := dor : dprop_scope.
Infix "->" := dimpl : dprop_scope.
Notation "!! P" := (dneg P) (at level 75, right associativity)
                   : dprop_scope.

Delimit Scope dprop_scope with dprop.
Local Open Scope dprop_scope.

(** ** Computation *)

(** In order to be able to "compute" with [DProp]s like booleans, we define a couple of typeclasses. *)

Class IsTrue (P : DProp) :=
  dprop_istrue : P.

Class IsFalse (P : DProp) :=
  dprop_isfalse : ~ P.

Global Instance true_istrue : IsTrue True := tt.

Global Instance false_isfalse : IsFalse False := idmap.

Global Instance dand_true_true {P Q} `{IsTrue P} `{IsTrue Q}
: IsTrue (P && Q).
Proof.
  exact (dprop_istrue, dprop_istrue).
Defined.

Global Instance dand_false_l {P Q} `{IsFalse P}
: IsFalse (P && Q).
Proof.
  intros [p q].
  exact (dprop_isfalse p).
Defined.

Global Instance dand_false_r {P Q} `{IsFalse Q}
: IsFalse (P && Q).
Proof.
  intros [p q].
  exact (dprop_isfalse q).
Defined.

Global Instance dor_true_l {P Q} `{IsTrue P}
: IsTrue (P || Q).
Proof.
  exact (tr (inl Q dprop_istrue)).
Defined.

Global Instance dor_true_r {P Q} `{IsTrue Q}
: IsTrue (P || Q).
Proof.
  exact (tr (inr P dprop_istrue)).
Defined.

Global Instance dor_false_false {P Q} `{IsFalse P} `{IsFalse Q}
: IsFalse (P || Q).
Proof.
  intros pq. strip_truncations. destruct pq as [p|q].
  - exact (dprop_isfalse p).
  - exact (dprop_isfalse q).
Defined.

Global Instance dneg_true `{Funext} {P} `{IsTrue P}
: IsFalse (!! P).
Proof.
  intros np; exact (np dprop_istrue).
Defined.

Global Instance dneg_false `{Funext} {P} `{IsFalse P}
: IsTrue (!! P).
Proof.
  exact dprop_isfalse.
Defined.

Global Instance dimpl_true_r `{Funext} {P Q} `{IsTrue Q}
: IsTrue (P -> Q).
Proof.
  intros p. exact dprop_istrue.
Defined.

Global Instance dimpl_false_l `{Funext} {P Q} `{IsFalse P}
: IsTrue (P -> Q).
Proof.
  intros p. elim (dprop_isfalse p).
Defined.

Global Instance dimpl_true_false `{Funext} {P Q} `{IsTrue P} `{IsFalse Q}
: IsFalse (P -> Q).
Proof.
  intros f. exact (dprop_isfalse (f dprop_istrue)).
Defined.
