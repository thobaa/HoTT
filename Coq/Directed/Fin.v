Add LoadPath "..".
Require Import Homotopy.

(* In this file we define a basic "finite set" datatype.  There is
   also something like this in the Coq 8.4 standard library.

   The names below are largely taken from Agda's Data.Fin.  Those that
   aren't, are fairly ad hoc.
   *)

Inductive fin : nat -> Type :=
| fzero : forall {n}, fin (S n)
| fsucc : forall {n}, fin n -> fin (S n).

Fixpoint from_nat n : fin (S n) :=
  match n with
    | 0 => fzero
    | S n' => fsucc (from_nat n')
  end.

Fixpoint to_nat {n} (k : fin n) : nat :=
  match k in fin n with
    | fzero _ => 0
    | fsucc _ k' => S (to_nat k')
  end.

(*
Definition fin' {n} (k : fin n) : Type
  := fin (to_nat k).
*)

Inductive fin' : forall {n}, fin n -> Type :=
| fzero' : forall {n} {k : fin n}, fin' (fsucc k)
| fsucc' : forall {n} {k : fin n} (i : fin' k), fin' (fsucc k).

Fixpoint from_fin {n} (k : fin n) : fin' (fsucc k) :=
  match k return (fin' (fsucc k)) with
    | fzero _ => fzero'
    | fsucc n' k' => fsucc' (from_fin k')
  end.

Definition fin0_rect {A:Type} (k : fin 0) : A :=
  match k in fin n return
    (match n with 0 => A | S _ => unit end) with
      | fzero _ => tt
      | fsucc _ _ => tt
    end.

Definition fin'0_rect {A:Type} {n} (k : fin' (@fzero n)) : A :=
  match k in fin' i return
    (match i with fzero _ => A | fsucc _ _ => unit end) with
      | fzero' _ _ => tt
      | fsucc' _ _ _ => tt
    end.

Definition fin1_rect {P : fin 1 -> Type} (p1 : P fzero) (k : fin 1) : P k :=
  match k in fin n return
    (match n return (fin n -> Type) with
       | 0 => fun _ => unit
       | 1 => P
       | S (S n') => fun _ => unit
     end) k with
    | fzero n' =>
      match n' return
        (match n' return (fin (S n') -> Type) with
           | 0 => P
           | S _ => fun _ => unit
         end) fzero with
        | 0 => p1
        | S _ => tt
      end
    | fsucc n' k' =>
      match n' return
        (forall k' : fin n',
          (match n' return (fin (S n') -> Type) with
             | 0 => P
             | S _ => fun _ => unit
           end) (fsucc k')) with
        | 0 => fun k' => fin0_rect k'
        | S n'' => fun _ => tt
      end k'
  end.

Fixpoint inject1 {n} (k : fin n) : fin (S n) :=
  match k in fin n with
    | fzero n' => fzero
    | fsucc n' k' => fsucc (inject1 k')
  end.

Fixpoint injectplus {n} m (k : fin n) : fin (n + m) :=
  match k in fin n return fin (n + m) with
    | fzero n' => @fzero (n' + m)
    | fsucc n' k' => @fsucc _ (injectplus m k')
  end.

Fixpoint injectplus2 {n} m (k : fin n) : fin (m + n) :=
  match m return fin (m + n) with
    | 0 => k
    | S m' => inject1 (injectplus2 m' k)
  end.

Fixpoint injectplus2S {n} m (k : fin (S n)) : fin (S (m + n)) :=
  match m return fin (S (m + n)) with
    | 0 => k
    | S m' => inject1 (injectplus2S m' k)
  end.

Definition injectplus2S_fzero {n} m :
  injectplus2S m (@fzero n) == fzero.
Proof.
  induction m; auto.
  simpl. path_via (inject1 (@fzero (m + n))).
Defined.

Fixpoint fplus2 {n} m (k : fin n) : fin (m + n) :=
  match m return fin (m + n) with
    | 0 => k
    | S m' => fsucc (fplus2 m' k)
  end.

Fixpoint fplus2S {n} m (k : fin (S n)) : fin (S (m + n)) :=
  match m return fin (S (m + n)) with
    | 0 => k
    | S m' => fsucc (fplus2S m' k)
  end.

(* These are for when the context determines the output type. *)
(*
Fixpoint inject {n} {i : fin n} (k : fin' i) : fin n :=
  match i in fin n return fin' i -> fin n with
    | fzero _ => fin0_rect
    | fsucc n' i' => fun k' =>
      match k' in fin Si' return
        ((fin (pred Si') -> fin n') -> fin (S n')) with
        | fzero Si' => fun _ => fzero
        | fsucc Si' k'' => fun next => fsucc (next k'')
      end (@inject n' i')
  end k.
*)

Fixpoint inject {n} {k : fin n} (i : fin' k) : fin n :=
  match i in @fin' n k return fin n with
    | fzero' n' k' => fzero
    | fsucc' n' k' i' => fsucc (inject i')
  end.

Fixpoint finject {n} {k : fin n} (i : fin' k) : fin (to_nat k) :=
  match i in @fin' n k return fin (to_nat k) with
    | fzero' _ _ => fzero
    | fsucc' n' k' i' => fsucc (finject i')
  end.

Definition finject_from_fin n (k : fin n) :
  finject (from_fin k) == from_nat (to_nat k).
Proof.
  induction k as [n' | n' k']; auto.
  simpl. apply map, IHk'.
Defined.

(*
Fixpoint inject_bang' {Sn} {i : fin Sn} (k : fin' i) : fin (pred Sn) :=
  match i in fin Sn return fin' i -> fin (pred Sn) with
    | fzero _ => fin0_rect
    | fsucc n i' => fun k' =>
      match k' in fin Si' return
        ((fin (pred Si') -> fin (pred n)) -> fin n) with
        | fzero Si' => fun _ =>
          match i' in fin n with
            | fzero _ => fzero
            | fsucc _ _ => fzero
          end
        | fsucc Si' k'' =>
          match i' in fin n with
            | fzero _ => fun next => fsucc (next k'')
            | fsucc _ _ => fun next => fsucc (next k'')
          end
      end (@inject_bang' n i')
  end k.
*)

Fixpoint inject_bang' {Sn} {i : fin Sn} (k : fin' i) : fin (pred Sn) :=
  match k in @fin' Sn i return fin (pred Sn) with
    | fzero' n' k' =>
      match k' in fin n' return fin n' with
        | fzero _ => fzero
        | fsucc _ _ => fzero
      end
    | fsucc' n' k' i' =>
      match k' in fin n' return fin (pred n') -> fin n' with
        | fzero _ => fsucc
        | fsucc _ _ => fsucc
      end (inject_bang' i')
  end.

Definition inject_bang {n} {i : fin (S n)} (k : fin' i) : fin n :=
  inject_bang' k.

Definition inject_bang2 {n} {i : fin n} (k : fin' (fsucc i)) : fin n :=
  inject_bang' k.

Definition inject_bang_fzero' Sn (i : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit:Type
    | S n => fun i => inject_bang' (@fzero' _ i) == @fzero n
  end i.
Proof.
  induction i as [n | n i']; auto.
Defined.

Definition inject_bang_fzero n (i : fin (S n)) :
  inject_bang' (@fzero' _ i) == @fzero n
  := inject_bang_fzero' (S n) i.

Definition inject_bang_from_fin n (k : fin n) :
  inject_bang' (from_fin k) == k.
Proof.
  induction k as [n' | n' k']; auto.
  simpl. apply map, IHk'.
Defined.

(* For [k : fin n], [cofin' k] is the type of naturals less than [n-k]. *)
Inductive cofin' : forall {n}, fin n -> Type :=
| fin_cofin : forall {n}, fin (S n) -> cofin' (@fzero n)
| cofinject1 : forall {n} {k : fin n}, cofin' k -> cofin' (fsucc k).

Fixpoint cofzero {n} (k : fin n) : cofin' k :=
  match k return cofin' k with
    | fzero _ => fin_cofin fzero
    | fsucc n' k' => cofinject1 (cofzero k')
  end.

Fixpoint cofmax {n} (k : fin n) : cofin' k :=
  match k return cofin' k with
    | fzero n' => fin_cofin (from_nat n')
    | fsucc n' k' => cofinject1 (cofmax k')
  end.

Fixpoint coinject {n} {k : fin n} (c : cofin' k) : fin n :=
  match c in @cofin' n k return fin n with
    | fin_cofin n' k' => k'
    | cofinject1 n k i => inject1 (coinject i)
  end.

Definition coinject_cofzero' Sn (k : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit:Type
    | S n => fun k => coinject (cofzero k) == @fzero n
  end k.
Proof.
  induction k as [n | n k']; auto.
  simpl.
  destruct n as [|n'].
  apply fin0_rect, k'.
  path_change (inject1 (@fzero n')).
Defined.

Definition coinject_cofzero n (k : fin (S n)) :
  coinject (cofzero k) == @fzero n
  := coinject_cofzero' (S n) k.

Fixpoint coinject_shifted {n} {k : fin n} (c : cofin' k) : fin n :=
  match c in @cofin' n k return fin n with
    | fin_cofin n' k' => k'
    | cofinject1 n k i => fsucc (coinject_shifted i)
  end.

Definition coinject_shifted_cofzero' Sn (k : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit:Type
    | S n => fun k => coinject_shifted (cofzero k) == k
  end k.
Proof.
  induction k as [n | n k']; auto.
  simpl.
  destruct n as [|n'].
  apply fin0_rect, k'.
  apply map, IHk'.
Defined.

Definition coinject_shifted_cofzero n (k : fin (S n)) :
  coinject_shifted (cofzero k) == k
  := coinject_shifted_cofzero' (S n) k.

Definition coinject_shifted_cofmax' Sn (k : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit:Type
    | S n => fun k => coinject_shifted (cofmax k) == from_nat n
  end k.
Proof.
  induction k as [n | n k']; auto.
  destruct n as [|n'].
  apply fin0_rect, k'.
  simpl. apply map, IHk'.
Defined.

Definition coinject_shifted_cofmax n (k : fin (S n)) :
  coinject_shifted (cofmax k) == from_nat n
  := coinject_shifted_cofmax' (S n) k.

(* Unlike [inject], the type of [coinject] is already best possible,
   so there is no need for a [coinject_bang]. *)

Fixpoint fin_flip {n} (k : fin n) : fin n :=
  match k in (fin n) with
    | fzero n' => from_nat n'
    | fsucc n' k' => inject1 (fin_flip k')
  end.

(* This is the composite [to_nat o fin_flip], written out separately
   so that it computes. *)

Fixpoint co_to_nat {n} (k : fin n) : nat :=
  match k with
    | fzero n' => n'
    | fsucc n' k' => co_to_nat k'
  end.

Fixpoint cofinject {n} {k : fin n} (c : cofin' k) : fin (S (co_to_nat k)) :=
  match c in @cofin' n k return fin (S (co_to_nat k)) with
    | fin_cofin n' k' => k'
    | cofinject1 n' k' i' => cofinject i'
  end.

Definition cofinject_cofzero' Sn (k : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit:Type
    | S n => fun k => cofinject (cofzero k) == @fzero (co_to_nat k)
  end k.
Proof.
  induction k as [n | n k']; auto.
  simpl.
  destruct n as [|n'].
  apply fin0_rect, k'.
  auto.
Defined.

Definition cofinject_cofzero n (k : fin (S n)) :
  cofinject (cofzero k) == @fzero (co_to_nat k)
  := cofinject_cofzero' (S n) k.

Definition cofinject_cofmax n (k : fin n) :
  cofinject (cofmax k) == from_nat (co_to_nat k).
Proof.
  induction k as [n' | n' k']; auto.
Defined.

Fixpoint cofsucc {n} {k : fin n} (c : cofin' k) : cofin' (inject1 k) :=
  match c in @cofin' n k return cofin' (inject1 k) with
    | fin_cofin n' k' => fin_cofin (fsucc k')
    | cofinject1 n' k' i' => cofinject1 (cofsucc i')
  end.

Fixpoint fplus2co {n} {k : fin n} (i : fin (S (co_to_nat k))) : fin n :=
  match k in fin n return fin (S (co_to_nat k)) -> fin n with
  | fzero n' => fun i => i
  | fsucc n' k' => fun i => fsucc (@fplus2co n' k' i)
  end i.

(* We prove a few lemmas about the behavior of these functions. *)

Definition flip_inject1 n (k : fin n) :
  fsucc (fin_flip k) == fin_flip (inject1 k).
Proof.
  induction k.
  auto.
  path_change (fin_flip (fsucc (inject1 k))).
  path_change (fsucc (inject1 (fin_flip k))).
  path_change (inject1 (fsucc (fin_flip k))).
  path_via (inject1 (fin_flip (inject1 k))).
Defined.

Definition flip_top n : fin_flip (from_nat n) == fzero.
Proof.
  induction n. auto.
  path_change (fin_flip (fsucc (from_nat n))).
  path_change (inject1 (fin_flip (from_nat n))).
  path_via (inject1 (@fzero n)).
Defined.

Definition flip_flip n (k : fin n) : fin_flip (fin_flip k) == k.
Proof.
  induction k. apply flip_top.
  simpl.
  path_via (fsucc (fin_flip (fin_flip k))).
  apply opposite, flip_inject1.
Defined.

Definition to_nat_top n : to_nat (from_nat n) == n.
Proof.
  induction n. auto.
  simpl. apply map, IHn.
Defined.

Definition to_nat_inject1 n (k : fin n) :
  to_nat (inject1 k) == to_nat k.
Proof.
  induction k. auto.
  simpl. apply map, IHk.
Defined.

Definition to_nat_injectplus n m (k : fin n) :
  to_nat (injectplus m k) == to_nat k.
Proof.
  induction k as [n' | n' k']; auto.
  simpl; apply map, IHk'.
Defined.

Definition co_to_nat_injectplus m n :
  co_to_nat (injectplus m (from_nat n)) == m.
Proof.
  induction n; auto.
Defined.

Definition to_nat_from_nat n :
  to_nat (from_nat n) == n.
Proof.
  induction n; simpl; try apply map; auto.
Defined.

Definition fplus2co_fzero n :
  fplus2co (@fzero (co_to_nat (from_nat n))) == from_nat n.
Proof.
  induction n; [ auto | simpl; apply map; assumption ].
Defined.

Definition fplus2co_from_nat' Sn (k : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit
    | S n => fun k => fplus2co (from_nat (co_to_nat k)) == from_nat n
  end k.
Proof.
  induction k as [n|n k'];
    [ auto | destruct n as [|n'];
      [ exact (fin0_rect k') | simpl; apply map; assumption ] ].
Defined.

Definition fplus2co_from_nat {n} {k : fin (S n)}:
  fplus2co (from_nat (co_to_nat k)) == from_nat n
  := fplus2co_from_nat' (S n) k.
