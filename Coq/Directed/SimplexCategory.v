Add LoadPath "..".
Require Import Homotopy Nat.
Require Import Fin.

(* Here we define the simplicial operators.  The type [sop n m] is the
   type of simplicial operators from $[n]$ to $[m]$ in $\Delta$, which
   is of course from $[m]$ to $[n]$ in $\Delta^{\mathrm{op}}$.  For
   our purposes, it seems to be most convenient to define $[n]$ to be
   an $(n+2)$-element total order with distinct endpoints, and take
   $\Delta^{\mathrm{op}}$ to consist of order- and endpoint-preserving
   maps.  *)

Inductive sop : nat -> nat -> Type :=

(* If $m=0$, there is a unique such map. *)

| sop_to0 : forall {n}, sop n 0

(* Otherwise, consider what happens to the rightmost non-basepoint
   element in $[m+1]$.  The first possibility is that it goes to the
   right-hand basepoint in $[n]$.  In this case, what is left of the
   domain is $[m]$, and the codomain is unchanged. *)

| sop_right : forall {n m}, sop n m -> sop n (S m)

(* The other option is that nothing in $[m+1]$ goes to the right-hand
   basepoint in the codomain.  In this case, the options depend on
   whether the codomain is $[0]$ or a successor.  If it is $[0]$, then
   there is exactly one possibility: everything has to go to the
   left-hand basepoint. *)

| sop_left0 : forall {m}, sop 0 (S m)

(* If the codomain is $[n+1]$, on the other hand, then knowing that
   nothing goes to its right-hand basepoint just means that we reduce
   the codomain to $[n]$.  Note, though, that the right-hand basepoint
   in $[n]$ corresponds to a *non-basepoint element* of $[n+1]$. *)

| sop_left : forall {n m}, sop n (S m) -> sop (S n) (S m).

(* The only operator landing in 0 is [sop_to0]. *)

Definition sop_to0_uniq {n} (d : sop n 0) : sop_to0 == d.
Proof.
  set (m := 0) in *.
  set (p := idpath m : m == 0).
  change (sop_to0 == transport p d).
  clearbody p.
  clearbody m.
  destruct d; try
    exact (False_rect _ (transport (P := fun n => match n with 0 => False | S _ => unit end) p tt)).
  path_via (transport (idpath 0) (@sop_to0 n)).
  apply happly, map, set_path2, nat_is_set.
Defined.

(* The identity *)

Fixpoint id_sop n : sop n n :=
  match n with
    | 0 => sop_to0
    | S n' => sop_left (sop_right (id_sop n'))
  end.

(* Next we do vertices.  An $n$-simplex has $n+1$ vertices, so the
   argument of [vertex] is of type [fin (S n)].  Vertices are
   traditionally numbered so that they increase in the pointwise
   ordering with increasing [k]. *)

Fixpoint vertex' {Sn} (k : fin Sn) :
  match Sn with 0 => unit:Type | S n => sop 0 n end
  :=
  match k in fin Sn with
    | fzero n =>
      match n return sop 0 n with
        | 0 => sop_to0
        | S n' => sop_left0
      end
    | fsucc n k =>
      match k in fin n return
        (match n with 0 => unit:Type | S n' => sop 0 n' end -> sop 0 n) with
        | fzero n' => fun v => sop_right v
        | fsucc n' k' => fun v => sop_right v
      end (vertex' k)
  end.

Definition vertex {n} (k : fin (S n)) : sop 0 n := vertex' k.

(* This tactic evaluates [vertex] by one step.  You may need to
   preceed it by a [destruct] on a [nat] or a [fin], since [vertex']
   contains nested [match]es. *)

Ltac do_vertex :=
  unfold vertex;
  match goal with
    | |- context cxt [ vertex' (@fzero 0) ] =>
      let next := context cxt [ (@sop_to0 0) ] in
        change next
    | |- context cxt [ vertex' (@fzero (S ?n)) ] =>
      let next := context cxt [ (@sop_left0 n) ] in
        change next
    | |- context cxt [ vertex' (fsucc ?k) ] =>
      let next := context cxt [ sop_right (vertex' k) ] in
        change next
  end; auto.

(* Vertex composed with [inject1]. *)

Definition vertex_inject1 {Sn} (k : fin Sn) :
  vertex' (inject1 k) ==
  match k in fin Sn return sop 0 Sn with
    | fzero n => sop_left0
    | fsucc n k' => sop_right (vertex' (inject1 k'))
  end.
Proof.
  induction k. auto.
  path_change (vertex' (fsucc (inject1 k))).
  destruct k.
  do_vertex.
  do_vertex.
Defined.

(* The next vertex *)

Definition vertex_fsucc' {Sn} (k : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit:Type
    | S n => fun k => vertex' (fsucc k) == sop_right (vertex' k)
  end k.
Proof.
  induction k.
  auto.
  do_vertex.
Defined.

Definition vertex_fsucc {n} (k : fin (S n)) :
  vertex (fsucc k) == sop_right (vertex k)
  := vertex_fsucc' k.

(* Now we define the (co)face simplicial operators.  They are
   traditionally numbered so that the [k]th face is the one which
   omits vertex [k].

   The following auxiliary function can be defined with tactics...
   *)

Definition face'alt {SSn} (k : fin SSn) :
  match SSn with 0 => unit:Type | 1 => unit | S (S n) =>
    sop n (S n)
  end.
Proof.
  induction k as [Sn|Sn k'].
  destruct Sn as [|n].
  exact tt.
  exact (sop_right (id_sop n)).
  destruct Sn as [|n].
  exact tt.
  destruct n as [|n'].
  exact sop_left0.
  exact (sop_left (sop_right IHk')).
Defined.

(* ... or as an explicit term using LOTS of match-within-return
   annotations. *)

Fixpoint face' {SSn} (k : fin SSn) :
  match SSn with 0 => unit:Type | 1 => unit | S (S n) =>
    sop n (S n)
  end
  :=
  match k in fin SSn with
    (* In the 0th face, the last element is [top]. *)
    | fzero Sn =>
      match Sn return (match Sn with
                         | 0 => unit:Type
                         | S n => sop n (S n)
                       end) with
        | 0 => tt
        | S n => sop_right (id_sop n)
      end
    (* In the (k+1)st face... *)
    | fsucc Sn k' =>
      match Sn return
        ((match Sn with
            | 0 => unit:Type
            | 1 => unit:Type
            | S (S n') => sop n' (S n')
          end)
         -> (match Sn with
               | 0 => unit:Type
               | S n => sop n (S n)
             end))
        with
        | 0 => fun _ => tt
        | S n => fun next =>
          match n return
            ((match n with
                | 0 => unit:Type
                | S n' => sop n' (S n')
              end) -> (sop n (S n)))
            with
            (* ...if n=0, we have the first vertex of a 1-simplex *)
            | 0 => fun _ => sop_left0
            (* ...otherwise, we copy the last element and recurse *)
            | S n' => fun next => sop_left (sop_right next)
          end next
      end (face' k')
  end.

(* The two are easily seen to be the same.  We'll use the explicit
   version. *)

Theorem face'_is_face'alt SSn (k : fin SSn) : face' k == face'alt k.
Proof.
  induction k as [Sn|Sn k]; auto.
  destruct Sn as [|n]; auto.
  destruct n as [|n']; auto.
  simpl; repeat apply map; auto.
Defined.

(* And now the actual operation. *)

Definition face {n} (k : fin (S (S n))) : sop n (S n) := face' k.

(* A tactic to evaluate [face] by one step.  As before, you may need
   to preceed it by a [destruct] on a [nat] or a [fin], since [face']
   contains nested [match]es. *)

Ltac do_face :=
  unfold face;
  match goal with
    | |- context cxt [ @face' (S (S ?n)) (@fzero _) ] =>
      let next := context cxt [ sop_right (id_sop n) ] in
        change next
    | |- context cxt [ @face' (S (S 0)) (fsucc ?k) ] =>
      let next := context cxt [ (@sop_left0 0) ] in
        change next
    | |- context cxt [ @face' (S (S ?n)) (fsucc ?k) ] =>
      let next := context cxt [ sop_left (sop_right (face' k)) ] in
        change next
  end.

(* The 0th face of the 1-simplex is the 1st vertex. *)

Lemma face0_1simplex_vertex1 :
  face (@fzero 1) == vertex (fsucc (@fzero 0)).
Proof.
  do_vertex.
Defined.

(* The 1st face of the 1-simplex is the 0th vertex *)

Lemma face1_1simplex_vertex0 :
  face (fsucc (@fzero 0)) == vertex (@fzero 1).
Proof.
  do_face. do_vertex.
Defined.

(* The following auxiliary simplicial operator collapses everything in
   [m] to the left-hand basepoint of [n]. *)

Fixpoint sop_allleft' n m : sop n (S m) :=
  match n return sop n (S m) with
    | 0 => sop_left0
    | S n' => sop_left (sop_allleft' n' m)
  end.

Definition sop_allleft n m : sop n m :=
  match m return sop n m with
    | 0 => sop_to0
    | S m' => sop_allleft' n m'
  end.

(* This auxiliary 'operatal' combines [sop_to0] with [sop_left]. *)

Definition sop_leftany {n m} : sop n m -> sop (S n) m :=
  match m with
    | 0 => fun _ => sop_to0
    | S m' => sop_left
  end.

(* Similarly, this 'operatal' adds [k] elements that go to the
   right-hand basepoint.  *)

Fixpoint sop_nright {n m} k (d : sop n m) : sop n (k + m) :=
  match k with
    | 0 => d
    | S k' => sop_right (sop_nright k' d)
  end.

(* A differently typed version which "fills out" to a given codomain. *)

Fixpoint sop_nright_fin' {n Sm} (i : fin Sm) (d : sop n (co_to_nat i)) :
  match Sm with | 0 => unit | S m => sop n m end
  :=
  match i in fin Sm return
    sop n (co_to_nat i) -> (match Sm with | 0 => unit | S m => sop n m end)
    with
    | fzero m => fun d => d
    | fsucc m i' =>
      match i' in fin m return
        (sop n (co_to_nat i') -> match m with 0 => unit| S m' => sop n m' end)
        -> sop n (co_to_nat (fsucc i'))
        -> sop n m
        with
        | fzero m' => fun IH d => sop_right (IH d)
        | fsucc m' i'' => fun IH d => sop_right (IH d)
      end (sop_nright_fin' i')
  end d.
      
Definition sop_nright_fin {n m} (i : fin (S m)) (d : sop n (co_to_nat i)) :
  sop n m :=
  sop_nright_fin' i d.

(* The k-bead in an n-simplex is the sub-k-simplex containing the
   first (k+1) vertices. *)

Fixpoint bead' {Sn} (k : fin Sn) : sop (to_nat k) (pred Sn) :=
  match k in fin Sn with
    | fzero n => sop_allleft 0 n
    | fsucc n k' =>
      match n return
        (forall (k' : fin n) (next : sop (to_nat k') (pred n)),
          sop (to_nat (fsucc k')) n) with
        | 0 => fun k' _ => fin0_rect k'
        | S n' => fun _ next => sop_left (sop_right next)
      end k' (bead' k')
  end.

Definition bead {n} (k : fin (S n)) : sop (to_nat k) n
  := bead' k.

Ltac do_bead :=
  unfold bead;
  match goal with
    | |- context cxt [ @bead' (S ?n) (@fzero ?n) ] =>
      let next := context cxt [ sop_allleft 0 n ] in
        change next
    | |- context cxt [ @bead' (S (S ?n)) (@fsucc (S ?n) ?k) ] =>
      let next := context cxt [ sop_left (sop_right (@bead' (S n) k)) ] in
        change next
  end; auto.

(* Dually, the k-cobead is the sub-(n-k)-simplex containing the last
   (n-k+1) vertices.  Thus, the k-bead and the k-cobead intersect in
   the k-vertex. *)

Fixpoint cobead' {Sn} (k : fin Sn) : sop (co_to_nat k) (pred Sn) :=
  match k in fin Sn with
    | fzero n => id_sop n
    | fsucc n k' =>
      match n return
        (forall (k' : fin n) (next : sop (co_to_nat k') (pred n)),
          sop (co_to_nat k') n) with
        | 0 => fun k' _ => fin0_rect k'
        | S n' => fun _ next => sop_right next
      end k' (cobead' k')
  end.

Definition cobead {n} (k : fin (S n)) : sop (co_to_nat k) n
  := cobead' k.

Ltac do_cobead :=
  unfold cobead;
  match goal with
    | |- context cxt [ @cobead' (S ?n) (@fzero ?n) ] =>
      let next := context cxt [ id_sop n ] in
        change next
    | |- context cxt [ @cobead' (S (S ?n)) (@fsucc (S ?n) ?k) ] =>
      let next := context cxt [ sop_right (cobead' k) ] in
        change next
  end.

(* A k-strand in an n-simplex is a map into it from the k-simplex
   which preserves the first and last vertices.  We describe a
   k-strand by the list of differences between the images of the
   vertices of the k-simplex. *)

Inductive strand_type : nat -> nat -> Type :=
| stnil : strand_type 0 0
| stcons : forall {n k} (i : fin (S n)),
  strand_type (co_to_nat i) k -> strand_type n (S k).

(* A differently typed version of [stnil]. *)
Fixpoint stnil' n : strand_type (co_to_nat (from_nat n)) 0
  := match n with
       | 0 => stnil
       | S n' => stnil' n'
     end.

Fixpoint strand {n k} (st : strand_type n k) : sop k n :=
  match st in strand_type n k return sop k n with
    | stnil => @sop_to0 0
    | stcons n k i st' => sop_leftany (sop_nright_fin i (strand st'))
  end.
  
(* The diagonal edge of a simplex is the [(n)]-strand. *)

Definition diag_strand n : strand_type n 1
  := stcons (from_nat n) (stnil' n).

Definition diag_edge n : sop 1 n
  := strand (diag_strand n).

(* The identity map of a simplex is the [(1,1,...,1)]-strand *)

Fixpoint id_strand (n : nat) : strand_type n n :=
  match n with
    | 0 => stnil
    | S n => stcons (fsucc fzero) (id_strand n)
  end.

Theorem id_strand_is_id n : strand (id_strand n) == id_sop n.
Proof.
  induction n as [|n]; auto; simpl.
  apply map; unfold sop_nright_fin; simpl.
  apply map; assumption.
Defined.

(* The composite of simplicial operators. *)

(* The operation [sop_compose] is defined by a nested fixpoint on both
   [d] and [e].  To make it easier to reason about, we separate out
   the inner fixpoint into a separate function [sop_compose_left].
   This composes [sop_left e] with [d], with the operation
   [sop_compose e] passed as a parameter [IHe]. *)

Fixpoint sop_compose_left {n m p} (e : sop m (S p)) (d : sop n (S m))
  (IHe : forall n':nat, sop n' m -> sop n' (S p)) :
  sop n (S p) :=
  match d in sop n m return
    (match m with
       | 0 => unit:Type
       | S m_minus_one =>
         sop m_minus_one (S p) ->
         (forall n':nat, sop n' m_minus_one -> sop n' (S p)) ->
         sop n (S p)
     end)
    with
    | sop_to0 _ =>
      tt       (* can't happen *)
    | sop_left0 _ => fun _ _ =>
      sop_left0
    | sop_right n _ d' => fun _ IHe =>
      IHe n d'
    | sop_left _ _ d' => fun e IHe =>
      sop_left (sop_compose_left e d' IHe)
  end e IHe.

Fixpoint sop_compose {n m p} (e : sop m p) (d : sop n m) : sop n p :=
  match e in sop m p return (forall n, sop n m -> sop n p) with
    | sop_to0 _ => fun n d =>
      sop_to0
    | sop_left0 p_minus_one => fun n d =>
      sop_allleft n (S p_minus_one)
    | sop_right _ _ e' => fun n d =>
      sop_right (sop_compose e' d)
    | sop_left m_minus_one _ e' => fun n d => 
      sop_compose_left e' d
      (fun n' (d' : sop n' m_minus_one) => sop_compose e' d')
  end n d.

(* A tactic to evaluate [sop_compose] by one step. *)

Ltac do_sop_compose :=
  match goal with
    | |- context cxt [ @sop_compose ?n ?m 0 (@sop_to0 ?m) ?d ] =>
      let next := context cxt [ @sop_to0 n ] in change next
    | |- context cxt [ @sop_compose ?n ?m ?p (@sop_left0 ?p_minus_one) ?d ] =>
      let next := context cxt [ sop_allleft' n p_minus_one ] in change next
    | |- context cxt [ @sop_compose ?n ?m ?p (@sop_right _ _ ?e') ?d ] =>
      let next := context cxt [ sop_right (sop_compose e' d) ] in change next
    | |- context cxt [ @sop_compose ?n ?m ?p (@sop_left ?m_minus_one _ ?e') ?d ] =>
      let next := context cxt [ sop_compose_left e' d
        (fun n' (d' : sop n' m_minus_one) => sop_compose e' d') ] in change next
    | |- context cxt [ @sop_compose_left ?n ?m ?p ?e (@sop_left0 _) ?IHe ] =>
      let next := context cxt [ @sop_left0 p ] in change next
    | |- context cxt [ @sop_compose_left ?n ?m ?p ?e (@sop_right ?n _ ?d') ?IHe ] =>
      let next := context cxt [ IHe n d' ] in change next
    | |- context cxt [ @sop_compose_left ?n ?m ?p ?e (@sop_left _ _ ?d') ?IHe ] =>
      let next := context cxt [ sop_left (sop_compose_left e d' IHe) ] in change next
  end; auto.

(* Now we calculate a bunch of composites of simplicial operators.  We
   start with the obvious observation that the composite of anything
   with the identity is itself. *)

Definition id_sop_left_unit {n m} (d : sop n m) :
  sop_compose (id_sop m) d == d.
Proof.
  induction d.
  auto.
  simpl; apply map; assumption.
  auto.
  simpl; apply map; path_change (sop_compose (id_sop (S m)) d).
Defined.

Definition id_sop_right_unit {n m} (d : sop n m) :
  sop_compose d (id_sop n) == d.
Proof.
  induction d.
  auto.
  simpl; apply map; assumption.
  auto.
  simpl; apply map; assumption.
Defined.

(* The composite of [sop_leftany] with [sop_left0] is [sop_left0]. *)

Definition sop_left_absorbing n m (d : sop n m) :
  sop_compose (sop_leftany d) sop_left0 == sop_allleft 0 m.
Proof.
  unfold sop_leftany.
  destruct m as [|m'].
  auto.
  do_sop_compose.
Defined.

(* The composite of [sop_leftany] with a vertex other than the last
   one is the corresponding vertex. *)

Definition sop_left_vertex' Sn m (d : sop (pred Sn) m) (k : fin Sn) :
  match Sn return sop (pred Sn) m -> fin Sn -> Type with
    | 0 => fun _ _ => unit:Type
    | S n => fun d k =>
      sop_compose (sop_leftany d) (vertex (fsucc k))
      == sop_compose d (vertex k)
  end d k.
Proof.
  induction k.
  simpl in d; induction d; auto.
  do_vertex.
  simpl in d; induction d; auto;
    unfold sop_leftany;
    repeat do_sop_compose.
Defined.

Definition sop_left_vertex n m (d : sop n m) (k : fin (S n)) :
  sop_compose (sop_leftany d) (vertex (fsucc k)) == sop_compose d (vertex k)
  := sop_left_vertex' (S n) m d k.

(* The composite of [sop_nright] with a vertex is the same vertex
   reindexed. *)

Definition sop_nright_compose_vertex'
  (Sn m k : nat) (d : sop (pred Sn) m) (i : fin Sn) :
  match Sn return sop (pred Sn) m -> fin Sn -> Type with
    | 0 => fun _ _ => unit:Type
    | S n => fun d i =>
      sop_compose (sop_nright k d) (vertex i) ==
      sop_nright k (sop_compose d (vertex i))
  end d i.
Proof.
  destruct i as [n | n i'].
  induction k as [|k']; auto.
  simpl. apply map, IHk'.
  induction k as [|k']; auto.
  simpl. apply map, IHk'.
Defined.

Definition sop_nright_compose_vertex
  (n m k : nat) (d : sop n m) (i : fin (S n)) :
  sop_compose (sop_nright k d) (vertex i)
    == sop_nright k (sop_compose d (vertex i))
  := sop_nright_compose_vertex' (S n) m k d i.

Definition sop_nright_vertex' (Sn k : nat) (i : fin Sn) :
  match Sn return fin Sn -> Type with
    | 0 => fun _ => unit:Type
    | S n => fun i =>
      sop_nright k (vertex i) == vertex (fplus2S k i)
  end i.
Proof.
  destruct i as [n | n i'];
    (destruct k as [|k']; auto; simpl;
    induction k' as [|k'']; auto; simpl;
    do_vertex; apply map, IHk'').
Defined.

Definition sop_nright_vertex (n k : nat) (i : fin (S n)) :
  sop_nright k (vertex i) == vertex (fplus2S k i)
  := sop_nright_vertex' (S n) k i.

(* Similarly for [sop_nright_fin]. *)

Definition sop_nright_fin_compose_vertex'
  (n Sm : nat) (j : fin Sm) (d : sop n (co_to_nat j)) (i : fin (S n)) :
  match Sm return
    forall (j : fin Sm), sop n (co_to_nat j) -> Type with
    | 0 => fun _ _ => unit:Type
    | S m => fun j d =>
      sop_compose (sop_nright_fin j d) (vertex i) ==
      sop_nright_fin j (sop_compose d (vertex i))
  end j d.
Proof.
  generalize dependent n.
  induction j as [m|m j']; auto.
  intros n d i.
  destruct j' as [m'|m' j''].
  unfold sop_nright_fin; auto.
  path_change (sop_right (sop_compose (sop_nright_fin (fsucc j'') d) (vertex i))).
  path_change (sop_right (sop_nright_fin (fsucc j'') (sop_compose d (vertex i)))).
Defined.

Definition sop_nright_fin_compose_vertex
  (n m : nat) (j : fin (S m)) (d : sop n (co_to_nat j)) (i : fin (S n)) :
  sop_compose (sop_nright_fin j d) (vertex i)
    == sop_nright_fin j (sop_compose d (vertex i))
  := sop_nright_fin_compose_vertex' n (S m) j d i.

Definition sop_nright_fin_vertex'
  (Sm : nat) (j : fin Sm) (i : fin (S (co_to_nat j))) :
  match Sm return
    forall (j : fin Sm), fin (S (co_to_nat j)) -> Type with
    | 0 => fun _ _ => unit:Type
    | S m => fun j i =>
      sop_nright_fin j (vertex i) == vertex (fplus2co i)
  end j i.
Proof.
  destruct j as [m|m j'].
  unfold sop_nright_fin; auto.
  simpl in *.
  induction j' as [m'|m' j''].
  unfold sop_nright_fin; simpl.
  simpl in i.
  path_change (sop_nright 1 (vertex i)).
  path_change (vertex (fplus2S 1 i)).
  apply sop_nright_vertex.
  simpl in *.
  do_vertex.
  path_change (sop_right (sop_nright_fin (fsucc j'') (vertex' i))).
  apply IHj''.
Defined.

Definition sop_nright_fin_vertex
  {m} (j : fin (S m)) (i : fin (S (co_to_nat j))) :
  sop_nright_fin j (vertex i) == vertex (fplus2co i)
  := sop_nright_fin_vertex' (S m) j i.


(* The vertices of a k-bead are the same vertices of the original simplex. *)

Definition bead_vertex' {SSn} (Sk : fin SSn) (i : fin' Sk) :
  match Sk in fin SSn return (fin' Sk -> sop 0 (pred (pred SSn))) with
    | fzero _ => fun i => fin'0_rect i
    | fsucc Sn k => fun i => sop_compose (bead' k) (vertex' (finject i))
  end i
  ==
  match SSn return fin SSn -> fin (pred SSn) -> sop 0 (pred (pred SSn)) with
    | 0 => fun Sk _ => fin0_rect Sk
    | S Sn => fun Sk next =>
      match Sn return fin Sn -> sop 0 (pred Sn) with
        | 0 => fun _ => sop_to0
        | S n => vertex
      end next
  end Sk (inject_bang' i).
Proof.
  induction i as [Sn k|Sn k i'].
  (* Case: i = 0 *)
  destruct k as [n|n k'].
  (* Subcase: k = 0 *)
  do_bead. simpl. destruct n; auto.
  (* Subcase: k = S k', n = S n' *)
  destruct n as [|n'].
  (* Subsubcase: n' = 0 *)
  apply fin0_rect, k'.
  (* Subsubcase: n' > 0 *)
  do_bead.
  (* Case: i = S i', Sk = S k, SSn = S Sn *)
  destruct i' as [n k' | n k' i''].
  (* Subcase: i' = 0 *)
  destruct k' as [n' | n' k''].
  (* Subsubcase: k' = 0, n = S n' *)
  do_bead. do_sop_compose. simpl.
  destruct n'; simpl; do_vertex.
  (* Subsubcase: k' > 0, n = S n' *)
  simpl. do_vertex. apply map.
  destruct n'.
  (* Subsubsubcase: n' = 0 *)
  apply fin0_rect, k''.
  (* Subsubsubcase: n' > 0 *)
  auto.
  (* Subcase: i' = S i'', k = S k', Sn = S n *)
  path_change (sop_compose (bead' (fsucc k'))
    (vertex' (fsucc (fsucc (finject i''))))).
  do_vertex.
  destruct k' as [n' | n' k''].
  (* Subsubcase: k' = 0 *)
  apply fin'0_rect, i''.
  (* Subsubcase: k' = S k'' *)
  path_change (vertex' (fsucc (inject_bang' (fsucc' i'')))).
  do_vertex. do_bead. do_sop_compose. do_sop_compose.
  path_change (sop_compose (sop_right (bead' (fsucc k'')))
    (vertex' (fsucc (finject i'')))).
  do_sop_compose. apply map.
  apply IHi'.
Qed.
  
Definition bead_vertex {n} (k : fin (S n)) (i : fin' (fsucc k)) :
  sop_compose (bead k) (vertex (finject i)) == vertex (inject_bang i)
  := bead_vertex' (fsucc k) i.

(* In particular, the first vertex of the k-bead is the first vertex,
   and the last vertex of the k-bead is the kth vertex. *)

Definition bead_vertex_first {n} (k : fin (S n)) :
  sop_compose (bead k) (vertex fzero) == vertex fzero.
Proof.
  path_change (sop_compose (bead k) (vertex (finject fzero'))).
  path_via (vertex (inject_bang (@fzero' (S n) k))).
  apply bead_vertex.
  simpl.
  apply inject_bang_fzero.
Qed.

Definition bead_vertex_last {n} (k : fin (S n)) :
  sop_compose (bead k) (vertex (from_nat (to_nat k))) == vertex k.
Proof.
  path_via (sop_compose (bead k) (vertex (finject (from_fin k)))).
  apply opposite, finject_from_fin.
  path_via (vertex (inject_bang (from_fin k))).
  apply bead_vertex.
  apply inject_bang_from_fin.
Qed.

(* The vertices of a k-cobead are the shifted vertices of the original
   simplex. *)

Definition cobead_vertex' {Sn} (k : fin Sn) (i : cofin' k) :
  match Sn return (forall (k : fin Sn), cofin' k -> Type) with
    | 0 => fun _ _ => unit:Type
    | S n => fun k i =>
      sop_compose (cobead k) (vertex' (cofinject i))
        == vertex' (coinject_shifted i)
  end k i.
Proof.
  induction i as [n j|n k' i'].
  (* Case: Sn = S n, k = 0, i = j. *)
  simpl; do_cobead; apply id_sop_left_unit.
  (* Case: Sn = S n, k = fsucc k', i = cofinject1 i' *)
  destruct i' as [n' j' | n' k'' i''].
  (* Subcase: n = S n', k' = 0, i' = j' *)
  simpl. clear IHi'.
  path_via (sop_right (vertex j')).
  apply id_sop_left_unit.
  unfold vertex.
  set (n := S n') in *.
  path_change (match n as n return fin n -> sop 0 n with
                 | 0 => fun _ => sop_to0
                 | S _ => fun k => sop_right (vertex k)
               end j').
  clearbody n. clear n'.
  destruct j' as [n' | n' j'']; auto.
  (* Subcase: n = S n', k' = fsucc k'', i' = cofinject1 i'' *)
  exact (map sop_right IHi').
Qed.

Definition cobead_vertex {n} (k : fin (S n)) (i : cofin' k) :
  sop_compose (cobead k) (vertex (cofinject i))
    == vertex (coinject_shifted i)
  := cobead_vertex' k i.

(* In particular, the first vertex of the k-cobead is the kth vertex,
   and the last vertex of the k-cobead is the last vertex. *)

Definition cobead_vertex_first {n} (k : fin (S n)) :
  vertex k == sop_compose (cobead k) (vertex fzero).
Proof.
  path_via (sop_compose (cobead k) (vertex (cofinject (cofzero k)))).
  2:apply cofinject_cofzero.
  path_via (vertex (coinject_shifted (cofzero k))).
  apply opposite, coinject_shifted_cofzero.
  apply opposite, cobead_vertex.
Qed.

Definition cobead_vertex_last {n} (k : fin (S n)) :
  sop_compose (cobead k) (vertex (from_nat (co_to_nat k)))
    == vertex (from_nat n).
Proof.
  path_via (sop_compose (cobead k) (vertex (cofinject (cofmax k)))).
  apply opposite, cofinject_cofmax.
  path_via (vertex (coinject_shifted (cofmax k))).
  apply cobead_vertex.
  apply coinject_shifted_cofmax.
Qed.


(* The vertices of a strand are the vertices of the original simplex
   numbered by adding up an appropriate number of differences in the
   strand type. *)

(* First, a function which computes the sum of all the first [i]
   differences specified in [st]. *)
Fixpoint strand_psum' n Sk (st : strand_type n (pred Sk)) (i : fin Sk)
  {struct i}
  : fin (S n)
  := match i in fin Sk return
       strand_type n (pred Sk) -> fin (S n) with
       | fzero k => fun _ => fzero
       | fsucc k i' => fun st =>
         match st in strand_type n k return
           (forall n' (st' : strand_type n' (pred k)), fin (S n'))
           -> fin k -> fin (S n)
           with
           | stnil => fun _ i' => fin0_rect i'
           | stcons n k' j st' => fun rec _ => fplus2co (rec _ st')
         end (fun n' st' => strand_psum' n' k st' i') i'
     end st.

Definition strand_psum {n k} (st : strand_type n k) (i : fin (S k))
  : fin (S n)
  := strand_psum' n (S k) st i.

(* The sum of a 1-element strand is that number. *)

Definition strand_psum_one n :
  strand_psum (diag_strand n) (fsucc fzero) == from_nat n.
Proof.
  destruct n; auto.
  unfold strand_psum; simpl.
  apply map, fplus2co_fzero.
Defined.

(* The total sum of a strand is [n].  *)

Definition strand_psum_total n k (st : strand_type n k) :
  strand_psum st (from_nat k) == from_nat n.
Proof.
  induction st as [|n' k' i st']; auto.
  simpl. unfold strand_psum; simpl.
  path_via (fplus2co (from_nat (co_to_nat i))).
  apply fplus2co_from_nat.
Defined.

(* Now we compute the vertices of a strand. *)

Definition strand_vertex' n Sk (st : strand_type n (pred Sk)) (i : fin Sk) :
  match Sk return (strand_type n (pred Sk) -> fin Sk -> Type) with
    | 0 => fun _ _ => unit:Type
    | S k => fun st i =>
      sop_compose (strand st) (vertex i) == vertex (strand_psum st i)
  end st i.
Proof.
  generalize dependent n.
  induction i as [k | k i'].
  (* Case: Sk = S k, i = 0 *)
  unfold strand_psum; simpl in *.
  destruct st as [|n' k' st' j].
  (* Subcase: n=k=0 *)
  auto.
  (* Subcase: other. *)
  destruct n' as [|n'']; auto.
  (* Case: Sk = S k, i = fsucc i'. *)
  simpl. intros n st.
  destruct st as [|n' k' j st'].
  (* Subcase: k = 0 *)
  exact (fin0_rect i').
  (* Subcase: other. *)
  path_via (sop_compose (sop_leftany (sop_nright_fin j (strand st')))
    (sop_right (vertex' i'))).
  apply vertex_fsucc.
  destruct n' as [|n'']; simpl.
  (* Subsubcase: n' = 0 *)
  apply sop_to0_uniq.
  (* Subsubcase: n' = S n'' *)
  path_via (sop_nright_fin j (sop_compose (strand st') (vertex' i'))).
  apply sop_nright_fin_compose_vertex.
  path_via (sop_nright_fin j (vertex (strand_psum st' i'))).
  unfold strand_psum; simpl.
  apply sop_nright_fin_vertex.
Qed.

Definition strand_vertex {n k} (st : strand_type n k) (i : fin (S k)) :
  sop_compose (strand st) (vertex i) == vertex (strand_psum st i)
  := strand_vertex' n (S k) st i.


(* In particular, the vertices of the diagonal edge are the 0th and
   the nth. *)

Definition diag_edge_vertex0 n :
  sop_compose (diag_edge n) (vertex fzero) == vertex fzero.
Proof.
  unfold diag_edge.
  path_via (vertex (strand_psum (diag_strand n) fzero)).
  apply strand_vertex.
Qed.

Definition diag_edge_vertex1 n :
  sop_compose (diag_edge n) (vertex (fsucc fzero)) == vertex (from_nat n).
Proof.
  unfold diag_edge.
  path_via (vertex (strand_psum (diag_strand n) (fsucc fzero))).
  apply strand_vertex.
  apply strand_psum_one.
Qed.

(* Other composites to compute:
   * strands of strands
   * faces of faces
   * vertices of faces
 *)
