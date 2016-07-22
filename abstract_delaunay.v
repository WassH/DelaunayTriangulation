Require Import Arith.
Require Import EqNat.
Require Import Ring.



(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq fintype.
From mathcomp Require Import finset zmodp matrix bigop ssralg matrix ssrnum.
From mathcomp Require Import finmap seq ssrfun finfun matrix ssrnum ssrfun.
From mathcomp Require Import bigop ssralg finset fingroup zmodp poly fingraph.
From mathcomp Require Import tuple choice path.
(* -------------------------------------------------------------------- *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Delaunay.

Local Notation "p '.1'" :=  (p (inZp 1)).
Local Notation "p '.0'" := (p (inZp 0))
  (at level 2, left associativity, format "p .0").
Local Notation "p '.2'" := (p (inZp 2))
  (at level 2, left associativity, format "p .2").

Variable R : numDomainType.
Variable P : finType.

Variable coords : P -> 'rV[R]_2.

Hypothesis coords_inj : injective coords.

Definition T := (P ^ 3)%type.


Definition oriented (t : T) : bool :=
  (0 < \det (col_mx (coords (t.1) - coords (t.0))
                    (coords (t.2) - (coords t.0))))%R.

Definition in_circle_row (v : 'rV[R]_2) : 'rV[R]_4 :=
    \row_(i < 4)
     if val i == 0 then (v.0.0 * v.0.0  + v.0.1 * v.0.1)%R
     else if val i == 1 then v.0.0
     else if val i == 2 then v.0.1
     else 1%R.

Definition incircle t (p : P) : bool :=
  (\det (col_mx (\matrix_(i < 3) in_circle_row (coords (t i)))
         (in_circle_row (coords p))) < 0)%R.

Definition triangulation := {set T}.

Variable triangulation_order : triangulation -> triangulation -> bool.

Hypothesis wf_triangulation_order : well_founded triangulation_order.

Definition inter_triangle (t1 t2 : T) : {set P} :=
  [set x | x \in codom t1] :&: [set x | x \in codom t2].

Definition third_point (t1 t2 : T) : P :=
 odflt (t2.0) (pick [pred x | x \in
                  [set t2 x | x : 'I_3] :\: inter_triangle t1 t2]).

Definition illegal_edge (t1 t2 : T) : bool :=
  (t1 != t2) &&
  (#|inter_triangle t1 t2| == 2) && incircle t1 (third_point t1 t2).

Definition build_triangle0 (p1 p2 p3 : P) : T :=
  [ffun x => if val x == 0 then p1 else if val x == 1 then p2 else p3].

Local Notation "[ 'triangle' a ; b ; c ]" := (build_triangle0 a b c)
  (format "[ triangle  a ;  b ;  c ]").

Definition build_triangle (p : P) (edge : {set P}) :=
  odflt [ffun _ => p]
    (pick [pred f : {ffun 'I_3 -> P} |
                  ([set x | x \in codom f] == [set p] :|: edge) &&
           oriented f]).

Definition flip_edge (t1 t2 : T) (m : triangulation) : triangulation :=
  let p1 := third_point t2 t1 in
  let p2 := third_point t1 t2 in
  [set build_triangle p1 (inter_triangle t1 t2);
       build_triangle p2 (inter_triangle t1 t2)] :|: (m :\: [set t1; t2]).

Definition find_triangle (m : triangulation) (p : P) : option T :=
  pick [pred t | (t \in m) &&
          oriented ([triangle t.0; t.1; p]) &&
          oriented [triangle t.1; t.2; p] &&
          oriented [triangle t.2; t.0; p]].

Definition Zp_succ (n : nat) (i : 'I_n.+1) := Zp_add i (inZp 1).

Definition border_triangles (m : triangulation) (p : P) : {set T} :=
  [set t | t : T &
     [exists i : 'I_3,  oriented [triangle t (Zp_succ i); t i; p] &&
                 [forall t' : T, ((t' \in m) && (t != t')) ==>
                                  (inter_triangle t t' !=
                                     [set t i ; t (Zp_succ i)])]]].

Definition triangles_out (m : triangulation) (p : P) : {set T} :=
  \bigcup_(t | t \in border_triangles m p)
     [set x | (x \in [set [triangle t (Zp_succ i); t i; p] | i : 'I_3])
   && oriented x].

Definition add_point (m : triangulation) (p : P) : triangulation :=
  match find_triangle m p with
  | Some t => [set [triangle t i ; t (Zp_succ i); p] | i : 'I_3] :|:
              (m :\: [set t])
  | None => triangles_out m p :|: m
  end.

Hypothesis flip_decrease : forall (m : triangulation) t1 t2,
  t1 \in m -> t2 \in m -> illegal_edge t1 t2 ->
  triangulation_order (flip_edge t1 t2 m) m.

Definition rflip_body (m : triangulation)
    (f : forall m', triangulation_order m' m -> triangulation) : triangulation.
case: (set_0Vmem [set x : T * T | (fst x \in m) && (snd x \in m) &&
                   illegal_edge (fst x) (snd x)]). 
  move => _; exact m.
move => [[t1 t2]]; rewrite in_set => /andP [] /andP [] intp1 intp2 ill.
apply: (f (flip_edge t1 t2 m) (flip_decrease intp1 intp2 ill)).
Defined.

Definition all_flips (m : triangulation) : triangulation :=
  Fix wf_triangulation_order _ rflip_body m.

Fixpoint delaunay (s : seq P) : triangulation :=
   match s with
   | nil => set0
   | _ :: nil => set0
   | _ :: _ :: nil => set0
   | p1 :: p2 :: p3 :: nil => [set build_triangle p1 [set p2 ; p3]]
   | p :: tl => all_flips (add_point (delaunay tl) p)
   end.