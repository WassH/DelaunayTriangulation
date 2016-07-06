Require Import Arith.
Require Import EqNat.
Require Import Ring.



(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq finfun matrix ssrnum ssrfun fintype tuple choice path.
From mathcomp Require Import finset zmodp matrix bigop ssralg.
From mathcomp Require Import finmap.
From mathcomp Require Import bigop ssralg finset fingroup zmodp poly.

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Delauney.


(* Notations de départ *) 

Notation "zero<1" := (ltn0Sn 0).
Notation "zero<2" := (ltn0Sn 1).
Notation "un<2" := (ltnSn 1).
Notation "zero<3" := (ltn0Sn 2).
Notation "un<3" := (ltn_trans (ltnSn 1) (ltnSn 2)).
Notation "deux<3" := (ltnSn 2).
Notation "zero<4" := (ltn0Sn 3).
Notation "un<4" := (ltn_trans (ltn_trans (ltnSn 1) (ltnSn 2)) (ltnSn 3)).
Notation "deux<4" := (ltn_trans (ltnSn 2) (ltnSn 3)).
Notation "trois<4" := (ltnSn 3).
Notation "zero<5" := (ltn0Sn 4).
Notation "un<5" := (ltn_trans (ltn_trans (ltn_trans (ltnSn 1) (ltnSn 2)) (ltnSn 3)) (ltnSn 4)).
Notation "deux<5" := (ltn_trans (ltn_trans (ltnSn 2) (ltnSn 3)) (ltnSn 4)).
Notation "trois<5" := (ltn_trans (ltnSn 3) (ltnSn 4)).
Notation "quatre<5" := (ltnSn 4).

(* R n'a pas besoin d'être un corps juste un anneau suffit *)
Variable R : numDomainType.
Definition point := 'rV[R]_2.

Definition E := nat.
Definition T := nat.

Open Local Scope type_scope.
Definition triangle := (E*bool)^3.

Definition edgemap := {fmap E -> point^2}.
Definition edgetmap := {fmap E -> {fset T}}.
Definition trianglemap := {fmap T -> triangle}.
Definition hull := {fmap E -> E*E}.

(* hull permet a partir d'une arete sur l'enveloppe convexe de donner la précédente et la suivante *)

Axiom modulo : forall i n:nat,  (i%%n)< n.

Definition addOrd2 : 'I_2 -> 'I_2 -> 'I_2 :=
  fun (p q : 'I_2) => Ordinal(modulo (p+q) 2).

Definition addOrd3 : 'I_3 -> 'I_3 -> 'I_3 :=
  fun (p q : 'I_3) => Ordinal(modulo (p+q) 3).




Open Scope fmap_scope.
(* triangleprop1 permet de dire que les aretes d'un triangle sont dans edgemap *)
Definition triangleprop1 (em: edgemap) (t : triangle) :=
  forall i :'I_3, fst (t i) \in em.



(* triangleprop2 dit que les arêtes d'un triangle sont connectées et qu'elles tournent en sens trigo *)
Definition triangleprop2 (em :edgemap) (t:triangle) (c : triangleprop1 em t) :=
  forall i :'I_3, forall i2 :'I_2,  (em.[c i] (addOrd2 i2 (Ordinal un<2)) == em.[c (addOrd3 i (Ordinal un<3))] (i2))

    && let M1 := ((em.[c i] i2)%fmap (Ordinal(zero<1)) (Ordinal(zero<2)) - (em.[c i] (addOrd2 i2 (Ordinal un<2)))%fmap (Ordinal(zero<1))  (Ordinal(zero<2)))%R in
       let M2 := ((em.[c i] i2)%fmap (Ordinal(zero<1))  (Ordinal(un<2)) -(em.[c i] (addOrd2 i2 (Ordinal un<2)))%fmap (Ordinal(zero<1))  (Ordinal(un<2)))%R in
       let M3 := ((em.[c (addOrd3 i (Ordinal un<3))] i2)%fmap (Ordinal(zero<1))  (Ordinal(zero<2)) -(em.[c (addOrd3 i (Ordinal un<3))] (addOrd2 i2 (Ordinal un<2)))%fmap (Ordinal(zero<1))  (Ordinal(zero<2)))%R in
       let M4 := ((em.[c (addOrd3 i (Ordinal un<3))] i2)%fmap (Ordinal(zero<1))  (Ordinal(un<2)) -(em.[c (addOrd3 i (Ordinal un<3))] (addOrd2 i2 (Ordinal un<2)))%fmap (Ordinal(zero<1))  (Ordinal(un<2)))%R in
         ((M1*M4 - M2*M3) >0)%R.


(* tmap_prop1 dit que toutes les arêtes de tous les triangles sont dans edgemap *)
Definition tmap_prop1 (em : edgemap) (tm : trianglemap) :=
  forall i : nat, forall h : i \in tm, triangleprop1 em tm.[h].


(* tmap_prop2 dit que pour tous les triangles dans trianglemap, leurs arêtes sont bien connectées et 
tournent en sens trigo *)
Definition tmap_prop2  (em : edgemap) (tm : trianglemap) :=
  forall h : tmap_prop1 em tm, forall t:T, forall h2 : t \in tm, 
      @triangleprop2 (em) (tm.[h2]) (h t h2).


