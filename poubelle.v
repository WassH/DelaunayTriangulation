Require Import Arith.
Require Import EqNat.



(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat matrix finfun ssrnum ssrfun fintype tuple choice path.
From mathcomp Require Import finset zmodp matrix bigop ssralg.
From mathcomp Require Import finmap.
(* -------------------------------------------------------------------- *)
Import GRing.Theory.
Open Local Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Variable R : numFieldType.
Check R.

(* Axiomes de départ *) 

Notation "zero<2" := (ltn0Sn 1).
Notation "un<2" := (ltnSn 1).
Notation "zero<3" := (ltn0Sn 2).
Notation "un<3" := (ltn_trans (ltnSn 1) (ltnSn 2)).
Notation "deux<3" := (ltnSn 2).


Definition Cn (n: nat) := \col_(j < n) (n.-1 == j).

Let M:= \col_(j < 4) 2.


(* Création des 3 tableaux (matrices) tabPoint, tabEdge et tabTriangle qui vont être modifiés par les fonctions 
unhook et atttach qui vont être utilisées dans le flip *)

Print finmap.
Variable P : choiceType.
Variable tabPoint : {fmap P -> 'I_2 -> R}.

Variable E : choiceType.
Variable tabEdge : {fmap E->'I_2->P}.

Variable T : choiceType.
Variable tabTriangle : {fmap T->'I_3-> E*bool}.

Variable E2T : {fmap E-> {fset T}}.


(* Fonction unhook qui détache une arete commune a deux triangles et qui va etre utile pour 
l'opération de flip *)

Definition unhook (e: edge) :=
if (edge2point1 e == tabEdge (Ordinal zero<2) (Ordinal zero<5)) && (edge2point2 e == tabEdge (Ordinal un<2) (Ordinal zero<5)) then tabEdge (Ordinal zero<2) (Ordinal zero<5) = origin & tabEdge (Ordinal un<2) (Ordinal zero<5)=origin
  else if (edge2point2 e == tabEdge (Ordinal zero<2) (Ordinal zero<5)) && (edge2point1 e == tabEdge (Ordinal un<2) (Ordinal zero<5)) then 

if (edge2point1 e == tabEdge (Ordinal zero<2) (Ordinal un<5)) && (edge2point2 e == tabEdge (Ordinal un<2) (Ordinal un<5)) then 
  else if (edge2point2 e == tabEdge (Ordinal zero<2) (Ordinal un<5)) && (edge2point1 e == tabEdge (Ordinal un<2) (Ordinal un<5)) then 

if (edge2point1 e == tabEdge (Ordinal zero<2) (Ordinal deux<5)) && (edge2point2 e == tabEdge (Ordinal un<2) (Ordinal deux<5)) then 
  else if (edge2point2 e == tabEdge (Ordinal zero<2) (Ordinal deux<5)) && (edge2point1 e == tabEdge (Ordinal un<2) (Ordinal deux<5)) then 

if (edge2point1 e == tabEdge (Ordinal zero<2) (Ordinal trois<5)) && (edge2point2 e == tabEdge (Ordinal un<2) (Ordinal trois<5)) then 
  else if (edge2point2 e == tabEdge (Ordinal zero<2) (Ordinal trois<5)) && (edge2point1 e == tabEdge (Ordinal un<2) (Ordinal trois<5)) then 

if (edge2point1 e == tabEdge (Ordinal zero<2) (Ordinal quatre<5)) && (edge2point2 e == tabEdge (Ordinal un<2) (Ordinal quatre<5)) then 
  else if (edge2point2 e == tabEdge (Ordinal zero<2) (Ordinal quatre<5)) && (edge2point1 e == tabEdge (Ordinal un<2) (Ordinal quatre<5)) then 

(* A RETRAVAILLER car je ne vois pas comment modifier la valeur d'une case de la matrice *).



Definition attach (e:edge) := 
if (origin == tabEdge (Ordinal zero<2) (Ordinal zero<5)) && (origin == tabEdge (Ordinal un<2) (Ordinal zero<5)) then tabEdge (Ordinal zero<2) (Ordinal zero<5) =
  

else if (origin == tabEdge (Ordinal zero<2) (Ordinal un<5)) && (origin == tabEdge (Ordinal un<2) (Ordinal un<5)) then 
  

else if (origin == tabEdge (Ordinal zero<2) (Ordinal deux<5)) && (origin == tabEdge (Ordinal un<2) (Ordinal deux<5)) then 
  

else if (origin == tabEdge (Ordinal zero<2) (Ordinal trois<5)) && (origin == tabEdge (Ordinal un<2) (Ordinal trois<5)) then 
 

else if (origin == tabEdge (Ordinal zero<2) (Ordinal quatre<5)) && (origin == tabEdge (Ordinal un<2) (Ordinal quatre<5)) then .


(* Faire appel à la fonction isDelauneyLocal *)
Definition findIllegal :=
  .

Definition flip (e:edge) :=
  unhook e; attach e.

(* Dans makeDelauney faire un test findIllegal et si oui alors faire flip et rappeler 
makeDelauney *)
Fixpoint makeDelauney :=




