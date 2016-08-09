(*=====================================================
=======================================================
JUNE 2016 - AUGUST 2016

AUTHOR : Wassim Haffaf.
=======================================================
=======================================================*)

Require Import Arith.
Require Import EqNat.



(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq finfun matrix ssrnum ssrfun fintype tuple choice path.
From mathcomp Require Import finset zmodp matrix bigop ssralg.
From mathcomp Require Import finmap.

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Notations de départ *) 

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


(* Création des Points, de l'ensemble R et de la fonction coords :*)

Section toto.

Variable R : numFieldType.
Check R.


Definition point := {ffun 'I_2 -> R}%type.
Print point.
Check point.

Variable origin : point.

Definition point2R1 (p: point) : R :=
  p (Ordinal(zero<2)).


Definition point2R2 (p: point) : R :=
  p (Ordinal(un<2)).


(* Création des edges (orientés seulement par la donnée du 1er point et du 2ème point)
   et des fonctions edge2point*)


Definition edge := {ffun 'I_2 -> point}.
Check edge.


Definition edge2point1 (e: edge) : point :=
  e (Ordinal(zero<2)).




Definition edge2point2 (e: edge) : point :=
  e (Ordinal(un<2)).


Definition head (e:edge) (b:bool) : point :=
  if b==true then edge2point2 e else edge2point1 e.


Definition tail (e:edge) (b:bool) : point :=
  if b==true then edge2point1 e else edge2point2 e.

Axiom modulo : forall i n:nat,  (i%%n)< n.


Definition addOrd3 : 'I_3 -> 'I_3 -> 'I_3 :=
  fun (p q : 'I_3) => Ordinal(modulo (p+q) 3).




(* Création des Triangles et de la fonction d'adjacence de triangles *)

Record triangle := {
  edges : {ffun 'I_3 -> edge*bool} ;
  _ : forall (i : 'I_3), tail (fst (edges i)) (snd (edges i)) ==
                         head (fst (edges (addOrd3 i (Ordinal un<3) ))) (snd (edges (addOrd3 i (Ordinal(un<3) ))))
}.




Definition triangle2edges (t1: triangle) : {ffun 'I_3 -> edge} :=
  [ffun Ord : 'I_3 => fst ((edges t1) Ord)].



(* adjE dit si 2 edges sont adjacents *)
Definition adjE : edge -> edge -> bool :=
  fun (e1 e2 : edge) => (tail e1 true == tail e2 true) && (tail e1 true == tail e2 true)
                        || (tail e1 false == tail e2 true) && (tail e1 false == tail e2 true).


(*adjT dit si 2 triangles sont adjacents*)
Definition adjT : triangle -> triangle -> bool :=
  fun (t1 t2 : triangle) => [exists x : 'I_3, exists y : 'I_3, (adjE  (fst(edges t1 x))  (fst(edges t2 y))) ==true].


Open Local Scope ring_scope.

(* Définition de inCircle, RMQ : si un point est sur le bord du cercle circonscrit alors il n'est pas 
inCircle *)
Definition inCircle (p1 : point) (t1 : triangle) : bool :=

  let M1 := \col_(j < 4) if j==0 then point2R1 (edge2point1 (triangle2edges t1 (Ordinal (zero<3))))
                         else if  j==1 then point2R1 (edge2point1 (triangle2edges t1 (Ordinal (un<3))))
                         else if  nat_of_ord j==2 then point2R1 (edge2point1 (triangle2edges t1 (Ordinal (deux<3))))
                         else point2R1 p1 in
  let M2 := \col_(j < 4) if j==0 then point2R2 (edge2point1 (triangle2edges t1 (Ordinal (zero<3))))
                         else if  j==1 then point2R2 (edge2point1 (triangle2edges t1 (Ordinal (un<3))))
                         else if  nat_of_ord j==2 then point2R2 (edge2point1 (triangle2edges t1 (Ordinal (deux<3))))
                         else point2R2 p1 in
  let M3 := \col_(j < 4) if j==0 then (point2R1 (edge2point1 (triangle2edges t1 (Ordinal (zero<3)))))^+2 + (point2R2 (edge2point1 (triangle2edges t1 (Ordinal (zero<3)))))^+2
                         else if j==1 then (point2R1 (edge2point1 (triangle2edges t1 (Ordinal (un<3)))))^+2 + (point2R2 (edge2point1 (triangle2edges t1 (Ordinal (un<3)))))^+2
                         else if  nat_of_ord j==2 then (point2R1 (edge2point1 (triangle2edges t1 (Ordinal (deux<3)))))^+2 + (point2R2 (edge2point1 (triangle2edges t1 (Ordinal (deux<3)))))^+2
                         else (point2R1 p1)^+2 + (point2R2 p1)^+2 in
  let M4 := \col_(j < 4) 1 in
  let M := row_mx (row_mx M1 M2) (row_mx M3 M4) in if \det M > 0 then true else false.


(* La fonction isDelauneyLocal va prendre 2 triangles et va renvoyer un bool qui vaudra true si
 la construction des 2 triangles est de Delauney *)
Definition isDelauneyLocal : triangle -> triangle -> bool :=
  fun (t1 t2 : triangle) => if (inCircle (tail (fst (edges t1 (Ordinal(zero<3)))) (snd (edges t1 (Ordinal(zero<3))))) (t2) == false
                              && inCircle (tail (fst (edges t1 (Ordinal(un<3)))) (snd (edges t1 (Ordinal(un<3))))) (t2) == false
                              && inCircle (tail (fst (edges t1 (Ordinal(deux<3)))) (snd (edges t1 (Ordinal(deux<3))))) (t2) == false)
                            then true
                            else false.


(* Création des 3 tableaux (finmap) tabPoint, tabEdge et tabTriangle qui vont être <<modifiés>> par les fonctions 
unhook et atttach qui vont être utilisées dans le flip *)

Variable P : choiceType.
Variable tabPoint : {fmap P -> 'I_2 -> R}.

Variable E : choiceType.
Variable tabEdge : {fmap E->'I_2->P}.

Variable T : choiceType.
Variable tabTriangle : {fmap T->'I_3-> E*bool}.

Variable E2T : {fmap E-> {fset T}}.


(* 
(* Fonction bind qui va permettre de faire plusieurs opérations à la suite dans les fonctions qui suivent *)
Definition bind := 

Notation ";" := bind ...



(* Fonctions add_point_triangle, add_point_out, add_edge et add_triangle *)

Definition add_point_triangle :=

Definition add_point_out := 

Definition add_edge :=

Definition add_triangle := 
 *)


(* Fonction unhook qui détache une arete commune a deux triangles et qui va etre utile pour 
l'opération de flip *)

Check tabEdge.

Open Scope fmap_scope.

Check fun e=> tabEdge.[~ e].

Locate ".[".

Definition unhook (table : {fmap E -> 'I_3 -> P}) (e: E) :=
    table.[~ e].

Definition unhookE (e: edge) := 
  let e1 := tabEdge.[& [fset edge2point1 e edge2point2 e]] in
  if ~(tabEdge.[& [fset edge2point1 e edge2point2 e]] == nil) then tabEdge.[~ e1]
  else tabEdge.

Definition unhookT (e:edge) :=
  let e1 := tabEdge.[& [fset edge2point1 e edge2point2 e]] in
  if ~(tabEdge.[& [fset edge2point1 e edge2point2 e]] == nil) then tabTriangle.[~ E2T e1]
  else tabTriangle.


Definition attachE (e1:edge) (b1 : bool) (e2:edge) (b2 : bool) (e3:edge) (b3 : bool) (e4:edge) (b4 : bool):= 
  let edgeNew : {fmap E->'I_2->P} := fun (x:E) (Ord : 'I_2) => 
      if Ord == Ordinal (zero<2) then tabPoint.[& [fset point2R1(head e1 b1) point2R2(head e1 b1)]]
      else tabPoint.[& [fset point2R1(tail e4 b4) point2R2(tail e4 b4)]] in
  tabEdge + edgeNew.

Definition attachT (e1:edge) (b1 : bool) (e2:edge) (b2 : bool) (e3:edge) (b3 : bool) (e4:edge) (b4 : bool):= 
  let edgeNew : {fmap E->'I_2->P} := fun (x:E) (Ord : 'I_2) => 
      if Ord == Ordinal (zero<2) then tabPoint.[& [fset point2R1(head e1 b1) point2R2(head e1 b1)]]
      else tabPoint.[& [fset point2R1(tail e4 b4) point2R2(tail e4 b4)]] in

  let triangleNew1 : {fmap T->'I_3-> E*bool} := fun (t:T) (Ord : 'I_3) => 
      if Ord == Ordinal (zero<2) then (edgeNew, bool??)
      else if Ord == Ordinal (zero<2) then (tabEdge.[& [fset (head e4 b4) (tail e4 b4)]],b4) 
      else (tabEdge.[& [fset (head e1 b1) (tail e1 b1)]],b1) in

   let triangleNew2 : {fmap T->'I_3-> E*bool} := fun (t:T) (Ord : 'I_3) => 
      if Ord == Ordinal (zero<2) then (edgeNew, ~bool??)
      else if Ord == Ordinal (zero<2) then (tabEdge.[& [fset (head e2 b2) (tail e2 b2)]],b2) 
      else (tabEdge.[& [fset (head e3 b3) (tail e3 b3)]],b3) in

  tabTriangle + triangleNew1 + triangleNew2.
(* Definition à revoir au niveau de la syntaxe et du chois dans les intersections avec tabEdge *)


(* Faire appel à la fonction isDelauneyLocal *)
Definition findIllegal := 

  let edge1 := in
  let edge2 := in
  let edge3 := 
  in


  forall t1:T, exists ord1 : 'I_3, exists (e1,b1) : E*bool, tabTriangle t1 ord1 == (e1,b1),
  forall t2:T, exists ord2 : 'I_3, exists (e2,b2) : E*bool, tabTriangle t2 ord2 == (e2,b2),
    adjT t1 t2, 

   let triangleT2 := Canonical Structure ()
    in
      if inCircle (head fst(tabTriangle t1 Ordinal(zero<3))) snd (tabTriangle t1 Ordinal(zero<3)) triangleT2 ||
             inCircle (head fst(tabTriangle t1 Ordinal(un<3))) snd (tabTriangle t1 Ordinal(un<3)) triangleT2 ||
               inCircle (head fst(tabTriangle t1 Ordinal(deux<3))) snd (tabTriangle t1 Ordinal(deux<3)) triangleT2
          then  (tabTriangle t2 Ordinal(zero<3),tabTriangle t2 Ordinal(un<3),tabTriangle t2 Ordinal(deux<3),
                  tabTriangle t1 Ordinal(zero<3),tabTriangle t1 Ordinal(un<3), tabTriangle t1 Ordinal(deux<3)).

(* A modifier car adjT et inCircle prend en 2nd argument un triangle et pas un T *)
(* 2eme problème : findIllegal doit renvoyer 5 edges accompagnés de 4 bool et non pas 6 edges *)


Definition flip (e1:edge) (b1 : bool) (e2:edge) (b2 : bool) (e3:edge) (b3 : bool) (e4:edge) (b4 : bool) 
                                (e5 : edge) :=
  unhookE e5; unhookT e5; 
attachE (e1:edge) (b1 : bool) (e2:edge) (b2 : bool) (e3:edge) (b3 : bool) (e4:edge) (b4 : bool);
attachT (e1:edge) (b1 : bool) (e2:edge) (b2 : bool) (e3:edge) (b3 : bool) (e4:edge) (b4 : bool).



(* Dans makeDelauney faire un test findIllegal et si oui alors faire flip et rappeler 
makeDelauney *)
Fixpoint makeDelauney :=
  if findIllegal is Some(i) then flip i; makeDelauney.

(* Définition à revoir car problème syntaxe et d'appels des fonctions *)

