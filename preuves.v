Require Import Arith.
Require Import EqNat.
Require Import Ring.



(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq path.
From mathcomp Require Import finset zmodp matrix bigop ssralg tuple choice.
From mathcomp Require Import finmap seq finfun matrix ssrnum ssrfun fintype.
From mathcomp Require Import bigop ssralg finset fingroup zmodp poly fingraph.

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Add LoadPath "/Users/haffaf/Desktop/Stage_INRIA/DelaunayTriangulation".
Load Structure_de_donnees_3.



(* -------------------------------------------------------------------- *)
(* Dans cette section, on va prouver que l'orientation des triangles est
   maintenue par les opérations add_point_triangle et flip *)
(* -------------------------------------------------------------------- *)

Section oriented.


(* oriented est le prédicat booléen d'orientation. oriented t tm vaut vrai 
   si le triangle (tm t) est un triplet de points orientés en sens trigo *)
Definition oriented (t : T) (tm :trianglemap) := 
  leftpoint (tm t (Ordinal(zero<3))) (tm t (Ordinal(un<3)))
                                             (tm t (Ordinal(deux<3))) > 0.


(* orientedpostadd_point_triangle prouve que si la tmap contenant t
   ne contient que des triangles oriented alors la tmap obtenue
   post-add_point_triangle ne contiendra que des triangles oriented *)
Lemma orientedpostadd_point_triangle (p:point) (t:T) (tm : trianglemap)
                                        (g:graph) (pm :pointmap) :
forall nomt:T, oriented t tm
         -> if add_point_triangle (p:point) (t:T) (tm : trianglemap)
                                           (g:graph) (pm :pointmap)
    is Some (g', tm') then forall t1:T, oriented t1 tm'
                 else oriented t tm.
Proof.
rewrite /=.
move=>t0 Htm_oriented.
rewrite /add_point_triangle.






(* orientedpostflip prouve que si la tmap contenant t1 et t2 ne contient 
   que des triangles oriented et si il faut flipper alors la tmap obtenue 
   post-flip ne contiendra que des triangles oriented *)
Lemma orientedpostflip (tm: trianglemap)  (ptext1 : point) (ptext2 : point)
                           (t1:T) (t2 :T) (g:graph) (pm: pointmap) :
forall t:T, oriented t tm -> (oriented t1 tm)
 -> (oriented t2 tm) -> isDelaunayLocal t1 t2 tm == false
  -> if flip (tm: trianglemap) (ptext1 : point) 
                                  (ptext2 : point) (t1:T) (t2 :T) (g:graph)
                                     (pm: pointmap) is Some (g',tm') then
        forall tt:T, oriented tt tm'
     else (oriented t1 tm) && (oriented t2 tm).
Proof.


End oriented.

