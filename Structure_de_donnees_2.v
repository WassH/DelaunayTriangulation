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


Section gensym.

Open Scope fmap_scope.

Definition E := nat.

Definition pre_newname (e : {fset nat}) : {n : nat | n \notin e}.
Proof.
exists (\max_(i : e) val i + 1).
set u := _ + 1; apply/negP => abs; move/negP: (ltnn u); apply.
move: abs; rewrite /u addn1 => abs; rewrite ltnS.
apply: (leq_bigmax [` abs ]%fset).
Qed.

Definition newname (e : {fset nat}) := val (pre_newname e).

Lemma new_nameP e : newname e \notin e.
Proof. rewrite /newname; apply: (@valP _ [pred n | n \notin e]). Qed.

End gensym.

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

Definition point2R1 (p: point) : R :=
  p (Ordinal zero<1) (Ordinal(zero<2)).


Definition point2R2 (p: point) : R :=
  p (Ordinal zero<1) (Ordinal(un<2)).



Definition T := nat.


Open Local Scope type_scope.
Definition triangle := (E*bool)^3.

Definition edgemap := {fmap E -> point^2}.
Definition edgetmap := {fsfun x: E => fset0 :{fset T}}.
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

(* etmprop1 permet de dire que les aretes d'un triangle sont dans edgetmap *)
Definition etmprop1 (etm :edgetmap) (t : triangle) :=
  forall i :'I_3, fst (t i) \in finsupp etm.


(* etmap_prop1 dit que toutes les arêtes de tous les triangles sont dans edgetmap *)
Definition etmap_prop1 (etm : edgetmap) (tm : trianglemap) :=
  forall i : nat, forall h : i \in tm, etmprop1 etm tm.[h].


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

(* triangleprop3 dit que tout triangle dans edgetmap est dans trianglemap *)
Definition triangleprop3 (etm : edgetmap) (tm : trianglemap) :=
  forall e (ep : e \in finsupp etm) t (tp : t \in etm e),    t \in tm.


Definition edge2point1 (e:E) (em : edgemap) (preuve : e \in em): point :=
  em.[preuve] (Ordinal(zero<2)).


Definition edge2point2 (e:E) (em : edgemap) (preuve : e \in em): point :=
  em.[preuve] (Ordinal(un<2)).


Definition head (e:E) (em : edgemap) (preuve : e \in em) (b:bool) : point :=
  if b==true then edge2point2 preuve else edge2point1 preuve.


Definition tail (e:E) (em : edgemap) (preuve : e \in em) (b:bool) : point :=
  if b==true then edge2point1 preuve else edge2point2 preuve.

Definition triangle2edges (t1: T) (tm : trianglemap) (preuve : t1 \in tm) : {ffun 'I_3 -> E} :=
  [ffun Ord : 'I_3 => fst(tm.[preuve] Ord)].



(* adjE dit si 2 edges sont adjacents *)
Definition adjE (e1: E) (e2 :E) (em :edgemap) (preuve1 : e1 \in em) (preuve2 : e2 \in em) : bool :=
  (tail preuve1 true == tail preuve2 true) && (tail preuve1 true == tail preuve2 true)
         || (tail preuve1 false == tail preuve2 true) && (tail preuve1 false == tail preuve2 true).



(*adjT dit si 2 triangles sont adjacents*)
Definition adjT (t1: T) (t2: T) (tm : trianglemap) (em:edgemap) (preuvetmap : tmap_prop1 em tm) 
   (preuve1 : t1 \in tm) (preuve2 : t2 \in tm): bool :=
   #|([set p : ('I_3*'I_3)| adjE  (preuvetmap t1 preuve1 p.1) (preuvetmap t2 preuve2 p.2) == true])| !=0.



Open Local Scope ring_scope.

(* Définition de inCircle, RMQ : si un point est sur le cercle circonscrit alors il n'est pas inCircle *)
Definition inCircle (p1 : point) (em : edgemap) (t1: T) (tm : trianglemap) (preuve : t1 \in tm)
                               (preuvetmap : tmap_prop1 em tm): bool :=
  let M1 := \col_(j < 4) if j==0 then point2R1 (edge2point1 (preuvetmap t1 preuve (Ordinal(zero<3))))
                         else if  j==1 then point2R1 (edge2point1 (preuvetmap t1 preuve (Ordinal (un<3))))
                         else if  nat_of_ord j==2 then point2R1 (edge2point1 (preuvetmap t1 preuve (Ordinal (deux<3))))
                         else point2R1 p1 in
  let M2 := \col_(j < 4) if j==0 then point2R2 (edge2point1 (preuvetmap t1 preuve (Ordinal (zero<3))))
                         else if  j==1 then point2R2 (edge2point1 (preuvetmap t1 preuve (Ordinal (un<3))))
                         else if  nat_of_ord j==2 then point2R2 (edge2point1 (preuvetmap t1 preuve (Ordinal (deux<3))))
                         else point2R2 p1 in
  let M3 := \col_(j < 4) if j==0 then (point2R1 (edge2point1 (preuvetmap t1 preuve (Ordinal (zero<3)))))^+2 + (point2R2 (edge2point1 (preuvetmap t1 preuve (Ordinal (zero<3)))))^+2
                         else if j==1 then (point2R1 (edge2point1 (preuvetmap t1 preuve (Ordinal (un<3)))))^+2 + (point2R2 (edge2point1 (preuvetmap t1 preuve (Ordinal (un<3)))))^+2
                         else if  nat_of_ord j==2 then (point2R1 (edge2point1 (preuvetmap t1 preuve (Ordinal (deux<3)))))^+2 + (point2R2 (edge2point1 (preuvetmap t1 preuve (Ordinal (deux<3)))))^+2
                         else (point2R1 p1)^+2 + (point2R2 p1)^+2 in
  let M4 := \col_(j < 4) 1 in
  let M := row_mx (row_mx M1 M2) (row_mx M3 M4) in if \det M > 0 then true else false.


(* La fonction isDelauneyLocal va prendre 2 triangles et va renvoyer un bool qui vaudra true si
 la construction des 2 triangles est de Delauney *)
Definition isDelaunayLocal (em :edgemap) (t1: T) (tm : trianglemap) (preuve1 : t1 \in tm) (t2: T) 
                                (preuve2 : t2 \in tm) (preuvetmap : tmap_prop1 em tm) : bool :=
  if (inCircle (tail (preuvetmap t1 preuve1 (Ordinal (zero<3))) (snd((tm.[preuve1]%fmap (Ordinal(zero<3)))))) preuve2 preuvetmap
                  == false
      && inCircle (tail (preuvetmap t1 preuve1 (Ordinal (un<3))) (snd((tm.[preuve1]%fmap (Ordinal(un<3)))))) preuve2 preuvetmap
                  == false
      && inCircle (tail (preuvetmap t1 preuve1 (Ordinal (deux<3))) (snd((tm.[preuve1]%fmap (Ordinal(deux<3)))))) preuve2 preuvetmap
                  == false)
              then true
              else false.


(* Fonction bind qui va permettre de faire plusieurs opérations à la suite dans les fonctions qui suivent *)
(*Definition bind := 

 Notation ";" := bind ...

 *)

(* Fonction unhook qui détache une arete commune a deux triangles et qui va etre utile pour 
l'opération de flip *)

Definition unhookE (e: E) (em : edgemap)  :=
  em.[~ e].

(* Changer unhookEetm pour faire en sorte que etm e renvoie fset0 *)
(* Definition unhookEetm (e: E) (etm : edgetmap)  :=
  etm.[~ e].
 *)

Definition unhookT (t1:T) (tm : trianglemap) :=
  tm.[~ t1].

Definition attachE (p1:point) (p2 : point) (em : edgemap) := 
  let f := [ffun x:'I_2 => if x==0 then p1 else p2] in
  em.[(newname (domf em))<- f].

(* 
Definition attachT (t1: triangle) (tm : trianglemap) := 
  tm.[(newname (domf tm)) <- t1].

 *)

(* Fonctions inTriangle, inHull, add_point_triangle, add_point_out, add_edge et add_triangle *)


(* La fonction inTriangle va dire si un point donné est à l'intérieur d'un triangle donné *)
Definition inTriangle  (tmap : trianglemap) (em : edgemap) (p:point) (t:T) (preuveT : t \in tmap)
                              (preuvetmap : tmap_prop1 em tmap) : bool :=
  
  let M11 := \col_(j < 3) if j==0 then point2R1 p
                         else if j==1 then point2R1 (tail (preuvetmap t preuveT (Ordinal (zero<3))) (snd (tmap.[preuveT]%fmap (Ordinal (zero<3)))))
                         else point2R1 (head (preuvetmap t preuveT (Ordinal (zero<3))) (snd (tmap.[preuveT]%fmap (Ordinal (zero<3))))) in

  let M12 := \col_(j < 3) if j==0 then point2R2 p
                         else if j==1 then point2R2 (tail (preuvetmap t preuveT (Ordinal (zero<3))) (snd (tmap.[preuveT]%fmap (Ordinal (zero<3)))))
                         else point2R2 (head (preuvetmap t preuveT (Ordinal (zero<3))) (snd (tmap.[preuveT]%fmap (Ordinal (zero<3))))) in

  let M13 := \col_(j < 3) 1 in 
     let M1 := row_mx (row_mx M11 M12) M13 in

  let M21 := \col_(j < 3) if j==0 then point2R1 p
                         else if j==1 then point2R1 (tail (preuvetmap t preuveT (Ordinal (un<3))) (snd (tmap.[preuveT]%fmap (Ordinal (un<3)))))
                         else point2R1 (head (preuvetmap t preuveT (Ordinal (un<3))) (snd (tmap.[preuveT]%fmap (Ordinal (un<3))))) in

  let M22 := \col_(j < 3) if j==0 then point2R2 p
                         else if j==1 then point2R2 (tail (preuvetmap t preuveT (Ordinal (un<3))) (snd (tmap.[preuveT]%fmap (Ordinal (un<3)))))
                         else point2R2 (head (preuvetmap t preuveT (Ordinal (un<3))) (snd (tmap.[preuveT]%fmap (Ordinal (un<3))))) in

  let M23 := \col_(j < 3) 1 in 
      let M2 := row_mx (row_mx M21 M22) M23 in
  
  let M31 := \col_(j < 3) if j==0 then point2R1 p
                         else if j==1 then point2R1 (tail (preuvetmap t preuveT (Ordinal (deux<3))) (snd (tmap.[preuveT]%fmap (Ordinal (deux<3)))))
                         else point2R1 (head (preuvetmap t preuveT (Ordinal (deux<3))) (snd (tmap.[preuveT]%fmap (Ordinal (deux<3))))) in

  let M32 := \col_(j < 3) if j==0 then point2R2 p
                         else if j==1 then point2R2 (tail (preuvetmap t preuveT (Ordinal (deux<3))) (snd (tmap.[preuveT]%fmap (Ordinal (deux<3)))))
                         else point2R2 (head (preuvetmap t preuveT (Ordinal (deux<3))) (snd (tmap.[preuveT]%fmap (Ordinal (deux<3))))) in

  let M33 := \col_(j < 3) 1 in 
      let M3 := row_mx (row_mx M31 M32) M33 in


    if ((\det M1)*(\det M2)>0) && ((\det M2)*(\det M3) >0)  then true
    else false.



(* La fonction inHull va dire si un point donné est à l'intérieur de l'enveloppe convexe
  dans ce cas elle retourne true ou sinon elle retourne false. Elle est construite 
  grâce à inTriangle*)
Definition inHull (tmap : trianglemap) (em : edgemap) (p:point) 
                          (preuvetmap : tmap_prop1 em tmap) : bool := 
  let dom1 := domf tmap in 
  [exists (i: dom1| true), inTriangle p (valP i) preuvetmap].


(* tr2pt va prendre un triangle et renvoyer pour un ordinal donné le point associé *)
Definition tr2pt (em : edgemap) (tmap : trianglemap) (preuvetmap : tmap_prop1 em tmap) (t1:T) (preuve1 : t1\in tmap) 
                          : 'I_3 -> point :=
  fun i : 'I_3 => head (preuvetmap t1 preuve1 i) (snd (tmap.[preuve1]%fmap i)).


(* edge2index va prendre un E, un T et des preuves et va fournir un 'I_3 qui est l'index de l'arete dans ce triangle *)
Definition edge2index (e:E) (t:T) (em : edgemap) (tmap : trianglemap) (preuvetmap : tmap_prop1 em tmap)
                              (preuve1 : t\in tmap) : 'I_3 :=
  if fst(tmap.[preuve1]%fmap (Ordinal(zero<3))) == e then Ordinal(zero<3)
  else if fst(tmap.[preuve1]%fmap (Ordinal(un<3))) == e then Ordinal(un<3)
  else Ordinal(deux<3).

Check fun (etm : edgetmap) (x : {y : {z : E | (z \in finsupp etm) } | ( #|{:etm (val y)}|==2 ) } ) => 
        (valP x : #| {: etm (val (val x))}|==2 ).

(* La fonction findInTriangle va (si c'est le cas) trouver le triangle dans lequel est 
  le point p *)
Definition findInTriangle 



(* Fonction qui va supprimer le triangle extérieur et qui va rajouter les 3 triangles 
  intérieurs et les 3 edges intérieurs *)
Definition add_point_triangle (t:T) (preuve1 : t \in tmap) (tm : trianglemap) (em : edgemap)
           (etm : edgetmap) (p:point) (preuvetmap : tmap_prop1 em tmap) := 
    unhookT t; attachE p (tr2pt em tm preuvetmap preuve (Ordinal(zero<3))) em;
               attachE p (tr2pt em tm preuvetmap preuve (Ordinal(un<3))) em;
               attachE p (tr2pt em tm preuvetmap preuve (Ordinal(deux<3))) em;

let edge1 := [ffun x:'I_2 => if x==0 then p else tr2pt em tm preuvetmap preuve (Ordinal(zero<3))] in
let edge2 := [ffun x:'I_2 => if x==0 then p else tr2pt em tm preuvetmap preuve (Ordinal(un<3))] in
let edge3 := [ffun x:'I_2 => if x==0 then p else tr2pt em tm preuvetmap preuve (Ordinal(deux<3))] in


(* Il faut remplacer Ordinal(zero<3) dans les 3 triangles qui suivent par l'index de l'edge qui relie 
le point 0 : (tr2pt em tm preuvetmap preuve (Ordinal(zero<3)))
 et le point 2 :attachE p (tr2pt em tm preuvetmap preuve (Ordinal(deux<3))) em
et de même pour Ordinal(un<3) et Ordinal(deux<3) *)

    let triangle1 := fun x:'I_3 => if x==0 then 
          if em.[preuvetmap (triangle2edges ... zero)] == (créer le edge de 0 à 2)
                                   || em.[preuvetmap (triangle2edges ... zero)] == (créer le edge de 2 à 0) 
                                              then (fst(tm.[preuve1]%fmap (Ordinal(zero<3)))]
                                                    ,snd(tm.[preuve1]%fmap (Ordinal(zero<3))))  
          else if em.[preuvetmap (triangle2edges ... un)] == (créer le edge de 0 à 2)
                                   || em.[preuvetmap (triangle2edges ... zero)] == (créer le edge de 2 à 0) 
                                              then (fst(tm.[preuve1]%fmap (Ordinal(un<3)))]
                                                    ,snd(tm.[preuve1]%fmap (Ordinal(un<3))))  
          else if em.[preuvetmap (triangle2edges ... deux)] == (créer le edge de 0 à 2)
                                   || em.[preuvetmap (triangle2edges ... zero)] == (créer le edge de 2 à 0) 
                                              then (fst(tm.[preuve1]%fmap (Ordinal(deux<3)))]
                                                    ,snd(tm.[preuve1]%fmap (Ordinal(deux<3))))  
                               else if x==1 then (\max_(i : domf em) (val i)-2, false)
                               else (\max_(i : domf em) val i, true) in
               attachT triangle1 tm;

(* Faire de même qu'au dessus pour triangle2 et triangle3 *)
  let triangle2 := fun x:'I_3 => if x==0 then (fst(tm.[preuve1]%fmap (Ordinal(un<3)))
                                                    ,snd(tm.[preuve1]%fmap (Ordinal(un<3)))) 
                               else if x==1 then  (\max_(i : domf em) (val i)-1,false)
                               else (\max_(i : domf em) (val i)-2,true) in
               attachT triangle2 tm;

  let triangle3 := fun x:'I_3 => if x==0 then (fst(tm.[preuve1]%fmap (Ordinal(deux<3)))
                                                    ,snd(tm.[preuve1]%fmap (Ordinal(deux<3))))
                               else if x==1 then  (\max_(i : domf em) val i, false)
                               else (\max_(i : domf em) (val i)-1, true) in
               attachT triangle3 tm;



Definition add_point_out := .







Definition change_ord (T : choiceType)(s : {fset T}) (h : #|{:s}| == 2) (x : 'I_2)
  : 'I_(#|{:s}|).
rewrite (eqP h); exact x.
Defined.


(*
Definition findIllegal (em : edgemap) (etm : edgetmap) (tmap : trianglemap) 
                    (preuvetmap : tmap_prop1 em tmap)
            (trp : forall e (ep : e \in finsupp etm) t (tp : t \in etm e),
                    triangleprop3 tmap ep tp): bool.
set X : {fset E} :=[fset x | x in finsupp etm & (#|{:etm x}|==2)]%fset.
have f_dummy : {: X} -> bool.
  rewrite /X. move => x.
have : (val x \in finsupp etm) && (#|{:etm (val x)}|==2).
Search _ (_ \in [fset _ | _ in _ & _ ])%fset.
have := valP x.
move/imfsetP => /= [v pv ->]. exact: pv.
move/andP => [A C].
set S' := etm (val x).
  set t1 := @enum_val  [finType of S'] xpredT (change_ord C
            (Ordinal(zero<2))).
 set t2 : {: S'} :=@enum_val  [finType of S'] xpredT (change_ord C
            (Ordinal(un<2))).
have pt1_try : val t1 \in S'.
apply: (valP t1).
have t1tm : val t1 \in tmap.
apply: trp _ A _ pt1_try.
have : (#|{:etm (val x)}|==2).
case: x => v /imfsetP [v' pv ->].
rewrite /=.
clear trp.
apply: in_imfset.
move => toto; exact:true.

have f : {y : X | #|{:etm (val y)}| == 2} -> bool.
  move => x.
  set S' : {fset T} := etm (val (val x)).
  set t1 := @enum_val  [finType of S'] xpredT (change_ord (valP x)
            (Ordinal(zero<2))).
 set t2 : {: S'} :=@enum_val  [finType of S'] xpredT (change_ord (valP x)
            (Ordinal(un<2))).

have : val t2 \in S'.

   exact:valP.
have : val x \in finsupp etm.
    *)

Definition toto (etm : edgetmap) (x : {: [fset x | x in finsupp etm & 
(#|{:etm x}|==2)]%fset }) :
   val x \in finsupp etm.
have:= valP x.
rewrite in_fsetE 2!inE => /andP [it _]; exact: it.
Defined.

(* La définition de edge2stuff qui renvoit pour un edge adjacent les 4 points et les 2 triangles et les 2
preuves que les triangles sont dans tmap  *)
Definition edge2stuff (e : E) (em : edgemap) (etm : edgetmap) (tmap : trianglemap) 
                    (preuvetmap : tmap_prop1 em tmap) (preuvetriprop3 : triangleprop3 etm tmap) 
                        (preuve : e \in finsupp etm) (preuve2 : #|{:etm e}|==2) :=
    
   let S := etm (e) in
    let t1 := @enum_val  [finType of S] xpredT (change_ord (preuve2)
            (Ordinal(zero<2)))in
    let t2 := @enum_val  [finType of S] xpredT (change_ord (preuve2)
            (Ordinal(un<2)))in 

    let i1 := @edge2index (e) (val t1) em tmap preuvetmap  (preuvetriprop3 (e) (preuve) (val t1) (valP t1)) in
    let i2 := @edge2index (e) (val t2) em tmap preuvetmap  (preuvetriprop3 (e) (preuve) (val t2) (valP t2))  in
    let ptext1 := @tr2pt em tmap preuvetmap (val t1) (preuvetriprop3 (e) (preuve) (val t1) (valP t1)) (addOrd3 i1 (Ordinal un<3)) in
    let ptext2 := @tr2pt em tmap preuvetmap (val t2) (preuvetriprop3 (e) (preuve) (val t2) (valP t2)) (addOrd3 i2 (Ordinal un<3)) in
    let ptin1 := @tr2pt em tmap preuvetmap (val t1) (preuvetriprop3 (e) (preuve) (val t1) (valP t1)) i1 in
    let ptin2 := @tr2pt em tmap preuvetmap (val t2) (preuvetriprop3 (e) (preuve) (val t2) (valP t2)) i2 in 
         if true then  (e, ptext1, ptext2, ptin1, ptin2, t1, t2, (preuvetriprop3 (e) (preuve) (val t1) (valP t1)),
                 (preuvetriprop3 (e) (preuve) (val t2) (valP t2)))
         else (e, ptext1, ptext2, ptin1, ptin2, t1, t2, (preuvetriprop3 (e) (preuve) (val t1) (valP t1)),
                 (preuvetriprop3 (e) (preuve) (val t2) (valP t2))).


Definition titi (etm : edgetmap): 
  [fset x | x in finsupp etm & #|{: etm x}| == 2]%fset ->
  {y : [fset x | x in finsupp etm & #|{: etm x}| == 2]%fset
   | #|{:etm (val y)}| == 2}. 
move => x'; exists x'.
by case: x' => v /=; rewrite in_fsetE inE; case/andP.
Defined.



(* findIllegal fait appel aux fonctions tr2pt et edge2index pour récupérer les 4 points *)

Definition illegaltupleprop (tmap: trianglemap)
    (p : E * point * point * point * point * T * T) :=
   let '(x, ptext1, ptext2, ptin1, ptin2, t1, t2 (* ,
                   preuvetriprop3  (toto (val x)) (valP t1),
                  preuvetriprop3  (toto (val x)) (valP t2) *)) := p in
       t1 \in tmap.

Section findIllegal.

Variables  (em : edgemap) (etm : edgetmap) (tmap : trianglemap) 
 (preuvetmap : tmap_prop1 em tmap) (preuvetriprop3 : triangleprop3 etm tmap).

Let  X := [fset x in finsupp etm | (#|{:etm x}|==2)]%fset.

Let f (* : X -> option ({y : X | #|{: etm (val y)}| == 2} * point * point *
                 point * point * T * T) *) := fun x' : {: X } =>
    let x :=  titi x' : {y : X | #|{:etm (val y)}| == 2} in
    (* S est le fset T contenant les 2 noms de triangles t1 et t2 adjacents en l'edge x *)
    let S := etm (val(val x)) in
    let t1 := @enum_val  [finType of S] xpredT (change_ord (valP x)
            (Ordinal(zero<2)))in
    let t2 := @enum_val  [finType of S] xpredT (change_ord (valP x)
            (Ordinal(un<2)))in

    let i1 := @edge2index (val (val x)) (val t1) em tmap preuvetmap
                          (preuvetriprop3 (toto (val x)) (valP t1)) in
    let i2 := @edge2index (val (val x)) (val t2) em tmap preuvetmap  (preuvetriprop3  (toto (val x)) (valP t2))  in
    let ptext1 := @tr2pt em tmap preuvetmap (val t1) (preuvetriprop3  (toto (val x)) (valP t1)) (addOrd3 i1 (Ordinal un<3)) in
    let ptext2 := @tr2pt em tmap preuvetmap (val t2) (preuvetriprop3  (toto (val x)) (valP t2)) (addOrd3 i2 (Ordinal un<3)) in
    let ptin1 := @tr2pt em tmap preuvetmap (val t1) (preuvetriprop3  (toto (val x)) (valP t1)) i1 in
    let ptin2 := @tr2pt em tmap preuvetmap (val t2) (preuvetriprop3  (toto (val x))  (valP t2)) i2 in 
      if (@inCircle ptext2 em (val t1) tmap (preuvetriprop3  (toto (val x)) (valP t1)) preuvetmap)==true 
                      then  Some (exist (illegaltupleprop tmap)
                        (val (val x), ptext1, ptext2, ptin1, ptin2, val t1, val t2 (* ,
                   preuvetriprop3  (toto (val x)) (valP t1),
                  preuvetriprop3  (toto (val x)) (valP t2) *))
                   (preuvetriprop3  (toto (val x)) (valP t1)))else None.

Let res := [fset f x | x in {: X} & f x != None]%fset.

Definition findIllegal := match pick (pred_of_simpl (@predT {:res})) with
   Some u => val u | None => None end.


Check (fun (tmap : trianglemap) (x : sig_choiceType (illegaltupleprop 
tmap)) =>
          let '(exist (x, ptext1, ptext2, ptin1, ptin2, t1, t2) _) := x in
          t1).

End findIllegal.


(* J'ai besoin de démontrer à part que les 2 triangles t1 et t2 sont dans tmap 
et je réutiliserai ces preuves dans flip *)


Definition flip (em : edgemap) (tm: trianglemap) (eAdj:E) (ptext1 : point) (ptext2 : point) 
                       (t1:T)  (preuve1 : t1 \in tm) (t2 :T) (preuve2: t2 \in tm) 
                                (preuvetmap : tmap_prop1 em tm):=
unhookE eAdj em; unhookEetm eAdj etm; unhookT t tm1; unhookT t2 tm;  attachE ptext1 ptext2 em;
let triangle1 := fun x:'I_3 => if x==0 then (fst(tm.[preuve1]%fmap (addOrd3 (@edge2index eAdj t1 em tm preuvetmap preuve1) 1))
                                                    ,snd(tm.[preuve1]%fmap (addOrd3 (@edge2index eAdj t1 em tm preuvetmap preuve1) 1)))  
                               else if x==1 then  (\max_(i : domf em) val i, true)
                               else (fst(tm.[preuve2]%fmap (addOrd3 (@edge2index eAdj t2 em tm preuvetmap preuve2) (Ordinal(deux<3))))
                                                    ,snd(tm.[preuve2]%fmap (addOrd3 (@edge2index eAdj t2 em tm preuvetmap preuve2) (Ordinal(deux<3)))))
in let triangle2 := fun x:'I_3 => if x==0 then (fst(tm.[preuve1]%fmap (addOrd3 (@edge2index eAdj t1 em tm preuvetmap preuve1) (Ordinal(deux<3))))
                                                    ,snd(tm.[preuve1]%fmap (addOrd3 (@edge2index eAdj t1 em tm preuvetmap preuve1) (Ordinal(deux<3)))))  
                               else if x==1 then  (fst(tm.[preuve2]%fmap (addOrd3 (@edge2index eAdj t2 em tm preuvetmap preuve2) (Ordinal(un<3))))
                                                    ,snd(tm.[preuve2]%fmap (addOrd3 (@edge2index eAdj t2 em tm preuvetmap preuve2) (Ordinal(un<3)))))
                               else (\max_(i : domf em) val i, false) 

in attachT triangle1 tm; attachT triangle2 tm.



(* Dans makeDelaunay faire un test findIllegal et si oui alors faire flip et rappeler 
makeDelaunay *)
Fixpoint makeDelaunay (em :edgemap) (etm : edgetmap) (tmap : trianglemap) (preuvetmap : tmap_prop1 em tmap) 
                                  (preuvetriprop3 : triangleprop3 etm tmap) :=

  if (findIllegal em etm tmap preuvetmap preuvetriprop3) is Some (x, ptext1, ptext2, ptin1, ptin2, t1, t2,preuve1, preuve2) 
    then  flip (em) (tm) (x) (ptext1) (ptext2) (t1) (preuve1) (t2) (preuve2) (preuvetmap)
  else makeDelaunay em etm tmap preuvetmap ;
  makeDelaunay em etm tmap preuvetmap.
