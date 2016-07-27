Require Import Arith.
Require Import EqNat.
Require Import Ring.
Require Import Bool.

Require Import ZArith.
Require Import Field.


Require Import field_tactics.

(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq fintype.
From mathcomp Require Import finset zmodp matrix bigop ssralg matrix ssrnum.
From mathcomp Require Import finmap seq ssrfun finfun matrix ssrnum ssrfun.
From mathcomp Require Import bigop ssralg finset fingroup zmodp poly fingraph.
From mathcomp Require Import tuple choice path rat.
(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Open Scope ring_scope.

Require Import Structure_de_donnees_3.

Section on_map.


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
Notation "un<5" := (ltn_trans (ltn_trans (ltn_trans (ltnSn 1) (ltnSn 2))
                                 (ltnSn 3)) (ltnSn 4)).
Notation "deux<5" := (ltn_trans (ltn_trans (ltnSn 2) (ltnSn 3)) (ltnSn 4)).
Notation "trois<5" := (ltn_trans (ltnSn 3) (ltnSn 4)).
Notation "quatre<5" := (ltnSn 4).

Open Scope ring_scope.

Variable R : numDomainType.

Variable P : finType.

Definition T := T P.

Check trianglemap.

Definition trianglemap := trianglemap P.

Variable default_triangle : point ^ 3.

Hypothesis leftpoint_default :
  leftpoint (default_triangle (inZp 0))
            (default_triangle (inZp 1))(default_triangle (inZp 2)) > 0.

Definition graph := T -> seq T.

Definition pointmap := pointmap P.




Definition surface_sans_bord (t:T) (tm: trianglemap) (pm : pointmap) :=
  [set nomp : P | (leftpoint (pm nomp) ((tm t) (Ordinal(zero<3)))
                        ((tm t) (Ordinal(un<3))) >0) &&
                  (leftpoint (pm nomp) ((tm t) (Ordinal(un<3)))
                        ((tm t) (Ordinal(deux<3)))>0) &&
                  (leftpoint (pm nomp) ((tm t) (Ordinal(deux<3)))
                        ((tm t) (Ordinal(zero<3)))>0)].


Definition bord1 (t:T) (tm: trianglemap) (pm :pointmap) :=
[set nomp :P | (leftpoint (pm nomp) ((tm t) (Ordinal(zero<3)))
                        ((tm t) (Ordinal(un<3))) == 0)
                 &&  (norm_carre ((tm t) (Ordinal(zero<3))) (pm nomp)
                              <= norm_carre ((tm t) (Ordinal(zero<3)))
                                              ((tm t) (Ordinal(un<3))))
                 && (prod_scal ((tm t) (Ordinal(zero<3))) (pm nomp)
                                    ((tm t) (Ordinal(zero<3)))
                                              ((tm t) (Ordinal(un<3))) >0)].



Definition bord2 (t:T) (tm: trianglemap) (pm :pointmap) :=
[set nomp :P | (leftpoint (pm nomp) ((tm t) (Ordinal(un<3)))
                        ((tm t) (Ordinal(deux<3))) == 0)
                 &&  (norm_carre ((tm t) (Ordinal(un<3))) (pm nomp)
                              <= norm_carre ((tm t) (Ordinal(un<3)))
                                              ((tm t) (Ordinal(deux<3))))
                 && (prod_scal ((tm t) (Ordinal(un<3))) (pm nomp)
                                    ((tm t) (Ordinal(un<3)))
                                              ((tm t) (Ordinal(deux<3))) >0)].


Definition bord3 (t:T) (tm: trianglemap) (pm :pointmap) :=
[set nomp :P | (leftpoint (pm nomp) ((tm t) (Ordinal(deux<3)))
                        ((tm t) (Ordinal(zero<3))) == 0)
                 &&  (norm_carre ((tm t) (Ordinal(deux<3))) (pm nomp)
                              <= norm_carre ((tm t) (Ordinal(deux<3)))
                                              ((tm t) (Ordinal(zero<3))))
                 && (prod_scal ((tm t) (Ordinal(deux<3))) (pm nomp)
                                    ((tm t) (Ordinal(deux<3)))
                                              ((tm t) (Ordinal(zero<3))) >0)].



Definition surface (t:T) (tm: trianglemap) (pm :pointmap) :=
  surface_sans_bord t tm pm :|: bord1 t tm pm :|: bord2 t tm pm
        :|: bord3 t tm pm.

Definition oriented (t : T) (tm :trianglemap) := 
  leftpoint (tm t (inZp 0)) (tm t (inZp 1)) (tm t (inZp 2)) > 0.


(* -------------------------------------------------------------------- *)
(* Dans cette section, on va prouver l'équivalence entre être <<dans>> 
   un triangle et s'écrire comme un barycentre des 3 sommets *)
(* -------------------------------------------------------------------- *)



Lemma eq_bar (t:T) (tm : trianglemap) (p:point) 
  (toriented  : (leftpoint ((tm t) (Ordinal(zero<3))) ((tm t) (Ordinal(un<3))) 
                  ((tm t) (Ordinal(deux<3))) > 0)) :
   (leftpoint p ((tm t) (Ordinal(zero<3))) ((tm t) (Ordinal(un<3))) 
                   > 0)
&& (leftpoint p ((tm t) (Ordinal(un<3))) ((tm t) (Ordinal(deux<3))) 
                   > 0)
&& (leftpoint p ((tm t) (Ordinal(deux<3))) ((tm t) (Ordinal(zero<3))) 
                  > 0)
<-> exists k1, exists k2, exists k3,
 (point2R1 p = k1*point2R1 ((tm t) (Ordinal(zero<3)))
                + k2*point2R1 ((tm t) (Ordinal(un<3)))
                + k3*point2R1 ((tm t) (Ordinal(deux<3)))) /\
 (point2R2 p = k1*point2R2 ((tm t) (Ordinal(zero<3)))
                + k2*point2R2 ((tm t) (Ordinal(un<3)))
                + k3*point2R2 ((tm t) (Ordinal(deux<3))))
            /\ (k1+k2+k3 ==1)
            /\ k1 > 0 /\ k2 > 0 /\ k3 > 0.
Proof.
  move: toriented; set bd := leftpoint _ _ _ => toriented.
split; last first.
  move=> [k1 [k2 [k3 [H1 H2]]]].
  move:H2.
  move=> [H2 H3].
  move:H3.
  move=> [H3 H4].
  move:H4.
  move=> [H4 H5].
  move:H5.
  move=> [H5 H6].
  rewrite /leftpoint.
  rewrite H1 H2.
  set u1 := \det _.
  have u1q : u1 = k3 * bd.
  rewrite /u1.
  rewrite (expand_det_row _ (Ordinal (deux<3))).
  rewrite big_ord_recl.
  rewrite mxE. rewrite //=.
  rewrite big_ord_recl.
  rewrite big_ord_recl.
  rewrite big_ord0.
  rewrite mxE. rewrite //=.
  rewrite mxE. rewrite //=.
  
  rewrite /cofactor.
  rewrite !//=.
  
  rewrite (expand_det_row _ (Ordinal (un<2))).
  rewrite big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor.
  rewrite !//=.

  rewrite big_ord_recl.
  rewrite big_ord0.
  rewrite !mxE !//=.
rewrite /row' /col'.
Locate "\matrix_".
set F := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F i j = (F ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

set F2 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F2 i j = (F2 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.


  rewrite (expand_det_row _ (Ordinal (un<2))).
  rewrite big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor.
  rewrite !//=.

rewrite /row' /col'.

set F3 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F3 i j = (F3 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

  rewrite big_ord_recl.
  rewrite big_ord0.
  rewrite (expand_det_row _ (Ordinal (un<2))).
  rewrite big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor.
  rewrite !//=.

set F4 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F4 i j = (F4 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

  rewrite big_ord_recl.
  rewrite big_ord0.
  rewrite !mxE !//=.

rewrite /col' /row'.
set F5 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F5 i j = (F5 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

set F6 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F6 i j = (F6 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

(* Expansion de bd *)

rewrite /bd /leftpoint.
rewrite (expand_det_row _ (Ordinal (deux<3))).
rewrite big_ord_recl.
rewrite !mxE !//=.
rewrite /cofactor.
rewrite (expand_det_row _ (Ordinal (un<2))).
rewrite big_ord_recl.
rewrite !mxE !//=.
rewrite /cofactor.

rewrite /row' /col'.
set F7 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F7 i j = (F7 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

rewrite big_ord_recl big_ord0.
rewrite !mxE !//=.
set F8 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F8 i j = (F8 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

rewrite big_ord_recl.
  rewrite (expand_det_row _ (Ordinal (un<2))).
  rewrite big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor.
  rewrite !//=.
rewrite big_ord0 big_ord_recl.
rewrite !mxE !//=.

rewrite /col' /row'.
set F9 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F9 i j = (F9 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

rewrite big_ord_recl big_ord0.
rewrite !mxE !//=.

set F10 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F10 i j = (F10 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

  rewrite (expand_det_row _ (Ordinal (un<2))).
  rewrite big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor.
  rewrite !//=.
rewrite !mxE !//=.

rewrite /col' /row'.
set F11 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F11 i j = (F11 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

rewrite big_ord_recl big_ord0.
rewrite !mxE !//=.
set F12 := (X in matrix_of_fun _ X).
rewrite (_ : \matrix_(i, j) F12 i j = (F12 ord0 ord0)%:M);[
rewrite det_scalar1 |]; last first.
apply/matrixP.
move => [[ | n] pn ]; last by [].
move => [[ | m] pm ]; last by [].
rewrite !mxE.
have-> : (Ordinal pn = Ordinal pm) by apply val_inj.
rewrite eqxx /= mulr1n.
by have-> : (Ordinal pm = ord0) by apply val_inj.

rewrite !//=.
rewrite /bump !//=.
rewrite /F6. rewrite 4!mxE /=.
rewrite /F. rewrite 4!mxE /=.
rewrite /F2. rewrite 4!mxE /=.
rewrite /F4. rewrite 4!mxE /=.
rewrite /F5. rewrite 4!mxE /=.
rewrite /F7. rewrite 4!mxE /=.
rewrite /F8. rewrite 4!mxE /=.
rewrite /F9. rewrite 4!mxE /=.
rewrite /F12. rewrite 4!mxE /=.
rewrite /F11. rewrite 4!mxE /=.
rewrite /F3. rewrite 4!mxE /=.
rewrite /F10. rewrite 4!mxE /=.

rewrite !mulN1r !addr0 !//=.
rewrite !expr2 !//=.
rewrite !exprD !expr1 !expr0 !//= !mulr1 !//= .
rewrite !mulN1r !//=.
rewrite !mul1r.
rewrite !mulrN1.

set a := point2R1 (tm t (Ordinal zero<3)).
set b := point2R2 (tm t (Ordinal zero<3)).
set c := point2R1 (tm t (Ordinal un<3)).
set d := point2R2 (tm t (Ordinal un<3)).
set e := point2R1 (tm t (Ordinal deux<3)).
set f := point2R2 (tm t (Ordinal deux<3)).



rat_field.




  (* rewrite lift0.
  rewrite /lift !//=.
  rewrite 
rewrite w9 /w7.




rewrite -[X in _ (Ordinal _) X](_ : _ = the_guy).
(* (_ : _ = (lshift 1 (ord0 : 'I_2))). *)
set w := (X in row_mx X _).
set w2 := cofactor _ _ _.

rewrite row_mxEl.

(* utiliser big_nat_recl *)


  set u2 := \det _.

  rewrite (expand
  rewrite /determinant.
  to_rat_type.
  rat_field.




exists (leftpoint (tm t (Ordinal(zero<3))) (tm t (Ordinal(un<3)))
                                                  (tm t (Ordinal(deux<3)))).
exists (leftpoint (tm t (Ordinal(zero<3))) (tm t (Ordinal(un<3))) p).
exists (leftpoint (tm t (Ordinal(un<3))) (tm t (Ordinal(deux<3))) p).
exists (leftpoint (tm t (Ordinal(deux<3))) (tm t (Ordinal(zero<3))) p).
rewrite /leftpoint.
to_rat_type.
 *)



Lemma oriented_triangles_after_flip (p:point) (t :T) (tm: trianglemap)  
 (toriented  : (leftpoint ((tm t) (Ordinal(zero<3))) ((tm t) (Ordinal(un<3))) 
                  ((tm t) (Ordinal(deux<3))) > 0)) :
   (leftpoint p ((tm t) (Ordinal(zero<3))) ((tm t) (Ordinal(un<3))) 
                   > 0)
&& (leftpoint p ((tm t) (Ordinal(un<3))) ((tm t) (Ordinal(deux<3))) 
                   > 0)
&& (leftpoint p ((tm t) (Ordinal(deux<3))) ((tm t) (Ordinal(zero<3))) 
                  > 0) -> inCircle p t tm ==false.
Proof.
rewrite /inCircle.
case info: (Num.lt 0
    (\det (\matrix_(i<4, j<4) if i ==0 then if j==0 then
                                       point2R1 (triangle2points t tm (Ordinal (zero<3)))
                                           else if j==1 then
                                       point2R2 (triangle2points t tm (Ordinal (zero<3)))
                                           else if nat_of_ord j==2 then 
                         (point2R1 (triangle2points t tm (Ordinal (zero<3))))^+2
                            + (point2R2 (triangle2points t tm (Ordinal (zero<3))))^+2
                                         else 1
                           else if i ==1 then if j==0 then
                                     point2R1 (triangle2points t tm (Ordinal (un<3)))
                                         else if j==1 then
                                     point2R2 (triangle2points t tm (Ordinal (un<3)))
                                         else if nat_of_ord j==2 then 
                         (point2R1 (triangle2points t tm (Ordinal (un<3))))^+2
                            + (point2R2 (triangle2points t tm (Ordinal (un<3))))^+2
                                         else 1
                           else if nat_of_ord i ==2 then if j==0 then
                                     point2R1 (triangle2points t tm (Ordinal (deux<3)))
                                         else if j==1 then
                                     point2R2 (triangle2points t tm (Ordinal (deux<3)))
                                         else if nat_of_ord j==2 then 
                         (point2R1 (triangle2points t tm (Ordinal (deux<3))))^+2
                            + (point2R2 (triangle2points t tm (Ordinal (deux<3))))^+2
                                         else 1
                           else if j==0 then
                                     point2R1 p
                                         else if j==1 then
                                     point2R2 p
                                         else if nat_of_ord j==2 then 
                                     (point2R1 p)^+2 + (point2R2 p)^+2 
                                         else 1))); last first.
  by [].
rewrite <-info.
rewrite {info}.
rewrite eq_bar; last first.
  by [].
move=> [k1 [k2 [k3 [H1 H2]]]].
move:H2.
move=> [H2 H3].
move:H3.
move=> [H3 H4].
move:H4.
move=> [H4 H5].
move:H5.
move=> [H5 H6].

have hyp: (\det (\matrix_(i<4, j<4) (if i == 0
                                      then
                                       if j == 0
                                       then
                                        point2R1
                                          ((triangle2points t tm)
                                            (Ordinal zero<3))
                                       else
                                        if j == 1
                                        then
                                         point2R2
                                           ((triangle2points t tm)
                                            (Ordinal zero<3))
                                        else
                                         if nat_of_ord j == 2
                                         then
                                          point2R1
                                            ((triangle2points t tm)
                                            (Ordinal zero<3)) ^+ 2 +
                                          point2R2
                                            ((triangle2points t tm)
                                            (Ordinal zero<3)) ^+ 2
                                         else 1
                                      else
                                       if i == 1
                                       then
                                        if j == 0
                                        then
                                         point2R1
                                           ((triangle2points t tm)
                                            (Ordinal un<3))
                                        else
                                         if j == 1
                                         then
                                          point2R2
                                            ((triangle2points t tm)
                                            (Ordinal un<3))
                                         else
                                          if nat_of_ord j == 2
                                          then
                                           point2R1
                                            ((triangle2points t tm)
                                            (Ordinal un<3)) ^+ 2 +
                                           point2R2
                                            ((triangle2points t tm)
                                            (Ordinal un<3)) ^+ 2
                                          else 1
                                       else
                                        if nat_of_ord i == 2
                                        then
                                         if j == 0
                                         then
                                          point2R1
                                            ((triangle2points t tm)
                                            (Ordinal deux<3))
                                         else
                                          if j == 1
                                          then
                                           point2R2
                                            ((triangle2points t tm)
                                            (Ordinal deux<3))
                                          else
                                           if nat_of_ord j == 2
                                           then
                                            point2R1
                                            ((triangle2points t tm)
                                            (Ordinal deux<3)) ^+ 2 +
                                            point2R2
                                            ((triangle2points t tm)
                                            (Ordinal deux<3)) ^+ 2
                                           else 1
                                        else
                                         if j == 0
                                         then point2R1 p
                                         else
                                          if j == 1
                                          then point2R2 p
                                          else
                                           if nat_of_ord j == 2
                                           then
                                            point2R1 p ^+ 2 +
                                            point2R2 p ^+ 2
                                           else 1)) = 

              \det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             ((triangle2points t tm)
                                (Ordinal zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              ((triangle2points t tm)
                                 (Ordinal zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               ((triangle2points t tm)
                                  (Ordinal zero<3)) ^+ 2 +
                             point2R2
                               ((triangle2points t tm)
                                  (Ordinal zero<3)) ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              ((triangle2points t tm) (Ordinal un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               ((triangle2points t tm)
                                  (Ordinal un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                ((triangle2points t tm)
                                   (Ordinal un<3)) ^+ 2 +
                              point2R2
                                ((triangle2points t tm)
                                   (Ordinal un<3)) ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               ((triangle2points t tm)
                                  (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                ((triangle2points t tm)
                                   (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 ((triangle2points t tm)
                                    (Ordinal deux<3)) ^+ 2 +
                               point2R2
                                 ((triangle2points t tm)
                                    (Ordinal deux<3)) ^+ 2
                              else 1
                           else
                            if j == 0
                            then 0
                            else
                             if j == 1
                             then 0
                             else
                              if nat_of_ord j == 2
                              then point2R1 p ^+ 2 + point2R2 p ^+ 2 
                - k1* (point2R1((triangle2points t tm)
                                  (Ordinal zero<3)) ^+ 2 +
                             point2R2
                               ((triangle2points t tm)
                                  (Ordinal zero<3)) ^+ 2)
                - k2* (point2R1((triangle2points t tm)
                                  (Ordinal un<3)) ^+ 2 +
                             point2R2
                               ((triangle2points t tm)
                                  (Ordinal un<3)) ^+ 2)
                - k3* (point2R1((triangle2points t tm)
                                  (Ordinal deux<3)) ^+ 2 +
                             point2R2
                               ((triangle2points t tm)
                                  (Ordinal deux<3)) ^+ 2)
                              else 0))); last first.

rewrite [X in Num.lt 0 X == false]hyp.



Abort.


Lemma orientedunhookT (tm : trianglemap) (g : T -> seq T) t1 :
  (forall t', oriented t' tm) ->
  forall t, oriented t (unhookT default_triangle t1 tm g).2.
Proof.
move => univ_o t.
rewrite /unhookT/=/oriented ffunE; case h : (t == t1); first by [].   
exact: (univ_o t).
Qed.

Lemma orientedattachT (tm : trianglemap)(pm : pointmap) tr :
  (forall t', oriented t' tm) ->
  leftpoint (tr (inZp 0))(tr (inZp 1))(tr (inZp 2)) > 0 ->
  if attachT tr tm pm is Some tm' then 
  forall t, oriented t tm' else true.
Proof.
move => univ_o otr.
case h : (attachT tr tm pm) => [tm' | ] //; move : h.
rewrite /attachT.
case p1q : (point2namefun (tr (Ordinal (ltn0Sn 2))) pm) => [i1 | ] //.
case p2q : (point2namefun (tr (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2)))) pm) =>
              [i2 | ] //.
case p3q : (point2namefun (tr (Ordinal (ltnSn 2))) pm) =>
              [i3 | ] //.
move => [qtm'] t; rewrite -qtm' /oriented.
set new_tr := [ffun x => if _ == _ then _ else _].
rewrite ffunE.
case h : (t == new_tr) => //=.
exact: univ_o.
Qed.

Definition pt_in_triangle  (tm : trianglemap) p t :=
         (p == tm t (Ordinal (ltn0Sn 2)))
      || (p == tm t (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
      || (p == tm t (Ordinal (ltnSn 2))) = true.


Lemma point2indext1t2_correct tm p t1 t2 :
    pt_in_triangle tm p t1 -> ~(pt_in_triangle tm p t2) ->
                                     tm t1 (point2indext1t2 p t1 t2 tm) = p.
Proof.
(* A faire par wassim. *)
rewrite /point2indext1t2 /pt_in_triangle.
case info: (tm t1 (Ordinal zero<3)==p).
case info2 : (p == tm t2 (Ordinal zero<3)) => //=. move/eqP:info=>info.
move=> Ha Hb.
case info3 : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:info3=>info3; rewrite info3.
case info4 : (p == tm t1 (Ordinal un<3)).
  by move/eqP:info4=>info4; rewrite info4.
case info5 : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:info5=>info5; rewrite info5.
case info6 : (p == tm t2 (Ordinal un<3)).
  move:Ha.
  rewrite info3 info5 //=.
  Search _ (_|| false).
  rewrite orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move:Ha.
rewrite info3 info4 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info2: (tm t2 (Ordinal zero<3)==p) => //=. move/eqP:info=>info.
move=> Ha Hb.
case info3 : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:info3=>info3; rewrite info3.
case info4 : (p == tm t1 (Ordinal un<3)).
  by move/eqP:info4=>info4; rewrite info4.
case info5 : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:info5=>info5; rewrite info5.
case info6 : (p == tm t2 (Ordinal zero<3)).
  move:Ha.
  rewrite info4 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite info3 info4 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info2b: (tm t2 (Ordinal un<3)==p) => //=. move/eqP:info=>info.
move=> Ha Hb.
case info3 : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:info3=>info3; rewrite info3.
case info4 : (p == tm t1 (Ordinal un<3)).
  by move/eqP:info4=>info4; rewrite info4.
case info5 : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:info5=>info5; rewrite info5.
case info6 : (p == tm t2 (Ordinal zero<3)).
  move:Ha.
  rewrite info4 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite info3 info4 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info2bb: (tm t2 (Ordinal deux<3)==p) => //=. move/eqP:info=>info.
move=> Ha Hb.
case info3 : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:info3=>info3; rewrite info3.
case info4 : (p == tm t1 (Ordinal un<3)).
  by move/eqP:info4=>info4; rewrite info4.
case info5 : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:info5=>info5; rewrite info5.
case info6 : (p == tm t2 (Ordinal zero<3)).
  move:Ha.
  rewrite info4 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite info3 info4 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.

case info1b: (tm t1 (Ordinal un<3)==p) => //=. move/eqP:info=>info.
move=> Ha Hb.
case info3 : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:info3=>info3; rewrite info3.
case info4 : (p == tm t1 (Ordinal un<3)).
  by move/eqP:info4=>info4; rewrite info4.
case info5 : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:info5=>info5; rewrite info5.
case info6 : (p == tm t2 (Ordinal zero<3)).
  move:Ha.
  rewrite info4 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite info3 info4 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.

case info1bb: (tm t2 (Ordinal deux<3)==p) => //=. move/eqP:info=>info.
move=> Ha Hb.
case info3 : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:info3=>info3; rewrite info3.
case info4 : (p == tm t1 (Ordinal un<3)).
  by move/eqP:info4=>info4; rewrite info4.
case info5 : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:info5=>info5; rewrite info5.
case info6 : (p == tm t2 (Ordinal zero<3)).
  move:Ha.
  rewrite info4 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite info3 info4 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move=> Ha Hb.
case toto : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:toto=>toto; rewrite toto.
case toto2 : (p == tm t1 (Ordinal un<3)).
  by move/eqP:toto2=>toto2; rewrite toto2.
case toto3 : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:toto3=>toto3; rewrite toto3.
case toto4 : (p == tm t2 (Ordinal zero<3)).
  move: Ha.
  rewrite toto2 toto3 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case toto5: (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite toto toto3 //=.
  rewrite !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite toto toto2 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
Qed.


Lemma point2indext2t1_correct tm p t1 t2 :
    pt_in_triangle tm p t2 -> ~(pt_in_triangle tm p t1) ->
                                     tm t2 (point2indext1t2 p t1 t2 tm) = p.
Proof.
rewrite /point2indext1t2 /pt_in_triangle.
case info: (tm t2 (Ordinal zero<3)==p).
case info2 : (p == tm t1 (Ordinal zero<3)) => //=. move/eqP:info=>info.
move=> Ha Hb.
case info3 : (p == tm t1 (Ordinal un<3)).
  Search _ (_||_=false).
  Search _ (_ <> true).
  intuition.
  rewrite info3 in Hb.
  rewrite //=.
  move: Hb.
  rewrite //=.
  move=> Hb.
  tauto.
case info4 : (p == tm t1 (Ordinal deux<3)).
  intuition.
  rewrite info4 in Hb.
  rewrite //=.
  move: Hb.
  rewrite //=.
  move=> Hb.
  Search _ (_||true).
  rewrite orb_true_r in Hb.
  tauto.
case info5 : (p == tm t2 (Ordinal zero<3)).
  exact: info.
case info6 : (p == tm t2 (Ordinal un<3)).
  move/eqP:info6=>info6.
  by rewrite info6.
move:Ha.
rewrite info5 info6 //=.
Search _ (_|| false).
move/eqP=> info7.
by rewrite info7.


case info3 : (p == tm t1 (Ordinal zero<3)) => //=.
move/eqP:info=>info.
move=> Ha Hb.
case info4 : (p == tm t1 (Ordinal un<3)).
  intuition.
  rewrite info4 in Hb.
  rewrite //=.
  move: Hb.
  rewrite //=.
  move=> Hb.
  tauto.
case info5 : (p == tm t1 (Ordinal deux<3)).
  intuition.
  rewrite info5 in Hb.
  rewrite //=.
  move: Hb.
  rewrite //=.
  move=> Hb.
  Search _ (_||true).
  rewrite orb_true_r in Hb.
  tauto.
case info6 : (p == tm t2 (Ordinal zero<3)).
  move/eqP:info6=>info6.
  by rewrite info6.
case info7 : (p == tm t2 (Ordinal un<3)).
  move/eqP:info7=>info7.
  by rewrite info7.
move:Ha.
rewrite info6 info7 //=.
Search _ (_|| false).
move/eqP=> toto.
by rewrite toto.
Qed.




Lemma orientedpostflip (tm: trianglemap)  (ptext1 : point) (ptext2 : point)
                           (t1:T) (t2 :T) (g:graph) (pm: pointmap) :
(forall t:T, oriented t tm) -> isDelaunayLocal t1 t2 tm == false
  -> if flip default_triangle (tm: trianglemap) (ptext1 : point) 
                                  (ptext2 : point) (t1:T) (t2 :T) (g:graph)
                                     (pm: pointmap) is Some (g',tm') then
        forall tt:T, oriented tt tm'
     else (oriented t1 tm) && (oriented t2 tm).
Proof.
move => univ_o illegal.
have [ot1 ot2] : oriented t1 tm /\ oriented t2 tm by split; apply univ_o.
case info : (flip default_triangle tm ptext1 ptext2 t1 t2 g pm) => [[g' tmap'] | ];
   last first.
  by rewrite ot1 ot2.
move : info; rewrite /flip.
case info1 : (unhookT default_triangle t1 tm g) => [g2 tm2].
case info2 : (unhookT default_triangle t2 tm2 g2) => [g3 tm3].
set temp := attachT _ _ _.
case info3 : temp => [vtemp | ]; last by [].
set temp2 := attachT _ _ _.
case info4 : temp2 => [vtemp2 | ]; last by [].
move => [_ vtemp2istmap'] tt.
set new_tr := (fun x : 'I_3 =>
              if x == 0
              then
               if
                (ptext2 == tm t2 (Ordinal (ltn0Sn 2)))
                || (ptext2 == tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
                || (ptext2 == tm t2 (Ordinal (ltnSn 2)))
               then tm t2 (point2indext1t2 ptext2 t1 t2 tm)
               else tm t1 (point2indext1t2 ptext2 t1 t2 tm)
              else
               if x == 1
               then
                if
                 (ptext1 == tm t2 (Ordinal (ltn0Sn 2)))
                 || (ptext1 ==
                     tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
                 || (ptext1 == tm t2 (Ordinal (ltnSn 2)))
                then tm t2 (point2indext1t2 ptext1 t1 t2 tm)
                else tm t1 (point2indext1t2 ptext1 t1 t2 tm)
               else
                if
                 (ptext2 == tm t2 (Ordinal (ltn0Sn 2)))
                 || (ptext2 ==
                     tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
                 || (ptext2 == tm t2 (Ordinal (ltnSn 2)))
                then
                 tm t2
                   (addOrd3 (point2indext1t2 ptext2 t1 t2 tm)
                      (Ordinal (ltnSn 2)))
                else
                 tm t1
                   (addOrd3 (point2indext1t2 ptext2 t1 t2 tm)
                      (Ordinal (ltnSn 2)))).
have otr : leftpoint (new_tr (inZp 0))(new_tr (inZp 1))(new_tr (inZp 2)) > 0.
  rewrite /new_tr /=.
  case h : ((ptext2 == tm t2 (Ordinal (ltn0Sn 2)))
          || (ptext2 == tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
          || (ptext2 == tm t2 (Ordinal (ltnSn 2)))).
(* Trouver un bon moyen d'exprimer ceci dans un lemme. *)
    have -> :  (ptext1 == tm t2 (Ordinal (ltn0Sn 2)))
          || (ptext1 == tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
          || (ptext1 == tm t2 (Ordinal (ltnSn 2))) = false; last first.
      move => {new_tr info4 vtemp2istmap' temp2 tt vtemp2}.
     rewrite !point2indext1t2_correct ?eqxx ?orbT //.















(* -------------------------------------------------------------------- *)
(* Dans cette section, on va s'intéresser aux surfaces qui sont conservées
   par les opérations de flip et add_point_triangle *)
(* -------------------------------------------------------------------- *)

Lemma surface_flip (tm: trianglemap)  (ptext1 : point) (ptext2 : point)
                       (t1:T) (t2 :T) (g:graph) (pm: pointmap) (p:point) 
                        (nomp : P) :
pm nomp ==p
-> (nomp \in surface t1 tm pm) 
    || (nomp \in surface t2 tm pm)
      -> exists t:T, if flip (tm: trianglemap) (ptext1 : point) 
                                  (ptext2 : point) (t1:T) (t2 :T) (g:graph)
                                     (pm: pointmap) is Some (g',tm') then
                            nomp \in surface t tm' pm
                   else (nomp \in surface t1 tm pm)
                          || (nomp \in surface t2 tm pm).
Abort.


Lemma surface_add_point_triangle (p:point) (t:T) (tm : trianglemap)
                                     (g:graph) (pm :pointmap) (nomp : P) :
pm nomp ==p ->
  (nomp \in surface t tm pm) -> if add_point_triangle (p:point) (t:T)
                                (tm : trianglemap) (g:graph) (pm :pointmap)
              is Some (g', tm') then exists t1:T, nomp \in surface t1 tm' pm
                          else (nomp \in surface t tm pm).
Abort.




(* -------------------------------------------------------------------- *)
(* Dans cette section, on va démontrer une propriété combinatoire *)
(* -------------------------------------------------------------------- *)



Lemma combi_flip (tm: trianglemap) (ptext1 : point) (ptext2 : point) 
             (t3 t4: T) (t1:T) (t2 :T) (g:graph) (pm: pointmap) (p:point) :
 (t3 \in g t4 -> t4 \in g t3)
-> forall (t5 t6 :T), if flip (tm: trianglemap) (ptext1 : point) 
                                  (ptext2 : point) (t1:T) (t2 :T) (g:graph)
                                     (pm: pointmap) is Some (g',tm') then
                             (t5 \in g' t6 -> t6 \in g' t5)
                   else (t3 \in g t4 -> t4 \in g t3).
Abort.

Lemma combi_add_point_triangle (p:point) (t:T) (tm : trianglemap)
                                 (g:graph) (pm :pointmap) (t1:T) (t2 :T) :
  (t1 \in g t2 -> t2 \in g t1)
-> forall (t3 t4 :T), if add_point_triangle (p:point) (t:T)
                                (tm : trianglemap) (g:graph) (pm :pointmap)
              is Some (g', tm') then   (t3 \in g' t4 -> t4 \in g' t3)
                          else (t1 \in g t2 -> t2 \in g t1).
Abort.


End Delaunay.
