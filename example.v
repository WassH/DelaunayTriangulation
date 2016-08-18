(*=====================================================
=======================================================
JUNE 2016 - AUGUST 2016

AUTHOR : Wassim Haffaf.
=======================================================
=======================================================*)


Require Import Arith.
Require Import EqNat.
Require Import Ring.
Require Import Bool.
Require Coq.Init.Nat.
Require Import ZArith.
Require Import Field.

Locate field_tactics.
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
Require Import determinant_complements.

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
<-> exists (k1 k2 k3 :rat),
 (point2R1 p = k1*point2R1 ((tm t) (Ordinal(zero<3)))
                + k2*point2R1 ((tm t) (Ordinal(un<3)))
                + k3*point2R1 ((tm t) (Ordinal(deux<3)))) /\
 (point2R2 p = k1*point2R2 ((tm t) (Ordinal(zero<3)))
                + k2*point2R2 ((tm t) (Ordinal(un<3)))
                + k3*point2R2 ((tm t) (Ordinal(deux<3))))
            /\ (k1+k2+k3 == 1)
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
  rewrite /leftpoint H1 H2.
  set u1 := \det _.
  have u1q : u1 = k3 * bd.
  rewrite /u1 (expand_det_row _ (Ordinal (deux<3))) big_ord_recl.
  rewrite mxE. rewrite //= big_ord_recl big_ord_recl big_ord0 mxE //=.
  rewrite mxE //=.
  
  rewrite /cofactor !//= (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= mxE //= /cofactor !//= big_ord_recl big_ord0 !mxE !//=.
rewrite /row' /col'.
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


  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor !//=.

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

  rewrite big_ord_recl big_ord0 (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor !//=.

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

  rewrite big_ord_recl big_ord0 !mxE !//=.

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

rewrite /bd /leftpoint (expand_det_row _ (Ordinal (deux<3))).
rewrite big_ord_recl !mxE !//= /cofactor (expand_det_row _ (Ordinal (un<2))).
rewrite big_ord_recl !mxE !//= /cofactor /row' /col'.
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

rewrite big_ord_recl (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //=.
  rewrite /cofactor !//=.
rewrite big_ord0 big_ord_recl !mxE !//=.

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

  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= /cofactor !//=.
rewrite !mxE !//= /col' /row'.
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

rewrite !//= /bump !//= /F6 4!mxE /=.
rewrite /F  4!mxE /= /F2 4!mxE /= /F4 4!mxE /=.
rewrite /F5. rewrite 4!mxE /= /F7. rewrite 4!mxE /= /F8 4!mxE /=.
rewrite /F9 4!mxE /= /F12 4!mxE /= /F11 4!mxE /= /F3 4!mxE /= /F10 4!mxE /=.

rewrite !mulN1r !addr0 !//= !expr2 !//= !exprD !expr1 !expr0 !//= !mulr1 !//=.
rewrite !mulN1r !//= !mulrN1.

set a := point2R1 (tm t (Ordinal zero<3)).
set b := point2R2 (tm t (Ordinal zero<3)).
set c := point2R1 (tm t (Ordinal un<3)).
set d := point2R2 (tm t (Ordinal un<3)).
set e := point2R1 (tm t (Ordinal deux<3)).
set f := point2R2 (tm t (Ordinal deux<3)).
rewrite (_ : k1 = 1 - k2 - k3).
simpl in k1, k2, k3.
prefield. field.


rewrite -(eqP H3). simpl in k1. prefield; ring.


rewrite u1q.
rewrite pmulr_rgt0; last first.
exact: H6.
rewrite toriented !//=.


(* On refait de même avec les points un<3 et deux<3 *)
set u2 := \det _.
  have u2q : u2 = k1 * bd.
  rewrite /u2 (expand_det_row _ (Ordinal (deux<3))) big_ord_recl.
  rewrite mxE. rewrite //= big_ord_recl big_ord_recl big_ord0 mxE //=.
  rewrite mxE //=.
  
  rewrite /cofactor !//=.
  
  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE. rewrite //=. rewrite mxE. rewrite //=. rewrite mxE. rewrite //=.
  rewrite /cofactor !//= big_ord_recl big_ord0 !mxE !//= /row' /col'.
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


  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= mxE //= /cofactor !//= /row' /col'.

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

  rewrite big_ord_recl big_ord0 (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= mxE //=.
  rewrite /cofactor !//=.

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

  rewrite big_ord_recl big_ord0 !mxE !//=.

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

rewrite /bd /leftpoint (expand_det_row _ (Ordinal (deux<3))).
rewrite big_ord_recl !mxE !//= /cofactor (expand_det_row _ (Ordinal (un<2))).
rewrite big_ord_recl !mxE !//= /cofactor /row' /col'.
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

rewrite big_ord_recl big_ord0 !mxE !//=.
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
  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl mxE //= mxE //=.
  rewrite /cofactor !//=.
rewrite big_ord0 big_ord_recl !mxE !//=.

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

rewrite big_ord_recl big_ord0 !mxE !//=.

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

  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE  //= mxE //= /cofactor !//=.
rewrite !mxE !//= /col' /row'.
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

rewrite big_ord_recl big_ord0 !mxE !//=.
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

rewrite !//= /bump !//= /F6. rewrite 4!mxE /=.
rewrite /F 4!mxE /= /F2 4!mxE /=.
rewrite /F4 4!mxE /= /F5 4!mxE /=.
rewrite /F7  4!mxE /= /F8  4!mxE /=.
rewrite /F9  4!mxE /= /F12 4!mxE /=.
rewrite /F11 4!mxE /= /F3 4!mxE /= /F10 4!mxE /=.

rewrite !mulN1r !addr0 !//= !expr2 !//=.
rewrite !exprD !expr1 !expr0 !//= !mulr1 !//= !mulN1r !//=.
rewrite !mulrN1.

set a := point2R1 (tm t (Ordinal zero<3)).
set b := point2R2 (tm t (Ordinal zero<3)).
set c := point2R1 (tm t (Ordinal un<3)).
set d := point2R2 (tm t (Ordinal un<3)).
set e := point2R1 (tm t (Ordinal deux<3)).
set f := point2R2 (tm t (Ordinal deux<3)).
rewrite (_ : k1 = 1 - k2 - k3); last first.
  rewrite -(eqP H3). simpl in k1. prefield; ring.
simpl in k2, k3.
prefield.
field.

rewrite u2q.
rewrite pmulr_rgt0; last first.
exact: H4.
rewrite toriented !//=.


(* On refait de même avec les points deux<3 et zero<3 *)
set u3 := \det _.
  have u3q : u3 = k2 * bd.
  rewrite /u3 (expand_det_row _ (Ordinal (deux<3))) big_ord_recl.
  rewrite mxE //= big_ord_recl big_ord_recl big_ord0.
  rewrite mxE //= mxE //=.
  
  rewrite /cofactor !//=.
  
  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= mxE //=.
  rewrite /cofactor !//=.

  rewrite big_ord_recl big_ord0 !mxE !//= /row' /col'.
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


  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= mxE //=.
  rewrite /cofactor !//=.

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

  rewrite big_ord_recl big_ord0 (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= mxE //=.
  rewrite /cofactor !//=.

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

  rewrite big_ord_recl big_ord0 !mxE !//=.

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

rewrite /bd /leftpoint (expand_det_row _ (Ordinal (deux<3))) big_ord_recl.
rewrite !mxE !//= /cofactor (expand_det_row _ (Ordinal (un<2))).
rewrite big_ord_recl !mxE !//= /cofactor.

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

rewrite big_ord_recl big_ord0 !mxE !//=.
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
  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= /cofactor !//=.
rewrite big_ord0 big_ord_recl !mxE !//=.

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

  rewrite (expand_det_row _ (Ordinal (un<2))) big_ord_recl.
  rewrite mxE //= mxE //= /cofactor !//=.
rewrite !mxE !//= /col' /row'.
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
rewrite /F6 4!mxE /= /F 4!mxE /=.
rewrite /F2  4!mxE /= /F4  4!mxE /=.
rewrite /F5  4!mxE /= /F7  4!mxE /=.
rewrite /F8  4!mxE /= /F9  4!mxE /=.
rewrite /F12  4!mxE /= /F11  4!mxE /=.
rewrite /F3  4!mxE /= /F10  4!mxE /=.

rewrite !mulN1r !addr0 !//= !expr2 !//=.
rewrite !exprD !expr1 !expr0 !//= !mulr1 !//=  !mulN1r !//=  !mulrN1.

set a := point2R1 (tm t (Ordinal zero<3)).
set b := point2R2 (tm t (Ordinal zero<3)).
set c := point2R1 (tm t (Ordinal un<3)).
set d := point2R2 (tm t (Ordinal un<3)).
set e := point2R1 (tm t (Ordinal deux<3)).
set f := point2R2 (tm t (Ordinal deux<3)).
rewrite (_ : k1 = 1 - k2 - k3); last first.
  rewrite -(eqP H3). simpl in k1. prefield; ring.
simpl in k2, k3.
prefield.
field.

rewrite u3q.
rewrite pmulr_rgt0; last first.
exact: H5.
rewrite toriented !//=.



(* Preuve de l'autre implication *)
move/andP=> [H2 H3].
move: H2; move/andP=> [H1 H2].

exists ((leftpoint (tm t (Ordinal(un<3))) (tm t (Ordinal(deux<3))) p)/bd).
exists ((leftpoint (tm t (Ordinal(deux<3))) (tm t (Ordinal(zero<3))) p)/bd).
exists ((leftpoint (tm t (Ordinal(zero<3))) (tm t (Ordinal(un<3))) p)/bd).
split.
move: toriented.
rewrite /bd /leftpoint.
rewrite expand_det33 !mxE !//= /leftpoint expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//= expand_det33 !mxE !//=.
set a := point2R1 (tm t (Ordinal zero<3)).
set b := point2R2 (tm t (Ordinal zero<3)).
set c := point2R1 (tm t (Ordinal un<3)).
set d := point2R2 (tm t (Ordinal un<3)).
set e := point2R1 (tm t (Ordinal deux<3)).
set f := point2R2 (tm t (Ordinal deux<3)).
set g := point2R1 p.
set h := point2R2 p.
move=> toriented.
prefield.
field.
rewrite/not.
move=>hyp_contra.
move:toriented.
rewrite !mulr1 !mul1r.
rewrite [X in (Num.lt 0 X-> False)]hyp_contra.
auto.

split.
move: toriented.
rewrite /bd /leftpoint.
rewrite expand_det33 !mxE !//= /leftpoint expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//= expand_det33 !mxE !//=.
set a := point2R1 (tm t (Ordinal zero<3)).
set b := point2R2 (tm t (Ordinal zero<3)).
set c := point2R1 (tm t (Ordinal un<3)).
set d := point2R2 (tm t (Ordinal un<3)).
set e := point2R1 (tm t (Ordinal deux<3)).
set f := point2R2 (tm t (Ordinal deux<3)).
set g := point2R1 p.
set h := point2R2 p.
move=> toriented.
prefield.
field.
rewrite/not.
move=>hyp_contra.
move:toriented.
rewrite !mulr1 !mul1r.
rewrite [X in (Num.lt 0 X-> False)]hyp_contra.
auto.

split.
move:toriented.
rewrite /bd /leftpoint.
rewrite expand_det33 !mxE !//= /leftpoint expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//= expand_det33 !mxE !//=.
set a := point2R1 (tm t (Ordinal zero<3)).
set b := point2R2 (tm t (Ordinal zero<3)).
set c := point2R1 (tm t (Ordinal un<3)).
set d := point2R2 (tm t (Ordinal un<3)).
set e := point2R1 (tm t (Ordinal deux<3)).
set f := point2R2 (tm t (Ordinal deux<3)).
set g := point2R1 p.
set h := point2R2 p.
rewrite !mul1r !mulr1.
move=> toriented.
set i := (c * f - c * h - d * e + d * g + e * h - f * g) /
(a * d - a * f - b * c + b * e + c * f - d * e) +
(e * b - e * h - f * a + f * g + a * h - b * g) /
(a * d - a * f - b * c + b * e + c * f - d * e) +
(a * d - a * h - b * c + b * g + c * h - d * g) /
(a * d - a * f - b * c + b * e + c * f - d * e).
simpl in i.
set i2 := 1.
simpl in i2.
apply/eqP.
rewrite /i /i2.

prefield.
field.
rewrite/not.
move=>hyp_contra.
move:toriented.
rewrite [X in (Num.lt 0 X-> False)]hyp_contra.
auto.

split.
rewrite divr_gt0; last first.
      by [].
    have egal_det12 : leftpoint (tm t (Ordinal un<3)) (tm t (Ordinal deux<3)) p
                   = leftpoint p (tm t (Ordinal un<3)) (tm t (Ordinal deux<3));
    last first.
      rewrite egal_det12.
      by [].
    rewrite /leftpoint expand_det33 !mxE !//= expand_det33 !mxE !//= !mulr1 !mul1r.
    prefield.
    field.
  by [].

split.
Search _ (_/_>0).
rewrite divr_gt0; last first.
      by [].
    have egal_det20 : leftpoint (tm t (Ordinal deux<3)) (tm t (Ordinal zero<3)) p
                   = leftpoint p (tm t (Ordinal deux<3)) (tm t (Ordinal zero<3));
    last first.
      rewrite egal_det20.
      by [].
    rewrite /leftpoint expand_det33 !mxE !//= expand_det33 !mxE !//= !mulr1 !mul1r.
    prefield.
    field.
  by [].

rewrite divr_gt0; last first.
      by [].
    have egal_det01 : leftpoint (tm t (Ordinal zero<3)) (tm t (Ordinal un<3)) p
                   = leftpoint p (tm t (Ordinal zero<3)) (tm t (Ordinal un<3));
    last first.
      rewrite egal_det01.
      by [].
    rewrite /leftpoint expand_det33 !mxE !//= expand_det33 !mxE !//= !mulr1 !mul1r.
    prefield.
    field.
  by [].
Qed.



Lemma mul0l (n :rat_Ring) : 0*n = 0.
Proof.
prefield.
field.
Qed.

Lemma mul0r (n :rat_Ring) : n*0 = 0.
Proof.
prefield.
field.
Qed.


Lemma mul1l (n :rat_Ring) : 1*n = n.
Proof.
prefield.
field.
Qed.

Lemma mul1r (n :rat_Ring) : n*1 = n.
Proof.
prefield.
field.
Qed.

Lemma plus0l (n :rat_Ring) : 0+n = n.
Proof.
prefield.
field.
Qed.


Lemma plus0r (n :rat_Ring) : n+0 = n.
Proof.
prefield.
field.
Qed.


Lemma expand_det44 (M : 'M[rat]_(4,4)) : 
\det M
=

M (@Ordinal 4 0 isT) (@Ordinal 4 0 isT) * 
(  M (@Ordinal 4 1 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 3 isT) -
  M (@Ordinal 4 1 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 1 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 3 isT) +
  M (@Ordinal 4 1 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 1 isT) +
  M (@Ordinal 4 1 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 1 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 1 isT))

- M (@Ordinal 4 1 isT) (@Ordinal 4 0 isT) * 
(   M (@Ordinal 4 0 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 3 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 3 isT) +
  M (@Ordinal 4 0 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 1 isT) +
  M (@Ordinal 4 0 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 1 isT))

+ M (@Ordinal 4 2 isT) (@Ordinal 4 0 isT) * 
(  M (@Ordinal 4 0 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 3 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 3 isT) +
  M (@Ordinal 4 0 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 1 isT) +
  M (@Ordinal 4 0 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 3 isT) (@Ordinal 4 1 isT))

- M (@Ordinal 4 3 isT) (@Ordinal 4 0 isT) * 
(  M (@Ordinal 4 0 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 3 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 3 isT) +
  M (@Ordinal 4 0 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 1 isT) +
  M (@Ordinal 4 0 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 1 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 2 isT) -
  M (@Ordinal 4 0 isT) (@Ordinal 4 3 isT) *
  M (@Ordinal 4 1 isT) (@Ordinal 4 2 isT) *
  M (@Ordinal 4 2 isT) (@Ordinal 4 1 isT)).

Proof.
    rewrite (expand_det_col _ (inZp 3)) big_ord_recl.
    rewrite !//= /cofactor !//= expand_det33 !mxE. rewrite !//=.

    rewrite big_ord_recl !//= /cofactor !//= expand_det33 !mxE !//=.
    rewrite big_ord_recl !//= /cofactor !//= expand_det33 !mxE !//=.
    rewrite big_ord_recl !//= /cofactor !//= expand_det33 !mxE !//=.
    rewrite big_ord0.
    rewrite !//=.
    rewrite (_ :  ((-1) ^+ (bump 0 (bump 0 0) + 3 %% 4) = -1)); last first.
      by [].
    rewrite (_ : (-1) ^+ (0 + 3 %% 4)  = -1); last first.
      by [].
    rewrite (_ : (-1) ^+ (bump 0 0 + 3 %% 4)  = 1); last first.
      by [].
    rewrite (_ : (-1) ^+ (bump 0 (bump 0 (bump 0 0)) + 3 %% 4) = 1); last first.
      by [].
    rewrite plus0r !//= !mul1l.
    rewrite (_ : (lift ord0 (lift ord0 (lift ord0 ord0)) = @Ordinal 4 3 isT))
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : ((lift ord0 (lift ord0 ord0)) = @Ordinal 4 2 isT))
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift ord0 (@Ordinal 3 0 isT) = @Ordinal 4 1 isT))
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (inZp 3) (@Ordinal 3 2 isT)) = @Ordinal 4 2 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (inZp 3) (@Ordinal 3 0 isT)) = @Ordinal 4 0 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (inZp 3) (@Ordinal 3 1 isT)) = @Ordinal 4 1 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : lift ord0 (@Ordinal 3 1 isT) = @Ordinal 4 2 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : lift ord0 (@Ordinal 3 2 isT) = @Ordinal 4 3 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : lift ord0 ord0 = @Ordinal 4 1 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 2 isT) (@Ordinal 3 1 isT))
                       = @Ordinal 4 1 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 3 isT) (@Ordinal 3 1 isT))
                       = @Ordinal 4 1 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 1 isT) (@Ordinal 3 1 isT))
                       = @Ordinal 4 2 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 1 isT) (@Ordinal 3 0 isT))
                       = @Ordinal 4 0 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 1 isT) (@Ordinal 3 2 isT))
                       = @Ordinal 4 3 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 2 isT) (@Ordinal 3 0 isT))
                       = @Ordinal 4 0 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 2 isT) (@Ordinal 3 2 isT))
                       = @Ordinal 4 3 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 3 isT) (@Ordinal 3 0 isT))
                       = @Ordinal 4 0 isT)
                  ; last first.
      apply val_inj.
      rewrite //.
    rewrite (_ : (lift (@Ordinal 4 3 isT) (@Ordinal 3 2 isT))
                       = @Ordinal 4 2 isT)
                  ; last first.
      apply val_inj.
      rewrite //.

      rewrite (_ : @inZp 3 3 = @Ordinal 4 3 isT); last first.
        apply: val_inj.
        by rewrite //.

      rewrite (_ : @ord0 3 = @Ordinal 4 0 isT); last first.
        apply: val_inj.
        by rewrite //.

      set a00 := M (@Ordinal 4 0 isT) (@Ordinal 4 0 isT).
      set a01 := M (@Ordinal 4 0 isT) (@Ordinal 4 1 isT).
      set a02 := M (@Ordinal 4 0 isT) (@Ordinal 4 2 isT).
      set a03 := M (@Ordinal 4 0 isT) (@Ordinal 4 3 isT).

      set a10 := M (@Ordinal 4 1 isT) (@Ordinal 4 0 isT).
      set a11 := M (@Ordinal 4 1 isT) (@Ordinal 4 1 isT).
      set a12 := M (@Ordinal 4 1 isT) (@Ordinal 4 2 isT).
      set a13 := M (@Ordinal 4 1 isT) (@Ordinal 4 3 isT).

      set a20 := M (@Ordinal 4 2 isT) (@Ordinal 4 0 isT).
      set a21 := M (@Ordinal 4 2 isT) (@Ordinal 4 1 isT).
      set a22 := M (@Ordinal 4 2 isT) (@Ordinal 4 2 isT).
      set a23 := M (@Ordinal 4 2 isT) (@Ordinal 4 3 isT).

      set a30 := M (@Ordinal 4 3 isT) (@Ordinal 4 0 isT).
      set a31 := M (@Ordinal 4 3 isT) (@Ordinal 4 1 isT).
      set a32 := M (@Ordinal 4 3 isT) (@Ordinal 4 2 isT).
      set a33 := M (@Ordinal 4 3 isT) (@Ordinal 4 3 isT).

      prefield; ring.
Qed.


Lemma fois_div (n1 n2: rat_Ring) : n2 <>0 -> n1 *n2/n2 = n1.
Proof.
move=> hypn2.
prefield.
by field.
Qed.


Definition ing0 : (0<2)%N.
Proof.
by apply: ltn_trans (ltnSn 0) (ltnSn 1).
Qed.

Definition ing1 : (1<2)%N.
Proof.
by apply: (ltnSn 1).
Qed.


Lemma eq_ordinal2 (x0 :'I_2):
  (x0 == Ordinal ing0) = false -> x0 = Ordinal ing1.
Proof.
move: x0.
move=> [a b] h.
apply: val_inj.
rewrite //=.
apply/eqP.
move/negbT:h.
apply contraR.
move=> hyp.
apply/eqP.
apply val_inj.
rewrite !//=.
rewrite ltnS in b.
have hyp2 : (a<1)%N.
  rewrite ltn_neqAle.
  apply/andP; split.
    by [].
  by [].
rewrite ltnS in hyp2.
rewrite leqn0 in hyp2.
move/eqP :hyp2.
by [].
Qed.


Lemma eq_ordinal (x1 :'I_2):
  (x1 == Ordinal ing1) = false -> x1 = Ordinal ing0.
Proof.
move: x1.
move=> [a b] h.
apply: val_inj.
rewrite //=.
apply/eqP.
move/negbT:h.
apply contraR.
move=> hyp.
apply/eqP.
apply val_inj.
rewrite !//=.
rewrite neq_ltn in hyp.
case tmp : (a < 0)%N.
  by [].
rewrite tmp in hyp.
rewrite orb_false_l in hyp.
apply: anti_leq.
move:b.
change ((a < 1+1)%N -> (a <= 1 <= a)%N).
rewrite ltnS !//=.
move=> hyp2.
rewrite hyp hyp2.
by [].
Qed.


Definition convex_fun (f : rat*rat -> rat) :=
 forall (k:rat), forall (x:rat*rat), forall (y:rat*rat), (0<=k) -> (k<=1) 
          -> 
         f (k*x.1 + (1-k)*y.1, k*x.2 + (1-k)*y.2) 
                  <= k*(f x) + (1-k)* (f y).

Definition convex_strict_fun (f : rat*rat -> rat) :=
 forall (k:rat), forall (x:rat*rat), forall (y:rat*rat), (0<k) -> (k<1) 
          -> (x.1 != y.1) || (x.2 != y.2) ->
         f (k*x.1 + (1-k)*y.1, k*x.2 + (1-k)*y.2) 
                  < k*(f x) + (1-k)* (f y).

Lemma convex_strict_implies_convex (f : rat*rat -> rat) :
  convex_strict_fun f -> convex_fun f.
Proof.
rewrite /convex_strict_fun /convex_fun.
move=> H k x y hypok0 hypok1.
case hypok0lt: (k>0).
  case hypok1lt : (k<1).
    case ex : (~~ (x.1 == y.1) || ~~ (x.2 == y.2)).
      move: (H k x y hypok0lt hypok1lt ex).
      rewrite ltr_def.
      move/andP=> hypo.
      move:hypo.
      move=> [hypo1 hypo2].
      by apply: hypo2.
    move/negbT : ex.
    rewrite negb_orb.
    move/andP=> ex1.
    move:ex1.
    move=> [ex1 ex2].
    move/negPn : ex1.
    move/negPn : ex2.
    move/eqP=> ex1.
    move/eqP=> ex2.
    have info1 : x = (x.1, x.2).
      apply: surjective_pairing.
    have info2 : y = (y.1, y.2).
      apply: surjective_pairing.
    rewrite [X in Num.le _ (k * f X + (1 - k) * f y)]info1 .
    rewrite [X in Num.le _ (k * f (x.1, x.2) + (1 - k) * f X)]info2 .
    rewrite -[X in Num.le (f (k * x.1 + (1 - k) * X, k * x.2 + (1 - k) * y.2))
        (k * f (x.1, x.2) + (1 - k) * f (y.1, y.2))]ex2.
    rewrite -[X in Num.le (f (k * x.1 + (1 - k) * x.1, k * x.2 + (1 - k) * X))
        (k * f (x.1, x.2) + (1 - k) * f (y.1, y.2))]ex1.
    rewrite -[X in Num.le (f (k * x.1 + (1 - k) * x.1, k * x.2 + (1 - k) * x.2))
        (k * f (x.1, x.2) + (1 - k) * f (X, y.2))]ex2.
    rewrite -[X in Num.le (f (k * x.1 + (1 - k) * x.1, k * x.2 + (1 - k) * x.2))
        (k * f (x.1, x.2) + (1 - k) * f (x.1,X))]ex1.
    have info3 : (k * x.1 + (1 - k) * x.1 = x.1).
      prefield; ring.
    have info4 : (k * x.2 + (1 - k) * x.2 = x.2).
      prefield; ring.
    have info5 : ((k * f (x.1, x.2) + (1 - k) * f (x.1, x.2) = f (x.1,x.2))).
      prefield; ring.
    rewrite info3 info4 info5.
    by [].

  have info : (k = 1).
    move : hypok1lt.
    rewrite ltr_def.
    set b1 := (1 == k).
    set b2 := Num.le k 1.
    move/negbT => bool1.
    move: bool1.
    rewrite negb_andb.
    move/orP=> h.
    move:h.
    case hypo : (~~ ~~ b1).
      move=>h.
      move/negPn : hypo.
      rewrite /b1.
      move/eqP=> hypo.
      by [].
    move/orP => H2.
    move: H2.
    rewrite orb_false_l /b2.
    move: hypok1.
    rewrite -/b2.
    move=> contra1 contra2.
    have contra : b2 && ~~ b2.
      apply/andP.
      split.
        by [].
      by [].
    move : contra.
    rewrite andb_negb_r.
    by [].
  rewrite info.
  have tmp1 : (1 * x.1 + (1 - 1) * y.1 = x.1).
    prefield. ring.
  have tmp2 : (1 * x.2 + (1 - 1) * y.2 = x.2).
    prefield; ring.
  have tmp3 : (1 * f x + (1 - 1) * f y = f x).
    prefield; ring.
  rewrite tmp1 tmp2 tmp3.
  have info1 : x = (x.1, x.2).
    apply: surjective_pairing.
  have info2 : y = (y.1, y.2).
    apply: surjective_pairing.
  rewrite -info1.
  by [].


have info : (k = 0).
  move : hypok0lt.
  rewrite ltr_def.
  set b1 := (k==0).
  set b2 := Num.le 0 k.
  move/negbT => bool1.
  move: bool1.
  rewrite negb_andb.
  move/orP=> h.
  move:h.
  case hypo : (~~ ~~ b1).
    move=>h.
    move/negPn : hypo.
    rewrite /b1.
    move/eqP=> hypo.
    by [].
  move/orP => H2.
  move: H2.
  rewrite orb_false_l /b2.
  move: hypok1.
  rewrite -/b2.
  move=> contra1 contra2.
  have contra : b2 && ~~ b2.
    apply/andP.
    split.
      by [].
    by [].
  move : contra.
  rewrite andb_negb_r.
  by [].
rewrite info.
have tmp1 : (0 * x.1 + (1 - 0) * y.1 = y.1).
  prefield. ring.
have tmp2 : (0 * x.2 + (1 - 0) * y.2 = y.2).
  prefield; ring.
have tmp3 : (0 * f x + (1 - 0) * f y = f y).
  prefield; ring.
rewrite tmp1 tmp2 tmp3.
have info2 : y = (y.1, y.2).
  apply: surjective_pairing.
rewrite -info2.
by [].
Qed.



Lemma sum_eq0 :forall (n:nat) (k:seq rat),
[forall (i:'I_(S n)|true), (Num.le 0 k`_((nat_of_ord) i))] ->
  ((\sum_(i < S n) (k`_((nat_of_ord) i)))==0) = [forall (i:'I_(S n)|true), k`_i == 0%Q].
Proof.
move => n k hyp.
have utile: forall m, ([forall (i:'I_(S m)|true), (Num.le 0 k`_((nat_of_ord) i))] ->
Num.le 0 (\sum_(i < m.+1) k`_i)).
  induction m.
    rewrite big_ord_recr !//= big_ord0 !//= -big_andE big_ord_recr !//=.
    rewrite big_ord0 !//= plus0l.
    by [].
  rewrite -big_andE big_ord_recr !//=.
  move/andP=> hypSm.
  move:hypSm.
  move=> [hypSm H].
  rewrite big_ord_recr !//=.
  apply: addr_ge0.
  move:hypSm.
  rewrite big_andE.
  move=>hypSm.
  apply (IHm hypSm).
by [].


induction n.
  rewrite big_ord_recl !//= big_ord0 !//= -big_andE !big_ord_recr !//=.
  rewrite big_ord0 !//= plus0r.
  by [].


move :hyp.
rewrite -big_andE.
rewrite big_ord_recr !//=.
move/andP=> hyp1.
move: hyp1.
move=> [hyp1 hyp2].
move: hyp1.
rewrite big_andE.
move=> hyp1.

rewrite big_ord_recr !//= -big_andE [RHS]big_ord_recr //= big_andE.
have utileSn : ([forall (i:'I_(S n)|true), (Num.le 0 k`_((nat_of_ord) i))] ->
 Num.le 0 (\sum_(i < n.+1) k`_i)).
  exact: (utile n).


(* rewrite -big_andE. rewrite big_ord_recr. rewrite !//=. *)
rewrite -(IHn hyp1).
rewrite paddr_eq0; last first.
    by [].
  exact : (utile n hyp1).
by [].
Qed.

Lemma pos_elt_pos_sum (k : seq rat) :
forall m, ([forall (i:'I_m|true), (Num.le 0 k`_((nat_of_ord) i))] ->
Num.le 0 (\sum_(i < m) k`_i)).
Proof.
induction m.
    by rewrite big_ord0 !//=.
  rewrite -big_andE big_ord_recr !//=.
  move/andP=> hypSm.
  move:hypSm.
  move=> [hypSm H].
  rewrite big_ord_recr !//=.
  apply: addr_ge0.
  move:hypSm.
  rewrite big_andE.
  move=>hypSm.
  apply (IHm hypSm).
by [].
Qed.


Lemma strict_pos_elt_strict_pos_sum (k : seq rat) :
forall m, ([forall (i:'I_(S m)|true), (Num.lt 0 k`_((nat_of_ord) i))] ->
Num.lt 0 (\sum_(i < m.+1) k`_i)).
Proof.
induction m.
    rewrite big_ord_recr !//= -big_andE big_ord_recr !//= big_ord0 !//=.
    rewrite big_ord0 !//= plus0l.
    by [].
  rewrite -big_andE big_ord_recr !//=.
  move/andP=> hypSm.
  move:hypSm.
  move=> [hypSm H].
  rewrite big_ord_recr !//=.
  apply: addr_gt0.
  move:hypSm.
  rewrite big_andE.
  move=>hypSm.
  apply (IHm hypSm).
by [].
Qed.

Lemma Jensen_inequality (n:nat)(f : rat*rat -> rat) 
              (f_is_convex : convex_fun f)
          (x :seq (rat*rat)) (nsup1 : (n>1)%nat ) :
  forall k:seq rat,(\sum_(i<n) (k`_((nat_of_ord) i)) = 1)->
      [forall (i:'I_n|true), (Num.le 0 k`_((nat_of_ord) i))]
  -> f (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1, 
          \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2)
            <= \sum_(i<n) (k`_((nat_of_ord) i))
                    *(f ((x`_((nat_of_ord) i)).1, (x`_((nat_of_ord) i)).2 )).
Proof.
induction n.
  move:nsup1.
  by rewrite !//=.
move=> k somme_egal_1 hypok.
set lambda := \sum_(i<n) (k`_((nat_of_ord) i)).
case ns1 : (1 < n)%N.
  case info: (lambda==0).

  rewrite !big_ord_recr !//=.
  have contra: (Num.le 0 (\sum_(i<n) (k`_((nat_of_ord) i)))).
    move: hypok.
    rewrite -big_andE !//=.
    rewrite big_ord_recr !//=.
    move/andP=> hypok.
    move :hypok.
    move=> [hypok1 hypok2].
    move: hypok1.
    rewrite big_andE.
    move=> hypok1.
    move:  info.
    rewrite /lambda.
    move=> info.
  move: somme_egal_1 nsup1 IHn ex lambda info  hypok2 hypok1 ns1.
  case : n.
    move=> h1 h2.
    by [].
  move=> n somme_egal_1 nsup1 IHn ex lambda info hypok2 hypok1 ns1.
  apply (pos_elt_pos_sum hypok1).
  move:contra.
  rewrite -/lambda.
  move=> hypo.

(* Il faut montrer que tous les ki sont nuls avec sum_eq0 *)
  rewrite /lambda in hypo info.
  move: somme_egal_1 nsup1 IHn ex info  hypo ns1 hypok lambda.
  case : n.
    move=> h1 h2.
    by [].
  move=> n somme_egal_1 nsup1 IHn ex info  hypo ns1 hypok lambda.

  move : hypok.
  rewrite -big_andE big_ord_recr.
  change (\big[andb_monoid/true]_(i :'I_(S n)) Num.le 0 k`_ i && Num.le 0 k`_(S n) 
          -> Num.le
  (f
     (\sum_(i < n.+1) k`_i * (x`_i).1 + k`_n.+1 * (x`_n.+1).1,
     \sum_(i < n.+1) k`_i * (x`_i).2 + k`_n.+1 * (x`_n.+1).2))
  (\sum_(i < n.+1) k`_i * f ((x`_i).1, (x`_i).2) +
   k`_n.+1 * f ((x`_n.+1).1, (x`_n.+1).2))).
  move/andP => hypok.
  move:hypok.
  move=> [hypok dernier].
  move:hypok.
  rewrite big_andE => hypok.
  move: (sum_eq0 hypok).
  move=> sum_eq0.
  rewrite sum_eq0 in info.
  have sum_egal_0 :  (\sum_(i < n.+1) k`_i == 0).
    rewrite sum_eq0.
    by [].
  move: somme_egal_1.
  rewrite big_ord_recr.
  change (\sum_(i < n.+1) k`_i + k`_(S n) = 1 -> Num.le
  (f
     (\sum_(i < n.+1) k`_i * (x`_i).1 + k`_n.+1 * (x`_n.+1).1,
     \sum_(i < n.+1) k`_i * (x`_i).2 + k`_n.+1 * (x`_n.+1).2))
  (\sum_(i < n.+1) k`_i * f ((x`_i).1, (x`_i).2) +
   k`_n.+1 * f ((x`_n.+1).1, (x`_n.+1).2))).
  move/eqP: sum_egal_0.
  move=> sum_egal_0.
  rewrite sum_egal_0 plus0l.
  move=> dernier_egal_1.
  rewrite dernier_egal_1 !mul1l.
  have intel : (\sum_(i < n.+1) k`_i * (x`_i).1 
                          = \sum_(i < n.+1) 0 * (x`_i).1).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> k`_i * (x`_i).1 = 0 * (x`_i).1).
    move/eqP => intel_tmp.
    rewrite intel_tmp.
    prefield. ring.
  rewrite intel.
  have intel2 : (\sum_(i < n.+1) 0 * (x`_i).1 
                          = \sum_(i < n.+1) 0).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> 0 * (x`_i).1 = 0 ).
    move/eqP => intel2_tmp.
    prefield. ring.
  rewrite intel2 sumr_const.
  
  have intel3 : (\sum_(i < n.+1) k`_i * (x`_i).2 
                          = \sum_(i < n.+1) 0 * (x`_i).2).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> k`_i * (x`_i).2 = 0 * (x`_i).2).
    move/eqP => intel_tmp.
    rewrite intel_tmp.
    prefield. ring.
  rewrite intel3.
  have intel4 : (\sum_(i < n.+1) 0 * (x`_i).2 
                          = \sum_(i < n.+1) 0).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> 0 * (x`_i).2 = 0 ).
    move/eqP => intel2_tmp.
    prefield. ring.
  rewrite intel4.
  rewrite sumr_const.
  
  have intel5 : (\sum_(i < n.+1) k`_i * f ((x`_i).1, (x`_i).2)
                          = \sum_(i < n.+1) 0 * f ((x`_i).1, (x`_i).2)).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> k`_i * f ((x`_i).1, (x`_i).2) 
                          = 0 * f ((x`_i).1, (x`_i).2)).
    move/eqP => intel_tmp.
    rewrite intel_tmp.
    prefield. ring.
  rewrite intel5.
  have intel6 : (\sum_(i < n.+1) 0 * f ((x`_i).1, (x`_i).2)
                          = \sum_(i < n.+1) 0).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> 0 * f ((x`_i).1, (x`_i).2) = 0 ).
    move/eqP => intel2_tmp.
    prefield. ring.
  rewrite intel6 sumr_const -mulr_natr !mul0l !plus0l.
  by [].

(* Ici on est toujours dans le premier cas où ns1 : n>1 est vrai *)

(* Cas où lambda est différent de 0 *)

set x1 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1)/lambda.
  set x2 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2)/lambda.
  rewrite big_ord_recr !//= big_ord_recr !//=.
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1
                   = x1 * lambda);last first.
    rewrite /x1.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div mul1r [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2
                   = x2 * lambda);last first.
    rewrite /x2.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div mul1r [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].
  rewrite big_ord_recr !//=.

  (* ....................................... *)

(* Cas où lambda est différent de 0, on applique donc l'inégalité de convexité 
   large et l'hypothèse de récurrence *)
have convex_large : (Num.le (f (x1 * lambda + k`_n * (x`_n).1,
                                        x2 * lambda + k`_n * (x`_n).2))
                              (lambda* f(x1,x2) + k`_n * f ((x`_n).1, (x`_n).2))).
      have lambda_pos: lambda>=0.
        rewrite /lambda.
        move: hypok.
        rewrite -big_andE big_ord_recr.
        change (\big[andb_monoid/true]_(i < n) Num.le 0
                                    k`_i &&
              (Num.le 0 k`_n) -> Num.le 0 (\sum_(i < n) k`_i)).
        rewrite big_andE.
        move/andP=> hypok.
        move: hypok.
        move => [hypok dernier].
        by apply : (pos_elt_pos_sum hypok).
      


          have infokn: k`_n = 1 - lambda.
          rewrite /lambda.
          Search _ (_ = _  -> _+_ =_+_).
          rewrite -somme_egal_1 big_ord_recr !//=.
          set sum_n := \sum_(i < n) k`_i.
          simpl in sum_n.
          prefield. ring.
        set x_f := (x1, x2).
        set y_f := ((x`_n).1, (x`_n).2).
        have egalx1 : (x_f.1 = x1).
          by [].
        have egalx2 : (x_f.2 = x2).
          by [].
        have egaly1 : (y_f.1 = (x`_n).1).
          by [].
        have egaly2 : (y_f.2 = (x`_n).2).
          by [].
        rewrite -egalx1 -egalx2 -egaly1 -egaly2.
        simpl in x_f, y_f.

        rewrite (_: x_f.1 * lambda = lambda * x_f.1); last first.
          prefield. ring.
        rewrite (_: x_f.2 * lambda = lambda * x_f.2); last first.
          prefield. ring.

        move: lambda_pos.
        rewrite infokn.
        have intel: (Num.le lambda 1).
          rewrite (_ : lambda = 1 - k`_n).
            change (Num.le (1 - k`_n) (1-0)).
            Search _ (Num.le (_-_) _).
            rewrite ler_sub.
                by [].
              by [].
            move/forallP: hypok.
            move=> hypok.
            About ord_max.
            set ord_n := (@ord_max n).
            move: (hypok ord_n).
            rewrite /=.
            by [].
          rewrite infokn.
          simpl in lambda.
          prefield; ring.
        move: intel.
        move=> intel intel2.
        apply : (f_is_convex).
          by [].
        by [].


      have autre_ing : f (x1, x2)
            <= \sum_(i<n) (k`_((nat_of_ord) i))/lambda
                    *(f ((x`_((nat_of_ord) i)).1, (x`_((nat_of_ord) i)).2 )).
       

        have info1: (\sum_(i < n) k`_i/lambda = 1).
          rewrite (_ : \sum_(i < n) k`_i/lambda = (\sum_(i < n) k`_i)/lambda).
            rewrite /lambda.
            Search _ (_/_= 1).
            rewrite divff.
            reflexivity.
            rewrite -/lambda.
            move/negPf : info.
            case tmp2 : (lambda == 0).
              by [].
            by [].

          rewrite (_ : (\sum_(i < n) k`_i) / lambda = (\sum_(i < n) k`_i)* (1 / lambda));
          last first.
          prefield. ring.
        rewrite mulr_suml.

        set F1 := fun i:'I_n => k`_i / lambda.
        set F2 := fun i:'I_n => k`_i * (1 / lambda).

        apply (eq_bigr F2).
        move=> i tmp.
        rewrite /F2.
        prefield; ring.

        rewrite /x1 /x2.
        rewrite (_ : f
     ((\sum_(i < n) k`_i * (x`_i).1) / lambda,
     (\sum_(i < n) k`_i * (x`_i).2) / lambda) = f
                                     ((\sum_(i < n) k`_i * (x`_i).1)* (1 / lambda),
                                     (\sum_(i < n) k`_i * (x`_i).2)* (1 / lambda)));
last first.
  Search _ (_*_/_).
  Search _ (_/1).
  rewrite -[X in _ = f
  (X * (1 / lambda),
  (\sum_(i < n) k`_i * (x`_i).2) * (1 / lambda))]divr1.
  rewrite -[X in _ = f
  (_ * (1 / lambda),
  (X * (1 / lambda)))]divr1.
  rewrite mulf_div !mul1r !mul1l.
  reflexivity.
rewrite !mulr_suml.

have info11: (\sum_(i < n) k`_i/lambda = 1).
  rewrite (_ : \sum_(i < n) k`_i/lambda = (\sum_(i < n) k`_i)/lambda).
    rewrite /lambda.
    Search _ (_/_= 1).
    rewrite divff.
    reflexivity.
    rewrite -/lambda.
    move/negPf : info.
    case tmp2 : (lambda == 0).
      by [].
    by [].

  rewrite (_ : (\sum_(i < n) k`_i) / lambda = (\sum_(i < n) k`_i)* (1 / lambda));
  last first.
  prefield. ring.
rewrite mulr_suml.

set F1 := fun i:'I_n => k`_i / lambda.
set F2 := fun i:'I_n => k`_i * (1 / lambda).

apply (eq_bigr F2).
move=> i tmp.
rewrite /F2.
prefield; ring.

        rewrite (_ : (\sum_(i < n) k`_i * (x`_i).1 *(1 / lambda)
                        = (\sum_(i < n) (k`_i/lambda) *  (x`_i).1))); last first.
          apply: eq_bigr.
          move=> i inutile.
          prefield. ring.

        rewrite (_ : (\sum_(i < n) k`_i * (x`_i).2 *(1 / lambda)
                        = (\sum_(i < n) (k`_i/lambda) *  (x`_i).2))); last first.
          apply: eq_bigr.
          move=> i inutile.
          prefield. ring.

        set F1 := fun i => k`_i / lambda.
            set k_sur_lam := mkseq F1 n.
            move:info11.
            rewrite (_ : \sum_(i < n) k`_i / lambda = \sum_(i < n) k_sur_lam`_i); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              About nth_mkseq.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

            rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i).1
                         = \sum_(i < n) k_sur_lam`_i * (x`_i).1); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              About nth_mkseq.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

            rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i).2
                         = \sum_(i < n) k_sur_lam`_i * (x`_i).2); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              About nth_mkseq.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

            rewrite (_ : (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2)
                    = (\sum_(i < n) k_sur_lam`_i * f ((x`_i).1, (x`_i).2)))); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              About nth_mkseq.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].



move=> sum_k_sur_lam.
apply :IHn.
by [].
by [].
have hypokN_lam : ([forall (i:'I_n | true), Num.le 0 k`_i]
                   = [forall (i:'I_n | true), Num.le 0 k_sur_lam`_i]).
    rewrite -!big_andE.
    apply: eq_bigr.
    move => i tmp.
    rewrite /k_sur_lam.
    simpl in F1.
    About nth_mkseq.
    rewrite (nth_mkseq ) /F1.
    Search _ (Num.lt 0 (_/_)).
      (* preuve que lambda >= 0 *)
      have lambda_pos : lambda>=0.
        rewrite /lambda.
        move : hypok.
  rewrite -big_andE big_ord_recr.
  change (\big[andb_monoid/true]_(i :'I_n) Num.le 0 k`_ i && Num.le 0 k`_n 
          -> Num.le 0 (\sum_(i0 < n) k`_i0)).
  move/andP => hypok.
  move:hypok.
  move=> [hypok dernier].
  move:hypok.
  rewrite big_andE => hypok.
  apply: pos_elt_pos_sum.
  by [].
        Search _ (Num.le 0 (_/_)).
        Search _ (_=_ <-> _=_).
        apply eq_iff_eq_true.
        split.
          move => hyp1.
          apply: divr_ge0.
          by [].
        by [].
        move=> hyp2.
        rewrite (_ : k`_i =( k`_i/lambda) *lambda); last first.
          simpl in lambda, k.
          set tmp1 := k`_i.
          set tmp2 := lambda.
          simpl in tmp1.
          prefield. field.
          rewrite /tmp2.
          move/eqP:info.
          by [].
        Search _ (Num.lt 0 (_*_)).
        apply mulr_ge0.
          by [].
        by [].
        by [].
    move: hypok.
    rewrite -big_andE big_ord_recr !//= big_andE.
    move/andP => hypokN.
    move:hypokN.
    move=> [hypokN hypodernier].
    move: hypokN.
    rewrite hypokN_lam.
    move=> hypokN.



by [].



(* On va combiner convex_large et autre_ing pour prouver le but *)
have autre_ing2 :  (Num.le (lambda * f (x1, x2) + k`_n * f ((x`_n).1, (x`_n).2))
                (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))
                      + k`_n * f ((x`_n).1, (x`_n).2))).
  Search _ (Num.lt (_+_) (_+_)) (Num.lt _ _).
  set term1 := lambda * f (x1, x2).
  set term2 := (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))).
  set term3 := (k`_n * f ((x`_n).1, (x`_n).2)).
  simpl in term1, term2, term3.
  About ler_add2r.
  rewrite ler_add2r /term1 /term2.
  Search _ (Num.le (_*_) (_*_)).
  Search _ (Num.le 0 (_-_)).
  rewrite -subr_ge0.
  Search _ ((_*_) - (_ *_)).
  rewrite -mulrBr.
  apply: mulr_ge0.

have lambda_pos: lambda>=0.
        rewrite /lambda.
        move: hypok.
        rewrite -big_andE big_ord_recr.
        change (\big[andb_monoid/true]_(i < n) Num.le 0
                                    k`_i &&
              (Num.le 0 k`_n) -> Num.le 0 (\sum_(i < n) k`_i)).
        rewrite big_andE.
        move/andP=> hypok.
        move: hypok.
        move => [hypok dernier].
        by apply : (pos_elt_pos_sum hypok).
      by [].
rewrite subr_ge0.
by [].


move: autre_ing2.

rewrite (_ : lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))
                = (\sum_(i < n) k`_i * f ((x`_i).1, (x`_i).2))).
  move=> autre_ing2.
apply (ler_trans convex_large autre_ing2).


rewrite mulr_sumr.
  set F1 := fun i:'I_n => lambda * (k`_i / lambda * f ((x`_i).1, (x`_i).2)) .
  set F2 := fun i:'I_n => k`_i * f ((x`_i).1, (x`_i).2).
  apply: eq_bigr.
  move=> i tmp.
  set tmp1 := f ((x`_i).1, (x`_i).2).
  set tmp2 :=lambda.
  set tmp3 := k`_i.
  simpl in tmp2, tmp3.
  prefield. field.
  rewrite /tmp2.
  move/eqP: info.
  by [].

(* Le dernier but à prouver correspond est le suivant et correspond au cas où
   ns1 : (1 < n)%N = false ce qui revient à dire que n = 1 grâce à 
   l'hypothèse nsup1 : (1 < n.+1)%N *)
have n_egal_1 : (1 = n)%N.
  move: nsup1.
  rewrite ltnS.
  move=> nsup1.
  move: ns1.
  rewrite ltnNge.
  move/negP => ninf1.
  move:ninf1.
  move/negP => ninf1.
  move: nsup1.
  rewrite leq_eqVlt.
  move=> nsup1.
  apply: anti_leq.
  rewrite ninf1 andb_true_r leq_eqVlt.
  by [].


have Sn_egal2 : 2 = n.+1.
  rewrite n_egal_1.
  reflexivity.

move: ex somme_egal_1 hypok.
rewrite -!Sn_egal2.
move=> ex somme_egal_1 hypok.


have info1 : k`_1 = 1 - k`_0.
  move: somme_egal_1.
  rewrite big_ord_recr.
  change ((\sum_(i :'I_1) (k`_i)) + k`_1 = 1 -> k`_1 = 1 - k`_0).
  rewrite big_ord_recr big_ord0.
  change (0 + k`_0 + k`_1 = 1 -> k`_1 = 1 - k`_0).
  rewrite plus0l.
  move=> tmp.
  rewrite -tmp.
  set a := k`_0.
  set b := k`_1.
  simpl in a, b.
  prefield. ring.


rewrite big_ord_recr.
change (Num.le
  (f
     (\sum_(i:'I_1) (k`_i* (x`_i).1) + (k`_1 * (x`_1).1),
     \sum_(i < 2) k`_i * (x`_i).2)   )
  (\sum_(i < 2) k`_i * f ((x`_i).1, (x`_i).2))).
rewrite !big_ord_recr !big_ord0.
change (Num.le
  (f
     (0 + (k`_0 * (x`_0).1) + (k`_1 * (x`_1).1),
     0 + (k`_0 * (x`_0).2) + (k`_1 * (x`_1).2)  )   )
  (0 + k`_0 * f ((x`_0).1, (x`_0).2) + k`_1 * f ((x`_1).1, (x`_1).2))).

rewrite !plus0l.
rewrite info1.

have tmp1 : x`_0 = ((x`_0).1, (x`_0).2).
  Search _ (_ = (_,_)).
  apply: surjective_pairing.
have tmp2 : x`_1 = ((x`_1).1, (x`_1).2).
  Search _ (_ = (_,_)).
  apply: surjective_pairing.

rewrite -tmp1 -tmp2.

move: hypok.
rewrite -big_andE.
rewrite !big_ord_recr !big_ord0.
change (Num.le 0 k`_0 && Num.le 0 k`_1 -> Num.le
  (f
     (k`_0 * (x`_0).1 + (1 - k`_0) * (x`_1).1,
     k`_0 * (x`_0).2 + (1 - k`_0) * (x`_1).2))
  (k`_0 * f x`_0 + (1 - k`_0) * f x`_1)
).
move/andP=> hypok.
move:hypok.
move=> [hypok0 hypok1].


have info2 : k`_0 = 1 - k`_1.
  move: somme_egal_1.
  rewrite big_ord_recr.
  change ((\sum_(i :'I_1) (k`_i)) + k`_1 = 1 -> k`_0 = 1 - k`_1).
  rewrite big_ord_recr big_ord0.
  change (0 + k`_0 + k`_1 = 1 -> k`_0 = 1 - k`_1).
  rewrite plus0l.
  move=> tmp.
  rewrite -tmp.
  set a := k`_0.
  set b := k`_1.
  simpl in a, b.
  prefield. ring.

have info3 : Num.le k`_0 1.
  rewrite info2.
  change (Num.le (1 - k`_1) (1-0)).
  Search _ (Num.le (_-_) (_-_)).
  apply: ler_sub.
    by [].
  by [].


have ineg0 : (0<2)%N.
  by apply: ltn_trans (ltnSn 0) (ltnSn 1).

have ineg1 : (1<2)%N.
  by apply: (ltnSn 1).
apply: f_is_convex.
  by [].
by [].
Qed.



Lemma lt_implies_le (n:nat) (k: seq rat) :
  [forall (i:'I_n|true), (Num.lt 0 k`_((nat_of_ord) i))]
    -> [forall (i:'I_n|true), (Num.le 0 k`_((nat_of_ord) i))].
Proof.
move=> hypok.
induction n.
  rewrite -big_andE.
  by rewrite big_ord0 !//=.
rewrite -big_andE.
rewrite big_ord_recr !//=.
apply/andP.
split.
  move:hypok.
  rewrite -big_andE.
  rewrite big_ord_recr !//=.
  move/andP=>hypok.
  move: hypok.
  rewrite !big_andE.
  move=> [hypokN dernier].
  apply (IHn hypokN).
move:hypok.
rewrite -big_andE.
rewrite big_ord_recr !//=.
move/andP=>hypok.
move: hypok.
rewrite !big_andE.
move=> [hypokN dernier].
move : dernier.
rewrite lt0r.
move/andP=>dernier.
move:dernier.
move=>[dernier1 dernier2].
by [].
Qed.


Lemma Jensen_inequality_strict (n:nat) (f : rat*rat -> rat) 
              (f_is_convex : convex_strict_fun f)
          (x :seq (rat*rat)) (nsup1 : (n>1)%nat )
             :
   forall k:seq rat,(\sum_(i<n) (k`_((nat_of_ord) i)) = 1)->
      [forall (i:'I_n|true), (Num.lt 0 k`_((nat_of_ord) i))] 
    -> [exists (i:'I_n|true), [exists (j:'I_n|true),
                      ((x`_i).1 != (x`_j).1) || ((x`_i).2 != (x`_j).2) ]]
  -> f (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1, 
          \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2)
            < \sum_(i<n) (k`_((nat_of_ord) i))
                    *(f ((x`_((nat_of_ord) i)).1, (x`_((nat_of_ord) i)).2 )).
Proof.
induction n.
  move:nsup1.
  by rewrite !//=.
move=> k somme_egal_1 hypok ex.
set lambda := \sum_(i<n) (k`_((nat_of_ord) i)).
case ns1 : (1 < n)%N.
  case info: (lambda==0).

  rewrite !big_ord_recr !//=.
  have hypokle : forall m, (m<(S n))%N -> 
            [forall (i :'I_m| true), Num.le 0 (k`_((nat_of_ord) i))].
        induction m.
          rewrite -big_andE.
          by rewrite big_ord0.
        rewrite -big_andE big_ord_recr !//=.
        move=>inf.
        rewrite big_andE.
        apply/andP.
        split.
          case info_utile: (m<(S n))%N.
            apply (IHm info_utile).
          move: info_utile.
          move/negbT => info_utile.
          rewrite -leqNgt in info_utile.
          auto.
        have ineg: (m<n.+1)%N.
          exact: (ltn_trans (ltnSn m) (inf)).
        have t: Num.lt 0 k`_m; last first.
          rewrite le0r.
          apply/orP.
          by right.
        move/forallP :  hypok.
        move=> hypok.
        set m_ord := Ordinal ineg.
        change (true ==>Num.lt 0 k`_(m_ord) ).
        apply: hypok.
  have contra: (Num.lt 0 (\sum_(i<n) (k`_((nat_of_ord) i)))).
    move: hypok.
    rewrite -big_andE !//= big_ord_recr !//=.
    move/andP=> hypok.
    move :hypok.
    move=> [hypok1 hypok2].
    move: hypok1.
    rewrite big_andE.
    move=> hypok1.
  move: somme_egal_1 nsup1 IHn ex lambda info hypokle hypok2 hypok1 ns1.
  case : n.
    move=> h1 h2.
    by [].
  move=> n somme_egal_1 nsup1 IHn ex lambda info hypokle hypok2 hypok1 ns1.
  apply (strict_pos_elt_strict_pos_sum hypok1).
  move:contra.
  rewrite -/lambda.
  move=> contra.
  rewrite lt0r in contra.
  move/andP:contra.
  move=> [contra1 contra2].
  move/negP:contra1.
  move=> contra1.
  by [].


(* Ici on est toujours dans le premier cas où ns1 : n>1 est vrai *)

(* Cas où lambda est différent de 0 *)

  set x1 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1)/lambda.
  set x2 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2)/lambda.
  rewrite big_ord_recr !//=.
  rewrite big_ord_recr !//=.
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1
                   = x1 * lambda);last first.
    rewrite /x1.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div mul1r [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2
                   = x2 * lambda);last first.
    rewrite /x2.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div mul1r [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].
  rewrite big_ord_recr !//=.

  (* ....................................... *)

    case x1_xn_egal: ((x1 == (x`_n).1) && (x2 == (x`_n).2)); last first.
      (* Dans le bout de code qui suit on peut appliquer hypconvex *)


    have : (Num.lt (f (x1 * lambda + k`_n * (x`_n).1, x2 * lambda + k`_n * (x`_n).2))
                  (lambda*(f (x1, x2)) + k`_n* (f ((x`_n).1, (x`_n).2)))).
    move:f_is_convex.
    rewrite /convex_strict_fun.
    move=> hypconvex.
      have : k`_n = 1 - lambda.
      rewrite /lambda.
      rewrite -somme_egal_1 big_ord_recr !//=.
      set sum_n := \sum_(i < n) k`_i.
      simpl in sum_n.
      prefield. ring.
    move=> info2.
    rewrite info2.
    set x_f := (x1, x2).
    set y_f := ((x`_n).1, (x`_n).2).
    have egalx1 : (x_f.1 = x1).
      by [].
    have egalx2 : (x_f.2 = x2).
      by [].
    have egaly1 : (y_f.1 = (x`_n).1).
      by [].
    have egaly2 : (y_f.2 = (x`_n).2).
      by [].
    rewrite -egalx1 -egalx2 -egaly1 -egaly2.
    simpl in x_f, y_f.
    have info3 : Num.lt 0 lambda.
      rewrite /lambda.
      rewrite lt0r.
      apply/andP.
      split.
        rewrite -/lambda.
        by rewrite info !//=.
      have hypokle : forall m, (m<(S n))%N -> 
            [forall (i :'I_m| true), Num.le 0 (k`_((nat_of_ord) i))].
        induction m.
          rewrite -big_andE.
          by rewrite big_ord0.
        rewrite -big_andE big_ord_recr !//=.
        move=>inf.
        rewrite big_andE.
        apply/andP.
        split.
          case info_utile: (m<(S n))%N.
            apply (IHm info_utile).
          move: info_utile.
          move/negbT => info_utile.
          rewrite -leqNgt in info_utile.
          auto.
        have ineg: (m<n.+1)%N.
          exact: (ltn_trans (ltnSn m) (inf)).
        have t: Num.lt 0 k`_m; last first.
          rewrite le0r.
          apply/orP.
          by right.
        move/forallP :  hypok.
        move=> hypok.
        set m_ord := Ordinal ineg.
        change (true ==>Num.lt 0 k`_(m_ord) ).
        apply: hypok.
      apply: pos_elt_pos_sum.
      by apply: hypokle.
    have info4: (Num.lt lambda 1).
      have info5 : lambda = 1 - k`_n.
        rewrite info2.
        simpl in lambda.
        prefield. ring.
      rewrite info5.
      rewrite -(ltr_add2r (k`_n -1) (1 - k`_n) 1).
      have w: (1 - k`_n + (k`_n - 1)) = 0.
        prefield; ring.
      rewrite w.
      have ww : (1 + (k`_n - 1)) = k`_n.
        prefield; ring.
      rewrite ww {ww}.
      rewrite {w}.
      move/forallP : hypok.
      move=> hypok.
      set n_ord := Ordinal (ltnSn n).
      change (true ==>Num.lt 0 k`_(n_ord) ).
      apply: hypok.
    case info_dif: (~~ (x_f.1 == y_f.1) || ~~ (x_f.2 == y_f.2)).
      rewrite (_ : x_f.1 * lambda =  lambda* x_f.1 ); last first.
        prefield; ring.
      rewrite (_ : x_f.2 * lambda =  lambda* x_f.2 ); last first.
        prefield; ring.
      apply (@hypconvex lambda x_f y_f info3 info4 info_dif).
    



(* Dans le bout de code qui suit on va appliquer hypconvex *)

rewrite (_ : x_f.1 * lambda = lambda * x_f.1); last first.
  prefield. ring.
rewrite (_ : x_f.2 * lambda = lambda * x_f.2); last first.
  prefield. ring.

apply: hypconvex.
  by [].
by [].
rewrite /x_f !//=.
move/negPf: x1_xn_egal.
set b1 := (x1 == (x`_n).1) .
set b2 := (x2 == (x`_n).2).
case infob1 : b1.
  case infob2 : b2.
    by [].
  by [].
by [].

(* A cet étape, on a l'inégalité de convexité stricte *)
(* Il ne reste alors qu'à appliquer Jensen large à f(x1, x2) *)


move=> info_strict_conv.
have autre_ing : f (x1, x2)
            <= \sum_(i<n) (k`_((nat_of_ord) i))/lambda
                    *(f ((x`_((nat_of_ord) i)).1, (x`_((nat_of_ord) i)).2 )).
   have hypokle : [forall (i :'I_(S n)| true), Num.le 0 (k`_((nat_of_ord) i))].
     apply: lt_implies_le hypok.
rewrite /x1 /x2.
rewrite (_ : f
     ((\sum_(i < n) k`_i * (x`_i).1) / lambda,
     (\sum_(i < n) k`_i * (x`_i).2) / lambda) = f
                                     ((\sum_(i < n) k`_i * (x`_i).1)* (1 / lambda),
                                     (\sum_(i < n) k`_i * (x`_i).2)* (1 / lambda)));
last first.
  rewrite -[X in _ = f
  (X * (1 / lambda),
  (\sum_(i < n) k`_i * (x`_i).2) * (1 / lambda))]divr1.
  rewrite -[X in _ = f
  (_ * (1 / lambda),
  (X * (1 / lambda)))]divr1.
  rewrite mulf_div !mul1r !mul1l.
  reflexivity.
rewrite !mulr_suml.

have info1: (\sum_(i < n) k`_i/lambda = 1).
  rewrite (_ : \sum_(i < n) k`_i/lambda = (\sum_(i < n) k`_i)/lambda).
    rewrite /lambda divff.
    reflexivity.
    rewrite -/lambda.
    move/negPf : info.
    case tmp2 : (lambda == 0).
      by [].
    by [].

  rewrite (_ : (\sum_(i < n) k`_i) / lambda = (\sum_(i < n) k`_i)* (1 / lambda));
  last first.
  prefield. ring.
rewrite mulr_suml.

set F1 := fun i:'I_n => k`_i / lambda.
set F2 := fun i:'I_n => k`_i * (1 / lambda).

apply (eq_bigr F2).
move=> i tmp.
rewrite /F2.
prefield; ring.


rewrite (_ : (\sum_(i < n) k`_i * (x`_i).1 *(1 / lambda)
                = (\sum_(i < n) (k`_i/lambda) *  (x`_i).1))); last first.
  apply: eq_bigr.
  move=> i inutile.
  prefield. ring.

rewrite (_ : (\sum_(i < n) k`_i * (x`_i).2 *(1 / lambda)
                = (\sum_(i < n) (k`_i/lambda) *  (x`_i).2))); last first.
  apply: eq_bigr.
  move=> i inutile.
  prefield. ring.

set F1 := fun i => k`_i / lambda.
    set k_sur_lam := mkseq F1 n.
    move:info1.
    rewrite (_ : \sum_(i < n) k`_i / lambda = \sum_(i < n) k_sur_lam`_i); last first.
      apply eq_bigr.
      move=> i tmp.
      rewrite /k_sur_lam.
      simpl in F1.
      rewrite (nth_mkseq ) /F1.
      reflexivity.
      by [].

    rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i).1
                 = \sum_(i < n) k_sur_lam`_i * (x`_i).1); last first.
      apply eq_bigr.
      move=> i tmp.
      rewrite /k_sur_lam.
      simpl in F1.
      rewrite (nth_mkseq ) /F1.
      reflexivity.
      by [].

    rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i).2
                 = \sum_(i < n) k_sur_lam`_i * (x`_i).2); last first.
      apply eq_bigr.
      move=> i tmp.
      rewrite /k_sur_lam.
      simpl in F1.
      rewrite (nth_mkseq ) /F1.
      reflexivity.
      by [].

    rewrite (_ : (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2)
            = (\sum_(i < n) k_sur_lam`_i * f ((x`_i).1, (x`_i).2)))); last first.
      apply eq_bigr.
      move=> i tmp.
      rewrite /k_sur_lam.
      simpl in F1.
      rewrite (nth_mkseq ) /F1.
      reflexivity.
      by [].

have hypokN_lam : ([forall (i:'I_n | true), Num.lt 0 k`_i]
                   = [forall (i:'I_n | true), Num.lt 0 k_sur_lam`_i]).
    rewrite -!big_andE.
    apply: eq_bigr.
    move => i tmp.
    rewrite /k_sur_lam.
    simpl in F1.
    rewrite (nth_mkseq ) /F1.
      (* preuve que lambda > 0 *)
      have lambda_pos : lambda>0.
        rewrite /lambda.
move: somme_egal_1 nsup1 IHn ex lambda info x1 x2 x1_xn_egal 
      info_strict_conv F1 k_sur_lam hypok ns1  i
     hypokle.
        case : n.
          by [].
move=> n somme_egal_1 nsup1 IHn ex lambda info x1 x2 x1_xn_egal 
      info_strict_conv F1 k_sur_lam hypok ns1  i hypokle
      .
move: hypok.
rewrite -big_andE big_ord_recr !//= big_andE.
move/andP => hypokSN.
move:hypokSN.
move=> [hypokSN hypodernier].
        apply (strict_pos_elt_strict_pos_sum hypokSN).
        apply eq_iff_eq_true.
        split.
          move => hyp1.
          apply: divr_gt0.
          by [].
        by [].
        move=> hyp2.
        rewrite (_ : k`_i =( k`_i/lambda) *lambda); last first.
          simpl in lambda, k.
          set tmp1 := k`_i.
          set tmp2 := lambda.
          simpl in tmp1.
          prefield. field.
          move:lambda_pos.
          rewrite lt0r.
          move/andP=> lambda_pos.
          move: lambda_pos.
          move=> [lambda_nonul lambda_pos].
          move/eqP: lambda_nonul.
          by [].
        apply mulr_gt0.
          by [].
        by [].
        by [].
    move: hypok.
    rewrite -big_andE big_ord_recr !//= big_andE.
    move/andP => hypokN.
    move:hypokN.
    move=> [hypokN hypodernier].
    move: hypokN.
    rewrite hypokN_lam.
    move=> hypokN.


move=>info_k_sur_lam.
  apply (@Jensen_inequality n f (convex_strict_implies_convex f_is_convex) 
                x ns1 k_sur_lam info_k_sur_lam (lt_implies_le hypokN)).

(* On va combiner info_strict_conv et autre_ing pour prouver le but *)
have autre_ing2 :  (Num.le (lambda * f (x1, x2) + k`_n * f ((x`_n).1, (x`_n).2))
                (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))
                      + k`_n * f ((x`_n).1, (x`_n).2))).
  set term1 := lambda * f (x1, x2).
  set term2 := (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))).
  set term3 := (k`_n * f ((x`_n).1, (x`_n).2)).
  simpl in term1, term2, term3.
  apply : ler_add; last first.
    by [].
  rewrite /term1 /term2 -subr_ge0.
  rewrite -mulrBr.
  apply: mulr_ge0.
  rewrite /lambda.
    move: (lt_implies_le hypok).
    rewrite -big_andE big_ord_recr !//=.
    move/andP=> hypokle.
    move:hypokle.
    move => [hypokl1 dernier].
    move: hypokl1.
    rewrite big_andE.
    move=> hypokl1.
  apply (pos_elt_pos_sum hypokl1).
  rewrite subr_ge0.
  by [].

move: autre_ing2.
rewrite (_ : lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))
                = (\sum_(i < n) k`_i * f ((x`_i).1, (x`_i).2))).
  move=> autre_ing2.
  apply: (ltr_le_trans info_strict_conv autre_ing2).
  rewrite mulr_sumr.
  set F1 := fun i:'I_n => lambda * (k`_i / lambda * f ((x`_i).1, (x`_i).2)) .
  set F2 := fun i:'I_n => k`_i * f ((x`_i).1, (x`_i).2).
  apply: eq_bigr.
  move=> i tmp.
  set tmp1 := f ((x`_i).1, (x`_i).2).
  set tmp2 :=lambda.
  set tmp3 := k`_i.
  simpl in tmp2, tmp3.
  prefield. field.
  rewrite /tmp2.
  have lambda_pos: lambda>0.
    rewrite /lambda.
    move: nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 autre_ing x1_xn_egal  info_strict_conv tmp2 ns1 F2 i tmp1 tmp3.
    case : n.
      by [].
    move=> n  nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 autre_ing x1_xn_egal  info_strict_conv tmp2 ns1 F2 i tmp1 tmp3.
    have hypokSn : [forall (i:'I_(S n) | true), Num.lt 0 k`_i].
      move: hypok.
      rewrite -big_andE big_ord_recr !//=.
      move/andP=> hypok.
      move: hypok.
      move=> [hypok1 hypok2].
      move: hypok1.
      rewrite big_andE.
      by [].
    apply (strict_pos_elt_strict_pos_sum hypokSn).
    move: lambda_pos.
    rewrite lt0r.
    move/andP=> lambda_pos.
    move: lambda_pos.
    move=> [lambda_pos1 lambda_pos2].
    apply/eqP.
    by [].


(* Nous sommes ici dans le où lambda différent de 0 et il existe i j<n tel que
   xi différent de xj *)
case xi_dif_xj_n : [exists (i:'I_n | true),
        [exists (j:'I_n | true),
        ~~ ((x`_i).1 == (x`_j).1) || ~~ ((x`_i).2 == (x`_j).2)]].
    have convex_large : (Num.le (f (x1 * lambda + k`_n * (x`_n).1,
                                        x2 * lambda + k`_n * (x`_n).2))
                              (lambda* f(x1,x2) + k`_n * f ((x`_n).1, (x`_n).2))).
      have lambda_pos: lambda>0.
        rewrite /lambda.
        move: nsup1 IHn somme_egal_1 hypok ex lambda info x1 
              x2 x1_xn_egal ns1 xi_dif_xj_n.
        case : n.
          by [].
        move=> n nsup1 IHn somme_egal_1 hypok ex lambda info x1 
              x2 x1_xn_egal ns1 xi_dif_xj_n.
        have hypokSn : [forall (i:'I_(S n) | true), Num.lt 0 k`_i].
          move: hypok.
          rewrite -big_andE big_ord_recr !//=.
          move/andP=> hypok.
          move: hypok.
          move=> [hypok1 hypok2].
          move: hypok1.
          rewrite big_andE.
          by [].
        apply (strict_pos_elt_strict_pos_sum hypokSn).


          have infokn: k`_n = 1 - lambda.
          rewrite /lambda -somme_egal_1 big_ord_recr !//=.
          set sum_n := \sum_(i < n) k`_i.
          simpl in sum_n.
          prefield. ring.
        set x_f := (x1, x2).
        set y_f := ((x`_n).1, (x`_n).2).
        have egalx1 : (x_f.1 = x1).
          by [].
        have egalx2 : (x_f.2 = x2).
          by [].
        have egaly1 : (y_f.1 = (x`_n).1).
          by [].
        have egaly2 : (y_f.2 = (x`_n).2).
          by [].
        rewrite -egalx1 -egalx2 -egaly1 -egaly2.
        simpl in x_f, y_f.

        rewrite (_: x_f.1 * lambda = lambda * x_f.1); last first.
          prefield. ring.
        rewrite (_: x_f.2 * lambda = lambda * x_f.2); last first.
          prefield. ring.

        move: lambda_pos.
        rewrite lt0r.
        move/andP=> lambda_pos.
        move:lambda_pos.
        move=> [lambda_pos1 lambda_pos2].
        have info4: (Num.le lambda 1).
          rewrite (_ : lambda = 1 - k`_n).
            change (Num.le (1 - k`_n) (1-0)).
            rewrite ler_sub.
                by [].
              by [].
            move/forallP: hypok.
            move=> hypok.
            set ord_n := (@ord_max n).
            move: (hypok ord_n).
            rewrite /= lt0r.
            move/andP=> kn0a.
            move:kn0a.
            move=> [kn0a kn0b].
            by [].
          rewrite infokn.
          simpl in lambda.
          prefield; ring.
        rewrite infokn /convex_fun.
        apply (convex_strict_implies_convex f_is_convex) .
          by [].
        by [].

      have autre_ing : f (x1, x2)
            < \sum_(i<n) (k`_((nat_of_ord) i))/lambda
                    *(f ((x`_((nat_of_ord) i)).1, (x`_((nat_of_ord) i)).2 )).
        have hypokle : [forall (i :'I_(S n)| true), Num.le 0 (k`_((nat_of_ord) i))].
          apply: lt_implies_le hypok.
        rewrite /x1 /x2.
        rewrite (_ : f
             ((\sum_(i < n) k`_i * (x`_i).1) / lambda,
             (\sum_(i < n) k`_i * (x`_i).2) / lambda) = f
                                             ((\sum_(i < n) k`_i * (x`_i).1)* (1 / lambda),
                                             (\sum_(i < n) k`_i * (x`_i).2)* (1 / lambda)));
        last first.
          rewrite -[X in _ = f
          (X * (1 / lambda),
          (\sum_(i < n) k`_i * (x`_i).2) * (1 / lambda))]divr1.
          rewrite -[X in _ = f
          (_ * (1 / lambda),
          (X * (1 / lambda)))]divr1.
          rewrite mulf_div !mul1r !mul1l.
          reflexivity.
        rewrite !mulr_suml.


        have info1: (\sum_(i < n) k`_i/lambda = 1).
          rewrite (_ : \sum_(i < n) k`_i/lambda = (\sum_(i < n) k`_i)/lambda).
            rewrite /lambda divff.
            reflexivity.
            rewrite -/lambda.
            move/negPf : info.
            case tmp2 : (lambda == 0).
              by [].
            by [].

          rewrite (_ : (\sum_(i < n) k`_i) / lambda = (\sum_(i < n) k`_i)* (1 / lambda));
          last first.
          prefield. ring.
        rewrite mulr_suml.

        set F1 := fun i:'I_n => k`_i / lambda.
        set F2 := fun i:'I_n => k`_i * (1 / lambda).

        apply (eq_bigr F2).
        move=> i tmp.
        rewrite /F2.
        prefield; ring.


        rewrite (_ : (\sum_(i < n) k`_i * (x`_i).1 *(1 / lambda)
                        = (\sum_(i < n) (k`_i/lambda) *  (x`_i).1))); last first.
          apply: eq_bigr.
          move=> i inutile.
          prefield. ring.

        rewrite (_ : (\sum_(i < n) k`_i * (x`_i).2 *(1 / lambda)
                        = (\sum_(i < n) (k`_i/lambda) *  (x`_i).2))); last first.
          apply: eq_bigr.
          move=> i inutile.
          prefield. ring.

        set F1 := fun i => k`_i / lambda.
            set k_sur_lam := mkseq F1 n.
            move:info1.
            rewrite (_ : \sum_(i < n) k`_i / lambda = \sum_(i < n) k_sur_lam`_i); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

            rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i).1
                         = \sum_(i < n) k_sur_lam`_i * (x`_i).1); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

            rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i).2
                         = \sum_(i < n) k_sur_lam`_i * (x`_i).2); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

            rewrite (_ : (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2)
                    = (\sum_(i < n) k_sur_lam`_i * f ((x`_i).1, (x`_i).2)))); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].



move=> sum_k_sur_lam.
apply :IHn.
by [].
by [].
have hypokN_lam : ([forall (i:'I_n | true), Num.lt 0 k`_i]
                   = [forall (i:'I_n | true), Num.lt 0 k_sur_lam`_i]).
    rewrite -!big_andE.
    apply: eq_bigr.
    move => i tmp.
    rewrite /k_sur_lam.
    simpl in F1.
    rewrite (nth_mkseq ) /F1.
      (* preuve que lambda > 0 *)
      have lambda_pos : lambda>0.
        rewrite /lambda.
move: somme_egal_1 nsup1 ex lambda info x1 x2 x1_xn_egal 
       hypok ns1 xi_dif_xj_n i
      convex_large F1  k_sur_lam sum_k_sur_lam hypokle.
        case : n.
          by [].
move=> n somme_egal_1 nsup1 ex lambda info x1 x2 x1_xn_egal 
       hypok ns1 xi_dif_xj_n i
      convex_large F1  k_sur_lam sum_k_sur_lam hypokle.
move: hypok.
rewrite -big_andE big_ord_recr !//= big_andE.
move/andP => hypokSN.
move:hypokSN.
move=> [hypokSN hypodernier].
        apply (strict_pos_elt_strict_pos_sum hypokSN).
        apply eq_iff_eq_true.
        split.
          move => hyp1.
          apply: divr_gt0.
          by [].
        by [].
        move=> hyp2.
        rewrite (_ : k`_i =( k`_i/lambda) *lambda); last first.
          simpl in lambda, k.
          set tmp1 := k`_i.
          set tmp2 := lambda.
          simpl in tmp1.
          prefield. field.
          move:lambda_pos.
          rewrite lt0r.
          move/andP=> lambda_pos.
          move: lambda_pos.
          move=> [lambda_nonul lambda_pos].
          move/eqP: lambda_nonul.
          by [].
        apply mulr_gt0.
          by [].
        by [].
        by [].
    move: hypok.
    rewrite -big_andE big_ord_recr !//= big_andE.
    move/andP => hypokN.
    move:hypokN.
    move=> [hypokN hypodernier].
    move: hypokN.
    rewrite hypokN_lam.
    move=> hypokN.



by [].
by [].


(* On va combiner convex_large et autre_ing pour prouver le but *)
have autre_ing2 :  (Num.lt (lambda * f (x1, x2) + k`_n * f ((x`_n).1, (x`_n).2))
                (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))
                      + k`_n * f ((x`_n).1, (x`_n).2))).
  set term1 := lambda * f (x1, x2).
  set term2 := (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))).
  set term3 := (k`_n * f ((x`_n).1, (x`_n).2)).
  simpl in term1, term2, term3.
  rewrite ltr_add2r /term1 /term2.
  rewrite -subr_gt0 -mulrBr.
  apply: mulr_gt0.



have lambda_pos : lambda>0.
        rewrite /lambda.
move: somme_egal_1 nsup1 ex lambda info x1 x2 x1_xn_egal 
       hypok ns1 xi_dif_xj_n 
      convex_large autre_ing term1 term2 term3 IHn.
        case : n.
          by [].
move=> n somme_egal_1 nsup1 ex lambda info x1 x2 x1_xn_egal 
       hypok ns1 xi_dif_xj_n 
      convex_large autre_ing term1 term2 term3 IHn.
move: hypok.
rewrite -big_andE big_ord_recr !//=.
rewrite big_andE.
move/andP => hypokSN.
move:hypokSN.
move=> [hypokSN hypodernier].
        apply (strict_pos_elt_strict_pos_sum hypokSN).
        apply eq_iff_eq_true.
        split.
          move => hyp1.
          by [].
        by [].
    Search _ (Num.lt 0 (_-_)).
    by rewrite subr_gt0.

move: autre_ing2.

rewrite (_ : lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i).1, (x`_i).2))
                = (\sum_(i < n) k`_i * f ((x`_i).1, (x`_i).2))).
  move=> autre_ing2.
apply (ler_lt_trans convex_large autre_ing2).


rewrite mulr_sumr.
  set F1 := fun i:'I_n => lambda * (k`_i / lambda * f ((x`_i).1, (x`_i).2)) .
  set F2 := fun i:'I_n => k`_i * f ((x`_i).1, (x`_i).2).
  apply: eq_bigr.
  move=> i tmp.
  set tmp1 := f ((x`_i).1, (x`_i).2).
  set tmp2 :=lambda.
  set tmp3 := k`_i.
  simpl in tmp2, tmp3.
  prefield. field.
  rewrite /tmp2.
  have lambda_pos: lambda>0.
    rewrite /lambda.
    move: nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 autre_ing x1_xn_egal  tmp2 ns1 F2 i tmp1 tmp3 convex_large
            xi_dif_xj_n.
    case : n.
      by [].
    move=> n nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 autre_ing x1_xn_egal  tmp2 ns1 F2 i tmp1 tmp3 convex_large
            xi_dif_xj_n.
    have hypokSn : [forall (i:'I_(S n) | true), Num.lt 0 k`_i].
      move: hypok.
      rewrite -big_andE big_ord_recr !//=.
      move/andP=> hypok.
      move: hypok.
      move=> [hypok1 hypok2].
      move: hypok1.
      rewrite big_andE.
      by [].
    apply (strict_pos_elt_strict_pos_sum hypokSn).
    move: lambda_pos.
    rewrite lt0r.
    move/andP=> lambda_pos.
    move: lambda_pos.
    move=> [lambda_pos1 lambda_pos2].
    apply/eqP.
    by [].




(* Dans le bout de code qui suit on est dans le cas contradiction *)
(* ie cas où  [exists (i<n | true),
                 exists (j<n | true),
                 ~~ ((x`_i).1 == (x`_j).1)
                 || ~~ ((x`_i).2 == (x`_j).2)] = false *)


move/negbT: xi_dif_xj_n.

rewrite negb_exists /= => /forallP => fne.

have tous_egaux : [forall i: 'I_n, [forall j : 'I_n,
    ((x`_i).1 == (x`_j).1) && ((x`_i).2 == (x`_j).2)]].
apply/forallP => i; move:(fne i); rewrite negb_exists /= => /forallP fnei.
by apply/forallP => j; move:(fnei j); rewrite negb_orb !negb_involutive.

have tous_meme: ([forall (i:'I_(n)|true), (x`_i).1 == (x`_0).1] 
                      && [forall (i:'I_(n)|true), (x`_i).2 == (x`_0).2])
      ; last first.





(* Dans le bout de code qui suits on prouve (x1 = (x`_0).1) *)
        have hh1: (x1 = (x`_0).1).
          rewrite /x1.
          move/andP:tous_meme.
          move=> [tous_meme1 tous_meme2].
          (* rewrite tous_meme1. *)
  set F1 : 'I_n-> rat := fun i => k`_i * (x`_i).1.
  set F2 : 'I_n-> rat := fun i => k`_i * (x`_0).1.
  have F1eqF2 : (forall i : 'I_n, true -> F1 i = F2 i).
    move=> i true.
    rewrite /F1 /F2.
    move/forallP : tous_meme1.
    move=>tous_meme1.

    move: (tous_meme1 i).
    change (((x`_i).1 == (x`_0).1) ->
      k`_i * (x`_i).1 = k`_i * (x`_0).1).
    set ff := fun x => k`_i * x.
    move/eqP=> hyp1.
    by apply: (congr1 ff).


rewrite (eq_bigr F2 F1eqF2) /F2 -mulr_suml /lambda -/lambda.
prefield ; field.
have lambda_pos: lambda>0.
    rewrite /lambda.
    move: nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 x1_xn_egal ns1 F2 F1eqF2 fne tous_egaux tous_meme1 tous_meme2
            .
    case : n.
      by [].
    move=> n nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 x1_xn_egal ns1 F2 F1eqF2 fne tous_egaux tous_meme1 tous_meme2
            .
    have hypokSn : [forall (i:'I_(S n) | true), Num.lt 0 k`_i].
      move: hypok.
      rewrite -big_andE big_ord_recr !//=.
      move/andP=> hypok.
      move: hypok.
      move=> [hypok1 hypok2].
      move: hypok1.
      rewrite big_andE.
      by [].
    apply (strict_pos_elt_strict_pos_sum hypokSn).
    move: lambda_pos.
    rewrite lt0r.
    move/andP=> lambda_pos.
    move: lambda_pos.
    move=> [lambda_pos1 lambda_pos2].
    apply/eqP.
    by [].



(* Dans le bout de code qui suits on prouve (x2 = (x`_0).2) *)
        have hh2: (x2 = (x`_0).2).
          rewrite /x1.
          move/andP:tous_meme.
          move=> [tous_meme1 tous_meme2].
          (* rewrite tous_meme1. *)
  set F1 : 'I_n-> rat := fun i => k`_i * (x`_i).2.
  set F2 : 'I_n-> rat := fun i => k`_i * (x`_0).2.
  have F1eqF2 : (forall i : 'I_n, true -> F1 i = F2 i).
    move=> i true.
    rewrite /F1 /F2.
    move/forallP : tous_meme2.
    move=>tous_meme2.

    move: (tous_meme2 i).
    change (((x`_i).2 == (x`_0).2) ->
      k`_i * (x`_i).2 = k`_i * (x`_0).2).
    set ff := fun x => k`_i * x.
    move/eqP=> hyp1.
    by apply: (congr1 ff).

rewrite /x2 (eq_bigr F2 F1eqF2) /F2 -mulr_suml /lambda -/lambda.
prefield ; field.
have lambda_pos: lambda>0.
    rewrite /lambda.
    move: nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 x1_xn_egal ns1 F2 F1eqF2 fne tous_egaux tous_meme1 tous_meme2 hh1
            .
    case : n.
      by [].
    move=> n nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 x1_xn_egal ns1 F2 F1eqF2 fne tous_egaux tous_meme1 tous_meme2 hh1
            .
    have hypokSn : [forall (i:'I_(S n) | true), Num.lt 0 k`_i].
      move: hypok.
      rewrite -big_andE big_ord_recr !//=.
      move/andP=> hypok.
      move: hypok.
      move=> [hypok1 hypok2].
      move: hypok1.
      rewrite big_andE.
      by [].
    apply (strict_pos_elt_strict_pos_sum hypokSn).
    move: lambda_pos.
    rewrite lt0r.
    move/andP=> lambda_pos.
    move: lambda_pos.
    move=> [lambda_pos1 lambda_pos2].
    apply/eqP.
    by [].  

(* Preuve de x`_n == x`_0 *)
move/andP: x1_xn_egal.
move=> [info1 info2].
move/eqP : info1; move/eqP: info2.
move=> info1 info2.
have infoa : (x`_n).1 = (x`_0).1.
  by rewrite -info2.
have infob : (x`_n).2 = (x`_0).2.
  by rewrite -info1.


(* Dans le bout de code qui suit on montre que ex et xn_meme donne false en 
   hypothèse et donc le but courant est démontré *)
move/existsP:ex.
rewrite !//=.
move=> [x0  ex1].

move/existsP:ex1.
rewrite !//=.
move=> [x3 ex2].

move/andP:tous_meme.
move=> [tous_meme1 tous_meme2].

move/eqP: infoa; move/eqP : infob.
move=> infoa infob.

have tous_meme1_Sn: [forall (i:'I_(n.+1) | true), (x`_i).1 == (x`_0).1].
  rewrite -big_andE big_ord_recr.
  apply/andP.
  split.
    rewrite big_andE.
    exact tous_meme1.
  change ((x`_n).1 == (x`_0).1).
  exact: infob.
have tous_meme2_Sn: [forall (i:'I_(n.+1) | true), (x`_i).2 == (x`_0).2].
  rewrite -big_andE big_ord_recr.
  apply/andP.
  split.
    rewrite big_andE.
    exact tous_meme2.
  change ((x`_n).2 == (x`_0).2).
  exact: infoa.

move/forallP : tous_meme1_Sn.
move=> tous_meme1_Sn.

move/forallP : tous_meme2_Sn.
move=> tous_meme2_Sn.

move : (tous_meme1_Sn x0).
move : (tous_meme2_Sn x0).
change (((x`_x0).2 == (x`_0).2) -> ((x`_x0).1 == (x`_0).1) ->
Num.lt
  (f
     (x1 * lambda + k`_n * (x`_n).1,
     x2 * lambda + k`_n * (x`_n).2))
  (\sum_(i < n) k`_i * f ((x`_i).1, (x`_i).2) +
   k`_n * f ((x`_n).1, (x`_n).2))).
move=>cont1x0 cont2x0.


move : (tous_meme1_Sn x3).
move : (tous_meme2_Sn x3).
change (((x`_x3).2 == (x`_0).2) -> ((x`_x3).1 == (x`_0).1) ->
Num.lt
  (f
     (x1 * lambda + k`_n * (x`_n).1,
     x2 * lambda + k`_n * (x`_n).2))
  (\sum_(i < n) k`_i * f ((x`_i).1, (x`_i).2) +
   k`_n * f ((x`_n).1, (x`_n).2))).
move=>cont1x3 cont2x3.

move/eqP :cont1x0.
move=>cont1x0.

move/eqP :cont2x0.
move=>cont2x0.

move/eqP :cont1x3.
move=>cont1x3.

move/eqP :cont2x3.
move=>cont2x3.

have contra1: ((x`_x0).1 == (x`_x3).1).
  by rewrite cont2x0 cont2x3.

have contra2: ((x`_x0).2 == (x`_x3).2).
  by rewrite cont1x0 cont1x3.

move: ex2.
Search _ (~~_||~~_).
set a1 := (x`_x0).1.
set b1 := (x`_x3).1.
set a2 := (x`_x0).2.
set b2 := (x`_x3).2.
simpl in a1, b1, a2, b2.
set bool1 := (a1 == b1).
set bool2 := (a2 == b2).

move : contra1 contra2.
rewrite -/bool1.
rewrite -/bool2.
move=> contra1.
move=> contra2.
have contra: (bool1 && bool2).
  apply/andP.
  split.
    rewrite /bool1.
    by exact contra1.
  rewrite /bool2.
  by exact: contra2.
rewrite -[~~ bool1 || ~~ bool2]negb_andb.
move:contra.
set bbool := bool1 && bool2.
move=> hyp1 hyp2.
have neg : (bbool && ~~bbool).
  apply/andP.
  split.
    rewrite /bbool contra1 contra2.
    by [].
  by [].
move: neg.
rewrite andb_negb_r.
by [].


(* Reste à démontrer le have tous_meme *)
apply/andP.
split.
  move/forallP : tous_egaux.
  move=> tous_egaux.
  have zero_inf_n : (0 < n)%N.
    by apply : ltn_trans (ltnSn 0)  (ns1).
  move: (tous_egaux (Ordinal zero_inf_n)).
  change ([forall (j : 'I_n|true),
   ((x`_0).1 == (x`_j).1) &&
   ((x`_0).2 == (x`_j).2)] ->
      [forall (i : 'I_n | true), (x`_i).1 == (x`_0).1]).
  move=> tous_egaux_0.
  apply/forallP.
  move=> x0.
  change (((x`_x0).1 == (x`_0).1)).
  move/forallP : tous_egaux_0.
  move=> tous_egaux_0.
  move: (tous_egaux_0 x0).
  change (((x`_0).1 == (x`_x0).1) && ((x`_0).2 == (x`_x0).2) ->
      (x`_x0).1 == (x`_0).1).
  move/andP=> egal0x0.
  move: egal0x0.
  move=> [ egal0x0_1  egal0x0_2].
  move/eqP: egal0x0_1.
  move=>  egal0x0_1.
  apply/eqP.
  rewrite  egal0x0_1.
  reflexivity.


move/forallP : tous_egaux.
move=> tous_egaux.
have zero_inf_n : (0 < n)%N.
  by apply : ltn_trans (ltnSn 0) (ns1).
move: (tous_egaux (Ordinal zero_inf_n)).
change ([forall (j : 'I_n|true),
   ((x`_0).1 == (x`_j).1) &&
   ((x`_0).2 == (x`_j).2)] ->
      [forall (i : 'I_n | true), (x`_i).2 == (x`_0).2]).
move=> tous_egaux0.
apply/forallP.
move=> x0.
change (((x`_x0).2 == (x`_0).2)).
move/forallP : tous_egaux0.
move=> tous_egaux0.
move: (tous_egaux0 x0).
change (((x`_0).1 == (x`_x0).1) && ((x`_0).2 == (x`_x0).2) ->
      (x`_x0).2 == (x`_0).2).
move/andP=> tous_egaux0x0.
move:tous_egaux0x0.
move=> [tous_egaux0x0_1 tous_egaux0x0_2].
move/eqP:tous_egaux0x0_2.
move=> tous_egaux0x0_2.
apply/eqP.
rewrite tous_egaux0x0_2.
reflexivity.



(* Le dernier but à prouver correspond est le suivant et correspond au cas où
   ns1 : (1 < n)%N = false ce qui revient à dire que n = 1 grâce à 
   l'hypothèse nsup1 : (1 < n.+1)%N *)
have n_egal_1 : (1 = n)%N.
  move: nsup1.
  rewrite ltnS.
  move=> nsup1.
  move: ns1.
  rewrite ltnNge.
  move/negP => ninf1.
  move:ninf1.
  move/negP => ninf1.
  move: nsup1.
  rewrite leq_eqVlt.
  move=> nsup1.
  apply: anti_leq.
  rewrite ninf1.
  rewrite andb_true_r.
  rewrite leq_eqVlt.
  by [].


have Sn_egal2 : 2 = n.+1.
  rewrite n_egal_1.
  reflexivity.

move: ex somme_egal_1 hypok.
rewrite -!Sn_egal2.
move=> ex somme_egal_1 hypok.


have info1 : k`_1 = 1 - k`_0.
  move: somme_egal_1.
  rewrite big_ord_recr.
  change ((\sum_(i :'I_1) (k`_i)) + k`_1 = 1 -> k`_1 = 1 - k`_0).
  rewrite big_ord_recr.
  rewrite big_ord0.
  change (0 + k`_0 + k`_1 = 1 -> k`_1 = 1 - k`_0).
  rewrite plus0l.
  move=> tmp.
  rewrite -tmp.
  set a := k`_0.
  set b := k`_1.
  simpl in a, b.
  prefield. ring.


rewrite big_ord_recr.
change (Num.lt
  (f
     (\sum_(i:'I_1) (k`_i* (x`_i).1) + (k`_1 * (x`_1).1),
     \sum_(i < 2) k`_i * (x`_i).2)   )
  (\sum_(i < 2) k`_i * f ((x`_i).1, (x`_i).2))).
rewrite !big_ord_recr !big_ord0.
change (Num.lt
  (f
     (0 + (k`_0 * (x`_0).1) + (k`_1 * (x`_1).1),
     0 + (k`_0 * (x`_0).2) + (k`_1 * (x`_1).2)  )   )
  (0 + k`_0 * f ((x`_0).1, (x`_0).2) + k`_1 * f ((x`_1).1, (x`_1).2))).

rewrite !plus0l.
rewrite info1.

have tmp1 : x`_0 = ((x`_0).1, (x`_0).2).
  apply: surjective_pairing.
have tmp2 : x`_1 = ((x`_1).1, (x`_1).2).
  apply: surjective_pairing.

rewrite -tmp1 -tmp2.

move: hypok.
rewrite -big_andE !big_ord_recr !big_ord0.
change (Num.lt 0 k`_0 && Num.lt 0 k`_1 -> Num.lt
  (f
     (k`_0 * (x`_0).1 + (1 - k`_0) * (x`_1).1,
     k`_0 * (x`_0).2 + (1 - k`_0) * (x`_1).2))
  (k`_0 * f x`_0 + (1 - k`_0) * f x`_1)).
move/andP=> hypok.
move:hypok.
move=> [hypok0 hypok1].


have info2 : k`_0 = 1 - k`_1.
  move: somme_egal_1.
  rewrite big_ord_recr.
  change ((\sum_(i :'I_1) (k`_i)) + k`_1 = 1 -> k`_0 = 1 - k`_1).
  rewrite big_ord_recr big_ord0.
  change (0 + k`_0 + k`_1 = 1 -> k`_0 = 1 - k`_1).
  rewrite plus0l.
  move=> tmp.
  rewrite -tmp.
  set a := k`_0.
  set b := k`_1.
  simpl in a, b.
  prefield. ring.

have info3 : Num.lt k`_0 1.
  rewrite info2.
  change (Num.lt (1 - k`_1) (1-0)).
  apply: ler_lt_sub.
    by [].
  by [].

have ex_utile : ((x`_0).1 != (x`_1).1) || ((x`_0).2 != (x`_1).2); last first.
  apply : f_is_convex.
      by [].
    by [].
  by [].
move/existsP : ex.
move=> [x0 ex].
move :ex.
rewrite andb_true_l.
move=> ex.
move/existsP : ex.
move=> [x1 ex].
move: ex.
rewrite andb_true_l.
move=> ex.

have ineg0 : (0<2)%N.
  by apply: ltn_trans (ltnSn 0) (ltnSn 1).

have ineg1 : (1<2)%N.
  by apply: (ltnSn 1).

case x0x1_dif : (x0 ==x1).
  move/eqP : x0x1_dif.
  move=> x0x1_dif.
  rewrite x0x1_dif in ex.
  move: ex.
  rewrite (_ : (x`_x1).1 == (x`_x1).1 = true); last first.
    apply/eqP.
    by reflexivity.
  rewrite (_ : (x`_x1).2 == (x`_x1).2 = true); last first.
    apply/eqP.
    by reflexivity.
rewrite !//=.

case x0_is0 : (x0 == Ordinal ing0).
  case x1_is1 : (x1 == Ordinal ing1).
    move/eqP : x0_is0.
    move=> x0_is0.
    move/eqP : x1_is1.
    move=> x1_is1.
    change (~~ ((x`_(Ordinal ing0)).1 == (x`_(Ordinal ing1)).1) 
              || ~~ ((x`_(Ordinal ing0)).2 == (x`_(Ordinal ing1)).2)).
    rewrite -x0_is0 -x1_is1.
    by [].
  have contra : (x1 == Ordinal ing0).
    apply/eqP.
    apply (eq_ordinal x1_is1).
  move/eqP : x0_is0.
  move/eqP : contra.
  move=> contra x0_is0.
  rewrite -contra in x0_is0.
  rewrite x0_is0 in ex.
  move: ex.
  rewrite (_ :(x`_x1).1 == (x`_x1).1 = true); last first.
    apply/eqP.
    by reflexivity.
  rewrite (_ :(x`_x1).2 == (x`_x1).2 = true); last first.
    apply/eqP.
    by reflexivity.
  rewrite (_ : ~~ true = false) ;last first.
    by [].
  rewrite orb_false_l.
  by [].
have infoa : x0 == Ordinal ing1.
  apply/eqP.
  apply: (eq_ordinal2 x0_is0).
move/eqP: infoa.
move=> infoa.
rewrite infoa in x0x1_dif.
have infob : (x1 = Ordinal ing0).
  move: x0x1_dif.
  rewrite (_ : (Ordinal ing1 == x1) = (x1 ==Ordinal ing1)).
    apply : (eq_ordinal ).
  by [].
rewrite infoa infob in ex.
move : ex.
change (~~ ((x`_(1)).1 == (x`_(0)).1)
|| ~~ ((x`_(1)).2 == (x`_(0)).2) ->
~~ ((x`_0).1 == (x`_1).1) || ~~ ((x`_0).2 == (x`_1).2)).
rewrite (_ : ((x`_1).1 == (x`_0).1) = ((x`_0).1 == (x`_1).1)); last first.
  by [].
rewrite (_ : ((x`_1).2 == (x`_0).2) = ((x`_0).2 == (x`_1).2)); last first.
  by [].
by [].
Qed.


Definition fJensen:= fun x:rat*rat => x.1 ^+2 + x.2 ^+2.


Lemma sum_gt01 : forall (r1 r2:rat), 
                  Num.lt 0 r1 -> Num.le 0 r2 -> Num.lt 0 (r1+r2).
Proof.
move=> r1 r2 hypr1 hypr2.
rewrite (_: r1+r2 = r1 - (-r2)); last first.
  prefield. field.
rewrite subr_gt0.
move: hypr2.
rewrite le0r.
case info : (r2 == 0).
  rewrite !//=.
  move/eqP:info. move=>info.
  rewrite info.
  by [].
rewrite !//=.
move=> hypr2.
move: hypr2.
rewrite -oppr_lt0.
move=> hypr2.
apply (ltr_trans hypr2 hypr1).
Qed.



Lemma sum_gt02 : forall (r1 r2:rat), 
                  Num.le 0 r1 -> Num.lt 0 r2 -> Num.lt 0 (r1+r2).
Proof.
move=> r1 r2 hypr1 hypr2.
rewrite (_: r1+r2 = r2 - (-r1)); last first.
  prefield. field.
rewrite subr_gt0.
move: hypr1.
rewrite le0r.
case info : (r1 == 0).
  rewrite !//=.
  move/eqP:info. move=>info.
  rewrite info.
  by [].
rewrite !//=.
move=> hypr1.
move: hypr1.
rewrite -oppr_lt0.
move=> hypr1.
apply (ltr_trans hypr1 hypr2).
Qed.




Lemma fJensen_convex : (convex_strict_fun fJensen).
Proof.
rewrite /convex_strict_fun.
move=>k x y H0k Hk1.
move/orP => Hxdify.
move:Hxdify.
move=> [Hxdify1 | Hxdify2].
rewrite /fJensen.
rewrite !expr2 !//=.
rewrite -subr_gt0.
have info_egalite: (k * (x.1 * x.1 + x.2 * x.2) + (1 - k) * (y.1 * y.1 + y.2 * y.2) -
   ((k * x.1 + (1 - k) * y.1) * (k * x.1 + (1 - k) * y.1) +
    (k * x.2 + (1 - k) * y.2) * (k * x.2 + (1 - k) * y.2)))
  = k*(1-k)*((x.1 - y.1)^+2 + (x.2 - y.2)^+2).
  rewrite !expr2 !//=.
  prefield; ring.
rewrite info_egalite.
rewrite pmulr_rgt0; last first.
rewrite pmulr_rgt0.
rewrite subr_gt0.
exact:Hk1.
exact H0k.
apply: sum_gt01.
set a := (x.1 -y.1).
rewrite expr2.
rewrite ltr_def.
apply/andP.
split; last first.
  rewrite -expr2.
  apply: sqr_ge0.
rewrite /a GRing.mulf_neq0.
  by [].
move: Hxdify1.
by rewrite subr_eq0.
move: Hxdify1.
by rewrite subr_eq0.


set b := (x.2 -y.2).
rewrite expr2 -expr2.
apply: sqr_ge0.


(* Cas 2 ou on a ~~ (x.2 == y.2) *)

rewrite /fJensen !expr2 !//= -subr_gt0.
have info_egalite: (k * (x.1 * x.1 + x.2 * x.2) + (1 - k) * (y.1 * y.1 + y.2 * y.2) -
   ((k * x.1 + (1 - k) * y.1) * (k * x.1 + (1 - k) * y.1) +
    (k * x.2 + (1 - k) * y.2) * (k * x.2 + (1 - k) * y.2)))
  = k*(1-k)*((x.1 - y.1)^+2 + (x.2 - y.2)^+2).
  rewrite !expr2 !//=.
  prefield; ring.
rewrite info_egalite.
rewrite pmulr_rgt0; last first.
rewrite pmulr_rgt0.
rewrite subr_gt0.
exact:Hk1.
exact H0k.
apply: sum_gt02.
set a := (x.1 -y.1).
rewrite expr2.
rewrite -expr2.
apply: sqr_ge0.

set b := (x.2 -y.2).
rewrite expr2 ltr_def.
apply/andP.
split; last first.
  rewrite -expr2.
  apply: sqr_ge0.
rewrite /b GRing.mulf_neq0.
  by [].
move: Hxdify2.
by rewrite subr_eq0.
move: Hxdify2.
by rewrite subr_eq0.
Qed.

Lemma lt_implies_le2 (r:rat) : Num.lt 0 r -> Num.le 0 r.
Proof.
rewrite lt0r.
move/andP=> H.
move: H.
move=> [H H2].
by [].
Qed.


Hypothesis triangle_non_degenere :
forall t:T, forall tm:trianglemap, 
let c := point2R1 (tm t (Ordinal un<3)) -
     point2R1 (tm t (Ordinal zero<3)) in
let d := point2R2 (tm t (Ordinal un<3)) -
     point2R2 (tm t (Ordinal zero<3)) in
let e := point2R1 (tm t (Ordinal deux<3)) -
     point2R1 (tm t (Ordinal zero<3)) in
let f := point2R2 (tm t (Ordinal deux<3)) -
     point2R2 (tm t (Ordinal zero<3)) in
let x1 := (0,0) in 
let x2 := (c,d) in
let x3 := (e,f) in 
let x := [:: x1;x2;x3] in
  [exists (i:'I_3|true), [exists (j:'I_3|true),
             ((x`_i).1 != (x`_j).1) 
                    || ((x`_i).2 != (x`_j).2) ]]. 




Lemma oriented_triangles_after_flip (p:point) (t :T) (tm: trianglemap)  
 (toriented  : (leftpoint ((tm t) (Ordinal(zero<3))) ((tm t) (Ordinal(un<3))) 
                  ((tm t) (Ordinal(deux<3))) > 0)) :
   (leftpoint p ((tm t) (Ordinal(zero<3))) ((tm t) (Ordinal(un<3))) 
                   > 0)
&& (leftpoint p ((tm t) (Ordinal(un<3))) ((tm t) (Ordinal(deux<3))) 
                   > 0)
&& (leftpoint p ((tm t) (Ordinal(deux<3))) ((tm t) (Ordinal(zero<3))) 
                  > 0) -> inCircle p t tm ==true.
Proof.
rewrite /inCircle.
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
                                          (tm t
                                            (Ordinal zero<3))
                                       else
                                        if j == 1
                                        then
                                         point2R2
                                           (tm t
                                            (Ordinal zero<3))
                                        else
                                         if nat_of_ord j == 2
                                         then
                                          point2R1
                                            (tm t
                                            (Ordinal zero<3)) ^+ 2 +
                                          point2R2
                                            (tm t
                                            (Ordinal zero<3)) ^+ 2
                                         else 1
                                      else
                                       if i == 1
                                       then
                                        if j == 0
                                        then
                                         point2R1
                                           (tm t
                                            (Ordinal un<3))
                                        else
                                         if j == 1
                                         then
                                          point2R2
                                            (tm t
                                            (Ordinal un<3))
                                         else
                                          if nat_of_ord j == 2
                                          then
                                           point2R1
                                            (tm t
                                            (Ordinal un<3)) ^+ 2 +
                                           point2R2
                                            (tm t
                                            (Ordinal un<3)) ^+ 2
                                          else 1
                                       else
                                        if nat_of_ord i == 2
                                        then
                                         if j == 0
                                         then
                                          point2R1
                                            (tm t
                                            (Ordinal deux<3))
                                         else
                                          if j == 1
                                          then
                                           point2R2
                                            (tm t
                                            (Ordinal deux<3))
                                          else
                                           if nat_of_ord j == 2
                                           then
                                            point2R1
                                            (tm t
                                            (Ordinal deux<3)) ^+ 2 +
                                            point2R2
                                            (tm t
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
                             (tm t
                                (Ordinal zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t
                                 (Ordinal zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t
                                  (Ordinal zero<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal zero<3)) ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (tm t (Ordinal un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t
                                  (Ordinal un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t
                                   (Ordinal un<3)) ^+ 2 +
                              point2R2
                                (tm t
                                   (Ordinal un<3)) ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t
                                  (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t
                                   (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t
                                    (Ordinal deux<3)) ^+ 2 +
                               point2R2
                                 (tm t
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
                - k1* (point2R1(tm t
                                  (Ordinal zero<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal zero<3)) ^+ 2)
                - k2* (point2R1(tm t
                                  (Ordinal un<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal un<3)) ^+ 2)
                - k3* (point2R1(tm t
                                  (Ordinal deux<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal deux<3)) ^+ 2)
                              else 0))).
  rewrite !expand_det44.
  rewrite !mxE. rewrite !//= !expr2 !mul1l !mul0l !mul0r !mul1r !plus0r !sub0r.

  rewrite H1 H2.

  have infok1: k1 = 1 - k2 - k3.
    rewrite -(eqP H3).  simpl in k1. prefield; ring.
  rewrite infok1.
  prefield.
  ring.

rewrite [X in Num.lt 0 X == true]hyp.

rewrite (expand_det_row _ (Ordinal (trois<4))).
rewrite big_ord_recl !mxE !//=.
set cof1 := cofactor
     (\matrix_(i, j) (if i == 0
                      then
                       if j == 0
                       then
                        point2R1
                          (tm t (Ordinal zero<3))
                       else
                        if j == 1
                        then
                         point2R2
                           (tm t (Ordinal zero<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1
                            (tm t (Ordinal zero<3))
                          ^+ 2 +
                          point2R2
                            (tm t (Ordinal zero<3))
                          ^+ 2
                         else 1
                      else
                       if i == 1
                       then
                        if j == 0
                        then
                         point2R1
                           (tm t (Ordinal un<3))
                        else
                         if j == 1
                         then
                          point2R2
                            (tm t (Ordinal un<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1
                             (tm t (Ordinal un<3))
                           ^+ 2 +
                           point2R2
                             (tm t (Ordinal un<3))
                           ^+ 2
                          else 1
                       else
                        if nat_of_ord i == 2
                        then
                         if j == 0
                         then
                          point2R1
                            (tm t (Ordinal deux<3))
                         else
                          if j == 1
                          then
                           point2R2
                             (tm t
                                (Ordinal deux<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1
                              (tm t
                                 (Ordinal deux<3)) ^+ 2 +
                            point2R2
                              (tm t
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
                           then
                            point2R1 p ^+ 2 + point2R2 p ^+ 2 -
                            k1 *
                            (point2R1
                               (tm t
                                  (Ordinal zero<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal zero<3)) ^+ 2) -
                            k2 *
                            (point2R1
                               (tm t
                                  (Ordinal un<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal un<3)) ^+ 2) -
                            k3 *
                            (point2R1
                               (tm t
                                  (Ordinal deux<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal deux<3)) ^+ 2)
                           else 0)) (Ordinal trois<4) ord0.
rewrite big_ord_recl !mxE !//=.
set cof2 := cofactor
     (\matrix_(i, j) (if i == 0
                      then
                       if j == 0
                       then
                        point2R1
                          (tm t (Ordinal zero<3))
                       else
                        if j == 1
                        then
                         point2R2
                           (tm t (Ordinal zero<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1
                            (tm t (Ordinal zero<3))
                          ^+ 2 +
                          point2R2
                            (tm t (Ordinal zero<3))
                          ^+ 2
                         else 1
                      else
                       if i == 1
                       then
                        if j == 0
                        then
                         point2R1
                           (tm t (Ordinal un<3))
                        else
                         if j == 1
                         then
                          point2R2
                            (tm t (Ordinal un<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1
                             (tm t (Ordinal un<3))
                           ^+ 2 +
                           point2R2
                             (tm t (Ordinal un<3))
                           ^+ 2
                          else 1
                       else
                        if nat_of_ord i == 2
                        then
                         if j == 0
                         then
                          point2R1
                            (tm t (Ordinal deux<3))
                         else
                          if j == 1
                          then
                           point2R2
                             (tm t
                                (Ordinal deux<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1
                              (tm t
                                 (Ordinal deux<3)) ^+ 2 +
                            point2R2
                              (tm t
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
                           then
                            point2R1 p ^+ 2 + point2R2 p ^+ 2 -
                            k1 *
                            (point2R1
                               (tm t
                                  (Ordinal zero<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal zero<3)) ^+ 2) -
                            k2 *
                            (point2R1
                               (tm t
                                  (Ordinal un<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal un<3)) ^+ 2) -
                            k3 *
                            (point2R1
                               (tm t
                                  (Ordinal deux<3)) ^+ 2 +
                             point2R2
                               (tm t
                                  (Ordinal deux<3)) ^+ 2)
                           else 0)) (Ordinal trois<4)
                                          (lift ord0 ord0).
rewrite big_ord_recl !mxE !//= /cofactor expand_det33 !mxE !//=.
rewrite big_ord_recl big_ord0 !mxE !//= expand_det33 !mxE !//=. 
move:toriented.
rewrite /leftpoint expand_det33 !mxE !//=.

rewrite  !mulN1r  !addr0  !//= !expr2 !//= !exprD  !expr1 !expr0 !//= !mulr1.
rewrite !//=.
rewrite !mulN1r  !//= !mul1l.

have : k1 = 1 - k2 - k3.
  rewrite -(eqP H3).  simpl in k1. prefield; ring.
move=> hypk1.
rewrite hypk1.

move=> toriented.
apply/eqP.
move:toriented.
set bd := (point2R1 (tm t (Ordinal zero<3)) *
               point2R2 (tm t (Ordinal un<3)) -
               point2R1 (tm t (Ordinal zero<3)) *
               point2R2 (tm t (Ordinal deux<3)) -
               point2R2 (tm t (Ordinal zero<3)) *
               point2R1 (tm t (Ordinal un<3)) +
               point2R2 (tm t (Ordinal zero<3)) *
               point2R1 (tm t (Ordinal deux<3)) +
               point2R1 (tm t (Ordinal un<3)) *
               point2R2 (tm t (Ordinal deux<3)) -
               point2R2 (tm t (Ordinal un<3)) *
               point2R1 (tm t (Ordinal deux<3))).
move=>toriented.
have devpt: (0 * cof1 +
   (0 * cof2 +
    ((point2R1 p * point2R1 p + point2R2 p * point2R2 p -
      (1 - k2 - k3) *
      (point2R1 (tm t (Ordinal zero<3)) *
       point2R1 (tm t (Ordinal zero<3)) +
       point2R2 (tm t (Ordinal zero<3)) *
       point2R2 (tm t (Ordinal zero<3))) -
      k2 *
      (point2R1 (tm t (Ordinal un<3)) *
       point2R1 (tm t (Ordinal un<3)) +
       point2R2 (tm t (Ordinal un<3)) *
       point2R2 (tm t (Ordinal un<3))) -
      k3 *
      (point2R1 (tm t (Ordinal deux<3)) *
       point2R1 (tm t (Ordinal deux<3)) +
       point2R2 (tm t (Ordinal deux<3)) *
       point2R2 (tm t (Ordinal deux<3)))) *
     -
     (point2R1 (tm t (Ordinal zero<3)) *
      point2R2 (tm t (Ordinal un<3)) -
      point2R1 (tm t (Ordinal zero<3)) *
      point2R2 (tm t (Ordinal deux<3)) -
      point2R2 (tm t (Ordinal zero<3)) *
      point2R1 (tm t (Ordinal un<3)) +
      point2R2 (tm t (Ordinal zero<3)) *
      point2R1 (tm t (Ordinal deux<3)) +
      point2R1 (tm t (Ordinal un<3)) *
      point2R2 (tm t (Ordinal deux<3)) -
      point2R2 (tm t (Ordinal un<3)) *
      point2R1 (tm t (Ordinal deux<3))) +
     0 *
     (point2R1 (tm t (Ordinal zero<3)) *
      point2R2 (tm t (Ordinal un<3)) *
      (point2R1 (tm t (Ordinal deux<3)) *
       point2R1 (tm t (Ordinal deux<3)) +
       point2R2 (tm t (Ordinal deux<3)) *
       point2R2 (tm t (Ordinal deux<3))) -
      point2R1 (tm t (Ordinal zero<3)) *
      (point2R1 (tm t (Ordinal un<3)) *
       point2R1 (tm t (Ordinal un<3)) +
       point2R2 (tm t (Ordinal un<3)) *
       point2R2 (tm t (Ordinal un<3))) *
      point2R2 (tm t (Ordinal deux<3)) -
      point2R2 (tm t (Ordinal zero<3)) *
      point2R1 (tm t (Ordinal un<3)) *
      (point2R1 (tm t (Ordinal deux<3)) *
       point2R1 (tm t (Ordinal deux<3)) +
       point2R2 (tm t (Ordinal deux<3)) *
       point2R2 (tm t (Ordinal deux<3))) +
      point2R2 (tm t (Ordinal zero<3)) *
      (point2R1 (tm t (Ordinal un<3)) *
       point2R1 (tm t (Ordinal un<3)) +
       point2R2 (tm t (Ordinal un<3)) *
       point2R2 (tm t (Ordinal un<3))) *
      point2R1 (tm t (Ordinal deux<3)) +
      (point2R1 (tm t (Ordinal zero<3)) *
       point2R1 (tm t (Ordinal zero<3)) +
       point2R2 (tm t (Ordinal zero<3)) *
       point2R2 (tm t (Ordinal zero<3))) *
      point2R1 (tm t (Ordinal un<3)) *
      point2R2 (tm t (Ordinal deux<3)) -
      (point2R1 (tm t (Ordinal zero<3)) *
       point2R1 (tm t (Ordinal zero<3)) +
       point2R2 (tm t (Ordinal zero<3)) *
       point2R2 (tm t (Ordinal zero<3))) *
      point2R2 (tm t (Ordinal un<3)) *
      point2R1 (tm t (Ordinal deux<3))))))
  = (-(    (point2R1 p)^+2 + (point2R2 p)^+2 
        -(1-k2-k3) *  (   (point2R1 (tm t (Ordinal zero<3)))^+2 
                   +     (point2R2 (tm t (Ordinal zero<3)))^+2)
        -k2*(   (point2R1 (tm t (Ordinal un<3)))^+2
                   + (point2R2 (tm t (Ordinal un<3)))^+2  )
        -k3*(   (point2R1 (tm t (Ordinal deux<3)))^+2 
                   + (point2R2 (tm t (Ordinal deux<3)))^+2)  ))
                           * bd.
  rewrite /bd.
  set a := point2R1 (tm t (Ordinal zero<3)).
  set b := point2R2 (tm t (Ordinal zero<3)).
  set c := point2R1 (tm t (Ordinal un<3)).
  set d := point2R2 (tm t (Ordinal un<3)).
  set e := point2R1 (tm t (Ordinal deux<3)).
  set f := point2R2 (tm t (Ordinal deux<3)).
  set g := point2R1 p.
  set h := point2R2 p.
  rewrite !expr2 !//= !mul0l (* !plus0l *) !plus0r.
  prefield.
  ring.
   rewrite devpt.
   rewrite (pmulr_lgt0 (-
   (point2R1 p ^+ 2 + point2R2 p ^+ 2 -
    (1 - k2 - k3) *
    (point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
     point2R2 (tm t (Ordinal zero<3)) ^+ 2) -
    k2 *
    (point2R1 (tm t (Ordinal un<3)) ^+ 2 +
     point2R2 (tm t (Ordinal un<3)) ^+ 2) -
    k3 *
    (point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
     point2R2 (tm t (Ordinal deux<3)) ^+ 2))) toriented).


rewrite ltr_oppr oppr0 H1 H2 !//= hypk1.

(*Ne pas oublier d'utiliser le fait que k1, k2 et k3 >0 *)
have: ((1 - k2 - k3) * point2R1 (tm t (Ordinal zero<3)) +
    k2 * point2R1 (tm t (Ordinal un<3)) +
    k3 * point2R1 (tm t (Ordinal deux<3))) ^+ 2 +
   ((1 - k2 - k3) * point2R2 (tm t (Ordinal zero<3)) +
    k2 * point2R2 (tm t (Ordinal un<3)) +
    k3 * point2R2 (tm t (Ordinal deux<3))) ^+ 2 -
   (1 - k2 - k3) *
   (point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
    point2R2 (tm t (Ordinal zero<3)) ^+ 2) -
   k2 *
   (point2R1 (tm t (Ordinal un<3)) ^+ 2 +
    point2R2 (tm t (Ordinal un<3)) ^+ 2) -
   k3 *
   (point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
    point2R2 (tm t (Ordinal deux<3)) ^+ 2) 

= ( k2 * (point2R1 (tm t (Ordinal un<3))-point2R1 (tm t (Ordinal zero<3))) +
    k3 * (point2R1 (tm t (Ordinal deux<3))-point2R1 (tm t (Ordinal zero<3)))) ^+ 2 +
   (k2 * (point2R2 (tm t (Ordinal un<3))-point2R2 (tm t (Ordinal zero<3))) +
    k3 * (point2R2 (tm t (Ordinal deux<3))-point2R2 (tm t (Ordinal zero<3)))) ^+ 2 
  - k2 *
   ((point2R1 (tm t (Ordinal un<3))-point2R1 (tm t (Ordinal zero<3))) ^+ 2 +
    (point2R2 (tm t (Ordinal un<3))-point2R2 (tm t (Ordinal zero<3))) ^+ 2) -
   k3 *
   ((point2R1 (tm t (Ordinal deux<3))-point2R1 (tm t (Ordinal zero<3))) ^+ 2 +
    (point2R2 (tm t (Ordinal deux<3))-point2R2 (tm t (Ordinal zero<3))) ^+ 2).


  set a := point2R1 (tm t (Ordinal zero<3)).
  set b := point2R2 (tm t (Ordinal zero<3)).
  set c := point2R1 (tm t (Ordinal un<3)).
  set d := point2R2 (tm t (Ordinal un<3)).
  set e := point2R1 (tm t (Ordinal deux<3)).
  set f := point2R2 (tm t (Ordinal deux<3)).
  rewrite !expr2 !//=.
  prefield.
  ring.


move=> egalite_wlog.
rewrite egalite_wlog.
  set c := point2R1 (tm t (Ordinal un<3)) - point2R1 (tm t (Ordinal zero<3)).
  set d := point2R2 (tm t (Ordinal un<3)) - point2R2 (tm t (Ordinal zero<3)).
  set e := point2R1 (tm t (Ordinal deux<3)) - point2R1 (tm t (Ordinal zero<3)).
  set f := point2R2 (tm t (Ordinal deux<3)) - point2R2 (tm t (Ordinal zero<3)).

simpl in c, d, e, f.

have : k2 = 1 - k1 - k3.
  rewrite -(eqP H3).  simpl in k2. prefield; ring.
move=> hypk2.

have : k3 = 1 - k1 - k2.
  rewrite -(eqP H3).  simpl in k3. prefield; ring.
move=> hypk3.

have: k2<1.
rewrite  hypk2 -{2}[1]plus0r !ltr_subl_addr -{1}[1]plus0r -{1}[1]plus0r.
change (Num.lt ((1 + 0) + 0) ((1 + 0) + k3 + k1)).
set z:= 1+0.
rewrite -[z]plus0r.
rewrite (_ : z+0+k3+k1 = z+(0+k3+k1)); last first.
  prefield; ring.
rewrite (ltr_add2l z 0 (0+k3+k1)) plus0l.
apply: Num.Internals.addr_gt0.
apply: H6.
apply: H4.

have: k3<1.
rewrite  hypk3 -{2}[1]plus0r !ltr_subl_addr -{1}[1]plus0r -{1}[1]plus0r.
change (Num.lt ((1 + 0) + 0) ((1 + 0) + k2 + k1)).
set z:= 1+0.
rewrite -[z]plus0r.
rewrite (_ : z+0+k2+k1 = z+(0+k2+k1)); last first.
  prefield; ring.
rewrite (ltr_add2l z 0 (0+k2+k1)) plus0l.
apply: Num.Internals.addr_gt0.
apply: H5.
apply: H4.

have: k1<1.
rewrite  hypk1 -{2}[1]plus0r.
rewrite !ltr_subl_addr -{1}[1]plus0r -{1}[1]plus0r.
change (Num.lt ((1 + 0) + 0) ((1 + 0) + k3 + k2)).
set z:= 1+0.
rewrite -[z]plus0r.
rewrite (_ : z+0+k3+k2 = z+(0+k3+k2)); last first.
  prefield; ring.
rewrite (ltr_add2l z 0 (0+k3+k2)) plus0l.
apply: Num.Internals.addr_gt0.
apply: H6.
apply: H5.

move=> hypk1inf1.
move=> hypk2inf1.
move=> hypk3inf1.

rewrite (_ : ((k2 * c + k3 * e) ^+ 2 + (k2 * d + k3 * f) ^+ 2 -
   k2 * (c ^+ 2 + d ^+ 2) - k3 * (e ^+ 2 + f ^+ 2)) = 
            ((k2 * c + k3 * e) ^+ 2 + (k2 * d + k3 * f) ^+ 2 -
   (k2 * (c ^+ 2 + d ^+ 2) + k3 * (e ^+ 2 + f ^+ 2)))); last first.
  rewrite !expr2 !//=.
  prefield; ring.
rewrite subr_lt0.

set fJensen:= fun x:rat*rat => x.1 ^+2 + x.2 ^+2.
set x1 := (0:rat, 0:rat).
set x2 := (c, d).
set x3:= (e, f).

have :((k2 * c + k3 * e) ^+ 2 + (k2 * d + k3 * f) ^+ 2)
              = (fJensen (k1*x1.1 + k2*x2.1 + k3*x3.1, 
                                k1*x1.2 + k2*x2.2 + k3*x3.2)    ).
  rewrite /fJensen !expr2 !//=.
  prefield; ring.
move=> hypoJensen.
have : (k2 * (c ^+ 2 + d ^+ 2) + k3 * (e ^+ 2 + f ^+ 2) 
          = k1*fJensen x1 + k2*fJensen x2 + k3*fJensen x3).
  rewrite /fJensen !expr2 !//=.
  prefield; ring.
move=>hypo2Jensen.

rewrite hypoJensen hypo2Jensen.


move/eqP:H3.
move=> H3.

(* Transformer les k1+k2+k3 en \sum *)
set x:= [::(x1.1, x1.2) ; (x2.1, x2.2) ; (x3.1, x3.2)].
move:H3.
set k := [::k1;k2;k3].
rewrite (_ : (k1 + k2 + k3 = 1) = (\sum_(i<3) k`_i = 1)); last first.
  rewrite !big_ord_recr !//= big_ord0 plus0l.
  by [].
move=> H3.
rewrite (_ : k1 * x1.1 + k2 * x2.1 + k3 * x3.1 = \sum_(i<3) k`_i *(x`_i).1)
              ; last first.
  rewrite !big_ord_recr !//= big_ord0 !mul0r !plus0l.
  by reflexivity.
rewrite (_ : k1 * x1.2 + k2 * x2.2 + k3 * x3.2 = \sum_(i<3) k`_i *(x`_i).2)
              ; last first.
  rewrite !big_ord_recr !//= big_ord0 !mul0r !plus0l.
  by reflexivity.
rewrite (_ : k1 * fJensen x1 + k2 * fJensen x2 + k3 * fJensen x3
               = \sum_(i<3) k`_i *fJensen (x`_i))
              ; last first.
  rewrite !big_ord_recr !//= big_ord0 !mul0r !plus0l.
  by reflexivity.


have test:  (Num.lt 0 k1 && Num.lt 0 k2 && Num.lt 0 k3) 
                = [forall (i:'I_3|true), (Num.lt 0 k`_((nat_of_ord) i))].
  rewrite -big_andE !big_ord_recr !//= big_ord0 !//=.

have : Num.lt 0 k1 && Num.lt 0 k2 && Num.lt 0 k3.
  by rewrite H4 H5 H6.
rewrite test.


move=> HH.
apply : (@Jensen_inequality_strict 3 _ fJensen_convex _
                (ltn_trans (ltnSn 1) (ltnSn 2)) k  H3  HH).
apply (triangle_non_degenere t tm).
Qed.



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


Lemma not_in_triangle (p:point) (t :T) (tm :trianglemap) :
 (p == tm t (Ordinal zero<3))
     || (p == tm t (Ordinal un<3))
     || (p == tm t (Ordinal deux<3)) = false <-> ~(pt_in_triangle tm p t).
Proof.
split.
set temp1 := (p == tm t (Ordinal zero<3)) || (p == tm t (Ordinal un<3)).
set bool1 := temp1 || (p == tm t (Ordinal deux<3)).
move/negbT=> hyp.
move: hyp.
rewrite /bool1 negb_orb.
move/andP=>hyp.
move:hyp.
move=> [hyp1 hyp3].
move: hyp1.
rewrite /temp1 negb_orb.
move/andP=>hyp1.
move:hyp1.
move=> [hyp1 hyp2].
rewrite /pt_in_triangle.
move/negbTE : hyp1.
move=> hyp1.
rewrite hyp1.
move/negbTE : hyp2.
move=> hyp2.
rewrite hyp2.
move/negbTE : hyp3.
move=> hyp3.
rewrite hyp3 //.

rewrite /pt_in_triangle.
by apply: not_true_is_false.
Qed.



Lemma point2indext1t2_correct tm p t1 t2 :
    pt_in_triangle tm p t1 -> ~(pt_in_triangle tm p t2) ->
                                     tm t1 (point2indext1t2 p t1 t2 tm) = p.
Proof.
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
  rewrite info3 info5 //= orb_false_r.
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
  rewrite info4 info5 //= !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //= !orb_false_r.
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
  rewrite info4 info5 //= !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //= !orb_false_r.
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
  rewrite info4 info5 //= !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //= !orb_false_r.
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
  rewrite info3 info5 //= !orb_false_r.
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
  rewrite info4 info5 //= !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case info7 : (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite info3 info5 //= !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite info3 info4 //=.
by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move=> Ha Hb.
case p_is_zero : (p == tm t1 (Ordinal zero<3)).
  by move/eqP:p_is_zero =>p_is_zero ; rewrite p_is_zero .
case p_is_un : (p == tm t1 (Ordinal un<3)).
  by move/eqP:p_is_un=>p_is_un; rewrite p_is_un.
case p_is_deux : (p == tm t1 (Ordinal deux<3)).
  by move/eqP:p_is_deux=>p_is_deux; rewrite p_is_deux.
case p_is_zero_t2 : (p == tm t2 (Ordinal zero<3)).
  move: Ha.
  rewrite p_is_un p_is_deux //= !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
case p_is_un_t2: (p == tm t2 (Ordinal un<3)).
  move: Ha.
  rewrite p_is_zero p_is_deux //= !orb_false_r.
  by move=>hyp; move/eqP:hyp=>hyp; rewrite hyp.
move: Ha.
rewrite p_is_zero p_is_un //=.
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
  rewrite orb_true_r in Hb.
  tauto.
case info5 : (p == tm t2 (Ordinal zero<3)).
  exact: info.
case info6 : (p == tm t2 (Ordinal un<3)).
  move/eqP:info6=>info6.
  by rewrite info6.
move:Ha.
rewrite info5 info6 //=.
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
move/eqP=> p_is_deuxt2.
by rewrite p_is_deuxt2.
Qed.

Definition inCircle2 (p1 : point) (t1: triangle) : bool :=
  let M:= \matrix_(i<4, j<4) if i ==0 then if j==0 then
                                     point2R1 (t1 (inZp 0))
                                         else if j==1 then
                                     point2R2 (t1 (inZp 0))
                                         else if nat_of_ord j==2 then 
                         (point2R1 (t1 (inZp 0)))^+2
                            + (point2R2 (t1 (inZp 0)))^+2
                                         else 1
                           else if i ==1 then if j==0 then
                                     point2R1 (t1 (inZp 1))
                                         else if j==1 then
                                     point2R2 (t1 (inZp 1))
                                         else if nat_of_ord j==2 then 
                         (point2R1 (t1 (inZp 1)))^+2
                            + (point2R2 (t1 (inZp 1)))^+2
                                         else 1
                           else if nat_of_ord i ==2 then if j==0 then
                                     point2R1 (t1 (inZp 2))
                                         else if j==1 then
                                     point2R2 (t1 (inZp 2))
                                         else if nat_of_ord j==2 then 
                         (point2R1 (t1 (inZp 2)))^+2
                            + (point2R2 (t1 (inZp 2)))^+2
                                         else 1
                           else if j==0 then
                                     point2R1 p1
                                         else if j==1 then
                                     point2R2 p1
                                         else if nat_of_ord j==2 then 
                                     (point2R1 p1)^+2 + (point2R2 p1)^+2 
                                         else 1
   in (\det M >0).

Lemma samedef_inCircle (p1 : point) (t1: triangle) (tm : trianglemap) (t2 :T): 
tm t2 = t1 -> (inCircle p1 t2 tm = inCircle2 p1 t1).
Proof.
move=> hyp.
rewrite /inCircle /inCircle2.
rewrite hyp.
have tmp1: (Ordinal zero<3 == inZp 0).
  by [].
have tmp2: (Ordinal un<3 == inZp 1).
  by [].
have tmp3: (Ordinal deux<3 == inZp 2).
  by [].
move/eqP:tmp1 => tmp1.
move/eqP:tmp2 => tmp2.
move/eqP:tmp3 => tmp3.
rewrite tmp1 tmp2 tmp3.
reflexivity.
Qed.

(* La fonction isDelaunayLocal2 va prendre 2 triangles et va renvoyer un bool
   qui vaudra true si la construction des 2 triangles est de Delauney *)
Definition isDelaunayLocal2 (t1: triangle) (t2: triangle) : bool :=
  (~~(inCircle2 (t1 (Ordinal (zero<3))) t2)
      && (~~inCircle2 (t1 (Ordinal (un<3))) t2)
      && (~~inCircle2 (t1 (Ordinal (deux<3))) t2)).

Lemma samedef_isDelaunayLocal (t1: triangle) (t2 :triangle) 
                                  (tm: trianglemap) (t3 : T) (t4: T): 
tm t3 = t1 -> tm t4 = t2 -> (isDelaunayLocal t3 t4 tm = isDelaunayLocal2 t1 t2).
Proof.
move=> hyp1 hyp2.
rewrite /isDelaunayLocal /isDelaunayLocal2.
rewrite /triangle2points.
rewrite !ffunE.
rewrite hyp1.
rewrite (@samedef_inCircle (t1 (Ordinal zero<3)) t2 tm t4).
  rewrite (@samedef_inCircle (t1 (Ordinal un<3)) t2 tm t4).
    rewrite (@samedef_inCircle (t1 (Ordinal deux<3)) t2 tm t4).
      by [].
    by [].
  by [].
by [].
Qed.


Lemma delaunay_post_flip (tm: trianglemap)  (ptext1 : point) (ptext2 : point)
                           (t1:T) (t2 :T) (g:graph) (pm: pointmap)  : 
  isDelaunayLocal t1 t2 tm == false
  -> pt_in_triangle tm ptext2 t2 /\ ~pt_in_triangle tm ptext2 t1
  -> pt_in_triangle tm ptext1 t1 /\ ~pt_in_triangle tm ptext1 t2
  -> if flip default_triangle (tm: trianglemap) (ptext1 : point) 
                                  (ptext2 : point) (t1:T) (t2 :T) (g:graph)
                                     (pm: pointmap) is Some (g',tm') then

       let ptext1 := (tm t1 (Ordinal(zero<3))) in
       let q1 := (tm t1 (Ordinal(un<3))) in
       let p1 := (tm t1 (Ordinal(deux<3))) in
       let ptext2 := (tm t2 (Ordinal(zero<3))) in
       let p2 := (tm t2 (Ordinal(un<3))) in
       let q2 :=(tm t2 (Ordinal(deux<3))) in
       let new_tr1 := (fun x : 'I_3 =>
           if x == 0
           then
            ptext1
           else
            if x == 1
            then
              ptext2
            else p1) in
        let new_tr2 := (fun x : 'I_3 =>
              if x == 0
              then ptext2
              else
               if x == 1
               then ptext1
               else q2) in
  p1 = p2
  -> q1 = q2
  -> ~pt_in_triangle tm ptext2 t1
  -> ~pt_in_triangle tm ptext1 t2
          -> isDelaunayLocal2 new_tr1 new_tr2
     else true.
Proof.
move=> illegal infop1 infop2.
move:infop1.
move=> [info1p1 info2p1].
move: infop2.
move=>[info1p2 info2p2].

case cas : (flip default_triangle tm ptext1 ptext2 t1 t2 g pm)=> [[g' tmap' ] | ]
      ; last first.
  by [].
move=> pt1 q1 p1 pt2 p2 q2 new_tr1 new_tr2 adj1 adj2 notint1 notint2.
rewrite /isDelaunayLocal2.
apply/andP.
split.
  apply/andP.
  split.
    rewrite (_ : new_tr1 (@Ordinal 3 0 zero<3) = pt1); last first.
      by [].
    rewrite /inCircle2.
    have det_eq_0 : (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (new_tr2 (@inZp 2 0))
                          else
                           if j == 1
                           then
                            point2R2
                              (new_tr2 (@inZp 2 0))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (new_tr2 (@inZp 2 0))
                             ^+ 2 +
                             point2R2
                               (new_tr2 (@inZp 2 0))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (new_tr2 (@inZp 2 1))
                           else
                            if j == 1
                            then
                             point2R2
                               (new_tr2 (@inZp 2 1))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (new_tr2 (@inZp 2 1))
                              ^+ 2 +
                              point2R2
                                (new_tr2 (@inZp 2 1))
                              ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (new_tr2 (@inZp 2 2))
                            else
                             if j == 1
                             then
                              point2R2
                                (new_tr2 (@inZp 2 2))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (new_tr2 (@inZp 2 2))
                               ^+ 2 +
                               point2R2
                                 (new_tr2 (@inZp 2 2))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then point2R1 pt1
                            else
                             if j == 1
                             then point2R2 pt1
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1 pt1 ^+ 2 +
                               point2R2 pt1 ^+ 2
                              else 1))) = 0.
      rewrite expand_det44 !mxE !//=.
      rewrite !expr2 !mul1r.
      rewrite !mul1l.
      set a := point2R1 (new_tr2 (@inZp 2 0)).
      set b:= point2R2 (new_tr2 (@inZp 2 0)).
      set c := point2R1 (new_tr2 (@inZp 2 1)).
      set d:= point2R2 (new_tr2 (@inZp 2 1)).
      set e := point2R1 (new_tr2 (@inZp 2 2)).
      set f:= point2R2 (new_tr2 (@inZp 2 2)).
      prefield. ring.
    rewrite lt0r.
    rewrite negb_andb.
    rewrite negb_involutive.
    move/eqP:det_eq_0 => det_eq_0.
    rewrite det_eq_0.
    rewrite orb_true_l.
    by [].
  rewrite (_ : new_tr1 (@Ordinal 3 1 un<3) = pt2); last first.
    by [].
  rewrite /inCircle2.
  have det_eq_0 : (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (new_tr2 (@inZp 2 0))
                          else
                           if j == 1
                           then
                            point2R2
                              (new_tr2 (@inZp 2 0))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (new_tr2 (@inZp 2 0))
                             ^+ 2 +
                             point2R2
                               (new_tr2 (@inZp 2 0))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (new_tr2 (@inZp 2 1))
                           else
                            if j == 1
                            then
                             point2R2
                               (new_tr2 (@inZp 2 1))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (new_tr2 (@inZp 2 1))
                              ^+ 2 +
                              point2R2
                                (new_tr2 (@inZp 2 1))
                              ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (new_tr2 (@inZp 2 2))
                            else
                             if j == 1
                             then
                              point2R2
                                (new_tr2 (@inZp 2 2))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (new_tr2 (@inZp 2 2))
                               ^+ 2 +
                               point2R2
                                 (new_tr2 (@inZp 2 2))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then point2R1 pt2
                            else
                             if j == 1
                             then point2R2 pt2
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1 pt2 ^+ 2 +
                               point2R2 pt2 ^+ 2
                              else 1))) = 0.
    rewrite expand_det44 !mxE !//=.
    rewrite !expr2 !mul1r.
    rewrite !mul1l.
    set a := point2R1 (new_tr2 (@inZp 2 0)).
    set b:= point2R2 (new_tr2 (@inZp 2 0)).
    set c := point2R1 (new_tr2 (@inZp 2 1)).
    set d:= point2R2 (new_tr2 (@inZp 2 1)).
    set e := point2R1 (new_tr2 (@inZp 2 2)).
    set f:= point2R2 (new_tr2 (@inZp 2 2)).
    prefield. ring.
  rewrite lt0r.
  rewrite negb_andb.
  rewrite negb_involutive.
  move/eqP:det_eq_0 => det_eq_0.
  rewrite det_eq_0.
  rewrite orb_true_l.
  by [].
rewrite (_ : new_tr1 (@Ordinal 3 2 deux<3) = p1); last first.
  by [].
move:illegal.
rewrite /isDelaunayLocal.
rewrite (_ : (@triangle2points P t1 tm) (@Ordinal 3 0 zero<3) = pt1); last first.
  rewrite /triangle2points ffunE.
  by [].
rewrite (_ : (@triangle2points P t1 tm) (@Ordinal 3 1 un<3) = q1); last first.
  rewrite /triangle2points ffunE.
  by [].
rewrite (_ : (@triangle2points P t1 tm) (@Ordinal 3 2 deux<3) = p1); last first.
  rewrite /triangle2points ffunE.
  by [].
have q1_notin_t2 : ~~ @inCircle P q1 t2 tm.
  rewrite /inCircle.
  rewrite adj2.
  have det_eq_0 :  (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2
                                (@Ordinal 3 0 zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2
                                 (@Ordinal 3 0 zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (tm t2 (@Ordinal 3 1 un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2
                                  (@Ordinal 3 1 un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2 +
                              point2R2
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 2 deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2
                                   (@Ordinal 3 2 deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then point2R1 q2
                            else
                             if j == 1
                             then point2R2 q2
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1 q2 ^+ 2 +
                               point2R2 q2 ^+ 2
                              else 1))) = 0.
    rewrite expand_det44 !mxE !//=.
    rewrite !expr2 !mul1r.
    rewrite !mul1l.
    set a := point2R1 (new_tr2 (@inZp 2 0)).
    set b:= point2R2 (new_tr2 (@inZp 2 0)).
    set c := point2R1 (tm t2 (@Ordinal 3 1 un<3)).
    set d:= point2R2 (tm t2 (@Ordinal 3 1 un<3)).
    set e := point2R1 (new_tr2 (@inZp 2 2)).
    set f:= point2R2 (new_tr2 (@inZp 2 2)).
    set h1:= point2R1 q2.
    set h2:= point2R2 q2.
    prefield. ring.
  rewrite lt0r.
  rewrite negb_andb.
  rewrite negb_involutive.
  move/eqP:det_eq_0 => det_eq_0.
  rewrite det_eq_0.
  rewrite orb_true_l.
  by [].
rewrite q1_notin_t2.
have p1_notin_t2 : ~~ @inCircle P p1 t2 tm.
  rewrite /inCircle.
  rewrite adj1.
  have det_eq_0 :  (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2
                                (@Ordinal 3 0 zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2
                                 (@Ordinal 3 0 zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (tm t2 (@Ordinal 3 1 un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2
                                  (@Ordinal 3 1 un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2 +
                              point2R2
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 2 deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2
                                   (@Ordinal 3 2 deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then point2R1 p2
                            else
                             if j == 1
                             then point2R2 p2
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1 p2 ^+ 2 +
                               point2R2 p2 ^+ 2
                              else 1))) = 0.
    rewrite expand_det44 !mxE !//=.
    rewrite !expr2 !mul1r.
    rewrite !mul1l.
    set a := point2R1 (new_tr2 (@inZp 2 0)).
    set b:= point2R2 (new_tr2 (@inZp 2 0)).
    set c := point2R1 (tm t2 (@Ordinal 3 1 un<3)).
    set d:= point2R2 (tm t2 (@Ordinal 3 1 un<3)).
    set e := point2R1 (new_tr2 (@inZp 2 2)).
    set f:= point2R2 (new_tr2 (@inZp 2 2)).
    set h1:= point2R1 p2.
    set h2:= point2R2 p2.
    prefield. ring.
  rewrite lt0r.
  rewrite negb_andb.
  rewrite negb_involutive.
  move/eqP:det_eq_0 => det_eq_0.
  rewrite det_eq_0.
  rewrite orb_true_l.
  by [].
rewrite p1_notin_t2.
rewrite !andb_true_r.
move/eqP=> inCirc.
apply negb_false_iff in inCirc.
move: inCirc.
rewrite /inCircle /inCircle2.
rewrite adj1.
have opp :   (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (new_tr2 (@inZp 2 0))
                          else
                           if j == 1
                           then
                            point2R2
                              (new_tr2 (@inZp 2 0))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (new_tr2 (@inZp 2 0))
                             ^+ 2 +
                             point2R2
                               (new_tr2 (@inZp 2 0))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (new_tr2 (@inZp 2 1))
                           else
                            if j == 1
                            then
                             point2R2
                               (new_tr2 (@inZp 2 1))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (new_tr2 (@inZp 2 1))
                              ^+ 2 +
                              point2R2
                                (new_tr2 (@inZp 2 1))
                              ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (new_tr2 (@inZp 2 2))
                            else
                             if j == 1
                             then
                              point2R2
                                (new_tr2 (@inZp 2 2))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (new_tr2 (@inZp 2 2))
                               ^+ 2 +
                               point2R2
                                 (new_tr2 (@inZp 2 2))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then point2R1 p2
                            else
                             if j == 1
                             then point2R2 p2
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1 p2 ^+ 2 +
                               point2R2 p2 ^+ 2
                              else 1))) 
            = - (
                      (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2
                                (@Ordinal 3 0 zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2
                                 (@Ordinal 3 0 zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (tm t2 (@Ordinal 3 1 un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2
                                  (@Ordinal 3 1 un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2 +
                              point2R2
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 2 deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2
                                   (@Ordinal 3 2 deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then point2R1 pt1
                            else
                             if j == 1
                             then point2R2 pt1
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1 pt1 ^+ 2 +
                               point2R2 pt1 ^+ 2
                              else 1)))).
  rewrite expand_det44 !mxE !//=.
  rewrite !expr2 !mul1r.
  rewrite !mul1l.
  rewrite expand_det44 !mxE !//=.
  rewrite !mul1r !mul1l.
  set a := point2R1 (new_tr2 (@inZp 2 0)).
  set b:= point2R2 (new_tr2 (@inZp 2 0)).
  set c := point2R1 (tm t2 (@Ordinal 3 1 un<3)).
  set d:= point2R2 (tm t2 (@Ordinal 3 1 un<3)).
  set e := point2R1 (new_tr2 (@inZp 2 2)).
  set f:= point2R2 (new_tr2 (@inZp 2 2)).
  set h1:= point2R1 (new_tr2 (@inZp 2 1)).
  set h2:= point2R2 (new_tr2 (@inZp 2 1)).
  set i1 := point2R1 p1.
  set i2 := point2R2 p1.
  prefield; ring.
rewrite opp.
set det := \det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2
                                (@Ordinal 3 0 zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2
                                 (@Ordinal 3 0 zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2
                                  (@Ordinal 3 0 zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1
                              (tm t2 (@Ordinal 3 1 un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2
                                  (@Ordinal 3 1 un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2 +
                              point2R2
                                (tm t2
                                   (@Ordinal 3 1 un<3))
                              ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2
                                  (@Ordinal 3 2 deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2
                                   (@Ordinal 3 2 deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2
                                    (@Ordinal 3 2 deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then point2R1 pt1
                            else
                             if j == 1
                             then point2R2 pt1
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1 pt1 ^+ 2 +
                               point2R2 pt1 ^+ 2
                              else 1)).
simpl in det.
move => det_gt0.
rewrite lt0r negb_andb negb_involutive -ltrNge.
rewrite -oppr_lt0 in det_gt0.
rewrite det_gt0.
rewrite orb_true_r.
by [].
Qed.


(*===================================
                  PROOF OF  ccw_exchange
===================================*)


Definition ccwd (xp yp xq yq xr yr : rat) :=
  xp * yq - xq * yp - xp * yr + xr * yp + xq * yr - xr * yq.

Definition ccwr (xp yp xq yq xr yr : rat) := ccwd xp yp xq yq xr yr > 0.

Lemma axiom1' : forall xp yp xq yq xr yr,
  ccwd xp yp xq yq xr yr = ccwd xq yq xr yr xp yp.
move=> xp yp xq yq xr yr.
rewrite /ccwd.
rat_field.
Qed.

Lemma axiom1 : forall xp yp xq yq xr yr,
  ccwr xp yp xq yq xr yr -> ccwr xq yq xr yr xp yp.
rewrite /ccwr.
move=> xp yp xq yq xr yr H.
rewrite axiom1' in H.
by [].
Qed.

Lemma axiom5 :
  forall xp yp xq yq xr yr xs ys xt yt,
  ccwr xq yq xp yp xr yr -> ccwr xq yq xp yp xs ys -> 
  ccwr xq yq xp yp xt yt -> ccwr xq yq xr yr xs ys ->
  ccwr xq yq xs ys xt yt -> ccwr xq yq xr yr xt yt.
rewrite /ccwr.
move=> xp yp xq yq xr yr xs ys xt yt pqr pqs pqt prs pst.
(* This is taken from Bertot & Pichardie 2001. *)
have : (ccwd xq yq xr yr xt yt = 
        (ccwd xq yq xs ys xt yt * ccwd xq yq xp yp xr yr + 
        ccwd xq yq xr yr xs ys * ccwd xq yq xp yp xt yt)
        /ccwd xq yq xp yp xs ys ).
  rewrite /ccwd.  move: pqs. rewrite /ccwd. rewrite lt0r.
  move/andP => info.
  move: info.
  move=> [info1 info2].
  move:info1.
  move/eqP=>info1.
  by rat_field.
move=>H.
rewrite H.
apply: divr_gt0.
  apply: addr_gt0.
    apply: mulr_gt0.
      by [].
    by [].
  apply: mulr_gt0.
    by [].
  by [].
by [].
Qed.

Lemma eq_not_ccwr :
  forall xp yp xq yq xr yr, xp = xq -> yp = yq -> ~ccwr xp yp xq yq xr yr.
move=> xp yp xq yq xr yr q1 q2.
rewrite q1 q2 /ccwr /ccwd.
have info : (xq * yq - xq * yq - xq * yr + xr * yq + xq * yr -
   xr * yq) = 0.
  set a := xq * yq.
  set b := xq * yr.
  set c := xq * yr.
  set d := xr * yq.
  simpl in a, b, c, d.
  prefield. ring.
rewrite info.
by [].
Qed.

Definition in_circled (xp yp xq yq xr yr xs ys : rat) :=
  xp *
       (yq * ((xr * xr + yr * yr) * 1 - 1 * (xs * xs + ys * ys)) -
        yr * ((xq * xq + yq * yq) * 1 - 1 * (xs * xs + ys * ys)) +
        ys * ((xq * xq + yq * yq) * 1 - 1 * (xr * xr + yr * yr))) -
       xq *
       (yp * ((xr * xr + yr * yr) * 1 - 1 * (xs * xs + ys * ys)) -
        yr * ((xp * xp + yp * yp) * 1 - 1 * (xs * xs + ys * ys)) +
        ys * ((xp * xp + yp * yp) * 1 - 1 * (xr * xr + yr * yr))) +
       xr *
       (yp * ((xq * xq + yq * yq) * 1 - 1 * (xs * xs + ys * ys)) -
        yq * ((xp * xp + yp * yp) * 1 - 1 * (xs * xs + ys * ys)) +
        ys * ((xp * xp + yp * yp) * 1 - 1 * (xq * xq + yq * yq))) -
       xs *
       (yp * ((xq * xq + yq * yq) * 1 - 1 * (xr * xr + yr * yr)) -
        yq * ((xp * xp + yp * yp) * 1 - 1 * (xr * xr + yr * yr)) +
        yr * ((xp * xp + yp * yp) * 1 - 1 * (xq * xq + yq * yq))).

Lemma ccwd_translation :
  forall a b xp yp xq yq xr yr,
  ccwd (xp + a) (yp + b) (xq + a) (yq + b) (xr + a) (yr + b) =
  ccwd xp yp xq yq xr yr.
move=> a b xp yp xq yq xr yr.
rewrite /ccwd.
rat_field.
Qed.

Definition distance_sq (xp yp xq yq:rat) :=
  (xp - xq)*(xp - xq) + (yp - yq)*(yp - yq).


Definition implicit_to_center_and_radius :
  forall (a b c x y :rat),  x*x + y*y + a*x +b*y + c =
  distance_sq x y (-a/(1+1)) (-b/(1+1)) 
                            + (c - ((a*a + b * b)/(1+1+1+1))).
move=> a b c x y.
rewrite /distance_sq.
prefield. field.
split.
  rewrite //.
change (2%:R <> 0%Q).
by [].
Qed.

Lemma translation_distance :
  forall (a b xp yp xq yq : rat),
    distance_sq (xp - a) (yp - b) (xq - a) (yq - b) =
    distance_sq xp yp xq yq.
move=> a b xp yp xq yq.
rewrite /distance_sq.
rat_field.
Qed.

Definition in_circle (xp yp xq yq xr yr xs ys : rat) :=
  in_circled xp yp xq yq xr yr xs ys > 0.

Lemma in_circled_polynomial :
  forall xp yp xq yq xr yr x y,
    in_circled xp yp xq yq xr yr x y =
    (- ccwd xp yp xq yq xr yr * (x * x + y * y) -
       ccwd yp (xp^+2 + yp^+2) yq (xq^+2 + yq^+2) yr (xr^+2 + yr^+2) * x +
       ccwd xp (xp^+2 + yp^+2) xq (xq^+2 + yq^+2) xr (xr^+2 + yr^+2) * y +
       ((xr^+2 + yr^+2) * yq * xp + xq * yr * (xp^+2 + yp^+2) +
        xr * yp * (xq^+2 + yq^+2) - xp * yr * (xq^+2 + yq^+2) -
        xq * yp * (xr^+2 + yr^+2) - xr * yq * (xp^+2 + yp^+2))).
move=> xp yp xq yq xr yr x y.
rewrite /in_circled /ccwd.
rewrite !expr2 !mul1r !mul1l.
rat_field.
Qed.

Lemma in_circled_distance :
  forall (xp yp xq yq xr yr: rat),
    ccwd xp yp xq yq xr yr > 0 ->
    exists a, exists b, exists r,
    forall x y,
    in_circled xp yp xq yq xr yr x y =
    - ccwd xp yp xq yq xr yr * ((distance_sq x y a b) - r).
Proof.
move=> xp yp xq yq xr yr cc.
have ccn : (ccwd xp yp xq yq xr yr <> 0).
  move=> H; rewrite H in cc.
  by [].
(* The formulas here are proposed by Coq in dummy proofs, where
  one first proposes 0 as value and use field_simplify
  to see what comes up.*)
exists (-(ccwd yp (xp^+2 + yp^+2) yq (xq^+2 + yq^+2) yr (xr^+2 + yr^+2)
         / ((1+1) * ccwd xp yp xq yq xr yr))).
exists (ccwd xp (xp^+2 + yp^+2) xq (xq^+2 + yq^+2) xr (xr^+2 + yr^+2)
         / ((1+1) * ccwd xp yp xq yq xr yr)).
exists(((1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * (xr ^+2) * yq * xp -
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * xr ^+2 * xq * yp +
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * xr * yq ^+2 * yp -
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * xr * yq * xp ^+2 -
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * xr * yq * yp ^+2 +
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * xr * xq ^+2 * yp +
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * yr ^+2 * yq * xp -
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * yr ^+2 * xq * yp -
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * yr * yq ^+2 * xp +
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * yr * xp ^+2 * xq -
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * yr * xp * xq ^+2 +
    (1+1+1+1) * ccwd xp yp xq yq xr yr ^+2 * yr * xq * yp ^+2 +
    ccwd xp yp xq yq xr yr *
    ccwd yp (xp ^+2 + yp ^+2) yq (xq ^+2 + yq ^+2) yr (xr ^+2 + yr ^+2) ^+2 +
    ccwd xp yp xq yq xr yr *
    ccwd xp (xp ^+2 + yp ^+2) xq (xq ^+2 + yq ^+2) xr (xr ^+2 + yr ^+2) ^+2) /
   ((1+1+1+1) * ccwd xp yp xq yq xr yr ^+3)).
move=> x y; rewrite in_circled_polynomial.
rewrite /distance_sq.
rewrite !exprSr !expr0.
rewrite !mul1l.
rewrite /ccwd.
prefield. field.
split.
  move: cc.
  rewrite lt0r.
  move/andP=> cc.
  move:cc.
  move=> [cc1 cc2].
  move/eqP: cc1.
  rewrite /ccwd.
  by [].
by rewrite //.
Qed.

Lemma distance_0_eq :
  forall x y x' y', distance_sq x y x' y' = 0 -> x = x' /\ y = y'.
move=> x y x' y'. rewrite /distance_sq; split.
Search _ (_ \/ _ \/ _).
About Num.RealMixin.le_total.
set a := (x - x') * (x - x').
set b := (y - y') * (y - y').
simpl in a,b.
set k := [::a;b].
move:H.
rewrite (_ : (x - x') * (x - x') + (y - y') * (y - y') = \sum_(i<2) k`_i)
        ; last first.
  rewrite big_ord_recr.
  change ((x - x') * (x - x') + (y - y') * (y - y') = \sum_(i<1) k`_i + k`_1).
  rewrite big_ord_recr big_ord0.
  change ((x - x') * (x - x') + (y - y') * (y - y') = 0 + k`_0 + k`_1).
  rewrite plus0l.
  rewrite /k.
  by rewrite //.
have elt1pos : Num.le 0 k`_0.
  rewrite /k.
  rewrite !//=.
  rewrite /a.
  set a1 := (x - x').
  rewrite -expr2.
  Search _ (Num.le 0 (_^+_)).
  apply: exprn_even_ge0.
  by [].
have elt2pos : Num.le 0 k`_1.
  rewrite /k.
  rewrite !//=.
  rewrite /b.
  set b1 := (y - y').
  rewrite -expr2.
  Search _ (Num.le 0 (_^+_)).
  apply: exprn_even_ge0.
  by [].
have pos : [forall (i:'I_2 | true), Num.le 0 k`_i] = true.
  rewrite -big_andE.
  rewrite big_ord_recr.
  change ((\big[andb_monoid/true]_(i < 1) Num.le 0 k`_i && (Num.le 0 k`_1)) = true).
  rewrite big_ord_recr big_ord0.
  change ( (Num.le 0 k`_0) && (Num.le 0 k`_1) = true).
  apply/andP.
  by [].
move/eqP=>tmp.
move:tmp.
rewrite (sum_eq0 pos).
move/forallP=>tmp2.
move : (tmp2 ord0).
change ((k`_0 == 0%Q) -> x = x').
rewrite /k !//= /a.
rewrite mulf_eq0.
rewrite orb_diag.
move/eqP=>tmp3.
apply subr0_eq.
by [].
set a := (x - x') * (x - x').
set b := (y - y') * (y - y').
simpl in a,b.
set k := [::a;b].
move:H.
rewrite (_ : (x - x') * (x - x') + (y - y') * (y - y') = \sum_(i<2) k`_i)
        ; last first.
  rewrite big_ord_recr.
  change ((x - x') * (x - x') + (y - y') * (y - y') = \sum_(i<1) k`_i + k`_1).
  rewrite big_ord_recr big_ord0.
  change ((x - x') * (x - x') + (y - y') * (y - y') = 0 + k`_0 + k`_1).
  rewrite plus0l.
  rewrite /k.
  by rewrite //.
have elt1pos : Num.le 0 k`_0.
  rewrite /k.
  rewrite !//=.
  rewrite /a.
  set a1 := (x - x').
  rewrite -expr2.
  Search _ (Num.le 0 (_^+_)).
  apply: exprn_even_ge0.
  by [].
have elt2pos : Num.le 0 k`_1.
  rewrite /k.
  rewrite !//=.
  rewrite /b.
  set b1 := (y - y').
  rewrite -expr2.
  Search _ (Num.le 0 (_^+_)).
  apply: exprn_even_ge0.
  by [].
have pos : [forall (i:'I_2 | true), Num.le 0 k`_i] = true.
  rewrite -big_andE.
  rewrite big_ord_recr.
  change ((\big[andb_monoid/true]_(i < 1) Num.le 0 k`_i && (Num.le 0 k`_1)) = true).
  rewrite big_ord_recr big_ord0.
  change ( (Num.le 0 k`_0) && (Num.le 0 k`_1) = true).
  apply/andP.
  by [].
move/eqP=>tmp.
move:tmp.
rewrite (sum_eq0 pos).
move/forallP=>tmp2.
move : (tmp2 (inZp 1)).
change ((k`_1 == 0%Q) -> y = y').
rewrite /k !//= /b.
rewrite mulf_eq0.
rewrite orb_diag.
move/eqP=>tmp3.
apply subr0_eq.
by [].
Qed.


Lemma distance_sq_pos :
  forall x y x' y', distance_sq x y x' y' >= 0.
move=> x y x' y'; rewrite /distance_sq.
have pos1 : Num.le 0 ((x - x') * (x - x')).
  rewrite -expr2.
  Search _ (Num.le 0 (_^+_)).
  apply: exprn_even_ge0.
  by [].
have pos2 : Num.le 0 ((y - y') * (y - y')).
  rewrite -expr2.
  Search _ (Num.le 0 (_^+_)).
  apply: exprn_even_ge0.
  by [].
set a := (x - x') * (x - x').
set b := (y - y') * (y - y').
simpl in a,b.
set k := [::a;b].
rewrite (_ : (x - x') * (x - x') + (y - y') * (y - y') = \sum_(i < 2) k`_i).
  apply pos_elt_pos_sum.
  rewrite -big_andE.
  rewrite big_ord_recr.
  change ((\big[andb_monoid/true]_(i < 1) Num.le 0 k`_i && (Num.le 0 k`_1)) = true).
  rewrite big_ord_recr big_ord0.
  change ( (Num.le 0 k`_0) && (Num.le 0 k`_1) = true).
  apply/andP.
  by [].
rewrite big_ord_recr.
change ((x - x') * (x - x') + (y - y') * (y - y') = \sum_(i<1) k`_i + k`_1).
rewrite big_ord_recr big_ord0.
change ((x - x') * (x - x') + (y - y') * (y - y') = 0 + k`_0 + k`_1).
rewrite plus0l.
rewrite /k.
by rewrite //.
Qed.

Lemma in_circled1 :
  forall xp yp xq yq xr yr, in_circled xp yp xq yq xr yr xp yp = 0.
move=> xp yp xq yq xr yr; rewrite /in_circled.
prefield. ring.
Qed.

Lemma in_circled2 :
  forall xp yp xq yq xr yr, in_circled xp yp xq yq xr yr xq yq = 0.
move=> xp yp xq yq xr yr; rewrite /in_circled.
prefield. ring.
Qed.

Lemma in_circled3 :
  forall xp yp xq yq xr yr, in_circled xp yp xq yq xr yr xr yr = 0.
move=> xp yp xq yq xr yr; rewrite /in_circled.
prefield. ring.
Qed.

Lemma ccw_circle_positive_radius :
  forall xp yp xq yq xr yr a b r,
    ccwd xp yp xq yq xr yr > 0 ->
    (forall x y, in_circled xp yp xq yq xr yr x y =
    - ccwd xp yp xq yq xr yr * ((distance_sq x y a b) - r)) ->
    r > 0.
move=> xp yp xq yq xr yr a b r q d.
have vp := (in_circled1 xp yp xq yq xr yr).
rewrite d in vp.
have vdp := (distance_sq_pos xp yp a b).
have info : (r >= 0).
  move : vp.
  set p1 := - ccwd xp yp xq yq xr yr.
  set p2 := (distance_sq xp yp a b - r).
  move=> vp.
  simpl in p1, p2.
  move/eqP: vp.
  rewrite GRing.mulf_eq0.
  move:q.
  rewrite /p1 lt0r oppr_eq0.
  move/andP=> q.
  move:q.
  move=> [q1 q2].
  move/negbTE:q1.
  move=> q1.
  rewrite q1 orb_false_l /p2.
  rewrite subr_eq0.
  move/eqP=>info2.
  rewrite -info2.
  by [].

move:info.
rewrite le0r.
move=> info.
case nul_ou_spos : ((r == 0)); last first.
  rewrite nul_ou_spos in info.
  rewrite orb_false_l in info.
  by [].
have pa : (distance_sq xp yp a b = 0).
  move/eqP: vp.
  rewrite GRing.mulf_eq0.
  move:q.
  set p1 := - ccwd xp yp xq yq xr yr.
  set p2 := (distance_sq xp yp a b - r).
  rewrite /p1 lt0r.
  rewrite oppr_eq0.
  move/andP=> q.
  move:q.
  move=> [q1 q2].
  move/negbTE:q1.
  move=> q1.
  rewrite q1 orb_false_l.
  rewrite /p2.
  move/eqP => fin.
  apply/eqP.
  move/eqP : nul_ou_spos.
  move=> nul_ou_spos.
  rewrite nul_ou_spos in fin.
  move : fin.
  rewrite subr0.
  move/eqP => t.
  by [].
have vq := (in_circled2 xp yp xq yq xr yr).
rewrite d in vq.
have qa : (distance_sq xq yq a b = 0).
  set p1 := - ccwd xp yp xq yq xr yr.
  set p2 := (distance_sq xq yq a b - r).
  move/eqP:vq.
  rewrite -/p1 -/p2.
  simpl in p1, p2.
  rewrite GRing.mulf_eq0.
  move:q.
  rewrite /p1 lt0r.
  rewrite oppr_eq0.
  move/andP=> q.
  move:q.
  move=> [q1 q2].
  move/negbTE:q1.
  move=> q1.
  rewrite q1 orb_false_l /p2.
  move/eqP : nul_ou_spos.
  move=> nul_ou_spos.
  rewrite nul_ou_spos.
  rewrite subr0.
  move/eqP => t.
  by [].
move : (distance_0_eq pa).
move : (distance_0_eq  qa).
move=> [info1a info1b] [info2a info2b].
have xpq :  (xp = xq).
  by rewrite info1a info2a.
have ypq :(yp = yq).
  by rewrite info1b info2b.
move : (@eq_not_ccwr xp yp xq yq xr yr xpq ypq).
move=> tmp.
case tmp.
rewrite /ccwr.
by [].
Qed.

Lemma in_circle_ccwr :
  forall x y a b, 0 < a^+2 + b^+2 ->
    distance_sq x y a b <= (a^+2 + b^+2) -> (x = 0 -> y <> 0) ->
    ccwr 0 0 b (-a) x y.
Proof.
rewrite /ccwr.
rewrite /ccwd.
rewrite /distance_sq.
move=> x y a b rp inc diff.
rewrite !mul0l !mul0r.
rewrite !subr0 plus0l.
rewrite !expr2 in inc.
rewrite (_ : (b * y - x * - a) = (b * y + (- x * - a))); last first.
  prefield; ring.
rewrite mulrNN.
case nul_ou_non : ((x == 0)).
  move/eqP : nul_ou_non.
  move=> nul_ou_non.
  rewrite nul_ou_non mul0l.
  rewrite subr0.
  move: (diff nul_ou_non).
  rewrite nul_ou_non in inc.
  rewrite !sub0r in inc.
  move : inc.
  rewrite mulrNN.
  set tmp := a*a.
  move=> hypo.
  simpl in tmp.
  move=>hypo2.
  rewrite ler_add2l in hypo.
  have info : ~~ (b ==0).
    apply/negP.
    rewrite /not.
    move/eqP=> contra.
    rewrite contra in hypo.
    move: hypo.
    rewrite //= mul0r subr0.
    rewrite -expr2.
    rewrite real_exprn_even_le0.
        move/andP=> hyp.
        move:hyp.
        move=> [hyp1 hyp2].
        move/eqP:hyp2 => hyp2.
        move : hyp2 hypo2.
        by [].
      apply : Num.Internals.num_real.
    by [].
  rewrite lt0r.
  apply/andP; split.
    apply:mulf_neq0.
      by [].
    by move/eqP:hypo2.
  




Admitted.
(* intros x0; rewrite x0 in inc |- *. 
assert (diff' := diff x0); psatz R.
intros; psatz R. 
Qed.*)

Lemma exists_tangent :
  forall xp yp xq yq xr yr, ccwr xp yp xq yq xr yr ->
   exists xt, exists yt,  ccwr xp yp xt yt xq yq /\ ccwr xp yp xt yt xr yr /\
      forall xs ys, in_circle xp yp xq yq xr yr xs ys -> ccwr xp yp xt yt xs ys.
Proof.
move=> xp yp xq yq xr yr cc.
rewrite /ccwr in cc.
case : (in_circled_distance cc) => [a [b [r H]]].
exists (xp + b - yp); exists (yp + xp - a).
have qa : (distance_sq xq yq a b = r).
have ciq := (in_circled2 xp yp xq yq xr yr).
rewrite H in ciq. rewrite /ccwr in cc. apply: subr0_eq. rewrite lt0r in cc.
  move/andP:cc => [cc1 cc2].
  rewrite -oppr_eq0 in cc1.
  move/eqP: ciq => ciq.
  rewrite mulf_eq0 in ciq.
  move/negbTE: cc1 => cc1.
  rewrite cc1 in ciq.
  rewrite orb_false_l in ciq.
  by move/eqP:ciq=>ciq.
have ra : (distance_sq xr yr a b = r).
have cir := (in_circled3 xp yp xq yq xr yr).
rewrite H in cir; rewrite /ccwr in cc. apply: subr0_eq. rewrite lt0r in cc.
  move/andP:cc => [cc1 cc2].
  rewrite -oppr_eq0 in cc1.
  move/eqP: cir => cir.
  rewrite mulf_eq0 in cir.
  move/negbTE: cc1 => cc1.
  rewrite cc1 in cir.
  rewrite orb_false_l in cir.
  by move/eqP:cir=>cir.
have info : (xq - xp = 0 -> yq - yp <> 0).
  move=> H1 H2; have H1' : (xp = xq). apply: subr0_eq. move/eqP:H1.
    rewrite -oppr_eq0.
    move/eqP=>H1. move:H1. rewrite (_ : - (xq - xp) = xp - xq); last first.
      rat_field.
    by [].
  have H2' : (yp = yq). apply: subr0_eq. move/eqP:H2.
    rewrite -oppr_eq0.
    move/eqP=>H2. move:H2. rewrite (_ : - (yq - yp) = yp - yq); last first.
      rat_field.
    by [].
case :(@eq_not_ccwr xp yp xq yq xr yr H1' H2'). by [].
have :  (xr - xp = 0 -> yr - yp <> 0).
  move=> H1 H2; have H1' : (xr = xp). apply: subr0_eq. by [].
  have H2' : (yr = yp) by apply: subr0_eq.
case :(@eq_not_ccwr xr yr xp yp xq yq H1' H2').
apply axiom1; apply axiom1; by [].
have pa : (distance_sq xp yp a b = r).
have cip := (in_circled1 xp yp xq yq xr yr).
rewrite H in cip; rewrite /ccwr in cc.  apply: subr0_eq. rewrite lt0r in cc.
  move/andP:cc => [cc1 cc2].
  rewrite -oppr_eq0 in cc1.
  move/eqP: cip => cip.
  rewrite mulf_eq0 in cip.
  move/negbTE: cc1 => cc1.
  rewrite cc1 in cip.
  rewrite orb_false_l in cip.
  by move/eqP:cip=>cip.
rewrite /ccwr; rewrite <- (ccwd_translation (-xp) (-yp) _ _ _ _ xq yq).
rewrite <- (ccwd_translation (-xp) (-yp) _ _ _ _ xr yr).
rewrite (_ : (xp - xp) = 0); last first.
  apply/eqP.
  rewrite subr_eq0.
  apply/eqP.
  by [].
rewrite (_ : (yp - yp) = 0); last first.
  apply/eqP.
  rewrite subr_eq0.
  apply/eqP.
  by [].
rewrite (_ : (xp + b - yp + - xp) = (b - yp)); last first.
  by rat_field.
rewrite (_ : (yp + xp - a + - yp) = (-(a - xp))); last first.
  by rat_field.
have rp := (@ccw_circle_positive_radius xp yp xq yq xr yr a b r cc H).
have d' : (0 < (a-xp)^+2 + (b-yp)^+2).
  rewrite (_ : ((a - xp) ^+ 2 + (b - yp) ^+ 2) = (distance_sq xp yp a b))
      ; last first.
    rewrite /distance_sq.
    rewrite !expr2.
    by rat_field.
  rewrite pa. 
  by [].
rewrite /distance_sq.
split.
  apply in_circle_ccwr.
      by [].
    rewrite -/(xq - xp); rewrite -/(yq - yp); rewrite translation_distance.
    have dq : ((distance_sq xq yq a b) = ((a - xp) ^+ 2 + (b - yp) ^+ 2)).
      rewrite qa. rewrite <- pa. rewrite /distance_sq. rewrite !expr2.
      by rat_field.
    rewrite dq.
    by [].
  by [].
split.
  apply in_circle_ccwr.
      by [].
    rewrite -/(xr - xp); rewrite-/(yr - yp); rewrite translation_distance.
    have dq : ((distance_sq xr yr a b) = ((a - xp) ^+ 2 + (b - yp) ^+ 2)).
      rewrite ra. rewrite <- pa; rewrite /distance_sq. rewrite !expr2. 
      by rat_field.
    rewrite dq.
     by [].
  by [].
move=> xs ys inc.
rewrite <- (ccwd_translation (-xp) (-yp) _ _ _ _ xs ys).
rewrite (_ : (xp - xp) = 0); last first.
  apply/eqP.
  rewrite subr_eq0.
  apply/eqP.
  by [].
rewrite (_ : (yp - yp) = 0); last first.
  apply/eqP.
  rewrite subr_eq0.
  apply/eqP.
  by [].
rewrite (_ : (xp + b - yp + - xp) = (b - yp)); last first.
  by rat_field.
rewrite (_ : (yp + xp - a + - yp) = (-(a - xp))); last first.
  by rat_field.
apply in_circle_ccwr.
    by [].
  rewrite /in_circle in inc; rewrite H in inc.
  have sa : (distance_sq xs ys a b < r).
    rewrite /ccwr in cc. rewrite -oppr_lt0 in cc.
    rewrite (nmulr_rgt0 (distance_sq xs ys a b - r) cc) in inc.
    rewrite -subr_lt0.
    by [].
  rewrite -/(xs - xp); rewrite-/(ys - yp); rewrite translation_distance.
  have dd : (distance_sq xp yp a b = ((a - xp) ^+ 2 + (b - yp) ^+ 2)).
    rewrite /distance_sq. rewrite !expr2. by rat_field.
  rewrite -dd. rewrite pa.
  rewrite ltr_def in sa. move/andP : sa => [sa1 sa2]. by [].
move=> Hx Hy; have Hx' : (xs = xp). apply/eqP. rewrite -subr_eq0. 
  by apply/eqP.
have Hy' : (ys = yp).  apply/eqP. rewrite -subr_eq0. 
  by apply/eqP.
rewrite Hx' Hy' in inc; rewrite /in_circle in inc; rewrite in_circled1 in inc.
move: inc.
by rewrite ltrr.
Admitted.
(* Admitted car Qed trop long *)

Lemma exchange :
forall xp yp xq yq xr yr xs ys,  ccwr xp yp xq yq xr yr ->
  ccwr xp yp xr yr xs ys ->
  in_circle xp yp xq yq xr yr xs ys ->
  ccwr xp yp xq yq xs ys /\ ccwr xq yq xr yr xs ys.
Proof.
move=> xp yp xq yq xr yr xs ys cc1 cc2 ic.
split.
case info1: (exists_tangent cc1) =>
  [xt [yt [ptq [ptr pta]]]].
apply axiom5 with xt yt xr yr. try by []. by [].
apply pta. by []. by []. by [].
apply axiom1 in cc2.
case : (exists_tangent cc2) =>
  [xt [yt [rts [rtp rta]]]].
apply axiom1; apply axiom1.
apply axiom5 with xt yt xp yp; try by [].
apply rta.
rewrite /in_circle. rewrite (_ :
  (in_circled xr yr xs ys xp yp xq yq) =
  (in_circled xp yp xq yq xr yr xs ys)).
move: ic.
rewrite /in_circled /in_circle /in_circled. by [].
rewrite !/in_circled. by rat_field.
apply axiom1; apply axiom1; by [].
Admitted.
(* Admitted car Qed trop long *)

(*========END OF YB'PROOF========*)

(*===========BRIDGE============ *)

Definition inCircle_point (p q r s : point) : bool :=
  let M:= \matrix_(i<4, j<4) if i ==0 then if j==0 then
                                     point2R1 p
                                         else if j==1 then
                                     point2R2 p
                                         else if nat_of_ord j==2 then 
                         (point2R1 p)^+2
                            + (point2R2 p)^+2
                                         else 1
                           else if i ==1 then if j==0 then
                                     point2R1 q
                                         else if j==1 then
                                     point2R2 q
                                         else if nat_of_ord j==2 then 
                         (point2R1 q)^+2
                            + (point2R2 q)^+2
                                         else 1
                           else if nat_of_ord i ==2 then if j==0 then
                                     point2R1 r
                                         else if j==1 then
                                     point2R2 r
                                         else if nat_of_ord j==2 then 
                         (point2R1 r)^+2
                            + (point2R2 r)^+2
                                         else 1
                           else if j==0 then
                                     point2R1 s
                                         else if j==1 then
                                     point2R2 s
                                         else if nat_of_ord j==2 then 
                                     (point2R1 s)^+2 + (point2R2 s)^+2 
                                         else 1
   in (\det M >0).

Lemma lien1 : forall (p q r: point), ccwd (point2R1 p) (point2R2 p)
                                         (point2R1 q) (point2R2 q)
                                        (point2R1 r) (point2R2 r) 
                                            = leftpoint p q r.
Proof.
move=> p q r.
rewrite /ccwd.
rewrite /leftpoint expand_det33 !mxE !//=.
rewrite !mul1l !mul1r.
rat_field.
Qed.


Lemma lien2 : forall (p q r: point), ccwr (point2R1 p) (point2R2 p)
                                         (point2R1 q) (point2R2 q)
                                        (point2R1 r) (point2R2 r) 
                                               = (leftpoint p q r > 0).
Proof.
move=> p q r.
rewrite /ccwr lien1.
by [].
Qed.


Lemma lien3 : forall (p q r s: point), in_circle (point2R1 p) (point2R2 p)
                                         (point2R1 q) (point2R2 q)
                                        (point2R1 r) (point2R2 r) 
                                       (point2R1 s) (point2R2 s) 
                                            = inCircle_point p q r s.
Proof.
move=> p q r s.
rewrite /in_circle /in_circled !mul1l !mul1r.
rewrite /inCircle_point.
rewrite expand_det44 !mxE !//=.
rewrite !mul1l.
rewrite !expr2 !mul1r.
rewrite (_:  (point2R1 p *
   (point2R2 q *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r -
     (point2R1 s * point2R1 s + point2R2 s * point2R2 s)) -
    point2R2 r *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q -
     (point2R1 s * point2R1 s + point2R2 s * point2R2 s)) +
    point2R2 s *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q -
     (point2R1 r * point2R1 r + point2R2 r * point2R2 r))) -
   point2R1 q *
   (point2R2 p *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r -
     (point2R1 s * point2R1 s + point2R2 s * point2R2 s)) -
    point2R2 r *
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p -
     (point2R1 s * point2R1 s + point2R2 s * point2R2 s)) +
    point2R2 s *
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p -
     (point2R1 r * point2R1 r + point2R2 r * point2R2 r))) +
   point2R1 r *
   (point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q -
     (point2R1 s * point2R1 s + point2R2 s * point2R2 s)) -
    point2R2 q *
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p -
     (point2R1 s * point2R1 s + point2R2 s * point2R2 s)) +
    point2R2 s *
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p -
     (point2R1 q * point2R1 q + point2R2 q * point2R2 q))) -
   point2R1 s *
   (point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q -
     (point2R1 r * point2R1 r + point2R2 r * point2R2 r)) -
    point2R2 q *
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p -
     (point2R1 r * point2R1 r + point2R2 r * point2R2 r)) +
    point2R2 r *
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p -
     (point2R1 q * point2R1 q + point2R2 q * point2R2 q))))


    =  (point2R1 p *
   (point2R2 q *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    point2R2 q *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 r +
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 s +
    point2R2 r *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) *
    point2R2 s) -
   point2R1 q *
   (point2R2 p *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    point2R2 p *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 r +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 s +
    point2R2 r *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) *
    point2R2 s) +
   point2R1 r *
   (point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    point2R2 p *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 q +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 s +
    point2R2 q *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 s) -
   point2R1 s *
   (point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    point2R2 p *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 q +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 r +
    point2R2 q *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 r))).
  by [].
prefield. ring.
Qed.

Axiom ccw_axiom_1 : forall (p q r : point),
  leftpoint p q r > 0 -> leftpoint q r p > 0.

Lemma ccw_exchange_bis: forall (p q r s: point),
  leftpoint p q r > 0 -> leftpoint p r s > 0 -> inCircle_point p q r s ->
      ((leftpoint p q s > 0) /\ (leftpoint q r s > 0)).
Proof.
move=> p q r s.
rewrite -!lien2. 
rewrite -lien3.
set xp := point2R1 p.
set yp := point2R2 p.
set xq := point2R1 q.
set yq := point2R2 q.
set xr := point2R1 r.
set yr := point2R2 r.
set xs := point2R1 s.
set ys := point2R2 s.
move=> pqr prs pqrs.
move:  (exchange pqr prs pqrs).
by [].
Qed.


(* IMPORTANT: *)

Theorem ccw_exchange: forall (p q r s: point),
  leftpoint p q r > 0 -> leftpoint q p s > 0 -> inCircle_point p q r s ->
      ((leftpoint r s q > 0) /\ (leftpoint s r p > 0)).
Proof. 
move=> p q r s.
rewrite -!lien2.
set xp := point2R1 p.
set yp := point2R2 p.
set xq := point2R1 q.
set yq := point2R2 q.
set xr := point2R1 r.
set yr := point2R2 r.
set xs := point2R1 s.
set ys := point2R2 s.
move=> pqr.
rewrite {1}/ccwr.
rewrite axiom1'.
rewrite (_ : Num.lt 0 (ccwd xp yp xs ys xq yq) = ccwr xp yp xs ys xq yq)
    ; last first.
  by rewrite /ccwr.
move=> psq.
rewrite (_ : inCircle_point p q r s = inCircle_point p s q r); last first.
rewrite /inCircle_point.

rewrite expand_det44 !mxE !//=.
rewrite expand_det44 !mxE !//=.
rewrite !mul1l.
rewrite !expr2 !mul1r.

    set tmp :=  (point2R1 p *
   (point2R2 q *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    point2R2 q *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 r +
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 s +
    point2R2 r *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) *
    point2R2 s) -
   point2R1 q *
   (point2R2 p *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    point2R2 p *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 r +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 s +
    point2R2 r *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) *
    point2R2 s) +
   point2R1 r *
   (point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    point2R2 p *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 q +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 s +
    point2R2 q *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 s) -
   point2R1 s *
   (point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    point2R2 p *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 q +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 r +
    point2R2 q *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 r)).
    


    set tmp2 := (point2R1 p *
   (point2R2 s *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    point2R2 s *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) *
    point2R2 q +
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) *
    point2R2 r +
    point2R2 q *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 r) -
   point2R1 s *
   (point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    point2R2 p *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 q +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 r +
    point2R2 q *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) *
    point2R2 r) +
   point2R1 q *
   (point2R2 p *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    point2R2 p *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 s +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 r +
    point2R2 s *
    (point2R1 r * point2R1 r + point2R2 r * point2R2 r) -
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) *
    point2R2 r) -
   point2R1 r *
   (point2R2 p *
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) -
    point2R2 p *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 s +
    (point2R1 p * point2R1 p + point2R2 p * point2R2 p) *
    point2R2 q +
    point2R2 s *
    (point2R1 q * point2R1 q + point2R2 q * point2R2 q) -
    (point2R1 s * point2R1 s + point2R2 s * point2R2 s) *
    point2R2 q)).
  rewrite (_ : tmp = tmp2); last first.
    rewrite /tmp /tmp2.
    prefield; ring.
  by [].
move=> psqr.
move: pqr psq psqr.
rewrite /xp /yp /xq /yq /xr /yr /xs /ys.
rewrite (_: ccwr (point2R1 p) (point2R2 p) (point2R1 q) 
  (point2R2 q) (point2R1 r) (point2R2 r) = (leftpoint p q r > 0)); last first.
  by rewrite lien2.
rewrite (_: ccwr (point2R1 p) (point2R2 p) (point2R1 s) 
  (point2R2 s) (point2R1 q) (point2R2 q) = (leftpoint p s q > 0)); last first.
  by rewrite lien2.
move=> pqr psq psqr.
move: (ccw_exchange_bis psq pqr psqr). 
move=> [hypo1 hypo2].
split.
rewrite (_: ccwr (point2R1 r) (point2R2 r) (point2R1 s) 
  (point2R2 s) (point2R1 q) (point2R2 q) = (leftpoint r s q > 0)); last first.
  by rewrite lien2.
move: (ccw_axiom_1 hypo2). move=> hypo3.
move: (ccw_axiom_1 hypo3). by [].
rewrite (_: ccwr (point2R1 s) (point2R2 s) (point2R1 r) 
  (point2R2 r) (point2R1 p) (point2R2 p) = (leftpoint s r p > 0)); last first.
  by rewrite lien2.
move: (ccw_axiom_1 hypo1). by [].
Qed.

(*===========END BRIDGE=====================*)


(* Il faut écrire un lemme qui montre que findIllegal renvoie bien ptext1 et
   ptext2 tel que pt_in_triangle tm ptext2 t2 /\ ~pt_in_triangle tm ptext2 t1
   et pt_in_triangle tm ptext1 t1 /\ ~pt_in_triangle tm ptext1 t2 et que
    p1 = p2 et q1 = q2 *)


Lemma orientedpostflip (tm: trianglemap)  (ptext1 : point) (ptext2 : point)
                           (t1:T) (t2 :T) (g:graph) (pm: pointmap) :
let ptext1 := (tm t1 (Ordinal(zero<3))) in
let q1 := (tm t1 (Ordinal(un<3))) in
let p1 := (tm t1 (Ordinal(deux<3))) in
let ptext2 := (tm t2 (Ordinal(zero<3))) in
let p2 := (tm t2 (Ordinal(un<3))) in
let q2 :=(tm t2 (Ordinal(deux<3))) in
(forall t:T, oriented t tm) -> isDelaunayLocal t1 t2 tm == false 
  -> p1 = p2
  -> q1 = q2
  -> ~pt_in_triangle tm ptext2 t1
  -> ~pt_in_triangle tm ptext1 t2
  -> if flip default_triangle (tm: trianglemap) (ptext1 : point) 
                                  (ptext2 : point) (t1:T) (t2 :T) (g:graph)
                                     (pm: pointmap) is Some (g',tm') then
        forall tt:T, oriented tt tm'
     else (oriented t1 tm) && (oriented t2 tm).
Proof.
move=> pt1 q1 p1 pt2 p2 q2 univ_o illegal adj1 adj2 notint1 notint2.

have [ot1 ot2] : oriented t1 tm /\ oriented t2 tm by split; apply univ_o.
case info : (flip default_triangle tm pt1 pt2 t1 t2 g pm) => [[g' tmap'] | ];
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
set new_tr1 := (fun x : 'I_3 =>
           if x == 0
           then
            if
             (pt1 == tm t1 (Ordinal zero<3))
             || (pt1 == tm t1 (Ordinal un<3))
             || (pt1 == tm t1 (Ordinal deux<3))
            then tm t1 (point2indext1t2 pt1 t1 t2 tm)
            else tm t2 (point2indext1t2 pt1 t1 t2 tm)
           else
            if x == 1
            then
             if
              (pt2 == tm t1 (Ordinal zero<3))
              || (pt2 == tm t1 (Ordinal un<3))
              || (pt2 == tm t1 (Ordinal deux<3))
             then tm t1 (point2indext1t2 pt2 t1 t2 tm)
             else tm t2 (point2indext1t2 pt2 t1 t2 tm)
            else
             if
              (pt1 == tm t1 (Ordinal zero<3))
              || (pt1 == tm t1 (Ordinal un<3))
              || (pt1 == tm t1 (Ordinal deux<3))
             then
              tm t1
                (addOrd3 (point2indext1t2 pt1 t1 t2 tm)
                   (Ordinal deux<3))
             else
              tm t2
                (addOrd3 (point2indext1t2 pt1 t1 t2 tm)
                   (Ordinal deux<3))).
set new_tr2 := (fun x : 'I_3 =>
              if x == 0
              then
               if
                (pt2 == tm t2 (Ordinal (ltn0Sn 2)))
                || (pt2 == tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
                || (pt2 == tm t2 (Ordinal (ltnSn 2)))
               then tm t2 (point2indext1t2 pt2 t1 t2 tm)
               else tm t1 (point2indext1t2 pt2 t1 t2 tm)
              else
               if x == 1
               then
                if
                 (pt1 == tm t2 (Ordinal (ltn0Sn 2)))
                 || (pt1 ==
                     tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
                 || (pt1 == tm t2 (Ordinal (ltnSn 2)))
                then tm t2 (point2indext1t2 pt1 t1 t2 tm)
                else tm t1 (point2indext1t2 pt1 t1 t2 tm)
               else
                if
                 (pt2 == tm t2 (Ordinal (ltn0Sn 2)))
                 || (pt2 ==
                     tm t2 (Ordinal (ltn_trans (ltnSn 1) (ltnSn 2))))
                 || (pt2 == tm t2 (Ordinal (ltnSn 2)))
                then
                 tm t2
                   (addOrd3 (point2indext1t2 pt2 t1 t2 tm)
                      (Ordinal (ltnSn 2)))
                else
                 tm t1
                   (addOrd3 (point2indext1t2 pt2 t1 t2 tm)
                      (Ordinal (ltnSn 2)))).

have oriented_tm2 : forall t : T, oriented t tm2.
  move: (orientedunhookT g t1 univ_o).
  rewrite info1.
  by [].

have oriented_tm3 : forall t : T, oriented t tm3.
  move: (orientedunhookT g2 t2 oriented_tm2).
  rewrite info2.
  by [].

have otr1 : leftpoint (new_tr1 (inZp 0))(new_tr1 (inZp 1))(new_tr1 (inZp 2)) > 0
    ; last first.
  have oriented_vtemp : forall t : T, oriented t vtemp.
    move: (orientedattachT pm oriented_tm3 otr1).
    case intel1 : (attachT new_tr1 tm3 pm) => [a | ].
      move : intel1.
      move: info3.
      rewrite /temp.
      rewrite -/new_tr1.
      move=> tempo1.
      rewrite tempo1.
      move=> tempo2.
      have some_eq : vtemp = a.
        move: tempo2.
        by case.
      by rewrite some_eq.
    move: intel1 info3.
    rewrite /temp -/new_tr1.
    move=> tempo1.
    rewrite tempo1.
    by discriminate.

have otr2 : leftpoint (new_tr2 (inZp 0))(new_tr2 (inZp 1))(new_tr2 (inZp 2)) > 0
    ; last first.
  have oriented_vtemp2 : forall t : T, oriented t vtemp2.
    move: (orientedattachT pm oriented_vtemp otr2).
    case intel1 : (attachT new_tr2 vtemp pm) => [a | ].
      move : intel1.
      move: info4.
      rewrite /temp2 -/new_tr2.
      move=> tempo1.
      rewrite tempo1.
      move=> tempo2.
      have some_eq : vtemp2 = a.
        move: tempo2.
        by case.
      by rewrite some_eq.
    move: intel1 info4.
    rewrite /temp2 -/new_tr2.
    move=> tempo1.
    rewrite tempo1.
    by discriminate.

by rewrite -vtemp2istmap'.

move : (@ccw_exchange p2 q2 pt2 pt1).
rewrite (_ : (new_tr2 (inZp 0)) = pt2); last first.
  rewrite /new_tr2.
  rewrite /pt2.
  rewrite !//=.
  rewrite (_ : tm t2 (Ordinal zero<3) == tm t2 (Ordinal zero<3) = true)
          ; last first.
    apply/eqP.
    by [].
  change ( tm t2 (point2indext1t2 (tm t2 (Ordinal zero<3)) t1 t2 tm) 
          = tm t2 (Ordinal zero<3)).
  rewrite point2indext2t1_correct.
  by [].
  rewrite /pt_in_triangle.
  rewrite (_ : tm t2 (Ordinal zero<3) == tm t2 (Ordinal zero<3) = true)
          ; last first.
    apply/eqP.
    by [].
  by [].
  by [].


(*  faire de même que le paragraphe précédent pour faire apparaitre dans le but
    les points p2 q2 pt2 etc ... *)
rewrite (_ : (new_tr2 (inZp 1)) = pt1); last first.
  rewrite /new_tr2.
  rewrite !//=.
  move: notint2. rewrite /pt_in_triangle. rewrite not_true_iff_false.
  move=> notint2.
  rewrite notint2.
  rewrite /pt1.
  rewrite point2indext1t2_correct.
  by [].
  rewrite /pt_in_triangle.
  rewrite (_ : tm t1 (Ordinal zero<3) == tm t1 (Ordinal zero<3) = true)
          ; last first.
    apply/eqP.
    by [].
  by [].
  apply not_true_iff_false in notint2.
  move:notint2.
  change (~ pt_in_triangle tm pt1 t2 ->
~ pt_in_triangle tm (tm t1 (Ordinal zero<3)) t2).
  by [].


rewrite (_ : (new_tr2 (inZp 2)) = q2); last first.
  rewrite /new_tr2.
  rewrite !//=.
  rewrite (_ : tm t2 (Ordinal zero<3) == tm t2 (Ordinal zero<3) = true)
        ; last first.
    apply/eqP.
    by [].
  change (tm t2
    (addOrd3 (point2indext1t2 pt2 t1 t2 tm)
       (Ordinal deux<3)) = q2).
  rewrite /point2indext1t2.
  rewrite /pt2.
  rewrite (_ : tm t2 (Ordinal zero<3) == tm t2 (Ordinal zero<3) = true)
        ; last first.
    apply/eqP.
    by [].
  move: notint1. rewrite /pt_in_triangle. rewrite not_true_iff_false.
  set b1 := ((pt2 == tm t1 (Ordinal zero<3))
                || (pt2 == tm t1 (Ordinal un<3))).
  set b2 := (pt2 == tm t1 (Ordinal deux<3)).
  Search _ ((_||_) = false).
  move=> notint1.
  apply orb_false_iff in notint1.
  move: notint1.
  move=> [notint11 notint12].
  apply orb_false_iff in notint11.
  move:notint11.
  move=> [notint111 notint112].
  rewrite notint111 notint112 notint12.
  rewrite (_ : (addOrd3 (Ordinal zero<3) (Ordinal deux<3)) 
                 = (Ordinal deux<3)); last first.
    rewrite /addOrd3.
    apply val_inj.
    by rewrite //.
  by [].


have infoLem1 : Num.lt 0 (leftpoint p2 q2 pt2).
  rewrite /p2 /q2 /pt2.
  apply ccw_axiom_1.
  rewrite ( _ : Num.lt 0
  (leftpoint (tm t2 (Ordinal zero<3))
     (tm t2 (Ordinal un<3)) (tm t2 (Ordinal deux<3))) = oriented t2 tm)
        ; last first.
    rewrite /oriented.
    rewrite (_ : (Ordinal zero<3) = inZp 0); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal un<3) = inZp 1); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal deux<3) = inZp 2); last first.
      apply: val_inj.
      by rewrite //.
  by [].
by [].


have infoLem2 : Num.lt 0 (leftpoint q2 p2 pt1).
  rewrite -adj1.
  rewrite -adj2.
  rewrite /q1 /p1 /pt1.
  apply ccw_axiom_1.
  rewrite ( _ : Num.lt 0
  (leftpoint (tm t1 (Ordinal zero<3))
     (tm t1 (Ordinal un<3)) (tm t1 (Ordinal deux<3))) = oriented t1 tm)
        ; last first.
    rewrite /oriented.
    rewrite (_ : (Ordinal zero<3) = inZp 0); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal un<3) = inZp 1); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal deux<3) = inZp 2); last first.
      apply: val_inj.
      by rewrite //.
  by [].
by [].


have infoLem3 : inCircle_point p2 q2 pt2 pt1.
  move/eqP: illegal.
  rewrite /isDelaunayLocal.
  rewrite (_ : (triangle2points t1 tm) (Ordinal zero<3) = tm t1 (Ordinal zero<3))
                      ; last first.
    rewrite /triangle2points.
    by apply ffunE.
  rewrite (_ : (triangle2points t1 tm) (Ordinal un<3) = tm t1 (Ordinal un<3))
                    ; last first.
    rewrite /triangle2points.
    by apply ffunE.
  rewrite (_ : (triangle2points t1 tm) (Ordinal deux<3) = tm t1 (Ordinal deux<3))
                      ; last first.
    rewrite /triangle2points.
    by apply ffunE.
  rewrite -/pt1 -/p1 -/q1.
  set btemp1 := ~~ inCircle pt1 t2 tm && ~~ inCircle q1 t2 tm .
  set btemp2 := ~~ inCircle p1 t2 tm.
  rewrite andb_false_iff /btemp1 andb_false_iff /btemp2 !negb_false_iff.
  rewrite {btemp1}.
  rewrite {btemp2}.
  move=> illegal.
  case cas1 : (inCircle pt1 t2 tm == true).
    move/eqP: cas1.
    rewrite /inCircle /inCircle_point.
    rewrite expand_det44 !mxE !//=.
    rewrite expand_det44. rewrite !mxE.
    rewrite !mul1l.
    rewrite !expr2 !mul1r.

  rewrite (_  : (nat_of_ord (@Ordinal 4 2 isT) == 2)); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 1 isT) == 1)); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 2 isT) == 0) = false); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 2 isT) == 1) = false); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 1 isT) == 0) = false); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 0 isT) == 1) = false); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 0 isT) == 0) ); last first.
      by [].
  rewrite (_  : (nat_of_ord (@Ordinal 4 3 isT) = 3) ); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 3 isT) == 1) = false); last first.
      by [].
  rewrite (_  : ((@Ordinal 4 3 isT) == 0) = false); last first.
      by [].
  rewrite (_  : (3 == 2) = false); last first.
      by [].


    have egal_tmp :(point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
   (point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1 +
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1) -
   point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
   (point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1 +
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1) +
   point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
   (point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) -
    point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) +
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1 +
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1) -
   point2R1 pt1 *
   (point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) -
    point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) +
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)))) 
  

      =(point2R1 p2 *
   (point2R2 q2 *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    point2R2 q2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt2 +
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1 +
    point2R2 pt2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1) -
   point2R1 q2 *
   (point2R2 p2 *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt2 +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1 +
    point2R2 pt2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1) +
   point2R1 pt2 *
   (point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1 +
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1) -
   point2R1 pt1 *
   (point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt2 +
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt2)).
    
    set a := point2R1 (tm t1 (Ordinal zero<3)).
    set b := point2R2 (tm t1 (Ordinal zero<3)).
    set c := point2R1 (tm t1 (Ordinal un<3)).
    set d := point2R2 (tm t1 (Ordinal un<3)).
    set e := point2R1 (tm t1 (Ordinal deux<3)).
    set f := point2R2 (tm t1 (Ordinal deux<3)).

    set a2 := point2R1 (tm t2 (Ordinal zero<3)).
    set b2 := point2R2 (tm t2 (Ordinal zero<3)).
    set c2 := point2R1 (tm t2 (Ordinal un<3)).
    set d2 := point2R2 (tm t2 (Ordinal un<3)).
    set e2 := point2R1 (tm t2 (Ordinal deux<3)).
    set f2 := point2R2 (tm t2 (Ordinal deux<3)).       
    
    prefield. ring.

    rewrite egal_tmp.
    rewrite {egal_tmp}.
    by [].

  case cas2 : (inCircle q1 t2 tm == true).
    move/eqP: cas2.
    rewrite adj2.
    rewrite /inCircle.
    rewrite /q2.
    have contra : (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2 (Ordinal un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2 (Ordinal un<3)) ^+ 2 +
                              point2R2
                                (tm t2 (Ordinal un<3)) ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2
                              else 1))) = 0.
    rewrite expand_det44 !mxE !//=.
    rewrite !expr2 !mul1l !mul1r.
    
    set a := point2R1 (tm t1 (Ordinal zero<3)).
    set b := point2R2 (tm t1 (Ordinal zero<3)).
    set c := point2R1 (tm t1 (Ordinal un<3)).
    set d := point2R2 (tm t1 (Ordinal un<3)).
    set e := point2R1 (tm t1 (Ordinal deux<3)).
    set f := point2R2 (tm t1 (Ordinal deux<3)).

    set a2 := point2R1 (tm t2 (Ordinal zero<3)).
    set b2 := point2R2 (tm t2 (Ordinal zero<3)).
    set c2 := point2R1 (tm t2 (Ordinal un<3)).
    set d2 := point2R2 (tm t2 (Ordinal un<3)).
    set e2 := point2R1 (tm t2 (Ordinal deux<3)).
    set f2 := point2R2 (tm t2 (Ordinal deux<3)).
    prefield; ring.
    rewrite lt0r.
    move/andP=> hypocontra.
    move: hypocontra.
    move=> [contra2 hypo].
    move/eqP: contra => contra.
    move: contra contra2.
    set tmp :=(\det (\matrix_(i, j) (if i == 0
                       then
                        if j == 0
                        then
                         point2R1 (tm t2 (Ordinal zero<3))
                        else
                         if j == 1
                         then
                          point2R2 (tm t2 (Ordinal zero<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1
                             (tm t2 (Ordinal zero<3)) ^+ 2 +
                           point2R2
                             (tm t2 (Ordinal zero<3)) ^+ 2
                          else 1
                       else
                        if i == 1
                        then
                         if j == 0
                         then
                          point2R1 (tm t2 (Ordinal un<3))
                         else
                          if j == 1
                          then
                           point2R2 (tm t2 (Ordinal un<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                            ^+ 2 +
                            point2R2 (tm t2 (Ordinal un<3))
                            ^+ 2
                           else 1
                        else
                         if nat_of_ord i == 2
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal deux<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal deux<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal deux<3))
                             ^+ 2
                            else 1
                         else
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal deux<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal deux<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal deux<3))
                             ^+ 2
                            else 1))).
      set b1 := tmp == 0.
      move/negP=> cont1.
      move/negP=> cont2.
      by [].

    move:illegal.
    move=> [[a |b] |c].
        move/eqP :a => a.
        move: a.
        move/negbT : cas1.
        set b1 := inCircle pt1 t2 tm == true.
        move=> cas1 a.
        have cont : b1 && ~~b1.
          apply/andP; split; by [].
        by rewrite andb_negb_r in cont.
      move/eqP :b => b.
      move: b.
      move/negbT : cas2.
      set b1 := inCircle q1 t2 tm == true.
      move=> cas2 b.
      have cont : b1 && ~~b1.
        apply/andP; split; by [].
      by rewrite andb_negb_r in cont.
    move : c.
    rewrite adj1.
    rewrite /inCircle.
    rewrite /p2.
    have contra :   (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2 (Ordinal un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2 (Ordinal un<3)) ^+ 2 +
                              point2R2
                                (tm t2 (Ordinal un<3)) ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal un<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal un<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal un<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal un<3))
                               ^+ 2
                              else 1))) = 0.
    rewrite expand_det44 !mxE !//=.
    rewrite !mul1l.
    rewrite !expr2 !mul1r.
    
    set a := point2R1 (tm t1 (Ordinal zero<3)).
    set b := point2R2 (tm t1 (Ordinal zero<3)).
    set c := point2R1 (tm t1 (Ordinal un<3)).
    set d := point2R2 (tm t1 (Ordinal un<3)).
    set e := point2R1 (tm t1 (Ordinal deux<3)).
    set f := point2R2 (tm t1 (Ordinal deux<3)).

    set a2 := point2R1 (tm t2 (Ordinal zero<3)).
    set b2 := point2R2 (tm t2 (Ordinal zero<3)).
    set c2 := point2R1 (tm t2 (Ordinal un<3)).
    set d2 := point2R2 (tm t2 (Ordinal un<3)).
    set e2 := point2R1 (tm t2 (Ordinal deux<3)).
    set f2 := point2R2 (tm t2 (Ordinal deux<3)).
    prefield; ring.
    rewrite lt0r.
    move/andP=> hypocontra.
    move: hypocontra.
    move=> [contra2 hypo].
    move/eqP: contra => contra.
    move: contra contra2.
    set tmp :=\det (\matrix_(i, j) (if i == 0
                      then
                       if j == 0
                       then
                        point2R1 (tm t2 (Ordinal zero<3))
                       else
                        if j == 1
                        then
                         point2R2 (tm t2 (Ordinal zero<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t2 (Ordinal zero<3))
                          ^+ 2 +
                          point2R2 (tm t2 (Ordinal zero<3))
                          ^+ 2
                         else 1
                      else
                       if i == 1
                       then
                        if j == 0
                        then
                         point2R1 (tm t2 (Ordinal un<3))
                        else
                         if j == 1
                         then
                          point2R2 (tm t2 (Ordinal un<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1 (tm t2 (Ordinal un<3))
                           ^+ 2 +
                           point2R2 (tm t2 (Ordinal un<3))
                           ^+ 2
                          else 1
                       else
                        if nat_of_ord i == 2
                        then
                         if j == 0
                         then
                          point2R1 (tm t2 (Ordinal deux<3))
                         else
                          if j == 1
                          then
                           point2R2
                             (tm t2 (Ordinal deux<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1
                              (tm t2 (Ordinal deux<3)) ^+ 2 +
                            point2R2
                              (tm t2 (Ordinal deux<3)) ^+ 2
                           else 1
                        else
                         if j == 0
                         then
                          point2R1 (tm t2 (Ordinal un<3))
                         else
                          if j == 1
                          then
                           point2R2 (tm t2 (Ordinal un<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                            ^+ 2 +
                            point2R2 (tm t2 (Ordinal un<3))
                            ^+ 2
                           else 1)).
      set b1 := tmp == 0.
      move/negP=> cont1.
      move/negP=> cont2.
      by [].

  move=> h.
  move: (h infoLem1 infoLem2 infoLem3).
  move=> [H1 H2].
  by [].



(* On va maintenant faire de même pour new_tr1 *)

move : (@ccw_exchange p2 q2 pt2 pt1).
rewrite (_ : (new_tr1 (inZp 0)) = pt1); last first.
  rewrite /new_tr1.
  rewrite /pt2.
  rewrite !//=.
  rewrite (_ : tm t1 (Ordinal zero<3) == tm t1 (Ordinal zero<3) = true)
          ; last first.
    apply/eqP.
    by [].
  rewrite //=.
  change ( tm t1 (point2indext1t2 (tm t1 (Ordinal zero<3)) t1 t2 tm) 
          = tm t1 (Ordinal zero<3)).
  rewrite point2indext1t2_correct.
  by [].
  rewrite /pt_in_triangle.
  rewrite (_ : tm t1 (Ordinal zero<3) == tm t1 (Ordinal zero<3) = true)
          ; last first.
    apply/eqP.
    by [].
  by [].
  by [].


(*  faire de même que le paragraphe précédent pour faire apparaitre dans le but
    les points p2 q2 pt2 etc ... *)
rewrite (_ : (new_tr1 (inZp 1)) = pt2); last first.
  rewrite /new_tr1.
  rewrite !//=.
  move: notint1. rewrite /pt_in_triangle. rewrite not_true_iff_false.
  move=> notint1.
  rewrite notint1.
  rewrite /pt1.
  rewrite point2indext2t1_correct.
  by [].
  rewrite /pt_in_triangle.
  rewrite (_ : tm t2 (Ordinal zero<3) == tm t2 (Ordinal zero<3) = true)
          ; last first.
    apply/eqP.
    by [].
  by [].
  apply not_true_iff_false in notint1.
  move:notint1.
  change (~ pt_in_triangle tm pt2 t1 ->
~ pt_in_triangle tm (tm t2 (Ordinal zero<3)) t1).
  by [].


rewrite (_ : (new_tr1 (inZp 2)) = p2); last first.
  rewrite /new_tr1.
  rewrite !//=.
  rewrite (_ : tm t1 (Ordinal zero<3) == tm t1 (Ordinal zero<3) = true)
        ; last first.
    apply/eqP.
    by [].
  rewrite //=.
  change (tm t1
    (addOrd3 (point2indext1t2 pt1 t1 t2 tm)
       (Ordinal deux<3)) = p2).
  rewrite /point2indext1t2.
  rewrite /pt1.
  rewrite (_ : tm t1 (Ordinal zero<3) == tm t1 (Ordinal zero<3) = true)
        ; last first.
    apply/eqP.
    by [].
  move: notint2. rewrite /pt_in_triangle. rewrite not_true_iff_false.
  set b1 := ((pt1 == tm t2 (Ordinal zero<3))
                || (pt1 == tm t2 (Ordinal un<3))).
  set b2 := (pt1 == tm t2 (Ordinal deux<3)).
  move=> notint2.
  apply orb_false_iff in notint2.
  move: notint2.
  move=> [notint11 notint12].
  apply orb_false_iff in notint11.
  move:notint11.
  move=> [notint111 notint112]. 
  rewrite (_ : (addOrd3 (Ordinal zero<3) (Ordinal deux<3)) 
                 = (Ordinal deux<3)); last first.
    rewrite /addOrd3.
    apply val_inj.
    by rewrite //.
  by [].


have infoLem1 : Num.lt 0 (leftpoint p2 q2 pt2).
  rewrite /p2 /q2 /pt2.
  apply ccw_axiom_1.
  rewrite ( _ : Num.lt 0
  (leftpoint (tm t2 (Ordinal zero<3))
     (tm t2 (Ordinal un<3)) (tm t2 (Ordinal deux<3))) = oriented t2 tm)
        ; last first.
    rewrite /oriented.
    rewrite (_ : (Ordinal zero<3) = inZp 0); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal un<3) = inZp 1); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal deux<3) = inZp 2); last first.
      apply: val_inj.
      by rewrite //.
  by [].
by [].


have infoLem2 : Num.lt 0 (leftpoint q2 p2 pt1).
  rewrite -adj1.
  rewrite -adj2.
  rewrite /q1 /p1 /pt1.
  apply ccw_axiom_1.
  rewrite ( _ : Num.lt 0
  (leftpoint (tm t1 (Ordinal zero<3))
     (tm t1 (Ordinal un<3)) (tm t1 (Ordinal deux<3))) = oriented t1 tm)
        ; last first.
    rewrite /oriented.
    rewrite (_ : (Ordinal zero<3) = inZp 0); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal un<3) = inZp 1); last first.
      apply: val_inj.
      by rewrite //.
    rewrite (_ : (Ordinal deux<3) = inZp 2); last first.
      apply: val_inj.
      by rewrite //.
  by [].
by [].


have infoLem3 : inCircle_point p2 q2 pt2 pt1.
  move/eqP: illegal.
  rewrite /isDelaunayLocal.
  rewrite (_ : (triangle2points t1 tm) (Ordinal zero<3) = tm t1 (Ordinal zero<3))
                      ; last first.
    rewrite /triangle2points.
    by apply ffunE.
  rewrite (_ : (triangle2points t1 tm) (Ordinal un<3) = tm t1 (Ordinal un<3))
                    ; last first.
    rewrite /triangle2points.
    by apply ffunE.
  rewrite (_ : (triangle2points t1 tm) (Ordinal deux<3) = tm t1 (Ordinal deux<3))
                      ; last first.
    rewrite /triangle2points.
    by apply ffunE.
  rewrite -/pt1 -/p1 -/q1.
  set btemp1 := ~~ inCircle pt1 t2 tm && ~~ inCircle q1 t2 tm .
  set btemp2 := ~~ inCircle p1 t2 tm.
  rewrite andb_false_iff /btemp1 andb_false_iff /btemp2 !negb_false_iff.
  rewrite {btemp1}.
  rewrite {btemp2}.
  move=> illegal.
  case cas1 : (inCircle pt1 t2 tm == true).
    move/eqP: cas1.
    rewrite /inCircle /inCircle_point.
    rewrite expand_det44 !mxE !//=.
    rewrite !mul1l.
    rewrite !expr2 !mul1r.

    rewrite expand_det44 !mxE !//=.
    rewrite !mul1l !mul1r.


    have egal_tmp : (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
   (point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1 +
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1) -
   point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
   (point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1 +
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1) +
   point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
   (point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) -
    point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) +
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1 +
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1) -
   point2R1 pt1 *
   (point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) -
    point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) +
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3)) +
    point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 (tm t2 (@Ordinal 3 2 deux<3))))
  

      = (point2R1 p2 *
   (point2R2 q2 *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    point2R2 q2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt2 +
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1 +
    point2R2 pt2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1) -
   point2R1 q2 *
   (point2R2 p2 *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    point2R2 p2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt2 +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1 +
    point2R2 pt2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) *
    point2R2 pt1) +
   point2R1 pt2 *
   (point2R2 p2 *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 p2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) * 
    point2R2 q2 +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt1 +
    point2R2 q2 *
    (point2R1 pt1 * point2R1 pt1 +
     point2R2 pt1 * point2R2 pt1) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt1) -
   point2R1 pt1 *
   (point2R2 p2 *
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) -
    point2R2 p2 *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) * 
    point2R2 q2 +
    (point2R1 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R1 (tm t2 (@Ordinal 3 1 un<3)) +
     point2R2 (tm t2 (@Ordinal 3 1 un<3)) *
     point2R2 (tm t2 (@Ordinal 3 1 un<3))) *
    point2R2 pt2 +
    point2R2 q2 *
    (point2R1 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R1 (tm t2 (@Ordinal 3 0 zero<3)) +
     point2R2 (tm t2 (@Ordinal 3 0 zero<3)) *
     point2R2 (tm t2 (@Ordinal 3 0 zero<3))) -
    (point2R1 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R1 (tm t2 (@Ordinal 3 2 deux<3)) +
     point2R2 (tm t2 (@Ordinal 3 2 deux<3)) *
     point2R2 (tm t2 (@Ordinal 3 2 deux<3))) *
    point2R2 pt2)).
        set a := point2R1 (tm t1 (Ordinal zero<3)).
        set b := point2R2 (tm t1 (Ordinal zero<3)).
        set c := point2R1 (tm t1 (Ordinal un<3)).
        set d := point2R2 (tm t1 (Ordinal un<3)).
        set e := point2R1 (tm t1 (Ordinal deux<3)).
        set f := point2R2 (tm t1 (Ordinal deux<3)).

        set a2 := point2R1 (tm t2 (Ordinal zero<3)).
        set b2 := point2R2 (tm t2 (Ordinal zero<3)).
        set c2 := point2R1 (tm t2 (Ordinal un<3)).
        set d2 := point2R2 (tm t2 (Ordinal un<3)).
        set e2 := point2R1 (tm t2 (Ordinal deux<3)).
        set f2 := point2R2 (tm t2 (Ordinal deux<3)).
        prefield; ring.

    rewrite egal_tmp.
    rewrite {egal_tmp}.
    by [].

  case cas2 : (inCircle q1 t2 tm == true).
    move/eqP: cas2.
    rewrite adj2.
    rewrite /inCircle.
    rewrite /q2.
    have contra : (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2 (Ordinal un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2 (Ordinal un<3)) ^+ 2 +
                              point2R2
                                (tm t2 (Ordinal un<3)) ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2
                              else 1))) = 0.
    rewrite expand_det44 !mxE !//=.
    rewrite !mul1r.
    
    set a := point2R1 (tm t1 (Ordinal zero<3)).
    set b := point2R2 (tm t1 (Ordinal zero<3)).
    set c := point2R1 (tm t1 (Ordinal un<3)).
    set d := point2R2 (tm t1 (Ordinal un<3)).
    set e := point2R1 (tm t1 (Ordinal deux<3)).
    set f := point2R2 (tm t1 (Ordinal deux<3)).

    set a2 := point2R1 (tm t2 (Ordinal zero<3)).
    set b2 := point2R2 (tm t2 (Ordinal zero<3)).
    set c2 := point2R1 (tm t2 (Ordinal un<3)).
    set d2 := point2R2 (tm t2 (Ordinal un<3)).
    set e2 := point2R1 (tm t2 (Ordinal deux<3)).
    set f2 := point2R2 (tm t2 (Ordinal deux<3)).
    prefield; ring.
    rewrite lt0r.
    move/andP=> hypocontra.
    move: hypocontra.
    move=> [contra2 hypo].
    move/eqP: contra => contra.
    move: contra contra2.
    set tmp :=(\det (\matrix_(i, j) (if i == 0
                       then
                        if j == 0
                        then
                         point2R1 (tm t2 (Ordinal zero<3))
                        else
                         if j == 1
                         then
                          point2R2 (tm t2 (Ordinal zero<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1
                             (tm t2 (Ordinal zero<3)) ^+ 2 +
                           point2R2
                             (tm t2 (Ordinal zero<3)) ^+ 2
                          else 1
                       else
                        if i == 1
                        then
                         if j == 0
                         then
                          point2R1 (tm t2 (Ordinal un<3))
                         else
                          if j == 1
                          then
                           point2R2 (tm t2 (Ordinal un<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                            ^+ 2 +
                            point2R2 (tm t2 (Ordinal un<3))
                            ^+ 2
                           else 1
                        else
                         if nat_of_ord i == 2
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal deux<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal deux<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal deux<3))
                             ^+ 2
                            else 1
                         else
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal deux<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal deux<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal deux<3))
                             ^+ 2
                            else 1))).
      set b1 := tmp == 0.
      move/negP=> cont1.
      move/negP=> cont2.
      by [].

    move:illegal.
    move=> [[a |b] |c].
        move/eqP :a => a.
        move: a.
        move/negbT : cas1.
        set b1 := inCircle pt1 t2 tm == true.
        move=> cas1 a.
        have cont : b1 && ~~b1.
          apply/andP; split; by [].
        by rewrite andb_negb_r in cont.
      move/eqP :b => b.
      move: b.
      move/negbT : cas2.
      set b1 := inCircle q1 t2 tm == true.
      move=> cas2 b.
      have cont : b1 && ~~b1.
        apply/andP; split; by [].
      by rewrite andb_negb_r in cont.
    move : c.
    rewrite adj1.
    rewrite /inCircle.
    rewrite /p2.
    have contra :   (\det (\matrix_(i<4, j<4) (if i == 0
                         then
                          if j == 0
                          then
                           point2R1
                             (tm t2 (Ordinal zero<3))
                          else
                           if j == 1
                           then
                            point2R2
                              (tm t2 (Ordinal zero<3))
                           else
                            if nat_of_ord j == 2
                            then
                             point2R1
                               (tm t2 (Ordinal zero<3))
                             ^+ 2 +
                             point2R2
                               (tm t2 (Ordinal zero<3))
                             ^+ 2
                            else 1
                         else
                          if i == 1
                          then
                           if j == 0
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                           else
                            if j == 1
                            then
                             point2R2
                               (tm t2 (Ordinal un<3))
                            else
                             if nat_of_ord j == 2
                             then
                              point2R1
                                (tm t2 (Ordinal un<3)) ^+ 2 +
                              point2R2
                                (tm t2 (Ordinal un<3)) ^+ 2
                             else 1
                          else
                           if nat_of_ord i == 2
                           then
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal deux<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal deux<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal deux<3))
                               ^+ 2
                              else 1
                           else
                            if j == 0
                            then
                             point2R1
                               (tm t2 (Ordinal un<3))
                            else
                             if j == 1
                             then
                              point2R2
                                (tm t2 (Ordinal un<3))
                             else
                              if nat_of_ord j == 2
                              then
                               point2R1
                                 (tm t2 (Ordinal un<3))
                               ^+ 2 +
                               point2R2
                                 (tm t2 (Ordinal un<3))
                               ^+ 2
                              else 1))) = 0.

    rewrite expand_det44 !mxE !//=.
    rewrite !mul1r.
    

    set a := point2R1 (tm t1 (Ordinal zero<3)).
    set b := point2R2 (tm t1 (Ordinal zero<3)).
    set c := point2R1 (tm t1 (Ordinal un<3)).
    set d := point2R2 (tm t1 (Ordinal un<3)).
    set e := point2R1 (tm t1 (Ordinal deux<3)).
    set f := point2R2 (tm t1 (Ordinal deux<3)).

    set a2 := point2R1 (tm t2 (Ordinal zero<3)).
    set b2 := point2R2 (tm t2 (Ordinal zero<3)).
    set c2 := point2R1 (tm t2 (Ordinal un<3)).
    set d2 := point2R2 (tm t2 (Ordinal un<3)).
    set e2 := point2R1 (tm t2 (Ordinal deux<3)).
    set f2 := point2R2 (tm t2 (Ordinal deux<3)).
    prefield; ring.
    rewrite lt0r.
    move/andP=> hypocontra.
    move: hypocontra.
    move=> [contra2 hypo].
    move/eqP: contra => contra.
    move: contra contra2.
    set tmp :=\det (\matrix_(i, j) (if i == 0
                      then
                       if j == 0
                       then
                        point2R1 (tm t2 (Ordinal zero<3))
                       else
                        if j == 1
                        then
                         point2R2 (tm t2 (Ordinal zero<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t2 (Ordinal zero<3))
                          ^+ 2 +
                          point2R2 (tm t2 (Ordinal zero<3))
                          ^+ 2
                         else 1
                      else
                       if i == 1
                       then
                        if j == 0
                        then
                         point2R1 (tm t2 (Ordinal un<3))
                        else
                         if j == 1
                         then
                          point2R2 (tm t2 (Ordinal un<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1 (tm t2 (Ordinal un<3))
                           ^+ 2 +
                           point2R2 (tm t2 (Ordinal un<3))
                           ^+ 2
                          else 1
                       else
                        if nat_of_ord i == 2
                        then
                         if j == 0
                         then
                          point2R1 (tm t2 (Ordinal deux<3))
                         else
                          if j == 1
                          then
                           point2R2
                             (tm t2 (Ordinal deux<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1
                              (tm t2 (Ordinal deux<3)) ^+ 2 +
                            point2R2
                              (tm t2 (Ordinal deux<3)) ^+ 2
                           else 1
                        else
                         if j == 0
                         then
                          point2R1 (tm t2 (Ordinal un<3))
                         else
                          if j == 1
                          then
                           point2R2 (tm t2 (Ordinal un<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1 (tm t2 (Ordinal un<3))
                            ^+ 2 +
                            point2R2 (tm t2 (Ordinal un<3))
                            ^+ 2
                           else 1)).
      set b1 := tmp == 0.
      move/negP=> cont1.
      move/negP=> cont2.
      by [].

  move=> h.
  move: (h infoLem1 infoLem2 infoLem3).
  move=> [H1 H2].
  by [].
Qed.



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
