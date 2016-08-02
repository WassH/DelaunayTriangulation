Require Import Arith.
Require Import EqNat.
Require Import Ring.
Require Import Bool.
Require Coq.Init.Nat.
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
rewrite (_ : k1 = 1 - k2 - k3).
simpl in k1, k2, k3.
prefield. field.


rewrite -(eqP H3). simpl in k1. prefield; ring.


rewrite u1q.
Search _ (Num.lt _ (_*_)).
rewrite pmulr_rgt0; last first.
exact: H6.
rewrite toriented !//=.


(* On refait de même avec les points un<3 et deux<3 *)
set u2 := \det _.
  have u2q : u2 = k1 * bd.
  rewrite /u2.
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
rewrite (_ : k1 = 1 - k2 - k3); last first.
  rewrite -(eqP H3). simpl in k1. prefield; ring.
simpl in k2, k3.
prefield.
field.

rewrite u2q.
Search _ (Num.lt _ (_*_)).
rewrite pmulr_rgt0; last first.
exact: H4.
rewrite toriented !//=.


(* On refait de même avec les points deux<3 et zero<3 *)
set u3 := \det _.
  have u3q : u3 = k2 * bd.
  rewrite /u3.
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
rewrite (_ : k1 = 1 - k2 - k3); last first.
  rewrite -(eqP H3). simpl in k1. prefield; ring.
simpl in k2, k3.
prefield.
field.

rewrite u3q.
Search _ (Num.lt _ (_*_)).
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
rewrite /bd.
rewrite /leftpoint.
rewrite expand_det33 !mxE !//=.
rewrite /leftpoint.
rewrite expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//=.
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
Search _ (Num.lt _ _ = _).
auto.

split.
move: toriented.
rewrite /bd.
rewrite /leftpoint.
rewrite expand_det33 !mxE !//=.
rewrite /leftpoint.
rewrite expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//=.
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
Search _ (Num.lt _ _ = _).
auto.

split.
move:toriented.
rewrite /bd.
rewrite /leftpoint.
rewrite expand_det33 !mxE !//=.
rewrite /leftpoint.
rewrite expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//=.
rewrite expand_det33 !mxE !//=.
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
Search _ (Num.lt _ _ = _).
auto.

split.
Search _ (_/_>0).
rewrite divr_gt0; last first.
      by [].
    have egal_det12 : leftpoint (tm t (Ordinal un<3)) (tm t (Ordinal deux<3)) p
                   = leftpoint p (tm t (Ordinal un<3)) (tm t (Ordinal deux<3));
    last first.
      rewrite egal_det12.
      by [].
    rewrite /leftpoint.
    rewrite expand_det33 !mxE !//=.
    rewrite expand_det33 !mxE !//=.
    rewrite !mulr1 !mul1r.
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
    rewrite /leftpoint.
    rewrite expand_det33 !mxE !//=.
    rewrite expand_det33 !mxE !//=.
    rewrite !mulr1 !mul1r.
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
    rewrite /leftpoint.
    rewrite expand_det33 !mxE !//=.
    rewrite expand_det33 !mxE !//=.
    rewrite !mulr1 !mul1r.
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

Lemma fois_div (n1 n2: rat_Ring) : n2 <>0 -> n1 *n2/n2 = n1.
Proof.
move=> hypn2.
prefield.
by field.
Qed.


Definition convex_strict_fun (f : rat*rat -> rat) :=
 forall (k:rat), forall (x:rat*rat), forall (y:rat*rat), (0<k) -> (k<1) 
          -> (x.1 != y.1) || (x.2 != y.2) ->
         f (k*x.1 + (1-k)*y.1, k*x.2 + (1-k)*y.2) 
                  < k*(f x) + (1-k)* (f y).


Lemma sum_eq0 :forall (n:nat) (k:seq rat),
[forall (i:'I_(S n)|true), (Num.le 0 k`_((nat_of_ord) i))] ->
  ((\sum_(i < S n) (k`_((nat_of_ord) i)))==0) = [forall (i:'I_(S n)|true), k`_i == 0%Q].
Proof.
move => n k hyp.
have utile: forall m, ([forall (i:'I_(S m)|true), (Num.le 0 k`_((nat_of_ord) i))] ->
Num.le 0 (\sum_(i < m.+1) k`_i)).
  induction m.
    rewrite big_ord_recr !//=.
    rewrite big_ord0 !//=.
    rewrite -big_andE.
    rewrite big_ord_recr !//=.
    rewrite big_ord0 !//=.
    rewrite plus0l.
    by [].
  rewrite -big_andE.
  rewrite big_ord_recr !//=.
  move/andP=> hypSm.
  move:hypSm.
  move=> [hypSm H].
  rewrite big_ord_recr !//=.
  Search _ (Num.le 0 (_+_)).
  apply: addr_ge0.
  move:hypSm.
  rewrite big_andE.
  move=>hypSm.
  apply (IHm hypSm).
by [].


induction n.
  rewrite big_ord_recl !//=.
  rewrite big_ord0 !//=.
  rewrite -big_andE.
  rewrite !big_ord_recr !//=.
  rewrite big_ord0 !//=.
  rewrite plus0r.
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

rewrite big_ord_recr !//=.
rewrite -big_andE. rewrite [RHS]big_ord_recr. rewrite //=.
rewrite big_andE.
have utileSn : ([forall (i:'I_(S n)|true), (Num.le 0 k`_((nat_of_ord) i))] ->
 Num.le 0 (\sum_(i < n.+1) k`_i)).
  exact: (utile n).


(* rewrite -big_andE. rewrite big_ord_recr. rewrite !//=. *)
rewrite -(IHn hyp1).
Search _ ((_ + _) ==0 = (_ == 0) && (_ == 0)).
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
  rewrite -big_andE.
  rewrite big_ord_recr !//=.
  move/andP=> hypSm.
  move:hypSm.
  move=> [hypSm H].
  rewrite big_ord_recr !//=.
  Search _ (Num.le 0 (_+_)).
  apply: addr_ge0.
  move:hypSm.
  rewrite big_andE.
  move=>hypSm.
  apply (IHm hypSm).
by [].
Qed.



(* Ajouter comme hypothèse que les x_i sont deux à deux distincts *)
Lemma Jensen_inequality (n:nat) (f : rat*rat -> rat) 
              (f_is_convex : convex_strict_fun f)
          (k : seq rat) (x :seq (rat*rat))
            (somme_egal_1 : \sum_(i<n) (k`_((nat_of_ord) i)) = 1)  :
  (n>2)%nat -> [forall (i:'I_n|true), (Num.lt 0 k`_((nat_of_ord) i))] ->
  f (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1, 
          \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2)
            < \sum_(i<n) (k`_((nat_of_ord) i))*(f (x`_((nat_of_ord) i))).
Proof.
move=> nsup2 hypok.
induction n.
  move:nsup2.
  by rewrite !//=.
set lambda := \sum_(i<n) (k`_((nat_of_ord) i)).
case info: (lambda==0); last first.
  set x1 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1)/lambda.
  set x2 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2)/lambda.
  rewrite big_ord_recr !//=.
  rewrite big_ord_recr !//=.
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).1
                   = x1 * lambda);last first.
    rewrite /x1.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div.
    rewrite mul1r.
    rewrite [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)).2
                   = x2 * lambda);last first.
    rewrite /x2.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div.
    rewrite mul1r.
    rewrite [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].
  rewrite big_ord_recr !//=.
  have : (Num.lt (f (x1 * lambda + k`_n * (x`_n).1, x2 * lambda + k`_n * (x`_n).2))
                  (lambda*(f (x1, x2)) + k`_n* (f ((x`_n).1, (x`_n).2)))).
    move:f_is_convex.
    rewrite /convex_strict_fun.
    move=> hypconvex.
      have : k`_n = 1 - lambda.
      rewrite /lambda.
      Search _ (_ = _  -> _+_ =_+_).
      rewrite -somme_egal_1.
      rewrite big_ord_recr !//=.
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
    rewrite -egalx1.
    rewrite -egalx2.
    rewrite -egaly1.
    rewrite -egaly2.
    simpl in x_f.
    simpl in y_f.
    have info3 : Num.lt 0 lambda.
      rewrite /lambda.
      Search _ (Num.lt 0 _ = ~~(_) && _).
      rewrite lt0r.
      apply/andP.
      split.
        rewrite -/lambda.
        by rewrite info !//=.
      About pos_elt_pos_sum.
      have hypokle : forall m, (m<n)%N -> 
            [forall (i :'I_m| true), Num.le 0 (k`_((nat_of_ord) i))].
        induction m.
          rewrite -big_andE.
          by rewrite big_ord0.
        rewrite -big_andE.
        rewrite big_ord_recr !//=.
        move=>inf.
        rewrite big_andE.
        apply/andP.
        split.
          case info_utile: (m<n)%N.
            apply (IHm info_utile).
          Search _ ((_<_) = false).
          move: info_utile.
          move/negbT => info_utile.
          rewrite -leqNgt in info_utile.
          auto.
        have ineg: (m<n.+1)%N.
          exact: ltn_trans (ltn_trans (ltnSn m) (inf)) (ltnSn n).
        have t: Num.lt 0 k`_m; last first.
          rewrite le0r.
          apply/orP.
          by right.
        
        


      (* apply (pos_elt_pos_sum hypokle). *)
    (*
    apply: hypconvex.
    



    apply : hypconvex lambda (x1, x2) ((x`_n).1, (x`_n).2))



move/eqP:info.
rewrite /lambda.
move=> info.
move: somme_egal_1.
rewrite big_ord_recr.
rewrite !//=.
rewrite info plus0l.
move=>somme_egal_1.
rewrite !big_ord_recr !//=.
move: hypok.
rewrite (sum_eq0 info).
rewrite -big_andE.
(* utilier big1_seq pour remplacer les k_i par 0 *)



Qed.

 *)
Admitted.


Definition fJensen:= fun x:rat*rat => x.1 ^+2 + x.2 ^+2.


Lemma sum_gt01 : forall (r1 r2:rat), 
                  Num.lt 0 r1 -> Num.le 0 r2 -> Num.lt 0 (r1+r2).
Proof.
move=> r1 r2 hypr1 hypr2.
Search _ (Num.lt _ (_+_)).
rewrite (_: r1+r2 = r1 - (-r2)); last first.
  prefield. field.
rewrite subr_gt0.
Search _ (Num.le 0 _ = _ || _).
move: hypr2.
rewrite le0r.
case info : (r2 == 0).
  rewrite !//=.
  move/eqP:info. move=>info.
  rewrite info.
  by [].
rewrite !//=.
move=> hypr2.
Search _ (Num.lt (-_) 0).
move: hypr2.
rewrite -oppr_lt0.
move=> hypr2.
apply (ltr_trans hypr2 hypr1).
Qed.



Lemma sum_gt02 : forall (r1 r2:rat), 
                  Num.le 0 r1 -> Num.lt 0 r2 -> Num.lt 0 (r1+r2).
Proof.
move=> r1 r2 hypr1 hypr2.
Search _ (Num.lt _ (_+_)).
rewrite (_: r1+r2 = r2 - (-r1)); last first.
  prefield. field.
rewrite subr_gt0.
Search _ (Num.le 0 _ = _ || _).
move: hypr1.
rewrite le0r.
case info : (r1 == 0).
  rewrite !//=.
  move/eqP:info. move=>info.
  rewrite info.
  by [].
rewrite !//=.
move=> hypr1.
Search _ (Num.lt (-_) 0).
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
Search _ ( Num.lt 0 (_-_)).
rewrite -subr_gt0.
have info_egalite: (k * (x.1 * x.1 + x.2 * x.2) + (1 - k) * (y.1 * y.1 + y.2 * y.2) -
   ((k * x.1 + (1 - k) * y.1) * (k * x.1 + (1 - k) * y.1) +
    (k * x.2 + (1 - k) * y.2) * (k * x.2 + (1 - k) * y.2)))
  = k*(1-k)*((x.1 - y.1)^+2 + (x.2 - y.2)^+2).
  rewrite !expr2 !//=.
  prefield; ring.
rewrite info_egalite.
Search _ (Num.lt 0 (_*_)).
rewrite pmulr_rgt0; last first.
rewrite pmulr_rgt0.
Search _ (Num.lt 0 (_-_)).
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
rewrite /a.
rewrite GRing.mulf_neq0.
  by [].
move: Hxdify1.
Search _ (_-_==0).
by rewrite subr_eq0.
move: Hxdify1.
Search _ (_-_==0).
by rewrite subr_eq0.


set b := (x.2 -y.2).
rewrite expr2.
rewrite -expr2.
apply: sqr_ge0.


(* Cas 2 ou on a ~~ (x.2 == y.2) *)

rewrite /fJensen.
rewrite !expr2 !//=.
Search _ ( Num.lt 0 (_-_)).
rewrite -subr_gt0.
have info_egalite: (k * (x.1 * x.1 + x.2 * x.2) + (1 - k) * (y.1 * y.1 + y.2 * y.2) -
   ((k * x.1 + (1 - k) * y.1) * (k * x.1 + (1 - k) * y.1) +
    (k * x.2 + (1 - k) * y.2) * (k * x.2 + (1 - k) * y.2)))
  = k*(1-k)*((x.1 - y.1)^+2 + (x.2 - y.2)^+2).
  rewrite !expr2 !//=.
  prefield; ring.
rewrite info_egalite.
Search _ (Num.lt 0 (_*_)).
rewrite pmulr_rgt0; last first.
rewrite pmulr_rgt0.
Search _ (Num.lt 0 (_-_)).
rewrite subr_gt0.
exact:Hk1.
exact H0k.
apply: sum_gt02.
set a := (x.1 -y.1).
rewrite expr2.
rewrite -expr2.
apply: sqr_ge0.

set b := (x.2 -y.2).
rewrite expr2.
rewrite ltr_def.
apply/andP.
split; last first.
  rewrite -expr2.
  apply: sqr_ge0.
rewrite /b.
rewrite GRing.mulf_neq0.
  by [].
move: Hxdify2.
Search _ (_-_==0).
by rewrite subr_eq0.
move: Hxdify2.
Search _ (_-_==0).
by rewrite subr_eq0.
Qed.

Lemma lt_implies_le (r:rat) : Num.lt 0 r -> Num.le 0 r.
Proof.
rewrite lt0r.
move/andP=> H.
move: H.
move=> [H H2].
by [].
Qed.

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


  rewrite (expand_det_row _ (Ordinal (trois<4))).
  rewrite big_ord_recl.
  rewrite !mxE !//=.
  set cof1 := cofactor
  (\matrix_(i, j) (if i == 0
                   then
                    if j == 0
                    then point2R1 (tm t (Ordinal zero<3))
                    else
                     if j == 1
                     then point2R2 (tm t (Ordinal zero<3))
                     else
                      if nat_of_ord j == 2
                      then
                       point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                       point2R2 (tm t (Ordinal zero<3)) ^+ 2
                      else 1
                   else
                    if i == 1
                    then
                     if j == 0
                     then point2R1 (tm t (Ordinal un<3))
                     else
                      if j == 1
                      then point2R2 (tm t (Ordinal un<3))
                      else
                       if nat_of_ord j == 2
                       then
                        point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                        point2R2 (tm t (Ordinal un<3)) ^+ 2
                       else 1
                    else
                     if nat_of_ord i == 2
                     then
                      if j == 0
                      then point2R1 (tm t (Ordinal deux<3))
                      else
                       if j == 1
                       then point2R2 (tm t (Ordinal deux<3))
                       else
                        if nat_of_ord j == 2
                        then
                         point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                         point2R2 (tm t (Ordinal deux<3)) ^+ 2
                        else 1
                     else
                      if j == 0
                      then point2R1 p
                      else
                       if j == 1
                       then point2R2 p
                       else
                        if nat_of_ord j == 2
                        then point2R1 p ^+ 2 + point2R2 p ^+ 2
                        else 1)) (Ordinal trois<4) ord0.

  rewrite big_ord_recl.
  rewrite !mxE !//=.
  set cof2 := cofactor
   (\matrix_(i, j) (if i == 0
                    then
                     if j == 0
                     then point2R1 (tm t (Ordinal zero<3))
                     else
                      if j == 1
                      then point2R2 (tm t (Ordinal zero<3))
                      else
                       if nat_of_ord j == 2
                       then
                        point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                        point2R2 (tm t (Ordinal zero<3)) ^+ 2
                       else 1
                    else
                     if i == 1
                     then
                      if j == 0
                      then point2R1 (tm t (Ordinal un<3))
                      else
                       if j == 1
                       then point2R2 (tm t (Ordinal un<3))
                       else
                        if nat_of_ord j == 2
                        then
                         point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                         point2R2 (tm t (Ordinal un<3)) ^+ 2
                        else 1
                     else
                      if nat_of_ord i == 2
                      then
                       if j == 0
                       then point2R1 (tm t (Ordinal deux<3))
                       else
                        if j == 1
                        then point2R2 (tm t (Ordinal deux<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal deux<3)) ^+ 2
                         else 1
                      else
                       if j == 0
                       then point2R1 p
                       else
                        if j == 1
                        then point2R2 p
                        else
                         if nat_of_ord j == 2
                         then point2R1 p ^+ 2 + point2R2 p ^+ 2
                         else 1)) (Ordinal trois<4) 
   (lift ord0 ord0).

  rewrite big_ord_recl.
  rewrite !mxE !//=.
  set cof3 := cofactor
    (\matrix_(i, j) (if i == 0
                     then
                      if j == 0
                      then point2R1 (tm t (Ordinal zero<3))
                      else
                       if j == 1
                       then point2R2 (tm t (Ordinal zero<3))
                       else
                        if nat_of_ord j == 2
                        then
                         point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                         point2R2 (tm t (Ordinal zero<3)) ^+ 2
                        else 1
                     else
                      if i == 1
                      then
                       if j == 0
                       then point2R1 (tm t (Ordinal un<3))
                       else
                        if j == 1
                        then point2R2 (tm t (Ordinal un<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal un<3)) ^+ 2
                         else 1
                      else
                       if nat_of_ord i == 2
                       then
                        if j == 0
                        then point2R1 (tm t (Ordinal deux<3))
                        else
                         if j == 1
                         then point2R2 (tm t (Ordinal deux<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                           point2R2 (tm t (Ordinal deux<3)) ^+ 2
                          else 1
                       else
                        if j == 0
                        then point2R1 p
                        else
                         if j == 1
                         then point2R2 p
                         else
                          if nat_of_ord j == 2
                          then point2R1 p ^+ 2 + point2R2 p ^+ 2
                          else 1)) (Ordinal trois<4)
    (lift ord0 (lift ord0 ord0)).

  rewrite big_ord_recl.
  rewrite !mxE !//=.
  set cof4 := cofactor
     (\matrix_(i, j) (if i == 0
                      then
                       if j == 0
                       then point2R1 (tm t (Ordinal zero<3))
                       else
                        if j == 1
                        then point2R2 (tm t (Ordinal zero<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal zero<3)) ^+ 2
                         else 1
                      else
                       if i == 1
                       then
                        if j == 0
                        then point2R1 (tm t (Ordinal un<3))
                        else
                         if j == 1
                         then point2R2 (tm t (Ordinal un<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                           point2R2 (tm t (Ordinal un<3)) ^+ 2
                          else 1
                       else
                        if nat_of_ord i == 2
                        then
                         if j == 0
                         then point2R1 (tm t (Ordinal deux<3))
                         else
                          if j == 1
                          then point2R2 (tm t (Ordinal deux<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                            point2R2 (tm t (Ordinal deux<3)) ^+ 2
                           else 1
                        else
                         if j == 0
                         then point2R1 p
                         else
                          if j == 1
                          then point2R2 p
                          else
                           if nat_of_ord j == 2
                           then point2R1 p ^+ 2 + point2R2 p ^+ 2
                           else 1)) (Ordinal trois<4)
     (lift ord0 (lift ord0 (lift ord0 ord0))).

  rewrite big_ord0.
  rewrite /cof1.
  rewrite /cofactor.
  rewrite expand_det33 !mxE !//=.
  rewrite /cof2.
  rewrite /cofactor.
  rewrite expand_det33 !mxE !//=.
  rewrite /cof3.
  rewrite /cofactor.
  rewrite expand_det33 !mxE !//=.
  rewrite /cof4.
  rewrite /cofactor.
  rewrite expand_det33 !mxE !//=.


rewrite (expand_det_row _ (Ordinal (trois<4))).
rewrite big_ord_recl.
rewrite !mxE !//=.
set cof1' := cofactor
  (\matrix_(i, j) (if i == 0
                   then
                    if j == 0
                    then point2R1 (tm t (Ordinal zero<3))
                    else
                     if j == 1
                     then point2R2 (tm t (Ordinal zero<3))
                     else
                      if nat_of_ord j == 2
                      then
                       point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                       point2R2 (tm t (Ordinal zero<3)) ^+ 2
                      else 1
                   else
                    if i == 1
                    then
                     if j == 0
                     then point2R1 (tm t (Ordinal un<3))
                     else
                      if j == 1
                      then point2R2 (tm t (Ordinal un<3))
                      else
                       if nat_of_ord j == 2
                       then
                        point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                        point2R2 (tm t (Ordinal un<3)) ^+ 2
                       else 1
                    else
                     if nat_of_ord i == 2
                     then
                      if j == 0
                      then point2R1 (tm t (Ordinal deux<3))
                      else
                       if j == 1
                       then point2R2 (tm t (Ordinal deux<3))
                       else
                        if nat_of_ord j == 2
                        then
                         point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                         point2R2 (tm t (Ordinal deux<3)) ^+ 2
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
                         (point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal zero<3)) ^+ 2) -
                         k2 *
                         (point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal un<3)) ^+ 2) -
                         k3 *
                         (point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal deux<3)) ^+ 2)
                        else 0)) (Ordinal trois<4) ord0.
rewrite big_ord_recl.
rewrite !mxE !//=.
set cof2' := cofactor
   (\matrix_(i, j) (if i == 0
                    then
                     if j == 0
                     then point2R1 (tm t (Ordinal zero<3))
                     else
                      if j == 1
                      then point2R2 (tm t (Ordinal zero<3))
                      else
                       if nat_of_ord j == 2
                       then
                        point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                        point2R2 (tm t (Ordinal zero<3)) ^+ 2
                       else 1
                    else
                     if i == 1
                     then
                      if j == 0
                      then point2R1 (tm t (Ordinal un<3))
                      else
                       if j == 1
                       then point2R2 (tm t (Ordinal un<3))
                       else
                        if nat_of_ord j == 2
                        then
                         point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                         point2R2 (tm t (Ordinal un<3)) ^+ 2
                        else 1
                     else
                      if nat_of_ord i == 2
                      then
                       if j == 0
                       then point2R1 (tm t (Ordinal deux<3))
                       else
                        if j == 1
                        then point2R2 (tm t (Ordinal deux<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal deux<3)) ^+ 2
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
                          (point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                           point2R2 (tm t (Ordinal zero<3)) ^+ 2) -
                          k2 *
                          (point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                           point2R2 (tm t (Ordinal un<3)) ^+ 2) -
                          k3 *
                          (point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                           point2R2 (tm t (Ordinal deux<3)) ^+ 2)
                         else 0)) (Ordinal trois<4) 
   (lift ord0 ord0).
rewrite big_ord_recl.
rewrite !mxE !//=.
set cof3' := cofactor
    (\matrix_(i, j) (if i == 0
                     then
                      if j == 0
                      then point2R1 (tm t (Ordinal zero<3))
                      else
                       if j == 1
                       then point2R2 (tm t (Ordinal zero<3))
                       else
                        if nat_of_ord j == 2
                        then
                         point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                         point2R2 (tm t (Ordinal zero<3)) ^+ 2
                        else 1
                     else
                      if i == 1
                      then
                       if j == 0
                       then point2R1 (tm t (Ordinal un<3))
                       else
                        if j == 1
                        then point2R2 (tm t (Ordinal un<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal un<3)) ^+ 2
                         else 1
                      else
                       if nat_of_ord i == 2
                       then
                        if j == 0
                        then point2R1 (tm t (Ordinal deux<3))
                        else
                         if j == 1
                         then point2R2 (tm t (Ordinal deux<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                           point2R2 (tm t (Ordinal deux<3)) ^+ 2
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
                           (point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                            point2R2 (tm t (Ordinal zero<3)) ^+ 2) -
                           k2 *
                           (point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                            point2R2 (tm t (Ordinal un<3)) ^+ 2) -
                           k3 *
                           (point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                            point2R2 (tm t (Ordinal deux<3)) ^+ 2)
                          else 0)) (Ordinal trois<4)
    (lift ord0 (lift ord0 ord0)).

rewrite big_ord_recl.
rewrite !mxE !//=.
set cof4' :=  cofactor
     (\matrix_(i, j) (if i == 0
                      then
                       if j == 0
                       then point2R1 (tm t (Ordinal zero<3))
                       else
                        if j == 1
                        then point2R2 (tm t (Ordinal zero<3))
                        else
                         if nat_of_ord j == 2
                         then
                          point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                          point2R2 (tm t (Ordinal zero<3)) ^+ 2
                         else 1
                      else
                       if i == 1
                       then
                        if j == 0
                        then point2R1 (tm t (Ordinal un<3))
                        else
                         if j == 1
                         then point2R2 (tm t (Ordinal un<3))
                         else
                          if nat_of_ord j == 2
                          then
                           point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                           point2R2 (tm t (Ordinal un<3)) ^+ 2
                          else 1
                       else
                        if nat_of_ord i == 2
                        then
                         if j == 0
                         then point2R1 (tm t (Ordinal deux<3))
                         else
                          if j == 1
                          then point2R2 (tm t (Ordinal deux<3))
                          else
                           if nat_of_ord j == 2
                           then
                            point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                            point2R2 (tm t (Ordinal deux<3)) ^+ 2
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
                            (point2R1 (tm t (Ordinal zero<3)) ^+ 2 +
                             point2R2 (tm t (Ordinal zero<3)) ^+ 2) -
                            k2 *
                            (point2R1 (tm t (Ordinal un<3)) ^+ 2 +
                             point2R2 (tm t (Ordinal un<3)) ^+ 2) -
                            k3 *
                            (point2R1 (tm t (Ordinal deux<3)) ^+ 2 +
                             point2R2 (tm t (Ordinal deux<3)) ^+ 2)
                           else 0)) (Ordinal trois<4)
     (lift ord0 (lift ord0 (lift ord0 ord0))).
rewrite big_ord0.

rewrite /cof3'.
rewrite /cofactor.
rewrite expand_det33 !mxE !//=.

rewrite !mulN1r !addr0 !//=.
rewrite !expr2 !//=.
rewrite !exprD !expr1 !expr0 !//= !mulr1 !//= .
rewrite !mulN1r !//=.
rewrite ?mul1r.
rewrite !mul0l !plus0l !plus0r.



rewrite H1 H2.
  set a := point2R1 (tm t (Ordinal zero<3)).
  set b := point2R2 (tm t (Ordinal zero<3)).
  set c := point2R1 (tm t (Ordinal un<3)).
  set d := point2R2 (tm t (Ordinal un<3)).
  set e := point2R1 (tm t (Ordinal deux<3)).
  set f := point2R2 (tm t (Ordinal deux<3)).
  set g := point2R1 p.
  set h := point2R2 p.
have infok1: k1 = 1 - k2 - k3.
  rewrite -(eqP H3).  simpl in k1. prefield; ring.
rewrite infok1.
prefield.
ring.



rewrite [X in Num.lt 0 X == true]hyp.
rewrite (expand_det_row _ (Ordinal (trois<4))).
rewrite big_ord_recl.
rewrite !mxE !//=.
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
rewrite big_ord_recl.
rewrite !mxE !//=.
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
rewrite big_ord_recl.
rewrite !mxE !//=.
rewrite /cofactor.
rewrite expand_det33 !mxE !//=.
rewrite big_ord_recl.
rewrite big_ord0.
rewrite !mxE !//=.
rewrite expand_det33 !mxE !//=.

move:toriented.
rewrite /leftpoint.
rewrite expand_det33 !mxE !//=.

rewrite !mulN1r !addr0 !//=.
rewrite !expr2 !//=.
rewrite !exprD !expr1 !expr0 !//= !mulr1 !//= .
rewrite !mulN1r !//=.
About mul1l.
rewrite !mul1l.

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
  rewrite !expr2 !//=.
  rewrite !mul0l !plus0l !plus0r.
  prefield.
  ring.
rewrite devpt.
Check pmulr_llt0.
Search _ (Num.lt _ (_*_)).
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


About ltr_oppr.
rewrite ltr_oppr oppr0.
rewrite H1 H2 !//=.

rewrite hypk1.

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
rewrite  hypk2.
rewrite -{2}[1]plus0r.
Search _ (Num.lt (_+_) (_+_)).
rewrite !ltr_subl_addr.
rewrite -{1}[1]plus0r.
rewrite -{1}[1]plus0r.
change (Num.lt ((1 + 0) + 0) ((1 + 0) + k3 + k1)).
About ltr_add2l.
set z:= 1+0.
rewrite -[z]plus0r.
About ltr_add2l.
Check (ltr_add2l z 0 (0+k3+k1)).
rewrite (_ : z+0+k3+k1 = z+(0+k3+k1)); last first.
  prefield; ring.
rewrite (ltr_add2l z 0 (0+k3+k1)).
rewrite plus0l.
Search _ (Num.lt _ (_+_)).
apply: Num.Internals.addr_gt0.
apply: H6.
apply: H4.

have: k3<1.
rewrite  hypk3.
rewrite -{2}[1]plus0r.
Search _ (Num.lt (_+_) (_+_)).
rewrite !ltr_subl_addr.
rewrite -{1}[1]plus0r.
rewrite -{1}[1]plus0r.
change (Num.lt ((1 + 0) + 0) ((1 + 0) + k2 + k1)).
About ltr_add2l.
set z:= 1+0.
rewrite -[z]plus0r.
About ltr_add2l.
Check (ltr_add2l z 0 (0+k2+k1)).
rewrite (_ : z+0+k2+k1 = z+(0+k2+k1)); last first.
  prefield; ring.
rewrite (ltr_add2l z 0 (0+k2+k1)).
rewrite plus0l.
Search _ (Num.lt _ (_+_)).
apply: Num.Internals.addr_gt0.
apply: H5.
apply: H4.

have: k1<1.
rewrite  hypk1.
rewrite -{2}[1]plus0r.
Search _ (Num.lt (_+_) (_+_)).
rewrite !ltr_subl_addr.
rewrite -{1}[1]plus0r.
rewrite -{1}[1]plus0r.
change (Num.lt ((1 + 0) + 0) ((1 + 0) + k3 + k2)).
About ltr_add2l.
set z:= 1+0.
rewrite -[z]plus0r.
About ltr_add2l.
Check (ltr_add2l z 0 (0+k3+k2)).
rewrite (_ : z+0+k3+k2 = z+(0+k3+k2)); last first.
  prefield; ring.
rewrite (ltr_add2l z 0 (0+k3+k2)).
rewrite plus0l.
Search _ (Num.lt _ (_+_)).
apply: Num.Internals.addr_gt0.
apply: H6.
apply: H5.

move=> hypk1inf1.
move=> hypk2inf1.
move=> hypk3inf1.

Search _ (Num.lt (_-_) 0).
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
  rewrite /fJensen.
  rewrite !expr2 !//=.
  prefield; ring.
move=> hypoJensen.
have : (k2 * (c ^+ 2 + d ^+ 2) + k3 * (e ^+ 2 + f ^+ 2) 
          = k1*fJensen x1 + k2*fJensen x2 + k3*fJensen x3).
  rewrite /fJensen.
  rewrite !expr2 !//=.
  prefield; ring.
move=>hypo2Jensen.

rewrite hypoJensen.
rewrite hypo2Jensen.


move/eqP:H3.
move=> H3.

About Jensen_inequality.
(* Transformer les k1+k2+k3 en \sum *)
set x:= [::(x1.1, x1.2) ; (x2.1, x2.2) ; (x3.1, x3.2)].
move:H3.
set k := [::k1;k2;k3].
rewrite (_ : (k1 + k2 + k3 = 1) = (\sum_(i<3) k`_i = 1)); last first.
  rewrite !big_ord_recr !//=.
  rewrite big_ord0.
  rewrite plus0l.
  by [].
move=> H3.
rewrite (_ : k1 * x1.1 + k2 * x2.1 + k3 * x3.1 = \sum_(i<3) k`_i *(x`_i).1)
              ; last first.
  rewrite !big_ord_recr !//=.
  rewrite big_ord0.
  rewrite !mul0r !plus0l.
  by reflexivity.
rewrite (_ : k1 * x1.2 + k2 * x2.2 + k3 * x3.2 = \sum_(i<3) k`_i *(x`_i).2)
              ; last first.
  rewrite !big_ord_recr !//=.
  rewrite big_ord0.
  rewrite !mul0r !plus0l.
  by reflexivity.
rewrite (_ : k1 * fJensen x1 + k2 * fJensen x2 + k3 * fJensen x3
               = \sum_(i<3) k`_i *fJensen (x`_i))
              ; last first.
  rewrite !big_ord_recr !//=.
  rewrite big_ord0.
  rewrite !mul0r !plus0l.
  by reflexivity.
About Jensen_inequality.


have test:  (Num.lt 0 k1 && Num.lt 0 k2 && Num.lt 0 k3) 
                = [forall (i:'I_3|true), (Num.lt 0 k`_((nat_of_ord) i))].
  rewrite -big_andE.
  rewrite !big_ord_recr !//=.
  rewrite big_ord0.
  rewrite !//=.

have : Num.lt 0 k1 && Num.lt 0 k2 && Num.lt 0 k3.
  by rewrite H4 H5 H6.
rewrite test.

(* Si besoin est de prouver que x1 x2 et x3 sont distincts le rajouter en 
  Hypothesis *)
move=> HH.
apply (@Jensen_inequality 3 _ fJensen_convex _ x H3 (ltnSn 2) HH).
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
