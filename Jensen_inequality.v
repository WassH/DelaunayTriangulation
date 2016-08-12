(*=====================================================
=======================================================
JUNE 2016 - AUGUST 2016

AUTHOR : Wassim Haffaf.


Preuve de l'inégalité de Jensen large et stricte dans le
cas général à n éléments.
=======================================================
=======================================================*)



Require Import Arith.
Require Import EqNat.
Require Import Ring.
Require Import Bool.
Require Coq.Init.Nat.
Require Import ZArith.
Require Import Field.




(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq fintype.
From mathcomp Require Import finset zmodp matrix bigop ssralg matrix ssrnum.
From mathcomp Require Import finmap seq ssrfun finfun matrix ssrnum ssrfun.
From mathcomp Require Import bigop ssralg finset fingroup zmodp poly fingraph.
From mathcomp Require Import tuple choice path rat.
(* -------------------------------------------------------------------- *)

Add LoadPath "/Users/haffaf/Desktop/Stage_INRIA/DelaunayTriangulation".
Require Import field_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Open Scope ring_scope.

Require Import determinant_complements.

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

Section Jensen_inequality.

Lemma mul0l (n :rat_Ring) : 0*n = 0.
Proof.
prefield.
rat_field.
Qed.

Lemma mul0r (n :rat_Ring) : n*0 = 0.
Proof.
prefield.
rat_field.
Qed.


Lemma mul1l (n :rat_Ring) : 1*n = n.
Proof.
prefield.
rat_field.
Qed.

Lemma mul1r (n :rat_Ring) : n*1 = n.
Proof.
prefield.
rat_field.
Qed.

Lemma plus0l (n :rat_Ring) : 0+n = n.
Proof.
prefield.
rat_field.
Qed.


Lemma plus0r (n :rat_Ring) : n+0 = n.
Proof.
prefield.
rat_field.
Qed.

Lemma fois_div (n1 n2: rat_Ring) : n2 <>0 -> n1 *n2/n2 = n1.
Proof.
move=> hypn2.
prefield.
by rat_field.
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
rewrite ltnS.
rewrite !//=.
move=> hyp2.
rewrite hyp hyp2.
by [].
Qed.


Definition convex_fun (f : rat -> rat) :=
 forall (k:rat), forall (x:rat), forall (y:rat), (0<=k) -> (k<=1) 
          -> 
         f (k*x + (1-k)*y) 
                  <= k*(f x) + (1-k)* (f y).

Definition convex_strict_fun (f : rat -> rat) :=
 forall (k:rat), forall (x:rat), forall (y:rat), (0<k) -> (k<1) 
          -> (x != y) ->
         f (k*x + (1-k)*y) 
                  < k*(f x) + (1-k)* (f y).

Lemma convex_strict_implies_convex (f : rat -> rat) :
  convex_strict_fun f -> convex_fun f.
Proof.
rewrite /convex_strict_fun /convex_fun.
move=> H k x y hypok0 hypok1.
case hypok0lt: (k>0).
  case hypok1lt : (k<1).
    case ex : (~~ (x == y)).
      move: (H k x y hypok0lt hypok1lt ex).
      rewrite ltr_def.
      move/andP=> hypo.
      move:hypo.
      move=> [hypo1 hypo2].
      by apply: hypo2.
    move/negbT : ex.
    move/negPn=> ex1.
    move:ex1.
    move/eqP=> ex1.
    rewrite ex1.
    have info3 : (k * y + (1 - k) * y = y).
      rat_field.
    have info5 : ((k * f (y) + (1 - k) * f (y) = f (y))).
      rat_field.
    rewrite info3 info5.
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
  have tmp1 : (1 * x + (1 - 1) * y = x).
    rat_field.
  have tmp3 : (1 * f x + (1 - 1) * f y = f x).
    rat_field.
  rewrite tmp1 tmp3.
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
have tmp1 : (0 * x + (1 - 0) * y = y).
  rat_field.
have tmp3 : (0 * f x + (1 - 0) * f y = f y).
  rat_field.
rewrite tmp1 tmp3.
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

Lemma Jensen_inequality (n:nat)(f : rat -> rat) 
              (f_is_convex : convex_fun f)
          (x :seq (rat)) (nsup1 : (n>1)%nat ) :
  forall k:seq rat,(\sum_(i<n) (k`_((nat_of_ord) i)) = 1)->
      [forall (i:'I_n|true), (Num.le 0 k`_((nat_of_ord) i))]
  -> f (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)))
            <= \sum_(i<n) (k`_((nat_of_ord) i))
                    *(f ((x`_((nat_of_ord) i)))).
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
     (\sum_(i < n.+1) k`_i * (x`_i) + k`_n.+1 * (x`_n.+1)))
  (\sum_(i < n.+1) k`_i * f ((x`_i)) +
   k`_n.+1 * f ((x`_n.+1)))).
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
     (\sum_(i < n.+1) k`_i * (x`_i) + k`_n.+1 * (x`_n.+1)))
  (\sum_(i < n.+1) k`_i * f ((x`_i)) +
   k`_n.+1 * f ((x`_n.+1)))).
  move/eqP: sum_egal_0.
  move=> sum_egal_0.
  rewrite sum_egal_0 plus0l.
  move=> dernier_egal_1.
  rewrite dernier_egal_1 !mul1l.
  have intel : (\sum_(i < n.+1) k`_i * (x`_i)
                          = \sum_(i < n.+1) 0 * (x`_i)).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> k`_i * (x`_i) = 0 * (x`_i)).
    move/eqP => intel_tmp.
    rewrite intel_tmp.
    rat_field.
  rewrite intel.
  have intel2 : (\sum_(i < n.+1) 0 * (x`_i)
                          = \sum_(i < n.+1) 0).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> 0 * (x`_i) = 0 ).
    move/eqP => intel2_tmp.
    rat_field.
  rewrite intel2 sumr_const.
  
  have intel3 : (\sum_(i < n.+1) k`_i * (x`_i)
                          = \sum_(i < n.+1) 0 * (x`_i)).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> k`_i * (x`_i) = 0 * (x`_i)).
    move/eqP => intel_tmp.
    rewrite intel_tmp.
    rat_field.
  have intel4 : (\sum_(i < n.+1) 0 * (x`_i)
                          = \sum_(i < n.+1) 0).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> 0 * (x`_i) = 0 ).
    move/eqP => intel2_tmp.
    rat_field.

  have intel5 : (\sum_(i < n.+1) k`_i * f ((x`_i))
                          = \sum_(i < n.+1) 0 * f ((x`_i))).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> k`_i * f ((x`_i)) 
                          = 0 * f ((x`_i))).
    move/eqP => intel_tmp.
    rewrite intel_tmp.
    rat_field.
  rewrite intel5.
  have intel6 : (\sum_(i < n.+1) 0 * f ((x`_i))
                          = \sum_(i < n.+1) 0).
    apply: eq_bigr.
    move=> i tmp.
    move/forallP : info.
    move=> info.
    move: (info i).
    change ((k`_i == 0%Q) -> 0 * f ((x`_i)) = 0 ).
    move/eqP => intel2_tmp.
    rat_field.
  rewrite intel6 sumr_const -mulr_natr !mul0l !plus0l.
  by [].

(* Ici on est toujours dans le premier cas où ns1 : n>1 est vrai *)

(* Cas où lambda est différent de 0 *)

set x1 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)))/lambda.
  rewrite big_ord_recr !//= big_ord_recr !//=.
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i))
                   = x1 * lambda);last first.
    rewrite /x1.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div mul1r [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].

  (* ....................................... *)

(* Cas où lambda est différent de 0, on applique donc l'inégalité de convexité 
   large et l'hypothèse de récurrence *)
have convex_large : (Num.le (f (x1 * lambda + k`_n * (x`_n)))
                              (lambda* f(x1) + k`_n * f ((x`_n)))).
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
      


          have toto: k`_n = 1 - lambda.
          rewrite /lambda.
          Search _ (_ = _  -> _+_ =_+_).
          rewrite -somme_egal_1 big_ord_recr !//=.
          set sum_n := \sum_(i < n) k`_i.
          simpl in sum_n.
          prefield. ring.
        set x_f := (x1).
        set y_f := ((x`_n)).
        simpl in x_f, y_f.

        rewrite (_: x_f * lambda = lambda * x_f); last first.
          rat_field.

        move: lambda_pos.
        rewrite toto.
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
          rewrite toto.
          simpl in lambda.
          rat_field.
        move: intel.
        move=> intel intel2.
        apply : (f_is_convex).
          by [].
        by [].


      have autre_ing : f (x1)
            <= \sum_(i<n) (k`_((nat_of_ord) i))/lambda
                    *(f ((x`_((nat_of_ord) i)))).
       

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
          rat_field.

        set F1 := fun i:'I_n => k`_i / lambda.
        set F2 := fun i:'I_n => k`_i * (1 / lambda).
        by move/eqP : info.
        Locate mulr_suml.
        rewrite mulr_suml.
        set F1 := fun i:'I_n => k`_i / lambda.
        set F2 := fun i:'I_n => k`_i * (1 / lambda).
        apply (eq_bigr F2).
        move=> i tmp.
        rewrite /F2.
        rat_field.

        rewrite /x1.
        by move/eqP : info.
        rewrite (_ : f
     ((\sum_(i < n) k`_i * (x`_i)) / lambda) = f
                                     ((\sum_(i < n) k`_i * (x`_i))* (1 / lambda)));
last first.
  Search _ (_*_/_).
  Search _ (_/1).
  rewrite -[X in _ = f
  (X * (1 / lambda))]divr1.
  About divr1.
(* 
  rewrite -[X in _ = f (_ * (1 / lambda))]divr1. *)
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
  rat_field.
by move/eqP: info.
rewrite mulr_suml.

set F1 := fun i:'I_n => k`_i / lambda.
set F2 := fun i:'I_n => k`_i * (1 / lambda).

apply (eq_bigr F2).
move=> i tmp.
rewrite /F2.
rat_field.
by move/eqP:info.

        rewrite (_ : (\sum_(i < n) k`_i * (x`_i) *(1 / lambda)
                        = (\sum_(i < n) (k`_i/lambda) *  (x`_i)))); last first.
          apply: eq_bigr.
          move=> i inutile.
          rat_field.
          by move/eqP:info.

        set F1 := fun i => k`_i / lambda.
            set k_sur_lam := mkseq F1 n.
            move:info11.
            rewrite (_ : \sum_(i < n) k`_i / lambda = \sum_(i < n) k_sur_lam`_i); last first.
              apply eq_bigr.
              move=> i2 tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              About nth_mkseq.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

            rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i)
                         = \sum_(i < n) k_sur_lam`_i * (x`_i)); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              About nth_mkseq.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].

(*             rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i)
                         = \sum_(i < n) k_sur_lam`_i * (x`_i)); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              About nth_mkseq.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by []. *)

            rewrite (_ : (\sum_(i < n) k`_i / lambda * f ((x`_i))
                    = (\sum_(i < n) k_sur_lam`_i * f ((x`_i))))); last first.
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
have autre_ing2 :  (Num.le (lambda * f (x1) + k`_n * f ((x`_n)))
                (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))
                      + k`_n * f ((x`_n)))).
  Search _ (Num.lt (_+_) (_+_)) (Num.lt _ _).
  set term1 := lambda * f (x1).
  set term2 := (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))).
  set term3 := (k`_n * f ((x`_n))).
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

rewrite (_ : lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))
                = (\sum_(i < n) k`_i * f ((x`_i)))).
  move=> autre_ing2.
apply (ler_trans convex_large autre_ing2).


rewrite mulr_sumr.
  set F1 := fun i:'I_n => lambda * (k`_i / lambda * f ((x`_i))) .
  set F2 := fun i:'I_n => k`_i * f ((x`_i)).
  apply: eq_bigr.
  move=> i tmp.
  set tmp1 := f ((x`_i)).
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
     (\sum_(i:'I_1) (k`_i* (x`_i)) + (k`_1 * (x`_1)))   )
  (\sum_(i < 2) k`_i * f ((x`_i)))).
rewrite !big_ord_recr !big_ord0.
change (Num.le
  (f
     (0 + (k`_0 * (x`_0)) + (k`_1 * (x`_1))  )   )
  (0 + k`_0 * f ((x`_0)) + k`_1 * f ((x`_1)))).

rewrite !plus0l.
rewrite info1.


move: hypok.
rewrite -big_andE.
rewrite !big_ord_recr !big_ord0.
change (Num.le 0 k`_0 && Num.le 0 k`_1 -> Num.le
  (f
     (k`_0 * (x`_0) + (1 - k`_0) * (x`_1)))
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


Lemma Jensen_inequality_strict (n:nat) (f : rat -> rat) 
              (f_is_convex : convex_strict_fun f)
          (x :seq (rat)) (nsup1 : (n>1)%nat )
             :
   forall k:seq rat,(\sum_(i<n) (k`_((nat_of_ord) i)) = 1)->
      [forall (i:'I_n|true), (Num.lt 0 k`_((nat_of_ord) i))] 
    -> [exists (i:'I_n|true), [exists (j:'I_n|true),
                      ((x`_i) != (x`_j))]]
  -> f (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)))
            < \sum_(i<n) (k`_((nat_of_ord) i))
                    *(f ((x`_((nat_of_ord) i)))).
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

  set x1 := (\sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i)))/lambda.
  rewrite big_ord_recr !//=.
  rewrite big_ord_recr !//=.
  rewrite  (_: \sum_(i<n) (k`_((nat_of_ord) i))*(x`_((nat_of_ord) i))
                   = x1 * lambda);last first.
    rewrite /x1.
    rewrite {2}(_ : lambda = lambda/1); last first.
      by rewrite divr1.
    rewrite mulf_div mul1r [RHS]fois_div.
      reflexivity.
    move/eqP: info.
    by [].
  (* ....................................... *)

    case x1_xn_egal: ((x1 == (x`_n)) ); last first.
      (* Dans le bout de code qui suit on peut appliquer hypconvex *)


    have : (Num.lt (f (x1 * lambda + k`_n * (x`_n)))
                  (lambda*(f (x1)) + k`_n* (f ((x`_n))))).
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
    set x_f := (x1).
    set y_f := ((x`_n)).
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
        rat_field.
      rewrite info5.
      rewrite -(ltr_add2r (k`_n -1) (1 - k`_n) 1).
      have w: (1 - k`_n + (k`_n - 1)) = 0.
        rat_field.
      rewrite w.
      have ww : (1 + (k`_n - 1)) = k`_n.
        rat_field.
      rewrite ww {ww}.
      rewrite {w}.
      move/forallP : hypok.
      move=> hypok.
      set n_ord := Ordinal (ltnSn n).
      change (true ==>Num.lt 0 k`_(n_ord) ).
      apply: hypok.
    case info_dif: (~~ (x_f == y_f) ).
      rewrite (_ : x_f * lambda =  lambda* x_f ); last first.
        rat_field.
      apply (@hypconvex lambda x_f y_f info3 info4 info_dif).
    



(* Dans le bout de code qui suit on va appliquer hypconvex *)

rewrite (_ : x_f * lambda = lambda * x_f); last first.
  rat_field.

apply: hypconvex.
  by [].
by [].
rewrite /x_f !//=.
move/negPf: x1_xn_egal.
set b1 := (x1 == (x`_n)) .
case infob1 : b1.
    by [].
  by [].


(* A cet étape, on a l'inégalité de convexité stricte *)
(* Il ne reste alors qu'à appliquer Jensen large à f(x1, x2) *)


move=> info_strict_conv.
have autre_ing : f (x1)
            <= \sum_(i<n) (k`_((nat_of_ord) i))/lambda
                    *(f ((x`_((nat_of_ord) i)) )).
   have hypokle : [forall (i :'I_(S n)| true), Num.le 0 (k`_((nat_of_ord) i))].
     apply: lt_implies_le hypok.
rewrite /x1 .
rewrite (_ : f
     ((\sum_(i < n) k`_i * (x`_i)) / lambda) = f
                                     ((\sum_(i < n) k`_i * (x`_i))* (1 / lambda)));
last first.
  rewrite -[X in _ = f
  (X * (1 / lambda))]divr1.
(*   rewrite -[X in _ =
    f ((\sum_(i < n) k`_i * x`_i) * (1 / lambda))]divr1.
  rewrite -[X in _ = f
  (_ * (1 / lambda),
  (X * (1 / lambda)))]divr1. *)
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
  rat_field.
  by move/eqP: info.
rewrite mulr_suml.

set F1 := fun i:'I_n => k`_i / lambda.
set F2 := fun i:'I_n => k`_i * (1 / lambda).

apply (eq_bigr F2).
move=> i tmp.
rewrite /F2.
rat_field.
by move/eqP:info.


rewrite (_ : (\sum_(i < n) k`_i * (x`_i) *(1 / lambda)
                = (\sum_(i < n) (k`_i/lambda) *  (x`_i)))); last first.
  apply: eq_bigr.
  move=> i inutile.
  rat_field.
  by move/eqP:info.

set F1 := fun i => k`_i / lambda.
    set k_sur_lam := mkseq F1 n.
    move:info1.
    rewrite (_ : \sum_(i < n) k`_i / lambda = \sum_(i < n) k_sur_lam`_i); last first.
      apply eq_bigr.
      move=> i2 tmp.
      rewrite /k_sur_lam.
      simpl in F1.
      rewrite (nth_mkseq ) /F1.
      reflexivity.
      by [].


    rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i)
                 = \sum_(i < n) k_sur_lam`_i * (x`_i)); last first.
      apply eq_bigr.
      move=> i tmp.
      rewrite /k_sur_lam.
      simpl in F1.
      rewrite (nth_mkseq ) /F1.
      reflexivity.
      by [].


    rewrite (_ : (\sum_(i < n) k`_i / lambda * f ((x`_i))
            = (\sum_(i < n) k_sur_lam`_i * f ((x`_i))))); last first.
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
move: somme_egal_1 nsup1 IHn ex lambda info x1 x1_xn_egal 
      info_strict_conv F1 k_sur_lam hypok ns1  i 
     hypokle.
        case : n.
          by [].
move=> n somme_egal_1 nsup1 IHn ex lambda info x1  x1_xn_egal 
      info_strict_conv F1 k_sur_lam hypok ns1  i  hypokle
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

move=> info_k_sur_lam.
apply (@Jensen_inequality n f (convex_strict_implies_convex f_is_convex) 
                x ns1 k_sur_lam info_k_sur_lam (lt_implies_le hypokN)).

(* On va combiner info_strict_conv et autre_ing pour prouver le but *)
have autre_ing2 :  (Num.le (lambda * f (x1) + k`_n * f ((x`_n)))
                (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))
                      + k`_n * f ((x`_n)))).
  set term1 := lambda * f (x1).
  set term2 := (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))).
  set term3 := (k`_n * f ((x`_n))).
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
rewrite (_ : lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))
                = (\sum_(i < n) k`_i * f ((x`_i)))).
  move=> autre_ing2.
  apply: (ltr_le_trans info_strict_conv autre_ing2).
  rewrite mulr_sumr.
  set F1 := fun i:'I_n => lambda * (k`_i / lambda * f ((x`_i))) .
  set F2 := fun i:'I_n => k`_i * f ((x`_i)).
  apply: eq_bigr.
  move=> i tmp.
  set tmp1 := f ((x`_i)).
  set tmp2 :=lambda.
  set tmp3 := k`_i.
  simpl in tmp2, tmp3.
  prefield. field.
  rewrite /tmp2.
  have lambda_pos: lambda>0.
    rewrite /lambda.
    move: nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          autre_ing x1_xn_egal  info_strict_conv tmp2 ns1 F2 i tmp1 tmp3.
    case : n.
      by [].
    move=> n  nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          autre_ing x1_xn_egal  info_strict_conv tmp2 ns1 F2 i tmp1 tmp3.
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
        ~~ ((x`_i) == (x`_j)) ]].
    have convex_large : (Num.le (f (x1 * lambda + k`_n * (x`_n)))
                              (lambda* f(x1) + k`_n * f ((x`_n)))).
      have lambda_pos: lambda>0.
        rewrite /lambda.
        move: nsup1 IHn somme_egal_1 hypok ex lambda info x1 
              x1_xn_egal ns1 xi_dif_xj_n.
        case : n.
          by [].
        move=> n nsup1 IHn somme_egal_1 hypok ex lambda info x1 
              x1_xn_egal ns1 xi_dif_xj_n.
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


          have toto: k`_n = 1 - lambda.
          rewrite /lambda -somme_egal_1 big_ord_recr !//=.
          set sum_n := \sum_(i < n) k`_i.
          simpl in sum_n.
          prefield. ring.
        set x_f := (x1).
        set y_f := ((x`_n)).
        simpl in x_f, y_f.

        rewrite (_: x_f * lambda = lambda * x_f); last first.
          rat_field.

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
          rewrite toto.
          simpl in lambda.
          rat_field.
        rewrite toto /convex_fun.
        apply (convex_strict_implies_convex f_is_convex) .
          by [].
        by [].

      have autre_ing : f (x1)
            < \sum_(i<n) (k`_((nat_of_ord) i))/lambda
                    *(f ((x`_((nat_of_ord) i)))).
        have hypokle : [forall (i :'I_(S n)| true), Num.le 0 (k`_((nat_of_ord) i))].
          apply: lt_implies_le hypok.
        rewrite /x1.
        rewrite (_ : f
             ((\sum_(i < n) k`_i * (x`_i)) / lambda) = f
                                             ((\sum_(i < n) k`_i * (x`_i))* (1 / lambda)));
        last first.
          rewrite -[X in _ = f
                (X * (1 / lambda))]divr1.
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
          rat_field.
          by move/eqP: info.
        rewrite mulr_suml.

        set F1 := fun i:'I_n => k`_i / lambda.
        set F2 := fun i:'I_n => k`_i * (1 / lambda).

        apply (eq_bigr F2).
        move=> i tmp.
        rewrite /F2.
        rat_field.
        by move/eqP:info.

        rewrite (_ : (\sum_(i < n) k`_i * (x`_i) *(1 / lambda)
                        = (\sum_(i < n) (k`_i/lambda) *  (x`_i)))); last first.
          apply: eq_bigr.
          move=> i inutile.
          rat_field.
          by move/eqP:info.

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

            rewrite (_ : \sum_(i < n) k`_i / lambda * (x`_i)
                         = \sum_(i < n) k_sur_lam`_i * (x`_i)); last first.
              apply eq_bigr.
              move=> i tmp.
              rewrite /k_sur_lam.
              simpl in F1.
              rewrite (nth_mkseq ) /F1.
              reflexivity.
              by [].



            rewrite (_ : (\sum_(i < n) k`_i / lambda * f ((x`_i))
                    = (\sum_(i < n) k_sur_lam`_i * f ((x`_i))))); last first.
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
move: somme_egal_1 nsup1 ex lambda info x1  x1_xn_egal 
       hypok ns1 xi_dif_xj_n i
      convex_large F1  k_sur_lam sum_k_sur_lam hypokle.
        case : n.
          by [].
move=> n somme_egal_1 nsup1 ex lambda info x1 x1_xn_egal 
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
have autre_ing2 :  (Num.lt (lambda * f (x1) + k`_n * f ((x`_n)))
                (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))
                      + k`_n * f ((x`_n)))).
  set term1 := lambda * f (x1).
  set term2 := (lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))).
  set term3 := (k`_n * f ((x`_n))).
  simpl in term1, term2, term3.
  rewrite ltr_add2r /term1 /term2.
  rewrite -subr_gt0 -mulrBr.
  apply: mulr_gt0.



have lambda_pos : lambda>0.
        rewrite /lambda.
move: somme_egal_1 nsup1 ex lambda info x1  x1_xn_egal 
       hypok ns1 xi_dif_xj_n 
      convex_large autre_ing term1 term2 term3 IHn.
        case : n.
          by [].
move=> n somme_egal_1 nsup1 ex lambda info x1  x1_xn_egal 
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

rewrite (_ : lambda * (\sum_(i < n) k`_i / lambda * f ((x`_i)))
                = (\sum_(i < n) k`_i * f ((x`_i)))).
  move=> autre_ing2.
apply (ler_lt_trans convex_large autre_ing2).


rewrite mulr_sumr.
  set F1 := fun i:'I_n => lambda * (k`_i / lambda * f ((x`_i))) .
  set F2 := fun i:'I_n => k`_i * f ((x`_i)).
  apply: eq_bigr.
  move=> i tmp.
  set tmp1 := f ((x`_i)).
  set tmp2 :=lambda.
  set tmp3 := k`_i.
  simpl in tmp2, tmp3.
  prefield. field.
  rewrite /tmp2.
  have lambda_pos: lambda>0.
    rewrite /lambda.
    move: nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
           autre_ing x1_xn_egal  tmp2 ns1 F2 i tmp1 tmp3 convex_large
            xi_dif_xj_n.
    case : n.
      by [].
    move=> n nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
           autre_ing x1_xn_egal  tmp2 ns1 F2 i tmp1 tmp3 convex_large
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
                 ] = false *)


move/negbT: xi_dif_xj_n.

rewrite negb_exists /= => /forallP => fne.

have toto : [forall i: 'I_n, [forall j : 'I_n,
    ((x`_i) == (x`_j)) ]].
apply/forallP => i; move:(fne i); rewrite negb_exists /= => /forallP fnei.
by apply/forallP => j; move:(fnei j); rewrite !negb_involutive.

have tous_meme: ([forall (i:'I_(n)|true), (x`_i) == (x`_0)] 
                      )
      ; last first.





(* Dans le bout de code qui suits on prouve (x1 = (x`_0)) *)
        have hh1: (x1 = (x`_0)).
          rewrite /x1.
          (* rewrite tous_meme1. *)
  set F1 : 'I_n-> rat := fun i => k`_i * (x`_i).
  set F2 : 'I_n-> rat := fun i => k`_i * (x`_0).
  have F1eqF2 : (forall i : 'I_n, true -> F1 i = F2 i).
    move=> i true.
    rewrite /F1 /F2.
    move/forallP : tous_meme.
    move=>tous_meme.

    move: (tous_meme i).
    change (((x`_i) == (x`_0)) ->
      k`_i * (x`_i) = k`_i * (x`_0)).
    set ff := fun x => k`_i * x.
    move/eqP=> hyp1.
    by apply: (congr1 ff).


rewrite (eq_bigr F2 F1eqF2) /F2 -mulr_suml /lambda -/lambda.
prefield ; field.
have lambda_pos: lambda>0.
    rewrite /lambda.
    move: nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x1_xn_egal ns1 F2 F1eqF2 fne toto tous_meme
            .
    case : n.
      by [].
    move=> n nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x1_xn_egal ns1 F2 F1eqF2 fne toto tous_meme
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


(* 
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
          x2 x1_xn_egal ns1 F2 F1eqF2 fne toto tous_meme1 tous_meme2 hh1
            .
    case : n.
      by [].
    move=> n nsup1 IHn somme_egal_1 hypok ex lambda F1 info x1 
          x2 x1_xn_egal ns1 F2 F1eqF2 fne toto tous_meme1 tous_meme2 hh1
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
    by [].   *)

(* Preuve de x`_n == x`_0 *)
move/eqP: x1_xn_egal.
move=> x1_xn_egal.
have infoa : (x`_n) = (x`_0).
  by rewrite -hh1 x1_xn_egal.


(* Dans le bout de code qui suit on montre que ex et xn_meme donne false en 
   hypothèse et donc le but courant est démontré *)
move/existsP:ex.
rewrite !//=.
move=> [x0  ex1].

move/existsP:ex1.
rewrite !//=.
move=> [x3 ex2].


have tous_meme1_Sn: [forall (i:'I_(n.+1) | true), (x`_i) == (x`_0)].
  rewrite -big_andE big_ord_recr.
  apply/andP.
  split.
    rewrite big_andE.
    exact tous_meme.
  change ((x`_n) == (x`_0)).
  move/eqP: infoa => infoa.
  exact : infoa.

move/forallP : tous_meme1_Sn.
move=> tous_meme1_Sn.


move : (tous_meme1_Sn x0).
change ((x`_x0 == x`_0) ->
Num.lt (f (x1 * lambda + k`_n * x`_n))
  (\sum_(i < n) k`_i * f x`_i + k`_n * f x`_n)). 
move=>cont1x0.


move : (tous_meme1_Sn x3).
change ( (x`_x3 == x`_0) ->
Num.lt (f (x1 * lambda + k`_n * x`_n))
  (\sum_(i < n) k`_i * f x`_i + k`_n * f x`_n)).
move=>cont1x3.

move/eqP :cont1x0.
move=>cont1x0.


move/eqP :cont1x3.
move=>cont1x3.


have contra1: ((x`_x0) == (x`_x3)).
  by rewrite cont1x0 cont1x3.

move: ex2.
Search _ (~~_||~~_).
set a1 := (x`_x0).
set b1 := (x`_x3).
simpl in a1, b1.
set bool1 := (a1 == b1).

move : contra1.
rewrite -/bool1.
move=> contra1.
move=> contra2.
have contra: (bool1 && ~~bool1).
  apply/andP.
  split.
    rewrite /bool1.
    by exact contra1.
  by exact: contra2.
move: contra.
rewrite andb_negb_r.
by [].


(* Reste à démontrer le have tous_meme *)
  move/forallP : toto.
  move=> toto.
  have zero_inf_n : (0 < n)%N.
    by apply : ltn_trans (ltnSn 0)  (ns1).
  move: (toto (Ordinal zero_inf_n)).
  change ([forall (j : 'I_n|true),
   ((x`_0) == (x`_j))] ->
      [forall (i : 'I_n | true), (x`_i) == (x`_0)]).
  move=> toto1.
  apply/forallP.
  move=> x0.
  change (((x`_x0) == (x`_0))).
  move/forallP : toto1.
  move=> toto1.
  move: (toto1 x0).
  change (((x`_0) == (x`_x0))  ->
      (x`_x0) == (x`_0)).
  move=> toto1x0.
  move/eqP:toto1x0.
  move=> toto1x0.
  apply/eqP.
  rewrite toto1x0.
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
     (\sum_(i:'I_1) (k`_i* (x`_i)) + (k`_1 * (x`_1))))
  (\sum_(i < 2) k`_i * f ((x`_i)))).
rewrite !big_ord_recr !big_ord0.
change (Num.lt
  (f
     (0 + (k`_0 * (x`_0)) + (k`_1 * (x`_1))  )   )
  (0 + k`_0 * f ((x`_0)) + k`_1 * f ((x`_1)))).

rewrite !plus0l.
rewrite info1.

move: hypok.
rewrite -big_andE !big_ord_recr !big_ord0.
change (Num.lt 0 k`_0 && Num.lt 0 k`_1 -> Num.lt
  (f
     (k`_0 * (x`_0) + (1 - k`_0) * (x`_1)))
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

have ex_utile : ((x`_0) != (x`_1)); last first.
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
  rewrite (_ : (x`_x1) == (x`_x1) = true); last first.
    apply/eqP.
    by reflexivity.
rewrite !//=.

case x0_is0 : (x0 == Ordinal ing0).
  case x1_is1 : (x1 == Ordinal ing1).
    move/eqP : x0_is0.
    move=> x0_is0.
    move/eqP : x1_is1.
    move=> x1_is1.
    change (~~ ((x`_(Ordinal ing0)) == (x`_(Ordinal ing1))) 
              ).
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
  rewrite (_ :(x`_x1) == (x`_x1) = true); last first.
    apply/eqP.
    by reflexivity.
  rewrite (_ : ~~ true = false) ;last first.
    by [].
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
change (~~ ((x`_(1)) == (x`_(0)))
 -> ~~ ((x`_0) == (x`_1)) ).
rewrite (_ : ((x`_1) == (x`_0)) = ((x`_0) == (x`_1))); last first.
  by [].
by [].
Qed.


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



Lemma lt_implies_le2 (r:rat) : Num.lt 0 r -> Num.le 0 r.
Proof.
rewrite lt0r.
move/andP=> H.
move: H.
move=> [H H2].
by [].
Qed.

End Jensen_inequality.