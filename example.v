Require Import Arith.
Require Import EqNat.
Require Import Ring.



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

Require Import Structure_de_donnees_3.

Section on_map.

Open Scope ring_scope.

Variable P : finType.

Definition T := T P.

Check trianglemap.

Definition trianglemap := trianglemap P.

Variable default_triangle : point ^ 3.

Hypothesis leftpoint_default :
  (leftpoint (default_triangle (inZp 0))
            (default_triangle (inZp 1))(default_triangle (inZp 2)) > 0)%R.

Definition graph := T -> seq T.

Definition pointmap := pointmap R P.

Definition oriented (t : T) (tm :trianglemap) := 
  leftpoint (tm t (inZp 0)) (tm t (inZp 1)) (tm t (inZp 2)) > 0.

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

Lemma point2indext1t2_correct tm p t t1 t2 :
    pt_in_triangle tm p t -> (t == t1) || (t == t2) ->
    tm t (point2indext1t2 p t1 t2 tm) = p.
Proof.
(* A faire par wassim. *)
Admitted.

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
