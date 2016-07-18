From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssrnum matrix mxalgebra.

From mathcomp Require Import finmap.

Section ch.

Open Scope fmap_scope.

Variable R : numDomainType.

Definition point := 'rV[R]_2.

Variable oriented : ('rV[R]_2 ^ 3) -> bool.

Definition edge := (point ^ 2)%type.

Definition E := nat.

Definition pre_newname (e : {fset nat}) : {n : nat | n \notin e}.
Proof.
exists (\max_(i : e) val i + 1).
set u := _ + 1; apply/negP => abs; move/negP: (ltnn u); apply.
move: abs; rewrite /u addn1 => abs; rewrite ltnS.
apply: (leq_bigmax [` abs ]%fset).
Qed.

Definition newname (e : {fset nat}) := val (pre_newname e).

Lemma newnameP e : newname e \notin e.
Proof. rewrite /newname; apply: (@valP _ [pred n | n \notin e]). Qed.

(*
Record edge_state := {
  head : point;
  tail : point;
  next : E;
  prev : E
}.

Definition main_state :=
  {fmap E -> edge_state}.

*)

Definition e_hd (e : point ^ 2 * E ^ 2) :=
  nosimpl (fst e (Ordinal ((erefl true) : 0 < 2))).

Definition e_tl (e : point ^ 2 * E ^ 2) :=
  nosimpl (fst e (Ordinal ((erefl true) : 1 < 2))).

Definition nxt (e : point ^ 2 * E ^ 2) :=
  nosimpl (snd e (Ordinal ((erefl true) : 0 < 2))).

Definition prv (e : point ^ 2 * E ^ 2) :=
  nosimpl (snd e (Ordinal ((erefl true) : 1 < 2))).

Definition mk_edge hd tl nxt prv : point ^ 2 * E ^ 2 :=
 nosimpl ([ffun x : 'I_2 => if val x == 0 then hd else tl],
  [ffun x : 'I_2 => if val x == 0 then nxt else prv]).

Definition mk_edgeK e : mk_edge (e_hd e) (e_tl e) (nxt e) (prv e) = e.
Proof.
by case: e => ptf cnf; rewrite /e_hd /e_tl /nxt /prv /mk_edge; congr (_ , _);
  apply/ffunP; move => [[ | [ | x]] px] /=; rewrite ffunE /=;
  try rewrite (bool_irrelevance (erefl true) px).
Qed.

Definition e_hdK a b c d : e_hd (mk_edge a b c d) = a.
Proof.
by rewrite /e_hd /mk_edge ffunE.
Qed.

Definition e_tlK a b c d : e_tl (mk_edge a b c d) = b.
Proof.
by rewrite /e_tl /mk_edge ffunE.
Qed.

Definition nxtK a b c d : nxt (mk_edge a b c d) = c.
Proof.
by rewrite /nxt /mk_edge ffunE.
Qed.

Definition prvK a b c d : prv (mk_edge a b c d) = d.
Proof.
by rewrite /prv /mk_edge ffunE.
Qed.

Definition edgemapprop (s : {fmap E -> point ^ 2 * E ^ 2}) :=
(* [forall (x : {: domf s} | true ) *)
\big[andb/true]_(x : {: domf s})
      ((nxt (s x) \in s) && (prv (s x) \in s)) (* ] *).

Lemma fnxt_aux s (sp : edgemapprop s) (x : {: domf s}) :
  (nxt (s x)) \in domf s.
Proof.
move: sp; rewrite /edgemapprop big_andE; move/forallP => /= sp.
by move/andP: (sp x) => [].
Qed.

Lemma fprv_aux s (sp : edgemapprop s) (x : {: domf s}) :
  (prv (s x)) \in domf s.
Proof.
move: sp; rewrite /edgemapprop big_andE; move/forallP => /= sp.
by move/andP: (sp x) => [].
Qed.

Definition fnxt s (sp : edgemapprop s) (x : domf s) : domf s :=
  nosimpl [` fnxt_aux s sp x ]%fset.

Definition fprv s (sp : edgemapprop s) (x : {: domf s}) : {:domf s} :=
  nosimpl [` fprv_aux s sp x ]%fset.

Lemma prvP s (h : edgemapprop s) : forall (x : {: domf s}), prv (s x) \in s.
Proof.
move: h; rewrite /edgemapprop big_andE; move/forallP => /= h x.
by move/andP: (h x) => [].
Qed.

Lemma nxtP s (h : edgemapprop s) : forall (x : {: domf s}), nxt (s x) \in s.
Proof.
move: h; rewrite /edgemapprop big_andE; move/forallP => /= h x.
by move/andP: (h x) => [].
Qed.

Definition edgemapprop2 s (sp : edgemapprop s) :=
  \big[andb/true]_(i : {: domf s}) ((e_hd (s i) == e_tl (s (fnxt s sp i))) &&
     (fnxt s sp (fprv s sp i) == i) && (fprv s sp (fnxt s sp i) == i)).

Lemma fprvK s sp (sp2 : edgemapprop2 s sp) : cancel (fnxt s sp) (fprv s sp).
Proof.
move => x; apply/eqP; move: sp2.
rewrite /edgemapprop2 big_andE => /forallP /= sp2.
by case/andP: (sp2 x) => /andP [].
Qed.

Lemma fnxtK s sp (sp2 : edgemapprop2 s sp) : cancel (fprv s sp) (fnxt s sp).
Proof.
move => x; apply/eqP; move: sp2.
rewrite /edgemapprop2 big_andE => /forallP /= sp2.
by case/andP: (sp2 x) => /andP [].
Qed.

(* utiliser le theoreme can_inj *)
Lemma fnxt_inj s sp (sp2 : edgemapprop2 s sp) : injective (fnxt _ sp).
Proof.
by intros x y fxy; rewrite -(fprvK _ _ sp2 x) -(fprvK _ _ sp2 y) fxy.
Qed.

Lemma fprv_inj s sp (sp2 : edgemapprop2 s sp) : injective (fprv _ sp).
Proof.
by intros x y fxy; rewrite -(fnxtK _ _ sp2 x) -(fnxtK _ _ sp2 y) fxy.
Qed.

Definition update_nxt s (sp : edgemapprop s) (x : {: domf s}) (y : E) :=
  let xvalues := s x in
  s.[fsval x <- mk_edge (e_hd xvalues) (e_tl xvalues) y (prv xvalues)].

Definition update_prv s (sp : edgemapprop s) (x : {: domf s}) (y : E) :=
  let xvalues := s x in
  s.[fsval x <- mk_edge (e_hd xvalues) (e_tl xvalues) (nxt xvalues) y].

Definition initial (p1 p2 : point) : {fmap E -> point ^ 2 * E ^ 2} :=
  nosimpl [fmap].[0 <- mk_edge p1 p2 1 1].[1 <- mk_edge p2 p1 0 0].
(* TODO : maybe shorter this way. *)
Definition initial2 (p1 p2 : point) : {fmap E -> point ^ 2 * E ^ 2} :=
  [fmap x : [fset 0; 1]%fset =>
     if val x == 0 then mk_edge p1 p2 1 1 else mk_edge p1 p2 0 0].

Lemma initialP (p1 p2 : point) (df : p1 != p2) : edgemapprop (initial p1 p2).
Proof.
have m0 : 0 \in initial p1 p2 by rewrite !inE.
have m1 : 1 \in initial p1 p2 by rewrite !inE.
(* 
have m2 : forall k, k.+2 \notin domf (initial p1 p2).
  by move => k; rewrite !in_fsetE.
*)
rewrite /edgemapprop.
(*
rewrite
  (eq_bigl [pred x | (x == [` m0]%fset) || (x == [` m1 ]%fset)]); last first.
  by case =>  [ [ | [ | x]]  px] //=; case/negP: (m2 x).
*)
(*
rewrite (eq_bigl (fun x => x \in [` m0]%fset :: [` m1 ]%fset :: nil)); last first.
(* At this point the goal contains information that explains me that everything
   is right, but I don't have a clue about how to use it, so I proceed with
   my initial plan. *)
  rewrite /=; move => [ [ | [ | x]] px]; rewrite !inE //=; case/negP: (m2 x).
(* At this point, the goal displays information I did not know how to obtain. but
  gives me another, better way to do it. *)
 exact px.
*)

(* Better way to find all elements : TODO
rewrite big_andE; apply/forallP => x.
have:= valP x; rewrite !inE.
*) 
rewrite (eq_bigl (fun x => val x \in (1 |` (0 |` fset0))%fset));
  last by move => [ [ | [ | x]] P].
have m1' : val [` m1 ]%fset \in (1 |` (0 |` fset0))%fset by [].
rewrite (bigD1 _ m1').
have m0' : (val [` m0 ]%fset \in (1 |` (0 |` fset0))%fset) &&
           ([` m0 ]%fset != [` m1 ]%fset) by rewrite !inE.
rewrite (bigD1 [` m0]%fset  m0') big_pred0 /= ?andbT; last first.
  by move => [ [ | [ | x]] /= _] ; rewrite ?andbF //= !in_fsetE.
(* I think the next proof would be easier if I knew how to write a finfun
  in a more systematic way. *)
set u := initial p1 p2; set v := u.[m0].
 (* TODO  rewrite !ffunE /= nxtK prvK /u /initial !inE. *)
apply/andP; split;
  apply/andP;split;
  try solve [rewrite /e_hd /e_tl /nxt /prv !ffunE //=].
  by rewrite /v /u /initial ffunE FmapE.fmapE nxtK.
by rewrite /v /u /initial ffunE FmapE.fmapE prvK.
Qed.

Lemma initial2P (p1 p2 : point) (h : edgemapprop (initial p1 p2)):
   edgemapprop2 (initial p1 p2) h.
Proof.
rewrite /edgemapprop2.
have m0 : 0 \in initial p1 p2 by rewrite !in_fsetE.
have m1 : 1 \in initial p1 p2 by rewrite !in_fsetE.
rewrite (eq_bigl (fun x => val x \in (1 |` (0 |` fset0))%fset));
  last by move => [ [ | [ | x]] P].
have m1' : val [` m1 ]%fset \in (1 |` (0 |` fset0))%fset by [].
rewrite (bigD1 _ m1') /=.
have m0' : (val [` m0 ]%fset \in (1 |` (0 |` fset0))%fset) &&
           ([` m0 ]%fset != [` m1 ]%fset) by rewrite !inE.
rewrite (bigD1 [` m0]%fset  m0') big_pred0 /= ?andbT; last first.
  by move => [ [ | [ | x]] /= _] ; rewrite ?andbF //= !in_fsetE.
(* Note : FmapE.fmapE devrait probablement etre remonte au niveau
  finmap. *)
apply/andP; split; (apply/andP; split;[apply/andP;split | ]);
 try (by apply/eqP/val_inj; rewrite /fnxt /fprv /initial /= 
       !(FmapE.fmapE, ffunE) /= !(FmapE.fmapE, ffunE, prvK, nxtK)).
  by rewrite !ffunE e_hdK /fnxt /= !ffunE nxtK FmapE.fmapE e_tlK.
by rewrite !ffunE /fnxt /= !(ffunE, FmapE.fmapE, nxtK, e_hdK, e_tlK).
Qed.

(* both pointing_edge and its successor are removed.  A new edge is created
   to connect the tail of pointing_edge and the head of its successor.
   the map we obtain does not satify the invariants anymore *)
(* TODO : remove sp2, not needed in the code. *)
Definition remove_point s
  (sp : edgemapprop s) (sp2 : edgemapprop2 _ sp) 
  (pointing_edge : {: domf s}) : {fmap E -> point ^ 2 * E ^ 2} :=
  let edge_values := s pointing_edge in
  let p1 := e_tl edge_values in
  let p2 := e_hd edge_values in
  let ne := fnxt _ sp pointing_edge in
  let old_prv := fprv _ sp pointing_edge in
  let old_prv_values := s old_prv in
  let old_nxt := fnxt _ sp ne in
  let old_nxt_values := s old_nxt in
  let s1 := s.[\ ([fset (val pointing_edge)] `|` [fset (val ne) ])%fset] in
  let k := newname (domf s1) in
  if old_nxt == old_prv then
     s1.[k <- mk_edge (e_tl old_nxt_values) p1 (val old_nxt) (val old_prv)]
       .[val old_nxt <- mk_edge (e_hd old_nxt_values) (e_tl old_nxt_values)
                    k k]
  else 
    s1.[k <- mk_edge (e_tl old_nxt_values) p1 (val old_nxt) (val old_prv)]
      .[val old_prv <- mk_edge (e_hd old_prv_values) (e_tl old_prv_values)
                    k (prv old_prv_values)]
      .[val old_nxt <- mk_edge (e_hd old_nxt_values) (e_tl old_nxt_values)
                      (nxt old_nxt_values) k].

Notation "'bind' x <- y ; z" :=
  (obind (fun x => z) y) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'bind'  x  <-  y ;  '/' z ']'").

Definition remove_point_typeless (s : {fmap E -> point ^ 2 * E ^ 2})
  (pointing_edge : E) : option {fmap E -> point ^ 2 * E ^ 2} :=
  bind edge_values <- s.[? pointing_edge] ;
  let p1 := e_tl edge_values in
  let p2 := e_hd edge_values in
  let ne := nxt edge_values in
  bind ne_values <- s.[? ne];
  let old_prv := prv edge_values in
  bind old_prv_values <- s.[? old_prv];
  let old_nxt := nxt ne_values in
  bind old_nxt_values <- s.[? old_nxt] ;
  let s1 := s.[\ ([fset pointing_edge] `|` [fset ne ])%fset] in
  let k := newname (domf s1) in
  Some (if old_nxt == old_prv then
     s1.[k <- mk_edge (e_tl old_nxt_values) p1 old_nxt old_prv]
       .[old_nxt <- mk_edge (e_hd old_nxt_values) (e_tl old_nxt_values)
                    k k]
  else 
    s1.[k <- mk_edge (e_tl old_nxt_values) p1 old_nxt old_prv]
      .[old_prv <- mk_edge (e_hd old_prv_values) (e_tl old_prv_values)
                    k (prv old_prv_values)]
      .[old_nxt <- mk_edge (e_hd old_nxt_values) (e_tl old_nxt_values)
                      (nxt old_nxt_values) k]).


Lemma remove_pointP (s : {fmap E -> point ^ 2 * E ^ 2})
 sp sp2 (pointing_edge : {: domf s}) :
  fprv _ sp pointing_edge != fnxt _ sp pointing_edge ->
  edgemapprop (remove_point s sp sp2 pointing_edge).
Proof.
move => at_least_three; rewrite /remove_point.
set edge_values := s pointing_edge.
set p1 := e_tl edge_values.
set p2 := e_hd edge_values.
set ne := fnxt _ sp pointing_edge.
set old_prv := fprv _ sp pointing_edge.
set old_prv_values := s old_prv.
set old_nxt := fnxt _ sp ne.
set old_nxt_values := s old_nxt.
set s1 := s.[\ ([fset (val pointing_edge)] `|` [fset (val ne) ])%fset].
set k := newname (domf s1).
have old_nxt_in_s : val old_nxt \in s  by clear; case: old_nxt.
have old_prv_in_s : val old_prv \in s  by clear; case: old_prv.
have old_nxt_in_s1 : val old_nxt \in s1.
  rewrite /s1 in_fsetE !inE; apply/andP; split;[exact old_nxt_in_s|].
  apply/andP;split; [ | exact old_nxt_in_s].
  apply/negP => /orP [/eqP abs1 | /eqP abs2]; case/negP: at_least_three.
    have onpe : old_nxt = pointing_edge by apply val_inj; rewrite <- abs1.
    by rewrite -[X in fprv _ _ X]onpe /old_nxt fprvK.
  have nepe : old_nxt = ne  by apply val_inj; rewrite <- abs2.
  rewrite -[X in fprv _ _ X](fprvK _ _ _ pointing_edge) //.
  rewrite -[X in fprv _ _ (fprv _ _ X)]/ne -nepe /old_nxt fprvK // -nepe.
  by rewrite /old_nxt fprvK.
have old_prv_in_s1 : val old_prv \in s1.
rewrite /s1 in_fsetE !inE; apply/andP; split;[exact old_prv_in_s|].
  apply/andP;split; [ | exact old_prv_in_s].
  apply/negP => /orP [/eqP abs1 | /eqP abs2]; case/negP: at_least_three.
    have onpe : old_prv = pointing_edge by apply val_inj; rewrite <- abs1.
    by rewrite -[X in fnxt _ _ X]onpe /old_prv fnxtK // -/old_prv onpe.
  have opne : old_prv = ne by apply: val_inj.
  by rewrite -/old_prv opne eqxx.
have kno : k != val old_nxt.
  apply/negP=> /eqP ko; case/negP: (newnameP (domf s1)).
  rewrite -/k ko; exact: old_nxt_in_s1.
have knp : k != val old_prv.
  apply/negP=> /eqP ko; case/negP: (newnameP (domf s1)).
  rewrite -/k ko; exact: old_prv_in_s1.
set newmap := (if _ then _ else _).
rewrite /edgemapprop.
case base : (old_nxt == old_prv).
  rewrite /newmap {newmap}; rewrite base; set newmap := (s1.[_ <- _].[_ <- _]).
  have old_nxt_new_map : val old_nxt \in domf newmap.
    by rewrite /newmap dom_setf inE in_fsetE eqxx.
  have k_new_map : k \in domf newmap.
    by rewrite /newmap !dom_setf 3!inE in_fsetE eqxx orbT.
    have k_new_map' : (val [` k_new_map]%fset \in domf newmap) &&
         ([` k_new_map ]%fset != [` old_nxt_new_map ]%fset).
    rewrite k_new_map andTb.
    apply/negP=> /eqP ko.
    have abs: 
     val [` k_new_map]%fset = val [` old_nxt_new_map]%fset by rewrite ko.
    by case/negP: kno; apply/eqP.
  rewrite (bigD1 [` old_nxt_new_map ]%fset) //; apply /andP; split.
    apply/andP; split; rewrite /newmap mem_setf 3!inE.
      by rewrite /newmap ffunE eqxx nxtK eqxx orbT.
    by rewrite /newmap ffunE eqxx prvK eqxx orbT.
  rewrite (bigD1 [` k_new_map ]%fset); apply /andP; split => //.
    apply/andP; split; rewrite /newmap mem_setf 3!inE ffunE;
      try (have -> : (val [` k_new_map]%fset == val old_nxt) = false
        by apply/negbTE; exact: kno).
      by rewrite FmapE.fmapE eqxx /= nxtK eqxx.
    rewrite FmapE.fmapE eqxx /= prvK.
    by rewrite -[(prv (s pointing_edge))]/(val old_prv) -(eqP base) eqxx.
  rewrite big_andE; apply/forallP => x; apply/implyP.
  move => /andP [] /andP [] _ px xk.
  have xs1 : val x \in s1.
    have : val x \in newmap by clear; case: x. 
  rewrite /newmap /s1 !in_fsetE !inE.
    case/orP => [/eqP a1 | ].
      by case/negP: px; apply/eqP; apply: val_inj.
    case/orP => [/eqP a2 | ].    
      by case/negP: xk; apply/eqP; apply:val_inj.
    by done.
  have xs : val x \in s.
    by move: xs1; rewrite /s1 in_fsetE !inE => /andP [] it _.
  have xf : val (fnxt _ sp [` xs]%fset) \in newmap.
    rewrite /newmap /s1 3!in_fsetE; apply/orP; right; apply/orP; right.
    rewrite !inE.
    have vfs : val (fnxt s sp [` xs]%fset) \in domf s  by apply: valP.
    rewrite vfs andTb andbT.
    apply/negP => /orP [ /eqP | /eqP].
      rewrite -[X in _ = val X](fnxtK _ _ sp2).
      move => a1; move : (val_inj _ _ a1) => a1'.
      move: (fnxt_inj s sp sp2 _ _ a1').
      rewrite -/old_prv => a1''.
      case/negP: px; apply/eqP; apply:val_inj.
      rewrite -[val x]/(val [` xs]%fset); rewrite a1''.
      rewrite -[val [` old_nxt_new_map ]%fset]/(val old_nxt).
      by rewrite (eqP base).
    rewrite /ne => a2; move: (val_inj _ _ a2) => a2'.
    move : (fnxt_inj _ _ sp2 _ _ a2') => a2''.
    move: xs1; rewrite /s1 in_fsetE !inE -a2'' eqxx.
    by rewrite orTb andbF.
(* The following lines are a duplication of the proof of xf *)
  have xpr : val (fprv _ sp [` xs]%fset) \in newmap.
    rewrite /newmap /s1 3!in_fsetE; apply/orP; right; apply/orP; right.
    rewrite !inE.
    have vfs : val (fprv s sp [` xs]%fset) \in domf s  by apply: valP.
    rewrite vfs andTb andbT.
    apply/negP => /orP [ /eqP | /eqP].
      rewrite -[X in _ = val X](fprvK _ _ sp2).
(* the two branches are swapped *)
      move => a1; move: (val_inj _ _ a1) => a1'.
      move: (fprv_inj _ _ sp2 _ _ a1') => a1''.
      move: xs1; rewrite /s1 in_fsetE !inE /ne -a1'' eqxx.
      by rewrite orbT andbF.
    rewrite -[X in _ = val X](fprvK _ _ sp2).
    move => a2; move : (val_inj _ _ a2) => a2'.
    move: (fprv_inj s sp sp2 _ _ a2').
    rewrite -/old_nxt => a2''.
    case/negP: px; apply/eqP; apply:val_inj.
    by rewrite -[val x]/(val [` xs]%fset) a2''.
  suff cmp :newmap x = s [` xs ]%fset by
    rewrite cmp -[nxt _]/(val (fnxt _ sp [` xs ]%fset))
      -[prv _]/(val (fprv _ sp [` xs]%fset)) xf xpr.
  rewrite /newmap ffunE (_ : (val x == val old_nxt) = false); last first.
    apply/negP=> xn; case/negP: px; apply/eqP.
    by apply: val_inj; rewrite (eqP xn).
  rewrite fnd_set (_ : (val x == k) = false); last first.
    by apply/negP=> xn; move: xs1; rewrite (eqP xn); apply/negP/newnameP.
(* Why, oh why is there a duplication of "x \in domf s" in the expansion
   of x \in s.[\ ... ] *)
  rewrite /s1 FmapE.fmapE; set tst := (_ `\` _)%fset.
  have -> : (val x \in tst) = (val x \in s1).
    by rewrite in_fsetD /s1 mem_remf; congr (_ && _).
  by rewrite xs1 (in_fnd xs).
rewrite /newmap base {newmap}.
set newm2 := s1.[_ <- _].
rewrite /newm2; set newm1 := s1.[_ <- _].[_ <- _].
rewrite /newm1; set newmap := _.[_ <- _].
have old_nxt_new_map : val old_nxt \in domf newmap.
  by rewrite /newmap dom_setf inE in_fsetE eqxx.
have old_prv_new_map : val old_prv \in domf newmap.
  by rewrite /newmap dom_setf !inE eqxx !orbT.
have k_new_map : k \in domf newmap.
  by rewrite /newmap !dom_setf 6!inE eqxx !orbT.
have k_new_map' : (val [` k_new_map]%fset \in domf newmap) &&
         ([` k_new_map ]%fset != [` old_nxt_new_map ]%fset).
  rewrite k_new_map andTb.
  apply/negP=> /eqP ko.
  have abs: 
     val [` k_new_map]%fset = val [` old_nxt_new_map]%fset by rewrite ko.
  by case/negP: kno; apply/eqP.
have k_in : k \in newm1.
  by rewrite /newm1 in_fsetE !dom_setf !inE eqxx orbT.
have k_in2 : k \in newm2.
  by rewrite /newm2 in_fsetE in_fsetE eqxx.
rewrite (bigD1 [` old_nxt_new_map ]%fset) //; apply /andP; split.
  set u := nxt newmap.[old_nxt_new_map]; set v := prv newmap.[old_nxt_new_map].
  apply/andP; split.
    rewrite /newmap !in_fsetE !inE andbC -!andbA Bool.andb_diag.
(* bug : the rule in_fset precedes all others in in_fsetE, not sure it is the
right choice. *)
    have uq : u = nxt old_nxt_values.
      by rewrite /u /newmap getf_set nxtK.
    have us : u \in domf s.
      by rewrite uq -[nxt _]/(val (fnxt s sp old_nxt)); apply: valP.
    have unpe : ~ u = val pointing_edge.
      move=> upe.
      case/negP: base; apply/eqP.
      apply: (fnxt_inj _ _ sp2).
      by rewrite /old_prv fnxtK //; apply: val_inj; rewrite -upe; symmetry.
    have unne : u <> val ne.
      move => une.
      case/negP: at_least_three; apply/eqP.
      have une' : [` us]%fset = ne  by apply: val_inj; rewrite -une.
      rewrite -/ne -une'.
      have uloop : [` us]%fset = fnxt _ sp (fnxt _ sp ne)  by apply: val_inj.
      rewrite -(fprvK _ sp sp2 pointing_edge) -/ne -une'. 
      by rewrite [X in fprv _ _ (fprv _ _ X)]uloop !fprvK; symmetry.
    move/eqP: unpe; move/eqP: unne => unne unpe.
    by rewrite (negbTE unne) (negbTE unpe) us !orbT.
  have vk : v == k.
    by rewrite /v /newmap getf_set prvK.
  by rewrite (eqP vk).
have k_edge : newmap.[k_new_map] = mk_edge (e_tl old_nxt_values)
                        p1 (val old_nxt) (val old_prv).
  by rewrite /newmap setfNK (negbTE kno) setfNK (negbTE knp) getf_set.
rewrite (bigD1 [` k_new_map ]%fset) //; apply /andP; split.
  by rewrite k_edge nxtK prvK old_nxt_new_map old_prv_new_map.  
have old_df : (val old_prv == val old_nxt) = false.
  apply/negP => /eqP abs; case/negP: base; apply/eqP; symmetry.
  by apply: val_inj.
rewrite (bigD1 [` old_prv_new_map ]%fset) //; apply /andP; last first.
  split.
    rewrite andTb; apply/negP => /eqP => abs; case/eqP: base; symmetry.
    apply: val_inj.
    by rewrite -[val old_prv]/(val [` old_prv_new_map]%fset) abs.
  apply/negP => /eqP => abs; case/eqP: knp; symmetry.
  by rewrite -[val old_prv]/(val [` old_prv_new_map]%fset) abs.
have prv_in1 : val old_prv \in newm1.
  by rewrite /newm1 mem_setf inE eqxx.
split.
  have prv_edge :
    newmap.[old_prv_new_map] = mk_edge (e_hd old_prv_values)
        (e_tl old_prv_values) k (prv old_prv_values).
    by rewrite /newmap setfNK old_df getf_set.
  rewrite prv_edge nxtK prvK k_new_map andTb. 
  set u := prv old_prv_values.
  have us : u \in domf s.
      by rewrite /u -[prv _]/(val (fprv s sp old_prv)); apply: valP.
  have unpe : ~ u = val pointing_edge.
    move => upe.
    case/negP: at_least_three; apply/eqP.
    have upe' : [` us]%fset = pointing_edge  by apply: val_inj; rewrite -upe.
    rewrite -/old_prv -upe'.
    have uloop : [` us]%fset = fprv _ sp (fprv _ sp pointing_edge)
      by apply: val_inj.
    by rewrite -(fnxtK _ sp sp2 old_prv) /old_prv -uloop.
  have unne : u <> val ne.
    move=> une.
    case/negP: base; apply/eqP.
    apply: (fprv_inj _ _ sp2).
    by rewrite /old_nxt fprvK //; apply: val_inj; rewrite -une.
  move/eqP: unpe; move/eqP: unne => unne unpe.
  by rewrite /newmap in_fsetE !inE us (negbTE unne) (negbTE unpe) !orbT.
rewrite big_andE; apply/forallP => x; rewrite andTb; apply/implyP.
move => /andP [] /andP [] xnxt xk xprv.
have xs1 : val x \in s1.
  have : val x \in newmap by clear; case: x. 
  rewrite /newmap /s1 !in_fsetE !inE.
  case/orP => [/eqP a1 | ].
    by case/negP: xnxt; apply/eqP; apply: val_inj.
  case/orP => [/eqP a2 | ].    
    by case/negP: xprv; apply/eqP; apply:val_inj.
  case/orP => [/eqP a3 | ].
    by case/negP: xk; apply/eqP; apply:val_inj.
  by done.
  have xs : val x \in s.
    by move: xs1; rewrite /s1 in_fsetE !inE => /andP [] it _.
have xf : val (fnxt _ sp [` xs]%fset) \in newmap.
  rewrite /newmap /s1 6!in_fsetE.
  apply/orP; right; apply/orP; right; apply/orP; right.
  rewrite !inE.
  have vfs : val (fnxt s sp [` xs]%fset) \in domf s  by apply: valP.
  rewrite vfs andTb andbT.
  apply/negP => /orP [ /eqP | /eqP].
(* Wouah: rewrite can't do it.  Why? *)
    rewrite -[X in _ = val X](fnxtK _ _ sp2).
    move => a1; move : (val_inj _ _ a1) => a1'.
    move: (fnxt_inj s sp sp2 _ _ a1').
    rewrite -/old_prv => a1''.
    case/negP: xprv; apply/eqP; apply:val_inj.
    by rewrite -[val x]/(val [` xs]%fset) a1''.
  rewrite /ne => a2; move: (val_inj _ _ a2) => a2'.
  move : (fnxt_inj _ _ sp2 _ _ a2') => a2''.
  move: xs1; rewrite /s1 in_fsetE !inE -a2'' eqxx.
  by rewrite orTb andbF.
(* The following lines are a duplication of the proof of xf *)
have xpr : val (fprv _ sp [` xs]%fset) \in newmap.
  rewrite /newmap /s1 6?in_fsetE.
  apply/orP; right; apply/orP; right; apply/orP; right.
  rewrite !inE.
  have vfs : val (fprv s sp [` xs]%fset) \in domf s  by apply: valP.
  rewrite vfs andTb andbT.
  apply/negP => /orP [ /eqP | /eqP].
    rewrite -[X in _ = val X](fprvK _ _ sp2).
(* the two branches are swapped *)
    move => a1; move: (val_inj _ _ a1) => a1'.
    move: (fprv_inj _ _ sp2 _ _ a1') => a1''.
    move: xs1; rewrite /s1 in_fsetE !inE /ne -a1'' eqxx.
    by rewrite orbT andbF.
  rewrite -[X in _ = val X](fprvK _ _ sp2).
  move => a2; move : (val_inj _ _ a2) => a2'.
  move: (fprv_inj s sp sp2 _ _ a2').
  rewrite -/old_nxt => a2''.
  case/negP: xnxt; apply/eqP; apply:val_inj.
  by rewrite -[val x]/(val [` xs]%fset) a2''.
suff cmp :newmap x = s [` xs ]%fset by
    rewrite cmp -[nxt _]/(val (fnxt _ sp [` xs ]%fset))
      -[prv _]/(val (fprv _ sp [` xs]%fset)) xf xpr.
rewrite /newmap ffunE (_ : (val x == val old_nxt) = false); last first.
  apply/negP=> xn; case/negP: xnxt; apply/eqP.
  by apply: val_inj; rewrite (eqP xn).
rewrite fnd_set (_ : (val x == val old_prv) = false); last first.
  apply/negP=> xn; case/negP: xprv; apply/eqP.
  by apply: val_inj; rewrite (eqP xn).
(* Why, oh why is there a duplication of "x \in domf s" in the expansion
   of x \in s.[\ ... ] *)
rewrite fnd_set (_ : (val x == k) = false); last first.
  apply/negP=> xn; case/negP: xk; apply/eqP.
  by apply: val_inj; rewrite (eqP xn).
(* Why, oh why is there a duplication of "x \in domf s" in the expansion
   of x \in s.[\ ... ] *)
rewrite /s1 FmapE.fmapE; set tst := (_ `\` _)%fset.
have -> : (val x \in tst) = (val x \in s1).
  by rewrite in_fsetD /s1 mem_remf; congr (_ && _).
by rewrite xs1 (in_fnd xs).
Qed.

Lemma remove_point_detype s sp sp2 pe :
  remove_point_typeless s (val pe) = Some (remove_point s sp sp2 pe).
Proof.
rewrite /remove_point_typeless /remove_point.
set edge_values := s pe.
have v_edge_values : (s.[? val pe]) = Some (edge_values).
  by rewrite /edge_values /fnd valK.
set p1 := e_hd edge_values.
set p2 := e_tl edge_values.
set ne := fnxt s sp pe.
have v_ne_values : s.[? nxt edge_values] = Some (s ne).
  rewrite /fnd /edge_values.
  by rewrite  (insubT [pred x | x \in domf s] (fnxt_aux s sp pe)).
set old_nxt := fnxt s sp ne.
set old_nxt_values := s old_nxt.
have v_old_nxt_values : s.[? nxt (s ne)] = Some (old_nxt_values).
  rewrite /fnd /old_nxt_values.
  by rewrite  (insubT [pred x | x \in domf s] (fnxt_aux s sp ne)).
set old_prv := fprv s sp pe.
set old_prv_values := s old_prv.
have v_old_prv_values : s.[? prv (s pe)] = Some (old_prv_values).
  rewrite /fnd /old_prv_values.
  by rewrite  (insubT [pred x | x \in domf s] (fprv_aux s sp pe)).
set s1 := s.[\ [fset val pe; val ne]%fset].
set k := newname (domf s1).
rewrite v_edge_values /= v_ne_values /= v_old_prv_values /= v_old_nxt_values
  /=.
rewrite -[s.[\ [fset fsval pe; nxt edge_values]%fset]]/s1.
rewrite -[newname
              [fset x
                 | x in domf s
                 & x \in domf s `\` [fset fsval pe; nxt edge_values]]%fset]/k.
suff : (nxt (s ne) == prv edge_values) = (old_nxt == old_prv)  by [].
apply/eqP/eqP.
  by move => h; apply/val_inj; exact: h.
by move => h; change (val old_nxt = val old_prv); congr val.
Qed.

Definition edgemapprop3 s :=
  \big[andb/true]_(i : {: domf s})
     ((oapp (fun v => (e_hd (s i) == e_tl v)) false
         (s.[?nxt (s i)])) &&
       (oapp (fun vprv => nxt vprv == val i) false s.[? prv (s i)]) &&
       (oapp (fun vnxt => prv vnxt == val i) false s.[? nxt (s i)])).

Lemma prop23_equiv s sp : edgemapprop2 s sp = edgemapprop3 s.
Proof.
rewrite /edgemapprop2 /edgemapprop3.
apply: eq_bigr => i _.
have qn : s.[? nxt (s i)] = Some (s (fnxt s sp i)).
  by rewrite /fnxt /fnd (insubT [pred x | x \in domf s] (fnxt_aux s sp i)).
have qp : s.[? prv (s i)] = Some (s (fprv s sp i)).
  by rewrite /fprv /fnd (insubT [pred x | x \in domf s] (fprv_aux s sp i)).
by rewrite qn qp.
Qed.

Lemma stable_update 
  (s s' : {fmap E -> point ^ 2 * E ^ 2})
  (side : E) v :
  side \in s -> (domf s' `<=` domf s)%fset ->
  (domf (s'.[side <- v]) `<=` domf s)%fset.
Proof.  
move => sides1 incl.
apply/fsubsetP => x; rewrite 2!in_fsetE => /orP [/eqP -> // | ]; last first.
by move/fsubsetP: incl => incl' xs1; rewrite (incl' _ xs1).
Qed.

Lemma stable_update2
  (s s' : {fmap E -> point ^ 2 * E ^ 2})
  (new : E) (side : E) vn v : side \in s' ->
  (domf s' `<=` domf (s.[new <- vn]))%fset ->
  (domf (s'.[side <- v]) `\ new `<=` domf s)%fset.
Proof.
rewrite !dom_setf=> side' /fsubsetP incl; apply/fsubsetP => x.
rewrite !in_fsetE => /andP [] xnn /orP [/eqP xside | xs'].
  by move: (incl _ side'); rewrite -xside !in_fsetE (negbTE xnn).
by move: (incl _ xs'); rewrite !in_fsetE (negbTE xnn).
Qed.

Lemma in_pair_nxt s sp (sp2 : edgemapprop2 s sp) pe x :
  val (fnxt _ sp x) \in [fset val pe; val (fnxt _ sp pe)]%fset ->
  val x \in [fset val pe; val (fprv _ sp pe)]%fset.
Proof.
rewrite !in_fsetE => /orP [xpe | xne]; apply/orP;[right | left].
  by apply/eqP; congr val; move/eqP/val_inj: xpe => <-; rewrite fprvK.
by apply/eqP; congr val; move/eqP/val_inj/ (fnxt_inj _ _ sp2): xne.
Qed.

Lemma at_least_three_next2 s sp (sp2 : edgemapprop2 s sp) pe :
  fprv _ sp pe != fnxt _ sp pe ->
  val (fnxt _ sp (fnxt _ sp pe)) \notin [fset val pe; val (fnxt _ sp pe)]%fset.
Proof.
move => three; apply/negP; move/(in_pair_nxt _ _ sp2).
rewrite in_fsetU !in_fset1 => /orP [] /eqP/val_inj a; case/negP: three;
  apply/eqP => //.
by rewrite -[X in fprv _ _ X]a fprvK.
Qed.

Lemma in_pair_prv s sp (sp2 : edgemapprop2 s sp) pe x :
  val (fprv _ sp x) \in [fset val pe; val (fnxt _ sp pe)]%fset ->
  val x \in [fset val (fnxt _ sp (fnxt _ sp pe)); val (fnxt _ sp pe)]%fset.
Proof.
rewrite !in_fsetE => /orP [xpe | xne]; apply/orP;[right | left].
  by apply/eqP; congr val; move/eqP/val_inj: xpe => <-; rewrite fnxtK.
apply/eqP; congr val; apply/(fprv_inj _ _ sp2); move/eqP/val_inj: xne => ->.
by rewrite fprvK.
Qed.

Lemma at_least_three_prv s sp (sp2 : edgemapprop2 s sp) pe :
  fprv _ sp pe != fnxt _ sp pe ->
  val (fprv _ sp pe) \notin [fset val pe; val (fnxt _ sp pe)]%fset.
Proof.
move => three; apply/negP; move/(in_pair_prv _ _ sp2).
by rewrite in_fsetU !in_fset1 => /orP [] /eqP/val_inj a; case/negP: three;
  apply/eqP; rewrite [X in fprv _ _ X]a fprvK.
Qed.

Lemma remove_point2P (s : {fmap E -> point ^ 2 * E ^ 2})
 sp sp2 (pointing_edge : {: domf s}) 
 (h : edgemapprop (remove_point s sp sp2 pointing_edge)) :
  fprv _ sp pointing_edge != fnxt _ sp pointing_edge ->
  edgemapprop2 (remove_point s sp sp2 pointing_edge) h.
Proof.
move => at_least_three; rewrite /remove_point prop23_equiv.
set edge_values := s pointing_edge.
set p1 := e_tl edge_values.
set p2 := e_hd edge_values.
set ne := fnxt _ sp pointing_edge.
set old_prv := fprv _ sp pointing_edge.
set old_prv_values := s old_prv.
set old_nxt := fnxt _ sp ne.
set old_nxt_values := s old_nxt.
set s1 := s.[\ ([fset (val pointing_edge)] `|` [fset (val ne) ])%fset].
set k := newname (domf s1).
(* TODO : these replace lines that were duplicated from the proof of *)
(* remove_pointP. Perform replacement there too. *)
have old_nxt_in_s1 : val old_nxt \in domf s1.
  rewrite /s1 (* complain: mem_remf has low priority in in_fsetE *).
  rewrite mem_remf (valP old_nxt) andbT.
  by apply: (at_least_three_next2 s sp sp2 _ at_least_three).
have old_prv_in_s1 : val old_prv \in domf s1.
  rewrite mem_remf (valP old_prv) andbT.
  by apply: (at_least_three_prv s sp sp2 _ at_least_three).
have kno :k != val old_nxt.
  apply/negP=> /eqP ko; case/negP: (newnameP (domf s1)).
  by rewrite -/k ko; exact: old_nxt_in_s1.
(* end of duplicated part. *)
have knp : k != val old_prv.
  apply/negP=> /eqP kp; case/negP: (newnameP (domf s1)). 
  by rewrite -/k kp; exact: old_prv_in_s1.
case base : (old_nxt == old_prv).
  set V := (X in s1.[k <- X]); set V2 := (X in s1.[_ <- _].[_ <- X]).
  set newmap := (s1.[_ <- _]).[_ <- _].
  have domnew : (domf newmap `\ k `<=` domf s1)%fset.
    apply: (stable_update2 _ _ _ _ V).
      by rewrite mem_setf inE old_nxt_in_s1 orbT.
    by apply/fsubsetP.
  have old_nxt_new_map : val old_nxt \in domf newmap.
    by rewrite /newmap dom_setf inE in_fsetE eqxx.
  set u := nxt newmap.[old_nxt_new_map]; set v := prv newmap.[old_nxt_new_map].
  have uk : u = k.
    by rewrite /u /newmap -[val old_nxt]/(val [` old_nxt_new_map]%fset)
          getf_set nxtK.
  have vk : v = k  by rewrite /v /newmap getf_set prvK.
  have := sp2; rewrite /edgemapprop2 big_andE => /forallP => s2'.
  rewrite /edgemapprop3.
  rewrite (bigD1 [` old_nxt_new_map ]%fset) //; apply /andP; split.
    apply/andP; split; [apply/andP; split | ].
        rewrite -/u uk fnd_set (negbTE kno) fnd_set eqxx /oapp e_tlK.
        rewrite /newmap getf_set e_hdK /old_nxt_values (eqP base).
        have := (s2' old_prv) => /implyP => s2''; have := s2'' (erefl _).
        by rewrite /old_prv fnxtK //; move => /andP [] /andP [].
      by rewrite -/v vk fnd_set (negbTE kno) fnd_set eqxx /oapp nxtK.
    by rewrite -/u uk fnd_set (negbTE kno) fnd_set eqxx /oapp prvK -(eqP base).
  have k_new_map : k \in domf newmap.
    by rewrite /newmap !dom_setf 3!inE in_fsetE eqxx orbT.
  rewrite (bigD1 [` k_new_map]%fset) //; apply /andP; split.
    have edgek : newmap.[k_new_map] =
            mk_edge (e_tl old_nxt_values) p1 (val old_nxt) (val old_prv).
      by rewrite /newmap ffunE (negbTE kno) fnd_set eqxx.
    rewrite edgek nxtK prvK.
    apply/andP; split; [apply/andP; split | ].
        by rewrite /newmap fnd_set eqxx /oapp e_hdK e_tlK.
      by rewrite -(eqP base) /newmap fnd_set eqxx /oapp nxtK.
    by rewrite /newmap fnd_set eqxx /oapp prvK.
  rewrite big_andE;apply/forallP => x;apply/implyP.
  rewrite andTb =>/andP [] xno xnk.

  have vxvo : val x == val old_nxt = false.
    by apply/negP => /eqP a; case/negP: xno; apply/eqP/val_inj.
  have vxk : val x == k = false.
    by apply/negP => /eqP a; case/negP: xnk; apply/eqP/val_inj.
  have xnewmap : val x \in (domf newmap `\ k)%fset.
    by rewrite 2!in_fsetE vxk (valP x).
  have oins1k : val old_nxt \in s1.[k <- V].
      have tmp := at_least_three_next2 s sp sp2 _ at_least_three.
      by rewrite /s1 mem_setf inE mem_remf (valP old_nxt) /old_nxt/ne tmp orbT.
  have xins1 : val x \in s1.
    have cmpf : (domf s1.[k <- V] `<=` domf s1.[k <- V])%fset.
      by apply/fsubsetP.
    have on : val old_nxt \in domf s1.[k <- V].
      by rewrite in_fsetU old_nxt_in_s1 orbT.
    apply/(fsubsetP domnew)/xnewmap.
  have xins : val x \in s.
    by move : xins1; rewrite /s1 mem_remf => /andP [].
  have valxx : val x = val [`xins]%fset by [].
  have xnne : val x != val ne.
    apply/negP => xne; move: xins1; rewrite /s1 mem_remf xins andbT.
    by rewrite in_fsetU !in_fset1 xne orbT.
  have xnpe : val x != val pointing_edge.
    apply/negP => xpe; move: xins1; rewrite /s1 mem_remf xins andbT.
    by rewrite in_fsetU !in_fset1 xpe.
  have vnewmap : (newmap x) = s [` xins]%fset.
    rewrite /newmap ffunE vxvo fnd_set vxk /fnd.
    rewrite (insubT [pred x | x \in domf s1] xins1) -[X in X = _]/(s1.[xins1]).
    by rewrite getf_restrict.
  have nxtxs : nxt s.[xins] \in s by apply: fnxt_aux.
  have prvxs : prv s.[xins] \in s by apply: fprv_aux.
  have prvxnne : prv s.[xins] != val ne.
    apply/negP => /eqP a.
    case/negP:vxvo; apply/eqP; rewrite valxx; congr val; apply: fprv_inj => //.
    by rewrite /old_nxt fprvK //; apply val_inj.
  have nxtxnne : nxt s.[xins] != val ne.
    apply/negP => /eqP a.
    case/negP: xnpe; apply/eqP; rewrite valxx; congr val.
    by apply/(fnxt_inj _ _ sp2)/val_inj.
  have prvxnpe : prv s.[xins] != val pointing_edge.
    apply/negP => /eqP a.
    case/negP: xnne; apply/eqP; rewrite valxx; congr val.
    by apply/fprv_inj => //; rewrite /ne fprvK //; apply/val_inj.
  have nxtxnpe : nxt s.[xins] != val pointing_edge.
    apply/negP => /eqP a.
    case/negP:vxvo; apply/eqP; rewrite valxx (eqP base) /old_prv; congr val.
    by apply/(fnxt_inj _ _ sp2); rewrite fnxtK //; apply val_inj.

  have nxtxs1 : nxt s.[xins] \in s1.
    by rewrite /s1 mem_remf nxtxs andbT in_fsetU !in_fset1 (negbTE nxtxnpe)
       (negbTE nxtxnne).
  have prvxs1 : prv s.[xins] \in s1.
    by rewrite /s1 mem_remf prvxs andbT in_fsetU !in_fset1 (negbTE prvxnpe)
       (negbTE prvxnne).

  have nxtxno : nxt s.[xins] == val old_nxt = false.
    apply/negP => /eqP nxo; case/negP: xnne; apply/eqP.
    by rewrite valxx; congr val; apply/(fnxt_inj _ _ sp2)/val_inj.
  have prvxno : (prv s.[xins] == val old_nxt) = false.
    apply/negP => /eqP pxo; case/negP: xnpe; apply/eqP.
    rewrite valxx; congr val; apply/(fprv_inj _ _ sp2)/val_inj.
  by rewrite -/old_prv -(eqP base).
  have nxtxnk : nxt s.[xins] == k = false.
    apply/negP => /eqP nxk.
    by case/negP: (newnameP (domf s1)); rewrite -/k -nxk.
  have prvxnk : prv s.[xins] == k = false.
    apply/negP => /eqP pxk.
    by case/negP: (newnameP (domf s1)); rewrite -/k -pxk.
  have vnxtx : newmap.[? nxt s.[xins]] = Some (s (fnxt _ sp [`xins]%fset)).
    rewrite /newmap fnd_set nxtxno fnd_set nxtxnk.
    rewrite /s1 fnd_rem in_fsetU !in_fset1.
    by rewrite (negbTE nxtxnpe) (negbTE nxtxnne) Some_fnd.
  have vprvx : newmap.[? prv s.[xins]] = Some (s (fprv _ sp [`xins]%fset)).
    rewrite /newmap fnd_set prvxno fnd_set prvxnk.
    rewrite /s1 fnd_rem in_fsetU !in_fset1.
    by rewrite (negbTE prvxnpe) (negbTE prvxnne) Some_fnd.
  rewrite vnewmap vnxtx vprvx /oapp.
  by have := s2' [`xins]%fset => /implyP tmp; apply tmp.
set V := (X in s1.[k <- X]); set V2 := (X in s1.[_ <- _].[_ <- X]).
set V3 := (X in s1.[_ <- _].[_ <- _].[_ <- X]).
set newmap := (X in edgemapprop3 X).
have domnew : (domf newmap `\ k `<=` domf s1)%fset.
  apply: (stable_update2 _ _ _ _ V).
    by rewrite mem_setf inE mem_setf inE old_nxt_in_s1 !orbT.
  apply: stable_update.
    by rewrite mem_setf inE old_prv_in_s1 !orbT.
  by apply/fsubsetP.
have old_nxt_new_map : val old_nxt \in domf newmap.
  by rewrite /newmap dom_setf inE in_fsetE eqxx.
have old_prv_new_map : val old_prv \in domf newmap.
  by rewrite /newmap dom_setf inE in_fsetE mem_setf inE eqxx !orbT.
have := sp2; rewrite /edgemapprop2 big_andE => /forallP => s2'.
set u := nxt newmap.[old_prv_new_map]; set v := prv newmap.[old_nxt_new_map].
have uk : u = k.
  rewrite /u /newmap -[val old_prv]/(val [` old_prv_new_map]%fset).
  rewrite ffunE (_ : (val old_prv == val old_nxt) = false); last first.
    by rewrite eq_sym; exact: base. (* Need to understand why rewrite base did not work*)
  by rewrite fnd_set eqxx nxtK.
  have vk : v = k  by rewrite /v /newmap getf_set prvK.
rewrite /edgemapprop3.
rewrite (bigD1 [` old_nxt_new_map ]%fset) //; apply /andP; split.
  have V3newmap : newmap.[old_nxt_new_map] = V3.
    by rewrite /newmap getf_set.
(* hard case. *)
  set u1 := nxt newmap.[old_nxt_new_map].
  have u1vals : u1 = nxt (s old_nxt).
    by rewrite /u1 V3newmap /V3 nxtK.
  have u1ins : u1 \in s.
    by rewrite u1vals; exact: fnxt_aux.
  have u1ins1 : u1 \in s1.
    rewrite /s1 mem_remf u1ins andbT u1vals.
    apply/negP; rewrite -[nxt _]/(val (fnxt _ sp old_nxt)).
    move/(in_pair_nxt _ _ sp2); rewrite in_fsetU !in_fset1 => /orP [/eqP abs | /eqP/val_inj abs].
      have := (at_least_three_next2 s sp sp2 _ at_least_three).
      by rewrite -/old_nxt abs in_fsetU in_fset1 eqxx.
    by move: base; rewrite abs eqxx.
  have u1no : u1 != val old_nxt.
    apply/negP => /eqP; rewrite u1vals -[nxt _]/(val (fnxt _ sp old_nxt)).
    move/val_inj/(fnxt_inj _ _ sp2) => abs.
    have := (at_least_three_next2 s sp sp2 _ at_least_three).
    by rewrite -/old_nxt -/ne in_fsetU !in_fset1 abs eqxx orbT.
  have u1k : u1 != k.
    apply/negP => abs; move: u1ins1; rewrite (eqP abs) /k => kins.
    by move:(newnameP (domf s1)); rewrite kins.
(* end of hard case. *)
  apply/andP; split; [apply/andP; split | ].
      rewrite /newmap fnd_set (negbTE u1no) fnd_set.
      case u1prv : (u1 == val old_prv).
        rewrite /oapp ffunE eqxx /V3 /V2 e_hdK e_tlK.
        move/implyP : (s2' old_nxt) => a. 
        move: (a (erefl _)) => {a}; rewrite -/old_nxt_values.
        move => /andP [] /andP [] a _ _; rewrite (eqP a) {a}.
        apply/eqP; congr e_tl; rewrite /old_prv_values.
        have -> : (fnxt s sp old_nxt) = old_prv => //.
        by apply:val_inj; rewrite -(eqP u1prv).
      rewrite fnd_set (negbTE u1k) in_fnd /oapp getf_set /V3 e_hdK.
      move/implyP : (s2' old_nxt) => a; move : (a (erefl true)).
      move => {a} /andP [] /andP [] a _ _; rewrite getf_restrict (eqP a).
      have -> : (fnxt s sp old_nxt) = [` u1ins]%fset => //.
      by apply:val_inj.
(* end of checking the points. *)
    rewrite -/v vk fnd_set (negbTE kno) fnd_set (negbTE knp) fnd_set eqxx.
    by rewrite /oapp /V nxtK.
  rewrite /newmap fnd_set (negbTE u1no) fnd_set.
  case u1prv : (u1 == val old_prv).
    rewrite /oapp /V2 prvK.
    move/implyP : (s2' old_nxt) => a. 
    move: (a (erefl _)) => {a}; rewrite -/old_nxt_values.
    move => /andP [] /andP [] _ _ a; rewrite -[val _]/(val old_nxt) -(eqP a).
    rewrite /old_prv_values.
    have -> : (fnxt s sp old_nxt) = old_prv => //.
    by apply:val_inj; rewrite -(eqP u1prv).

  rewrite fnd_set (negbTE u1k) in_fnd /oapp.
  move/implyP : (s2' old_nxt) => a; move : (a (erefl true)).
  move => {a} /andP [] /andP [] _ _ a; rewrite getf_restrict.
  rewrite -[val _]/(val old_nxt) -(eqP a).
  have -> : (fnxt s sp old_nxt) = [` u1ins]%fset => //.
  by apply:val_inj.

(* Duplication for old_prv. *)

rewrite (bigD1 [` old_prv_new_map ]%fset) //; last first.
  rewrite andTb; apply /negP => /eqP => abs.
  case/negP: base; apply/eqP/val_inj.
  by rewrite -[val old_prv]/(val [` old_prv_new_map]%fset) abs.
 apply /andP; split.
  have V2newmap : newmap.[old_prv_new_map] = V2.
    rewrite /newmap ffunE -[X in X == _]/(val old_prv) eq_sym.
    rewrite (_ : (val old_nxt == val old_prv) = false); last by [].
    by rewrite fnd_set eqxx.

(* hard case. *)
  set u1 := prv newmap.[old_prv_new_map].
  have u1vals : u1 = prv (s old_prv).
    by rewrite /u1 V2newmap /V2 prvK.
  have u1ins : u1 \in s.
    by rewrite u1vals; exact: fprv_aux.
  have u1ins1 : u1 \in s1.
    rewrite /s1 mem_remf u1ins andbT u1vals.
    apply/negP; rewrite -[prv _]/(val (fprv _ sp old_prv)).
    move/(in_pair_prv _ _ sp2); rewrite in_fsetU !in_fset1.
    move => /orP [/eqP abs | /eqP/val_inj/eqP abs].
      by case/negP: base; apply/eqP/val_inj; rewrite abs.
    by case/negP: at_least_three.
  have u1no : u1 != val old_prv.
    apply/negP => /eqP; rewrite u1vals -[prv _]/(val (fprv _ sp old_prv)).
    move/val_inj/(fprv_inj _ _ sp2) => abs.
    have := (at_least_three_prv s sp sp2 _ at_least_three).
    by rewrite -/old_prv in_fsetU !in_fset1 abs eqxx.
  have u1k : u1 != k.
    apply/negP => abs; move: u1ins1; rewrite (eqP abs) /k => kins.
    by move:(newnameP (domf s1)); rewrite kins.
(* end of hard case. *)
  apply/andP; split; [apply/andP; split | ].
      rewrite V2newmap /V2 nxtK /newmap fnd_set (negbTE kno).
      rewrite fnd_set (negbTE knp) fnd_set eqxx.
      rewrite /oapp /V e_hdK e_tlK /p1.
      move/implyP: (s2' old_prv) => a; move: (a (erefl true)).
      move => {a} /andP [] /andP [] /eqP a _ _; rewrite /old_prv_values a.
      by rewrite /old_prv fnxtK.
(* end of checking the points. *)
    rewrite /newmap fnd_set; case u1o : (u1 == val old_nxt).
      rewrite /oapp /V3 nxtK.
      move/implyP: (s2' old_prv) => a; move: (a (erefl true)).
      move => {a} /andP [] /andP [] /eqP _ a _.
      rewrite -[nxt old_nxt_values]/(val (fnxt _ sp old_nxt)).
      rewrite -[X in _ == X]/(val old_prv) -(eqP a) fnxtK //.
      apply/eqP; congr val; apply/(fprv_inj _ _ sp2).
      by rewrite fprvK //; apply/val_inj; rewrite -(eqP u1o) u1vals.
    rewrite fnd_set (negbTE u1no) fnd_set (negbTE u1k) in_fnd /oapp.
    move/implyP : (s2' old_prv) => a; move : (a (erefl true)).
    move => {a} /andP [] /andP [] _ a _; rewrite getf_restrict.
    rewrite -[val _]/(val old_prv) -(eqP a) {a}.
    have -> : fprv s sp old_prv = [` u1ins]%fset => //.
    by apply: val_inj.
  rewrite V2newmap /V2 nxtK fnd_set (negbTE kno) fnd_set (negbTE knp).
  by rewrite fnd_set eqxx /oapp /V prvK.
(* end of duplication. *)
(* Now proving the properties for edge k *)
have k_new_map : k \in domf newmap.
  by rewrite /newmap !dom_setf !in_fsetU !in_fset1 eqxx !orbT.
rewrite (bigD1 [` k_new_map ]%fset) //; last first.
  rewrite andTb; apply/andP; split; apply/negP => /eqP a.
    by case/negP: kno; apply/eqP; rewrite -[k]/(val [` k_new_map]%fset) a.
  by case/negP: knp; apply/eqP; rewrite -[k]/(val [` k_new_map]%fset) a.
apply/andP; split.
   have valk : newmap.[k_new_map] = V.
   rewrite/newmap ffunE -[X in X == _]/k (negbTE kno) fnd_set.
   by rewrite -[X in X == _]/k (negbTE knp) fnd_set eqxx.
   rewrite valk /V nxtK prvK; apply/andP; split; first (apply/andP; split).
      by rewrite /newmap fnd_set eqxx /oapp /V3 /old_nxt_values e_tlK e_hdK.
    rewrite /newmap fnd_set.
    rewrite (_ : (val old_prv == val old_nxt) = false); last first.
      apply/negP=> /eqP/val_inj/eqP a; case/negP: base.
      by rewrite eq_sym.
    by rewrite fnd_set eqxx /oapp /V2 nxtK.
  by rewrite /newmap fnd_set eqxx /oapp /V3 prvK.
(* Now handling the general case. *)
rewrite big_andE; apply/forallP => x; apply/implyP.
rewrite andTb => /andP [] /andP [] xno' xnp' xnk'.
have vxk : val x == k = false.
  by apply/negP => /eqP a; case/negP: xnk'; apply/eqP/val_inj.
have xnewmap : val x \in (domf newmap `\ k)%fset.
  by rewrite 2!in_fsetE vxk (valP x).
have xins1 : val x \in s1.
  have cmpf : (domf s1.[k <- V] `<=` domf s1.[k <- V])%fset  by apply/fsubsetP.
  have on : val old_nxt \in domf s1.[k <- V].
    by rewrite in_fsetU old_nxt_in_s1 orbT.
    apply/(fsubsetP domnew)/xnewmap.
  have xins : val x \in s.
    by move : xins1; rewrite /s1 mem_remf => /andP [].

have vxvo : val x == val old_nxt = false.
  by apply/negP => /eqP a; case/negP: xno'; apply/eqP/val_inj.
have vxvp : val x == val old_prv = false.
  by apply/negP => /eqP a; case/negP: xnp'; apply/eqP/val_inj.
have valxx : val x = val [`xins]%fset by [].
have xnne : val x != val ne.
  apply/negP => xne; move: xins1; rewrite /s1 mem_remf xins andbT.
  by rewrite in_fsetU !in_fset1 xne orbT.
have xnpe : val x != val pointing_edge.
  apply/negP => xpe; move: xins1; rewrite /s1 mem_remf xins andbT.
  by rewrite in_fsetU !in_fset1 xpe.
have vnewmap : (newmap x) = s [` xins]%fset.
  rewrite /newmap ffunE vxvo fnd_set vxvp fnd_set vxk /fnd.
    rewrite (insubT [pred x | x \in domf s1] xins1) -[X in X = _]/(s1.[xins1]).
    by rewrite getf_restrict.
have nxtxs : nxt s.[xins] \in s by apply: fnxt_aux.
have prvxs : prv s.[xins] \in s by apply: fprv_aux.
have prvxnne : prv s.[xins] != val ne.
  apply/negP => /eqP a.
  case/negP:vxvo; apply/eqP; rewrite valxx; congr val; apply: fprv_inj => //.
  by rewrite /old_nxt fprvK //; apply val_inj.
have nxtxnne : nxt s.[xins] != val ne.
  apply/negP => /eqP a.
  case/negP: xnpe; apply/eqP; rewrite valxx; congr val.
  by apply/(fnxt_inj _ _ sp2)/val_inj.
have prvxnpe : prv s.[xins] != val pointing_edge.
  apply/negP => /eqP a.
  case/negP: xnne; apply/eqP; rewrite valxx; congr val.
  by apply/fprv_inj => //; rewrite /ne fprvK //; apply/val_inj.
have nxtxnpe : nxt s.[xins] != val pointing_edge.
  apply/negP => /eqP a.
  case/negP:vxvp; apply/eqP; rewrite valxx /old_prv; congr val.
  by apply/(fnxt_inj _ _ sp2); rewrite fnxtK //; apply val_inj.

have nxtxs1 : nxt s.[xins] \in s1.
  by rewrite /s1 mem_remf nxtxs andbT in_fsetU !in_fset1 (negbTE nxtxnpe)
       (negbTE nxtxnne).
have prvxs1 : prv s.[xins] \in s1.
  by rewrite /s1 mem_remf prvxs andbT in_fsetU !in_fset1 (negbTE prvxnpe)
       (negbTE prvxnne).

have nxtxno : nxt s.[xins] == val old_nxt = false.
  apply/negP => /eqP nxo; case/negP: xnne; apply/eqP.
  by rewrite valxx; congr val; apply/(fnxt_inj _ _ sp2)/val_inj.
have prvxnp : prv s.[xins] == val old_prv = false.
  apply/negP => /eqP nxp; case/negP: xnpe; apply/eqP.
  by rewrite valxx; congr val; apply/(fprv_inj _ _ sp2)/val_inj.
have nxtxnk : nxt s.[xins] == k = false.
  apply/negP => /eqP nxk.
  by case/negP: (newnameP (domf s1)); rewrite -/k -nxk.
have prvxnk : prv s.[xins] == k = false.
  apply/negP => /eqP pxk.
  by case/negP: (newnameP (domf s1)); rewrite -/k -pxk.
move/implyP: (s2' [` xins]%fset) => a; move: (a (erefl _)).
move => {a} /andP [] /andP [] point_cond nxtlk prvlk.
rewrite vnewmap; apply/andP; split; first (apply/andP; split).
    rewrite /newmap fnd_set nxtxno fnd_set.
    case nxtxp : (nxt s.[xins] == val old_prv).
      rewrite /oapp /V2 e_tlK (eqP point_cond).
      rewrite (_ : fnxt s sp [` xins]%fset = old_prv) => //.
      by apply/val_inj; rewrite -(eqP nxtxp).
    rewrite fnd_set nxtxnk /fnd.
    rewrite (insubT [pred x | x \in domf s1] nxtxs1).
    rewrite /omap /obind /oapp getf_restrict (eqP point_cond).
    by rewrite (_ : fnxt s sp [`xins]%fset = [`nxtxs]%fset) //; apply/val_inj.
  rewrite /newmap fnd_set.  
  case prvxn : (prv s.[xins] == val old_nxt).
    rewrite /oapp /V3 nxtK /old_nxt_values.
    rewrite -[nxt _]/(val (fnxt s sp old_nxt)) -[val x]/(val [`xins]%fset).
    apply/eqP; congr val; apply/(fprv_inj _ _ sp2)/val_inj.
    by rewrite fprvK // -(eqP prvxn).
  rewrite fnd_set prvxnp fnd_set prvxnk /fnd.
  rewrite (insubT [pred x | x \in domf s1] prvxs1).
  rewrite /omap /obind /oapp getf_restrict.

  rewrite -[nxt _]/(val (fnxt s sp [`prvxs]%fset)) -[val x]/(val [`xins]%fset).
    apply/eqP; congr val; apply/(fprv_inj _ _ sp2)/val_inj.
    by rewrite fprvK // -(eqP prvxn).
rewrite /newmap fnd_set nxtxno fnd_set.

case nxtxp : (nxt s.[xins] == val old_prv).
  rewrite /oapp /V2 prvK /old_prv_values.
  rewrite -[prv _]/(val (fprv s sp old_prv)) -[val x]/(val [`xins]%fset).      
  apply/eqP; congr val; apply/(fnxt_inj _ _ sp2)/val_inj.
  by rewrite fnxtK // -(eqP nxtxp).
rewrite fnd_set nxtxnk /fnd.
rewrite (insubT [pred x | x \in domf s1] nxtxs1).
rewrite /omap /obind /oapp getf_restrict.
rewrite [prv _]/(val (fprv s sp [`nxtxs]%fset)) -[val x]/(val [`xins]%fset).
apply/eqP; congr val; apply/(fnxt_inj _ _ sp2)/val_inj.
by rewrite fnxtK.
Qed.

End ch.
