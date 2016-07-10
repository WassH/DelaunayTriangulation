From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssrnum matrix mxalgebra.

Require Import finmap.

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

Lemma new_nameP e : newname e \notin e.
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

Definition fnxt s (sp : edgemapprop s) (x : {: domf s}) : {:domf s} :=
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

Lemma fnxtK s sp (sp2 : edgemapprop2 s sp) : cancel (fnxt s sp) (fprv s sp).
Proof.
move => x; apply/eqP; move: sp2.
rewrite /edgemapprop2 big_andE => /forallP /= sp2.
by case/andP: (sp2 x) => /andP [].
Qed.

Lemma fprvK s sp (sp2 : edgemapprop2 s sp) : cancel (fprv s sp) (fnxt s sp).
Proof.
move => x; apply/eqP; move: sp2.
rewrite /edgemapprop2 big_andE => /forallP /= sp2.
by case/andP: (sp2 x) => /andP [].
Qed.

Definition initial (p1 p2 : point) : {fmap E -> point ^ 2 * E ^ 2} :=
  nosimpl [fmap].[0 <- mk_edge p1 p2 1 1].[1 <- mk_edge p2 p1 0 0].

Lemma initialP (p1 p2 : point) (df : p1 != p2) : edgemapprop (initial p1 p2).
Proof.
have m0 : 0 \in initial p1 p2 by rewrite !in_fsetE.
have m1 : 1 \in initial p1 p2 by rewrite !in_fsetE.
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
apply/andP; split; (apply/andP; split;[apply/andP;split | ]);
 try (by apply/eqP/val_inj; rewrite /fnxt /fprv /initial /= 
       !(FmapE.fmapE, ffunE) /= !(FmapE.fmapE, ffunE, prvK, nxtK)).
  by rewrite !ffunE e_hdK /fnxt /= !ffunE nxtK FmapE.fmapE e_tlK.
by rewrite !ffunE /fnxt /= !(ffunE, FmapE.fmapE, nxtK, e_hdK, e_tlK).
Qed.

(* both pointing_edge and its successor are removed.  A new edge is created
   to connect the tail of pointing_edge and the head of its successor.
   the map we obtain does not satify the invariants anymore *)
Definition remove_point s
  (sp : edgemapprop s) (sp2 : edgemapprop2 _ sp) 
  (pointing_edge : {: domf s}) : {fmap E -> point ^ 2 * E ^ 2} :=
  let edge_values := s pointing_edge in
  let p1 := e_tl edge_values in
  let p2 := e_hd edge_values in
  let ne := fnxt _ sp pointing_edge in
  let old_prv := fprv _ sp pointing_edge in
  let old_prv_values := s old_prv in
  let old_nxt := fnxt _ sp (fnxt _ sp pointing_edge) in
  let old_nxt_values := s old_nxt in
  let s1 := s.[\ ([fset (val pointing_edge)] `|` [fset (val ne) ])%fset] in
  let k := newname (domf s1) in
  s1.[k <- mk_edge p2 p1 (val old_nxt) (val old_prv)]
    .[val old_prv <- mk_edge (e_hd old_prv_values) (e_tl old_prv_values)
                    k (prv old_prv_values)]
    .[val old_nxt <- mk_edge (e_hd old_prv_values) (e_tl old_prv_values)
                    (nxt old_nxt_values) k].

Lemma remove_pointP (s : {fmap E -> point ^ 2 * E ^ 2})
 sp sp2 (pointing_edge : {: domf s}) :
  fprv _ sp pointing_edge != fnxt _ sp pointing_edge ->
  edgemapprop (remove_point s sp sp2 pointing_edge).
Proof.
(*
move => at_least_three; rewrite /remove_point.
set edge_values := s [` pe ]%fset.
set p1 := e_tl edge_values.
set p2 := e_hd edge_values.
set ne := nxt edge_values.
set old_prv := prv edge_values.
set old_prv_values := s [` prvP _ sp [` pe ]]%fset.
set old_nxt := nxt (s [` nxtP _ sp [` pe ] ]%fset).
set old_nxt_values := s [` nxtP _ sp [` nxtP _ sp [` pe ] ] ]%fset.
set s1 := s.[\ ([fset pointing_edge] `|` [fset ne ])%fset].
set k := newname (domf s1).
set newmap := _.[_ <- _].
have old_nxt_new_map : old_nxt \in domf newmap.
  by rewrite /newmap dom_setf inE in_fsetE eqxx.
rewrite /edgemapprop.
rewrite (bigD1 [` old_nxt_new_map ]%fset) //; apply /andP; split.
  apply /andP; split.
  rewrite /newmap ffunE eqxx nxtK.
  rewrite /newmap ffunE eqxx /nxt ffunE eqxx /old_prv_values /=.
  rewrite /old_nxt_values /=.
have : s.[prvP s sp [` pe]%fset].2 (@Ordinal 2 0 (erefl true)) = 1.
rewrite (bigD1 [` pe]%fset pe).
  by move => [ [ | [ | x]] /= _] ; rewrite ?andbF //= !in_fsetE.
*)