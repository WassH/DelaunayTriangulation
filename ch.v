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

Record edge_state := {
  head : point;
  tail : point;
  next : E;
  prev : E
}.

Definition e_hd (e : point ^ 2 * E ^ 2) :=
  fst e (Ordinal ((erefl true) : 0 < 2)).

Definition e_tl (e : point ^ 2 * E ^ 2) :=
  fst e (Ordinal ((erefl true) : 1 < 2)).

Definition nxt (e : point ^ 2 * E ^ 2) :=
  snd e (Ordinal ((erefl true) : 0 < 2)).

Definition prv (e : point ^ 2 * E ^ 2) :=
  snd e (Ordinal ((erefl true) : 1 < 2)).

Definition state := {fmap E -> edge_state}.

Definition edgemapprop (s : {fmap E -> point ^ 2 * E ^ 2}) :=
(* [forall (x : {: domf s} | true ) *)
\big[andb/true]_(x : {: domf s})
     ((e_hd (s x) != e_tl (s x)) &&
      (nxt (s x) \in s) && (prv (s x) \in s)) (* ] *).

Lemma prvP s (h : edgemapprop s) : forall (x : {: domf s}), prv (s x) \in s.
Proof.
move: h; rewrite /edgemapprop big_andE; move/forallP => /= h x.
by move/andP: (h x) => [] /andP [].
Qed.

Lemma nxtP s (h : edgemapprop s) : forall (x : {: domf s}), nxt (s x) \in s.
Proof.
move: h; rewrite /edgemapprop big_andE; move/forallP => /= h x.
by move/andP: (h x) => [] /andP [].
Qed.

Definition edgemapprop2 (s : {fmap E -> point ^ 2 * E ^ 2}) (mp1 : edgemapprop s) :=
  \big[andb/true]_(i : {: domf s}) ((e_hd (s i) == e_tl (s.[nxtP s mp1 i])) &&
     (e_tl (s i) == e_hd (s.[prvP s mp1 i])) &&
     (nxt (s.[prvP s mp1 i]) == val i) && (prv (s.[nxtP s mp1 i]) == val i)).

Definition initial (p1 p2 : point) : {fmap E -> point ^ 2 * E ^ 2} :=
  ([fmap].[0 <- ([ffun x => if nat_of_ord x == 0 then p1 else p2],[ffun _ => 1])])
    .[1 <-([ffun x => if nat_of_ord x == 0 then p2 else p1],[ffun _ => 0])].

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
rewrite (bigD1 [` m0]%fset  m0') big_pred0; last first.
  by move => [ [ | [ | x]] /= _] ; rewrite ?andbF //= !in_fsetE.
(* I think the next proof would be easier if I knew how to write a finfun
  in a more systematic way. *)
set u := initial p1 p2; set v := u.[m0].
have v2 : v.2 = [ffun _ => 1]
    by rewrite /v /u /initial ffunE FmapE.fmapE eqxx.
apply/andP; split;[ | apply/andP; split;[ | done]];
 (apply/andP; split;[apply/andP;split | ]);
  try solve [rewrite /e_hd /e_tl /nxt /prv !ffunE //=].
      by rewrite /e_hd /e_tl !ffunE /= eq_sym.
(* Here fnd_set was found in FmapE.fmapE *)
    by rewrite /e_hd /e_tl /v /u !ffunE fnd_set eqxx /= !ffunE /=.
  by rewrite /nxt v2 ffunE.
by rewrite /prv v2 ffunE.
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
rewrite (bigD1 _ m1').
have m0' : (val [` m0 ]%fset \in (1 |` (0 |` fset0))%fset) &&
           ([` m0 ]%fset != [` m1 ]%fset) by rewrite !inE.
rewrite (bigD1 [` m0]%fset  m0') big_pred0; last first.
  by move => [ [ | [ | x]] /= _] ; rewrite ?andbF //= !in_fsetE.
set u1 := _ [` m1 ]%fset; set u0 := _ [` m0 ]%fset.
set v1 := nxtP _ _ [` m1]%fset; set w1 := prvP _ _ [` m1 ]%fset.
set v0 := nxtP _ _ [` m0]%fset; set w0 := prvP _ _ [` m0 ]%fset.
have v1v : nxt u1 = 0   by rewrite /u1 /nxt ffunE eqxx ffunE.
have w1v : prv u1 = 0   by rewrite /u1 /prv ffunE eqxx ffunE.
have v1v' : val [` v1]%fset = 0 by rewrite /v1 /= v1v.
have w1v' : val [` w1]%fset = 0 by rewrite /w1 /= w1v.
have v0v : nxt u0 = 1   by rewrite /u0 /nxt ffunE fnd_set eqxx ffunE.
have w0v : prv u0 = 1   by rewrite /u0 /prv ffunE fnd_set eqxx ffunE.
have v0v' : val [` v0]%fset = 1 by rewrite /v0 /= v0v.
have w0v' : val [` w0]%fset = 1 by rewrite /w0 /= w0v.
apply/andP; split;[ | apply/andP; split;[ | done]];
 (apply/andP; split;[apply/andP;split | ]).
apply /andP; split.
by rewrite /v1 ffunE /= v1v fnd_set /= /u1 /initial /e_hd /e_tl !ffunE eqxx.
by rewrite /w1 ffunE /= w1v fnd_set /= /u1 /initial /e_hd /e_tl !ffunE eqxx.
by rewrite ffunE w1v' fnd_set /= /nxt ffunE.
by rewrite ffunE v1v' fnd_set /= /prv ffunE.
apply /andP; split.
by rewrite /v0 ffunE /= v0v fnd_set /u0 /initial /e_hd /e_tl !ffunE fnd_set ffunE.
by rewrite /w0 ffunE /= w0v fnd_set /u0 /initial /e_hd /e_tl !ffunE fnd_set ffunE.
by rewrite ffunE w0v' fnd_set /= /nxt ffunE.
by rewrite ffunE v0v' fnd_set /= /prv ffunE.
Qed.
