Require Import Arith.
Require Import EqNat.
Require Import Ring.



(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq fintype.
From mathcomp Require Import finset zmodp matrix bigop ssralg matrix ssrnum.
From mathcomp Require Import finmap seq ssrfun finfun matrix ssrnum ssrfun.
From mathcomp Require Import bigop ssralg finset fingroup zmodp poly fingraph.
From mathcomp Require Import tuple choice path perm.
(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Import GRing.

Definition p012 : injective [ffun i : 'I_3 => nth i 
               [:: @Ordinal 3 0 isT ; @Ordinal 3 1 isT; @Ordinal 3 2 isT] i].
Proof.
by move => [[ | [ | [ | n]]] n3] [[ | [ | [ | m]]] m3];
  rewrite !ffunE //= => h; apply: val_inj.
Qed.

Definition p021 : injective [ffun i : 'I_3 => nth i
              [:: @Ordinal 3 0 isT ; @Ordinal 3 2 isT; @Ordinal 3 1 isT] i].
Proof.
by move => [[ | [ | [ | n]]] n3]
  [[ | [ | [ | m]]] m3];
  rewrite !ffunE //= => h; apply: val_inj.
Qed.

Definition p102 : injective [ffun i : 'I_3 => nth i 
              [:: @Ordinal 3 1 isT ; @Ordinal 3 0 isT; @Ordinal 3 2 isT] i].
Proof.
by move => [[ | [ | [ | n]]] n3]
  [[ | [ | [ | m]]] m3];
  rewrite !ffunE //= => h; apply: val_inj.
Qed.

Definition p120 : injective [ffun i : 'I_3 => nth i
              [:: @Ordinal 3 1 isT ; @Ordinal 3 2 isT; @Ordinal 3 0 isT] i].
Proof.
by move => [[ | [ | [ | n]]] n3]
  [[ | [ | [ | m]]] m3];
  rewrite !ffunE //= => h; apply: val_inj.
Qed.

Definition p201 : injective [ffun i : 'I_3 => nth i
              [:: @Ordinal 3 2 isT ; @Ordinal 3 0 isT; @Ordinal 3 1 isT] i].
Proof.
by move => [[ | [ | [ | n]]] n3]
  [[ | [ | [ | m]]] m3];
  rewrite !ffunE //= => h; apply: val_inj.
Qed.

Definition p210 : injective [ffun i : 'I_3 => nth i 
              [:: @Ordinal 3 2 isT ; @Ordinal 3 1 isT; @Ordinal 3 0 isT] i].
Proof.
by move => [[ | [ | [ | n]]] n3]
  [[ | [ | [ | m]]] m3];
  rewrite !ffunE //= => h; apply: val_inj.
Qed.

Lemma second_value (s : {perm 'I_3}) (j : 'I_3) :
  val j != s (@Ordinal 3 0 isT) ->
  (s (@Ordinal 3 1 isT) == j) = false ->
  nat_of_ord (s (@Ordinal 3 1 isT)) = (3 - (s (@Ordinal 3 0 isT) + j))%nat.
Proof.
move => js0 hf.
set w1 := (LHS); case h1 : w1 => [ | [ | [ | m]]];
 set w0 := (nat_of_ord _); case h0 : w0 => [ | [ | [ | n]]]; try (
suff : @Ordinal 3 0 isT = @Ordinal 3 1 isT;[ done |
   by apply/(@perm_inj _ s)/val_inj; have : w0 = w1 by rewrite h1]); try (
by have := ltn_ord (s (@Ordinal 3 1 isT)); rewrite [X in (X < 3)%N]h1); try (
by have := ltn_ord (s (@Ordinal 3 0 isT)); rewrite [X in (X < 3)%N]h0);
(case hj : j js0 hf => [[ | [ | [ | nj]]] pj]; [ | | | done]); try (
move => _ /eqP abs; case: abs; apply: val_inj => /=; exact: h1); try (
by move => /eqP abs; case: abs => /=; rewrite -[LHS]h0);
by rewrite /=.
Qed.

Lemma last_value (s : {perm 'I_3}) :
  nat_of_ord (s (@Ordinal 3 2 isT)) =
     (3 - (s (@Ordinal 3 0 isT) + s (@Ordinal 3 1 isT)))%nat.
Proof.
case h0 : (s (@Ordinal 3 0 isT)) => [[ | [ | [ | n]]] p0]; [ | | | done];
(case h1 : (s (@Ordinal 3 1 isT)) => [[ | [ | [ | n1]]] p1]; [ | | | done]); try
(suff : @Ordinal 3 0 isT = @Ordinal 3 1 isT;[done |apply/(@perm_inj _ s); 
   rewrite h1 h0; apply val_inj; done ]);
(case h2 : (s (@Ordinal 3 2 isT)) => [[ | [ | [ | n2]]] p2]; [ | | | done]); try
(suff : @Ordinal 3 0 isT = @Ordinal 3 2 isT;[done |apply/(@perm_inj _ s); 
   rewrite h2 h0; apply val_inj; done ]); try
(suff : @Ordinal 3 1 isT = @Ordinal 3 2 isT;[done |apply/(@perm_inj _ s); 
   rewrite h2 h1; apply val_inj; done ]); by [].
Qed.

Lemma all_perms3 (s : {perm 'I_3}) :
  s \in [:: perm p012 ; perm p021 ; perm p102 ; perm p120 ; perm p201 ; perm p210 ].
Proof.
case h00 : (s (@Ordinal 3 0 isT) == @Ordinal 3 0 isT).
  case h11 : (s (@Ordinal 3 1 isT) == @Ordinal 3 1 isT).
    rewrite in_cons; apply /orP; left.
    apply/eqP/permP; case => [[ | [ | [ | x ]]] x3]; last by [].
        have -> : Ordinal x3 = @Ordinal 3 0 isT  by apply: val_inj.
        by rewrite (eqP h00) /= permE ffunE /=.
      have -> : Ordinal x3 = @Ordinal 3 1 isT  by apply: val_inj.
      by rewrite (eqP h11) /= permE ffunE /=.
   have q2 : Ordinal x3 = @Ordinal 3 2 isT  by apply: val_inj.
   apply/val_inj; rewrite q2 [LHS]last_value.
   by rewrite permE ffunE /= (eqP h00) (eqP h11).
  have h12 : (s (@Ordinal 3 1 isT) == @Ordinal 3 2 isT).
    apply/eqP/val_inj => /=.
    by rewrite (second_value _ h11) // (eqP h00).
  rewrite 2!in_cons; do 1 (apply/orP; right); apply/orP; left.
  apply/eqP/permP; case => [[ | [ | [ | x ]]] x3]; last by [].
      have -> : Ordinal x3 = @Ordinal 3 0 isT  by apply: val_inj.
      by rewrite (eqP h00) /= permE ffunE /=.
    have -> : Ordinal x3 = @Ordinal 3 1 isT  by apply: val_inj.
    by rewrite (eqP h12) /= permE ffunE /=.
  have q2 : Ordinal x3 = @Ordinal 3 2 isT  by apply: val_inj.
  apply/val_inj; rewrite q2 [LHS]last_value.
  by rewrite permE ffunE /= (eqP h00) (eqP h12).
case h01 : (s (@Ordinal 3 0 isT) == @Ordinal 3 1 isT).
  case h10 : (s (@Ordinal 3 1 isT) == @Ordinal 3 0 isT).
  rewrite 3!in_cons; do 2 (apply/orP; right); apply/orP; left.
    apply/eqP/permP; case => [[ | [ | [ | x ]]] x3]; last by [].
        have -> : Ordinal x3 = @Ordinal 3 0 isT  by apply: val_inj.
        by rewrite (eqP h01) /= permE ffunE /=.
      have -> : Ordinal x3 = @Ordinal 3 1 isT  by apply: val_inj.
      by rewrite (eqP h10) /= permE ffunE /=.
   have q2 : Ordinal x3 = @Ordinal 3 2 isT  by apply: val_inj.
   apply/val_inj; rewrite q2 [LHS]last_value.
   by rewrite permE ffunE /= (eqP h01) (eqP h10).
  have h12 : (s (@Ordinal 3 1 isT) == @Ordinal 3 2 isT).
    apply/eqP/val_inj => /=.
    by rewrite (second_value _ h10) // (eqP h01).
  rewrite 4!in_cons; do 3 (apply/orP; right); apply/orP; left.
  apply/eqP/permP; case => [[ | [ | [ | x ]]] x3]; last by [].
      have -> : Ordinal x3 = @Ordinal 3 0 isT  by apply: val_inj.
      by rewrite (eqP h01) /= permE ffunE /=.
    have -> : Ordinal x3 = @Ordinal 3 1 isT  by apply: val_inj.
    by rewrite (eqP h12) /= permE ffunE /=.
  have q2 : Ordinal x3 = @Ordinal 3 2 isT  by apply: val_inj.
  apply/val_inj; rewrite q2 [LHS]last_value.
  by rewrite permE ffunE /= (eqP h01) (eqP h12).
have h02 : s (@Ordinal 3 0 isT) == @Ordinal 3 2 isT.
  by case : (s (@Ordinal 3 0 isT)) h00 h01 => [[ | [ | [ | n]]] pn]
   /eqP h00 /eqP h01;
  try (by case : h00; apply: val_inj); try (by case : h01; apply: val_inj).
case h10 : (s (@Ordinal 3 1 isT) == @Ordinal 3 0 isT).
rewrite 5!in_cons; do 4 (apply/orP; right); apply/orP; left.
  apply/eqP/permP; case => [[ | [ | [ | x ]]] x3]; last by [].
      have -> : Ordinal x3 = @Ordinal 3 0 isT  by apply: val_inj.
      by rewrite (eqP h02) /= permE ffunE /=.
    have -> : Ordinal x3 = @Ordinal 3 1 isT  by apply: val_inj.
    by rewrite (eqP h10) /= permE ffunE /=.
  have q2 : Ordinal x3 = @Ordinal 3 2 isT  by apply: val_inj.
  apply/val_inj; rewrite q2 [LHS]last_value.
  by rewrite permE ffunE /= (eqP h02) (eqP h10).
have h11 : (s (@Ordinal 3 1 isT) == @Ordinal 3 1 isT).
  apply/eqP/val_inj => /=.
  by rewrite (second_value _ h10) // (eqP h02).
rewrite 6!in_cons; do 5 (apply/orP; right); apply/orP; left.
apply/eqP/permP; case => [[ | [ | [ | x ]]] x3]; last by [].
    have -> : Ordinal x3 = @Ordinal 3 0 isT  by apply: val_inj.
    by rewrite (eqP h02) /= permE ffunE /=.
  have -> : Ordinal x3 = @Ordinal 3 1 isT  by apply: val_inj.
  by rewrite (eqP h11) /= permE ffunE /=.
have q2 : Ordinal x3 = @Ordinal 3 2 isT  by apply: val_inj.
apply/val_inj; rewrite q2 [LHS]last_value.
by rewrite permE ffunE /= (eqP h02) (eqP h11).
Qed.

Lemma odd_perm012 : perm p012 = false :> bool.
Proof.
suff -> : perm p012 = 1%g by apply: odd_perm1.
by (apply/permP; case => [ [ | [ | [ | n]]] pn]; [ | | | done]);
  rewrite !permE !ffunE /=; apply val_inj => /=.
Qed.

Lemma odd_perm021 : perm p021 = true :> bool.
Proof.
rewrite [perm _](_ : _ = (tperm (@Ordinal 3 1 isT) (@Ordinal 3 2 isT))); last first.
  (apply/permP; case => [ [ | [ | [ | n]]] pn]; [ | | | done]);
   rewrite !permE !ffunE; apply/val_inj => /=;
   try (rewrite (_ : Ordinal pn = @Ordinal 3 0 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 1 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 2 isT);[ | by apply: val_inj]);
   rewrite ?(tpermL, tpermR) //.
by apply: odd_tperm.
Qed.

Lemma odd_perm102 : perm p102 = true :> bool.
Proof.
rewrite [perm _](_ : _ = (tperm (@Ordinal 3 0 isT) (@Ordinal 3 1 isT))); last first.
  (apply/permP; case => [ [ | [ | [ | n]]] pn]; [ | | | done]);
   rewrite !permE !ffunE; apply/val_inj => /=;
   try (rewrite (_ : Ordinal pn = @Ordinal 3 0 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 1 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 2 isT);[ | by apply: val_inj]);
   rewrite ?(tpermL, tpermR) //.
by apply: odd_tperm.
Qed.

Lemma odd_perm120 : perm p120 = false :> bool.
Proof.
rewrite [perm _](_ : _ = (tperm (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) *
                       tperm (@Ordinal 3 0 isT) (@Ordinal 3 2 isT))%g); last first.
  (apply/permP; case => [ [ | [ | [ | n]]] pn]; [ | | | done]);
   rewrite !permE !ffunE; apply/val_inj => /=;
   try (rewrite (_ : Ordinal pn = @Ordinal 3 0 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 1 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 2 isT);[ | by apply: val_inj]);
   rewrite ?(tpermL, tpermR) //.
   by rewrite tpermD.
  by rewrite [X in (tperm _ _) X]tpermD // tpermR.
by rewrite odd_permM !odd_tperm.
Qed.

Lemma odd_perm210 : perm p210 = true :> bool.
Proof.
rewrite [perm _](_ : _ = (tperm (@Ordinal 3 0 isT) (@Ordinal 3 2 isT))); last first.
  (apply/permP; case => [ [ | [ | [ | n]]] pn]; [ | | | done]);
   rewrite !permE !ffunE; apply/val_inj => /=;
   try (rewrite (_ : Ordinal pn = @Ordinal 3 0 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 1 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 2 isT);[ | by apply: val_inj]);
   rewrite ?(tpermL, tpermR) //.
by apply: odd_tperm.
Qed.

Lemma odd_perm201 : perm p201 = false :> bool.
Proof.
rewrite [perm _](_ : _ = (tperm (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) *
                       tperm (@Ordinal 3 0 isT) (@Ordinal 3 1 isT))%g); last first.
  (apply/permP; case => [ [ | [ | [ | n]]] pn]; [ | | | done]);
   rewrite !permE !ffunE; apply/val_inj => /=;
   try (rewrite (_ : Ordinal pn = @Ordinal 3 0 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 1 isT);[ | by apply: val_inj]);
   try (rewrite (_ : Ordinal pn = @Ordinal 3 2 isT);[ | by apply: val_inj]);
   rewrite ?(tpermL, tpermR) //.
   by rewrite tpermD.
  by rewrite [X in (tperm _ _) X]tpermD // tpermR.
by rewrite odd_permM !odd_tperm.
Qed.

Lemma uniq_size (T: finType) (s t : seq T) :
   uniq s -> {subset s <= t} -> size s = size t -> uniq t.
Proof.
move=> Hu Hs Es; apply/card_uniqP/anti_leq.
rewrite card_size -Es -(_ : #|s| = size s); last by apply: card_uniqP.
apply: subset_leq_card.
by apply/subsetP.
Qed. 

Lemma uniq_perms3 : 
  uniq [:: perm p012; perm p021; perm p102; perm p120; perm p201; perm p210].
Proof.
have h : uniq (Finite.enum [finType of 'S_3]).
  apply: count_mem_uniq => x; rewrite mem_index_enum; apply/enumP.
apply (uniq_size h).
   by move => /= x _; apply: all_perms3.
rewrite /= -enumT -cardT /=.
have := card_perm (setT : {set 'I_3}).
rewrite cardsT /= card_ord; move => h'; rewrite -[RHS]h'.
apply: eq_card; move => i //=; rewrite inE; symmetry.
by apply/subsetP.
Qed.

Lemma expand_det33 (R : ringType) (M : 'M[R]_(3,3)) : \det M = 
  M (@Ordinal 3 0 isT) (@Ordinal 3 0 isT) *
  M (@Ordinal 3 1 isT) (@Ordinal 3 1 isT) *
  M (@Ordinal 3 2 isT) (@Ordinal 3 2 isT) -
  M (@Ordinal 3 0 isT) (@Ordinal 3 0 isT) *
  M (@Ordinal 3 1 isT) (@Ordinal 3 2 isT) *
  M (@Ordinal 3 2 isT) (@Ordinal 3 1 isT) -
  M (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) *
  M (@Ordinal 3 1 isT) (@Ordinal 3 0 isT) *
  M (@Ordinal 3 2 isT) (@Ordinal 3 2 isT) +
  M (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) *
  M (@Ordinal 3 1 isT) (@Ordinal 3 2 isT) *
  M (@Ordinal 3 2 isT) (@Ordinal 3 0 isT) +
  M (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) *
  M (@Ordinal 3 1 isT) (@Ordinal 3 0 isT) *
  M (@Ordinal 3 2 isT) (@Ordinal 3 1 isT) -
  M (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) *
  M (@Ordinal 3 1 isT) (@Ordinal 3 1 isT) *
  M (@Ordinal 3 2 isT) (@Ordinal 3 0 isT).
Proof.
rewrite /determinant.
rewrite (eq_big_perm  [:: perm p012 ; perm p021 ; perm p102 ; perm p120 ;
                          perm p201 ; perm p210 ]).
  rewrite !big_cons big_nil/= addr0 !addrA odd_perm012 odd_perm021 odd_perm102
           odd_perm120 odd_perm210 odd_perm201.
  rewrite !big_ord_recl /= !big_ord0 expr0 expr1 !mulNr !mul1r !mulr1 !mulrA.
  rewrite (_ : ord0 = @Ordinal 3 0 isT); last by apply: val_inj.
  set w := (lift _ (ord0 : 'I_3.-1)).
  have -> : w = @Ordinal 3 1 isT by apply: val_inj.
  set w2 := (lift _ (lift _ _)).
  have -> : w2 = @Ordinal 3 2 isT by apply: val_inj.
  by rewrite !permE !ffunE.
apply uniq_perm_eq.  
    by apply: count_mem_uniq => x; rewrite mem_index_enum; apply/enumP.
  by apply: uniq_perms3.
by  move => s; rewrite mem_index_enum all_perms3.
Qed.
