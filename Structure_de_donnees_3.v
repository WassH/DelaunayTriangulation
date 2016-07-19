Require Import Arith.
Require Import EqNat.
Require Import Ring.



(* -------------------------------------------------------------------- *)
From mathcomp Require Import div ssreflect eqtype ssrbool ssrnat seq finfun matrix ssrnum ssrfun fintype tuple choice path.
From mathcomp Require Import finset zmodp matrix bigop ssralg.
From mathcomp Require Import finmap.
From mathcomp Require Import bigop ssralg finset fingroup zmodp poly fingraph.

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

Axiom modulo : forall i n:nat,  (i%%n)< n.

Definition addOrd2 : 'I_2 -> 'I_2 -> 'I_2 :=
  fun (p q : 'I_2) => Ordinal(modulo (p+q) 2).

Definition addOrd3 : 'I_3 -> 'I_3 -> 'I_3 :=
  fun (p q : 'I_3) => Ordinal(modulo (p+q) 3).

Definition minOrd2 : 'I_2 -> 'I_2 -> 'I_2 :=
  fun (p q : 'I_2) => Ordinal(modulo (p-q) 2).

Definition minrd3 : 'I_3 -> 'I_3 -> 'I_3 :=
  fun (p q : 'I_3) => Ordinal(modulo (p-q) 3).

Definition addOrdn (n:nat) : 'I_n -> 'I_n -> 'I_n :=
  fun (p q : 'I_n) => Ordinal(modulo (p-q) n).


Variable R : numDomainType.
Variable P : finType.
Definition point := 'rV[R]_2.

Definition point2R1 (p: point) : R :=
  p (Ordinal zero<1) (Ordinal(zero<2)).


Definition point2R2 (p: point) : R :=
  p (Ordinal zero<1) (Ordinal(un<2)).


Open Local Scope type_scope.
Definition T := P^3 .


(* Tous les triangles sur lesquels nous allons travailler seront 
un triplet de points donnés dans le sens trigo *)
Definition triangle :=  point^3.

Variable tnull : triangle.

Definition trianglemap := {ffun T -> triangle}.
Definition pointmap := {ffun P -> point}.

Definition point2namefun : point -> pointmap -> option P :=
 fun (p1 : point) (pm : pointmap) => let S := [fset i in P | (pm i ==p1)]%fset in
 if #|S| !=0  then [pick i | i \in S]
 else None.


(* s va etre l'ensemble des points dans la triangulation *)
Variable s: {set P}.


(* graph est une fonction qui à un nom de triangle associe la liste des noms de triangles qui 
lui sont adjacents *)
Definition graph := T-> seq T.


Definition triangle2points (t: T) (tm : trianglemap) : {ffun 'I_3 -> point}  :=
  [ffun Ord : 'I_3 => (tm t) Ord].


(*adjT dit si 2 triangles sont adjacents*)
Definition adjT (t1: T) (t2: T) (tm : trianglemap) : bool :=
  if [exists (i1 : 'I_3| true), [exists (i2: 'I_3 | true), (triangle2points t1 tm i1 == triangle2points t2 tm i2) && 
     [exists (i3 : 'I_3|true), [exists (i4 : 'I_3 | true), (triangle2points t1 tm i3 == triangle2points t2 tm i4) && (i1!=i3) && (i2!=i4)]]]]
                   then true
  else false.



Open Local Scope ring_scope.

(* Définition de inCircle, RMQ : si un point est sur le cercle circonscrit alors il n'est pas inCircle *)
Definition inCircle (p1 : point) (t1: T) (tm : trianglemap) : bool :=
  let M1 := \col_(j < 4) if j==0 then point2R1 (triangle2points t1 tm (Ordinal (zero<3)))
                         else if  j==1 then point2R1 (triangle2points t1 tm (Ordinal (un<3)))
                         else if  nat_of_ord j==2 then point2R1 (triangle2points t1 tm (Ordinal (deux<3)))
                         else point2R1 p1 in
  let M2 := \col_(j < 4) if j==0 then point2R2 (triangle2points t1 tm (Ordinal (zero<3)))
                         else if  j==1 then point2R2 (triangle2points t1 tm (Ordinal (un<3)))
                         else if  nat_of_ord j==2 then point2R2 (triangle2points t1 tm (Ordinal (deux<3)))
                         else point2R2 p1 in
  let M3 := \col_(j < 4) if j==0 then (point2R1 (triangle2points t1 tm (Ordinal (zero<3))))^+2 + (point2R2 (triangle2points t1 tm (Ordinal (zero<3))))^+2
                         else if j==1 then (point2R1 (triangle2points t1 tm (Ordinal (un<3))))^+2 + (point2R2 (triangle2points t1 tm (Ordinal (un<3))))^+2
                         else if  nat_of_ord j==2 then (point2R1 (triangle2points t1 tm (Ordinal (deux<3))))^+2 + (point2R2 (triangle2points t1 tm (Ordinal (deux<3))))^+2
                         else (point2R1 p1)^+2 + (point2R2 p1)^+2 in
  let M4 := \col_(j < 4) 1 in
  let M := row_mx (row_mx M1 M2) (row_mx M3 M4) in if \det M > 0 then true else false.



(* La fonction isDelaunayLocal va prendre 2 triangles et va renvoyer un bool qui vaudra true si
 la construction des 2 triangles est de Delauney *)
Definition isDelaunayLocal (t1: T) (t2: T)  (tm : trianglemap) : bool :=
  if (inCircle (triangle2points t1 tm (Ordinal (zero<3))) t2 tm == false
      && inCircle (triangle2points t1 tm (Ordinal (un<3))) t2 tm== false
      && inCircle (triangle2points t1 tm (Ordinal (deux<3))) t2 tm== false)
              then true
              else false.


(* unhookT t va retirer le triangle t de la tmap et va faire que g t = nil *)
Definition unhookT (t1:T) (tm : trianglemap) (g:graph) :=
  let tm' := [ffun i => if i != t1 then tm i else tnull] in
  let g' : T -> seq T := fun i : T => if i != t1 then g i else nil in
  (g', tm).


(* attachT va seulement rajouter un triangle t1 dans la tmap *)
(* Le rajout du nouveau triangle dans le graph sera fait au cas par cas dans les fonctions le nécessitant *)
Definition attachT (t1: triangle) (tm : trianglemap) (pm : pointmap)  := 
  if  point2namefun (t1 (Ordinal(zero<3))) pm is Some i1 then let i1' := i1 in
      if  point2namefun (t1 (Ordinal(un<3))) pm is Some i2 then let i2' := i2 in
          if point2namefun (t1 (Ordinal(deux<3))) pm is Some i3 then let i3' := i3 in
                let tm' :=[ffun i :T => if i != [ffun x : 'I_3 => if x==0 then i1'
                                                                  else if x==1 then i2'
                                                                  else i3']  then tm i else t1] in Some tm'
          else None
      else None
  else None.



(* Fonctions inTriangle, inHull, add_point_triangle, add_point_out, add_edge et add_triangle *)


(* La fonction inTriangle va dire si un point donné est à l'intérieur d'un triangle donné *)
Definition inTriangle (p:point) (t:T) (tm : trianglemap) : bool :=

  let M11 := \col_(j < 3) if j==0 then point2R1 p
                         else if j==1 then point2R1 (triangle2points t tm (Ordinal(zero<3)))
                         else point2R1 (triangle2points t tm (Ordinal(un<3))) in

  let M12 := \col_(j < 3) if j==0 then point2R2 p
                         else if j==1 then point2R2  (triangle2points t tm (Ordinal(zero<3)))
                         else point2R2 (triangle2points t tm (Ordinal(un<3))) in

  let M13 := \col_(j < 3) 1 in 
     let M1 := row_mx (row_mx M11 M12) M13 in

  let M21 := \col_(j < 3) if j==0 then point2R1 p
                         else if j==1 then point2R1(triangle2points t tm (Ordinal(un<3)))
                         else  point2R1 (triangle2points t tm (Ordinal(deux<3))) in

  let M22 := \col_(j < 3) if j==0 then point2R2 p
                         else if j==1 then point2R2 (triangle2points t tm (Ordinal(un<3)))
                         else point2R2  (triangle2points t tm (Ordinal(deux<3))) in

  let M23 := \col_(j < 3) 1 in 
      let M2 := row_mx (row_mx M21 M22) M23 in
  
  let M31 := \col_(j < 3) if j==0 then point2R1 p
                         else if j==1 then point2R1 (triangle2points t tm (Ordinal(deux<3)))
                         else point2R1 (triangle2points t tm (Ordinal(zero<3))) in

  let M32 := \col_(j < 3) if j==0 then point2R2 p
                         else if j==1 then point2R2 (triangle2points t tm (Ordinal(deux<3)))
                         else point2R2 (triangle2points t tm (Ordinal(zero<3))) in

  let M33 := \col_(j < 3) 1 in 
      let M3 := row_mx (row_mx M31 M32) M33 in


    if ((\det M1)*(\det M2)>0) && ((\det M2)*(\det M3) >0)  then true
    else false.



(* La fonction inHull va dire si un point donné est à l'intérieur de l'enveloppe convexe
  dans ce cas elle retourne true ou sinon elle retourne false. Elle est construite 
  grâce à inTriangle*)
Definition inHull (p:point) (tmap : trianglemap) : bool := 
  [exists (i: T| true), inTriangle p i tmap].


(* La fonction ofindtriangle va (si c'est le cas) trouver et retourner un Option T, car 
soit le point est dans l'enveloppe convexe est alors j'ai un Some(i), i étant le nom du triangle et la
preuve qu'il est dans tmap, soit j'ai un None car il est hors enveloppe convexe. *)
(* Cette fonction peut être utilisée pour dire si un point est dans l'enveloppe convexe alors elle retourne
Some u et si il n'y est pas alors elle retourne None *)
Definition ofindtriangle (p:point) (tm : trianglemap)  : option (T) := 
  [pick i: T| inTriangle p i tm].


(* La fonction findtriangle va prendre un argument de plus que ofindtriangle une preuve inHull p ptm,
 que le point est dans l'enveloppe convexe et va savoir retourner un domf tm. *)
Definition findtriangle (p:point) (tm : trianglemap) (h : inHull p tm) : T.
Proof.
case h':(@ofindtriangle p tm) => [ v | ].
  exact: v.
move:h'; rewrite /ofindtriangle.
case: pickP =>//.
move => abs _.
Search in_mem in ssrbool fintype.
elimtype False.
move: h. 
rewrite /inHull.
move/existsP=> []x /= xP.
have := (abs x).
by rewrite xP.
Defined.



(* Fonction qui va supprimer le triangle extérieur et qui va rajouter les 3 triangles intérieurs *)
(* Definition add_point_triangle  (p:point) (t:T) (tm : trianglemap) (g:graph) :=   *)
(* Rajouter le point p à pointmap en utilisant newname ???*)
(* let (tm1,g1):= unhookT t tm g in
  let triangle1 := fun x:'I_3 => if x==0 then tm t (Ordinal(zero<3))
                               else if x==1 then tm t (Ordinal(un<3))
                               else p in
          if attachT triangle1 tm1 is Some tm2' then let tm2 := tm2' in


  let triangle2 := fun x:'I_3 => if x==0 then tm t (Ordinal(un<3))
                               else if x==1 then tm t (Ordinal(deux<3))
                               else p in
           if attachT triangle2 tm2 is Some tm3' then let tm3 := tm3' in


  let triangle3 := fun x:'I_3 => if x==0 then tm t (Ordinal(deux<3))
                               else if x==1 then tm t (Ordinal(zero<3))
                               else p in
            if attachT triangle3 tm3 is Some tm4' then let tm4 := tm4' in

  (* mettre à jour le graph g1 *)

let g' : T -> seq T := fun i :T => 

else None
else None
else None. *)

(* La fonction add_point_out va rajouter les edges et supprimer les edges qu'il faut *)
(* Cette fonction (comme add_point_triangle) sera appliquée dans add_point qui déterminera 
à laquelle de ces deux fonctions il faut faire appel *)
(* Definition add_point_out  (p:point) (tm: trianglemap) (g:graph) := 
  let S := [fset eH \in hu | true] in
  let 
  let S2 := [fset eh \in hu | \det M <0] *)

(* Cette fonction add_point_out sera récursive pour sortir la liste des edges de hull qui sont rouges
ainsi que les deux points extremaux *)
(* Ensuite il faudra créer pour chaque head (ou tail) de ces edges un edge et en plus un edge 
pour la queue du premier. Ensuite il faut créer les triangles *)





(* Fonction add_point globale, qui va faire appel selon les cas à add_point_triangle ou add_point_out *)
(* Definition add_point  (p:point) (tm: trianglemap) (g:graph) := 
  if (inHull p tm) then 
                    let t1 :=findtriangle p tm true in
                    add_point_triangle p t1 tm g
  else add_point_out p tm g.

 *)


Definition change_ord (T : choiceType)(ss : {fset T}) (h : #|{:ss}| == 2) (x : 'I_2)
  : 'I_(#|{:ss}|).
rewrite (eqP h); exact x.
Defined.


Section findIllegal.

Variables (tm : trianglemap) (g:graph).

Let triangleSet := [fset t:P^3 | true]%fset.


Let f := fun x : {:triangleSet} =>
  if g (val x) is t1 :: _ then 

let p0t1:= tm t1 (Ordinal(zero<3)) in
let p1t1:= tm t1 (Ordinal(un<3)) in
let p2t1:= tm t1 (Ordinal(deux<3)) in
let p0t2:= tm (val x) (Ordinal(zero<3)) in
let p1t2:= tm (val x) (Ordinal(un<3)) in
let p2t2:= tm (val x) (Ordinal(deux<3)) in


                                  if isDelaunayLocal (val x) t1 tm==true then None
                                  else if ~~((p0t1 == p0t2) ||(p0t1 == p1t2) ||(p0t1 == p2t2)) && ~~((p0t2 == p0t1) ||(p0t2 == p1t1) ||(p0t2 == p2t1)) then let ptext1 := p0t1 in let ptext2 := p0t2 in Some(ptext1, ptext2, val x, t1)
                                       else if ~~((p0t1 == p0t2) ||(p0t1 == p1t2) ||(p0t1 == p2t2)) && ~~((p1t2 == p0t1) ||(p1t2 == p1t1) ||(p1t2 == p2t1)) then let ptext1 := p0t1 in let ptext2 := p1t2 in Some(ptext1, ptext2, val x, t1)
                                       else if ~~((p0t1 == p0t2) ||(p0t1 == p1t2) ||(p0t1 == p2t2)) && ~~((p2t2 == p0t1) ||(p2t2 == p1t1) ||(p2t2 == p2t1)) then let ptext1 := p0t1 in let ptext2 := p2t2 in Some(ptext1, ptext2, val x, t1)

                                       else if ~~((p1t1 == p0t2) ||(p1t1 == p1t2) ||(p1t1 == p2t2)) && ~~((p0t2 == p0t1) ||(p0t2 == p1t1) ||(p0t2 == p2t1)) then let ptext1 := p1t1 in let ptext2 := p0t2 in Some(ptext1, ptext2, val x, t1)
                                       else if ~~((p1t1 == p0t2) ||(p1t1 == p1t2) ||(p1t1 == p2t2)) && ~~((p1t2 == p0t1) ||(p1t2 == p1t1) ||(p1t2 == p2t1)) then let ptext1 := p1t1 in let ptext2 := p1t2 in Some(ptext1, ptext2, val x, t1)
                                       else if ~~((p1t1 == p0t2) ||(p1t1 == p1t2) ||(p1t1 == p2t2)) && ~~((p2t2 == p0t1) ||(p2t2 == p1t1) ||(p2t2 == p2t1)) then let ptext1 := p1t1 in let ptext2 := p2t2 in Some(ptext1, ptext2, val x, t1)

                                       else if ~~((p2t1 == p0t2) ||(p2t1 == p1t2) ||(p2t1 == p2t2)) && ~~((p0t2 == p0t1) ||(p0t2 == p1t1) ||(p0t2 == p2t1)) then let ptext1 := p2t1 in let ptext2 := p0t2 in Some(ptext1, ptext2, val x, t1)
                                       else if ~~((p2t1 == p0t2) ||(p2t1 == p1t2) ||(p2t1 == p2t2)) && ~~((p1t2 == p0t1) ||(p1t2 == p1t1) ||(p1t2 == p2t1)) then let ptext1 := p2t1 in let ptext2 := p1t2 in Some(ptext1, ptext2, val x, t1)
                                       else let ptext1 := p2t1 in let ptext2 := p2t2 in Some(ptext1, ptext2, val x, t1)

  else None.

Let res := [fset f x | x in {: triangleSet} & f x != None]%fset.

Definition findIllegal := match pick (pred_of_simpl (@predT {:res})) with
   Some u => val u | None => None end.


End findIllegal.

About findIllegal.


(* point2index va prendre un point, un T et va fournir un 'I_3 qui est l'index de l'arete dans ce triangle *)
(* RMQ : Si ce point n'est pas un des 3 sommets du triangle alors la fonction retourne Ordinal(deux<3) *)
Definition point2index (p:point) (t:T) (tmap : trianglemap) : 'I_3 :=
  if (tmap t (Ordinal(zero<3))) == p then Ordinal(zero<3)
  else if (tmap t (Ordinal(un<3))) == p then Ordinal(un<3)
  else Ordinal(deux<3).


Definition flip (tm: trianglemap)  (ptext1 : point) (ptext2 : point) (t1:T) (t2 :T) (g:graph) (pm: pointmap) :=
let p0t1:= tm t1 (Ordinal(zero<3)) in
let p1t1:= tm t1 (Ordinal(un<3)) in
let p2t1:= tm t1 (Ordinal(deux<3)) in
let p0t2:= tm t2 (Ordinal(zero<3)) in
let p1t2:= tm t2 (Ordinal(un<3)) in
let p2t2:= tm t2 (Ordinal(deux<3)) in

if ptext1 == p0t1 then let indexptext1 := (Ordinal(zero<3)) in
else if ptext1 == p1t1 then let indexptext1 := (Ordinal(un<3)) in
else if ptext1 == p2t1 then let indexptext1 := (Ordinal(deux<3)) in
else if ptext1 == p0t2 then let indexptext1 := (Ordinal(zero<3)) in
else if ptext1 == p1t2 then let indexptext1 := (Ordinal(un<3)) in
else then let indexptext1 := (Ordinal(deux<3)) in

if ptext2 == p0t1 then let indexptext2 := (Ordinal(zero<3)) in
else if ptext2 == p1t1 then let indexptext2 := (Ordinal(un<3)) in
else if ptext2 == p2t1 then let indexptext2 := (Ordinal(deux<3)) in
else if ptext2 == p0t2 then let indexptext2 := (Ordinal(zero<3)) in
else if ptext2 == p1t2 then let indexptext2 := (Ordinal(un<3)) in
else then let indexptext2 := (Ordinal(deux<3)) in


let (tm2, g2) := fst unhookT t1 tm g in let (tm3,g3):= unhookT t2 tm2 g2 in


let triangle1 := fun x:'I_3 => if x==0 then if ptext1 == p0t1 || ptext1 == p1t1 || ptext1 == p2t1 then tm3 t1 indexptext1
                                            else tm3 t2 indexptext1
                               else if x==1 then if ptext2 == p0t1 || ptext2 == p1t1 || ptext2 == p2t1 then tm3 t1 indexptext2 
                                            else tm3 t2 indexptext2 
                               else if ptext1 == p0t1 || ptext1 == p1t1 || ptext1 == p2t1 then tm3 t1 addOrd3 indexptext1 2
                                            else tm3 t2 addOrd3 indexptext1 2


in let triangle2 := fun x:'I_3 => if x==0 then if ptext2 == p0t2 || ptext2 == p1t2 || ptext2 == p2t2 then tm3 t2 indexptext2
                                            else tm3 t1 indexptext2
                               else if x==1 then if ptext1 == p0t2 || ptext1 == p1t2 || ptext1 == p2t2 then tm3 t2 indexptext1
                                            else tm3 t1 indexptext1
                               else if ptext2 == p0t2 || ptext2 == p1t2 || ptext2 == p2t2 then tm3 t2 addOrd3 indexptext2 2
                                            else tm3 t1 addOrd3 indexptext2 2

in if attachT triangle1 tm3 pm is Some tm4' then let tm4 := tm4' in 
      if attachT triangle2 tm4 pm is Some tm5' then let tm5 := tm5' in

(* Mise à jour des adjacences dans le graph g3 : *)



      else None 
   else None.
(* Faire en sorte que flip ressorte un tmap, un graph *)


(* Dans makeDelaunay faire un test findIllegal et si oui alors faire flip et rappeler 
makeDelaunay *)
Fixpoint makeDelaunay (tmap : trianglemap) (g:graph) (pm : pointmap):=

  if (findIllegal tmap graph) is Some (ptext1', ptext2', t1', t2') then 
            let (ptext1, ptext2, t1, t2):= (ptext1', ptext2', t1', t2') in
             let (tmap1, g1) :=flip tmap ptext1 ptext2 t1 t2 g pm in makeDelaunay tmap1 g1 pm
  else makeDelaunay  tmap g pm.
