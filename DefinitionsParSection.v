(* findIllegal fait appel aux fonctions tr2pt et edge2index pour récupérer les 4 points *)

Definition illegaltupleprop (tmap: trianglemap)
    (p : E * point * point * point * point * T * T) :=
   let '(x, ptext1, ptext2, ptin1, ptin2, t1, t2 (* ,
                   preuvetriprop3  (toto (val x)) (valP t1),
                  preuvetriprop3  (toto (val x)) (valP t2) *)) := p in
       t1 \in tmap.

Section findIllegal.

Variables  (em : edgemap) (etm : edgetmap) (tmap : trianglemap) 
 (preuvetmap : tmap_prop1 em tmap) (preuvetriprop3 : triangleprop3 etm tmap).

Let  X := [fset x in finsupp etm | (#|{:etm x}|==2)]%fset.

Let f (* : X -> option ({y : X | #|{: etm (val y)}| == 2} * point * point *
                 point * point * T * T) *) := fun x' : {: X } =>
    let x :=  titi x' : {y : X | #|{:etm (val y)}| == 2} in
    (* S est le fset T contenant les 2 noms de triangles t1 et t2 adjacents en l'edge x *)
    let S := etm (val(val x)) in
    let t1 := @enum_val  [finType of S] xpredT (change_ord (valP x)
            (Ordinal(zero<2)))in
    let t2 := @enum_val  [finType of S] xpredT (change_ord (valP x)
            (Ordinal(un<2)))in

    let i1 := @edge2index (val (val x)) (val t1) em tmap preuvetmap
                          (preuvetriprop3 (toto (val x)) (valP t1)) in
    let i2 := @edge2index (val (val x)) (val t2) em tmap preuvetmap  (preuvetriprop3  (toto (val x)) (valP t2))  in
    let ptext1 := @tr2pt em tmap preuvetmap (val t1) (preuvetriprop3  (toto (val x)) (valP t1)) (addOrd3 i1 (Ordinal un<3)) in
    let ptext2 := @tr2pt em tmap preuvetmap (val t2) (preuvetriprop3  (toto (val x)) (valP t2)) (addOrd3 i2 (Ordinal un<3)) in
    let ptin1 := @tr2pt em tmap preuvetmap (val t1) (preuvetriprop3  (toto (val x)) (valP t1)) i1 in
    let ptin2 := @tr2pt em tmap preuvetmap (val t2) (preuvetriprop3  (toto (val x))  (valP t2)) i2 in 
      if (@inCircle ptext2 em (val t1) tmap (preuvetriprop3  (toto (val x)) (valP t1)) preuvetmap)==true 
                      then  Some (exist (illegaltupleprop tmap)
                        (val (val x), ptext1, ptext2, ptin1, ptin2, val t1, val t2 (* ,
                   preuvetriprop3  (toto (val x)) (valP t1),
                  preuvetriprop3  (toto (val x)) (valP t2) *))
                   (preuvetriprop3  (toto (val x)) (valP t1)))else None.

Let res := [fset f x | x in {: X} & f x != None]%fset.

Definition findIllegal := match pick (pred_of_simpl (@predT {:res})) with
   Some u => val u | None => None end.


Check (fun (tmap : trianglemap) (x : sig_choiceType (illegaltupleprop 
tmap)) =>
          let '(exist (x, ptext1, ptext2, ptin1, ptin2, t1, t2) _) := x in
          t1).

End findIllegal.
