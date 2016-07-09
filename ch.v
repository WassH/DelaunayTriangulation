4 subgoals, subgoal 1 (ID 2503)
  
  R : numDomainType
  oriented : 'rV_2 ^ 3 -> bool
  p1, p2 : point
  df : p1 != p2
  m0 : 0 \in initial p1 p2
  m1 : 1 \in initial p1 p2
  m2 : forall k : nat, k.+2 \notin domf (initial p1 p2)
  m1' : val [` m1]%fset \in (1 |` (0 |` fset0))%fset
  m0' : (val [` m0]%fset \in (1 |` (0 |` fset0))%fset) &&
        ([` m0]%fset != [` m1]%fset)
  ============================
   p2 != p1

subgoal 2 (ID 2609) is:
 (odflt ([ffun x => if x == 0 then p2 else p1], [ffun=> 0])
    [ffun k => if fsval k == 0
               then ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
               else
                odflt ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
                  (ffun0 ({ffun 'I_2 -> point} * nat ^ 2)
                     (cardfs0 nat_choiceType)).[? 
                  fsval k]].[? 0]).1 (Ordinal (n:=2) (m:=0) (erefl true))
 != (odflt ([ffun x => if x == 0 then p2 else p1], [ffun=> 0])
       [ffun k => if fsval k == 0
                  then ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
                  else
                   odflt
                     ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
                     (ffun0 ({ffun 'I_2 -> point} * nat ^ 2)
                        (cardfs0 nat_choiceType)).[? 
                     fsval k]].[? 0]).1
      (Ordinal (n:=2) (m:=1) (erefl true))
subgoal 3 (ID 2653) is:
 (odflt ([ffun x => if x == 0 then p2 else p1], [ffun=> 0])
    [ffun k => if fsval k == 0
               then ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
               else
                odflt ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
                  (ffun0 ({ffun 'I_2 -> point} * nat ^ 2)
                     (cardfs0 nat_choiceType)).[? 
                  fsval k]].[? 0]).2 (Ordinal (n:=2) (m:=0) (erefl true))
   \in initial p1 p2
subgoal 4 (ID 2697) is:
 (odflt ([ffun x => if x == 0 then p2 else p1], [ffun=> 0])
    [ffun k => if fsval k == 0
               then ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
               else
                odflt ([ffun x => if x == 0 then p1 else p2], [ffun=> 1])
                  (ffun0 ({ffun 'I_2 -> point} * nat ^ 2)
                     (cardfs0 nat_choiceType)).[? 
                  fsval k]].[? 0]).2 (Ordinal (n:=2) (m:=1) (erefl true))
   \in initial p1 p2