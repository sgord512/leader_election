Require Export SfLib.

Definition store := partial_map nat.

Inductive uid : Type := 
  | UID : nat -> uid.

Inductive inbox : Type :=
  | EmptyIn : inbox
  | FullIn : nat -> inbox.

Inductive outbox : Type :=
  | EmptyOut : outbox
  | FullOut : uid -> nat -> outbox.

Inductive neighbors : Type :=
  | Neighbors : list uid -> neighbors. 

Inductive aexp : Type := 
  | AUId : aexp
  | AId : id -> aexp
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AUId" | Case_aux c "AId" 
  | Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Inductive avalue : aexp -> Prop :=
  | AV_num : forall n, avalue (ANum n).

Reserved Notation " a '/' st '#' u '==>a' a' " (at level 40, st at level 39, u at level 41).
Inductive astep : aexp -> store -> uid -> aexp -> Prop :=
  | AS_UId : forall st n, 
               AUId / st # (UID n) ==>a (ANum n)
               
  | AS_Id : forall (id : id) (st : store) (i : inbox) (o : outbox) (u : uid) (n : nat),
              st id = Some n -> 
              (AId id) / st # u ==>a (ANum n)
  | AS_Plus1 : forall (al al' ar : aexp) (st : store) (u : uid),
                 al / st # u ==>a al' -> 
                 (APlus al ar) / st # u ==>a (APlus al' ar)
  | AS_Plus2 : forall (al ar ar' : aexp) (st : store) (u : uid),
                 avalue al ->
                 ar / st # u ==>a ar' ->
                 (APlus al ar) / st # u ==>a (APlus al ar')
  | AS_Plus : forall (nl nr : nat) (st :store) (u : uid),
                (APlus (ANum nl) (ANum nr)) / st # u ==>a (ANum (nl + nr))
  | AS_Mult1 : forall (al al' ar : aexp) (st : store) (u : uid),
                 al / st # u ==>a al' -> 
                 (AMult al ar) / st # u ==>a (AMult al' ar)
  | AS_Mult2 : forall (al ar ar' : aexp) (st : store) (u : uid),
                 avalue al ->
                 ar / st # u ==>a ar' ->
                 (AMult al ar) / st # u ==>a (AMult al ar')
  | AS_Mult : forall (nl nr : nat) (st :store) (u : uid),
                (AMult (ANum nl) (ANum nr)) / st # u ==>a (ANum (nl * nr))
  | AS_Minus1 : forall (al al' ar : aexp) (st : store) (u : uid),
                 al / st # u ==>a al' -> 
                 (AMinus al ar) / st # u ==>a (AMinus al' ar)
  | AS_Minus2 : forall (al ar ar' : aexp) (st : store) (u : uid),
                 avalue al ->
                 ar / st # u ==>a ar' ->
                 (AMinus al ar) / st # u ==>a (AMinus al ar')
  | AS_Minus : forall (nl nr : nat) (st :store) (u : uid),
                (AMinus (ANum nl) (ANum nr)) / st # u ==>a (ANum (nl - nr))
  where " a '/' st '#' u '==>a' a' " := (astep a st u a').

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Inductive bvalue : bexp -> Prop :=
  | BV_true : bvalue BTrue
  | BV_false : bvalue BFalse.

Reserved Notation " b '/' st '#' u '==>b' b' " (at level 40, st at level 39, u at level 41).
Inductive bstep : bexp -> store -> uid -> bexp -> Prop :=
  | BS_EqTrue : forall (nl nr : nat) (st : store) (u : uid),
                  nl = nr ->
                  (BEq (ANum nl) (ANum nr)) / st # u ==>b BTrue
  | BS_EqFalse : forall (nl nr : nat) (st : store) (u : uid),
                  nl <> nr ->
                  (BEq (ANum nl) (ANum nr)) / st # u ==>b BFalse
  | BS_Eq1 : forall (al al' ar : aexp) (st : store) (u : uid),
               al / st # u ==>a al' ->
               (BEq al ar) / st # u ==>b (BEq al' ar)
  | BS_Eq2 : forall (al ar ar' : aexp) (st : store) (u : uid),
               avalue al -> 
               ar / st # u ==>a ar' ->
               (BEq al ar) / st # u ==>b (BEq al ar')
  | BS_LeTrue : forall (nl nr : nat) (st : store) (u : uid),
                  nl <= nr ->
                  (BLe (ANum nl) (ANum nr)) / st # u ==>b BTrue
  | BS_LeFalse : forall (nl nr : nat) (st : store) (u : uid),
                  nl > nr ->
                  (BLe (ANum nl) (ANum nr)) / st # u ==>b BFalse
  | BS_Le1 : forall (al al' ar : aexp) (st : store) (u : uid),
               al / st # u ==>a al' ->
               (BLe al ar) / st # u ==>b (BLe al' ar)
  | BS_Le2 : forall (al ar ar' : aexp) (st : store) (u : uid),
               avalue al -> 
               ar / st # u ==>a ar' ->
               (BLe al ar) / st # u ==>b (BLe al ar')
  | BS_NotTrue : forall (st : store) (u : uid), 
                   BNot BTrue / st # u ==>b BFalse
  | BS_NotFalse : forall (st : store) (u : uid), 
                    BNot BFalse / st # u ==>b BFalse
  | BS_Not1 : forall (b b' : bexp) (st : store) (u : uid), 
                b / st # u ==>b b' ->
                BNot b / st # u ==>b BNot b'
  | BS_AndTrue : forall (st : store) (u : uid), 
                   BAnd BTrue BTrue / st # u ==>b BTrue
  | BS_And1 : forall (bl bl' br : bexp) (st : store) (u : uid),
                bl / st # u ==>b bl' ->
                BAnd bl br / st # u ==>b BAnd bl' br
  | BS_And2 : forall (bl br br' : bexp) (st : store) (u : uid),
                bvalue bl ->
                br / st # u ==>b br' ->
                BAnd bl br / st # u ==>b BAnd bl br'
  | BS_AndFalseL : forall (br : bexp) (st : store) (u : uid),                
                BAnd BFalse br / st # u ==>b BFalse
  | BS_AndFalseR : forall (st : store) (u : uid),
                     BAnd BTrue BFalse / st # u ==>b BFalse
  where " b '/' st '#' u '==>b' b' " := (bstep b st u b').

Inductive com : Type :=
  | CDone : com
  | CAssign : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CSend : uid -> aexp -> com
  | CReceive : id -> com.

Notation "'DONE'" := 
  CDone.
Notation "X '::=' a" := 
  (CAssign X a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" := 
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'SEND' uid: msg" :=
  (CSend uid msg) (at level 80).
Notation "id <- 'RECEIVE'" := 
  (CReceive id) (at level 60).

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "DONE" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "SEND" 
  | Case_aux c "RECEIVE" ].


Inductive cvalue : com -> Prop :=
  | CV_done : cvalue CDone. 

Definition state : Type := (store * inbox * outbox)%type.

Reserved Notation " c '/' state '#' u '==>c' c' '&' state' " (at level 40, state at level 39, u at level 41).
Inductive cstep : com -> (store * inbox * outbox) -> uid -> com -> (store * inbox * outbox) -> Prop :=
  | CS_AssignVal : forall (id : id) (c : com) (n : nat) (st : store) (i : inbox) (o : outbox) (u : uid),
                     (CAssign id (ANum n)) / (st,i,o) # u ==>c CDone & (extend st id n,i,o)
  | CS_AssignStep : forall (id : id) (a a' : aexp) (st : store) (i : inbox) (o : outbox) (u : uid), 
                      a / st # u ==>a a' ->  
                      (CAssign id a) / (st,i,o) # u ==>c (CAssign id a') & (st,i,o)

  | CS_SeqNext : forall (c2 c2' : com) (state : state) (u : uid), 
                   (CSeq CDone c2) / state # u ==>c c2 & state
  | CS_SeqStep : forall (c1 c1' c2 : com) (st st' : store) (i i' : inbox) (o o' : outbox) (u : uid),
                   c1 / (st,i,o) # u ==>c c1' & (st',i',o') -> 
                   (CSeq c1 c2) / (st',i',o') # u ==>c c2 & (st',i',o')

  | CS_IfTrue : forall (ct cf : com) (state : state) (u : uid), 
              (CIf BTrue ct cf) / state # u ==>c ct & state 
  | CS_IfFalse : forall (ct cf : com) (state : state) (u : uid), 
                   (CIf BFalse ct cf) / state # u ==>c cf & state
  | CS_IfStep : forall (b b' : bexp) (ct cf : com) (st : store) (i : inbox) (o : outbox) (u : uid),
                  b / st # u ==>b b' -> 
                  (CIf b ct cf) / (st,i,o) # u ==>c (CIf b' ct cf) & (st,i,o)

  | CS_SendVal : forall (to : uid) (n : nat) (st : store) (i : inbox) (u : uid),
                   (CSend to (ANum n)) / (st,i,EmptyOut) # u ==>c CDone & (st,i,FullOut to n)
  | CS_SendStep : forall (to : uid) (a a' : aexp) (st : store) (i : inbox) (o : outbox) (u : uid),
                    a / st # u ==>a a' -> 
                    (CSend to a) / (st,i,o) # u ==>c (CSend to a') & (st,i,o)
  | CS_Receive : forall (id : id) (n : nat) (st : store) (o : outbox) (u : uid), 
                   (CReceive id) / (st,FullIn n,o) # u ==>c CDone & (extend st id n,EmptyIn,o)
  where " c '/' state '#' u '==>c' c' '&' state' " := (cstep c state u c' state').

Inductive process : Type :=
  | Process : com -> state -> uid -> neighbors -> process.

Inductive system : Type := 
  | System : list process -> system. 

Inductive pdone : process -> Prop :=
  | PD_done : forall (state : state) (u : uid) (n : neighbors), 
              pdone (Process CDone state u n).

Reserved Notation " p '==>p' p' " (at level 50). 
Inductive pstep : process -> process -> Prop := 
  | PS_Step : forall (c c' : com) (s s' : state) (u : uid) (n : neighbors), 
                c / s # u ==>c c' & s' -> 
                (Process c s u n) ==>p (Process c' s' u n)
  where " p '==>p' p' " := (pstep p p').                                  

Reserved Notation " s '!!' s' " (at level 50).
Inductive sync_step : system -> system -> Prop :=
  | SyncStepNil : sync_step (System []) (System [])
  | SyncStepCons : forall (sys sys' : list process) (p p' : process),
                     p ==>p p' ->
                     sync_step (System sys) (System sys') -> 
                     sync_step (System (p :: sys)) (System (p' :: sys')).

Fixpoint 

Fixpoint transfer_messages (sys : system) : system :=
  match sys with 
  | System [] => sys
  | System (h :: tl) => 
    match h with 
    | Process c (st,i,Empty) u n p
                            

Reserved Notation " curr '/' st '(' s '&' b ')' '==>' next '/' st' '(' s' '&' b' ')' " (at level 40, st at level 39).
Inductive step : proc -> store -> inbox -> outbox -> proc -> store -> inbox -> outbox -> Prop :=
  

(* Each process will be associated with a list of UIDs, which will be the neighbors it is connected to, and it is important that the neighbor ID's be abstract as far as the process is concerned. Also,  *)


(* The programs that implement these algorithms are going to basically be transition functions, and I need to prove that for a given network topology, the execution of 
