Require Export SfLib.
Require Export Permutation.
Require Import List.

Inductive store : Type := 
  | Empty : store
  | Extend : store -> id -> nat -> store.

Fixpoint gets (i : id) (s : store) : option nat :=
  match s with 
    | Empty => None
    | Extend s' i' n => 
      if beq_id i i' then 
        Some n else 
        gets i s'
  end.

Inductive uid : Type := 
  | UID : nat -> uid.

Definition neighbors : Type := (list uid)%type.

Inductive neighbor : Type := 
  | Neighbor : nat -> neighbor.

Inductive aexp : Type := 
  | AUId : aexp
  | AId : id -> aexp
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.
Hint Constructors aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AUId" | Case_aux c "AId" 
  | Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Inductive avalue : aexp -> Prop :=
  | AV_num : forall n, avalue (ANum n).
Hint Constructors avalue.

Reserved Notation " a '/' st '#' u '==>a' a' " (at level 40, st at level 39, u at level 41).
Inductive astep : aexp -> store -> uid -> aexp -> Prop :=
  | AS_UId : forall st n, 
               AUId / st # (UID n) ==>a (ANum n)
  | AS_Id : forall (id : id) (st : store) (u : uid) (n : nat),
              gets id st = Some n -> 
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
Hint Constructors astep.

Inductive aeval : aexp -> store -> uid -> aexp -> Prop :=
  | AE_Value : forall a s u,
                 avalue a -> aeval a s u a
  | AE_Step : forall a a' s u a'',
                a / s # u ==>a a' -> 
                aeval a' s u a'' -> 
                aeval a s u a''.
Hint Constructors aeval.
(* Notation " a '/' st '#' u '~~>a' a' " := (aeval a st u a') (at level 39, st at level 38, u at level 40). *)

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.
Hint Constructors bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Notation "'BTRUE'" := 
  BTrue (at level 60).
Notation "'BFALSE'" :=
  BFalse (at level 60).
Notation "'B='" :=
  BEq (at level 60).
Notation "'B<'" :=
  BLe (at level 60).
Notation "'B!'" :=
  BNot (at level 60).
Notation "'B&&'" :=
  BAnd (at level 60).

Inductive bvalue : bexp -> Prop :=
  | BV_true : bvalue BTrue
  | BV_false : bvalue BFalse.
Hint Constructors bvalue.

Reserved Notation " b '/' st '#' u '==>b' b' " (at level 40, st at level 39, u at level 41).
Inductive bstep : bexp -> store -> uid -> bexp -> Prop :=
  | BS_EqTrue : forall (nl nr : nat) (st : store) (u : uid),
                  nl = nr ->
                  (BEq (ANum nl) (ANum nr)) / st # u ==>b BTrue
  | BS_EqFalse : forall (nl nr : nat) (st : store) (u : uid),
                  nl <> nr ->
                  (BEq (ANum nl) (ANum nr)) / st # u ==>b BFalse
  | BS_Eq1 : forall (al al' ar : aexp) (st : store) (u : uid),
               aeval al st u  al' ->
               (BEq al ar) / st # u ==>b (BEq al' ar)
  | BS_Eq2 : forall (al ar ar' : aexp) (st : store) (u : uid),
               avalue al -> 
               aeval ar st u ar' ->
               (BEq al ar) / st # u ==>b (BEq al ar')
  | BS_LeTrue : forall (nl nr : nat) (st : store) (u : uid),
                  nl <= nr ->
                  (BLe (ANum nl) (ANum nr)) / st # u ==>b BTrue
  | BS_LeFalse : forall (nl nr : nat) (st : store) (u : uid),
                  nl > nr ->
                  (BLe (ANum nl) (ANum nr)) / st # u ==>b BFalse
  | BS_Le1 : forall (al al' ar : aexp) (st : store) (u : uid),
               aeval al st u al' ->
               (BLe al ar) / st # u ==>b (BLe al' ar)
  | BS_Le2 : forall (al ar ar' : aexp) (st : store) (u : uid),
               avalue al -> 
               aeval ar st u ar' ->
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
Hint Constructors bstep.

Inductive beval : bexp -> store -> uid -> bexp -> Prop :=
  | BE_Value : forall a s u,
                 bvalue a -> beval a s u a
  | BE_Step : forall b b' s u b'',
                b / s # u ==>b b' -> 
                beval b' s u b'' -> 
                beval b s u b''.
Hint Constructors beval.
(* Notation " b '/' st '#' u '~~>b' b' " := (beval b st u b') (at level 50, st at level 49, u at level 51). *)

Inductive com : Type :=
  | CDone : com
  | CAssign : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CSend : neighbor -> aexp -> com
  | CReceive : id -> com.
Hint Constructors com.

Notation "'DONE'" := 
  CDone.
Notation "X '::=' a" := 
  (CAssign X a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" := 
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'WHILEB' c1 'DO' c2 'END'" :=
  (CWhile c1 c2) (at level 80, right associativity).
Notation "'SEND' msg 'TO' nbor " :=
  (CSend nbor msg) (at level 80).
Notation "id <- 'RECEIVE'" := 
  (CReceive id) (at level 60).

(* Notation "'IFMANYB' (c1, b1) 'ORB' .. 'ORB' (cn, bn) 'OTHERWISE'  b' 'FIMANY'" := *)
(*   IFB c1 THEN b1 ELSE .. *)
(*       (IFB cn THEN bn ELSE .. ELSE b' FI) .. FI. *)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "DONE" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "SEND" 
  | Case_aux c "RECEIVE" ].

Inductive cvalue : com -> Prop :=
  | CV_done : cvalue CDone. 
Hint Constructors cvalue.

Definition queue : Type := (list nat)%type.
Definition state : Type := (store * queue)%type.
Definition empty_state : state := (Empty,[]).

Fixpoint index {A : Type} (n : nat) (ls : list A) : option A :=
  match ls with
  | nil => None
  | h :: t => 
    match n with 
    | O => Some h
    | S n' => index n' t
    end
  end.

Fixpoint pull {A : Type} (q : list A) : option A :=   
  match q with
  | nil => None
  | h :: nil => Some h
  | (h :: t) => pull t
  end.

Reserved Notation " c '/' state '#' u '==>c' c' '&' state' " (at level 40, state at level 39, u at level 41).
Inductive cstep : com -> state -> uid -> com -> state -> Prop :=
  | CS_AssignVal : forall (id : id) (n : nat) (st : store) (q : queue) (u : uid),
                     (CAssign id (ANum n)) / (st,q) # u ==>c CDone & (Extend st id n,q)
  | CS_AssignStep : forall (id : id) (a a' : aexp) (st : store) (q : queue) (u : uid), 
                      aeval a st u a' -> 
                      (CAssign id a) / (st,q) # u ==>c (CAssign id a') & (st,q)

  | CS_SeqNext : forall (c2 : com) (state : state) (u : uid), 
                   (CSeq CDone c2) / state # u ==>c c2 & state
  | CS_SeqStep : forall (c1 c1' c2 : com) (stt stt' : state) (u : uid),
                   c1 / stt # u ==>c c1' & stt' -> 
                   (CSeq c1 c2) / stt # u ==>c (CSeq c1' c2) & stt'

  | CS_IfTrue : forall (ct cf : com) (state : state) (u : uid), 
              (CIf BTrue ct cf) / state # u ==>c ct & state
  | CS_IfFalse : forall (ct cf : com) (state : state) (u : uid), 
                   (CIf BFalse ct cf) / state # u ==>c cf & state
  | CS_IfStep : forall (b b' : bexp) (ct cf : com) (st : store) (q : queue) (u : uid),
                  beval b st u b' -> 
                  (CIf b ct cf) / (st,q) # u ==>c (CIf b' ct cf) & (st,q)
  | CS_WhileUnfold : forall (b : bexp) (c : com) (st : store) (q : queue) (u : uid),
                  (CWhile b c) / (st,q) # u ==>c (CIf b (CSeq c (CWhile b c)) CDone) & (st,q)
  | CS_ReceiveStep : forall (id : id) (n : nat) (rest : list nat) (u : uid) (st : store) (q : queue),
                       pull q = Some n -> 
                       removelast q = rest -> 
                       (CReceive id) / (st,q) # u ==>c CDone & (Extend st id n, rest)
  | CS_SendStep : forall (msg msg' : aexp) (st : store) (q : queue) (u : uid) (nbor : neighbor),
                    aeval msg st u msg' ->
                    (CSend nbor msg) / (st,q) # u ==>c (CSend nbor msg') & (st,q)
  where " c '/' st '#' u '==>c' c' '&' st' " := (cstep c st u c' st').
Hint Constructors cstep.

Inductive process : Type :=
  | Process : com -> state -> uid -> neighbors -> process.

Reserved Notation " p '=local=>' p' " (at level 40).
Inductive local_step : process -> process -> Prop := 
  | LS : forall c c' st st' q q' n u,
           c / (st,q) # u ==>c c' & (st',q') -> 
           (Process c (st,q) u n) =local=> (Process c' (st',q') u n)
  where " p '=local=>' p' " := (local_step p p').                                           
Hint Constructors local_step.

Fixpoint clear_send (p : process) : process :=
  match p with 
  | Process (CSend _ _) s u n => Process CDone s u n
  | Process (CSeq (CSend _ _) c') s u n => Process c' s u n
  | _ => p
  end.

Inductive sending_msg_to : process -> nat -> uid -> Prop :=
  | SendingLast : forall s n_ix nbors msg_val u u',
                    index n_ix nbors = Some u' -> 
                    sending_msg_to (Process (CSend (Neighbor n_ix) (ANum msg_val)) s u nbors)
                                   msg_val u'
  | SendingSeq : forall c' s n_ix nbors msg_val u u',
                   index n_ix nbors = Some u' -> 
                   sending_msg_to (Process (CSeq (CSend (Neighbor n_ix) (ANum msg_val)) c') s u nbors)
                                  msg_val u'.
Hint Constructors sending_msg_to.

Inductive send_step : (process * process) -> (process * process) -> Prop :=
  | SS : forall c c' s st' q' u u' n n' msg,
           sending_msg_to (Process c s u n) msg u' ->
           send_step (Process c s u n, Process c' (st',q') u' n')
                     (clear_send (Process c s u n), Process c' (st',q' ++ [msg]) u' n').
Hint Constructors send_step.

Inductive system : Type := 
  | System : list process -> system. 
Hint Constructors system.

Inductive step : system -> system -> Prop :=
  | Step_Permute : forall proc_list proc_list',
                     Permutation proc_list proc_list' ->
                     step (System proc_list)
                          (System proc_list')
  | Step_LocalStep : forall rest proc proc' proc_list,
                     Permutation (proc :: rest) proc_list -> 
                     proc =local=> proc' -> 
                     step (System proc_list)
                          (System (proc' :: rest))
  | Step_SendStep : forall sender sender' receiver receiver' rest proc_list,
                      Permutation (sender :: (receiver :: rest)) proc_list -> 
                      send_step (sender, receiver) (sender', receiver') ->
                      step (System proc_list)
                           (System (sender' :: (receiver' :: rest))).                            
Hint Constructors step.

Definition multistep : system -> system -> Prop := multi step.
Hint Unfold multistep.
Hint Constructors multi.

Notation "s '!!' s'" :=
  (multistep s s') (at level 30).

