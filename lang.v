Require Export SfLib.
Require Export Permutation.

Require Import Misc. 

Definition store := partial_map nat.

Inductive uid : Type := 
  | UID : nat -> uid.

Definition beq_uid uid1 uid2 :=
  match (uid1, uid2) with
    (UID n1, UID n2) => beq_nat n1 n2
  end.

Theorem beq_uid_refl : forall i,
  true = beq_uid i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl.  Qed.

Theorem beq_uid_eq : forall i1 i2,
  true = beq_uid i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_eq in H. subst.
  reflexivity.  Qed.

Theorem beq_uid_false_not_eq : forall i1 i2,
  beq_uid i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity.  Qed.

Theorem not_eq_beq_uid_false : forall i1 i2,
  i1 <> i2 -> beq_uid i1 i2 = false.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption.  Qed.

Theorem beq_uid_sym: forall i1 i2,
  beq_uid i1 i2 = beq_uid i2 i1.
Proof.
  intros i1 i2. destruct i1. destruct i2. apply beq_nat_sym. Qed.

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
   | AS_Id : forall (id : id) (st : store) (u : uid) (n : nat),
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

Inductive aeval_step : (aexp * store * uid) -> (aexp * store * uid) -> Prop :=
  | AEvalStep : forall a a' s u, 
                  a / s # u ==>a a' -> 
                  aeval_step (a,s,u) (a',s,u).
Inductive aeval : aexp -> store -> uid -> aexp -> Prop :=
  | AE_Value : forall a s u a',
              avalue a' -> aeval a s u a'.
  | AE_Step : forall a s u a',
              avalue a' -> 
              (multi aeval_step) (a,s,u) (a',s,u) -> 
              aeval a s u a'.
(* Notation " a '/' st '#' u '~~>a' a' " := (aeval a st u a') (at level 39, st at level 38, u at level 40). *)

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

Inductive beval_step : (bexp * store * uid) -> (bexp * store * uid) -> Prop :=
  | BEvalStep : forall b b' s u, 
                  b / s # u ==>b b' -> 
                  beval_step (b,s,u) (b',s,u).
Inductive beval : bexp -> store -> uid -> bexp -> Prop :=
  | BEval : forall b s u b',
              bvalue b' -> 
              (multi beval_step) (b,s,u) (b',s,u) -> 
              beval b s u b'.
(* Notation " b '/' st '#' u '~~>b' b' " := (beval b st u b') (at level 50, st at level 49, u at level 51). *)

Inductive com : Type :=
  | CDone : com
  | CAssign : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CSend : neighbor -> aexp -> com
  | CReceive : id -> com.

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

Definition queue : Type := (list nat)%type.
Definition state : Type := (store * queue)%type.
Definition empty_state : state := (empty,[]).

Reserved Notation " c '/' state '#' u '==>c' c' '&' state' " (at level 40, state at level 39, u at level 41).
Inductive cstep : com -> state -> uid -> com -> state -> Prop :=
  | CS_AssignVal : forall (id : id) (c : com) (n : nat) (st : store) (q : queue) (u : uid),
                     (CAssign id (ANum n)) / (st,q) # u ==>c CDone & (extend st id n,q)
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
                       remove_last q = rest -> 
                       (CReceive id) / (st,q) # u ==>c CDone & (extend st id n, rest)
  | CS_SendStep : forall (msg msg' : aexp) (st : store) (q : queue) (u : uid) (nbor : neighbor),
                    aeval msg st u msg' ->
                    (CSend nbor msg) / (st,q) # u ==>c (CSend nbor msg') & (st,q)
  where " c '/' st '#' u '==>c' c' '&' st' " := (cstep c st u c' st').

Inductive process : Type :=
  | Process : com -> state -> uid -> neighbors -> process.

Reserved Notation " p '=local=>' p' " (at level 40).
Inductive local_step : process -> process -> Prop := 
  | LS : forall c c' st st' q q' n u,
           c / (st,q) # u ==>c c' & (st',q') -> 
           (Process c (st,q) u n) =local=> (Process c' (st',q') u n)
  where " p '=local=>' p' " := (local_step p p').                                           

Fixpoint clear_send (p : process) : process :=
  match p with 
  | Process (CSend _ _) s u n => Process CDone s u n
  | Process (CSeq (CSend _ _) c') s u n => Process c' s u n
  | _ => p
  end.

Inductive proc_terminates : process -> Prop :=
  | P_Termination : forall p s u n, 
                      p =local=> (Process DONE s u n) -> 
                      proc_terminates p.

Inductive sending_msg_to : process -> nat -> uid -> Prop :=
  | SendingLast : forall s n_ix nbors msg_val u u',
                    index n_ix nbors = Some u' -> 
                    sending_msg_to (Process (CSend (Neighbor n_ix) (ANum msg_val)) s u nbors)
                                   msg_val u'
  | SendingSeq : forall c' s n_ix nbors msg_val u u',
                   index n_ix nbors = Some u' -> 
                   sending_msg_to (Process (CSeq (CSend (Neighbor n_ix) (ANum msg_val)) c') s u nbors)
                                  msg_val u'.

Inductive send_step : (process * process) -> (process * process) -> Prop :=
  | SS : forall c c' s st' q' u u' n n' msg,
           sending_msg_to (Process c s u n) msg u' ->
           send_step (Process c s u n, Process c' (st',q') u' n')
                     (clear_send (Process c s u n), Process c' (st',q' ++ [msg]) u' n').

Inductive system : Type := 
  | System : list process -> system. 


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

Definition multistep : system -> system -> Prop := multi step.
Notation "s '!!' s'" :=
  (multistep s s') (at level 30).

Inductive system_halted : system -> Prop :=
  | SystemHalted : forall p s u n proc_list, 
                     In p proc_list -> 
                     p = Process DONE s u n -> 
                     system_halted (System proc_list).

Inductive system_halts : system -> Prop :=
  | SystemHalts : forall s s', 
                    s !! s' -> 
                    system_halted s' ->
                    system_halts s. 

Definition leader : id := Id 0.
Definition finished : id := Id 1.
Definition msg : id := Id 2.
Definition leaderA : aexp := (AId leader).
Definition finishedA : aexp := (AId finished).
Definition msgA : aexp := (AId msg).

Definition leader_election : com :=
  leader ::= (ANum 0);
  finished ::= (ANum 0);
  SEND AUId TO (Neighbor 0);
  WHILEB (B= finishedA (ANum 0)) DO
    msg <-RECEIVE;     
    IFB (B= msgA (ANum 0))
    THEN finished ::= (ANum 1)
    ELSE 
      IFB (B= msgA AUId)
      THEN leader ::= msgA;
           finished ::= (ANum 1);
           SEND (ANum 0) TO (Neighbor 0)
      ELSE 
        IFB (B< AUId msgA)
        THEN leader ::= msgA;
             SEND msgA TO (Neighbor 0)
        ELSE SEND AUId TO (Neighbor 0) 
        FI
      FI
    FI
  END.
        
Definition SystemP2 : system :=
  System ((Process leader_election empty_state (UID 1) [UID 2]) :: 
         [Process leader_election empty_state (UID 2) [UID 1]]).

Ltac pull_to_front :=
  eapply multi_step; [eapply Step_Permute; apply Permutation_cons_append | ].

Tactic Notation "takes_local_step" int_or_var(n) "then" tactic(ts) :=
  eapply multi_step; 
  [eapply Step_LocalStep; [ apply Permutation_refl | apply LS; do n (apply CS_SeqStep); ts ] | ].
Tactic Notation "takes_local_step" "then" tactic(ts) :=
  takes_local_step 1 then ts.
Tactic Notation "takes_local_step" int_or_var(n) := 
  takes_local_step n then idtac.
Tactic Notation "takes_local_step" := takes_local_step 1.
Tactic Notation "seq_next" := takes_local_step 0 then (apply CS_SeqNext).
Tactic Notation "takes_assign_step" := 
  takes_local_step then (apply CS_AssignVal; apply CDone).
Tactic Notation "takes_receive_step" :=
  takes_local_step 2 then 
    (apply CS_ReceiveStep; reflexivity; apply CDone);
  takes_local_step 1 then (apply CS_SeqNext).
Tactic Notation "takes_send_local_step" tactic(ts) := 
  takes_local_step 1 then (apply CS_SendStep; apply AEval; ts).  
Ltac takes_send_step :=
  eapply multi_step; 
  [eapply Step_SendStep; [ apply Permutation_refl | eapply SS; eapply SendingSeq; reflexivity ]
  |].
Tactic Notation "takes_while_unfold_step" :=
  takes_local_step 0 then (apply CS_WhileUnfold).
Tactic Notation "takes_if_step" tactic(ts) := takes_local_step 0 then (apply CS_IfStep; ts).
Tactic Notation "takes_if_true_step" :=
  takes_local_step 0 then (apply CS_IfTrue).
Tactic Notation "takes_if_false_step" := 
  takes_local_step 0 then (apply CS_IfFalse).

Ltac steps_to_receive := 
  do 2 (takes_assign_step; seq_next);
  takes_send_local_step (apply AS_UId);
  takes_send_step; simpl;
  takes_while_unfold_step;
  takes_if_step (eapply BS_Eq1; eapply AS_Id; reflexivity);
  takes_if_step (eapply BS_EqTrue; reflexivity);
  takes_if_true_step.

Lemma SystemP2Halts : system_halts SystemP2.
Proof with simpl. 
  unfold SystemP2. eapply SystemHalts. unfold leader_election.  
  do 2 (takes_assign_step; seq_next).
  takes_local_step then (apply CS_SendStep). 
    apply AEval. eapply AV_num. eapply multi_step.
    apply AEvalStep. apply AS_UId. apply multi_refl.
  takes_send_local_step (apply AEval; apply AS_UId).
  takes_send_step...
  takes_while_unfold_step.
  takes_if_step (apply BS_Eq1; apply AS_Id; reflexivity).
  takes_if_step (apply BS_EqTrue; reflexivity).
  takes_if_true_step.
  steps_to_receive. simpl.
  pull_to_front.
  steps_to_receive. simpl.
  takes_receive_step.
  pull_to_front.
  takes_receive_step.
  takes_if_step_w_ 1.
    
(* Informally, the code I want to execute is the following 
leader := 0;
finished := 0
while not (finished == 0):
  msg <-RECEIVE
  if msg == 0:
    DONE
  else:
    if(msg == u) { 
      leader := u;
    }
*)    
