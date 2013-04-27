Require Export SfLib.
Require Export Permutation.
Require Import NPeano.
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
Definition empty_state : state := (empty,[]).

Reserved Notation " c '/' state '#' u '==>c' c' '&' state' " (at level 40, state at level 39, u at level 41).
Inductive cstep : com -> state -> uid -> com -> state -> Prop :=
  | CS_AssignVal : forall (id : id) (n : nat) (st : store) (q : queue) (u : uid),
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

Inductive proc_terminates : process -> Prop :=
  | P_Termination : forall p s u n, 
                      p =local=> (Process DONE s u n) -> 
                      proc_terminates p.
Hint Constructors proc_terminates.

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

Fixpoint allDone (ps : list process) : bool :=
  match ps with
    | nil => true
    | (Process CDone _ _ _) :: ps' => allDone ps'
    | _ => false
  end.

Definition system_halted (s : system) : Prop :=
  match s with
    | System ps => allDone ps = true
  end.

Inductive system_halts : system -> Prop :=
  | SystemHalts : forall s s', 
                    s !! s' -> 
                    system_halted s' ->
                    system_halts s. 
Hint Constructors system_halts.

Notation "'leader'" := (Id 0).
Notation "'finished'" := (Id 1).
Notation "'msg'" := (Id 2).
Notation "'leaderA'" := (AId leader).
Notation "'finishedA'" := (AId finished).
Notation "'msgA'" := (AId msg).

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

Fixpoint leaderElected (n : nat) (ps : list process) : bool :=
  match ps with 
    | nil => true
    | (Process _ (st,_) _ _) :: ps' => match st leader with 
                                         | Some m => beq_nat n m && leaderElected n ps'
                                         | _ => false
                                       end
    end.

Inductive leader_elected : uid -> system -> Prop :=
  | LeaderElected : forall n proc_list,
                      leaderElected n proc_list = true -> 
                      leader_elected (UID n) (System proc_list).
Hint Constructors leader_elected. 

Fixpoint maxUidN (n : nat) (ps : list process) : nat :=
  match ps with 
    | nil => n
    | (Process _ _ (UID n') _) :: ps' => maxUidN (if ltb n n' then n' else n) ps'
  end.

Fixpoint max_uid (ps : list process) : option uid := 
  match ps with 
    | nil => None
    | (Process _ _ (UID n) _) :: ps' => Some (UID (maxUidN n ps'))
  end.

Inductive system_leader : system -> uid -> Prop :=
  | SystemLeader : forall proc_list u,
                     max_uid proc_list = Some u -> 
                     system_leader (System proc_list) u.
Hint Constructors system_leader.

Inductive correctness : system -> Prop :=
| Correctness :  forall (n : nat) (s s' : system), 
                   s !! s' -> 
                   system_halted s' -> 
                   system_leader s' (UID n) -> 
                   leader_elected (UID n) s' -> 
                   correctness s.
Hint Constructors correctness.         

Fixpoint n_proc_list (i : nat) (n : nat) : list process :=
  match i with 
    | 0 => (Process leader_election empty_state (UID n) [UID 1]) :: []
    | S i' =>  (Process leader_election empty_state (UID (n - i)) [UID (n + 1 - i)]) 
                 :: n_proc_list i' n
  end.

Definition SystemPN (n : nat) : system := System (n_proc_list (n - 1) n).
Lemma SystemP3Correct : correctness (SystemPN 3).
Proof.
  unfold SystemPN. simpl.

Definition SystemP2 : system :=
  System ((Process leader_election empty_state (UID 1) [UID 2]) :: 
         [Process leader_election empty_state (UID 2) [UID 1]]).

Ltac switch_to_next_proc :=
  eapply multi_step; [eapply Step_Permute; apply Permutation_cons_append | ].

Fixpoint firstCommandIsSend (c : com) : bool :=
  match c with
    | CSend _ (ANum _) => true
    | CSeq c' _ => firstCommandIsSend c'
    | _ => false
  end.
Fixpoint isSending (ps : list process) : bool :=
  match ps with
    | (Process c _ _ _) :: _ => firstCommandIsSend c
    | _ => false
  end.

Ltac a_reduction :=
  match goal with
    | [ |- astep (AId _) _ _ _ ] => eapply AS_Id; eauto; try reflexivity
    | [ |- astep AUId _ _ _ ] => eapply AS_UId; a_reduction
    | [ |- aeval (ANum _) _ _ _ ] => eapply AE_Value; eauto
    | [ |- aeval _ _ _ _ ] => eapply AE_Step; a_reduction
  end.
Ltac b_reduction :=
  match goal with
    | [ |- bstep (BEq (ANum ?n) (ANum ?n)) _ _ _ ] => apply BS_EqTrue; reflexivity
    | [ |- bstep (BEq (ANum ?x) (ANum ?y)) _ _ _ ] => apply BS_EqFalse; auto
    | [ |- bstep (BEq (ANum ?n) _) _ _ _ ] => eapply BS_Eq2; [auto | eapply AE_Step; a_reduction]
    | [ |- bstep (BEq _ _) _ _ _ ] => eapply BS_Eq1; eapply AE_Step; a_reduction

    | [ |- bstep (BLe (ANum ?x) (ANum ?y)) _ _ _ ] => 
      let isLe := (eval compute in (ble_nat x y)) in
      match isLe with
        | true => apply BS_LeTrue; auto
        | false => apply BS_LeFalse; auto
      end
    | [ |- bstep (BLe (ANum ?n) _) _ _ _ ] => eapply BS_Le2; [auto | eapply AE_Step; a_reduction]
    | [ |- bstep (BLe _ _) _ _ _ ] => eapply BS_Le1; eapply AE_Step; a_reduction

    | [ |- beval BTrue _ _ _ ] => apply BE_Value; eauto
    | [ |- beval BFalse _ _ _ ] => apply BE_Value; eauto
    | [ |- beval _ _ _ _ ] => eapply BE_Step; b_reduction
  end.
Ltac c_reduction :=
  match goal with
    | [ |- multi step (System ?PS) _ ] =>
      let done := (eval compute in (allDone PS)) in
      match done with 
        | true => eapply multi_refl
        | false => eapply multi_step; [c_reduction | idtac]
      end
        
    | [ |- step (System ?PS) _ ] =>
      let isSend := (eval compute in (isSending PS)) in
      match isSend with
        | true => fail 1
        | false => eapply Step_LocalStep; [ apply Permutation_refl | apply LS; c_reduction ]
      end
        
    | [ |- cstep (CIf BTrue _ _) _ _ _ _ ] => apply CS_IfTrue; c_reduction
    | [ |- cstep (CIf BFalse _ _) _ _ _ _ ] => apply CS_IfFalse; c_reduction
    | [ |- cstep (CIf _ _ _) _ _ _ _ ] => eapply CS_IfStep; b_reduction
    | [ |- cstep (CAssign _ (ANum _)) _ _ _ _ ] => eapply CS_AssignVal; c_reduction
    | [ |- cstep (CAssign _ _) _ _ _ _ ] => eapply CS_AssignStep; a_reduction
    | [ |- cstep (CWhile _ _) _ _ _ _ ] => apply CS_WhileUnfold; c_reduction
    | [ |- cstep (CReceive _) (_, _::_) _ _ _ ] => eapply CS_ReceiveStep; eauto; try reflexivity
    | [ |- cstep (CSend _ _) _ _ _ _ ] => eapply CS_SendStep; a_reduction
    | [ |- cstep (CSeq CDone _) _ _ _ _ ] => eapply CS_SeqNext; c_reduction
    | [ |- cstep (CSeq _ _) _ _ _ _ ] => eapply CS_SeqStep; c_reduction
    | [ |- _ ] => fail
  end.

Lemma SystemP2Halts : system_halts SystemP2.
Proof with simpl.
  unfold SystemP2. eapply SystemHalts. unfold leader_election. unfold multistep.
  repeat c_reduction. 
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction. 
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction.
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction. 
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction.
  reflexivity.
Qed.

Lemma SystemP2Correct : correctness (SystemPN 2).
Proof with simpl.
  unfold SystemPN. simpl.
  eapply Correctness. unfold leader_election. unfold multistep.
  repeat c_reduction. 
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction. 
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction.
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction. 
  eapply multi_step. eapply Step_SendStep. apply Permutation_refl. repeat constructor. simpl.
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction. 
  reflexivity. 
  (* Check that (UID 2) is the leader *)
  eapply SystemLeader. reflexivity.
  (* Did we actually elect proc with (UID 2) as the leader? *)
  eapply LeaderElected. reflexivity.
Qed.

Lemma Leader

Lemma SystemPNCorrect : forall n, 
                          n > 1 -> 
                          correctness (SystemPN n).
  intros.