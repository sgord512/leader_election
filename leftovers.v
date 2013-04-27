
Inductive inbox : Type :=
  | EmptyIn : inbox
  | FullIn : nat -> inbox.

Inductive outbox : Type :=
  | EmptyOut : outbox
  | FullOut : uid -> nat -> outbox.

Inductive active_proc1 : Type := 
  | LoneAct : process -> active_proc1.
Inductive active_proc2 : Type :=
  | PairAct : process -> process -> active_proc2.

Inductive proc_ctxt1 : Type :=
  | LoneCtxt : list process -> list process -> proc_ctxt1.
Inductive proc_ctxt2 : Type :=
  | PairCtxt : list process -> list process -> list process -> proc_ctxt2.

Inductive decompose_system1 : system -> active_proc1 -> proc_ctxt1 -> Prop :=
  | LoneDecompose : forall b a p,
                      decompose_system1 (System (b ++ (p :: a))) (LoneAct p) (LoneCtxt b a).
Inductive decompose_system2 : system -> active_proc2 -> proc_ctxt2 -> Prop :=
  | PairDecompose : forall l m r p1 p2,
                      decompose_system2 (System (l ++ (p1 :: (m ++ (p2 :: r)))))
                                       (PairAct p1 p2) (PairCtxt l m r).

Fixpoint plug1 (p_ctxt : proc_ctxt1) (a_proc : active_proc1) : list process :=
  match a_proc, p_ctxt with
      (LoneAct p), (LoneCtxt b a) => b ++ (p :: a)
  end.

Fixpoint plug2 (p_ctxt : proc_ctxt2) (a_proc : active_proc2) : list process :=
  match a_proc, p_ctxt with
      (PairAct pl pr), (PairCtxt l m r) => l ++ (pl :: (m ++ (pr :: r)))
  end.


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

Tactic Notation "takes_local_step" "then" tactic(ts) :=
  eapply multi_step; 
  [eapply Step_LocalStep; [ apply Permutation_refl | apply LS; repeat (apply CS_SeqNext || apply CS_SeqStep); ts ] | ].
Tactic Notation "takes_local_step" := 
  takes_local_step then idtac.

Tactic Notation "seq_next" := takes_local_step then (apply CS_SeqNext).
Tactic Notation "takes_assign_step" := 
  takes_local_step then (apply CS_AssignVal; apply CDone).
Tactic Notation "takes_receive_step" :=
  (takes_local_step then 
    (apply CS_ReceiveStep; reflexivity; apply CDone));
  (takes_local_step then (apply CS_SeqNext)).
Tactic Notation "takes_send_local_step" tactic(ts) := 
  takes_local_step then (apply CS_SendStep; ts).  
Tactic Notation "takes_send_step" :=
  eapply multi_step; 
  [eapply Step_SendStep; [ apply Permutation_refl
                         | solve [try econstructor; eauto] ] | idtac ].
Tactic Notation "takes_while_unfold_step" :=
  takes_local_step then (apply CS_WhileUnfold).
Tactic Notation "takes_if_step" tactic(ts) := takes_local_step then (apply CS_IfStep; ts).
Tactic Notation "takes_if_true_step" int_or_var(n) :=
  takes_local_step then (apply CS_IfTrue).
Tactic Notation "takes_if_false_step" int_or_var(n) := 
  takes_local_step then (apply CS_IfFalse).
Tactic Notation "takes_not_finished_step" int_or_var(n):=
  (takes_local_step then (apply CS_IfStep;                           
    eapply BE_Step; [apply BS_Eq1; eapply AE_Step; solve [eauto]
                    | eapply BE_Step; solve [eauto] ]));
  takes_if_true_step 0.
Tactic Notation "takes_msg_not_0_step" :=
  (takes_local_step then (apply CS_IfStep; eapply BE_Step;
  [ apply BS_Eq1; eapply AE_Step; solve [eauto] 
  | eapply BE_Step; [ eapply BS_EqFalse; discriminate
                    | apply BE_Value; apply BV_false ] ]));
  takes_if_false_step 1.
Tactic Notation "takes_msg_not_uid_step" :=
  (takes_local_step then (apply CS_IfStep; 
    eapply BE_Step; [ apply BS_Eq1;
                      eapply AE_Step; solve [eauto]
                    | eapply BE_Step; solve [eauto]
                    | eapply BE_Step; [ apply BS_EqFalse; discriminate 
                                      | solve [eauto] ] ]));
    takes_if_false_step 1.

Tactic Notation "takes_msg_not_gt_uid_step" :=
  (takes_local_step then (apply CS_IfStep; 
    eapply BE_Step; 
    [ apply BS_Le1;
      eapply AE_Step; [ apply AS_UId; reflexivity 
                      | apply AE_Value; apply AV_num ] 
    | eapply BE_Step;
      [ apply BS_Le2; [ apply AV_num
                      | eapply AE_Step; [ apply AS_Id; reflexivity
                                        | apply AE_Value; apply AV_num ] ]
      | eapply BE_Step; 
        [ apply BS_LeFalse; apply le_n
        | eapply BE_Value; apply BV_false ] ] ]));
    takes_if_false_step 1.

Tactic Notation "takes_initialization_steps" :=
  (do 2 (takes_assign_step; seq_next));
  (takes_local_step then (apply CS_SendStep;
    eapply AE_Step; [apply AS_UId | apply AE_Value; apply AV_num ]));
  takes_send_step; simpl.
(*  takes_while_unfold_step;
  takes_not_finished_step 0.*)

(* Tactic Notation "blah" := *)
(*   match goal with  *)
(*   | [ |-  ] => e *)
