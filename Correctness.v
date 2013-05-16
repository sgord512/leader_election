Require Import Misc.
Require Import Lang.
Require Import Leader.
Require Import Cases.
Require Export SfLib.

Definition RingP2 : system := NProcRing 2.

Definition proc_uid (p : process) : uid :=
  match p with Process _ _ u _ => u end.
Definition proc_neighbors (p : process) : list uid :=
  match p with Process _ _ _ n => n end.
Definition proc_command (p : process) : com :=
  match p with Process c _ _ _ => c end.
Definition proc_state (p : process) : state :=  
  match p with Process _ s _ _ => s end. 
Definition system_proc_list s : list process :=
  match s with System p => p end. 
Definition uid_to_nat (u : uid) : nat :=
  match u with UID n => n end. 
Fixpoint firstCommandIsSend (c : com) : bool :=
  match c with
    | CSend _ (ANum _) => true
    | CSeq c' _ => firstCommandIsSend c'
    | _ => false
  end.
Definition isSending (ps : list process) : bool :=
  match ps with
    | (Process c _ _ _) :: _ => firstCommandIsSend c
    | _ => false
  end.
Definition proc_list_uids (ps : list process) : list uid := map proc_uid ps.
Hint Unfold proc_list_uids.
Definition contains_uid (u : uid) (us : list uid) : bool := existsb (beq_uid u) us.
Definition contains_uids (us us' : list uid) : bool := forallb (fun u => contains_uid u us') us.
Definition edges_in_proc_list (ps : list process) (uids : list uid) : bool :=
  forallb (fun p => contains_uids (proc_neighbors p) uids) ps.
Fixpoint count_occurrences (u : uid) (us : list uid) : nat :=
  match u, us with 
    | UID n, UID m :: us' => (count_occurrences u us') + (if beq_nat n m then 1 else 0)
    | _, _ => 0
  end.

Definition unique_uid (u : uid) (us : list uid) : bool :=
  beq_nat (count_occurrences u us) 1.
Definition uniqueUids (us : list uid) : bool :=
  forallb (fun u => unique_uid u us) us.
Hint Unfold uniqueUids. 
Definition uniqueUidsProc (ps : list process) : bool :=
  let uids := proc_list_uids ps in 
  uniqueUids uids.
Hint Unfold uniqueUidsProc. 
Fixpoint com_neighbor_indices (c : com) : list neighbor := 
  match c with 
    | CSend n _ => [n]
    | CSeq c1 c2 => com_neighbor_indices c1 ++ com_neighbor_indices c2
    | CIf b ct cf => com_neighbor_indices ct ++ com_neighbor_indices cf
    | CWhile b c => com_neighbor_indices c
    | _ => []
    end.
Definition neighbor_indices (p : process) : list neighbor := com_neighbor_indices (proc_command p).
Definition procAllSendsValid (p : process) : bool :=
  let indices := map (fun nbor => match nbor with Neighbor n => n end) (neighbor_indices p) in 
  let nbor_len := length (proc_neighbors p) in 
  forallb (fun n => ble_nat n nbor_len) indices.

Inductive all_sends_valid : system -> Prop :=
| AllSendsValid : forall proc_list, 
                    forallb procAllSendsValid proc_list = true -> 
                    all_sends_valid (System proc_list).
Hint Constructors all_sends_valid.

Lemma all_sends_valid_subset :
  forall p ps, 
    all_sends_valid (System (p :: ps)) ->
    all_sends_valid (System ps).
Proof. 
  intros. inversion H. unfold forallb in H1. apply andb_true_iff in H1. 
  inversion H1. constructor. unfold forallb. assumption.
Qed.

Lemma contains_uid_superset : 
  forall u us u', 
    contains_uid u us = true -> 
    contains_uid u (u' :: us) = true.
Proof. 
  intros. unfold contains_uid. unfold contains_uid in H. 
  assert ([u'] ++ us = (u' :: us)). reflexivity.
  rewrite <- H0. rewrite existsb_app with (l1 := [u']). rewrite H. apply orb_true_r.
Qed. 

Lemma contains_uids_superset : 
  forall proc_list us u, 
    contains_uids proc_list us = true -> 
    contains_uids proc_list (u :: us) = true.
Proof. 
  intros. unfold contains_uids.
  unfold contains_uids in H. 
  induction proc_list. simpl. reflexivity.
  assert (a :: proc_list = [a] ++ proc_list). reflexivity.
  rewrite H0. rewrite forallb_app with (l1 := [a]). 
  rewrite H0 in H. rewrite forallb_app with (l1 := [a]) in H. apply andb_true_iff in H.
  inversion H. apply IHproc_list in H2. simpl in H1. rewrite andb_true_r in H1. 
  (* apply contains_uid_superset with (u' := u) in H1. *)
  simpl forallb at 1. rewrite H1. rewrite orb_true_r. simpl. exact H2.
Qed. 

Lemma edges_in_proc_list_superset :
  forall proc_list p ps,
    edges_in_proc_list proc_list ps = true ->
    edges_in_proc_list proc_list (p :: ps) = true.
Proof. 
  intros. induction ps.
  unfold edges_in_proc_list.
  unfold edges_in_proc_list in H. rewrite forallb_forall in H. 
  rewrite forallb_forall. intros. apply H in H0. 
  eapply contains_uids_superset in H0. exact H0.
  unfold edges_in_proc_list in IHps. rewrite forallb_forall in IHps. 
  unfold edges_in_proc_list in H. rewrite forallb_forall in H.
  unfold edges_in_proc_list. rewrite forallb_forall. intros. apply H in H0.
  unfold contains_uids. unfold contains_uids in H0. rewrite forallb_forall in H0. 
  rewrite forallb_forall. intros. apply H0 in H1. eapply contains_uid_superset. assumption.
Qed.    

Inductive unique_uids : system -> Prop :=
| UniqueUIds : forall proc_list, 
                 uniqueUidsProc proc_list = true -> 
                 unique_uids (System proc_list).
Hint Constructors unique_uids.

Lemma ring_uids_are_n_to_1 : 
  forall n,
    proc_list_uids (n_proc_list n) = uid_range n.
Proof.
  intro n. 
  induction n as [| n']. 
  Case "n = 0". reflexivity. 
  Case "n = S n'". simpl. rewrite IHn'. reflexivity.
Qed.

Lemma uid_range_cons : 
  forall n, 
    uid_range (S n) = (UID (S n)) :: uid_range n.
Proof. 
  induction n. reflexivity.
  simpl. reflexivity.
Qed. 

Lemma count_occurrences_cons : 
  forall u u' us, 
    count_occurrences u (u' :: us) = (if beq_uid u u' then 1 else 0) + count_occurrences u us.
Proof. 
  intros u u' us. simpl. destruct u. destruct u'. unfold beq_uid. eapply plus_comm.
Qed.

Lemma count_occurrences_O_not_contains : 
  forall u us, 
    count_occurrences u us = 0 <-> contains_uid u us = false.
Proof. 
  intros. induction us; split; intro.
  Case "->". reflexivity.
  Case "<-". simpl. destruct u. reflexivity.
    simpl. rewrite orb_false_intro. reflexivity.
    rewrite count_occurrences_cons in H. destruct (beq_uid u a). inversion H.
      reflexivity.
    rewrite count_occurrences_cons in H. destruct (beq_uid u a). inversion H. simpl in H.
    rewrite <- IHus. assumption.
    rewrite count_occurrences_cons. simpl in H. destruct (beq_uid u a). 
      inversion H. simpl in H. rewrite IHus. assumption.
Qed.    

Lemma uid_above_range_do_not_occur : 
  forall n m, 
    S n > m -> 
    count_occurrences (UID (S n)) (uid_range m) = 0.
Proof. 
  intro n. induction n as [| n']. intro m. intro. inversion H. reflexivity.
  inversion H1.
  intro m. intro H. 
    induction m as [| m']. reflexivity. 
    simpl. apply gt_S_n in H. assert (S (S n') > m'). omega. apply IHm' in H0.
    rewrite H0. simpl. destruct m'. reflexivity. apply gt_S_n in H. replace (beq_nat n' m') with false. auto. symmetry. apply beq_nat_false_iff. omega. 
Qed. 

Lemma all_uid_in_range_occur_once : 
  forall n m, 
    S n <= m -> 
    count_occurrences (UID (S n)) (uid_range m) = 1.
Proof. 
  intros n m. generalize dependent n. induction m as [| m'].
  intros n H. inversion H. 
  intros n H. simpl. remember (beq_uid (UID (S n)) (UID (S m'))) as eq. 
  destruct eq. unfold beq_uid in Heqeq. apply beq_nat_eq in Heqeq. rewrite -> Heqeq. 
  assert (forall n, count_occurrences (UID (S n)) (uid_range n) = 0).
    intro n0. apply uid_above_range_do_not_occur. auto.
    inversion Heqeq. rewrite <- beq_nat_true_iff in H2. 
    assert (beq_nat m' m' = true). symmetry. apply beq_nat_refl. rewrite -> H1. 
    assert (count_occurrences (UID (S m')) (uid_range m') = 0).
    apply uid_above_range_do_not_occur. auto. rewrite -> H3. reflexivity.
    unfold beq_uid in Heqeq.
    assert (false = beq_nat  n m'). symmetry in Heqeq. rewrite -> beq_nat_false_iff in Heqeq. 
    unfold not in Heqeq. symmetry. apply beq_nat_false_iff. intro. apply Heqeq. auto. rewrite <- H0. 
    assert (count_occurrences (UID (S n)) (uid_range m') = 1).
    apply IHm'. apply le_lt_or_eq_iff in H. symmetry in Heqeq. rewrite -> beq_nat_false_iff in Heqeq.
    assert (S n < S m'). inversion H. assumption. 
    exfalso. apply Heqeq in H1. assumption.
    apply lt_n_Sm_le. assumption. 
    rewrite -> H1. reflexivity.
Qed.

Lemma all_uid_in_range_are_unique : 
  forall n m, 
    S n <= m -> 
    unique_uid (UID (S n)) (uid_range m) = true.
Proof. 
  intros n m. generalize dependent n. 
  induction m as [| m']; intro n.  
    intro. inversion H.
    intro. unfold unique_uid. apply beq_nat_true_iff. 
    apply all_uid_in_range_occur_once. assumption.
Qed.

Definition neighbors_in_system (proc_list : list process) : Prop :=
  edges_in_proc_list proc_list (proc_list_uids proc_list) = true.

Definition well_formed_system (s : system) : Prop :=
  all_sends_valid s /\ unique_uids s /\ neighbors_in_system (system_proc_list s).

Lemma rings_are_same_except_front : 
  forall (n : nat), 
    tl (SnRingProcList n) = tl (tl (SnRingProcList (S n))).
Proof. 
  intro n. induction n as [| n']; reflexivity.
Qed.

Lemma unique_uid_one : forall u, uniqueUids [u] = true.
Proof. intros u. 
       unfold uniqueUids. simpl. rewrite andb_true_iff; split; auto. unfold unique_uid. simpl.
       destruct u. simpl. replace (beq_nat n n) with true. reflexivity. apply beq_nat_refl. 
Qed.
  
Lemma unique_uids_cons : 
  forall u us, 
    uniqueUids us = true -> 
    contains_uid u us = false ->
    uniqueUids (u :: us) = true.
Proof.
  intros u us. generalize dependent u.
  induction us. simpl. intro u. intro. intro. apply unique_uid_one.
  intros. unfold uniqueUids. Admitted.

Lemma well_formed_rings : forall (n : nat), 
                            n > 0 ->
                            well_formed_system (NProcRing n).
Proof.
  intro n. unfold NProcRing; unfold SnProcRing. unfold SnRingProcList.
  induction n as [ | n' ]; intro H. 
    inversion H. 
    destruct n'. simpl. unfold well_formed_system. 
      split. constructor. reflexivity.
      split. constructor. reflexivity.
      unfold neighbors_in_system. simpl. reflexivity.      
    simpl. simpl in IHn'. rewrite <- minus_n_O in IHn'.  
    assert (S n' > 0). apply gt_Sn_O. apply IHn' in H0. clear IHn'. 
    inversion H0. inversion H2. clear H2.
    unfold well_formed_system. split.
    Case "all_sends_valid".
      constructor. simpl. 
      eapply all_sends_valid_subset in H1. inversion H1. 
      exact H5. 
    split. 
    Case "unique_uids". 
      constructor. unfold uniqueUidsProc.
      eapply unique_uids_cons. simpl. inversion H3. 
      unfold uniqueUidsProc in H5. 
      unfold proc_list_uids in H5. simpl in H5. exact H5.
      simpl. replace (beq_uid (UID (S (S n'))) (UID (S n'))) with false. simpl.
      apply count_occurrences_O_not_contains. rewrite -> ring_uids_are_n_to_1. 
      apply uid_above_range_do_not_occur.
        assert (S n' > n'). apply gt_Sn_n. 
        assert (S (S n') > S n'). apply gt_Sn_n.
        eapply gt_trans. exact H5. exact H2.
      unfold beq_uid. symmetry. rewrite beq_nat_false_iff. intro. 
      assert (S (S n') > S n'). apply gt_Sn_n. 
      rewrite -> H2 in H5. apply gt_irrefl in H5. assumption.
    Case "neighbors_in_system".
      unfold neighbors_in_system in H4. simpl in H4.
      rewrite ring_uids_are_n_to_1 in H4.
      unfold neighbors_in_system. simpl. 
      apply andb_true in H4. inversion H4. 
      rewrite ring_uids_are_n_to_1.
      rewrite -> H2. simpl. rewrite -> andb_true_r in H4. 
      rewrite -> andb_true_r in H2. 
      rewrite -> andb_true_r.

      assert (beq_uid (UID (S (n' + 1))) (UID (S (S n'))) = true).
      unfold beq_uid. simpl. rewrite -> plus_comm. simpl. symmetry. apply beq_nat_refl.
      rewrite H6. simpl. apply edges_in_proc_list_superset. assumption.
Qed.

(* Lemma well_formed_system_subset :  *)
(*   forall p ps,  *)
(*     well_formed_system (p :: ps) ->  *)
(*     well_formed *)
    
                                    


(* Definition contains_nat (n : nat) (ls : list nat) : bool := *)
(*   existsb (beq_nat n) ls. *)
(* Definition receivingHaltMessage (p : process) : bool := *)
(*   match p with  *)
(*     | Process _ (_, q) _ _ => contains_nat 0 q *)
(*   end. *)

(* Inductive receiving_halt_msg : process -> Prop := *)
(*   | ReceivingHaltMsg : forall p,  *)
(*                          receivingHaltMessage p = true ->  *)
(*                          receiving_halt_msg p. *)
(* Hint Constructors receiving_halt_msg.   *)

(* Lemma proc_halts_on_0 : forall p,  *)
(*                      receiving_halt_msg p ->                       *)


Ltac switch_to_next_proc :=
  eapply multi_step; [eapply Step_Permute; apply Permutation_cons_append | ].

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

Ltac send_message := 
   eapply multi_step; [ eapply Step_SendStep; [ apply Permutation_refl | repeat constructor ] | ]; simpl. 

Ltac unfold_rings := unfold NProcRing; unfold SnProcRing; unfold SnRingProcList.

Ltac unfold_procs := unfold leader_election_proc; unfold leader_election.

Ltac unfold_multi := unfold multistep.

Ltac unfolding := unfold_rings; unfold_procs; unfold_multi; simpl.

Lemma RingP2Halts : system_halts RingP2.
Proof with simpl.
  unfold RingP2; unfolding.
  eapply SystemHalts. unfolding.
  (* Begin stepping *)
  repeat c_reduction. 
  send_message. simpl. 
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction. 
  send_message. simpl.
  repeat c_reduction.
  send_message. simpl. 
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction.
  send_message. simpl. 
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction.
  reflexivity.
Qed.

Lemma RingP2Correct : correctness (NProcRing 2).
Proof with simpl.
  unfolding.
  eapply Correctness. unfolding. 
  repeat c_reduction. 
  send_message. simpl. 
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction. 
  send_message. simpl. 
  repeat c_reduction.
  send_message. simpl. 
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction.
  send_message. simpl. 
  repeat c_reduction.
  switch_to_next_proc.
  repeat c_reduction.
  reflexivity.
  (* Check that (UID 2) is the leader *)
  eapply SystemLeader. reflexivity.
  (* Did we actually elect proc with (UID 2) as the leader? *)
  eapply LeaderElected. reflexivity.
Qed.

Lemma S_n_minus_1_S : forall n, n > 1 -> S (n - 1) = n.
  Proof.
    intros. destruct n. simpl. inversion H. simpl. 
    rewrite <- minus_n_O. reflexivity. 
Qed.

Lemma Progress : 
  forall (l : list process),
    (forall p, In p l -> is_receiving p)
    \/ (exists lr p ls, l = lr ++ p :: ls ->
                       (forall p0, In p0 lr -> is_receiving p0)
                       /\ ~ is_receiving p 
                       /\ (exists p', System (lr ++ p :: ls) !! System (lr ++ p' :: ls)
                                      /\ is_receiving p'))
    \/ (exists l', (System l) !! (System l') /\ system_halted (System l'))
    \/ ~ well_formed_system (System l).
Proof.
  intros. 
  induction l.
  left. intros. simpl in H. exfalso. assumption.
  inversion IHl.
  inversion H. apply all_sends_valid_subset in H0.
  inversion H1. apply unique_uids_subset in H2.
  remember (System l) as sys. intros.
  apply 

Lemma initialization : 
  forall n, 
    n > 1 -> 
    NProcRing n !! initialized n.
Proof. 
  intros. unfold_rings. unfold_multi.
  induction n. inversion H. destruct n. apply gt_irrefl in H. exfalso. assumption.
  destruct n.
  unfolding. 
  repeat c_reduction. 
  send_message. simpl. 
  repeat c_reduction.
  switch_to_next_proc.
  unfolding.
  repeat c_reduction. 
  send_message. simpl.
  do 3 c_reduction.
  switch_to_next_proc. simpl.
  unfold initialized. unfold ring_n_round_m. simpl.
  unfold receiving. unfold modulo. simpl.
  eapply multi_refl.


Lemma SystemPNCorrect : forall n, 
                          n > 1 -> 
                          correctness (NProcRing n).
  intros.
  eapply Correctness. unfolding. remember H as G. clear HeqG. apply S_n_minus_1_S in G. rewrite G.
  repeat c_reduction. 
    destruct (n - 1). 
    Case "n - 1 = 0". 
      rewrite G in H. apply gt_irrefl in H. exfalso. assumption.
    Case "n - 1 > 0".
      simpl. switch_to_next_proc. unfolding. repeat c_reduction.
      induction n0; simpl.
      SCase "n0 = 0". 
        send_message. rewrite G. reflexivity. simpl.
        
      