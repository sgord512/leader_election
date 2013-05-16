Require Import Misc.
Require Import Lang. 
Require Import NPeano.

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

Definition leader_election_proc (n : nat) (u : uid) : process :=
  Process leader_election empty_state (UID n) [u].

Fixpoint leaderElected (n : nat) (ps : list process) : bool :=
  match ps with 
    | nil => true
    | (Process _ (st,_) _ _) :: ps' => match gets leader st with 
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

Fixpoint n_proc_list (n : nat) : list process :=
  match n with 
    | 0 => []
    | S n' => leader_election_proc n (UID (n + 1)) :: n_proc_list n'
  end.

Fixpoint range (n : nat) : list nat :=
  match n with 
    | 0 => []
    | S n' => n :: range n'
  end.

Fixpoint uid_range (n : nat) : list uid :=
  match n with 
    | 0 => []
    | S n' => (UID n) :: uid_range n'
    end.       

Fixpoint uid_range_two (start more : nat) : list uid :=
  match more with 
    | 0 => UID start :: []
    | S more' => (UID (start + more)) :: uid_range_two start more'
  end.

Definition SnRingProcList (n : nat) := leader_election_proc (S n) (UID 1) :: n_proc_list n.
Hint Unfold SnRingProcList.
Definition SnProcRing (n : nat) : system := System (SnRingProcList n).
Hint Unfold SnProcRing.
Definition NProcRing (n : nat) : system := SnProcRing (n - 1).
Hint Unfold NProcRing.

Definition receiving (n : nat) (u : uid) (m : nat) : process := Process
((msg <-RECEIVE;
  IFB (B=) msgA (ANum 0) 
  THEN finished ::= ANum 1
  ELSE IFB (B=) msgA AUId
    THEN leader ::= msgA; finished ::= ANum 1; SEND ANum 0 TO Neighbor 0
    ELSE IFB (B<) AUId msgA
      THEN leader ::= msgA; SEND msgA TO Neighbor 0
      ELSE SEND AUId TO Neighbor 0 FI FI FI);
           WHILEB (B=) finishedA (ANum 0)
           DO msg <-RECEIVE;
             IFB (B=) msgA (ANum 0) THEN finished ::= ANum 1
             ELSE IFB (B=) msgA AUId
               THEN leader ::= msgA;
                    finished ::= ANum 1; SEND ANum 0 TO Neighbor 0
               ELSE IFB (B<) AUId msgA
                 THEN leader ::= msgA; SEND msgA TO Neighbor 0
                 ELSE SEND AUId TO Neighbor 0 FI FI FI END)
   (Extend (Extend Empty leader 0) finished 0, [m]) 
   (UID n)
   [u].
Hint Unfold receiving.

Inductive is_receiving : process -> Prop :=
  | IsReceiving : forall p n u m, 
                    p = receiving n u m ->
                    is_receiving p.
Hint Constructors is_receiving.                                   

Definition modulo (m : nat) (n : nat) : nat :=
  if ble_nat n m 
  then n
  else n - m.
Hint Unfold modulo.

Definition msg_in_ring_n_round_m (n : nat) (m : nat) (o : nat) : nat :=
  if ble_nat o (S m) then n else (o - 1).
Hint Unfold msg_in_ring_n_round_m.

Definition ring_n_round_m (n : nat) (m : nat) : system :=
  System ((receiving n (UID 1) (n - 1)) 
            :: map (fun o => receiving o (UID (S o)) (msg_in_ring_n_round_m n m o)) (range (n - 1))).
Hint Unfold ring_n_round_m.

Lemma ring_n_round_m_correct : 
  ring_n_round_m 5 2 = System [receiving 5 (UID 1) 4, 
                               receiving 4 (UID 5) 3,
                               receiving 3 (UID 4) 5,
                               receiving 2 (UID 3) 5,
                               receiving 1 (UID 2) 5].
Proof.
  unfold ring_n_round_m. simpl. 
  unfold msg_in_ring_n_round_m. simpl.
  reflexivity.
Qed. 

Definition initialized (n : nat) : system :=
  ring_n_round_m n 0.
Hint Unfold initialized.

(* First, prove by induction on the list, the following lemma:
 forall (s : system), 
     list = proc_list system -> 
     forall p, In p list -> is_receiving p 
  \/ exists lr p ls, list = lr ++ p :: ls,p
          forall p0, In p0 lr -> is_receiving p0
       /\ ~ is_receiving p 
       /\ exists p', p -local-> p' 
       /\ receiving p'
*)       
    
(* And then add in induction upon the list *)