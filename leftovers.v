
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
