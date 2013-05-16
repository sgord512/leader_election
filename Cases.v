Require Import Misc.
Require Import Lang.
Require Import Leader. 
Require Import Coq.Logic.Decidable.
Require Import ListExt.
Require Export SfLib.


Inductive is_done : process -> Prop :=
  | cDone : forall s u n, is_done (Process CDone s u n).
Hint Constructors is_done.

Lemma decidable_is_done : forall p, decidable (is_done p).
Proof.
  intros. unfold decidable. destruct p.
  com_cases (destruct c) Case; 
    try solve [right; unfold not; intros; inversion H].
  Case "DONE". 
    left. constructor.
Qed.

Inductive is_sending : process -> Prop :=
  | cSend : forall s u n nbor m, is_sending (Process (CSend (Neighbor nbor) (ANum m)) s u n).
Hint Constructors is_sending.

Lemma decidable_is_sending : forall p, decidable (is_sending p).
Proof. 
  intros. unfold decidable. destruct p.
  com_cases (destruct c) Case;
    try solve [right; unfold not; intros; inversion H].
  Case "SEND";
    aexp_cases (destruct a) SCase;
    try solve [right; unfold not; intros; inversion H].
    SCase "ANum".
      left. destruct n0.
      constructor.
Qed.

Fixpoint isReceiving (c : com) : bool :=
  match c with 
    | CSeq c' _ => isReceiving c'
    | CReceive _ => true
    | _ => false
  end.

Inductive is_receiving : process -> Prop :=
| cReceive : forall c st m msgs u n, 
               isReceiving c = true -> 
               is_receiving (Process c (st, m :: msgs) u n).
Hint Constructors is_receiving.

Lemma decidable_is_receiving : forall p, decidable (is_receiving p).
Proof.
  intros. unfold decidable. destruct p.
  com_cases (induction c) Case;
    try solve [right; unfold not; intros; inversion H; inversion H1].
  Case ";".
    inversion IHc1. 
    SCase "is_receiving c1". 
      inversion H. left. constructor. simpl. assumption.
    SCase "not (is_receiving c1)". 
      right. unfold not. intro. inversion H0. 
      assert (is_receiving (Process c1 s u n)).
      subst. apply cReceive. simpl in H2. assumption. 
      apply H in H6. assumption.
  Case "RECEIVE".
     destruct s. destruct q. 
     SCase "[]". 
       right. unfold not; intros. inversion H.
     SCase "msg :: msgs".
       left. constructor. reflexivity.
Qed.

Definition decidable_list_forall {A : Type} (aProp : A -> Prop) := 
  forall ls,
    decidable (forall x, In x ls -> aProp x).

(*
Tactic Notation "decided" constr(prop) "by" constr(lemma) :=
  assert (decidable prop); apply lemma. 
*)
  
Lemma decidable_in : 
  forall {A : Type} (a : A) (ls : list A), 
    (forall (x y : A), decidable (x = y)) -> 
    decidable (In a ls).
Proof.
  intros. unfold decidable. 
  induction ls as [| l ls']. 
  Case "[]".
    right. intro. inversion H0.
  Case "l :: ls'".
    inversion IHls'.
    SCase "In a ls'".
      left. apply in_cons. assumption.
    SCase "~ In a ls'".
      assert (decidable (a = l)).
      apply H. unfold decidable in H1. inversion H1.
      SSCase "a = l".
        left. unfold In. left. rewrite H2. reflexivity. 
      SSCase "a <> l".
      right. unfold not. intros. 
        inversion H3. apply H2. rewrite H4. reflexivity.
        apply H0 in H4. assumption.
Qed.      

Lemma decidable_list_forall_if_decidable :
  forall {A : Type} (P : A -> Prop),
    (forall (x y : A), decidable (x = y)) -> 
    (forall (a : A), decidable (P a)) -> 
    decidable_list_forall P.
Proof. 
  unfold decidable_list_forall. intros. unfold decidable. 
  induction ls as [| x ls']. 
  Case "[]". left. intros. 
    inversion H1.
  Case "x :: ls". 
    inversion IHls'.
    SCase "forall".
      unfold decidable in H0. 
      assert (decidable (P x)).
      apply H0. unfold decidable in H2.
      inversion H2.
      SSCase "P x".
        left. intros.
        inversion H4. rewrite <- H5. assumption.
        apply H1. assumption.
      SSCase "~ P x".
        right. unfold not. intros. unfold not in H3. apply H3.
        apply H4. apply in_eq.
   SCase "~ forall".
     right. unfold not. intros.
     unfold not in H1.
     apply H1. intros.
     apply H2. apply in_cons. assumption.
Qed.     

Definition decidable_eq (A : Type) : Prop := forall (x y : A), decidable (x = y).
Hint Unfold decidable_eq.

Tactic Notation "start_dec_eq" ident(x) ident(y) := unfold decidable_eq; induction x; induction y.
Tactic Notation "dec" constr(a) constr(b) "via" reference(lemma) := assert (a = b \/ a <> b); apply lemma. 

Lemma decidable_id : decidable_eq id.
Proof. 
  start_dec_eq x y. assert (n = n0 \/ n <> n0). apply dec_eq_nat. 
  inversion H. 
    subst. left. reflexivity.
    right. unfold not. intro.
    apply H0. inversion H1. reflexivity.
Qed. 

Lemma decidable_neighbor : decidable_eq neighbor.
Proof. 
  start_dec_eq x y. unfold decidable. decide equality. apply dec_eq_nat.
Qed. 

Lemma decidable_aexp : decidable_eq aexp.
Proof. 
  start_dec_eq x y;
    try solve [left; reflexivity | right; unfold not; intros; inversion H].
    assert (decidable (i = i0)).
      apply decidable_id. inversion H. 
      left. subst. reflexivity.
      right. unfold not. unfold not in H0. intros. apply H0. inversion H1. reflexivity.
    assert (decidable (n = n0)). apply dec_eq_nat.
    inversion H. 
      left. subst. reflexivity.     
      right. unfold not. unfold not in H0. intros. apply H0. inversion H1. reflexivity.
    assert (decidable (x1 = y1)). apply IHx1.
    inversion H.
      assert (decidable (x2 = y2)). apply IHx2. 
      inversion H1. 
        subst. left. reflexivity.
        right. unfold not. intros. 
        unfold not in H2. apply H2. inversion H3. reflexivity.
      right. unfold not. intros. unfold not in H0. apply H0. inversion H1. reflexivity.
    assert (decidable (x1 = y1)). apply IHx1.
    inversion H.
      assert (decidable (x2 = y2)). apply IHx2. 
      inversion H1. 
        subst. left. reflexivity.
        right. unfold not. intros. 
        unfold not in H2. apply H2. inversion H3. reflexivity.
      right. unfold not. intros. unfold not in H0. apply H0. inversion H1. reflexivity.
    assert (decidable (x1 = y1)). apply IHx1.
    inversion H.
      assert (decidable (x2 = y2)). apply IHx2. 
      inversion H1. 
        subst. left. reflexivity.
        right. unfold not. intros. 
        unfold not in H2. apply H2. inversion H3. reflexivity.
      right. unfold not. intros. unfold not in H0. apply H0. inversion H1. reflexivity.
Qed.        

Tactic Notation "disimilar" :=
    try solve [left; reflexivity | right; unfold not; intros; inversion H].

Lemma decidable_bexp : decidable_eq bexp.
Proof. 
  unfold decidable_eq. intros x y. 
  generalize dependent y. bexp_cases (induction x) Case; intro y.
  bexp_cases (induction y) SCase;
    disimilar. 
  bexp_cases (induction y) SCase; 
    disimilar.
  bexp_cases (induction y) SCase;
    disimilar.
  Case "BEq". SCase "BEq".
  assert (decidable (a = a1)). apply decidable_aexp.
  inversion H.
    assert (decidable (a0 = a2)). apply decidable_aexp.
      inversion H1. 
        subst. left. reflexivity.
        right. unfold not. intros. 
        unfold not in H2. apply H2. inversion H3. reflexivity.
      right. unfold not. intros. unfold not in H0. apply H0. inversion H1. reflexivity.
  bexp_cases (induction y) SCase;
    disimilar.
  Case "BLe". SCase "BLe".      
  assert (decidable (a = a1)). apply decidable_aexp.
  inversion H.
    assert (decidable (a0 = a2)). apply decidable_aexp.
      inversion H1. 
        subst. left. reflexivity.
        right. unfold not. intros. 
        unfold not in H2. apply H2. inversion H3. reflexivity.
      right. unfold not. intros. unfold not in H0. apply H0. inversion H1. reflexivity.
  Case "BNot". destruct y; try disimilar.
  assert (decidable (x = y)) by apply IHx.
  inversion H. subst; left; auto.
  right. intro C; inversion C; contradiction.
  Case "BAnd". destruct y; try disimilar. 
  assert (decidable (x1 = y1)) by apply IHx1.
  assert (decidable (x2 = y2)) by apply IHx2.
  inversion H; inversion H0.
  subst. left. reflexivity.
  right. unfold not. intro. inversion H3. contradiction.
  right. unfold not. intro. inversion H3. contradiction.
  right. unfold not. intro. inversion H3. contradiction.
Qed.

Lemma decidable_com : forall (c c' : com), decidable (c = c').
Proof. 
  intros. unfold decidable. decide equality. 
    apply decidable_aexp. 
    apply decidable_id.
    apply decidable_bexp.
    apply decidable_bexp.
    apply decidable_aexp.
    apply decidable_neighbor.
    apply decidable_id.
Qed.

Lemma decidable_uid : decidable_eq uid.
Proof. 
  unfold decidable_eq. intros. unfold decidable. decide equality. apply dec_eq_nat.
Qed.

Lemma decidable_neighbors : decidable_eq neighbors. 
Proof. 
  unfold decidable_eq. intros. unfold decidable. decide equality.
  apply decidable_uid.
Qed. 

Lemma decidable_store : decidable_eq store.
Proof. 
    unfold decidable_eq. unfold decidable. intros. decide equality.
      apply dec_eq_nat.
      apply decidable_id.
Qed.

Lemma decidable_msgs : decidable_eq (list nat).
Proof. 
  unfold decidable_eq. unfold decidable. intros. decide equality. 
    apply dec_eq_nat.
Qed. 

Lemma decidable_state : decidable_eq state.
Proof. 
  unfold decidable_eq. unfold decidable. intros. decide equality.
    unfold queue in *. apply decidable_msgs. apply decidable_store.
Qed.

Lemma decidable_process : decidable_eq process.
Proof. 
  unfold decidable_eq. intros. unfold decidable. decide equality.
    apply decidable_neighbors.
    apply decidable_uid.
    apply decidable_state.
    apply decidable_com.
Qed.

Lemma decidable_is_done_list : decidable_list_forall is_done.
Proof.  
  unfold decidable_list_forall. apply decidable_list_forall_if_decidable. 
  apply decidable_process. apply decidable_is_done.
Qed.

Lemma decidable_is_sending_list : decidable_list_forall is_sending.
Proof.  
  unfold decidable_list_forall. apply decidable_list_forall_if_decidable. 
  apply decidable_process. apply decidable_is_sending.
Qed.

Lemma decidable_is_receiving_list : decidable_list_forall is_receiving.
Proof.  
  unfold decidable_list_forall. apply decidable_list_forall_if_decidable. 
  apply decidable_process. apply decidable_is_receiving.
Qed.

