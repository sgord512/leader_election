Require Import List.
Require Import Lang.

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

Theorem beq_uid_sym : forall i1 i2,
  beq_uid i1 i2 = beq_uid i2 i1.
Proof.
  intros i1 i2. destruct i1. destruct i2. apply beq_nat_sym. Qed.