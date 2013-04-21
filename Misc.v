Require Import List.
Require Export Permutation.

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

Fixpoint remove_last {A : Type} (q : list A) : list A :=
  match q with
  | nil => nil
  | h :: nil => nil
  | (h :: t) => h :: (remove_last t)
  end.

Lemma