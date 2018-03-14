(* Require Import FunInd. selon les versions*)

Inductive is_fact : nat -> nat -> Prop :=
| is_fact_O : is_fact 0 1
| is_fact_S : forall n f : nat, is_fact n f -> is_fact (S n) ((S n)*f).


Fixpoint fact (n:nat) : nat :=
match n with
| 0 => 1
| (S n) => (S n)*(fact n)
end.

Functional Scheme fact_ind := Induction for fact Sort Prop.

Theorem fact_sound :
forall (n : nat) (f : nat), (fact n) = f -> is_fact n f.
Proof.
intro.
functional induction (fact n) using fact_ind;intros.
rewrite <-H.
apply is_fact_O.
rewrite <-H.
apply is_fact_S.
apply IHn0.
reflexivity.
Qed.

(*tri*)
Require Import List.
Open Scope list_scope. 

Inductive is perm := (list nat) -> (list nat) -> Prop :=
forall l1 l2  