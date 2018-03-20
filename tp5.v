Lemma decid_egal:
 forall (n m : nat), { n = m } + { n <> m }.
double induction n m;intros.
left.
reflexivity.
right.
discriminate.
right.
discriminate.
elim (H0 n0).
intro.
left.
congruence.
intro.
right.
SearchAbout (_ <> _ -> _ <> _).
apply not_eq_S.
assumption.
Defined.
Recursive Extraction decid_egal.


Inductive is_fact : nat -> nat -> Prop :=
| is_fact_O : is_fact 0 1
| is_fact_S : forall n f : nat, is_fact n f -> is_fact (S n) ((S n)*f). 


Lemma fact: 
 forall (n : nat), { v : nat | is_fact n v }.
  intro.
  elim n.
  exists 1.
  apply is_fact_O.
  
  intros.
  elim H.
  intros.
  exists ((S n0)* x).
  apply is_fact_S.
  assumption.

Open Scope list_scope.
Inductive is_map (f : nat -> nat) : (list nat) -> (list nat) -> Prop :=
 | is_map_nil : is_map f nil nil
 | is_map_rec : forall (l1 l2 : list nat) (a : nat),
                 is_map f l1 l2 ->
                 is_map f (a::l1) ((f a)::l2).

Lemma map :forall (f : nat -> nat)(l1 : list nat) , { l2 : list nat | is_map f l1 l2 }.
induction l1.
exists nil.
apply is_map_nil.

elim IHl1.
intros.
exists ((f a)::x).
apply is_map_rec.
apply p.

Ltac add 




