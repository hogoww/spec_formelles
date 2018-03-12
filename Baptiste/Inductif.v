Lemma Na : forall N :nat, (N * 1) = N.
intros.
elim N.
simpl.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.
Qed.


Fixpoint f (n : nat) {struct n} : nat := 
 match n with 
 | 0 => 1
 | S p => 2 * (f p)
end.

Lemma  f10 : (f 10) = 1024.

simpl.
reflexivity.
Qed.

Require Export List.
Lemma trois : forall E: Type ,forall l : list E, forall e:
E , rev(l ++ e::nil) = e :: rev l.
intros.
elim l.
simpl.
reflexivity.
intros.
simpl.
rewrite H.
simpl.
reflexivity.
Qed.


Lemma quatre : forall E : Type , forall l : list E , rev(rev l) = l.
intros.
elim l.
simpl.
reflexivity.
intros.
simpl.
rewrite trois.
rewrite H.
reflexivity.
Qed.



Inductive is_even : nat -> Prop :=
| is_even_0 : is_even 0
| is_even_S : forall n : nat, is_even n -> is_even (S (S n)).

Lemma iseven2 : is_even 2.
apply is_even_S.
apply is_even_0.
Qed.


Ltac isEven :=
intros;
(repeat
 apply is_even_S);
  apply is_even_0.


Lemma is_even4 : is_even 4.

isEven.
Qed.

Ltac NotIsEven :=
intro;
(repeat
match goal with  
|H : is_even ?A |-_ => inversion H
end).

Lemma nonIsEven3 : ~is_even 2037.

NotIsEven.




















