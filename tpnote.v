Parameter E : Set.
Parameter P Q : E -> Prop.
Lemma e1_1:
forall x : E, (P x) -> (Q x) -> exists x : E, (P x) -> exists x : E,(Q x).
intro.
exists x.
intro.
exists x.
assumption.
Qed.

Lemma e1_2:
 (exists x : E, (P x)) \/ (exists x : E, (Q x)) -> exists x : E, (P x) \/ (Q x).
intros.
elim H;intros.
elim H0.
intros.
exists x.
left.
assumption.
elim H0.
intros.
exists x.
right.
assumption.
Qed.


Open Scope list.
Require Export List.

Lemma e2:
 forall (A : Set) (l1 l2 : list A), length(l1 ++ l2) = length l1 + length l2.
intros.
elim l1.
elim l2.
reflexivity.
intros.
reflexivity.
intros.

simpl.

auto.
