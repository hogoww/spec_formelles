Parameter A B : Prop.
Goal A->B->A.
intros.
assumption.

Parameter C : Prop.
Goal (A->B->C) -> (A -> B) -> A->C.
intros.
apply (H H1).
apply (H0 H1).

Goal A /\ B -> B.
intro.
elim H.
intros.
assumption.

Goal B->A \/ B.
intro.
right.
assumption.

Goal (A \/B) -> (A->C) -> (B-> C) -> C.
intros.
elim H.
assumption.
assumption.

Goal A -> False-> ~A.
intros.
intro.
assumption.

Goal False -> A.
intros.
auto.

Goal (A <->B) -> A->B.
intros.
elim H.
intros.
apply (H1 H0).

Goal (A <->B) -> B->A.
intros.
elim H.
intros.
apply (H2 H0).

Goal (A->B)->(B->A)->(A<->B).
intros.
split.
assumption.
assumption.
(*tauto marche aussi, logique classique decidable*)


(*2nde partie*)
Parameter E : Set.
Parameter P Q : E -> Prop.
Goal forall x : E, (P x) -> exists y : E, (P y) \/ (Q y).
intros.
exists x.
left.
assumption.

Goal (exists x : E, (P x) \/ (Q x)) -> (exists x : E, (P x)) \/ (exists x : E, (Q x)).
intro.
elim H.
intro.
intro.
elim H0.
intro.
left.
exists x.
assumption.
intro.
right.
exists x.
assumption.

Goal (forall x : E, (P x)) /\ (forall x : E, (Q x)) -> forall x : E , (Q x) /\ (P x).
intro.
intro.
split.
apply H.
apply H.

Goal (forall x : E , (Q x) /\ (P x)) -> (forall x : E, (P x)) /\ (forall x : E, (Q x)).
intros.
split.
intro.
apply H.
intro.
apply H.

Goal (forall x : E, ~P(x)) -> ~(exists x : E,P(x)).
intro.
intro.
elim H0.
apply H.

Require Export Classical.
(* Check NNPP. *)

Goal ~(forall x : E, (P x)) -> (exists x : E, ~P(x)).
intro.
apply NNPP.
intro.
apply H.
intro.
apply NNPP.
intro.
apply H0.
exists x.
assumption.



(*load file.v*)
