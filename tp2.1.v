Open Scope type_scope.
Section Iso_axioms.
Variables A B C : Set.
Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.
End Iso_axioms.

Lemma P_unit_bis : forall A : Set,
unit * A = A.
intros.
rewrite Com.
rewrite P_unit.
reflexivity.
Qed.

Lemma isos_ex1 : forall A B:Set,
A * unit * B = B * (unit * A).
intros.
rewrite Ass.
rewrite P_unit.
rewrite P_unit.
rewrite Com.
reflexivity.

Lemma isos_ex2 : forall A B C:Set,
(A * unit -> B * (C * unit)) =
(A * unit -> (C -> unit) * C) * (unit -> A -> B).

intros.
rewrite P_unit.
rewrite P_unit.
rewrite AR_unit.
rewrite AL_unit.
rewrite Dis.
rewrite Dis.
rewrite AR_unit.
rewrite (Com unit (A->C)).
rewrite P_unit.
rewrite Com.
reflexivity.

Ltac all_but_com :=
  repeat
    match goal with
    | |- context[?A * (?B * ?C)] => rewrite Ass
    | |- context[?A * ?B -> ?C] => rewrite Cur
    | |- context[?A -> ?B * ?C] => rewrite Dis
    | |- context[?A * unit] => rewrite P_unit
    | |- context[unit * ?A] =>rewrite P_unit_bis
    | |- context[?A -> unit] => rewrite AR_unit
    | |- context[unit -> ?A] => rewrite AL_unit
    end.


Lemma isos_ex1_1 : forall A B:Set,
A * unit * B = B * (unit * A).
intros.
all_but_com.
rewrite Com.
reflexivity.

Lemma isos_ex2_1 : forall A B C:Set,
(A * unit -> B * (C * unit)) =
(A * unit -> (C -> unit) * C) * (unit -> A -> B).
intros.
all_but_com.
rewrite Com.
reflexivity.