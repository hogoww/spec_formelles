Goal forall x : nat, 1 * x = x.
intros.
simpl.
elim x.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.


Fixpoint f (n : nat) {struct n} : nat :=
match n with
0 => 1
| S(n) =>2 * f(n)
end.

Lemma fdix :
(f 10)=1024.
simpl.
reflexivity.

Print list.
Open Scope list.Check (0 :: 1 :: nil).

Require Export List.

Lemma rev_proof:
forall E : Type, forall l : (list E), forall a : E, rev (l ++ a::nil)=a ::rev l.
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


(*Lemma list_identity :
Goal forall (E : Type) (l : list E), l ++ nil = l.
intros.
elim l.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.
Qed.
*)

Lemma rev_consistence :
forall E : Type, forall l : (list E), rev(rev l) = l.
intros.
elim l.
reflexivity.
intros.
simpl.
rewrite rev_proof.
rewrite H.
reflexivity.

Lemma my_eq_nat_dec :
forall n m : nat, {n = m} + {n <> m}.
decide equality.
(*No idea how to do that*)


Inductive binary_tree ( A : Type ) : Type

