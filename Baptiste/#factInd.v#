Require Import Omega.
Open Scope list_scope.

(* PAIR*)
Inductive is_even : nat -> Prop :=
| is_even_O : is_even 0
| is_even_S : forall n : nat , is_even n-> is_even (S (S n)).


Fixpoint even (n : nat) : Prop := 
  match n with
  | 0 => True
  | 1 => False
  | (S (S n)) => even n
end.


Functional Scheme even_ind := Induction for even Sort Prop.

Theorem even_sound :
 forall (n : nat) (v : Prop) , (even n) = True -> is_even n.
Proof.
  do 2 intro.
  functional induction (even n) using even_ind; intros.
  apply is_even_O.
  elimtype False; rewrite H; auto.
  apply is_even_S; apply IHP; assumption.
Qed.


(* FACTORIELLE *)

Inductive is_fact : nat -> nat -> Prop :=
| fact_0 :  is_fact 0 1
| fact_S : forall n : nat , forall s : nat , is_fact n s  -> is_fact (S n) (s * (S n)).


Fixpoint fact (n : nat) : nat :=
  match n with 
 | 0 => 1
 | (S n) => (fact n * (S n))
 end.


Functional Scheme fact_ind := Induction for fact Sort Prop.

Theorem fact_sound : 
  forall (n : nat) (r: nat) , (fact n ) = r -> is_fact  n r.
Proof. 
  intro.
  functional induction (fact n) using fact_ind; intros.
  elim H.
  apply fact_0.
  elim H.
  apply fact_S.
  apply (IHn0 (fact n0)).
  reflexivity.
Qed.

(* TRI PAR INSERTION *)

Inductive is_perm : (list nat) -> (list nat) -> Prop := 
| is_perm_refl : forall l1 : (list nat) , is_perm l1 l1
| is_perm_transitive : forall l1 l2 l3 :(list nat) , is_perm l1 l2 -> is_perm l2 l3 -> is_perm l1 l3
| is_perm_sym : forall l1 l2 : (list nat) , is_perm l1 l2 -> is_perm l2 l1
| is_perm_cons : forall l1 l2 : (list nat) , forall a : nat , is_perm l1 l2 -> is_perm (a::l1) (a::l2)
| is_perm_a : forall l1 : (list nat) , forall a : nat , is_perm(a::l1)(l1++ a::nil).


Definition l1 := 1::2::3::nil.
Definition l2 := 3::2::1::nil.

Lemma undeuxtrois : is_perm l1 l2.

unfold l1.
unfold l2.


apply (is_perm_transitive (1::(2::(3::nil))) ((2::(3::nil))++(1::nil)) (3::(2::(1::nil)))).
apply is_perm_a.
simpl.
apply (is_perm_transitive (2::(3::(1::nil))) ((3::(1::nil))++(2::nil)) (3::(2::(1::nil)))).
apply is_perm_a.
simpl.
apply is_perm_cons.
apply (is_perm_transitive (1::(2::nil)) ((1::nil)++(2::nil)) (2::(1::nil))).
simpl.
apply is_perm_cons.
apply is_perm_refl.
apply is_perm_a.
Qed.

Inductive is_sort :(list nat) -> Prop := 
| is_sort_0 : is_sort nil
| is_sort_1 : forall n : nat , is_sort(n::nil)
| is_sort_N : forall n m : nat , forall l :(list nat) ,  n <= m -> is_sort(m::l) -> is_sort (n::m::l).

Lemma sort123 : is_sort l1.
unfold l1.
apply is_sort_N.
omega.
apply is_sort_N.
omega.
apply is_sort_1.
Qed.


Fixpoint Insert (x : nat) (l : (list nat)) : (list nat) := 
  match l with 
 | (nil) => (x::nil)
 | h::t => match le_dec x h with
      | left _ => x::h::t
      | right _ => h::(Insert x t)
      end
end.

Fixpoint Sort (l : (list nat)) : (list nat) :=
 match l with 
 | (nil) => (nil)
 | h::t => (Insert h (Sort t))
end.


Theorem Insert_Sort_Sound :
  forall (l : (list nat)) (l1 : (list nat)) ,(Sort l) = l1 -> (is_perm l l1) /\ (is_sort l1).
Proof. 
induction l.
intros.
split.
simpl in H.
rewrite <- H. 
apply is_perm_refl.
simpl in H.
rewrite <- H.
apply is_sort_0.









 














