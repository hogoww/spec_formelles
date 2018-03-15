Open Scope list.
Require Export List.
Require Import Omega.

Inductive is_perm : (list nat) -> (list nat) -> Prop :=
| is_perm_refl :forall l : (list nat), is_perm l l
| is_perm_sym : forall l1 l2 : (list nat), is_perm l1 l2 -> is_perm l2 l1
| is_perm_transi : forall l1 l2 l3 : (list nat), is_perm l1 l2 -> is_perm l2 l3 -> is_perm l1 l3
| is_perm_cons : forall (a : nat) (l1 l2 : (list nat)), is_perm l1 l2 -> is_perm (a::l1) (a::l2)
| is_perm_a : forall (a : nat) (l : (list nat)), is_perm (a::l) (l++a::nil).



Definition l1 : (list nat) := 1::2::3::nil.
Definition l2 : (list nat) := 3::2::1::nil.

Lemma lemma1 : is_perm l1 l2.
unfold l1.
unfold l2.
apply (is_perm_transi (1::2::3::nil) ((2::3::nil)++1::nil) (3::2::1::nil)).
apply is_perm_a.
apply (is_perm_transi (2::3::1::nil) ((3::1::nil)++2::nil) (3::2::1::nil)).
apply is_perm_a.
apply is_perm_cons.
apply (is_perm_transi (1::2::nil) ((1::nil)++(2::nil)) (2::1::nil)).
apply is_perm_cons.
apply is_perm_refl.
apply is_perm_a.
Qed.

Inductive is_sorted : (list nat) -> Prop :=
| is_sorted_nil : is_sorted nil
| is_sorted_base : forall a : nat , is_sorted (a::nil)
| is_sorted_rec : forall (a b : nat) (l : (list nat)), a <= b -> is_sorted (b::l) -> is_sorted (a::b::l).


Lemma lemma2 : is_sorted l1.
unfold l1.
apply is_sorted_rec.
omega.
apply is_sorted_rec.
omega.
apply is_sorted_base.
Qed.

Fixpoint sorted_insert (n : nat) (l : (list nat)) : (list nat) :=
match l with
 | (nil) => (n::nil)
 | (a::h)=> match le_dec n a with 
           | left _=> n::a::h
           | right _=> a::(sorted_insert n h)
           end
 end.

Fixpoint insert_sort (l : (list nat)) : (list nat):=
match l with
 | (nil) => (nil)
 | a::h => (sorted_insert a (insert_sort h))
end.

Theorem insert_sort_corre: 
forall (l1 : (list nat)) (l2 : (list nat)),(insert_sort l1) = l2 -> (is_perm l1 l2)  /\ (is_sorted l2).
induction l3.
simpl.
intro.

intro.
rewrite <- H.
split.
apply is_perm_refl.
apply is_sorted_nil.

simpl.
intro.
rewrite 

reflexivity.