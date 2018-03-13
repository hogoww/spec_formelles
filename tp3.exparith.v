Require Export ZArith.
Open Scope Z_scope.

Inductive expr : Set :=
| Cte : Z -> expr
| Plus : expr -> expr -> expr
| Moins : expr -> expr -> expr
| Mult : expr -> expr -> expr
| Div : expr -> expr -> expr.

Inductive eval : expr -> Z -> Prop :=
| ECte : forall c : Z , eval (Cte c) c
| EPlus : forall (e1 e2 : expr) (v v1 v2 : Z),
eval e1 v1 -> eval e2 v2 -> v = v1 + v2 ->
eval (Plus e1 e2) v
| EMoins : forall (e1 e2 :expr) (v v1 v2 : Z),
eval e1 v1 -> eval e2 v2 -> v = v1 - v2 ->
eval (Moins e1 e2) v
| EMult : forall (e1 e2 : expr) (v v1 v2 : Z),
eval e1 v1 -> eval e2 v2 -> v = v1 * v2 ->
eval (Mult e1 e2) v
| EDiv : forall (e1 e2 : expr) (v v1 v2 : Z),
eval e1 v1 -> eval e2 v2 -> v = v1 / v2 ->
eval (Div e1 e2) v.

Inductive eval2 : expr -> Z -> Prop :=
| ECte2 : forall c : Z , eval2 (Cte c) c
| EPlus2 : forall (e1 e2 : expr) (v1 v2 : Z),
eval2 e1 v1 -> eval2 e2 v2 ->
eval2 (Plus e1 e2) (v1 + v2)
| EMoins2 : forall (e1 e2 :expr) (v1 v2 : Z),
eval2 e1 v1 -> eval2 e2 v2 ->
eval2 (Moins e1 e2) (v1 - v2)
| EMult2 : forall (e1 e2 : expr) (v1 v2 : Z),
eval2 e1 v1 -> eval2 e2 v2 -> 
eval2 (Mult e1 e2) (v1 * v2)
| EDiv2 : forall (e1 e2 : expr) (v1 v2 : Z),
eval2 e1 v1 -> eval2 e2 v2 ->
eval2 (Div e1 e2) (v1 / v2).

Fixpoint f_eval (e:expr) : Z :=
 match e with 
  | Cte c => c
  | Plus e1 e2 =>
   let v1 := f_eval e1 in
   let v2 := f_eval e2 in 
   v1 + v2
  | Moins e1 e2 =>
   let v1 := f_eval e1 in
   let v2 := f_eval e2 in
   v1 - v2
  | Mult e1 e2 =>
   let v1 := f_eval e1 in
   let v2 := f_eval e2 in 
   v1 * v2
  | Div e1 e2 =>
   let v1 := f_eval e1 in
   let v2 := f_eval e2 in 
   v1 / v2
end.


Definition t1 : expr := Plus (Cte 1) (Cte 2).

Lemma add : eval t1 3.
unfold t1.
eapply EPlus.
eapply ECte.
eapply ECte.
reflexivity.
Qed.

Eval compute in (f_eval t1).

Definition t2 : expr := Moins (Cte 3) (Cte 2).

Lemma moins : eval t2 1.
unfold t2.
eapply EMoins.
eapply ECte.
eapply ECte.
reflexivity.
Qed.


Definition t3 : expr := Mult (Cte 3) (Cte 2).

Lemma mult : eval t3 6.
unfold t3.
eapply EMult.
eapply ECte.
eapply ECte.
reflexivity.
Qed.


Definition t4 : expr := Div (Cte 4) (Cte 2).

Lemma div : eval t4 2.

unfold t4.
eapply EDiv.
apply ECte.
apply ECte.
simpl.
reflexivity.
Qed.


Ltac calcul :=
intros;
(repeat
 match goal with 
 | |- (eval (Cte _)_) => eapply ECte
 | |- (eval( Plus _ _)_) => eapply EPlus
 | |- (eval( Moins _ _)_)=> eapply EMoins
 | |- (eval (Mult _ _)_) => eapply EMult
 | |- (eval (Div _ _)_) => eapply EDiv
 end);
try reflexivity.

Definition test_calcul : expr := Div (Mult (Cte 3) (Cte 2)) (Cte 2).

Lemma test_calcul_eval : eval test_calcul 3.
unfold test_calcul.
calcul.

Lemma correction :
 forall (e : expr) (v : Z),
 v=f_eval(e) -> eval e v.
intros.
rewrite H.
elim e;intros.
eapply ECte.
eapply EPlus.
apply H0.
apply H1.
reflexivity.

eapply EMoins.
apply H0.
apply H1.
reflexivity.

eapply EMult.
apply H0.
apply H1.
reflexivity.

eapply EDiv.
apply H0.
apply H1.
reflexivity.
Qed.

Lemma completude:
 forall (e : expr) (v :Z),
 eval e v -> f_eval e = v.
intros.
