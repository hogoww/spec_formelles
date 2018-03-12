Require Export ZArith.
Open Scope Z_scope.

Inductive expr : Set :=
 |Cte : Z -> expr
 | Plus : expr -> expr -> expr
 | Moins : expr -> expr -> expr
 | Mult : expr -> expr -> expr
 | Div : expr -> expr -> expr.


Inductive eval : expr -> Z -> Prop :=
 | ECte : forall c : Z, eval (Cte c) c
 | EPlus : forall (e1 e2 : expr) (v1 v2 : Z),
   eval e1 v1 -> eval e2 v2 ->
   eval (Plus e1 e2) (v1 + v2)
 | EMoins : forall (e1 e2 : expr) (v1 v2 : Z),
   eval e1 v1 -> eval e2 v2 ->
   eval (Moins e1 e2) (v1 - v2)
 | EMult : forall (e1 e2 : expr) (v1 v2 : Z),
   eval e1 v1 -> eval e2 v2 ->
   eval (Mult e1 e2) (v1 - v2)
 | EDiv : forall (e1 e2 : expr) (v1 v2 : Z),
   eval e1 v1 -> eval e2 v2 ->
   eval (Div e1 e2) (v1 - v2).

Inductive eval2 : expr -> Z -> Prop :=
 | ECte2 : forall c : Z, eval2 (Cte c) c
 | EPlus2 : forall (e1 e2 : expr) (v v1 v2 : Z),
   eval2 e1 v1 -> eval2 e2 v2 -> v = v1 + v2 -> 
   eval2 (Plus e1 e2) v
 | EMoins2 : forall (e1 e2 : expr) (v v1 v2 : Z),
   eval2 e1 v1 -> eval2 e2 v2 -> v = v1 - v2 ->
   eval2 (Moins e1 e2) v
 | EMult2 : forall (e1 e2 : expr) (v v1 v2 : Z),
   eval2 e1 v1 -> eval2 e2 v2 -> v = v1 * v2 ->
   eval2 (Mult e1 e2) v
 | EDiv2 : forall (e1 e2 : expr) (v v1 v2 : Z),
   eval2 e1 v1 -> eval2 e2 v2 -> v = v1 / v2 ->
   eval2 (Div e1 e2) v.



Fixpoint f_eval (e : expr) : Z :=
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

Lemma add : eval2 t1 3.

unfold t1.
eapply EPlus2.
apply ECte2.
apply ECte2.
simpl.
reflexivity.

Qed.


Eval compute in (f_eval t1).

Definition t2 : expr := Moins (Cte 3) (Cte 2).



Definition t3 : expr := Mult (Cte 3) (Cte 2).

Lemma mult : eval2 t3 6.

unfold t3.
eapply EMult2.
apply ECte2.
apply ECte2.
simpl.
reflexivity.
Qed.


Definition t4 : expr := Div (Cte 4) (Cte 2).

Lemma div : eval2 t4 2.

unfold t4.
eapply EDiv2.
apply ECte2.
apply ECte2.
simpl.
reflexivity.
Qed.


Definition t5 : expr := Mult (Mult (Cte 2 ) (Cte 3)) (Cte 6).

Lemma multi : eval2 t5 36.

unfold t5.
eapply EMult2.
eapply EMult2.
apply ECte2.
apply ECte2.
simpl.
auto.
apply ECte2.
auto.



Ltac calcul :=
intros;
(repeat
 match goal with 
 | |- (eval2( Plus _ _)_) => eapply EPlus2
 | |- (eval2( Moins _ _)_) => eapply EMoins2
 | |- (eval2( Mult _ _)_) => eapply EMult2
 | |- (eval2( Div _ _)_) => eapply EDiv2
 | |- (eval2( Cte _ )_) => apply ECte2
end);
auto;
reflexivity.


Definition t6 : expr := Mult (Mult (Cte 2) (Cte 3)) (Cte 5).

Lemma mul : eval2 t6 30.

unfold t6.
calcul.


















