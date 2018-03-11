Section Peano.
Parameter N : Set.
Parameter o : N.
Parameter s : N -> N.
Parameters plus mult : N -> N -> N.
Variables x y : N.
Axiom ax1 : ~((s x) = o).
Axiom ax2 : exists z, ~(x = o) -> (s z) = x.
Axiom ax3 : (s x) = (s y) -> x = y.
Axiom ax4 : (plus x o) = x.
Axiom ax5 : (plus x (s y)) = s (plus x y).
Axiom ax6 : (mult x o) = o.
Axiom ax7 : (mult x (s y)) = (plus (mult x y) x).
End Peano.


Lemma add : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).

rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.


Lemma div : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).

rewrite ax7.
rewrite ax7.

rewrite ax5.
rewrite ax5.
rewrite ax5.
rewrite ax5.
rewrite ax4.
rewrite ax4.
rewrite ax6.
reflexivity.
Qed.

Ltac Peano :=
intros;
  (repeat
   match goal with
   | |- context[(plus ?A o)] => rewrite ax4
   | |- context[(plus ?A (?B ?C))] => rewrite ax5
   | |- context[(mult ?A o)] => rewrite ax6
   | |- context[(mult ?A (?B ?C))] => rewrite ax7
   end).

Lemma add_tac : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).

Peano.
reflexivity.
Qed.

Lemma mult_tac : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
Peano.
reflexivity.
Qed.


Hint Rewrite ax4   ax5  ax6  ax7 : peano.

Lemma add_auto : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).

autorewrite with peano using (try reflexivity).
Qed.





















