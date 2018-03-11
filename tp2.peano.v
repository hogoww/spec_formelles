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

Lemma deuxplusdeux :
(plus (s(s(o))) (s(s(o))))=s(s(s(s(o)))).
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.

Lemma deuxmuldeux :
(mult (s(s(o))) (s(s(o))))=s(s(s(s(o)))).
rewrite ax7.
rewrite ax7.
rewrite ax6.
rewrite ax5.
rewrite ax5.
rewrite ax4.
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.

Ltac calcplusmult:=
  repeat
    match goal with
    | |- context[(mult ?x (s ?y))] => rewrite ax7
    | |- context[(mult ?x o)] => rewrite ax6
    | |- context[(plus ?x (s ?y))] => rewrite ax5
    | |- context[(plus ?x o)] => rewrite ax4
    end.


Lemma deuxplusdeux_1 :
(plus (s(s(o))) (s(s(o))))=s(s(s(s(o)))).
calcplusmult.
reflexivity.

Lemma deuxmuldeux_1 :
(mult (s(s(o))) (s(s(o))))=s(s(s(s(o)))).
calcplusmult.
reflexivity.

Create HintDb plusfois.
Hint Rewrite ax7 ax6 ax5 ax4 : plusfois.

Lemma deuxplusdeux_2 :
(plus (s(s(o))) (s(s(o))))=s(s(s(s(o)))).
autorewrite with plusfois using (try reflexivity).
