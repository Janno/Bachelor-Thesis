Require Import ssreflect ssrbool eqtype fintype finfun seq fingraph.

Set Implicit Arguments.

Section FA.
Variable S: finType.
Definition word := seq S.


Section DFA.
Variable Q: finType.
Definition dfa_rel (d: Q -> S -> Q) := (fun x y => existsb a, d x a == y).
Inductive dfa (s0: Q) (f: pred Q) : rel Q  -> Type :=
| dfaI  (d: Q -> S -> Q) : dfa s0 f 
(dfa_rel d).

Section Acceptance.
Variable s0: Q.
Variable f: pred Q.
Definition AutR {R} (_: dfa s0 f R) := R.

Variable R': rel Q.
Variable A: dfa s0 f R'.

Let R := AutR A.
Definition d: Q -> S -> Q. elim: A => //. Defined.


(* dfa A accepts word w starting in state q *)
Fixpoint accept' (q: Q) (w: word): bool.
Proof. move: q. elim: w => [ | a w IHw ]. 
  exact: (f).
move => q. exact: (accept' (d q a) w).
Defined.
Print accept'.

Definition accept (w: word) := 
accept' s0 w.

Lemma d_connect q a: connect R q (d q a).
Proof. unfold R. rewrite/d. elim: A => /= d0. rewrite/AutR. 
apply/connect1. apply/existsP. by exists a.
Qed.

Definition sink q := forallb q', connect R q q' ==> ~~ f q'.

Lemma sink_trans q q' : sink q -> connect R q q' -> sink q'.
Proof.
move/forallP => H0 H1.
apply/forallP => q''.
move: (H0 q''). case_eq (f q'') => F /=;
case_eq (connect R q' q'') => //=.
move => H2. 
by move: (connect_trans H1 H2) => -> //.
Qed.

Lemma final_not_sink q: f q -> ~~ sink q.
Proof. rewrite/sink => H0. rewrite negb_forall. apply/existsP.
exists q. rewrite negb_imply. apply/andP => //=. split.
  by apply/connect0. 
by apply/negPn.
Qed.

Lemma sink_not_final q: sink q -> ~~ f q.
Proof. rewrite/sink. move/forallP => H0. 
move: (H0 q). move: (connect0 R q) => ->.
move/implyP => H1. exact: H1.
Qed.


Lemma sink_dead_end w q : sink q -> ~~ accept' q w.
move: q. elim: w => [|a w IHw]. 
  move => q H. apply/sink_not_final. by exact: H.
move => q H /=. pose q' := (d q a). fold q'.
apply/IHw. apply/(sink_trans q) => //. apply/d_connect.
Qed.

End Acceptance.
Implicit Arguments accept [R'].


End DFA.

Section NFA.
Variable Q: finType.
Variable s0: Q.
Variable f: pred Q.
Variable d: Q -> S -> pred Q.
Definition Q' := [ finType of {ffun Q -> bool_eqType} ].
Definition f' (q': Q') := existsb q:Q, q' q && f q.
Let s0' : Q' := finfun (fun q:Q => q==s0).

Definition d_det (q': Q') (a: S) : Q' :=
finfun (
 fun (q: Q) => existsb p: Q, q' p && d p a q
).

Definition to_dfa : dfa Q' s0' f' (dfa_rel Q' d_det). constructor. Defined.
End NFA.



End FA.


Section Operators.
(* Operations on two automata with the same alphabet *)
Variable Alph: finType.
Variable Q1 Q2: finType.
Variable s01: Q1.
Variable s02: Q2.
Variable f1: pred Q1.
Variable f2: pred Q2.

Variable R1': rel Q1.
Variable R2': rel Q2.
Variable A1: dfa Alph Q1 s01 f1 R1'.
Variable A2: dfa Alph Q2 s02 f2 R2'.

Let R1 := AutR A1.
Definition d1: Q1 -> Alph -> Q1. elim: A1 => //. Defined.
Let R2 := AutR A2.
Definition d2: Q2 -> Alph -> Q2. elim: A2 => //. Defined.

Definition Q_prod := prod_finType Q1 Q2.

Definition d_or (q: Q_prod) a := let (q1, q2) := q in (d1 q1 a, d2 q2 a).
Definition Aut_or : dfa Alph Q_prod (s01, s02) 
(fun q => let (q1,q2) := q in f1 q1 || f2 q2)
(dfa_rel Alph (Q_prod) d_or).
constructor. Defined.

Lemma Aut_or_correct' w q1 q2 : accept' A1 q1 w || accept' A2 q2 w = accept' Aut_or (q1, q2) w.
Proof. elim: w q1 q2 => [|a w IHw].
  rewrite/accept => //.
rewrite/accept => /=. move => q1 q2. 
by exact: IHw.
Qed.

Lemma Aut_or_correct w: accept A1 w || accept A2 w = accept Aut_or w.
Proof. exact: Aut_or_correct'. Qed.


Definition d_and (q: Q_prod) a := let (q1, q2) := q in (d1 q1 a, d2 q2 a).
Definition Aut_and : dfa Alph Q_prod (s01, s02) 
(fun q => let (q1,q2) := q in f1 q1 && f2 q2)
(dfa_rel Alph (Q_prod) d_or).
constructor. Defined.

Lemma Aut_and_correct' w q1 q2 : accept' A1 q1 w && accept' A2 q2 w = accept' Aut_and (q1, q2) w.
Proof. elim: w q1 q2 => [|a w IHw].
  rewrite/accept => //.
rewrite/accept => /=. move => q1 q2. 
by exact: IHw.
Qed.

Lemma Aut_and_correct w: accept A1 w && accept A2 w = accept Aut_and w.
Proof. exact: Aut_and_correct'. Qed.

Definition Q_sum := sum_finType Q1 Q2.
Definition Q_sum_option := option_finType Q_sum.

Definition Q1_conc (q1: Q1) : Q_sum. constructor. exact q1. Defined.
Definition Q2_conc (q2: Q2) : Q_sum. apply/inr. exact q2. Defined.
Definition s0_conc : Q_sum. constructor. exact: s01. Defined.

Definition d_conc (q: Q_sum) a (q': Q_sum) := 
match q with
| inl q1 => 
  match q' with
  | inl q1' => d1 q1 a == q1'
  | inr q2' => f1 q1 && (q2' == s02)
  end
| inr q2 =>
  match q' with
  | inr q2' => d2 q2 a == q2'
  | _ => false
  end
end.

Definition f_conc (q: Q_sum) :=
match q with
| inr q2 => f2 q2
| _ => false
end.
Definition Aut_conc := to_dfa Alph Q_sum (s0_conc) f_conc d_conc. 



Lemma Aut_conc_correct q1 w1 w2: 
accept' A1 q1 w1 && accept A2 w2 
= accept' Aut_conc (finfun (fun q=> match q with | inl q1 => q1==q1 | _ => false end)) (w1 ++ w2).
elim: w1 q1 w2 => [|a w1 IHw1] q1 w2 //=.
  rewrite/accept. elim: w2 => /=.
Admitted.

Lemma Aut_conc_correct w1 w2: accept A1 w1 && accept A2 w2 = accept Aut_conc (w1 ++ w2).


End Operators.





(* Example *)
(* 2-state 2-character automaton, accepting (true)* *)
Definition Bool := [ finType of bool ].

Definition A := dfaI Bool Bool false id (andb).

Lemma false_to_false q : connect (AutR A) false q -> q = false.
Proof. elim: q => //=. 
move/connectP => [p]. elim: p => [| q' p IHp] //=.
move/andP => []. rewrite {1}/AutR. move/existsP => [] x. rewrite andFb.
rewrite eq_sym. move/eqP => ->. 
by exact: IHp.
Qed.

Lemma false_not_to_true q : ~~ connect (AutR A) false q -> q = true.
Proof. elim: q => //=.
by move: (connect0 (AutR A) false) => ->.
Qed.

Lemma sink_false: sink A false.
Proof. rewrite/sink. apply/forallP => q.
case_eq (connect (AutR A) false q). 
  by move/false_to_false => ->.
move/negbT. by move/false_not_to_true => ->.
Qed.


Goal forall w q, accept' A q w -> ~~(false \in w).
Proof. move => w. elim: w => [ | a w IHw ] //=. rewrite in_cons negb_or.
move => q H.
apply/andP. case: q H; case a; split; move: H => //=; try by exact: IHw.
  move: sink_false => S; by move: (sink_dead_end A w false S) => /negbTE => -> //.
move: sink_false => S; by move: (sink_dead_end A w false S) => /negbTE => -> //.
Qed.



