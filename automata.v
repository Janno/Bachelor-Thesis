Require Import ssreflect ssrbool eqtype fintype finfun seq fingraph ssrfun.

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
Definition Q_ndet := [ finType of {ffun Q -> bool_eqType} ].
Definition f' (q': Q_ndet) := existsb q:Q, q' q && f q.
Let s0' : Q_ndet := finfun (fun q:Q => q==s0).

Definition d_det (q': Q_ndet) (a: S) : Q_ndet :=
finfun (
 fun (q: Q) => existsb p: Q, q' p && d p a q
).

Definition to_dfa : dfa Q_ndet s0' f' (dfa_rel Q_ndet d_det). constructor. Defined.
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
(*Definition d1: Q1 -> Alph -> Q1. elim: A1 => //. Defined.*)
Definition d1 := d A1.
Let R2 := AutR A2.
(*Definition d2: Q2 -> Alph -> Q2. elim: A2 => //. Defined.*)
Definition d2 := d A2.

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
Definition Q_conc := Q_ndet Q_sum.
Definition s0_conc : Q_sum. constructor. exact: s01. Defined.

Definition d_conc (q: Q_sum) a (q': Q_sum) := 
match q with
| inl q1 => 
  match q' with
  | inl q1' => d1 q1 a == q1'
  | inr q2' => f1 q1 && (d2 s02 a == q2')
  end
| inr q2 =>
  match q' with
  | inr q2' => d2 q2 a == q2'
  | _ => false
  end
end.

Definition f_conc (q: Q_sum) :=
match q with
| inl q1 => f1 q1 && f2 s02
| inr q2 => f2 q2
end.
Definition Aut_conc := to_dfa Alph Q_sum (s0_conc) f_conc d_conc. 

Definition q_conc_leq (q1' q2': Q_conc) := forall q, q1' q -> q2' q.

Notation "q1' ===> q2'" := (q_conc_leq q1' q2') (at level 70).

Lemma q_conc_leq_trans (q1' q2' q3': Q_conc) : q1' ===> q2' -> q2' ===> q3' -> q1' ===> q3'.
Proof. rewrite/q_conc_leq. move => H0 H1 q. by move/H0/H1. Qed.

Lemma q_conc_leq_d_trans (q1' q2' : Q_conc) a : 
q1' ===> q2' -> d_det Alph d_conc q1' a ===> d_det Alph d_conc q2' a.
Proof. move => H0 q. rewrite/d_det. rewrite 2!ffunE. 
move/existsP => [] p /andP [] /H0 H1 H2. apply/existsP. exists p. 
by rewrite H1 H2. Qed.

Lemma Aut_conc_expand1 (q1' q2': Q_conc) w:
q1' ===> q2' ->
accept' Aut_conc q1' w ->
accept' Aut_conc q2' w.
Proof. elim: w q1' q2' => [|a w IHw]. 
  rewrite/accept'/f' => /= q1' q2' H. move/existsP => [] q /andP []. 
  move => H0 H1. apply/existsP. move: (H q H0). exists (q). by rewrite H2 H1.
move => q1' q2'. move/(@q_conc_leq_d_trans _ _ a). simpl. 
by apply: IHw.
Qed.

Lemma Aut_conc_correct1' q1 w1: 
accept' A1 q1 w1 && accept A2 [::] 
-> accept' Aut_conc (finfun (fun q=> q == Q1_conc q1)) w1.
Proof.
elim: w1 q1 => [|a w1 IHw1] q1.
  rewrite /f' /f_conc /accept /accept' /=.
  move/andP => [] H0 H1. apply/existsP. exists (Q1_conc q1). 
  rewrite ffunE. apply/andP. split.
    by apply/eqP.
  by rewrite H0 H1.
move => /=. move/andP => [].
move => H0 H1. move: (IHw1 (d A1 q1 a)). 
rewrite H0 H1 => /=. move => H2. move: (H2 is_true_true).
apply Aut_conc_expand1. 
move => q. rewrite 2!ffunE. move/eqP => ->. apply/existsP. 
exists (Q1_conc q1). rewrite ffunE. apply/andP. split.
  by apply/eq_refl.
rewrite/d_conc => /=. by apply/eq_refl.
Qed.


Lemma Aut_conc_correct2' q2 w2: 
accept' A2 q2 w2
-> accept' Aut_conc (finfun (fun q=> q == Q2_conc q2)) w2.
Proof. elim: w2 q2 => [|a w2 IHw2] q2 /=.
  move => H0. rewrite/f'/f_conc. apply/existsP. exists (Q2_conc q2). apply/andP. split.
    by rewrite ffunE.
  by exact: H0.
move/IHw2. apply: Aut_conc_expand1 => q. rewrite 2!ffunE. move/eqP => ->.
apply/existsP. exists (Q2_conc q2). apply/andP. split.
  by rewrite ffunE. 
by rewrite/d_conc => /=.
Qed.

Lemma Aut_conc_end1 q1 a:
f1 q1 ->
d_det Alph d_conc [ffun q => q == Q2_conc s02] a ===> d_det Alph d_conc [ffun q => q == Q1_conc q1] a.
Proof.
rewrite /d_det /d_conc => /=. move => H0 [q|q];
rewrite ffunE => /existsP [] q'; rewrite ffunE => /andP [] /eqP -> /=.
  by [].
rewrite eq_sym ffunE => /eqP ->. apply/existsP. exists (Q1_conc q1).
rewrite ffunE eq_refl andTb. by rewrite H0 eq_refl.
Qed.


Lemma Aut_conc_correct3' q1 w2:
f1 q1 ->
accept' Aut_conc [ffun q => q == Q2_conc s02] w2 ->
accept' Aut_conc [ffun q => q == Q1_conc q1] w2.
Proof. elim: w2 q1 => [|a w2 IHw2] q1 H0 /=.
  rewrite/f'/f_conc. move/existsP => [] q /andP []. rewrite ffunE => /eqP -> /= H1.
  apply/existsP. exists (Q1_conc q1). by rewrite ffunE eq_refl andTb H0 H1.
apply: Aut_conc_expand1. apply: Aut_conc_end1. by exact: H0.
Qed.

Lemma Aut_conc_correct1 q1 w1 w2: (accept' A1 q1 w1 && accept A2 w2) -> accept' Aut_conc [ffun q => q == Q1_conc q1] (w1 ++ w2).
Proof. elim: w1 w2 q1 => [|a w1 IHw1] w2 q1.
  rewrite/accept => /andP [] /= H0. rewrite/s0_conc. move/(Aut_conc_correct2').
  rewrite/Q2_conc. apply: Aut_conc_correct3'. by exact: H0.
simpl. move/IHw1. apply: Aut_conc_expand1 => q.
rewrite /d_det /d_conc ffunE => /eqP -> /=. rewrite ffunE. apply/existsP.
exists (Q1_conc q1). by rewrite ffunE eq_refl andTb eq_refl.
Qed.


Lemma Aut_conc_correct4' w1 w2:
accept A1 w1 -> 
accept' Aut_conc [ffun q => q == Q1_conc s01] (w1 ++ w2) ->
accept A2 w2 \/ accept A1 (w1 ++ w2).
Proof. elim: w1 w2 => [| a w1 IHw1 ] w2 => /=.
  rewrite /accept => /=. apply: Aut_conc_correct3'. 


Lemma Aut_conc_correct2 w: 
accept' Aut_conc [ffun q => q == Q1_conc s01] w -> 
exists w1, exists w2, w = w1 ++ w2 /\ accept A1 w1 && accept A2 w2.
Proof. move: w.
apply: last_ind => [| w a IHw ].
  rewrite /f' /f_conc => /existsP [] q /andP []. rewrite ffunE => /eqP -> /= /andP [] H0 H1.
  exists [::]. exists [::]. rewrite/accept => /=. by rewrite H0 H1.
case_eq (accept' Aut_conc [ffun q => q == Q1_conc s01] w). 
  move/IHw => [] w1 [] w2 [] ->. rewrite rcons_cat.
  move => /andP [] H0 H1 H2. exists w1. exists (rcons w2 a). split.
    by [].
  rewrite H0 andTb.


elim: w => [| a w IHw] /=.



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



