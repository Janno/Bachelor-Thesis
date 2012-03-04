Require Import ssreflect ssrbool eqtype fintype finfun seq fingraph ssrfun ssrnat.

Set Implicit Arguments.

(* Finite automata. *)
Section FA.
(* input alphabet. *)
Variable char: finType.
(* Type of input sequences *)
Definition word := seq char.

(* Deterministic finite automata.
   This is the only actual type of automata.
   NFAs will be translated on the fly (they
   never exist as instances of some type). *)
Section DFA.

(* The (finite) type of states *)
Variable state: finType.

(* The inductive type of deterministic finite automata *)
Inductive dfa (s0: state) (fin: pred state) (step: state -> char -> state) : Type :=
    | dfaI : dfa s0 fin step.


(* Acceptance on DFAs *)
Section Acceptance.

(* Assume some automaton *)
Variable s0_: state.
Variable fin_: pred state.
Variable step_: state -> char -> state.
Variable A: dfa s0_ fin_ step_.

(* This is a giant, steaming pile of hack.
   (It forces all the following functions to
   take an automaton as argument.) *)
Definition A_s0 := [fun A: dfa s0_ fin_ step_ => s0_ ].
Definition A_fin := [ fun A: dfa s0_ fin_ step_ => fin_ ].
Definition A_step := [ fun A: dfa s0_ fin_ step_ => step_ ].
Let s0 := A_s0 A.
Let fin := A_fin A.
Let step := A_step A.

(* We define a run of w on the automaton A
   to be the list of states x_1 .. x_|w|
   traversed when following the edges labeled
   w_1 .. w_|w| starting in x. *)
Fixpoint run' (x: state) (w: word) : seq state :=
match w with
  | [::] => [::]
  | a::w => (step x a) ::run' (step x a) w
end.

(* A simplifying function for a "complete" run
   (i.e. starting at s0). *)
Definition run := [fun w => run' s0 w].

(* Acceptance of w in x is defined as
   finality of the last state of a run of w on A
   starting in x. *)
Definition accept' := [ fun x w => fin (last x (run' x w) ) ].

(* Acceptance of w on A starting in s0. *)
Definition accept := [fun w => accept' s0 w].

(* A lemma that helps us avoid cumbersome unfolding of accept' *)
Lemma accept'S x a w : accept' x (a::w) = accept' (step x a) w.
Proof. elim: w x a => [|b w IHw] x a //=. Qed.
(* Same for run' *)
Lemma run'S x a w : run' x (a::w) = (step x a) :: run' (step x a) w.
Proof. by []. Qed.
  
(* The size of a run is the size of the input word. *)
Lemma run_size x w : size (run' x w) = size w.
Proof. elim: w x => [|a w IHw] x //=.
  by rewrite IHw.
Qed.

(* take lemma. *)
Lemma run'_take x w n: take n (run' x w) = run' x (take n w).
Proof. elim: w x n => [|a w IHw] x n //.
rewrite run'S 2!take_cons. case: n => [|n] //.
by rewrite IHw run'S.
Qed.

(* rcons and cat lemmas. *)
Lemma run'_cat x w1 w2 : run' x (w1 ++ w2) = run' x w1 ++ run' (last x (run' x w1)) w2.
Proof. elim: w1 w2 x => [|a w1 IHw1] w2 x //.
simpl. by rewrite IHw1.
Qed.

Lemma run'_rcons x w a : run' x (rcons w a) = rcons (run' x w) (step (last x (run' x w)) a).
Proof. move: w a x. apply: last_ind => [|w b IHw] a x //.
rewrite -3!cats1. rewrite 2!run'_cat. by [].
Qed.

  

(* Predicate to distinguish between accepting
   and non-accepting runs. *)
Definition run_accepting := [fun x xs => fin (last x xs)].

Definition run_accepts x xs w := xs = run' x w.

End Acceptance.


End DFA.

(* Non-deterministic automata. These exist only
   implicitly as non-functional transitions. *)
Section NFA.

(* Usual stuff. *)
Variable state: finType.
Variable s0: state.
Variable fin: pred state.

(* Non-functional transitions. *)
Variable step_rel: state -> char -> pred state.

(* Type of states after powerset construction. *)
Definition state_det := [ finType of {ffun state -> bool_eqType} ].

(* Finality predicate after powerset construction. *)
Definition fin_det := [ fun q': state_det => existsb q:state, q' q && fin q ].
Definition s0_det : state_det := [ ffun q:state => q==s0 ].

(* Functional step after powerset construction. *)
Definition step_det := [ fun (x': state_det) (a: char) => 
[ ffun x => existsb y: state, x' y && step_rel y a x ] ].

(* Conversion from a non-functional transitions to a DFA. *)
Definition to_dfa := dfaI state_det s0_det fin_det step_det.

End NFA.

End FA.

Hint Unfold A_step.
Hint Unfold A_s0.
Hint Unfold A_fin.

(* Operations on up to two automata with the same alphabet *)
Section Operators.
Variable char: finType.
Variable state1 state2: finType.
Variable s01: state1.
Variable s02: state2.
Variable fin1: pred state1.
Variable fin2: pred state2.
Variable step1: state1 -> char -> state1.
Variable step2: state2 -> char -> state2.

Variable A1: dfa char state1 s01 fin1 step1.
Variable A2: dfa char state2 s02 fin2 step2.


(* Complement automaton *)

(* The only change needed is to negate the finality predicate. *)
Definition fin_not := [ fun q1 => ~~ fin1 q1 ].
(* We construct the resulting automaton. *)
Definition Aut_not := dfaI char state1 s01 fin_not step1.

(* We proof that the complement automaton accepts exactly
   the words not accepted by the original automaton. *)
Lemma Aut_not_correct w q: accept' A1 q w = ~~ accept' Aut_not q w.
Proof.
  by apply/idP/negPn.
Qed.


(* Star automaton. *)

(* We change the finality predicate s.t. only the starthing
   state will be accepting. *)
Definition fin_star' := [ pred x | x == s01 ].
(* The type of states in the star automaton. *)
Definition state_star := state_det state1.
(* We construct a non-functional relation which is 
   the new transitions of the star automaton.
   Whenever we enter a former final state, we
   also enter the starting state, thereby ensuring
   acceptance. *)
Definition step_rel_star : state1 -> char -> pred state1 := (fun x1 a => [ pred x2 | (x2 == step1 x1 a) || (fin1 (step1 x1 a) && (x2 == s01)) ] ).
(* We construct the star automaton. *)
(* Definition Aut_star := to_dfa char state1 s01 fin_star' step_rel_star. *)
Definition step_star := step_det char step_rel_star.
Definition s0_star := s0_det state1 s01.
Definition fin_star := fin_det state1 fin_star'.
Definition Aut_star := dfaI char (state_det state1) s0_star fin_star step_star.

(* We proof that membership in state powerset is
   preserved by step and step_star. *)
Lemma step_step_star x (X: state_star) a : X x -> (step_star X a) (step1 x a).
move => H0 /=. rewrite /step_rel_star ffunE. apply/existsP. exists x.
rewrite H0 andTb. rewrite /SimplPred => /=. by rewrite eq_refl orTb.
Qed.

(* Starting state correctness. *)
Lemma Aut_star_s0 : s0_star s01. by rewrite /s0_star /s0_det ffunE eq_refl. Qed.

(* step_star_rel invariant. *)
Lemma Aut_star_step_rel (X: state_star) a: fin_star (step_star X a) -> (step_star X a) s01.
Proof. simpl. move/existsP => [] x. by rewrite andbC => /andP [] /eqP ->. Qed.
  
(* We proof that the empty word is contained in the
   language of the star automaton. *)
Lemma Aut_star_correct0 : accept Aut_star [::].
Proof. rewrite/accept/accept'/fin_star => /=. apply/existsP. exists s01.
by rewrite /s0_det ffunE eq_refl. Qed.

(* We proof that all non-empty words accepted by the
   original automaton are also accepted by the star
   automaton.
   Translating x to [pred x' | x'==x] gives us an
   induction hypothesis which is too weak to prove
   the statement. Therefore, we allow the star automaton
   to start from any set of states containing x.
   *)
Lemma Aut_star_correctS (X: state_star) a w x :
  X x -> accept' A1 x (a::w) -> accept' Aut_star X (a::w).
Proof. elim: w a X x => [| b w IHw ] a X x H0.
  move => /= H1. apply/existsP. exists s01. rewrite ffunE eq_refl andbT.
  apply/existsP. exists x. rewrite H0 andTb /step_rel_star /=.
  by rewrite H1 eq_refl orbT.
rewrite accept'S. apply: IHw. rewrite ffunE. apply/existsP. exists x.
by rewrite H0 andTb /step_rel_star /= eq_refl.
Qed.

(* We show that every accepting run of the
   star automaton ends in a state Y s.t. Y s01. *)
Lemma Aut_star_end X w: accept' Aut_star X w -> last X (run' Aut_star X w) s01.
Proof. elim: w X => [|a w IHw] X.
  by move => /= /existsP [] q /andP [] H0 /eqP <-.
rewrite accept'S. by apply: IHw.
Qed.

(* We define a predicate on star runs and
   normal runs, which decides if the normal run
   is contained in the star run, i.e. for
   every X_i and x_i: X_i x_i *) 
Fixpoint Aut_star_run_contains (Xs: seq state_star) (xs: seq state1) : bool :=
match Xs, xs with
  | [::] , [::]  => true
  | X::Xs, x::xs => X x && Aut_star_run_contains Xs xs
  | _    , _     => false
end.

(* We define the notion of a shortest, non-empty, accepting prefix *)
Definition Aut_star_prefix (X: state_star) (w: word char) (n: nat) : bool :=
      (n > 0) && (n <= size w) && (accept' Aut_star X (take n w)) &&
  forallb n': ordinal n, (n' > 0) ==> ~~ accept' Aut_star X (take n' w).

(* We proof that there are no shorter prefixes than the shortest prefix. *)
Definition Auf_star_prefix_shortest (X: state_star) (w: word char) (n: nat) :
  Aut_star_prefix X w n -> forallb n' : 'I_n, ~~ Aut_star_prefix X w n'.
Proof. move: w X. apply: last_ind => [| w b IHw ] X.
  rewrite /Aut_star_prefix => /andP [] /andP [] /andP []. rewrite lt0n => H0.
  rewrite leqn0 => H1. by move: H1 H0 => ->.
rewrite /Aut_star_prefix => /andP [] /andP [] /andP [] H0 H1 H2 /forallP H3.
apply/forallP => m. rewrite 3!negb_and. apply/orP. left.
case_eq (nat_of_ord m == 0).
  by move/eqP => ->.
move/neq0_lt0n => H4. apply/orP. right.
move: (H3 m) => /implyP. move => H5. apply: H5. by [].
Qed.

(* We proof that there is a shortest, non-empty, accepting prefix
   for every non-empty word accept by the star automaton. *)
Lemma Aut_star_run_shortest (X: state_star) (a: char) w:
  accept' Aut_star X (rcons w a) ->
  exists n,
    Aut_star_prefix X (rcons w a) n.
Proof. move: w a X. apply: last_ind => [| w b IHw] a X.
  move => H0. 
  exists 1. apply/andP. split.
    rewrite andTb. by exact: H0. 
  apply/forallP => x. apply/implyP. move: (ltn_ord x).
  rewrite leq_eqVlt => /andP [] /eqP H1.
  (* this is a very convoluted way of proving that x=0. *)
  case_eq (nat_of_ord x) => [|x'].
    by [].
  move/(f_equal S). rewrite H1. move/(f_equal predn). by [].
 
move => H0.
(* See if there already is a prefix: *)
case_eq (existsb m : 'I_ (size (rcons w b)), Aut_star_prefix X (rcons w b) m).
  move/existsP => [] m /andP [] /andP [] /andP [] H1 H2 H3 /forallP H4.
  pose n:=nat_of_ord m.
  exists n. apply/andP. split.
    apply/andP. split.
      apply/andP. split => //.
      rewrite size_rcons. move: H2. by apply: leqW.
    rewrite -cats1 (takel_cat H2). by exact: H3.
  apply/forallP => k. apply/implyP => H5.
  rewrite -cats1 takel_cat. move: H5. apply/implyP. by exact: H4.
  apply: leq_trans. apply ltnW. apply ltn_ord. by [].

move/negbT. rewrite negb_exists => /forallP H1. exists (size (rcons (rcons w b) a)).
apply/andP. split.
  apply/andP. split.
    by rewrite size_rcons ltn0Sn ltnSn.
  rewrite take_size. by exact: H0.
apply/forallP.

  
      



(* We proof that there is a shortest, non-empty, accepting prefix
   for every non-empty word accept by the star automaton. *)
Lemma Aut_star_run_shortest X a w:
  accept' Aut_star X (rcons w a) ->
  exists n,
    Aut_star_prefix X (rcons w a) n.
Proof. move: w a X. apply: last_ind => [| w b IHw] a X.
  move => H0. 
  exists 1. apply/andP. split.
    rewrite andTb. by exact: H0. 
  apply/forallP => x. apply/implyP. move: (ltn_ord x).
  rewrite leq_eqVlt => /andP [] /eqP H1.
  (* this is a very convoluted way of proving that x=0. *)
  case_eq (nat_of_ord x) => [|x'].
    by [].
  move/(f_equal S). rewrite H1. move/(f_equal predn). by [].
 
move => H0.
(* 2 cases: - Aut_star accepts (rcons w b) and IHw can be used to
              find the shortest prefix.
            - Aut_star does not accept rcons w b
              *)
case_eq (accept' Aut_star X (rcons w b)) => H1; [move: (IHw b X H1)|].
  move => [] n.
  rewrite /Aut_star_prefix => /andP [] /andP [] /andP [] H2 H3 H4 /forallP H5.
  exists n. apply/andP. split.
    apply/andP. split.
      apply/andP. split => //.
      rewrite size_rcons. move: H3. by apply leqW.
    rewrite -2!cats1 takel_cat.
      by rewrite cats1.
    rewrite cats1. by exact H3.
  apply/forallP => n'. 
  rewrite -{1}cats1 take_cat.
  move: (leq_trans (ltn_ord n') H3) => ->.
  apply: H5.
(* 2 cases:  *)  
  
  
  
Lemma Aut_star_help : seq state_star -> seq (state1 -> bool).
Proof. rewrite /state_star /state_ndet. move => xs. elim: xs => [|x xs IHxs].
  exact: nil.
apply: cons. move: x. move/finfun. by [].
exact IHxs.
Qed.

Lemma Aut_star_det_run (X: state_star) Xs :
  (exists x, fin1 x) ->
  X s01 ->
  run_accepting Aut_star X (X::Xs) ->
  last X (X::Xs) s01 ->
  all [fun X' => ~~X' s01] (Aut_star_help Xs) ->
  exists x, exists xs,
    size (x::xs) = size (X::Xs)
    /\ run_accepting A1 x (x::xs)
    /\ all (fun (t: state_star * state1) => let (X,x) := t in X x) (zip (X::Xs) (x::xs)).
Proof. move => [] z H0. elim: Xs X => [|x Xs IHXs] X.
  move => H1 /existsP [] x /andP [] /= H2 /eqP H3 H4 _.
  exists z. exists nil. split => //=. rewrite andbT.
  split => //.

(* Next, we show that every non-empty word accepted
   by the star automaton generates a run which
   has a non-empty prefix ending in X s.t. X s01. *)
Lemma Aut_star_correct' (X: state_star) a w :
  accept' Aut_star X (a::w) -> let xs := run' Aut_star X (a::w) in exists n.
Proof.


(* We proof that (step_star s0_star a) is a subset
   of all (step_star X a) s.t. fin_star X. *)
Lemma Aut_star_s0_sub X a :
  fin_star X -> subpred (step_star s0_star a) (step_star X a).
Proof. rewrite /fin_star/fin_det/fin_star' /s0_star/s0_det => /=. move/existsP => [] x /andP [] H0 /orP []; [ move => H1 y | move/eqP => <- y ]; rewrite ffunE;
move/existsP => [] z; rewrite 2!ffunE /step_rel_star;
move/andP => [] /eqP -> /= H2.
      apply/existsP. exists s01. rewrite H2 andbT /=.
      
      right. by rewrite H1 andTb eq_refl.
    move/andP => [] H2 /eqP ->. apply/existsP. exists x. rewrite H0 andTb. apply/orP.
    right. by rewrite H1 andTb eq_refl.
  move/eqP => ->. apply/ existsP. exists x. rewrite H0 andTb. apply/orP.
  left. by rewrite eq_refl.
move/andP => [] H1 /eqP ->. apply/existsP. exists x. rewrite H0 andTb.
apply/orP. right. by rewrite H1 eq_refl.
Qed.

(* We proof that the subset relation is transitive
   under step_star. *)
Lemma Aut_star_subpred_trans (X Y: state_star) a : subpred X Y -> subpred (step_star X a) (step_star Y a).
simpl. move => H0 x. rewrite 2!ffunE. move/existsP => [] y /andP [] /H0 H1 H2.
apply/existsP. exists y. by rewrite H1 H2.
Qed.

(* We proof that powerset states accept
   all words of all subsets *)
Lemma Aut_star_subpred (X Y: state_star) w:
 subpred X Y ->
   (accept' Aut_star X) w -> (accept' Aut_star Y) w.
Proof. elim: w X Y => [|a w IHw] X Y.
  move => H0 /existsP [] x /andP [] /= H1 H2.
  apply/existsP. exists x. rewrite H2 andbT.
  apply: H0. by [].
rewrite 2!accept'S. move => H0. apply: IHw. move: H0. by exact: Aut_star_subpred_trans.
Qed.

 
(* We proof that final states accept all words
   accepted by the inital state. *) 
Lemma Aut_star_correct' w (X: state_star) : fin_star X -> accept Aut_star w -> accept' Aut_star X w.
Proof. elim: w X => [| a w IHw ] X. 
  rewrite/fin_star/fin_det/ffunE. move => H0 _. simpl. rewrite /fin_star' in H0.
  by move: H0 => /=. 
move/(@Aut_star_s0_sub X a).
apply: Aut_star_subpred.
Qed.

Lemma Aut_star_correct'' a w: accept Aut_star (a::w) -> exists w1, exists w2, w = w1 ++ w2 /\ accept A1 (a::w1) /\ accept Aut_star w2.
Proof. rewrite {1}/accept {1}/accept' => /existsP [] x /andP [] H0 H1. simpl in H0.
elim: w H0 => [|b w IHw].
  move => H0. rewrite ffunE in H0. move/existsP: H0 => [] y /andP [] H0 H2.
  exists [::]. exists [::]. split. by [].
  split. simpl. rewrite/step_rel_star in H2. rewrite /s0_det ffunE in H0.
  move/eqP: H0 H2 => H0 /=.
  move/orP => []. move => H2. move: H1. move/eqP: H2 => ->. move: H0 => ->.
  rewrite /fin_star' => /orP [] //.  
  
  rewrite Aut_star_correct0. 
  

  rewrite {1}/accept/accept' {1}[[fun _ => _] _]/=.
elim: w => [|b w IHw].
  simpl.

  
  


Definition state_prod := prod_finType state1 state2.

Definition d_or (q: state_prod) a := let (q1, q2) := q in (step1 q1 a, step2 q2 a).
Definition Aut_or : dfa char state_prod (s01, s02) 
(fun q => let (q1,q2) := q in fin1 q1 || fin2 q2)
(dfa_rel char (state_prod) d_or).
constructor. Defined.

Lemma Aut_or_correct' w q1 q2 : accept' A1 q1 w || accept' A2 q2 w = accept' Aut_or (q1, q2) w.
Proof. elim: w q1 q2 => [|a w IHw].
  rewrite/accept => //.
rewrite/accept => /=. move => q1 q2. 
by exact: IHw.
Qed.

Lemma Aut_or_correct w: accept A1 w || accept A2 w = accept Aut_or w.
Proof. exact: Aut_or_correct'. Qed.


Definition d_and (q: state_prod) a := let (q1, q2) := q in (step1 q1 a, step2 q2 a).
Definition Aut_and : dfa char state_prod (s01, s02) 
(fun q => let (q1,q2) := q in fin1 q1 && fin2 q2)
(dfa_rel char (state_prod) d_or).
constructor. Defined.

Lemma Aut_and_correct' w q1 q2 : accept' A1 q1 w && accept' A2 q2 w = accept' Aut_and (q1, q2) w.
Proof. elim: w q1 q2 => [|a w IHw].
  rewrite/accept => //.
rewrite/accept => /=. move => q1 q2. 
by exact: IHw.
Qed.

Lemma Aut_and_correct w: accept A1 w && accept A2 w = accept Aut_and w.
Proof. exact: Aut_and_correct'. Qed.

Definition state_sum := sum_finType state1 state2.
Definition state_sum_option := option_finType state_sum.

Definition state1_conc (q1: state1) : state_sum. constructor. exact q1. Defined.
Definition state2_conc (q2: state2) : state_sum. apply/inr. exact q2. Defined.
Definition state_conc := state_ndet state_sum.
Definition s0_conc : state_sum. constructor. exact: s01. Defined.

Definition d_conc (q: state_sum) a (q': state_sum) := 
match q with
| inl q1 => 
  match q' with
  | inl q1' => step1 q1 a == q1'
  | inr q2' => fin1 q1 && (step2 s02 a == q2')
  end
| inr q2 =>
  match q' with
  | inr q2' => step2 q2 a == q2'
  | _ => false
  end
end.

Definition f_conc (q: state_sum) :=
match q with
| inl q1 => fin1 q1 && fin2 s02
| inr q2 => fin2 q2
end.
Definition Aut_conc := to_dfa char state_sum (s0_conc) f_conc d_conc. 

Lemma q_conc_leq_d_trans (q1' q2' : state_conc) a : 
q1' ===> q2' -> step_det char d_conc q1' a ===> step_det char d_conc q2' a.
Proof. move => H0 q. rewrite/step_det. rewrite 2!ffunE. 
move/existsP => [] p /andP [] /H0 H1 H2. apply/existsP. exists p. 
by rewrite H1 H2. Qed.

Lemma Aut_conc_expanstep1 (q1' q2': state_conc) w:
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
-> accept' Aut_conc (finfun (fun q=> q == state1_conc q1)) w1.
Proof.
elim: w1 q1 => [|a w1 IHw1] q1.
  rewrite /f' /f_conc /accept /accept' /=.
  move/andP => [] H0 H1. apply/existsP. exists (state1_conc q1). 
  rewrite ffunE. apply/andP. split.
    by apply/eqP.
  by rewrite H0 H1.
move => /=. move/andP => [].
move => H0 H1. move: (IHw1 (d A1 q1 a)). 
rewrite H0 H1 => /=. move => H2. move: (H2 is_true_true).
apply Aut_conc_expanstep1. 
move => q. rewrite 2!ffunE. move/eqP => ->. apply/existsP. 
exists (state1_conc q1). rewrite ffunE. apply/andP. split.
  by apply/eq_refl.
rewrite/d_conc => /=. by apply/eq_refl.
Qed.


Lemma Aut_conc_correct2' q2 w2: 
accept' A2 q2 w2
-> accept' Aut_conc (finfun (fun q=> q == state2_conc q2)) w2.
Proof. elim: w2 q2 => [|a w2 IHw2] q2 /=.
  move => H0. rewrite/f'/f_conc. apply/existsP. exists (state2_conc q2). apply/andP. split.
    by rewrite ffunE.
  by exact: H0.
move/IHw2. apply: Aut_conc_expanstep1 => q. rewrite 2!ffunE. move/eqP => ->.
apply/existsP. exists (state2_conc q2). apply/andP. split.
  by rewrite ffunE. 
by rewrite/d_conc => /=.
Qed.

Lemma Aut_conc_end1 q1 a:
fin1 q1 ->
step_det char d_conc [ffun q => q == state2_conc s02] a ===> step_det char d_conc [ffun q => q == state1_conc q1] a.
Proof.
rewrite /step_det /d_conc => /=. move => H0 [q|q];
rewrite ffunE => /existsP [] q'; rewrite ffunE => /andP [] /eqP -> /=.
  by [].
rewrite eq_sym ffunE => /eqP ->. apply/existsP. exists (state1_conc q1).
rewrite ffunE eq_refl andTb. by rewrite H0 eq_refl.
Qed.


Lemma Aut_conc_correct3' q1 w2:
fin1 q1 ->
accept' Aut_conc [ffun q => q == state2_conc s02] w2 ->
accept' Aut_conc [ffun q => q == state1_conc q1] w2.
Proof. elim: w2 q1 => [|a w2 IHw2] q1 H0 /=.
  rewrite/f'/f_conc. move/existsP => [] q /andP []. rewrite ffunE => /eqP -> /= H1.
  apply/existsP. exists (state1_conc q1). by rewrite ffunE eq_refl andTb H0 H1.
apply: Aut_conc_expand1. apply: Aut_conc_end1. by exact: H0.
Qed.

Lemma Aut_conc_correct1 q1 w1 w2: (accept' A1 q1 w1 && accept A2 w2) ->
  accept' Aut_conc [ffun q => q == state1_conc q1] (w1 ++ w2).
Proof. elim: w1 w2 q1 => [|a w1 IHw1] w2 q1.
  rewrite/accept => /andP [] /= H0. rewrite/s0_conc. move/(Aut_conc_correct2').
  rewrite/state2_conc. apply: Aut_conc_correct3'. by exact: H0.
simpl. move/IHw1. apply: Aut_conc_expand1 => q.
rewrite /step_det /d_conc ffunE => /eqP -> /=. rewrite ffunE. apply/existsP.
exists (state1_conc q1). by rewrite ffunE eq_refl andTb eq_refl.
Qed.

Lemma Aut_conc_correct2 w: 
accept' Aut_conc [ffun q => q == state1_conc s01] w -> 
exists w1, exists w2, w = w1 ++ w2 /\ accept A1 w1 && accept A2 w2.
Proof. move: w.
apply: last_ind => [| w a IHw ].
  rewrite /f' /f_conc => /existsP [] q /andP []. rewrite ffunE => /eqP -> /= /andP [] H0 H1.
  exists [::]. exists [::]. rewrite/accept => /=. by rewrite H0 H1.
case_eq (accept A1 (rcons w a)); case_eq (accept A2 [::]); move => H0 H1.
      exists (rcons w a). exists [::]. by rewrite cats0 H0 H1.
    case_eq (accept' Aut_conc [ffun q => q == state1_conc s01] w).
      move/IHw => [] w1 [] w2 [] -> /andP [] H2 H3. rewrite rcons_cat.
      case_eq (accept A2 (rcons w2 a)) => H4.
        exists w1. exists (rcons w2 a). split.
          by [].
        by rewrite H2 H4.
      
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
  move: sink_false => char; by move: (sink_dead_end A w false char) => /negbTE => -> //.
move: sink_false => char; by move: (sink_dead_end A w false char) => /negbTE => -> //.
Qed.



