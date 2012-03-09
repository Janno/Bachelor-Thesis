Require Import ssreflect ssrbool eqtype fintype finfun seq fingraph ssrfun ssrnat finset.

Require Import misc.

Set Implicit Arguments.

(** Finite automata. ***)
Section FA.

(** The finite input alphabet. ***)
Variable char: finType.

(** Type of input sequences ***)
Definition word := misc.word char.

(** Deterministic finite automata.
   This is the only actual type of automata.
   NFAs will be translated on the fly (they
   never exist as instances of some type). ***)
Section DFA.

(** The finite type of states ***)
Variable state: finType.

(** The type of deterministic finite automata. ***)
Record dfa : Type :=
  dfaI {
    dfa_s0: state;
    dfa_fin: pred state;
    dfa_step: state -> char -> state
    }.

(** Acceptance on DFAs **)
Section Acceptance.

(** Assume some automaton **)
Variable A: dfa.

(** We define a run of w on the automaton A
   to be the list of states x_1 .. x_|w|
   traversed when following the edges labeled
   w_1 .. w_|w| starting in x. **)
Fixpoint dfa_run' (x: state) (w: word) : seq state :=
match w with
  | [::] => [::]
  | a::w => (dfa_step A x a) ::dfa_run' (dfa_step A x a) w
end.

(** A simplifying function for a "complete" run
   (i.e. starting at s0). **)
Definition dfa_run := [fun w => dfa_run' (dfa_s0 A) w].

(** Acceptance of w in x is defined as
   finality of the last state of a run of w on A
   starting in x. **)
Definition dfa_accept' := [ fun x w => dfa_fin A (last x (dfa_run' x w) ) ].

(** Acceptance of w on A starting in s0. **)
Definition dfa_accept := [fun w => dfa_accept' (dfa_s0 A) w].

(** A lemma that helps us avoid cumbersome unfolding of accept' **)
Lemma dfa_accept'S x a w : dfa_accept' x (a::w) = dfa_accept' (dfa_step A x a) w.
Proof. elim: w x a => [|b w IHw] x a //=. Qed.
(** Same for run' **)
Lemma dfa_run'S x a w : dfa_run' x (a::w) = (dfa_step A x a) :: dfa_run' (dfa_step A x a) w.
Proof. by []. Qed.
  
(** The size of a run is the size of the input word. **)
Lemma dfa_run_size x w : size (dfa_run' x w) = size w.
Proof. elim: w x => [|a w IHw] x //=.
  by rewrite IHw.
Qed.

(** take lemma. **)
Lemma dfa_run'_take x w n: take n (dfa_run' x w) = dfa_run' x (take n w).
Proof. elim: w x n => [|a w IHw] x n //.
rewrite dfa_run'S 2!take_cons. case: n => [|n] //.
by rewrite IHw dfa_run'S.
Qed.

(** rcons and cat lemmas. **)
Lemma dfa_run'_cat x w1 w2 : dfa_run' x (w1 ++ w2) = dfa_run' x w1 ++ dfa_run' (last x (dfa_run' x w1)) w2.
Proof. elim: w1 w2 x => [|a w1 IHw1] w2 x //.
simpl. by rewrite IHw1.
Qed.

Lemma dfa_run'_rcons x w a : dfa_run' x (rcons w a) = rcons (dfa_run' x w) (dfa_step A (last x (dfa_run' x w)) a).
Proof. move: w a x. apply: last_ind => [|w b IHw] a x //.
rewrite -3!cats1. rewrite 2!dfa_run'_cat. by [].
Qed.

  

(** Predicate to distinguish between accepting
   and non-accepting runs. **)
Definition dfa_run_accepting := [fun x xs => dfa_fin (last x xs)].

Definition dfa_run_accepts x xs w := xs == dfa_run' x w.

End Acceptance.

End DFA.



(** Non-deterministic automata. **)
Section NFA.

(** The finite type of states ***)
Variable state: finType.
  
(** The type of non-deterministic finite automata. ***)
Record nfa : Type :=
  nfaI {
    nfa_s0: state;
    nfa_fin: pred state;
    nfa_step: state -> char -> pred state
    }.

(** Acceptance on non-deterministic automata. **)
Section Acceptance.

Variable A: nfa.

(** Non-deterministic acceptance. **)
Fixpoint nfa_accept' (x: state) w :=
match w with
  | [::] => nfa_fin A x
  | a::w => existsb y, (nfa_step A x a y) && nfa_accept' y w
end.

(** We define labeled paths over the non-deterministic step relation **)
Fixpoint nfa_lpath x (xs : seq state) (w: word) {struct xs} :=
match xs,w with
  | y :: xs', a::w' => nfa_step A x a y && nfa_lpath y xs' w'
  | [::]    , [::]  => true
  | _       , _     => false
end.

(** We proof that there is a path labeled with w induced
   by nfa_accept' starting at x and ending in an accepting
   state. **)
Lemma nfa_accept_lpath x w: nfa_accept' x w -> exists xs, nfa_lpath x xs w /\ nfa_fin A (last x xs).
Proof. elim: w x => [|a w IHw] x.
  by exists [::].
move => /existsP [] y /andP [] H0 /IHw [xs [H1 H2]].
exists (y::xs) => /=.
by rewrite H0 H1 H2.
Qed.

(** We proof that the existence of a path labeled with w
   implies the acceptance of w. **)
Lemma nfa_lpath_accept x xs w: nfa_lpath x xs w /\ nfa_fin A (last x xs) -> nfa_accept' x w.
Proof. elim: w x xs => [|a w IHw] x xs.
  (* We destruct the path to ensure that it is empty. *)
  case: xs => [|y xs].
    move/andP => []. by [].
  (* Non-empty paths can not be not be produced by empty words. *)
  by move/andP.
case: xs => [|y xs].
  (* Empty paths can not accept non-empty words. *)
  by move/andP.
simpl. move => [] /andP [] H0 H1 H2.
apply/existsP. exists y.
rewrite H0 andTb. apply: IHw.
split; eassumption.
Qed.

End Acceptance.

End NFA.

(** We define the powerset construction to obtain
   a deterministic automaton from a non-deterministic one. **) 
Section PowersetConstruction.

Variable state: finType.
Variable A: nfa state.

(** The new automaton's states are sets of the given
   automatons' states. **)
Definition powerset_state : finType := [finType of {set state}].


Definition nfa_to_dfa :=
  dfaI
    powerset_state
    (set1 (nfa_s0 A))
    [ pred X: powerset_state | existsb x: state, (x \in X) && nfa_fin A x]
    [fun X a => cover [set finset (nfa_step A x a) | x <- X] ]
.

(** We prove that nfa_to_dfa builds an automaton which
   accepts exactly the language of the given automaton.
   We first prove that, for every state x, the new automaton
   accepts the same language when starting in a set containing x. **)
Lemma nfa_to_dfa_correct (x: state) w (X: powerset_state): x \in X -> (nfa_accept' A x w <-> dfa_accept' nfa_to_dfa X w).
Proof. move => H0. split.
  (* "->" *)
  elim: w x H0 => [|a w IHw] x H0.
    (* [::] *)
    move => /= H1. apply/existsP. exists x.
    by rewrite H0 H1.
  (* a::w *)
  move/nfa_accept_lpath => [] y [] H1 H2.
  move/existsP => [] y /andP [] H1 H2.
  


End PowersetConstruction.

End FA.

Hint Unfold A_step.
Hint Unfold A_s0.
Hint Unfold A_fin.

(** Operations on up to two automata with the same alphabet **)
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


(** Complement automaton **)
Section Complement.
  
(** The only change needed is to negate the finality predicate. **)
Definition fin_not := [ fun q1 => ~~ fin1 q1 ].
(** We construct the resulting automaton. **)
Definition Aut_not := dfaI char state1 s01 fin_not step1.

(** We proof that the complement automaton accepts exactly
   the words not accepted by the original automaton. **)
Lemma Aut_not_correct w q: accept' A1 q w = ~~ accept' Aut_not q w.
Proof.
  by apply/idP/negPn.
Qed.

End Complement.


(** Cross product of the two state sets **)
Definition state_prod := prod_finType state1 state2.


(** Disjunction automaton **)
Section Disjunction.

Definition step_or (q: state_prod) a := let (q1, q2) := q in (step1 q1 a, step2 q2 a).
Definition Aut_or := dfaI char state_prod (s01, s02) 
(fun q => let (q1,q2) := q in fin1 q1 || fin2 q2)
step_or.

(** Correctness w.r.t. any state. **)
Lemma Aut_or_correct' w q1 q2 : accept' A1 q1 w || accept' A2 q2 w = accept' Aut_or (q1, q2) w.
Proof. elim: w q1 q2 => [|a w IHw].
  rewrite/accept => //.
rewrite/accept => /=. move => q1 q2. 
by exact: IHw.
Qed.

(** Language correctness. **)
Lemma Aut_or_correct w: accept A1 w || accept A2 w = accept Aut_or w.
Proof. exact: Aut_or_correct'. Qed.

End Disjunction.
  

(** Conjunction **) 
Section Conjunction.
  
Definition step_and (q: state_prod) a := let (q1, q2) := q in (step1 q1 a, step2 q2 a).
Definition Aut_and := dfaI char state_prod (s01, s02) 
(fun q => let (q1,q2) := q in fin1 q1 && fin2 q2)
step_or.

(** Correctness w.r.t. any state. **)
Lemma Aut_and_correct' w q1 q2 : accept' A1 q1 w && accept' A2 q2 w = accept' Aut_and (q1, q2) w.
Proof. elim: w q1 q2 => [|a w IHw].
  rewrite/accept => //.
rewrite/accept => /=. move => q1 q2. 
by exact: IHw.
Qed.

(** Language correctness. **)
Lemma Aut_and_correct w: accept A1 w && accept A2 w = accept Aut_and w.
Proof. exact: Aut_and_correct'. Qed.

End Conjunction.


(** Star automaton. **)
Section Star.
  
(** We need to add a new state. **)
Definition state_star' := option_finType state1.
Definition s0_star' : state_star' := None.
(** We only accept the empty state. **)
Definition fin_star' := [ pred x | x == s0_star' ].
(** The type of states in the star automaton. **)
Definition state_star := state_det state_star'.
(** We construct a non-functional relation which is 
   the new transitions of the star automaton.
   Whenever we enter a former final state, we
   also enter the new starting state, thereby
   ensuring acceptance. **)
Definition step_rel_star : state_star' -> char -> pred state_star' :=
  (fun x1 a =>
    match x1 with
      (** any old state **)
      | Some x1 => [ pred x2 |
                       (x2 == Some (step1 x1 a))
                    || (fin1 (step1 x1 a) && (x2 == s0_star'))
                   ]
      (** the new state s0_sta **)
      | s0_star' => [ pred x2 | x2 == Some (step1 s01 a) ]
    end
  ).
(** We construct the star automaton. **)
(** Definition Aut_star := to_dfa char state1 s01 fin_star' step_rel_star. **)
Definition step_star := step_det char step_rel_star.
Definition s0_star := s0_det state_star' s0_star'.
Definition fin_star := fin_det state_star' fin_star'.
Definition Aut_star := dfaI char (state_det state_star') s0_star fin_star step_star.

(** Starting state correctness. **)
Lemma Aut_star_s0 : s0_star s0_star'. by rewrite /s0_star /s0_det ffunE eq_refl. Qed.

(** step_star_rel invariant. **)
Lemma Aut_star_step_rel (X: state_star) a: fin_star (step_star X a) -> (step_star X a) s0_star'.
Proof. simpl. move/existsP => [] x. by rewrite andbC => /andP [] /eqP ->. Qed.
  
(** We proof that the empty word is contained in the
   language of the star automaton. **)
Lemma Aut_star_correct0 : accept Aut_star [::].
Proof. rewrite/accept/accept'/fin_star => /=. apply/existsP. exists s0_star'.
by rewrite /s0_det ffunE eq_refl. Qed.

(** We proof that all non-empty words accepted by the
   original automaton are also accepted by the star
   automaton.
   Translating x to [pred x' | x'==x] gives us an
   induction hypothesis which is too weak to prove
   the statement. Therefore, we allow the star automaton
   to start from any set of states containing x.
   **)
Lemma Aut_star_correctS (X: state_star) a w x :
  X (Some x) -> accept' A1 x (a::w) -> accept' Aut_star X (a::w).
Proof. elim: w a X x => [| b w IHw ] a X x H0.
  move => /= H1. apply/existsP. exists s0_star'. rewrite ffunE eq_refl andbT.
  apply/existsP. exists (Some x). rewrite H0 andTb /step_rel_star /=.
  by rewrite H1 eq_refl.
rewrite accept'S. apply: IHw. rewrite ffunE. apply/existsP. exists (Some x).
by rewrite H0 andTb /step_rel_star /= eq_refl.
Qed.

(** We show that every accepting run of the
   star automaton ends in a state Y s.t. Y s0_star'. **)
Lemma Aut_star_end X w: accept' Aut_star X w -> last X (run' Aut_star X w) s0_star'.
Proof. elim: w X => [|a w IHw] X.
  by move => /= /existsP [] q /andP [] H0 /eqP <-.
rewrite accept'S. by apply: IHw.
Qed.

(** We define the notion of a shortest, non-empty, accepting prefix **)
Definition Aut_star_prefix (X: state_star) (w: word char) (n: nat) : bool :=
      (n > 0) && (n <= size w) && (accept' Aut_star X (take n w)) &&
  forallb n': ordinal n, (n' > 0) ==> ~~ accept' Aut_star X (take n' w).
 
(** We proof that there are no shorter prefixes than the shortest prefix. **)
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
Defined.

(** This, too. **)
Lemma word_expand (w: word char) : 0 < (size w) -> exists a, w = rcons (take (size w).-1 w) a.
Proof. move: w. apply: last_ind => [| w a IHw].
  by [].
move => H0. exists a.
rewrite -cats1 takel_cat.
  rewrite -cats1 size_cat. rewrite addn1. by rewrite take_size.
by rewrite size_cat addn1.
Qed.

(** We proof that Aut_star_prefix is "transitive" regarding
   additional suffixes. **)
Lemma Aut_star_prefix_trans X w k m:
k >= m -> Aut_star_prefix X (take k w) m -> Aut_star_prefix X w m.
Proof. move: w m k. apply: last_ind => [|w b IHw] m k.
  by [].
move => H0.
case_eq (k < size (rcons w b)) => H1.
  rewrite -cats1 takel_cat.
    move/andP => [] /andP [] /andP [] H2 H3 H4 /forallP H5.
    (** we'll need this a few times: **)
    have: m <= size w.
      apply: leq_trans.
        by apply H3.
      exact: size_take_bound.
    move => H6.
    
    rewrite /Aut_star_prefix. rewrite H2.
    have: m <= size (w++ [::b]).
      apply: leq_trans.
          by apply H6.
        rewrite cats1 size_rcons.
        by apply: ltnW.
      move => ->.
    rewrite take_undersize in H4 => //.
    rewrite takel_cat => //.
    rewrite H4.
    rewrite 2!andTb.
    apply/forallP => n'.
    rewrite takel_cat.
      move: (H5 n').
      rewrite take_undersize => //.
      apply: leq_trans.
        apply ltnW.
        by apply (ltn_ord n').
      by [].
    apply: leq_trans.
      apply ltnW.
      by apply (ltn_ord n').
    exact: H6.
  move: H1.
  rewrite size_rcons. by rewrite ltnS.
move: (negbT H1). rewrite -leqNgt => H2.
by rewrite take_oversize.
Qed.

(** We proof that there are no accepted prefixes < n if there is
   no shortest, non-empty, accepting prefix < n **)
Lemma Aut_star_prefix_none X w a n:
  0 < n ->
  (forallb m : 'I_(S n), (0 < m) ==> ~~ Aut_star_prefix X (rcons w a) m) -> ~~ accept' Aut_star X (take n (rcons w a)).
Proof. elim: n X w a => [|n IHn] X w a;
move => H0 /forallP H1.
  by [].
pose m := (@Ordinal n.+2 n.+1 (ltnSn n.+1)).
have: n.+1 = nat_of_ord m. by []. move => H3.
move: (H1 m) => /implyP H4.
have: (0 < m). rewrite -H3. by [].
move: (H4 H0).
rewrite 3!negb_and. move/orP => [].
  move/orP => [].
    move/orP => [].
      rewrite ltnNge. move/negbNE.
      rewrite leq_eqVlt => /orP [].
        rewrite -H3 => /eqP H5. by move : H5 H0 => ->.
      by [].
    rewrite leqNgt. move/negbNE. rewrite -{1}H3 => H5 H6.
    apply/negbT. rewrite take_oversizeS.
      apply/negbTE.
      case_eq n => [|n'].
        move => H7. rewrite H7 in H5. move: H5. rewrite ltnS. rewrite leqn0.
        rewrite size_rcons. by [].
      move => H7. rewrite -H7. apply IHn.
        rewrite H7. by [].
      apply/forallP. move => k. move: (ltn_ord k). move/leqW => H8.
      pose k' := (@Ordinal n.+2 k H8).
      have: nat_of_ord k' = k. by [].
      move => <-. by apply H1.
      exact: H5.
 
   move => H5 H6. rewrite H3. exact H5.
rewrite -negb_exists_in. move/negbNE => /existsP [] k.
move/andP => [] H5 H6 H7.
move: (H4 H7). rewrite 3!negb_and. rewrite H7. rewrite orFb.
  case_eq (m <= size (rcons w a)) => H8.
    rewrite orFb.
  move/orP => [].
    by rewrite -H3. 
  rewrite -negb_exists_in. move/negbNE => /existsP [].
     
Admitted.

(** We proof that there is a shortest, non-empty, accepting prefix
   for every non-empty word accept by the star automaton. **)
Lemma Aut_star_shortest_prefix (X: state_star) (a: char) w:
  accept' Aut_star X (rcons w a) ->
  exists n,
    Aut_star_prefix X (rcons w a) n.
Proof.
(** We use size_induction to get a helpful IH. **)
move: w a X. apply: (size_induction size) => w IHw a X.
case_eq (size w) => [|s] Hs.
  rewrite (size0nil Hs).
  move => H0. 
  exists 1. apply/andP. split.
    rewrite andTb. by exact: H0. 
  apply/forallP => x. apply/implyP. move: (ltn_ord x).
  rewrite leq_eqVlt => /andP [] /eqP H1.
  (** this is a very convoluted way of proving that x=0. **)
  case_eq (nat_of_ord x) => [|x'].
    by [].
  move/(f_equal S). rewrite H1. move/(f_equal predn). by [].

(** We use word_expand to get separate prefix and the 1-suffix **)
have: 0 < size w.
  by rewrite Hs.
move/word_expand => [] b Hw. rewrite Hw.
move Ew: (take (size w).-1 w) => w'.
move => H0.
(** See if there already is a prefix: **)
case_eq (existsb m : 'I_ (size (rcons (rcons w' b) a)), Aut_star_prefix X (rcons w' b) m).
(** prefix. **)
  move/existsP => [] m /andP [] /andP [] /andP [] H1 H2 H3 /forallP H4.
  pose n:=nat_of_ord m.
  exists n. apply/andP. split.
    apply/andP. split.
      apply/andP. split => //.
      rewrite size_rcons.
        move: H2. by exact: leqW.
      rewrite -{}cats1. rewrite {1}(takel_cat H2). 
      by exact: H3.
  apply/forallP => k. apply/implyP => H5.
  rewrite -cats1 takel_cat. move: H5. apply/implyP. by exact: H4.
  apply: leq_trans. apply ltnW. apply ltn_ord. by [].

(** no prefix. **)

move/negbT. rewrite negb_exists => /forallP H1. exists (size (rcons (rcons w' b) a)).
apply/andP. split.
  apply/andP. split.
    by rewrite size_rcons ltn0Sn ltnSn.
  rewrite take_size. by exact: H0.
apply/forallP => n'. apply/implyP => H2.
move: (H1 n').
(** We'll need this a few times. **)
have: (n' <= size (rcons w' b)).
    rewrite -{1}ltnS -(size_rcons (rcons w' b ) a).
    exact: (ltn_ord n').
move => H3.

rewrite negb_and H2 => /orP [].
  rewrite negb_and => /orP [].
    rewrite negb_and => /orP [].
      by [].
    by rewrite H3. 
  rewrite -(takel_cat H3 [::a]).
  by rewrite cats1.

rewrite negb_forall.
rewrite negb_forall_in.
move/existsP => [] m.
(** take m w' would be the shortest, non-empty, accepting prefix
   but there is no such prefix. **)
move/andP => [] H4 /negbNE H5.
Admitted.


Lemma Aut_star_prefix_det w a n:
  Aut_star_prefix s0_star (rcons w a) n ->  accept A1 (take n (rcons w a)).
Proof. move: w a n. apply: last_ind => [|w b IHw] a n.
  move => /andP [] /andP [] /andP [] H0 H1 H2 /forallP H3.
  rewrite take_oversize /accept' in H2 => //.
  rewrite /A_fin /fin_star /s0_star in H2.
  move: H2 => /existsP [] y /andP [].
  rewrite /run' ffunE => /existsP [] z.
  rewrite ffunE => /andP [] /eqP ->.
  rewrite /step_rel_star /fin_star' => /= /eqP ->. by [].

move => /andP [] /andP [] /andP [] H0 H1 H2 /forallP H3.

case_eq (n < size (rcons (rcons w b) a)).
  rewrite size_rcons => H4.
  have: n <= size (rcons w b). by []. move => H5.
  move: H2. rewrite -cats1. rewrite takel_cat => //.
  move => H2. apply: IHw.
  rewrite /Aut_star_prefix H0 H5 H2 2!andTb.
  apply/forallP. move => m.
  move: (H3 m). rewrite -cats1 takel_cat.
    by [].
  apply: leq_trans.
    eapply ltnW.
    by eapply ltn_ord.
  by [].

Admitted.
  
End Star.

(** Concatenation **)
Section Concatenation.
  
Definition state_sum := sum_finType state1 state2.
Definition state_sum_option := option_finType state_sum.

Definition state1_conc (x1: state1) : state_sum. constructor. exact x1. Defined.
Definition state2_conc (x2: state2) : state_sum. apply/inr. exact x2. Defined.
Definition state_conc := state_det state_sum.
Definition s0_conc : state_sum. constructor. exact: s01. Defined.

Definition step_conc (x: state_sum) a (x': state_sum) := 
match x with
| inl x1 => 
  match x' with
  | inl x1' => step1 x1 a == x1'
  | inr x2' => fin1 x1 && (step2 s02 a == x2')
  end
| inr x2 =>
  match x' with
  | inr x2' => step2 x2 a == x2'
  | _ => false
  end
end.

Definition fin_conc := [fun x : state_sum =>
match x with
| inl x1 => fin1 x1 && fin2 s02
| inr x2 => fin2 x2
end ].
Definition Aut_conc := to_dfa char state_sum (s0_conc) fin_conc step_conc. 

(** We define a relation (an order) on states. **)
Definition state_conc_leq (q1' q2': state_conc) := forall q, q1' q -> q2' q.

Notation "q1' ===> q2'" := (state_conc_leq q1' q2') (at level 70).

(** We proof a few interesting properties of this relation. **)
Lemma q_conc_leq_trans (q1' q2' q3': state_conc) : q1' ===> q2' -> q2' ===> q3' -> q1' ===> q3'.
Proof. rewrite/state_conc_leq. move => H0 H1 q. by move/H0/H1. Qed.

Lemma q_conc_leq_d_trans (q1' q2' : state_conc) a : 
q1' ===> q2' -> step_det char step_conc q1' a ===> step_det char step_conc q2' a.
Proof. move => H0 q. rewrite/step_det. rewrite 2!ffunE. 
move/existsP => [] p /andP [] /H0 H1 H2. apply/existsP. exists p. 
by rewrite H1 H2. Qed.

Lemma Aut_conc_expand1 (q1' q2': state_conc) w:
q1' ===> q2' ->
accept' Aut_conc q1' w ->
accept' Aut_conc q2' w.
Proof. elim: w q1' q2' => [|a w IHw]. 
  rewrite/accept'/fin_det => /= q1' q2' H. move/existsP => [] q /andP []. 
  move => H0 H1. apply/existsP. move: (H q H0). exists (q). by rewrite H2 H1.
move => q1' q2'. move/(@q_conc_leq_d_trans _ _ a). simpl. 
by apply: IHw.
Qed.

(** We proof that the concatenation automaton accepts
   all words of the first automaton if the second automaton
   accepts the empty word. **)
Lemma Aut_conc_correct1' q1 w1: 
accept' A1 q1 w1 && accept A2 [::] 
-> accept' Aut_conc (finfun (fun q=> q == state1_conc q1)) w1.
Proof.
elim: w1 q1 => [|a w1 IHw1] q1.
  rewrite /fin_det /fin_conc /accept /accept' /=.
  move/andP => [] H0 H1. apply/existsP. exists (state1_conc q1). 
  rewrite ffunE. apply/andP. split.
    by apply/eqP.
  by rewrite H0 H1.
move/andP => [].
move => H0 H1. move: (IHw1 (step1 q1 a)).
rewrite accept'S in H0.
rewrite /accept. rewrite H0 H1. move => H2. move: (H2 is_true_true).
rewrite accept'S.
apply Aut_conc_expand1. 
move => q. rewrite 2!ffunE. move/eqP => ->. apply/existsP. 
exists (state1_conc q1). rewrite ffunE. apply/andP. split.
  by apply/eq_refl.
rewrite/step_conc => /=. by apply/eq_refl.
Qed.


(** We proof that the concatenation automaton accepts
   all words accepted by the second automaton when if
   they both start in the same state. **)
Lemma Aut_conc_correct2' x2 w2: 
accept' A2 x2 w2
-> accept' Aut_conc (finfun (fun x=> x == state2_conc x2)) w2.
Proof. elim: w2 x2 => [|a w2 IHw2] x2 /=.
  move => H0. rewrite/fin_det/fin_conc. apply/existsP. exists (state2_conc x2). apply/andP. split.
    by rewrite ffunE.
  by exact: H0.
move/IHw2. apply: Aut_conc_expand1 => x. rewrite 2!ffunE. move/eqP => ->.
apply/existsP. exists (state2_conc x2). apply/andP. split.
  by rewrite ffunE. 
by rewrite/step_conc => /=.
Qed.

(** We proof that final states of the first automaton have at
   least all transitions of s02 in the concatenation automaton. **)
Lemma Aut_conc_end1 x1 a:
fin1 x1 ->
step_det char step_conc [ffun x => x == state2_conc s02] a ===> step_det char step_conc [ffun x => x == state1_conc x1] a.
Proof.
rewrite /step_det /step_conc => /=. move => H0 [x|x];
rewrite ffunE => /existsP [] x'; rewrite ffunE => /andP [] /eqP -> /=.
  by [].
rewrite eq_sym ffunE => /eqP ->. apply/existsP. exists (state1_conc x1).
rewrite ffunE eq_refl andTb. by rewrite H0 eq_refl.
Qed.

(** We proof that all words accepted by s02 are also accepted
   by final states of the first automaton in the concatenation
   automaton. **)
Lemma Aut_conc_correct3' x1 w2:
fin1 x1 ->
accept' Aut_conc [ffun x => x == state2_conc s02] w2 ->
accept' Aut_conc [ffun x => x == state1_conc x1] w2.
Proof. elim: w2 x1 => [|a w2 IHw2] x1 H0 /=.
  rewrite/fin_det/fin_conc. move/existsP => [] x /andP []. rewrite ffunE => /eqP -> /= H1.
  apply/existsP. exists (state1_conc x1). by rewrite ffunE eq_refl andTb H0 H1.
apply: Aut_conc_expand1. apply: Aut_conc_end1. exact: H0.
Qed.

(** We proof that the concatenation automaton accepts
   all words that are made up of a prefix accepted by the first automaton
   and a suffix accepted by the second automaton. **)
Lemma Aut_conc_correct1 x1 w1 w2: (accept' A1 x1 w1 && accept A2 w2) ->
  accept' Aut_conc [ffun x => x == state1_conc x1] (w1 ++ w2).
Proof. elim: w1 w2 x1 => [|a w1 IHw1] w2 x1.
  rewrite/accept => /andP [] /= H0. rewrite/s0_conc. move/(Aut_conc_correct2').
  rewrite/state2_conc. apply: Aut_conc_correct3'. exact: H0.
simpl. move/IHw1. apply: Aut_conc_expand1 => x.
rewrite /step_det /step_conc ffunE => /eqP -> /=. rewrite ffunE. apply/existsP.
exists (state1_conc x1). by rewrite ffunE eq_refl andTb eq_refl.
Qed.

(** We proof that the concatenation automaton only accepts
   words that can be expressed as a prefix accepted by the first automaton
   and a suffix accepted by the second automaton. **)
Lemma Aut_conc_correct2 w: 
accept' Aut_conc [ffun x => x == state1_conc s01] w -> 
exists w1, exists w2, w = w1 ++ w2 /\ accept A1 w1 && accept A2 w2.
Proof. move: w.
apply: last_ind => [| w a IHw ].
  rewrite /fin_det /fin_conc => /existsP [] x /andP []. rewrite ffunE => /eqP -> /= /andP [] H0 H1.
  exists [::]. exists [::]. rewrite/accept => /=. by rewrite H0 H1.
case_eq (accept A1 (rcons w a)); case_eq (accept A2 [::]); move => H0 H1.
      exists (rcons w a). exists [::]. by rewrite cats0 H0 H1.
    case_eq (accept' Aut_conc [ffun x => x == state1_conc s01] w).
      move/IHw => [] w1 [] w2 [] -> /andP [] H2 H3. rewrite rcons_cat.
      case_eq (accept A2 (rcons w2 a)) => H4.
        exists w1. exists (rcons w2 a). split.
          by [].
        by rewrite H2 H4.
Admitted.  


End Concatenation.

End Operators.


