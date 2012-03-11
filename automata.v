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
Fixpoint dfa_accept x w :=
match w with
  | [::] => dfa_fin A x
  | a::w => dfa_accept (dfa_step A x a) w
end.

(** We define the language of the deterministic
   automaton, i.e. acceptance in the starting state. **)
Definition dfa_lang := [fun w => dfa_accept (dfa_s0 A) w].

(** A lemma that helps us avoid cumbersome unfolding of accept **)
Lemma dfa_acceptS x a w : dfa_accept x (a::w) = dfa_accept (dfa_step A x a) w.
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
Fixpoint nfa_accept (x: state) w :=
match w with
  | [::] => nfa_fin A x
  | a::w => existsb y, (nfa_step A x a y) && nfa_accept y w
end.

(** We define the language of the non-deterministic
   automaton, i.e. acceptance in the starting state. **)
Definition nfa_lang := [fun w => nfa_accept (nfa_s0 A) w].

(** We define labeled paths over the non-deterministic step relation **)
Fixpoint nfa_lpath x (xs : seq state) (w: word) {struct xs} :=
match xs,w with
  | y :: xs', a::w' => nfa_step A x a y && nfa_lpath y xs' w'
  | [::]    , [::]  => true
  | _       , _     => false
end.

(** We proof that there is a path labeled with w induced
   by nfa_accept starting at x and ending in an accepting
   state. **)
Lemma nfa_accept_lpath x w: nfa_accept x w -> exists xs, nfa_lpath x xs w /\ nfa_fin A (last x xs).
Proof. elim: w x => [|a w IHw] x.
  by exists [::].
move => /existsP [] y /andP [] H0 /IHw [xs [H1 H2]].
exists (y::xs) => /=.
by rewrite H0 H1 H2.
Qed.

(** We proof that the existence of a path labeled with w
   implies the acceptance of w. **)
Lemma nfa_lpath_accept x xs w: nfa_lpath x xs w -> nfa_fin A (last x xs) -> nfa_accept x w.
Proof. elim: w x xs => [|a w IHw] x xs.
  (* We destruct the path to ensure that it is empty. *)
  case: xs => [|y xs].
    by [].
  (* Non-empty paths can not be not be produced by empty words. *)
  by [].
case: xs => [|y xs].
  (* Empty paths can not accept non-empty words. *)
  by [].
simpl. move => [] /andP [] H0 H1 H2.
apply/existsP. exists y.
rewrite H0 andTb.
apply: IHw; by eassumption.
Qed.

(** Helpful facts **)
Lemma nfa_accept_cat x w1 w2:
  nfa_accept x (w1 ++ w2) <->
  exists xs,
    nfa_lpath x xs w1
    && nfa_accept (last x xs) w2.
Proof. split.
  elim: w1 w2 x => [|a w1 IHw1] w2 x.
    simpl. exists [::]. simpl. exact: H.
  move/existsP => [] y /andP [] H0 /IHw1 [] ys /andP [] H1 H2.
  exists (y::ys) => /=. by rewrite H0 H1 H2.
elim: w1 w2 x => [|a w1 IHw1] w2 x; move => [] [|y ys] /andP [] H0 H1 //.
move: H0 => /= /andP [] H2 H3. 
apply/existsP. exists y. rewrite H2 => /=.
apply: IHw1.
exists ys. by rewrite H3 H1.
Qed.

End Acceptance.

End NFA.

(** We define the powerset construction to obtain
   a deterministic automaton from a non-deterministic one. **) 
Section PowersetConstruction.

Variable state: finType.
Variable A: nfa state.

(** The new automaton's states are sets of the given
   automaton' states. **)
Definition powerset_state : finType := [finType of {set state}].

(** The new starting state is the singleton set containing
   the given automaton's starting state. **)
Definition powerset_s0 : powerset_state := set1 (nfa_s0 A).

Definition nfa_to_dfa :=
  dfaI
    powerset_state
    powerset_s0 
    [ pred X: powerset_state | existsb x: state, (x \in X) && nfa_fin A x]
    [fun X a => cover [set finset (nfa_step A x a) | x <- X] ]
.

(** We prove that for every state x, the new automaton
   accepts at least the language of the given automaton
   when starting in a set containing x. **)
Lemma nfa_to_dfa_correct1 (x: state) w (X: powerset_state):
  x \in X -> nfa_accept A x w -> dfa_accept nfa_to_dfa X w.
Proof. move => H0.
  (* "->" *)
  elim: w X x H0 => [|a w IHw] X x H0.
    (* [::] *)
    move => /= H1. apply/existsP. exists x.
    by rewrite H0 H1.
  (* a::w *)
  move/nfa_accept_lpath => [] xs [].
  (* We destruct xs to eliminate the nil case. *)
  case: xs => [|y xs] H1 H2.
    by [].
  (* move => /andP [] H1 H2 H3. *)
  apply: (IHw _ y).
    simpl. rewrite cover_imset.
    apply/bigcupP. exists x.
      exact: H0.
    move: H1 => /andP [] H3 _.
    rewrite in_set. exact: H3.
  move: H1 => /andP [] _. move/nfa_lpath_accept => H3.
  exact: (H3 H2).
Qed.

(** Next we prove that in any set of states X, for every word w,
   if the powerset automaton accepts w in X, there exists one
   representative state of that set in which the given automaton
   accepts w. **)
Lemma nfa_to_dfa_correct2 (X: powerset_state) w:
  dfa_accept nfa_to_dfa X w -> existsb x, (x \in X) && nfa_accept A x w.
Proof. elim: w X => [|a w IHw] X.
  by [].
move/IHw => /existsP [] y /andP [].
rewrite /dfa_step /nfa_to_dfa => /=. rewrite cover_imset.
move/bigcupP => [] x H0 H1 H2.
apply/existsP. exists x. rewrite H0 andTb.
apply/existsP. exists y. move: H1. rewrite in_set => ->.
exact: H2.
Qed.

(** Finally, we prove that the language of the powerset
   automaton is exactly the language of the given
   automaton. **)
Lemma nfa_to_dfa_correct w : nfa_lang A w = dfa_lang nfa_to_dfa w.
Proof. apply/idP/idP => /=.
  apply: nfa_to_dfa_correct1. by apply/set1P.
by move/nfa_to_dfa_correct2 => /existsP [] x /andP [] /set1P ->.
Qed.
  

End PowersetConstruction.


(** Embedding deterministic automata in non-deterministic automata. **)
Section Embed.

Variable state: finType.

Variable A: dfa state.

Definition dfa_to_nfa : nfa state :=
  nfaI
    state
    (dfa_s0 A)
    (dfa_fin A)
    [fun x a => fun y => y == dfa_step A x a ]
.

(** We proof that dfa_to_nfa accepts the same language as
   the given automaton in any state. **)
Lemma dfa_to_nfa_correct' x w : dfa_accept A x w = nfa_accept dfa_to_nfa x w.
Proof. elim: w x => [|b w IHw] x.
  by [].
simpl. rewrite IHw.
apply/idP/existsP.
  move => H0. exists (dfa_step A x b). by rewrite eq_refl H0.
by move => [] y /andP [] /eqP ->.
Qed.

(** We proof that dfa_to_nfa accepts the same language
   as the given automaton in the starting state, i.e. their
   languages are equal. **)
Lemma dfa_to_nfa_correct w : dfa_lang A w = nfa_lang dfa_to_nfa w.
  exact: dfa_to_nfa_correct'.
Qed.
    
End Embed.



(** Operations on non-deterministic automata. **)
Section DFAOps.

Variable state1: finType.
Variable A1: dfa state1.


(** Complement automaton **)
  
(** The only change needed is to negate the finality predicate. **)
Definition fin_compl := [ fun x1 => ~~ dfa_fin A1 x1 ].
(** We construct the resulting automaton. **)
Definition dfa_compl :=
  dfaI
    state1
    (dfa_s0 A1)
    fin_compl
    (dfa_step A1).

(** We proof that the complement automaton accepts exactly
   the words not accepted by the original automaton. **)
Lemma dfa_compl_correct' w x: dfa_accept A1 x w = ~~ dfa_accept dfa_compl x w.
Proof. elim: w x => [|a w IHw] x.  
  by apply/idP/negPn.
simpl. by rewrite IHw.
Qed.

Lemma dfa_compl_correct w: dfa_lang A1 w = ~~ dfa_lang dfa_compl w.
Proof. exact: dfa_compl_correct'. Qed.

  
(** Operations on two automata. **)
Section BinaryOps.
  
Variable state2: finType.
Variable A2: dfa state2.

(** Cross product of the two state sets **)
Definition state_prod := prod_finType state1 state2.

(** Disjunction automaton **)

Definition step_disj (x: state_prod) a := let (x1, x2) := x in (dfa_step A1 x1 a, dfa_step A2 x2 a).
Definition dfa_disj :=
  dfaI
    state_prod
    (dfa_s0 A1, dfa_s0 A2) 
    (fun q => let (x1,x2) := q in dfa_fin A1 x1 || dfa_fin A2 x2)
    step_disj.

(** Correctness w.r.t. any state. **)
Lemma dfa_disj_correct' w x1 x2 : dfa_accept A1 x1 w || dfa_accept A2 x2 w = dfa_accept dfa_disj (x1, x2) w.
Proof. elim: w x1 x2 => [|a w IHw].
  by [].
move => x1 x2. by exact: IHw.
Qed.

(** Language correctness. **)
Lemma dfa_disj_correct w: dfa_lang A1 w || dfa_lang A2 w = dfa_lang dfa_disj w.
Proof. exact: dfa_disj_correct'. Qed.

(** Conjunction **) 
  
Definition step_conj (x: state_prod) a := let (x1, x2) := x in (dfa_step A1 x1 a, dfa_step A2 x2 a).
Definition dfa_conj :=
  dfaI
    state_prod
    (dfa_s0 A1, dfa_s0 A2) 
    (fun q => let (x1,x2) := q in dfa_fin A1 x1 && dfa_fin A2 x2)
    step_disj
.

(** Correctness w.r.t. any state. **)
Lemma dfa_conj_correct' w x1 x2 : dfa_accept A1 x1 w && dfa_accept A2 x2 w = dfa_accept dfa_conj (x1, x2) w.
Proof. elim: w x1 x2 => [|a w IHw].
  by [].
move => x1 x2.
exact: IHw.
Qed.

(** Language correctness. **)
Lemma dfa_conj_correct w: dfa_lang A1 w && dfa_lang A2 w = dfa_lang dfa_conj w.
Proof. exact: dfa_conj_correct'. Qed.

End BinaryOps.

End DFAOps.

(** Operations on non-deterministic automata. **)
Section NFAOps.
Variable state1 state2: finType.
Variable A1: nfa state1.
Variable A2: nfa state2.

(** Concatenation of two non-deterministic automata. **)

Definition state_conc : finType := sum_finType state1 state2.

Definition step_conc x a y :=
match x,y with
  | inl x, inl y => nfa_step A1 x a y
  | inl x, inr y => nfa_fin A1 x && nfa_step A2 (nfa_s0 A2) a y
  | inr x, inr y => nfa_step A2 x a y
  | inr x, inl y => false
end.

Definition fin_conc (x: state_conc) : bool :=
match x with
  | inl x => nfa_fin A1 x && nfa_fin A2 (nfa_s0 A2)
  | inr x => nfa_fin A2 x
end.

Definition s0_conc : state_conc := inl _ (nfa_s0 A1).

Definition nfa_conc : nfa state_conc :=
  nfaI
    state_conc
    s0_conc
    fin_conc
    step_conc.

Lemma nfa_conc_cont x xs w:
  nfa_lpath A2 x xs w
  -> nfa_lpath nfa_conc (inr _ x) (map (@inr state1 state2) xs) w.
Proof. elim: xs x w => [|y xs IHxs] x w; case: w => [|a w] => //.
simpl. by move/andP => [] -> /IHxs ->.
Qed.

Lemma nfa_conc_fin1 x1 w:
  nfa_fin A1 x1 ->
  nfa_lang A2 w ->
  nfa_accept nfa_conc (inl _ x1) w.
Proof.
move => H0 /nfa_accept_lpath [] ys.
elim: ys w x1 H0 => [|y ys IHys] [|a w] x1 H0 /andP //=.
  by move: H0 => -> ->.
move/andP => [] /andP [] H1 H2 H3.
apply/existsP. exists (inr _ y).
rewrite H0 H1 => /=.
apply: nfa_lpath_accept.
  apply nfa_conc_cont.
  by eassumption.
by rewrite last_map /nfa_fin.
Qed.
    

Lemma nfa_conc_correct1 x w1 w2:
  nfa_accept A1 x w1 ->
  nfa_lang A2 w2 ->
  nfa_accept nfa_conc (inl _ x) (w1 ++ w2).
Proof. elim: w1 w2 x => [|a w1 IHw1] w2 x.
  move => H0 /nfa_accept_lpath [] xs [] H1 H2.
  move: (nfa_conc_cont _ _ _ H1) => H3.
  apply/nfa_accept_cat.
  exists [::] => /=.
  apply: nfa_conc_fin1.
    exact: H0.
  apply: nfa_lpath_accept.
    by eassumption.
  exact: H2.
move => /existsP [] y /andP [] H1 H2 H3 /=.
apply/existsP. exists (inl _ y).
rewrite H1 => /=.
apply: IHw1.
  exact: H2.
exact: H3.
Qed.
  
Lemma nfa_conc_correct2 X w :
  nfa_accept nfa_conc X w ->
  match X with
  | inl x => exists w1, exists w2, (w == w1 ++ w2) && (nfa_accept A1 x w1) && nfa_lang A2 w2
  | inr x => nfa_accept A2 x w
end.
Proof.
elim: w X => [|a w IHw] [x|x] //=.
    move => /andP [] H0 H1. exists [::]. exists [::].
    simpl. by rewrite H0 H1.
  move/existsP => [] [y|y] /andP [] H0 /IHw.
      (* inl / inl *)
      move => [] w1 [] w2 /andP [] /andP [] /eqP H1 H2 /= H3.
      exists (a::w1). exists w2.
      rewrite H1 eq_refl H3 andTb andbT.
      apply/existsP. exists y.
      move: H0 => /= ->. rewrite andTb.
      exact H2.
    (* inl / inr *)
    move: H0 => /= /andP [] H0 H1 /= H2.
    exists [::]. exists (a::w) => /=.
    rewrite H0 eq_refl 2!andTb.
    apply/existsP. exists y.
    by rewrite H1 H2.
  (* inr / inl  *)
  move/existsP => [] [y|y] /andP [] H0 /IHw.
  by [].
(* inr / inr *)
move: H0 => /= H0 H1.
apply/existsP. exists y.
by rewrite H0 H1.
Qed.
  

End NFAOps.

End FA.


