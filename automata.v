Require Import ssreflect ssrbool eqtype fintype choice finfun seq fingraph ssrfun ssrnat finset.

Require Import misc.

Set Implicit Arguments.

(** Finite automata. ***)
Section FA.

Variable char: finType.

(** Type of input sequences ***)
Definition word := misc.word char.

(** Deterministic finite automata. **)
Section DFA.

(** The type of deterministic finite automata. ***)
Record dfa : Type :=
  dfaI {
    dfa_state :> finType;
    dfa_s0: dfa_state;
    dfa_fin: pred dfa_state;
    dfa_step: dfa_state -> char -> dfa_state
    }.

(** Acceptance on DFAs **)
Section Acceptance.

(** Assume some automaton **)
Variable A: dfa.

(** We define a run of w on the automaton A
   to be the list of states x_1 .. x_|w|
   traversed when following the edges labeled
   w_1 .. w_|w| starting in x. **)
Fixpoint dfa_run' (x: A) (w: word) : seq A :=
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
Definition dfa_lang := [pred w | dfa_accept (dfa_s0 A) w].

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

Lemma dfa_run'_drop x w n: drop n (dfa_run' x w) = dfa_run' (last x (dfa_run' x (take n w))) (drop n w).
Proof. elim: w x n => [|a w IHw] x n //.
rewrite dfa_run'S 2!drop_cons. case: n => [|n] //.
by rewrite IHw /=.
Qed.

Lemma dfa_run'_drop' x w n: last x (dfa_run' x (take n w)) = x -> dfa_run' x (drop n w) = drop n (dfa_run' x w).
Proof. move => {1}<-. by rewrite dfa_run'_drop. Qed.

(** rcons and cat lemmas. **)
Lemma dfa_run'_cat x w1 w2 :
  dfa_run' x (w1 ++ w2) = dfa_run' x w1 ++ dfa_run' (last x (dfa_run' x w1)) w2.
Proof. elim: w1 w2 x => [|a w1 IHw1] w2 x //.
simpl. by rewrite IHw1.
Qed.

Lemma dfa_run'_cat' x x1 x2 w:
  dfa_run' x w = x1 ++ x2 -> exists w1, exists w2, w = w1 ++ w2 /\ dfa_run' x w1 = x1 /\ dfa_run' (last x x1) w2 = x2.
Proof.
  elim: x1 x x2 w => [|y x1 IHx1] x x2 w.
    exists ([::]). by exists w.
  case: w => [|a w] => //.
  move => [] H0.
  move/IHx1 => [] w1 [] w2 [] H1 [] H2 H3.
  exists (a::w1). exists (w2).   
  rewrite H1 -H0 H3 -H2 /=.
  by auto.
Qed.
  
Lemma dfa_run'_rcons x w a :
  dfa_run' x (rcons w a) = rcons (dfa_run' x w) (dfa_step A (last x (dfa_run' x w)) a).
Proof. move: w a x. apply: last_ind => [|w b IHw] a x //.
rewrite -3!cats1. rewrite 2!dfa_run'_cat. by [].
Qed.


(* slightly altered acceptance statement. *)
Lemma dfa_run_accepts x w: last x (dfa_run' x w) \in dfa_fin A = dfa_accept x w.
Proof. elim: w x => [|a w IHw] x //. by rewrite /= IHw. Qed.

End Acceptance.

End DFA.



(** Non-deterministic automata. **)
Section NFA.

(** The type of non-deterministic finite automata. ***)
Record nfa : Type :=
  nfaI {
    nfa_state :> finType;
    nfa_s0: nfa_state;
    nfa_fin: pred nfa_state;
    nfa_step: nfa_state -> char -> pred nfa_state
    }.

(** Acceptance on non-deterministic automata. **)
Section Acceptance.

Variable A: nfa.

(** Non-deterministic acceptance. **)
Fixpoint nfa_accept (x: A) w :=
match w with
  | [::] => nfa_fin A x
  | a::w => existsb y, (nfa_step A x a y) && nfa_accept y w
end.

(** We define the language of the non-deterministic
   automaton, i.e. acceptance in the starting state. **)
Definition nfa_lang := [fun w => nfa_accept (nfa_s0 A) w].

(** We define labeled paths over the non-deterministic step relation **)
Fixpoint nfa_lpath x (xs : seq A) (w: word) {struct xs} :=
match xs,w with
  | y :: xs', a::w' => nfa_step A x a y && nfa_lpath y xs' w'
  | [::]    , [::]  => true
  | _       , _     => false
end.

(** We prove that there is a path labeled with w induced
   by nfa_accept starting at x and ending in an accepting
   state. **)
Lemma nfa_accept_lpath x w:
  nfa_accept x w -> exists xs, nfa_lpath x xs w /\ nfa_fin A (last x xs).
Proof. elim: w x => [|a w IHw] x.
  by exists [::].
move => /existsP [] y /andP [] H0 /IHw [xs [H1 H2]].
exists (y::xs) => /=.
by rewrite H0 H1 H2.
Qed.

(** We prove that the existence of a path labeled with w
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
apply/existsP. exists y. rewrite H2 /=.
apply: IHw1.
exists ys. by rewrite H3 H1.
Qed.

End Acceptance.

End NFA.

(** We define the powerset construction to obtain
   a deterministic automaton from a non-deterministic one. **) 
Section PowersetConstruction.

Variable A: nfa.

(** The new automaton's states are sets of the given
   automaton' states. **)
Definition powerset_state : finType := [finType of {set A}].

(** The new starting state is the singleton set containing
   the given automaton's starting state. **)
Definition powerset_s0 : powerset_state := set1 (nfa_s0 A).

Definition nfa_to_dfa :=
  dfaI
    powerset_state
    powerset_s0 
    [ pred X: powerset_state | existsb x: A, (x \in X) && nfa_fin A x]
    [fun X a => cover [set finset (nfa_step A x a) | x <- X] ]
.

(** We prove that for every state x, the new automaton
   accepts at least the language of the given automaton
   when starting in a set containing x. **)
Lemma nfa_to_dfa_correct1 (x: A) w (X: nfa_to_dfa):
  x \in X -> nfa_accept A x w -> dfa_accept nfa_to_dfa X w.
Proof. move => H0.
  elim: w X x H0 => [|a w IHw] X x H0.
    (* [::] *)
    move => /= H1. apply/existsP. exists x.
    by rewrite H0 H1.
  (* a::w *)
  move => /= /existsP [] y /andP [] H1.
  apply (IHw).
  rewrite cover_imset.
  apply/bigcupP.
  exists x => //.
  by rewrite in_set.
Qed.

(** Next we prove that in any set of states X, for every word w,
   if the powerset automaton accepts w in X, there exists one
   representative state of that set in which the given automaton
   accepts w. **)
Lemma nfa_to_dfa_correct2 (X: nfa_to_dfa) w:
  dfa_accept nfa_to_dfa X w -> existsb x, (x \in X) && nfa_accept A x w.
Proof. elim: w X => [|a w IHw] X.
    by [].
  move/IHw => /existsP [] y /andP [].
  rewrite /dfa_step /nfa_to_dfa /=. rewrite cover_imset.
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

Variable A: dfa.

Definition dfa_to_nfa : nfa :=
  nfaI
    A
    (dfa_s0 A)
    (dfa_fin A)
    [fun x a => fun y => y == dfa_step A x a ].

(** We prove that dfa_to_nfa accepts the same language as
   the given automaton in any state. **)
Lemma dfa_to_nfa_correct' x w : dfa_accept A x w = nfa_accept dfa_to_nfa x w.
Proof. elim: w x => [|b w IHw] x.
  by [].
simpl. rewrite IHw.
apply/idP/existsP.
  move => H0. exists (dfa_step A x b). by rewrite eq_refl H0.
by move => [] y /andP [] /eqP ->.
Qed.

(** We prove that dfa_to_nfa accepts the same language
   as the given automaton in the starting state, i.e. their
   languages are equal. **)
Lemma dfa_to_nfa_correct w : dfa_lang A w = nfa_lang dfa_to_nfa w.
  exact: dfa_to_nfa_correct'.
Qed.
    
End Embed.

(** Primitive automata **)
Section Primitive.
  Definition dfa_void :=
    dfaI
      bool_finType
      false
      pred0
      [fun x a => false].
  
  Lemma dfa_void_correct x w: ~~ dfa_accept dfa_void x w.
  Proof. by elim: w x => [|a w IHw] //= x. Qed.

  Definition dfa_empty :=
    dfaI
      bool_finType
      true
      (pred1 true)
      [fun x a => false].

  Lemma dfa_empty_correct w: dfa_lang dfa_empty w = (w == [::]).
  Proof.
    have H: (forall w, ~~ dfa_accept dfa_empty false w).
      by elim => [|a v IHv] //=.
    elim: w => [|a w IHw] //.
    apply/idP/idP.
    exact: H. 
  Qed.
      
  Definition dfa_char a :=
    dfaI
      (option_finType (bool_finType))
      None
      (pred1 (Some true))
      [fun x b => if x == None then if b == a then Some true else Some false else Some false ].
            
  Lemma dfa_char_correct'' a w: ~~ dfa_accept (dfa_char a) (Some false) w.
  Proof. by elim: w => [|b v IHv] //=. Qed.
  Lemma dfa_char_correct' a w: dfa_accept (dfa_char a) (Some true) w = (w == [::]).
  Proof.
    elim: w a => [|b w IHw] a //=.
    apply/idP/idP.
    exact: dfa_char_correct''.
  Qed.
  Lemma dfa_char_correct a w: dfa_lang (dfa_char a) w = (w == [::a]).
  Proof.
    elim: w a => [|b w IHw] a //=.
    case H: (b == a).
      move/eqP: H => ->.
      rewrite dfa_char_correct'.
      by apply/eqP/eqP => [-> | []].
    apply/idP/eqP.
      move => H0. move: (dfa_char_correct'' a w). by rewrite H0.
    move => [] /eqP. by rewrite H.
  Qed.

  Definition dfa_dot :=
    dfaI
      (option_finType (bool_finType))
      None
      (pred1 (Some true))
      [fun x b => if x == None then Some true else Some false ].
            
  Lemma dfa_dot_correct'' w: ~~ dfa_accept dfa_dot (Some false) w.
  Proof. by elim: w => [|b v IHv] //=. Qed.
  Lemma dfa_dot_correct' w: dfa_accept dfa_dot (Some true) w = (w == [::]).
  Proof.
    elim: w => [|b w IHw] //=.
    apply/idP/idP.
    exact: dfa_dot_correct''.
  Qed.
  Lemma dfa_dot_correct w: dfa_lang dfa_dot w = (size w == 1).
  Proof.
    elim: w => [|b w IHw] //=.
    rewrite dfa_dot_correct'.
    apply/eqP/eqP => [-> | []] //=.
    exact: size0nil.
  Qed.

  
End Primitive.

(** Operations on non-deterministic automata. **)
Section DFAOps.

Variable A1: dfa.


(** Complement automaton **)
  
(** The only change needed is to negate the finality predicate. **)
Definition fin_compl := [ fun x1 => ~~ dfa_fin A1 x1 ].
(** We construct the resulting automaton. **)
Definition dfa_compl :=
  dfaI
    A1
    (dfa_s0 A1)
    fin_compl
    (dfa_step A1).

(** We prove that the complement automaton accepts exactly
   the words not accepted by the original automaton. **)
Lemma dfa_compl_correct' w x:
  dfa_accept A1 x w = ~~ dfa_accept dfa_compl x w.
Proof. elim: w x => [|a w IHw] x.  
  by apply/idP/negPn.
simpl. by rewrite IHw.
Qed.

(** Language correctness for dfa_compl **)
Lemma dfa_compl_correct w:
  dfa_lang A1 w = ~~ dfa_lang dfa_compl w.
Proof. exact: dfa_compl_correct'. Qed.

  
(** Operations on two automata. **)
Section BinaryOps.
  
Variable A2: dfa.

(** Cross product of the two state sets **)
Definition state_prod := prod_finType A1 A2.

(** Disjunction automaton **)

Definition step_disj (x: state_prod) a :=
  let (x1, x2) := x in (dfa_step A1 x1 a, dfa_step A2 x2 a).
Definition dfa_disj :=
  dfaI
    state_prod
    (dfa_s0 A1, dfa_s0 A2) 
    (fun q => let (x1,x2) := q in dfa_fin A1 x1 || dfa_fin A2 x2)
    step_disj.

(** Correctness w.r.t. any state. **)
Lemma dfa_disj_correct' w x1 x2 :
  dfa_accept A1 x1 w || dfa_accept A2 x2 w
    = dfa_accept dfa_disj (x1, x2) w.
Proof. elim: w x1 x2 => [|a w IHw].
  by [].
move => x1 x2. by exact: IHw.
Qed.

(** Language correctness. **)
Lemma dfa_disj_correct w:
  dfa_lang A1 w || dfa_lang A2 w
    = dfa_lang dfa_disj w.
Proof. exact: dfa_disj_correct'. Qed.

(** Conjunction **) 
  
Definition step_conj (x: state_prod) a :=
  let (x1, x2) := x in (dfa_step A1 x1 a, dfa_step A2 x2 a).
Definition dfa_conj :=
  dfaI
    state_prod
    (dfa_s0 A1, dfa_s0 A2) 
    (fun q => let (x1,x2) := q in dfa_fin A1 x1 && dfa_fin A2 x2)
    step_disj
.

(** Correctness w.r.t. any state. **)
Lemma dfa_conj_correct' w x1 x2 :
  dfa_accept A1 x1 w && dfa_accept A2 x2 w
  = dfa_accept dfa_conj (x1, x2) w.
Proof. elim: w x1 x2 => [|a w IHw].
  by [].
move => x1 x2.
exact: IHw.
Qed.

(** Language correctness. **)
Lemma dfa_conj_correct w:
  dfa_lang A1 w && dfa_lang A2 w
  = dfa_lang dfa_conj w.
Proof. exact: dfa_conj_correct'. Qed.

End BinaryOps.

(* Remove unreachable states *)
Section Reachability.
  Definition e := [ fun x y => existsb a, dfa_step A1 x a == y ].

  Definition connected_s0 := enum (connect e (dfa_s0 A1)).

  Definition Connect_finMixin := seq_sub_finMixin (connected_s0).

  Canonical Structure Connect_finType := FinType _ Connect_finMixin.

  Lemma connected_step x a: x \in connected_s0 ->  dfa_step A1 x a \in connected_s0.
  Proof.
    rewrite 2!mem_enum -2!topredE /= => Hx.
    eapply connect_trans.
      eassumption.
    apply/connectP.
    exists [::dfa_step A1 x a] => //=.
    rewrite andbT. apply/existsP. by exists a.
  Qed.

  Definition dfa_connected_step (x: Connect_finType) (a: char) : Connect_finType.
    elim: x => [x Hx].
    exact (SeqSub (connected_step _ a Hx)).
  Defined.

  Lemma connected_s0_s0 : dfa_s0 A1 \in connected_s0. 
  Proof. rewrite mem_enum -topredE /= /connected_s0. by apply connect0. Qed.
  
  Definition dfa_connected :=
    dfaI
      Connect_finType
      (SeqSub (connected_s0_s0))
      (fun x => match x with SeqSub x _ => dfa_fin A1 x end)
      dfa_connected_step.
      

  Lemma dfa_connected_correct' x (Hx: x \in connected_s0) : dfa_accept dfa_connected (SeqSub Hx) =1 dfa_accept A1 x.
  Proof. move => w. elim: w x Hx => [|a w IHw] x Hx //=. Qed. 

  Lemma dfa_connected_correct: dfa_lang dfa_connected =1 dfa_lang A1.
  Proof.
    move => w. by rewrite /dfa_lang /= dfa_connected_correct'.
  Qed.

  Definition e_connected := [ fun x y => existsb a, dfa_step dfa_connected x a == y ].
  Lemma e_e_connected x y (Hx: x \in connected_s0) (Hy: y \in connected_s0) : connect e x y -> connect e_connected (SeqSub Hx) (SeqSub Hy).
  Proof.
    move/connectP => [p].
    elim: p x Hx y Hy => [|z p IHp] x Hx y Hy //=.
      move => _ H.                                
      move: Hx Hy. rewrite H => Hx Hy.
      have: (Hx = Hy).
        by apply: bool_irrelevance.
      move => ->.
      apply: connect0.
    move/andP => [] /existsP [] a /eqP Ha Hpz H.
    have Hz: (z \in connected_s0).
      rewrite -Ha. by apply connected_step.
    pose H0 := (IHp _ Hz _ Hy Hpz H).
    eapply connect_trans.
      apply connect1.
      instantiate (1 := SeqSub Hz).
      apply/existsP. exists a.
      simpl. move: Hz H0.
      rewrite -Ha => Hz H0.
      have: Hz = connected_step x a Hx.
        apply bool_irrelevance.
      by move => ->.
    assumption.
  Qed.
                   
  Lemma dfa_connected_repr' (x y: dfa_state dfa_connected): connect e_connected y x -> exists w, last y (dfa_run' dfa_connected y w) = x.
  Proof.
    move/connectP => [] p.
    elim: p x y => [|z p IHp] x y.
      move => _ -> /=. by exists [::].
    move => /= /andP [] /existsP [] a /eqP Ha Hp Hx.
    destruct (IHp x z) as [w Hw] => //.
    exists (a::w).
    by rewrite /= Ha.
  Qed.

  Definition dfa_connected_repr x : exists w, last (dfa_s0 dfa_connected) (dfa_run dfa_connected w) = x.
    apply dfa_connected_repr'.
    destruct x as [x Hx].
    apply (e_e_connected (dfa_s0 A1) x connected_s0_s0).
    by rewrite mem_enum -topredE /= in Hx.
  Qed.
    
End Reachability.


End DFAOps.

(** Operations on non-deterministic automata. **)
Section NFAOps.
Variable A1: nfa.
Variable A2: nfa.

(** Concatenation of two non-deterministic automata. **)

Definition state_conc : finType := sum_finType A1 A2.

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

Definition nfa_conc : nfa :=
  nfaI
    state_conc
    s0_conc
    fin_conc
    step_conc.

(** We prove that every path of A2 can be mapped to a path
   of nfa_conc. **)
Lemma nfa_conc_cont x xs w:
  nfa_lpath A2 x xs w
  -> nfa_lpath nfa_conc (inr _ x) (map (@inr A1 A2) xs) w.
Proof. elim: xs x w => [|y xs IHxs] x w; case: w => [|a w] => //.
simpl. by move/andP => [] -> /IHxs ->.
Qed.

(** We prove that every word in the language of A2
   is also accepted by any final state of A1 in
   nfa_conc. **)
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
rewrite H0 H1 /=.
apply: nfa_lpath_accept.
  apply nfa_conc_cont.
  by eassumption.
by rewrite last_map /nfa_fin.
Qed.

(** We prove that for every word w1 accepted by A1 in
   some state x and for every word w2 in the language of A2
   w1 ++ w2 will be accepted by the corresponding state in
   nfa_conc. **)
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
rewrite H1 /=.
apply: IHw1.
  exact: H2.
exact: H3.
Qed.

(** We prove that every word accepted by some state X in nfa_conc is
   - EITHER a concatenation of two words w1, w2 which are accpeted
   by A1, A2 (resp.) if X corresponds to one of A1's states
   - OR accepted by A2 in the state corresponding to X if X
   corresponds to one of A2's states. **)
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


(** Plus operator for non-deterministic automata. **)

(** The step relation implements the following rules:
   - every edge to a final state will also be duplicated
   to point to s0.
   **)
Definition step_plus x a y : bool :=
nfa_step A1 x a y || (
                      (y == nfa_s0 A1)
                      && existsb z, (nfa_fin A1 z) && (nfa_step A1 x a z)
                    ).

(** **)
Definition nfa_plus : nfa :=
  nfaI
    A1
    (nfa_s0 A1)
    (nfa_fin A1)
    step_plus.




(** We prove that every path of A1 can be mapped to a path
   of nfa_plus. **)
Lemma nfa_plus_cont x xs w:
  nfa_lpath A1 x xs w
  -> nfa_lpath nfa_plus x xs w.
Proof. elim: xs x w => [|y xs IHxs] x w; case: w => [|a w] => //.
move/andP => [] H0 /= /IHxs ->.
by rewrite /step_plus H0 orTb.
Qed.

(** We prove that every accepting path labeled (a::w) in A1
   exists in nfa_plus with only the last state changed to
   A1's starting state. This new path need not be accepting. **)
Lemma nfa_plus_lpath x y xs a w:
  nfa_fin nfa_plus (last x (y::xs)) ->
  nfa_lpath nfa_plus x (y::xs) (a::w) ->
  nfa_lpath nfa_plus x (rcons (belast y xs) (nfa_s0 A1)) (a::w).
Proof. elim: xs x y a w => [|z xs IHxs] x y a [|b w] //=.
      rewrite 2!andbT.
      move => H0 /orP [|/andP [] /eqP].
        move => H1. rewrite/step_plus.
        apply/orP. right. rewrite eq_refl.
        apply/existsP. exists y. by rewrite H0 H1.
      move => H1 /existsP [] z /andP [] H2 H3. move: H1 H0 => -> H4.
      apply/orP. right. rewrite eq_refl /=.
      apply/existsP. exists z. by rewrite H2 H3.
    by rewrite andbF.
  by rewrite andbF.
rewrite -(last_cons y). move => H0 /andP [] H1 /andP [] H3 H4.
rewrite H1 /=. apply: IHxs.
  by rewrite H0.
simpl. by rewrite H3 H4.
Qed.
  
(** We prove that every word accepted by A1 in
   some state x is also accepted by nfa_plus in
   that state. **)
Lemma nfa_plus_correct0' x w1 :
  nfa_accept A1 x w1 ->
  nfa_accept nfa_plus x w1.
Proof.
move/nfa_accept_lpath => [] xs [].
move/nfa_plus_cont => H0 H1.
apply: nfa_lpath_accept; by eassumption.
Qed.

(** We prove that every word accepted by A1 is also
   accepted by nfa_plus. **)
Lemma nfa_plus_correct0 w :
  nfa_lang A1 w ->
  nfa_lang nfa_plus w.
Proof. exact: nfa_plus_correct0'. Qed.

(** We prove that every prefix accpeted by A1 followed
   by a suffix accepted by nfa_plus is again accepted
   by nfa_plus. This is the first part of the proof of
   language correctness for nfa_plus. **)
Lemma nfa_plus_correct1 w1 w2:
  nfa_lang A1 w1 ->
  nfa_lang nfa_plus w2 ->
  nfa_lang nfa_plus (w1 ++ w2).
Proof.
move => /nfa_accept_lpath [] [|x xs] []; case: w1 => [|a w1] => //.
move => H0 H1 H2.
apply/(nfa_accept_cat).
exists (rcons (belast x xs) (nfa_s0 A1)).
apply/andP. split.
  apply: nfa_plus_lpath.
    exact: H1.
  apply: nfa_plus_cont.
  exact: H0.
rewrite last_rcons.
exact H2.
Qed.


(** We prove that every word accepted by some state x in nfa_plus
   is a concatenation of two words w1, w2 which are accpeted by
   A1 in x and nfa_plus (resp.). **) 
Lemma nfa_plus_correct2' x w :
  nfa_accept nfa_plus x w ->
  ((exists w1, exists w2, (w == w1 ++ w2) && (w1 != [::]) && (nfa_accept A1 x w1) && nfa_lang nfa_plus w2
    ) \/ nfa_accept A1 x w ).
Proof. elim: w x => [|a w IHw] x.
  move => H0. right.
  exact: H0.
case/existsP => y /andP [H0 H1].
case: (IHw _ H1) => [[w1 [w2 /andP [/andP [/andP [/eqP H2 H9] H3] H4]]]|H2].
  move: H0 => /orP [H5|].
    left. exists (a::w1). exists w2.
    rewrite H2 eq_refl H4 andbT /=.
    apply/existsP. exists y.
    by rewrite H5 H3.
  move/andP => [] H5 /existsP [] z /andP [H6 H7].
  move: H5 H1 H3 => /eqP -> H1 H3.
  left. exists ([::a]). exists w.
  rewrite eq_refl /=. apply/andP. split.
    apply/existsP. exists z. by rewrite H6 H7.
  exact: H1.
move: H0 => /orP [H5|].
  right => /=. apply/existsP. exists y.
  by rewrite H5 H2.
move/andP => [/eqP H3 /existsP [z /andP [H4 H5]]].
move: H3 H1 H2 => -> H1 H2.
left. exists [::a]. exists w.
rewrite eq_refl /=. apply/andP. split.
  apply/existsP. exists z. by rewrite H5 H4.
exact H1.
Qed.

(** We prove the second part of language correctness
   for nfa_plus. **)
Lemma nfa_plus_correct2 w:
  nfa_lang nfa_plus w ->
  ((exists w1, exists w2, (w == w1 ++ w2) && (w1 != [::]) && (nfa_lang A1 w1) && nfa_lang nfa_plus w2
    ) \/ nfa_lang A1 w ).
Proof. exact: nfa_plus_correct2'. Qed.



End NFAOps.


End FA.


