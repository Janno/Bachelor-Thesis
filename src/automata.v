Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype fingraph  finfun  finset.

Require Import misc.
Require Import regexp.

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
  {
    dfa_state :> finType;
    dfa_s: dfa_state;
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

(** A simplifying function for a "aux2" run
   (i.e. starting at s). **)
Definition dfa_run := [fun w => dfa_run' (dfa_s A) w].

(** Acceptance of w in x is defined as
   finality of the last state of a run of w on A
   starting in x. **)
Fixpoint dfa_accept x w :=
match w with
  | [::] => dfa_fin A x
  | a::w => dfa_accept (dfa_step A x a) w
end.

Lemma dfa_accept_cons x a w:
  a::w \in dfa_accept x = (w \in dfa_accept (dfa_step A x a)).
Proof. by rewrite -simpl_predE /=. Qed.

(** We define the language of the deterministic
   automaton, i.e. acceptance in the starting state. **)
Definition dfa_lang := [pred w | dfa_accept (dfa_s A) w].

(** take lemma. **)
Lemma dfa_run'_take x w n: take n (dfa_run' x w) = dfa_run' x (take n w).
Proof. elim: w x n => [|a w IHw] x n //.
case: n => [|n] //=. by rewrite IHw.
Qed.

(** rcons and cat lemmas. **)
Lemma dfa_run'_cat x w1 w2 :
  dfa_run' x (w1 ++ w2) = dfa_run' x w1 ++ dfa_run' (last x (dfa_run' x w1)) w2.
Proof. elim: w1 w2 x => [|a w1 IHw1] w2 x //.
simpl. by rewrite IHw1.
Qed.


(* slightly altered acceptance statement. *)
Lemma dfa_run_accept x w: last x (dfa_run' x w) \in dfa_fin A = (w \in dfa_accept x).
Proof. elim: w x => [|a w IHw] x //. by rewrite /= IHw. Qed.

End Acceptance.

End DFA.

Implicit Arguments Build_dfa [dfa_state]. 


(** Non-deterministic automata. **)
Section NFA.

(** The type of non-deterministic finite automata. ***)
Record nfa : Type :=
  {
    nfa_state :> finType;
    nfa_s: nfa_state;
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
  | a::w => [ exists y, (nfa_step A x a y) && nfa_accept y w ]
end.

(** We define the language of the non-deterministic
   automaton, i.e. acceptance in the starting state. **)
Definition nfa_lang := [pred w | nfa_accept (nfa_s A) w].

(** We define labeled paths over the non-deterministic step relation **)
Fixpoint nfa_run x (xs : seq A) (w: word) {struct xs} :=
match xs,w with
  | y :: xs', a::w' => nfa_step A x a y && nfa_run y xs' w'
  | [::]    , [::]  => true
  | _       , _     => false
end.

Lemma nfa_run_accept x w:
  reflect (exists2 xs, nfa_run x xs w & last x xs \in nfa_fin A)
          (nfa_accept x w).
Proof.
  elim: w x => [|a w IHw] x.
    case H: (nfa_accept x [::]); constructor.
      by exists [::].
    move => [[|y xs]] //.
    move: H => /= H _.
    by rewrite -topredE /= H.
  case H: nfa_accept => /=; constructor.
    move/existsP: H => [] y /andP [] H1 /IHw [] xs H2 H3.
    exists (y::xs) => //=.
    by rewrite H1 H2 /=.
  move => [[|y xs]] //= /andP [] H1 H2 H3.
  move/existsP: H => H.
  apply: H. exists y.
  rewrite H1 /=.
  apply/IHw.
  by exists xs.
Qed.
 

(** Helpful facts **)
Lemma nfa_accept_cat x w1 w2:
  nfa_accept x (w1 ++ w2) <->
  exists xs,
    nfa_run x xs w1
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

Implicit Arguments Build_nfa [nfa_state]. 

(** We define the powerset construction to obtain
   a deterministic automaton from a non-deterministic one. **) 
Section PowersetConstruction.

Variable A: nfa.

Definition nfa_to_dfa :=
  {| dfa_s := set1 (nfa_s A);
    dfa_fin := [ pred X: {set A} | [ exists x: A, (x \in X) && nfa_fin A x] ];
    dfa_step := [ fun X a => \bigcup_(x | x \in X) finset (nfa_step A x a) ]
   |}.

(** We prove that for every state x, the new automaton
   accepts at least the language of the given automaton
   when starting in a set containing x. **)
Lemma nfa_to_dfa_aux2 (x: A) w (X: nfa_to_dfa):
  x \in X -> nfa_accept A x w -> dfa_accept nfa_to_dfa X w.
Proof. move => H0.
  elim: w X x H0 => [|a w IHw] X x H0.
    (* [::] *)
    move => /= H1. apply/existsP. exists x.
    by rewrite H0 H1.
  (* a::w *)
  move => /= /existsP [] y /andP [] H1.
  apply (IHw).
  apply/bigcupP.
  exists x => //.
  by rewrite in_set.
Qed.

(** Next we prove that in any set of states X, for every word w,
   if the powerset automaton accepts w in X, there exists one
   representative state of that set in which the given automaton
   accepts w. **)
Lemma nfa_to_dfa_aux1 (X: nfa_to_dfa) w:
  dfa_accept nfa_to_dfa X w -> [ exists x, (x \in X) && nfa_accept A x w ].
Proof. elim: w X => [|a w IHw] X => //.
  move/IHw => /existsP [] y /andP [].
  rewrite /dfa_step /nfa_to_dfa. 
  move/bigcupP => [] x H0. rewrite in_set => H1 H2 /=.
  apply/existsP. exists x. rewrite H0 /=.
  apply/existsP. exists y. 
  by rewrite H1 H2.
Qed.

(** Finally, we prove that the language of the powerset
   automaton is exactly the language of the given
   automaton. **)
Lemma nfa_to_dfa_correct : nfa_lang A =i dfa_lang nfa_to_dfa.
Proof. move => w. apply/idP/idP => /=.
  apply: nfa_to_dfa_aux2. by apply/set1P.
by move/nfa_to_dfa_aux1 => /existsP [] x /andP [] /set1P ->.
Qed.
  

End PowersetConstruction.


(** Embedding deterministic automata in non-deterministic automata. **)
Section Embed.

Variable A: dfa.

Definition dfa_to_nfa : nfa :=
  {|
    nfa_s := dfa_s A;
    nfa_fin := dfa_fin A;
    nfa_step := fun x a y => y == dfa_step A x a 
  |}.

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
Lemma dfa_to_nfa_correct : dfa_lang A =i nfa_lang dfa_to_nfa.
Proof.
  exact: dfa_to_nfa_correct'.
Qed.
    
End Embed.

(** Primitive automata **)
Section Primitive.
  Definition dfa_void :=
   {| 
      dfa_s := tt;
      dfa_fin := pred0;
      dfa_step := [fun x a => tt]
   |}.
  
  Lemma dfa_void_correct x w: ~~ dfa_accept dfa_void x w.
  Proof. by elim: w x => [|a w IHw] //= x. Qed.

  Definition dfa_eps :=
    {|
      dfa_s := true;
      dfa_fin := pred1 true;
      dfa_step := [fun x a => false]
     |}.

  Lemma dfa_eps_correct: dfa_lang dfa_eps =i pred1 [::].
  Proof.
    have H: (forall w, ~~ dfa_accept dfa_eps false w).
      by elim => [|a v IHv] //=.
    move => w.
    elim: w => [|a w IHw] //.
    apply/idP/idP.
    exact: H. 
  Qed.
      
  Definition dfa_char a :=
    {|
      dfa_s := None;
      dfa_fin := pred1 (Some true);
      dfa_step := [fun x b => if x == None then if b == a then Some true else Some false else Some false ]
    |}.
  
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
    {|
      dfa_s := None;
      dfa_fin := pred1 (Some true);
      dfa_step := [fun x b => if x == None then Some true else Some false ]
    |}.
            
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
  
(** We construct the resulting automaton. **)
Definition dfa_compl :=
 {| 
    dfa_s := dfa_s A1;
    dfa_fin := [ fun x1 => ~~ dfa_fin A1 x1 ];
    dfa_step := (dfa_step A1)
  |}.

(** We prove that the complement automaton accepts exactly
   the words not accepted by the original automaton. **)
Lemma dfa_compl_correct' x:
  [ predC dfa_accept A1 x ] =i dfa_accept dfa_compl x.
Proof. move => w. elim: w x => [|a w IHw] x.  
    by apply/idP/idP.
  simpl. rewrite -topredE dfa_accept_cons /= -IHw.
  apply/negP/idP; rewrite dfa_accept_cons; by move/negP.
Qed.

(** Language correctness for dfa_compl **)
Lemma dfa_compl_correct:
  [ predC dfa_lang A1 ] =i dfa_lang dfa_compl.
Proof. exact: dfa_compl_correct'. Qed.

  
(** Operations on two automata. **)
Section BinaryOps.
  
Variable A2: dfa.

(** Disjunction automaton **)

Definition dfa_disj :=
  {|
    dfa_s := (dfa_s A1, dfa_s A2);
    dfa_fin := (fun q => let (x1,x2) := q in dfa_fin A1 x1 || dfa_fin A2 x2);
    dfa_step := [fun x a => (dfa_step A1 x.1 a, dfa_step A2 x.2 a)]
   |}.

(** Correctness w.r.t. any state. **)
Lemma dfa_disj_correct' x:
  [ predU dfa_accept A1 x.1 & dfa_accept A2 x.2 ]
    =i dfa_accept dfa_disj x.
Proof. move => w. elim: w x => [|a w IHw].
  by move => [].
move => x /=. by rewrite dfa_accept_cons -IHw.
Qed.

(** Language correctness. **)
Lemma dfa_disj_correct:
  [ predU  dfa_lang A1 & dfa_lang A2 ]
    =i dfa_lang dfa_disj.
Proof. move => w /=. by rewrite -dfa_disj_correct'. Qed.

(** Conjunction **) 
  
Definition dfa_conj :=
 {| 
    dfa_s := (dfa_s A1, dfa_s A2);
    dfa_fin := (fun x => dfa_fin A1 x.1 && dfa_fin A2 x.2);
    dfa_step := [fun x a => (dfa_step A1 x.1 a, dfa_step A2 x.2 a)]
  |}.

(** Correctness w.r.t. any state. **)
Lemma dfa_conj_correct' x1 x2 :
  [ predI  dfa_accept A1 x1 & dfa_accept A2 x2 ]
  =i dfa_accept dfa_conj (x1, x2).
Proof. move => w. elim: w x1 x2 => [|a w IHw].
  by [].
move => x1 x2.
exact: IHw.
Qed.

(** Language correctness. **)
Lemma dfa_conj_correct:
  [ predI dfa_lang A1 & dfa_lang A2 ]
  =i dfa_lang dfa_conj.
Proof. move => w. by rewrite -dfa_conj_correct'  /=. Qed.

End BinaryOps.

(* Remove unreachable states *)
Section Reachability.
  Definition reachable1 := [ fun x y => [ exists a, dfa_step A1 x a == y ] ].

  Definition reachable := enum (connect reachable1 (dfa_s A1)).

  Lemma reachable_step x a: x \in reachable ->  dfa_step A1 x a \in reachable.
  Proof.
    rewrite 2!mem_enum -2!topredE /= => Hx.
    eapply connect_trans.
      eassumption.
    apply/connectP.
    exists [::dfa_step A1 x a] => //=.
    rewrite andbT. apply/existsP. by exists a.
  Qed.

  Lemma reachable0 : dfa_s A1 \in reachable. 
  Proof. rewrite mem_enum -topredE /=. by apply connect0. Qed.

  Definition dfa_connected :=
   {| 
      dfa_s := SeqSub reachable0;
      dfa_fin := fun x => match x with SeqSub x _ => dfa_fin A1 x end;
      dfa_step := fun x a => match x with
        | SeqSub _ Hx => SeqSub (reachable_step _ a Hx)
        end
    |}.
      

  Lemma dfa_connected_correct' x (Hx: x \in reachable) :
    dfa_accept dfa_connected (SeqSub Hx) =i dfa_accept A1 x.
  Proof. move => w. elim: w x Hx => [|a w IHw] x Hx //=.
    by rewrite 2!dfa_accept_cons IHw.
  Qed. 

  Lemma dfa_connected_correct: dfa_lang dfa_connected =i dfa_lang A1.
  Proof.
    move => w. by rewrite /dfa_lang /= dfa_connected_correct'.
  Qed.

  Definition reachable1_connected := [ fun x y => [ exists a, dfa_step dfa_connected x a == y ] ].
  Lemma reachable1_connected_aux2 x y (Hx: x \in reachable) (Hy: y \in reachable) : connect reachable1 x y -> connect reachable1_connected (SeqSub Hx) (SeqSub Hy).
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
    have Hz: (z \in reachable).
      rewrite -Ha. by apply reachable_step.
    pose H0 := (IHp _ Hz _ Hy Hpz H).
    eapply connect_trans.
      apply connect1.
      instantiate (1 := SeqSub Hz).
      apply/existsP. exists a.
      simpl. move: Hz H0.
      rewrite -Ha => Hz H0.
      have: Hz = reachable_step x a Hx.
        apply bool_irrelevance.
      by move => ->.
    assumption.
  Qed.

                   
  Lemma dfa_connected_repr' (x y: dfa_connected):
    connect reachable1_connected y x ->
    exists w, last y (dfa_run' dfa_connected y w) = x.
  Proof.
    move/connectP => [] p.
    elim: p x y => [|z p IHp] x y.
      move => _ -> /=. by exists [::].
    move => /= /andP [] /existsP [] a /eqP Ha Hp Hx.
    destruct (IHp x z) as [w Hw] => //.
    exists (a::w).
    by rewrite /= Ha.
  Qed.

  Lemma dfa_connected_repr x :
    exists w, last (dfa_s dfa_connected) (dfa_run dfa_connected w) = x.
  Proof.
    apply dfa_connected_repr'.
    destruct x as [x Hx].
    apply (reachable1_connected_aux2 (dfa_s A1) x reachable0).
    by rewrite mem_enum -topredE /= in Hx.
  Qed.
  
  Lemma dfa_connected_repr_pred x :
    exists w, last (dfa_s dfa_connected) (dfa_run dfa_connected w) == x.
  Proof.
    move: (dfa_connected_repr x) => [w /eqP].
    by eauto.
  Defined.
  
  Lemma dfa_connected_repr_fun (x: dfa_connected):
    word.
  Proof.
    move: (dfa_connected_repr_pred x).
    apply (xchoose).
  Defined.

  Lemma dfa_connected_repr_fun_correct x: last (dfa_s dfa_connected) (dfa_run dfa_connected (dfa_connected_repr_fun x)) = x.
  Proof.
    rewrite /dfa_connected_repr_fun. 
    by move: (xchooseP (dfa_connected_repr_pred x)) => /eqP.
  Qed.
    
  Lemma dfa_connected_repr_fun_injective: injective dfa_connected_repr_fun.
  Proof.
    move => x y.
    rewrite /dfa_connected_repr_fun => H.
    move: (xchooseP (dfa_connected_repr_pred x)) => /eqP.
    move: (xchooseP (dfa_connected_repr_pred y)) => /eqP.
    rewrite H. by move => -> ->.
  Qed.
    
End Reachability.

Section Emptiness.

  Definition dfa_lang_empty := #|dfa_fin dfa_connected| == 0.

  Lemma dfa_lang_empty_aux2: dfa_lang dfa_connected =i pred0 -> dfa_lang_empty.
  Proof.
    rewrite /dfa_lang_empty.
    move => H.
    apply/eqP/eq_card0.
    move => x.
    apply/idP/idP.
    apply/negP.
    move: (dfa_connected_repr x) => [w Hw].
    move: (H w).
    rewrite /dfa_lang /= -dfa_run_accept.
    rewrite Hw.
    by move/negP.
  Qed. 
  
  Lemma dfa_lang_empty_aux1: dfa_lang_empty -> dfa_lang dfa_connected =i pred0.
  Proof.
    rewrite /dfa_lang_empty.
    move => H w.
    apply/idP/idP.
    apply/negP.
    rewrite /dfa_lang /= -dfa_run_accept.
    by move/eqP/card0_eq: H => ->.
  Qed.
                              
  Lemma dfa_lang_empty_correct:
    reflect (dfa_lang A1 =i pred0)
            dfa_lang_empty.
  Proof.
    apply/iffP.
    eexact (@idP dfa_lang_empty ).
      move => H w. rewrite -dfa_connected_correct.
      exact: dfa_lang_empty_aux1.
    move => H.
    apply: dfa_lang_empty_aux2.
    move => w.
    by rewrite dfa_connected_correct.
  Qed.
    
End Emptiness.

End DFAOps.

Section Equivalence.
  Definition dfa_sym_diff A1 A2 :=
    dfa_disj (dfa_conj A1 (dfa_compl A2)) (dfa_conj A2 (dfa_compl A1)).

  Definition dfa_equiv A1 A2 := dfa_lang_empty (dfa_sym_diff A1 A2).

  Lemma dfa_equiv_correct A1 A2:
    dfa_equiv A1 A2 <-> dfa_lang A1 =i dfa_lang A2.
  Proof.
    split; rewrite /dfa_sym_diff.
      move/dfa_lang_empty_correct => H w.
      move: (H w).
      rewrite -dfa_disj_correct -topredE /= -2!dfa_conj_correct -2!topredE /= -2!dfa_compl_correct.
      move/norP => [] /nandP [] /negP H1 /nandP [] /negP H2;
      apply/idP/idP; try by [];
      move/negP: H1; move/negP: H2;
      by auto using negbNE.
    move => H. apply/dfa_lang_empty_correct => w. move: (H w).
    rewrite -dfa_disj_correct -3!topredE /= -2!dfa_conj_correct -2!topredE /= -2!dfa_compl_correct.
    rewrite -H -4!topredE /= -2!topredE /= andbN => ->.
    by rewrite andbN.
Qed.    

End Equivalence.


(** Operations on non-deterministic automata. **)
Section NFAOps.
Variable A1: nfa.
Variable A2: nfa.

(** Concatenation of two non-deterministic automata. **)

Definition nfa_conc : nfa :=
  {|
    nfa_s := inl _ (nfa_s A1);
    nfa_fin := [fun x => 
        match x with
          | inl x => nfa_fin A1 x && nfa_fin A2 (nfa_s A2)
          | inr x => nfa_fin A2 x
        end];
     nfa_step := fun x a y =>
        match x,y with
          | inl x, inl y => nfa_step A1 x a y
          | inl x, inr y => nfa_fin A1 x && nfa_step A2 (nfa_s A2) a y
          | inr x, inr y => nfa_step A2 x a y
          | inr x, inl y => false
        end
   |}.

(** We prove that every path of A2 can be mapped to a path
   of nfa_conc. **)
Lemma nfa_conc_cont x xs w:
  nfa_run A2 x xs w
  -> nfa_run nfa_conc (inr _ x) (map (@inr A1 A2) xs) w.
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
move => H0 /nfa_run_accept [] ys.
elim: ys w x1 H0 => [|y ys IHys] [|a w] x1 H0 //=.
  rewrite -topredE /=.
  by move: H0 => -> _ ->.
move => /andP [] H1 H2 H3.
apply/existsP. exists (inr _ y).
rewrite H0 H1 /=.
apply/nfa_run_accept.
  eexists _.
  apply nfa_conc_cont.
  by eassumption.
by rewrite last_map /nfa_fin.
Qed.

(** We prove that for every word w1 accepted by A1 in
   some state x and for every word w2 in the language of A2
   w1 ++ w2 will be accepted by the corresponding state in
   nfa_conc. **)
Lemma nfa_conc_aux2 x w1 w2:
  nfa_accept A1 x w1 ->
  nfa_lang A2 w2 ->
  nfa_accept nfa_conc (inl _ x) (w1 ++ w2).
Proof. elim: w1 w2 x => [|a w1 IHw1] w2 x.
    move => H0 /nfa_run_accept [] xs [] H1 H2.
    move: (nfa_conc_cont _ _ _ H1) => H3.
    apply/nfa_accept_cat.
    exists [::] => /=.
    apply: nfa_conc_fin1 => //.
    apply/nfa_run_accept.
    by eauto.
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
Lemma nfa_conc_aux1 X w :
  nfa_accept nfa_conc X w ->
  match X with
  | inl x => exists w1, exists w2, (w == w1 ++ w2) && (nfa_accept A1 x w1) && nfa_lang A2 w2
  | inr x => nfa_accept A2 x w
end.
Proof.
  elim: w X => [|a w IHw] [x|x] //=.
      move => /andP [] H0 H1. exists [::]. exists [::].
      by rewrite /= H0 H1.
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

Lemma nfa_conc_correct: nfa_lang nfa_conc =i conc (nfa_lang A1) (nfa_lang A2).
Proof.
  move => w.
  apply/idP/concP.
    move/nfa_conc_aux1.
    rewrite /nfa_conc /nfa_s.
    move => [] w1 [] w2 /andP [] /andP [] /eqP H0 H1 H2.
    by eauto.
  move => [] w1 H0 [] w2 H2 ->.
  by apply/nfa_conc_aux2.
  Qed.  

(** Plus operator for non-deterministic automata. **)

(** The step relation implements the following rule:
   - every edge to a final state will also be duplicated
   to point to s0.
   **)
Definition step_plus x a y : bool :=
nfa_step A1 x a y || (
                      (y == nfa_s A1)
                      && [ exists z, (nfa_fin A1 z) && (nfa_step A1 x a z) ]
                    ).

(** **)
Definition nfa_repeat : nfa :=
  {|
    nfa_s := nfa_s A1;
    nfa_fin := nfa_fin A1;
    nfa_step := fun x a y =>
        nfa_step A1 x a y || (
                      (y == nfa_s A1)
                      && [ exists  z, (nfa_fin A1 z) && (nfa_step A1 x a z) ]
                    )
   |}.


(** We prove that every path of A1 can be mapped to a path
   of nfa_repeat. **)
Lemma nfa_repeat_cont x xs w:
  nfa_run A1 x xs w
  -> nfa_run nfa_repeat x xs w.
Proof. elim: xs x w => [|y xs IHxs] x w; case: w => [|a w] => //.
move/andP => [] H0 /= /IHxs ->.
by rewrite /step_plus H0 orTb.
Qed.

(** We prove that every accepting path labeled (a::w) in A1
   exists in nfa_repeat with only the last state changed to
   A1's starting state. This new path need not be accepting. **)
Lemma nfa_repeat_lpath x y xs a w:
  nfa_fin nfa_repeat (last x (y::xs)) ->
  nfa_run nfa_repeat x (y::xs) (a::w) ->
  nfa_run nfa_repeat x (rcons (belast y xs) (nfa_s A1)) (a::w).
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
   some state x is also accepted by nfa_repeat in
   that state. **)
Lemma nfa_repeat_correct0' x w1 :
  nfa_accept A1 x w1 ->
  nfa_accept nfa_repeat x w1.
Proof.
  move/nfa_run_accept => [] xs [].
  move/nfa_repeat_cont => H0 H1.
  apply/nfa_run_accept.
  by exists xs. 
Qed.

(** We prove that every word accepted by A1 is also
   accepted by nfa_repeat. **)
Lemma nfa_repeat_correct0 w :
  nfa_lang A1 w ->
  nfa_lang nfa_repeat w.
Proof. exact: nfa_repeat_correct0'. Qed.

(** We prove that every prefix accpeted by A1 followed
   by a suffix accepted by nfa_repeat is again accepted
   by nfa_repeat. This is the first part of the proof of
   language correctness for nfa_repeat. **)
Lemma nfa_repeat_aux2 w1 w2:
  nfa_lang A1 w1 ->
  nfa_lang nfa_repeat w2 ->
  nfa_lang nfa_repeat (w1 ++ w2).
Proof.
move => /nfa_run_accept [] [|x xs] []; case: w1 => [|a w1] => //.
move => H0 H1 H2.
apply/(nfa_accept_cat).
exists (rcons (belast x xs) (nfa_s A1)).
apply/andP. split.
  apply: nfa_repeat_lpath.
    exact: H1.
  apply: nfa_repeat_cont.
  exact: H0.
rewrite last_rcons.
exact H2.
Qed.


(** We prove that every word accepted by some state x in nfa_repeat
   is a concatenation of two words w1, w2 which are accpeted by
   A1 in x and nfa_repeat (resp.). **) 
Lemma nfa_repeat_aux1' x w :
  nfa_accept nfa_repeat x w ->
  ((exists w1, exists w2, (w == w1 ++ w2) && (w1 != [::]) && (nfa_accept A1 x w1) && nfa_lang nfa_repeat w2
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
   for nfa_repeat. **)
Lemma nfa_repeat_aux1 w:
  nfa_lang nfa_repeat w ->
  ((exists w1, exists w2, (w == w1 ++ w2) && (w1 != [::]) && (nfa_lang A1 w1) && nfa_lang nfa_repeat w2
    ) \/ nfa_lang A1 w ).
Proof. exact: nfa_repeat_aux1'. Qed.


(* Star operator *)
Definition nfa_star := (dfa_disj dfa_eps (nfa_to_dfa nfa_repeat)).

Lemma nfa_star_aux1 w: w \in dfa_lang nfa_star -> w \in star (nfa_lang A1).
Proof.
  rewrite /nfa_star -dfa_disj_correct -topredE /=.
    rewrite dfa_eps_correct => /orP [].
      move => /eqP ->.
      apply/starP. by exists [::].
    rewrite -nfa_to_dfa_correct.
    move: w.
    apply: (size_induction size).
    move => w IHw.
    move/nfa_repeat_aux1' => [].
      move => [] w1 [] w2 [/andP [/andP [/andP [/eqP H1 H2] H3] H4]].
      have H5: (size w2 < size w).
        rewrite H1 size_cat addnC -{1}(addn0 (size w2)).
        rewrite ltn_add2l.
        by destruct w1.
      move: (IHw w2 H5 H4) => /starP [] vv H6 H7.
      apply/starP. exists (w1::vv).
          by rewrite /= H6 -topredE /= /eps /= H2 /nfa_lang /= -topredE /= H3.
        by rewrite H1 H7.
      rewrite /nfa_lang /=.

      case: w IHw => [|a w] IHw H.
        apply/starP. by exists [::].
      apply/starP.
        exists [::(a::w)] => //=.
        by rewrite -topredE andbT.
      by rewrite cats0.
Qed.  
      
Lemma nfa_star_aux2 w: w \in star (nfa_lang A1) -> w \in dfa_lang nfa_star.
Proof.
    rewrite /nfa_star -dfa_disj_correct -2!topredE /= -nfa_to_dfa_correct.
    move/starP => [] vv. elim: vv w => [|v vv IHvv] w.
      rewrite /= => _ ->. move: (dfa_eps_correct [::]).
      by rewrite /dfa_lang /=.
    rewrite [all _ _]/=.
    move/andP => [] /andP [] H0 H1 H2 H3.
    rewrite H3 [flatten _]/=.
    move/orP: (IHvv (flatten vv) H2 (Logic.eq_refl _)) => [].
      rewrite dfa_eps_correct => /eqP H4.
      move: H3. rewrite [flatten _]/= H4 cats0.
      move => H5. subst. apply/orP. right.
      rewrite H4 in IHvv.
      by apply nfa_repeat_correct0.
    move => H4.
    apply/orP. right.
    by apply: nfa_repeat_aux2.
Qed.

Lemma nfa_star_correct: dfa_lang nfa_star =i star (nfa_lang A1).
Proof.
  move => w.
  apply/idP/idP.
    by move/nfa_star_aux1.
  by move/nfa_star_aux2.
Qed.

End NFAOps.


End FA.


