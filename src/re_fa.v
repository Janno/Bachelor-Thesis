Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype finfun fingraph  finset.
Require Import automata regexp misc.

Set Implicit Arguments.

Section RE_FA.
  Variable char: finType.
  Definition word:= misc.word char.

  Fixpoint re_to_dfa (r: regular_expression char): dfa char :=
    match r with
    | Void => dfa_void char
    | Eps => dfa_eps char
    | Dot => dfa_dot char
    | Atom a => dfa_char char a
    | Star s => nfa_star (dfa_to_nfa (re_to_dfa s))
    | Plus s t => dfa_disj (re_to_dfa s) (re_to_dfa t)
    | And s t => dfa_conj (re_to_dfa s) (re_to_dfa t)
    | Conc s t => nfa_to_dfa (nfa_conc (dfa_to_nfa (re_to_dfa s)) (dfa_to_nfa (re_to_dfa t)))
    | Not s => dfa_compl (re_to_dfa s)
    end.

  Lemma re_to_dfa_correct r: dfa_lang (re_to_dfa r) =i r.
  Proof.
    elim: r => [].

    move => w. apply/idP/idP. exact: dfa_void_correct.

    exact: dfa_eps_correct.
    
    move => w.
    rewrite -topredE /= /dot.
    exact: dfa_dot_correct.

    move => a. 
    move => w. exact: dfa_char_correct.

    (* Star *)
    move => s IHs.
    move => w.
    rewrite nfa_star_correct.
    apply/starP/starP.
      move => [] vv.
      move => H0 H1.
      exists vv.
      erewrite (eq_all).
          eexact H0.
        move => x /=.
        apply/andP/andP; move => [] H2 H3; split => //.
          rewrite -dfa_to_nfa_correct.
          move: H3. by rewrite -IHs.
        move: H3. 
        rewrite -dfa_to_nfa_correct.
        by rewrite -IHs.
      exact H1.
    move => [] vv H1 H2. exists vv => //.
    erewrite eq_all. eexact H1.
    move => x /=.
    apply/andb_id2l => H3.
    by rewrite -IHs -dfa_to_nfa_correct.
     
        
    move => s Hs t Ht.
    move => w. rewrite -dfa_disj_correct in_simpl /=.
    by rewrite Ht Hs /=.

    move => s Hs t Ht.
    move => w. rewrite -dfa_conj_correct in_simpl /=.
    by rewrite Hs Ht /=.

    move => s Hs t Ht.
    move => w. rewrite -nfa_to_dfa_correct. 
    apply/idP/idP.
    move/nfa_conc_aux1 => [] w1 [] w2 /andP [] /andP [] /eqP H0 H1 H2.
    rewrite -topredE /=.
    apply/concP.
    exists w1. by rewrite -Hs -topredE /= dfa_to_nfa_correct' /nfa_lang /= H1.
    exists w2. rewrite /= in H2. by rewrite -Ht dfa_to_nfa_correct in_simpl H2.
    exact H0.
    move/concP => [] w1. rewrite -Hs => H1 [] w2. rewrite -Ht => H2 ->.
    apply/nfa_conc_aux2.
      move: H1. by rewrite  dfa_to_nfa_correct /nfa_lang /=.
    move: H2. by rewrite dfa_to_nfa_correct /nfa_lang /=.
                 
    move => s H.
    move => w. by rewrite -dfa_compl_correct -topredE /= H.
  Qed.

  Definition re_equiv r s := dfa_equiv (re_to_dfa r) (re_to_dfa s).
  
  Lemma re_equiv_correct r s: re_equiv r s <-> r =i s.
  Proof.
    rewrite dfa_equiv_correct.
    split => H w. 
      move/H: (w). by rewrite !re_to_dfa_correct.
    by rewrite !re_to_dfa_correct.
  Qed.

End RE_FA.

