Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype finfun fingraph  finset.
Require Import automata regexp misc.

Set Implicit Arguments.

Section RE_FA.
  Variable char: finType.
  Definition word:= misc.word char.
  Variable r: regular_expression char.

  Lemma re_to_dfa: exists A: dfa char,
    forall w: word, w \in (dfa_lang A: pred word) = (w \in r).
  Proof.
    elim: r => [].

    exists (dfa_void char).
    move => w. apply/idP/idP. exact: dfa_void_correct.

    exists (dfa_eps char).
    exact: dfa_eps_correct.
    
    exists (dfa_dot char).
    move => w.
    rewrite -topredE /= /dot.
    exact: dfa_dot_correct.

    move => a. exists (dfa_char char a).
    move => w. exact: dfa_char_correct.

    (* Star *)
    move => s [] A H.
    exists (nfa_star (dfa_to_nfa A)).
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
          move: H3. by rewrite -H.
        move: H3. 
        rewrite -dfa_to_nfa_correct.
        by rewrite -H.
      exact H1.
    move => [] vv H1 H2. exists vv => //.
    erewrite eq_all. eexact H1.
    move => x /=.
    apply/andb_id2l => H3.
    by rewrite -H -dfa_to_nfa_correct.
     
        
    move => s [] As Hs t [] At Ht.
    exists (dfa_disj As At).
    move => w. rewrite -dfa_disj_correct in_simpl /=.
    by rewrite Ht Hs /=.

    move => s [] As Hs t [] At Ht.
    exists (dfa_conj As At).
    move => w. rewrite -dfa_conj_correct in_simpl /=.
    by rewrite Hs Ht /=.

    move => s [] As Hs t [] At Ht.
    exists (nfa_to_dfa (nfa_conc (dfa_to_nfa As) (dfa_to_nfa At))).
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
                 
    move => s [] A H.
    exists (dfa_compl A).
    move => w. by rewrite -dfa_compl_correct -topredE /= H.
  Qed.
    
End RE_FA.