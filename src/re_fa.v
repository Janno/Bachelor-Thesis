Require Import ssreflect ssrbool eqtype fintype finfun seq fingraph ssrfun ssrnat finset.
Require Import automata regexp misc.

Set Implicit Arguments.

Lemma sizeNnil char (w: word char): w != [::] -> size w > 0.
Proof. case: w => //. Qed.

Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) (x : X) :
(forall x, (forall y, f y  < f x -> p y)  -> p x) -> p x.

Proof. intros A. apply A. 
induction (f x) ; move => y B => //=.
apply A. move => z C. apply: IHn. apply: leq_trans. eassumption.
apply: leq_trans.
eassumption. by [].
Qed.

Section RE_FA.
  Variable char: finType.
  Definition word:= misc.word char.
  Variable r: regular_expression char.

  Lemma RE_FA: exists A: dfa char,
    forall w: word, w \in (dfa_lang A: pred word) = (w \in r).
  Proof.
    elim: r => [].

    exists (dfa_void char).
    move => w. apply/idP/idP. exact: dfa_void_correct.

    exists (dfa_empty char).
    exact: dfa_empty_correct.
    
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
    rewrite in_simpl -topredE [topred _]/=.
    rewrite nfa_star_correct.
    apply/starP/starP.
      move => [] vv.
      move => H0 H1.
      exists vv.
      erewrite (eq_all).
          eexact H0.
        move => x /=.
        apply/andP/andP; move => [] H2 H3; split => //.
          rewrite -topredE [topred _]/= -dfa_to_nfa_correct.
          move: H3. by rewrite -H.
        move: H3. 
        rewrite -topredE [topred _]/= -dfa_to_nfa_correct.
        by rewrite -H.
      exact H1.
    move => [] vv H1 H2. exists vv => //.
    erewrite eq_all. eexact H1.
    move => x /=.
    apply/andb_id2l => H3.
    by rewrite -H -topredE [topred _]/= -dfa_to_nfa_correct.
     
        
    move => s [] As Hs t [] At Ht.
    exists (dfa_disj As At).
    move => w. rewrite in_simpl -dfa_disj_correct -topredE /= /plus /predU /=.
    by rewrite -Hs -Ht 2!in_simpl /=.

    move => s [] As Hs t [] At Ht.
    exists (dfa_conj As At).
    move => w. rewrite in_simpl -dfa_conj_correct -topredE /= /prod /predU /=.
    by rewrite -Hs -Ht 2!in_simpl /=.

    move => s [] As Hs t [] At Ht.
    exists (nfa_to_dfa (nfa_conc (dfa_to_nfa As) (dfa_to_nfa At))).
    move => w. rewrite in_simpl -nfa_to_dfa_correct. 
    apply/idP/idP.
    move/nfa_conc_sound => [] w1 [] w2 /andP [] /andP [] /eqP H0 H1 H2.
    apply/concP.
    exists w1. by rewrite -Hs in_simpl dfa_to_nfa_correct /nfa_lang /= H1.
    exists w2. by rewrite -Ht in_simpl dfa_to_nfa_correct H2.
    exact H0.
    move/concP => [] w1. rewrite -Hs => H1 [] w2. rewrite -Ht => H2 ->.
    apply/nfa_conc_complete.
      move: H1. by rewrite in_simpl dfa_to_nfa_correct /nfa_lang /=.
    move: H2. by rewrite in_simpl dfa_to_nfa_correct /nfa_lang /=.


    move => s [] A H.
    exists (dfa_compl A).
    move => w. rewrite 2!in_simpl /predC /=.
    move: (H w). rewrite -(topredE w s) /= /mem_reg => <-.
    rewrite in_simpl dfa_compl_correct.
    by apply/idP/negPn.

  Qed.
    
End RE_FA.