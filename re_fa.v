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
    exists (
        dfa_disj
          (dfa_empty char)
          (nfa_to_dfa
             (nfa_plus
                (dfa_to_nfa A)
             )
          )
      ).
    move => w.
    rewrite in_simpl -dfa_disj_correct.
    apply/idP/idP.
      rewrite dfa_empty_correct => /orP [].
        move => /eqP ->.
        apply/starP. by exists [::].

      rewrite -nfa_to_dfa_correct.
      apply (size_induction size (fun w => _) w).
      clear w. move => w IHw.
      move/nfa_plus_correct2 => [].
        move => [] w1 [] w2 [/andP [/andP [/andP [/eqP H1 H2] H3] H4]].
        have H5: (size w2 < size w).
          rewrite H1 size_cat addnC -{1}(addn0 (size w2)).
          rewrite ltn_add2l.
          by apply: sizeNnil.
        move: (IHw w2 H5 H4) => /starP [] vv H6 H7.
        apply/starP. exists (w1::vv).
          rewrite /= H6 -topredE /= /eps /= H2 -H in_simpl /dfa_lang /=.
          move: H3. move: (dfa_to_nfa_correct A w1).
          by rewrite /dfa_lang /= => -> ->.
        by rewrite H1 H7.

      rewrite -dfa_to_nfa_correct.
      move => H0.
      case: w IHw H0 => [|a w] IHw H0; apply/starP.
        by exists [::]=> //=.
      exists ([::(a::w)]).
        by rewrite /= -H in_simpl H0.
      by rewrite /= cats0.

    rewrite -nfa_to_dfa_correct.
    move/starP => [] vv. elim: vv w => [|v vv IHvv] w.
      rewrite /= => _ ->. move: (dfa_empty_correct char [::]).
      by rewrite /dfa_lang /=.
    move/andP => [] /andP [] H0 H1 H2 H3.
    rewrite H3 [flatten _]/=.
    move/orP: (IHvv (flatten vv) H2 (Logic.eq_refl _)) => [].
      rewrite dfa_empty_correct => /eqP H4.
      move: H3. rewrite [flatten _]/= H4 cats0.
      move => H5. subst. apply/orP. right.
      rewrite H4 in IHvv.
      apply nfa_plus_correct0.
      rewrite -dfa_to_nfa_correct.
      move: (H v).
      by rewrite in_simpl -topredE /= => ->.
    move => H4.
    apply/orP. right.
    apply: nfa_plus_correct1 => //.
    move: (H v).
    by rewrite -dfa_to_nfa_correct in_simpl -topredE /= => ->.

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
    move/nfa_conc_correct2 => [] w1 [] w2 /andP [] /andP [] /eqP H0 H1 H2.
    apply/concP.
    exists w1. by rewrite -Hs in_simpl dfa_to_nfa_correct /nfa_lang /= H1.
    exists w2. by rewrite -Ht in_simpl dfa_to_nfa_correct H2.
    exact H0.
    move/concP => [] w1. rewrite -Hs => H1 [] w2. rewrite -Ht => H2 ->.
    apply/nfa_conc_correct1.
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