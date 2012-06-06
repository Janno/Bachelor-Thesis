Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool finset choice.
Require Import automata misc regexp.
Require Import Program.Equality.

Section MyhillNerode.
  Variable char: finType.
  Definition word:= word char.

  Section Relation.
    Variable X: finType.
    Variable L: language char.

    Definition MH_rel w1 w2 := forall w3, w1++w3 \in L <-> w2++w3 \in L.

    (* We model finiteness of equivalence classes
     by functions to some finType. *)

    Definition Fin_eq_cls := word -> X.
    
    (* We define what it means to be a refinement
     of the MH relation: *)
    Definition MH_rel_ref (f: Fin_eq_cls) := forall w1 w2, f w1 = f w2 <-> MH_rel w1 w2.
    
  End Relation.

  Section ToDFA.
    Variable L: language char.
    Variable X: finType.
    Variable f: Fin_eq_cls X.
    Variable ref: MH_rel_ref X L f.

    Definition surj (f: Fin_eq_cls X) := forall x, exists w, f(w) == x. 

    Variable f_surj: surj f.

    Definition f_inv := fun x => xchoose (f_surj x).

    Definition f_invK: cancel f_inv f.
    Proof.
      move => x.
      by move: (xchooseP (f_surj x)) => /eqP {2}<-.
    Qed.
    
    Definition repr := [ fun w => f_inv (f w) ].
                                         
    Lemma f_inv_inj: injective f_inv.
    Proof.
      move => x y.
      move: (xchooseP (f_surj x)) => /eqP {2}<-.
      move: (xchooseP (f_surj y)) => /eqP {2}<-.
      by rewrite /f_inv => ->.
    Qed.

    Lemma f_inv_invariant_rcons w a: f (rcons (f_inv (f w)) a) = f (rcons w a).
    Proof.
      apply ref.
      move => z.
      rewrite -2!cats1 -2!catA /=. pattern (a::z).
      assert (MH_rel L (f_inv (f w)) w).
        apply ref.
        by rewrite f_invK.
      exact: H.
    Qed.

    Lemma f_inv_invariant_L w: f_inv (f w) \in L <-> (w \in L).
    Proof.
      move: (ref (f_inv (f w)) w) => [H1 H2].
      rewrite f_invK in H1.
      move: (H1 (Logic.eq_refl _)) => H3.
      move: (H3 [::]).
      by rewrite 2!cats0.
    Qed.
      
    Definition state : finType := X.

    Definition s0 : state := f [::].

    Definition fin: pred state :=
      [pred x | f_inv x \in L ].
    
    Definition step x (a: char): X :=
      f (rcons (f_inv x) a).

    Definition MN_dfa := dfaI char state s0 fin step.

    
    Lemma MN_dfa_run_f w: last s0 (dfa_run' MN_dfa s0 w) = f w.
    Proof.
      move: w.
      apply: last_ind => [|w a IHw] //.
      rewrite -{1}cats1 dfa_run'_cat last_cat IHw /=.
      rewrite /step.
      exact: f_inv_invariant_rcons.
    Qed.
      
    Lemma MN_dfa_correct: L =1 dfa_lang MN_dfa.
    Proof.
      move => w.
      rewrite /dfa_lang /= -dfa_run_accepts MN_dfa_run_f in_simpl /=.
      apply/idP/idP;
      by rewrite f_inv_invariant_L.
    Qed.
      
  End ToDFA.

  Section ToMN.
    Variable A: dfa char.
    Definition f : Fin_eq_cls A := [ fun w => last (dfa_s0 A) (dfa_run A w) ].

    Lemma f_correct: MH_rel_ref _ (dfa_lang A) f.
    Proof.
      move => w1 w2.
      rewrite /f /=.
      split.
        move => H0 w3.
        rewrite /dfa_lang /= 2!in_simpl /= -2!dfa_run_accepts 2!dfa_run'_cat 2!last_cat.
        by rewrite H0.
      move => H0.
      move: (H0 [::]) => [].
      rewrite 2!cats0 2!in_simpl /dfa_lang /= -2!dfa_run_accepts. 
      move => H1 H2.
    Qed.
  End ToMN.
  
End MyhillNerode.
