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
    Definition MH_rel_ref (f: Fin_eq_cls) := forall w1 w2, f w1 = f w2 -> MH_rel w1 w2.
    
  End Relation.

  Section ToMN.
    Variable A: dfa char.
    Definition f : Fin_eq_cls A := [ fun w => last (dfa_s0 A) (dfa_run A w) ].

    Lemma f_correct: MH_rel_ref _ (dfa_lang A) f.
    Proof.
      move => w1 w2.
      rewrite /f /=.
      move => H0 w3.
      rewrite /dfa_lang /= 2!in_simpl /= -2!dfa_run_accepts 2!dfa_run'_cat 2!last_cat.
      by rewrite H0.
    Qed.
  End ToMN.
  
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
      
      
    Lemma MN_dfa_correct: L =1 dfa_lang MN_dfa.
    Proof.
      case/lastP.
        have H1: f [::] = f (f_inv s0).
          move: (xchooseP (f_surj s0)) => /eqP.
          by rewrite /s0 /f_inv.
        apply/idP/idP => /= H0.
          rewrite /fin /=.
          move: (ref _ _ H1 [::]).
          rewrite 2!cats0.
          case.
          by auto.
        move: (ref _ _ H1 [::]) => /=.
        rewrite cats0. case => _ H2.
        apply: H2.
        
  End ToDFA.
End MyhillNerode.
