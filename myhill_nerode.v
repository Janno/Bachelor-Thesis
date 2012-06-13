Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool finset choice.
Require Import automata misc regexp.
Require Import Program.Equality.

Require Import base.

Set Implicit Arguments.

Section MyhillNerode.
  Variable char: finType.
  Definition word:= word char.

  Section Relation.
    Variable X: finType.
    Variable L: language char.

    Definition MN w1 w2 := forall w3, w1++w3 \in L <-> w2++w3 \in L.

    (* We model finiteness of equivalence classes
     by functions to some finType. *)

    Definition Fin_eq_cls := word -> X.
    
    (* We define what it means to be a refinement
     of the MH relation: *)
    Definition MN_rel (f: Fin_eq_cls) := forall w1 w2, f w1 = f w2 <-> MN w1 w2.

    (* We also define refinements of the MN relation *)
    Definition MN_ref (f: Fin_eq_cls) := forall w1 w2, f w1 = f w2 -> MN w1 w2.
    
  End Relation.

  Section ToDFA.
    Variable L: language char.
    Variable X: finType.
    Variable f: Fin_eq_cls X.
    Variable ref: MN_rel L f.

    Definition surj (f: Fin_eq_cls X) := forall x, exists w, f(w) == x. 

    Variable f_surj: surj f.

    Definition f_inv := fun x => xchoose (f_surj x).

    Definition f_invK: cancel f_inv f.
    Proof.
      move => x.
      by move: (xchooseP (f_surj x)) => /eqP {2}<-.
    Qed.
    
    Definition repr := [ fun w => f_inv (f w) ].
                                         
    Lemma f_inv_invariant_rcons w a: f (rcons (f_inv (f w)) a) = f (rcons w a).
    Proof.
      apply ref.
      move => z.
      rewrite -2!cats1 -2!catA /=. pattern (a::z).
      assert (MN L (f_inv (f w)) w).
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

  Section Minimalization.
    Variable L: language char.
    Variable X: finType.
    Variable f: Fin_eq_cls X.
    Variable ref: MN_ref L f.
    Variable f_surj: surj f.

    Record MState :=
      mstateI {
          todo: seq (X*X);
          disjunct: {set X*X}
      }.

    Definition ext x y a := (f (rcons (f_inv f_surj x) a), f (rcons (f_inv f_surj y) a)). 
    Definition dist_ext1 x y a:= f (rcons (f_inv f_surj x) a) != f (rcons (f_inv f_surj y) a).

    Definition dist_extS x y w := f (cat (f_inv f_surj x) w) != f (cat (f_inv f_surj y) w).

    

    Definition propagate x y disjunct :=
      disjunct :|: [ set x' | (x,y) \in [ set ext (fst x') (snd x') a | a <- char ]  ].

    Lemma propagate_monotone (disjunct: {set X*X}) x y: disjunct \subset (propagate x y disjunct). 
    Proof.
      by apply: subsetUl.
    Qed.

    Fixpoint unnamed1 todo  :=
      match todo with
      | [::] => set0: {set X*X}
      | ((x,y)::todo) =>
          if x == y then unnamed1 todo else  
          match [ pick a | dist_ext1 x y a ] with
          | None => unnamed1 todo
          | Some a => let r := unnamed1 todo in
                        set1 (x,y) :|: r :|: (mu (propagate x y)) 
          end
      end.

    Section Correctness.
      Definition reflexive (S: {set X*X}):= forall x y, (x,y) \in S -> (y,x) \in S.
      
      Lemma unnamed1_final todo x y: (x,y) \in  unnamed1 todo -> exists a, dist_ext1 x y a. 
      Proof.
        elim: todo => [|[x' y'] todo IHtd].          
          by rewrite /= in_set0.
        rewrite /=.
        case H0: (x' == y') => //.
        case: pickP => [a H|H] //.
        rewrite /= 2!in_setU => /orP [] .
          move/orP => [] //.
          rewrite in_set1 => /eqP [] -> ->.
          by exists a.
                                          
        eapply mu_ind => [|s IHs].
          rewrite in_set0 //.
        rewrite in_setU => /orP [] //.
        rewrite in_set /=.
        move/imsetP => [] b _ [] H1 H2.
        exists b.
        by rewrite /dist_ext1 -H1 -H2 H0.
      Qed.

      Lemma unnamed1_dist_ext todo x y a: (x,y) \in todo -> dist_ext1 x y a -> (x,y) \in unnamed1 todo.
      Proof.
        elim: todo => [|[x' y'] todo IHtd] //.
        rewrite in_cons => /orP [].
          move/eqP => [] -> -> /=.
          case H0: (x' == y').
            rewrite /dist_ext1.
            move/eqP: H0 => ->.
            by rewrite eq_refl.
          case: pickP => [b H|H] H1.
            apply/setUP. left.
            apply/setUP. left.
            by rewrite in_set1 eq_refl.
          by rewrite H in H1.
        rewrite /=.
        case H0: (x' == y') => //.
        case: pickP => [b H|H] H1 H2.
          apply/setUP. left.
          apply/setUP. right.
          by apply: IHtd.
        by apply: IHtd.
      Qed.

    End Correctness.    

    
        
  End Minimalization.
  

  Section ToMN.
    Variable A: dfa char.
    Definition f : Fin_eq_cls A := [ fun w => last (dfa_s0 A) (dfa_run A w) ].

    Lemma f_correct: MN_rel _ (dfa_lang A) f.
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
