Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool finset choice.
Require Import automata misc regexp.
Require Import base.

Set Implicit Arguments.

Section MyhillNerode.
  Variable char: finType.
  Definition word:= word char.

  Section Relation.
    Variable X: finType.
    Variable L: language char.

    Definition MN w1 w2 := forall w3, w1++w3 \in L == (w2++w3 \in L).

    (* We model finiteness of equivalence classes
     by functions to some finType. *)

    Definition Fin_eq_cls := word -> X.
    
    (* We define what it means to be a refinement
     of the MH relation: *)
    Definition MN_rel (f: Fin_eq_cls) := forall w1 w2, f w1 == f w2 <-> MN w1 w2.

    (* We also define refinements of the MN relation *)
    Definition MN_ref (f: Fin_eq_cls) := forall w1 w2, f w1 == f w2 -> MN w1 w2.
    
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
                                         
    Lemma f_inv_invariant_rcons w a: f (rcons (f_inv (f w)) a) == f (rcons w a).
    Proof.
      apply ref.
      move => z.
      rewrite -2!cats1 -2!catA /=. pattern (a::z).
      assert (MN L (f_inv (f w)) w).
        apply ref.
        by rewrite f_invK.
      exact: H.
    Qed.

    Lemma f_inv_invariant_L w: f_inv (f w) \in L == (w \in L).
    Proof.
      move: (ref (f_inv (f w)) w) => [H1 H2].
      rewrite f_invK in H1.
      move: H1. rewrite eq_refl => H3.
      move: (H3 is_true_true [::]).
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
      apply/eqP. exact: f_inv_invariant_rcons.
    Qed.
      
    Lemma MN_dfa_correct: L =1 dfa_lang MN_dfa.
    Proof.
      move => w.
      rewrite /dfa_lang /= -dfa_run_accepts MN_dfa_run_f in_simpl /=.
      apply/eqP.
      move: (f_inv_invariant_L w).
      by rewrite eq_sym.
    Qed.
      
  End ToDFA.

  Section Minimalization.
    Variable L: language char.
    Variable X: finType.
    Variable f: Fin_eq_cls X.
    Variable ref: MN_ref L f.
    Variable f_surj: surj f.

    Notation "f^-1" := (f_inv f_surj).

    Definition ext x y a := (f (rcons (f^-1 x) a), f (rcons (f^-1 y) a)).
    Definition extS x y w := (f (cat (f^-1 x) w), f (cat (f^-1 y) w)).
    Definition dist x y := (f^-1 x) \in L != ((f^-1 y) \in L).
    Definition dist_ext1 x y a:= dist (f (rcons (f^-1 x) a)) (f (rcons (f^-1 y) a)).
    Definition distinct0 :=
        [set x | dist (fst x) (snd x) ].
    
    Definition unnamed distinct :=
        distinct0 :|: distinct :|: [set (x,y) | x <- X, y <- X, existsb a, ext x y a \in distinct]
    .            

    Definition distinct := mu unnamed.

    Lemma unnamed_mono: mono unnamed.
    Proof.
    Admitted.
        
        
    Lemma f_inv_ref_invariant_L w: f^-1 (f w) \in L = (w \in L).
    Proof.
      move: (@ref (f^-1 (f w)) w). 
      rewrite f_invK eq_refl => H1.
      move: (H1 is_true_true) => H3.
      move/eqP: (H3 [::]).
      by rewrite 2!cats0.
    Qed.
    
    Lemma f_inv_ref_invariant_L_rcons w a: f^-1 (f (rcons w a)) \in L = (rcons w a \in L).
    Proof.
      move: (@ref (f^-1 (f (rcons w a))) (rcons w a)). 
      rewrite f_invK eq_refl => H1.
      move: (H1 is_true_true) => H3.
      move/eqP: (H3 [::]).
      by rewrite 2!cats0.
    Qed.
    
    Lemma f_inv_ref_invariant_L_rcons2 x a: f^-1 (f (rcons (f^-1 x) a)) \in L = (rcons (f^-1 x) a \in L).
    Proof.
      by rewrite f_inv_ref_invariant_L_rcons.
    Qed.
    
    Lemma f_inv_ref_invariant_L_cat w1 w2: f^-1 (f (w1 ++ w2)) \in L = (w1 ++ w2 \in L).
    Proof.
      elim: w2 w1 => [|a w2 IHw2] w1.
        rewrite cats0. by apply: f_inv_ref_invariant_L.
      rewrite -(cat1s a w2).
      rewrite catA cats1.
      exact: IHw2.
    Qed.

    Lemma dist_not_MN x y:  MN L (f^-1 x) (f^-1 y) -> dist x y -> False. 
    Proof.
      move => H.
      move: (H [::]).
      rewrite 2!cats0 /dist -topredE /=.
      by move => ->.
    Qed.       

    Lemma dist_ext1_not_MN x y a: MN L (f^-1 x) (f^-1 y) -> dist_ext1 x y a -> False. 
    Proof.
      move => H.
      move: (H [::a]).
      rewrite 2!cats1 /dist_ext1 /dist -2!f_inv_ref_invariant_L_rcons -topredE /=.
      by move => ->.
    Qed.       
    
    Lemma distinct_final x y:
      (x,y) \in distinct ->
      exists w, (f^-1 x) ++ w \in L != ((f^-1 y) ++ w \in L). 
    Proof.
      rewrite /distinct.
      move: x y.
      apply mu_ind => [|dist IHdist] x y.
        by rewrite in_set.
      rewrite /unnamed.
      rewrite 2!in_setU => /orP [].
        move/orP => [].
          rewrite /distinct0 /Minimalization.dist in_set /=.
          move => H.
          exists [::]. by rewrite 2!cats0.
        exact: IHdist.
      move/imset2P => [] x1 y1 _.
      rewrite in_set => /andP [] _.
      move/existsP => [] a H3 [] H4 H5.
      subst.
      move: (IHdist (ext x1 y1 a).1 (ext x1 y1 a).2 H3) => [w].
      rewrite /ext /= => H4.
      exists (a::w).
        rewrite -cat1s.
        rewrite -f_inv_ref_invariant_L_cat.
        rewrite 2!catA 2!cats1.
        rewrite f_inv_ref_invariant_L_cat.
      have/eqP: (f (f^-1 (f (rcons (f^-1 x1) a))) = f (rcons (f^-1 x1) a)).
        by apply: f_invK.
      move/ref => H5.
      move/eqP: (H5 w) => <-.
      have/eqP: (f (f^-1 (f (rcons (f^-1 y1) a))) = f (rcons (f^-1 y1) a)).
        by apply: f_invK.
      move/ref => H6.
      by move/eqP: (H6 w) => <-.
    Qed.

    Lemma distinct_dist_extS x y:
      (x,y) \in distinct ->
      forall a, ext x y a \in distinct.
    Proof.
      rewrite /distinct.
      apply mu_ind => [|s IHs].
        by rewrite in_set.
      rewrite /unnamed 3!in_set.
      move/orP => [/orP [H|H]|H] a.
        rewrite 3!in_set /distinct0.
      
    Lemma distinct_mono x y (s: {set _}):
      (x,y) \in s ->
      (x,y) \in (unnamed s).
    Proof.
      rewrite /unnamed.
        move => H. rewrite 2!in_set. apply/orP. left.
        apply/orP. by right.
    Qed.

    Lemma distinct_mono_not x y (s: {set _}):
      (x,y) \notin (unnamed s) ->
      (x,y) \notin s.
    Proof.
      rewrite /unnamed 3!in_set 2!negb_or.
      by move/andP => [/andP [] H1 H2 H3]. 
    Qed.

    Lemma distinct_notin x y:
      (x,y) \notin distinct ->
      (f^-1 x) \in L = ((f^-1 y) \in L).
    Proof.
      rewrite /distinct muE -/distinct /unnamed.
      rewrite 2!in_setU.
      move /norP => [].
      move /norP => [].
      rewrite 3!in_set.
      rewrite /dist.
      by move/negPn/eqP.
      exact unnamed_mono.
    Qed.
    
    Lemma distinct_final' x y: (x, y) \in distinct -> ~ MN L (f^-1 x) (f^-1 y).
    Proof.
      move => /distinct_final [w H] H0.
      move/eqP: (H0 w).
      move/eqP => H1. move: H.
      by rewrite H1.
    Qed.

    Lemma distinct_notin_ext x y a:
      (x,y) \notin distinct ->
      ext x y a \notin distinct.
    Proof.
      pose (m := unnamed_mono).
      rewrite /distinct {1}muE -/distinct // /unnamed.
      rewrite 2!in_set.
      apply: contraL => H.
      apply/negPn.
      apply/orP. right.
      rewrite mem_imset2 // in_set.
      apply/andP; split => //.
      apply/existsP. by exists a.
    Qed.


    Lemma distinct_notin_extS x y w:
      (x,y) \notin distinct ->
      extS x y w \notin distinct.
    Proof.
      elim: w x y => [|a w IHw] x y H.
        by rewrite /extS 2!cats0 2!f_invK.
      move/(distinct_notin_ext _ _ a): (H).
      move/IHw.
      rewrite /ext /extS.
    Admitted.
      
      
    Lemma distinct_final'' x y:
      (x,y) \notin distinct ->
      MN L (f^-1 x) (f^-1 y).
    Proof.
      move => H w.
      rewrite -(f_inv_ref_invariant_L_cat [::] (f^-1 x ++ w)).
      rewrite -(f_inv_ref_invariant_L_cat [::] (f^-1 y ++ w)).
      move/(distinct_notin_extS _ _ w): H.
      by rewrite /extS => /distinct_notin /= /eqP.
    Qed.

    Lemma distinct0_not_refl x:
      (x,x) \notin distinct0.
    Proof.
      by rewrite in_set /dist eq_refl.
    Qed.
      
    Lemma distinct_not_refl x:
       (x,x) \notin distinct.
    Proof.
      rewrite /distinct.
      move: x.
      apply mu_ind => [|dist IHdist] x.
        by rewrite  in_set.
      rewrite /unnamed /=.
      rewrite in_setU.
      rewrite in_setU 2!negb_or.
      rewrite (IHdist x) distinct0_not_refl /=.
      apply/imset2P => H. destruct H as [y z _ H1 H2].
      move: H2 H1 => [H3 H4]. do 2!subst.
      rewrite in_set => /existsP [] a.
      apply/negP. exact: IHdist.
    Qed.

      
    Lemma distinct_trans_not x y z: (x,y) \notin distinct -> (y,z) \notin distinct -> (x,z) \notin distinct.
    Proof.
      move => H1 H2.
      apply/negP => /distinct_final [w /negP H3].
      apply: H3.
      move/distinct_notin: (distinct_notin_extS _ _ w H1) => H3.      
      move/distinct_notin: (distinct_notin_extS _ _ w H2) => H4.      
      rewrite -(f_inv_ref_invariant_L_cat (f^-1 x)).
      rewrite -(f_inv_ref_invariant_L_cat (f^-1 z)).
      by rewrite H3 H4 eq_refl.
    Qed.

    Lemma distinct_sym_not x y: (x,y) \notin distinct -> (y,x) \notin distinct.
      move => H1.
      apply/negP => /distinct_final [w /negP H3].
      apply: H3.
      move/distinct_notin: (distinct_notin_extS _ _ w H1) => H3.      
      rewrite -(f_inv_ref_invariant_L_cat (f^-1 x)).
      rewrite -(f_inv_ref_invariant_L_cat (f^-1 y)).
      by rewrite H3 eq_refl.
    Qed.
    
    
    Definition dist_repr := [ fun x => [set y | (x,y) \notin distinct] ].

    Lemma dist_repr_refl x : x \in dist_repr x.
    Proof.
      by rewrite in_set distinct_not_refl.
    Qed.
    
    Lemma dist_equiv x y: (x, y) \notin distinct -> dist_repr x = dist_repr y.
    Proof.
      move => H /=.
      apply/setP => z.
      rewrite 2!in_set.
      apply/idP/idP.
      move/distinct_sym_not in H.
        by apply: distinct_trans_not.
      by apply: distinct_trans_not.
    Qed.
        
    Lemma in_dist_repr x y: y \in dist_repr x = ~~ existsb a, dist_ext1 x y a.
    Proof.
      apply/idP/idP.
        rewrite in_set.
        apply: contraL.
        move/existsP => [] a H.
        rewrite /distinct in_set. apply/negPn.
        admit.
      rewrite in_set.
      apply: contraL.
      move/distinct_final' => H.
      apply/negPn.
      apply/existsP.
      admit.
    Qed.
      
    Definition X_min := map dist_repr (enum X).
    Definition X_min_finMixin := seq_sub_finMixin X_min.

    Canonical Structure X_min_finType := FinType _ X_min_finMixin.

    Lemma dist_repr_in_X_min x: dist_repr x \in X_min.
    Proof.
      apply/mapP.
      exists x => //.
      by rewrite mem_enum.
    Qed.

    Definition f_min: Fin_eq_cls X_min_finType :=
      [ fun w => SeqSub _ (dist_repr_in_X_min (f w)) ].

    Lemma f_min_eq_distinct x y: f_min x = f_min y -> (f x, f y) \notin distinct.
    Proof.
      move => [] /= /setP H1.
      move: (H1 (f y)).
      by rewrite dist_repr_refl in_set => ->.
    Qed.                                            

    Lemma f_min_distinct_eq x y: (f x, f y) \notin distinct -> f_min x == f_min y.
    Proof.
      move => H.
      rewrite /f_min /=.
      change ([set y0 | (f x, y0) \notin distinct] == [set y0 | (f y, y0) \notin distinct]).
      apply/eqP.
      apply/setP => z.
      rewrite 2!in_set.
      apply/idP/idP => H0.
        apply: distinct_sym_not.
        apply: distinct_trans_not.
          eapply distinct_sym_not.
          eassumption.
        by [].
      apply: distinct_sym_not.
      apply: distinct_trans_not.
        eapply distinct_sym_not.
        eassumption.
      apply: distinct_sym_not.
      by [].
    Qed.
      
      
    Lemma f_min_MN_rel: MN_rel L f_min.
    Proof.
      move => x y.
      split.
        
        move/eqP/f_min_eq_distinct => H z.
        apply distinct_notin.

        move/eqP/f_min_eq_distinct => H.

        (*
        move/(distinct_notin_extS _ _ z): H.
        move/distinct_notin => H.
        rewrite -(f_inv_ref_invariant_L_cat [::] (x++z)).
        rewrite -(f_inv_ref_invariant_L_cat [::] (y++z)).
        move/eqP: H => /=.
        *)

        apply: last_ind => [|z a IHz].
          rewrite 2!cats0.
          rewrite -(f_inv_ref_invariant_L_cat [::] x).
          rewrite -(f_inv_ref_invariant_L_cat [::] y).
          by move/distinct_notin/eqP: H => /=.
        rewrite -cats1 catA.
        rewrite -f_inv_ref_invariant_L_cat.
        move/(distinct_notin_extS _ _ z): H.
        move/(distinct_notin_ext _ _ a).
        move/distinct_notin.
        rewrite cats1.
        
          
      move => H /=.
      have: (dist_repr (f x) = dist_repr (f y)).
      
      apply/eqP.
        rewrite /dist_repr.
        
        rewrite distinct_correct.
        
        rewrite eqEsubset.
        
        
      
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
