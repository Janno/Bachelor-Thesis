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

    Notation "f^-" := (f_inv f_surj).

    Lemma f_inv_ref_invariant_L w: f^- (f w) \in L = (w \in L).
    Proof.
      move: (@ref (f^- (f w)) w). 
      rewrite f_invK eq_refl => H1.
      move: (H1 is_true_true) => H3.
      move/eqP: (H3 [::]).
      by rewrite 2!cats0.
    Qed.
    
    Lemma f_inv_ref_invariant_L_rcons w a: f^- (f (rcons w a)) \in L = (rcons w a \in L).
    Proof.
      move: (@ref (f^- (f (rcons w a))) (rcons w a)). 
      rewrite f_invK eq_refl => H1.
      move: (H1 is_true_true) => H3.
      move/eqP: (H3 [::]).
      by rewrite 2!cats0.
    Qed.
    
    Lemma f_inv_ref_invariant_L_rcons2 x a: f^- (f (rcons (f^- x) a)) \in L = (rcons (f^- x) a \in L).
    Proof.
      by rewrite f_inv_ref_invariant_L_rcons.
    Qed.
    
    Lemma f_inv_ref_invariant_L_cat w1 w2: f^- (f (w1 ++ w2)) \in L = (w1 ++ w2 \in L).
    Proof.
      elim: w2 w1 => [|a w2 IHw2] w1.
        rewrite cats0. by apply: f_inv_ref_invariant_L.
      rewrite -(cat1s a w2).
      rewrite catA cats1.
      exact: IHw2.
    Qed.


    Definition ext x a := f (rcons (f^- x) a).
    Fixpoint ext_star x w :=
      match w with [::] =>  x | (a::w) => ext_star (ext x a) w end.

    Notation "ext*" := (ext_star).
    
    Definition pext x y a := (f (rcons (f^- x) a), f (rcons (f^- y) a)).
    Definition pextS x y w := (f (cat (f^- x) w), f (cat (f^- y) w)).
    Definition dist x y := (f^- x) \in L != ((f^- y) \in L).
    Definition dist_pext1 x y a:= dist (f (rcons (f^- x) a)) (f (rcons (f^- y) a)).
    Definition distinct0 :=
        [set x | dist (fst x) (snd x) ].

    Lemma dist_not_MN x y:  MN L (f^- x) (f^- y) -> dist x y -> False. 
    Proof.
      move => H.
      move: (H [::]).
      rewrite 2!cats0 /dist -topredE /=.
      by move => ->.
    Qed.       

    Lemma dist_pext1_not_MN x y a: MN L (f^- x) (f^- y) -> dist_pext1 x y a -> False. 
    Proof.
      move => H.
      move: (H [::a]).
      rewrite 2!cats1 /dist_pext1 /dist -2!f_inv_ref_invariant_L_rcons -topredE /=.
      by move => ->.
    Qed.       
    
    Definition unnamed distinct :=
        distinct0 :|: distinct :|: [set (x,y) | x <- X, y <- X, existsb a, pext x y a \in distinct ].            

    Definition distinct := mu unnamed.
    
    Notation "x ~= y" := ((x,y) \notin distinct) (at level 70, no associativity).

    Lemma unnamed_mono: mono unnamed.
    Proof.
    Admitted.
    
    Lemma unnamed_mono_in x y (s: {set _}):
      (x,y) \in s ->
      (x,y) \in (unnamed s).
    Proof.
      rewrite /unnamed.
        move => H. rewrite 2!in_set. apply/orP. left.
        apply/orP. by right.
    Qed.
    
    Lemma unnamed_mono_notin x y (s: {set _}):
      (x,y) \notin (unnamed s) ->
      (x,y) \notin s.
    Proof.
      rewrite /unnamed 3!in_set 2!negb_or.
      by move/andP => [/andP [] H1 H2 H3]. 
    Qed.

    Lemma distinct_pext x y (distinct: {set _}): (x,y) \in [set (x,y) | x <- X, y <- X, existsb a, pext x y a \in distinct ] -> exists a, pext x y a \in distinct.
    Proof.
      move/imset2P => [] x' y' _.
      rewrite in_set. move/andP => [] _ /existsP [] a H [] H1 H2; do 2!subst.
      by exists a.
    Qed.
    
    Lemma equiv0_refl x:
      (x,x) \notin distinct0.
    Proof. by rewrite in_set /dist eq_refl. Qed.


    Lemma equiv_refl x: x ~= x.
    Proof.
      rewrite /distinct.
      move: x.
      apply mu_ind => [|dist IHdist] x.
        by rewrite  in_set.
      rewrite /unnamed /= 2!in_setU 2!negb_or.
      rewrite (IHdist x) equiv0_refl /=.
      apply/imset2P => H. destruct H as [y z _ H1 H2].
      move: H2 H1 => [H3 H4]. do 2!subst.
      rewrite in_set => /existsP [] a.
      apply/negP. rewrite /pext.
      exact: IHdist.
    Qed.

    Lemma dist_sym x y: dist x y -> dist y x.
    Proof. by rewrite /dist eq_sym. Qed.
    Lemma not_dist_sym x y: ~~ dist x y -> ~~ dist y x.
    Proof. apply: contraL. move/dist_sym => H. by apply/negPn. Qed.
    
    Lemma equiv0_sym x y: (x,y) \notin distinct0 -> (y,x) \notin distinct0.
    Proof. by rewrite /distinct0 /dist 2!in_set eq_sym. Qed.
    
    Lemma distinct0_sym x y: (x,y) \in distinct0 -> (y,x) \in distinct0.
    Proof. by rewrite /distinct0 /dist 2!in_set eq_sym. Qed.

    Lemma equiv_sym x y:  x ~= y -> y ~= x.
    Proof.
      move: x y.  
      rewrite /distinct.
      apply mu_ind => [|s IHs] x y.
        by rewrite 2!in_set.
      rewrite /unnamed 6!in_set 4!negb_or.
      move/andP => [] /andP [] H1 H2 H3.
      rewrite not_dist_sym //= IHs //=.
      apply/negP. move/imset2P => [] x' y' _.
      rewrite in_set => /existsP [] a.
      move => H [] H4 H5; do 2!subst;
        move/negP: H3 => H3; apply: H3;
        rewrite mem_imset2 //=;
        rewrite in_set; apply/existsP; exists a.
      apply/negPn.
      move: H. apply: contraL.
      exact: IHs.
    Qed.

    Lemma equiv_trans x y z: (x,y) \notin distinct -> (y,z) \notin distinct -> (x,z) \notin distinct.
    Proof.
      move: x y z.  
      rewrite /distinct.
      apply mu_ind => [|s IHs] x y z.
        by rewrite 3!in_set.
      rewrite /unnamed.
      rewrite 6!in_set 4!negb_or.
      move/andP => [] /andP [] H1 H2 H3.
      move/andP => [] /andP [] H4 H5 H6.
      rewrite in_set. apply/negPn.
      rewrite in_set => /orP [/orP [H|H]|H]; move: H.
          move: H1 H4.
          rewrite /distinct0 in_set /= /dist.
          move => /negPn /eqP -> /negPn /eqP ->.
          by rewrite eq_refl.
        apply/negPn. move: H2 H5.
        exact: IHs.
      move/distinct_pext => [] a H.
      move/imset2P: H3 => []. apply/imset2P.
      rewrite mem_imset2 //= in_set.
      apply/existsP. exists a. apply: contraT => H7.
      move/imset2P: H6 => []. apply/imset2P.
      rewrite mem_imset2 //= in_set.
      apply/existsP. exists a. apply: contraT => H8.
      move: (IHs _ _ _ H7 H8).
      by rewrite H.
    Qed.
    
    Lemma equiv_L x y:
      x ~= y ->
      (f^- x) \in L = ((f^- y) \in L).
    Proof.
      rewrite /distinct muE -/distinct /unnamed.
      rewrite 2!in_setU.
      move /norP => [] /norP [].
      rewrite 3!in_set.
      rewrite /dist.
      by move/negPn/eqP.
      exact unnamed_mono.
    Qed.

    Lemma equiv_L_contra x y:
      (f^- x) \in L != ((f^- y) \in L) ->
      ~~ (x ~= y).
    Proof. apply: contraR. by move/negPn/equiv_L/eqP. Qed.
    
      
    Lemma equiv_L' x y s:
      (x,y) \notin unnamed s ->
      (f^- x) \in L = ((f^- y) \in L).
      rewrite 2!in_setU.
      move /norP => [].
      move /norP => [].
      rewrite in_set.
      rewrite /dist.
      by move/negPn/eqP.
    Qed.

    Lemma equiv_ext x y a:
      x ~= y ->
      ext x a ~= ext y a.
    Proof.
      pose (m := unnamed_mono).
      rewrite /distinct {1}muE -/distinct // /unnamed /= 2!in_set.
      apply: contraL => H.
      apply/negPn. apply/orP. right.
      rewrite mem_imset2 // in_set.
      apply/existsP.
      by exists a.
    Qed.
      
    Lemma L_equiv x y:
      (forall a, ext (f x) a ~= ext (f y) a) ->
      x \in L = (y \in L) ->
      (f x ~= f y).
    Proof.
      rewrite /distinct.
      move: x y.
      apply mu_ind => [|s IHs] x y H0 H1.
        by rewrite in_set.
      rewrite /unnamed.
      rewrite 3!in_set 2!negb_or IHs // /dist /=.
      rewrite 2!f_inv_ref_invariant_L H1 eq_refl //=.
      apply/negP.
      move/distinct_pext => [] a.
      apply/negP.
      apply/unnamed_mono_notin.
      exact: H0.
      move => a.
      apply/unnamed_mono_notin.
      exact: H0.
    Qed.
    
    Lemma L_ext_cat x u a:
      f u = x ->
      f^- (ext x a) \in L = (u ++ [:: a] \in L).
    Proof.
      rewrite -f_inv_ref_invariant_L_cat.
      move => H.
      move: (ref u (f^- x)). rewrite H f_invK eq_refl => H0.
      rewrite f_inv_ref_invariant_L.
      move/H0: is_true_true => H1.
      rewrite /ext f_inv_ref_invariant_L -cats1.
      by move/eqP: (H1 [::a]) => ->.
    Qed.
      

    Lemma L_ext_cat' x a:
    f^- (ext x a) \in L = (f^- x ++ [:: a] \in L).
    Proof. apply: L_ext_cat. by rewrite f_invK. Qed.


    (*
    Lemma equiv_cat_step1 x y a:
      x ~= y ->
      (ext x a) ~= f (f^- y ++ [:: a]).
    Proof.
      move => H.
      apply/L_equiv.
        move => b.
        apply/equiv_ext.
        
        
      (*move/(equiv_ext _ _ a): (H) => H3.*)
      move: x y a H.
      rewrite /distinct.
      apply mu_ind => [|s IHs] x y a H.
        by rewrite !in_set.
      move: H.
      rewrite /unnamed.
      rewrite 6!in_set 4!negb_or => /andP [] /andP [] H4 H5 H6.
      have H7: forall a, (ext x a, ext y a) \notin s.
        move => b.
        move: H6. apply: contraR.
        move/negPn => H.
        rewrite mem_imset2 //= in_set.
        apply/existsP.
        by exists b.
      rewrite IHs // andbT /= /dist.
      apply/andP. split.
        apply/negPn.
        admit.
      apply/negPn. move/distinct_pext => [] b.
      apply/negPn. rewrite /pext.
      admit.
    Qed.
      
    Lemma equiv_cat_step x y a w:
      x ~= y -> f (f^- (ext x a) ++ w) ~= f (f^- y ++ a::w).
    Proof.
      move: w x y a.
      apply: last_ind => [|b w IHw] x y a.
        rewrite cats0 f_invK.
        exact: equiv_cat_step1.

      elim: w x y a => [|b w IHw] x y a.
        rewrite cats0 f_invK.
        exact: equiv_cat_step1.
      move/(IHw _ _ a).
      
      
        
      
        
    
    Lemma equiv_cat x w: ext* x w ~= f (f^- x ++ w).
    Proof.
      elim: w x => [|a w IHw] x.
        by rewrite /= cats0 f_invK equiv_refl.
      simpl.
      apply: equiv_trans.
      eapply IHw.
    *)  
      
    Lemma distinct_final x y:
      (x,y) \in distinct ->
      exists w, (f^- x) ++ w \in L != ((f^- y) ++ w \in L). 
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
      move/existsP => [] a H3 [] H4 H5. move: H3.
      rewrite in_set => /orP [H3|H3]; subst.
        exists [::a]. move: H3. by rewrite /pext /distinct0 in_set /Minimalization.dist /= 2!cats1 -2!f_inv_ref_invariant_L_rcons.

      move: (IHdist (pext x1 y1 a).1 (pext x1 y1 a).2 H3) => [w].
      rewrite /pext /= => H4.
      exists (a::w).
        rewrite -cat1s.
        rewrite -f_inv_ref_invariant_L_cat.
        rewrite 2!catA 2!cats1.
        rewrite f_inv_ref_invariant_L_cat.
      have/eqP: (f (f^- (f (rcons (f^- x1) a))) = f (rcons (f^- x1) a)).
        by apply: f_invK.
      move/ref => H5.
      move/eqP: (H5 w) => <-.
      have/eqP: (f (f^- (f (rcons (f^- y1) a))) = f (rcons (f^- y1) a)).
        by apply: f_invK.
      move/ref => H6.
      by move/eqP: (H6 w) => <-.
    Qed.
      

    Lemma distinct_final' x y: (x, y) \in distinct -> ~ MN L (f^- x) (f^- y).
    Proof.
      move => /distinct_final [w H] H0.
      move/eqP: (H0 w).
      move/eqP => H1. move: H.
      by rewrite H1.
    Qed.

    Lemma distinct_notin_pextS x y w:
      (x,y) \notin distinct ->
      pextS x y w \notin distinct.
    Proof.
      elim: w x y => [|a w IHw] x y H.
        by rewrite /pextS 2!cats0 2!f_invK.
      move/(distinct_notin_pext _ _ a): (H).
      move/IHw.
      rewrite /pext /pextS.
    Admitted.
      
      
    Lemma distinct_final'' x y:
      (x,y) \notin distinct ->
      MN L (f^- x) (f^- y).
    Proof.
      move => H w.
      rewrite -(f_inv_ref_invariant_L_cat [::] (f^- x ++ w)).
      rewrite -(f_inv_ref_invariant_L_cat [::] (f^- y ++ w)).
      move/(distinct_notin_pextS _ _ w): H.
      by rewrite /pextS => /distinct_notin /= /eqP.
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
      move/equiv_sym in H.
        by apply: equiv_trans.
      by apply: equiv_trans.
    Qed.
        
    Lemma in_dist_repr x y: y \in dist_repr x = ~~ existsb a, dist_pext1 x y a.
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
        apply: equiv_sym.
        apply: equiv_trans.
          eapply equiv_sym.
          eassumption.
        by [].
      apply: equiv_sym.
      apply: equiv_trans.
        eapply equiv_sym.
        eassumption.
      apply: equiv_sym.
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
        move/(distinct_notin_pextS _ _ z): H.
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
        move/(distinct_notin_pextS _ _ z): H.
        move/(distinct_notin_pext _ _ a).
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
