Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool finset choice.
Require Import automata misc regexp.
Require Import base.

Set Implicit Arguments.
Import Prenex Implicits.



Lemma nand3P (b1 b2 b3: bool):
  reflect (~[\/ b1, b2 | b3]) [&& ~~ b1, ~~ b2 & ~~ b3].
Proof.
  apply: iffP.
      apply and3P.
    by move/and3P/andP => [] /negP H0 /andP [] /negP H1 /negP H2 [].
  move => H0. constructor; apply/negP => H1; apply H0; firstorder.
Qed.

Section MyhillNerode.
  Variable char: finType.
  Definition word:= word char.

  Section Relations.
    Variable L: language char.


    (* We model finiteness of equivalence classes
     by functions to some finType. *)

    Definition surjective {X: finType} {Y} (f: Y -> X) := forall x, exists w, f w == x.
    
    Record Fin_Eq_Cls :=
      {
        fin_type : finType;
        fin_f :> word -> fin_type;
        fin_surjective : surjective fin_f
      }.

    Section Inversion. 

      Variable f: Fin_Eq_Cls.
    
      Definition inv (f: Fin_Eq_Cls) x :=
        xchoose (fin_surjective f x).

      Lemma invK: cancel (inv f) f.
      Proof. move => x. by move: (xchooseP (fin_surjective f x)) => /eqP {2}<-. Qed.

      (* Needed? *)
      Lemma eq_inv x: x = (f (inv f x)).
      Proof. by rewrite invK. Qed.
      
      Definition repr := inv f \o f.

    End Inversion.

    Section Myhill.

      Definition right_congruent {X} (f: word -> X) :=
        forall u v a, f u = f v -> f (rcons u a) = f (rcons v a).

      Definition refining {X} (f: word -> X) :=
        forall u v, f u = f v -> u \in L = (v \in L).
        
      Record Myhill_Rel :=
        {
          myhill_func :> Fin_Eq_Cls; 
          myhill_congruent: right_congruent myhill_func;
          myhill_refining: refining myhill_func
        }.
        
    End Myhill.

    
    Section Nerode.

      Definition equal_suffix u v :=
        forall w, u++w \in L = (v++w \in L).

      Definition equiv_suffix {X} (f: word -> X) :=
        forall u v, f u = f v <-> equal_suffix u v.
      
      Record Nerode_Rel :=
        {
          nerode_func :> Fin_Eq_Cls;
          nerode_equiv: equiv_suffix nerode_func
        }.

    End Nerode.

    
    Section Nerode_Facts.

      Variable f: Nerode_Rel.

      Lemma inv_rcons w a: f (rcons (inv f (f w)) a) = f (rcons w a).
      Proof.
        apply (f.(nerode_equiv)) => u.
        rewrite -2!cats1 -2!catA /=. 
        apply f.(nerode_equiv).
        by rewrite invK.
      Qed.
      
    End Nerode_Facts.
    

    Section Weak_Nerode.
      
      Definition imply_suffix {X} (f: word -> X) :=
        forall u v, f u = f v -> equal_suffix u v.
      
      Record Weak_Nerode_Rel :=
        {
          weak_nerode_func :> Fin_Eq_Cls;
          weak_nerode_imply: imply_suffix weak_nerode_func
        }.

    End Weak_Nerode.

    Section Weak_Nerode_Facts.

      Variable f: Weak_Nerode_Rel.

      Lemma inv_mem_L_cat u v: inv f (f u) ++ v \in L = (u ++ v \in L).
      Proof.
        erewrite f.(weak_nerode_imply).
          reflexivity.
        by rewrite invK.
      Qed.

      Lemma inv_mem_L w: inv f (f w) \in L = (w \in L).
      Proof.
        rewrite -(cats0 (inv f (f w))) -{2}(cats0 w).
        exact: inv_mem_L_cat.
      Qed.

    End Weak_Nerode_Facts.


    Definition nerode_weak_nerode (f: Nerode_Rel): Weak_Nerode_Rel :=
      {| weak_nerode_imply := fun u v H => match nerode_equiv f u v with conj H0 H1 => H0 H end |}.
    
    Coercion nerode_weak_nerode : Nerode_Rel >-> Weak_Nerode_Rel.

    
      
  End Relations.
  
  Section Myhill_Weak_Nerode.

    Variable L: language char.
    Variable f: Myhill_Rel L.

    Lemma myhill_closure: imply_suffix L f.
    Proof.
      move => u v Huv w.
      elim: w u v Huv => [|a w IHw] u v Huv.
        rewrite 2!cats0.
        exact: f.(myhill_refining).
      rewrite -cat1s 2!catA 2!cats1.
      apply: IHw.
      exact: f.(myhill_congruent).
    Qed.

    Definition myhill_to_weak_nerode: Weak_Nerode_Rel L :=
      {| weak_nerode_imply := myhill_closure |}.
    
  End Myhill_Weak_Nerode.
  

  Section Nerode_To_DFA.
    Variable L: language char.
    Variable f: Nerode_Rel L.

    Definition state : finType := f.(fin_type).

    Definition s0 : state := f [::].

    Definition fin: pred state :=
      [pred x | inv f x \in L ].
    
    Definition step x (a: char) :=
      f (rcons (inv f x) a).

    Definition nerode_to_dfa := {|dfa_s := s0; dfa_fin := fin; dfa_step := step |}.
    
    Lemma nerode_to_dfa_run_f w: last s0 (dfa_run' nerode_to_dfa s0 w) = f w.
    Proof.
      move: w.
      apply: last_ind => [|w a IHw] //.
      rewrite -{1}cats1 dfa_run'_cat last_cat IHw /=.
      rewrite /step.
      exact: inv_rcons.
    Qed.
      
    Lemma nerode_to_dfa_correct: L =i dfa_lang nerode_to_dfa.
    Proof.
      move => w.
      rewrite /dfa_lang /= -dfa_run_accept nerode_to_dfa_run_f in_simpl /=.
      by rewrite (inv_mem_L f w).
    Qed.
      
  End Nerode_To_DFA.

  Section Minimalization.
    Variable L: language char.
    Variable f: Weak_Nerode_Rel L.
    Definition X := f.(fin_type).

    Definition ext := [ fun x a => f ((inv f x) ++ [::a]) ].
    
    Definition pext := [ fun x y => [ fun a => (ext x a, ext y a) ] ].

    Definition distinguishable := [ fun x y => (inv f x) \in L != ((inv f y) \in L) ].

    Definition distinct0 := [set x | distinguishable x.1 x.2 ].

    Definition distinctS (distinct: {set X*X}) :=
      [set  (x,y) | x in X, y in X & [ exists a, pext x y a \in distinct ] ].

    Lemma distinctSP (distinct: {set X*X}) x y:
      reflect (exists a, pext x y a \in distinct)
              ((x,y) \in distinctS distinct).
    Proof.
      apply: iffP. apply idP.
        move/imset2P => [] x' y' _. 
        rewrite !inE /= => /existsP [] a.
        move => H [H1 H2]. subst.
        by eauto.
      move => [a H].
      apply mem_imset2; first by done.
      rewrite !inE /=. apply/existsP.
      exists a. exact H.
    Qed.

    Lemma distinctSnegP (distinct: {set X*X}) x y:
      reflect (forall a, pext x y a \notin distinct)
              ((x,y) \notin distinctS distinct).
    Proof.
      apply: introP.
        move/distinctSP => H1 a.
        apply/negP => H2. by eauto.
      move/negbTE/distinctSP => [a H1] H2.
      absurd (pext x y a \in distinct) => //.
      by apply/negP.
    Qed.
    
    Definition unnamed distinct :=
        distinct0 :|: distinct :|: (distinctS distinct).

    Lemma unnamedP (distinct: {set X*X}) x:
      reflect ([\/ x \in distinct0, x \in distinct | x \in distinctS distinct])
              (x \in unnamed distinct).
    Proof.
      rewrite /unnamed !inE.
      apply: introP.
        move/orP => [/orP [] |]; eauto using or3.
      by move/norP => [] /norP [] /negbTE -> /negbTE -> /negbTE -> [].
    Qed.
      
    Definition distinct := mu unnamed.

    Notation "x ~!= y" := ((x,y) \in distinct) (at level 70, no associativity).
    Notation "x ~= y" := ((x,y) \notin distinct) (at level 70, no associativity).

    Lemma unnamed_mono: mono unnamed.
    Proof.
      move => s t.
      rewrite unlock /= => /existsP H.
      apply/existsP => [] [] x /andP [].
      move/unnamedP/nand3P/and3P => [].
      move => /negbTE /negP H0 H1 H2 /unnamedP [] H3;
        first by done.
        apply: H. exists x.
        by rewrite !inE H1 H3.
      destruct x. move/distinctSP: H3 => [a H4].
      move/distinctSP: H2 => H2. apply: H.
      eexists. rewrite /=. apply/andP. split;
        last by eassumption.
      apply/negP => H5. by eauto.
    Qed.
    
    Lemma unnamed_mono_in x y (s: {set _}):
      (x,y) \in s ->
      (x,y) \in (unnamed s).
    Proof.
      rewrite /unnamed.
        move => H. rewrite 2!in_set. apply/orP. left.
        apply/orP. by right.
    Qed.

    Lemma equiv0_refl x:
      (x,x) \notin distinct0.
    Proof. by rewrite in_set /= eq_refl. Qed.

    Lemma equiv_refl x: x ~= x.
    Proof.
      rewrite /distinct. move: x.
      apply mu_ind => [|dist IHdist] x.
        by rewrite  in_set.
      apply/unnamedP/nand3P/and3P; econstructor => //;
        first by exact: equiv0_refl.
      apply/distinctSnegP => a.
      exact: IHdist.
    Qed.

    Lemma dist_sym x y: distinguishable x y -> distinguishable y x.
    Proof. by rewrite /= eq_sym. Qed.

    Lemma not_dist_sym x y: ~~ distinguishable x y -> ~~ distinguishable y x.
    Proof. apply: contraL. move/dist_sym => H. by apply/negPn. Qed.
    
    Lemma equiv0_sym x y: (x,y) \notin distinct0 -> (y,x) \notin distinct0.
    Proof. by rewrite /distinct0 /= 2!in_set eq_sym. Qed.
    
    Lemma distinct0_sym x y: (x,y) \in distinct0 -> (y,x) \in distinct0.
    Proof. by rewrite /distinct0 /= 2!in_set eq_sym. Qed.

    Lemma equiv_sym x y:  x ~= y -> y ~= x.
    Proof.
      move: x y.  
      rewrite /distinct.
      apply mu_ind => [|s IHs] x y.
        by rewrite 2!in_set.
      move/unnamedP/nand3P/and3P => [] H0 H1 H2.
      apply/unnamedP. apply/nand3P. apply/and3P.
      constructor.
          exact: equiv0_sym.
        exact: IHs.
      apply/distinctSnegP => a. 
      move/distinctSnegP in H2. 
      apply: IHs. exact: H2.
    Qed.

    Lemma equiv_trans x y z: x ~= y -> y ~= z -> x ~= z.
    Proof.
      move: x y z.  
      rewrite /distinct.
      apply mu_ind => [|s IHs] x y z.
        by rewrite 3!in_set.
      move/unnamedP/nand3P/and3P => [] H1 H2 /distinctSnegP H3.
      move/unnamedP/nand3P/and3P => [] H4 H5 /distinctSnegP H6.
      apply/unnamedP. apply/nand3P. apply/and3P.
      constructor.
          move: H1 H4.
          rewrite /distinct0 !inE /= => /negbNE.
          by move => /eqP ->. 
        by apply: IHs; eassumption.
      apply/distinctSnegP => a.
      apply: IHs.
        by eapply H3.
      exact: H6.
    Qed.


    Lemma equiv_equal_suffix u v: f u ~= f v -> equal_suffix L u v.
    Proof.
      move => H w. apply/eqP. move: H.
      apply: contraR.
      elim: w u v => [|a w IHw] u v.
        rewrite 2!cats0.
        rewrite /distinct muE -/distinct /unnamed => H;
          last by exact: unnamed_mono.
        by rewrite /distinct0  /= 3!in_set 2!inv_mem_L H.
      move => H.
      rewrite /distinct muE -/distinct;
        last by exact: unnamed_mono.
      apply/unnamedP. apply: Or33.
      apply/distinctSP. exists a.
      apply: IHw.
      by rewrite -2!catA cat1s 2!(inv_mem_L_cat f).
    Qed.
   
    Lemma distinct_not_equal_suffix' u v:
      f u ~!= f v ->
      exists w, u ++ w \in L != (v ++ w \in L). 
    Proof.
      rewrite /distinct.
      move: u v.
      apply mu_ind => [|dist IHdist] u v.
        by rewrite in_set.
      move/unnamedP => [].
          rewrite /distinct0 in_set /= => H.
          exists [::]. rewrite 2!cats0.
          by rewrite 2!inv_mem_L in H.
        exact: IHdist.
      move/distinctSP => [a] /IHdist [w].
      rewrite -2!catA !cat1s !inv_mem_L_cat.
      by eauto.
    Qed.
      
    Lemma distinct_not_equal_suffix u v: f u ~!= f v -> ~ equal_suffix L u v.
    Proof.
      move => /distinct_not_equal_suffix' [w H] H0.
      move: (H0 w).
      move => H1. move/eqP: H.
      by rewrite H1.
    Qed.
      
    
    Definition dist_repr := fun x => [set y | x ~= y].

    Lemma dist_repr_refl x : x \in dist_repr x.
    Proof. by rewrite in_set equiv_refl. Qed.
    
    Definition X_min := map dist_repr (enum f.(fin_type)).

    Lemma dist_repr_in_X_min x: dist_repr x \in X_min.
    Proof. apply/mapP. exists x => //. by rewrite mem_enum. Qed.

    Definition f_min := fun w => SeqSub _ (dist_repr_in_X_min (f w)).
      
    Lemma f_min_eq_distinct x y: f_min x = f_min y -> f x ~= f y.
    Proof.
      move => [] /= /setP H1. move: (H1 (f y)).
      by rewrite dist_repr_refl in_set => ->.
    Qed.                                            

    Lemma f_min_distinct_eq x y: f x ~= f y -> f_min x = f_min y.
    Proof.
      move => H.
      rewrite /f_min /=.
      apply/eqP.
      change ([set y0 | (f x, y0) \notin distinct] == [set y0 | (f y, y0) \notin distinct]).
      apply/eqP.
      apply/setP => z.
      rewrite 2!in_set.
      apply/idP/idP => H0.
        apply: equiv_sym. apply: equiv_trans. eapply equiv_sym.
          eassumption.
        by [].
      apply: equiv_sym.
      apply: equiv_trans.
        eapply equiv_sym.
        eassumption.
      apply: equiv_sym.
      by [].
    Qed.
      
      
    Lemma f_min_correct: equiv_suffix L f_min.
    Proof.
      move => u v.
      split.
        move/f_min_eq_distinct.
        exact: equiv_equal_suffix.
     move => H. 
     apply f_min_distinct_eq.
     by apply/negP => /distinct_not_equal_suffix.
    Qed.                                                  

    Lemma f_min_surjective: surjective f_min.
    Proof.
      move => [x Hx].
      move/mapP: (Hx) => [y Hy Hxy].
      exists (inv f y).
      rewrite /f_min.
      change (dist_repr (f (inv f y)) == x).
      by rewrite Hxy invK.
    Qed.

    Definition weak_nerode_to_nerode: Nerode_Rel L :=
      {|
        nerode_func := {| fin_surjective := f_min_surjective |};
        nerode_equiv := f_min_correct
      |}.

  End Minimalization.
  

  Section DFA_To_Nerode.
    Variable A: dfa char.
    Definition A' := dfa_connected A.
    Definition f := fun w => last (dfa_s A') (dfa_run A' w).
    
    Definition f_surjective: surjective f.
    Proof.
      move => x.
      move/dfa_connected_repr: (x).
      move => [] w H.
      exists w.
      by rewrite /f /= H. 
    Qed.

    Lemma f_right_congruent: right_congruent f.
    Proof.
      move => u v a H.
      rewrite -2!cats1 /f /= 2!dfa_run'_cat.
      by rewrite 2!last_cat -/(f u) -/(f v) H.
    Qed.

    Lemma f_refining: refining (dfa_lang A') f.
    Proof.
      move => u v H.
      rewrite -!dfa_run_accept.
      by rewrite -/(f v) -/(f u) -H.
    Qed.

    Definition dfa_to_myhill : Myhill_Rel (dfa_lang A') :=
      {|
        myhill_func := {| fin_surjective := f_surjective |};
        myhill_congruent := f_right_congruent;
        myhill_refining := f_refining
      |}.

    Definition dfa_to_nerode' : Nerode_Rel (dfa_lang A') :=
      weak_nerode_to_nerode (myhill_to_weak_nerode dfa_to_myhill).

    Lemma nerode_lang_eq L1 L2: L1 =i L2 -> Nerode_Rel L1 -> Nerode_Rel L2.
    Proof.
      move => H [f H1]. econstructor.
      move => u v. split.
        move => H2 w. rewrite -!H. eapply H1.
        by eassumption.
      move => H2. apply H1 => w. rewrite !H.
      exact: H2.
    Qed.

    Definition dfa_to_nerode : Nerode_Rel (dfa_lang A) :=
      nerode_lang_eq (dfa_connected_correct A) dfa_to_nerode'.

  End DFA_To_Nerode.

  Check dfa_to_nerode.
  
End MyhillNerode.
