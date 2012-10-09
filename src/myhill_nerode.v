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
        fin_func :> word -> fin_type;
        fin_surjective : surjective fin_func
      }.

    Section Inversion. 

      Variable f: Fin_Eq_Cls.
    
      Definition cr (f: Fin_Eq_Cls) x := xchoose (fin_surjective f x).

      Lemma crK: cancel (cr f) f.
      Proof. move => x. by move: (xchooseP (fin_surjective f x)) => /eqP {2}<-. Qed.

      (* Needed? *)
      Lemma eq_cr x: x = (f (cr f x)).
      Proof. by rewrite crK. Qed.
      
    End Inversion.

    Section Myhill.

      Definition right_congruent {X} (f: word -> X) :=
        forall u v a, f u = f v -> f (rcons u a) = f (rcons v a).

      Definition refines {X} (f: word -> X) :=
        forall u v, f u = f v -> u \in L = (v \in L).
        
      Record Myhill_Rel :=
        {
          myhill_func :> Fin_Eq_Cls; 
          myhill_congruent: right_congruent myhill_func;
          myhill_refines: refines myhill_func
        }.
        
    End Myhill.

    
    Definition suffix_equal u v :=
      forall w, u++w \in L = (v++w \in L).

    Definition equiv_suffix {X} (f: word -> X) :=
      forall u v, f u = f v <-> suffix_equal u v.
    
    Record Nerode_Rel :=
      {
        nerode_func :> Fin_Eq_Cls;
        nerode_equiv: equiv_suffix nerode_func
      }.

    Lemma cr_rcons (f: Nerode_Rel) w a: f (rcons (cr f (f w)) a) = f (rcons w a).
    Proof.
      apply (f.(nerode_equiv)) => u.
      rewrite -2!cats1 -2!catA /=. 
      apply f.(nerode_equiv).
      by rewrite crK.
    Qed.

    Section Weak_Nerode.
      
      Definition imply_suffix {X} (f: word -> X) :=
        forall u v, f u = f v -> suffix_equal u v.
      
      Record Weak_Nerode_Rel :=
        {
          weak_nerode_func :> Fin_Eq_Cls;
          weak_nerode_imply: imply_suffix weak_nerode_func
        }.

    End Weak_Nerode.

    Section Weak_Nerode_Facts.

      Variable f: Weak_Nerode_Rel.

      Lemma cr_mem_L_cat u v: cr f (f u) ++ v \in L = (u ++ v \in L).
      Proof.
        erewrite f.(weak_nerode_imply).
          reflexivity.
        by rewrite crK.
      Qed.

      Lemma cr_mem_L w: cr f (f w) \in L = (w \in L).
      Proof.
        rewrite -(cats0 (cr f (f w))) -{2}(cats0 w).
        exact: cr_mem_L_cat.
      Qed.

    End Weak_Nerode_Facts.


    Definition nerode_weak_nerode (f: Nerode_Rel): Weak_Nerode_Rel :=
      {| weak_nerode_imply := fun u v H => match nerode_equiv f u v with conj H0 H1 => H0 H end |}.
    
    Coercion nerode_weak_nerode : Nerode_Rel >-> Weak_Nerode_Rel.

    
      
  End Relations.
  


  Section DFA_To_Myhill.
    Variable A: dfa char.
    Definition A_c := dfa_connected A.
    Definition f_M := fun w => last (dfa_s A_c) (dfa_run A_c w).
    
    Lemma f_M_surjective: surjective f_M.
    Proof.
      move => x.
      move: (dfa_connected_repr x) => [] w <-.
      by exists w.
    Qed.

    Definition f_fin : Fin_Eq_Cls :=
      {|
        fin_func := f_M;
        fin_surjective := f_M_surjective
      |}.

    Lemma f_M_right_congruent: right_congruent f_M.
    Proof.
      move => u v a H.
      rewrite -2!cats1 /f_M /= 2!dfa_run'_cat.
      by rewrite 2!last_cat -/(f_M u) -/(f_M v) H.
    Qed.

    Lemma f_M_refines: refines (dfa_lang A_c) f_M.
    Proof.
      move => u v H.
      rewrite -!dfa_run_accept.
      by rewrite -/(f_M v) -/(f_M u) -H.
    Qed.

    Definition dfa_to_myhill' : Myhill_Rel (dfa_lang A_c) :=
      {|
        myhill_func := f_fin;
        myhill_congruent := f_M_right_congruent;
        myhill_refines := f_M_refines
      |}.

    Lemma myhill_lang_eq L1 L2: L1 =i L2 -> Myhill_Rel L1 -> Myhill_Rel L2.
    Proof.
      move => H [f H1]. econstructor;
        first by eauto.
      move => u v. rewrite -H. eauto.
    Qed.

    Lemma dfa_to_myhill : Myhill_Rel (dfa_lang A).
    Proof. exact: myhill_lang_eq (dfa_connected_correct A) dfa_to_myhill'. Defined.

  End DFA_To_Myhill.
  
  Section Myhill_Weak_Nerode.

    Variable L: language char.
    Variable f: Myhill_Rel L.

    Lemma myhill_suffix: imply_suffix L f.
    Proof.
      move => u v Huv w.
      elim: w u v Huv => [|a w IHw] u v Huv.
        rewrite 2!cats0.
        exact: f.(myhill_refines).
      rewrite -cat1s 2!catA 2!cats1.
      apply: IHw.
      exact: f.(myhill_congruent).
    Qed.

    Lemma myhill_to_weak_nerode: Weak_Nerode_Rel L.
    Proof. exact
      {|
        weak_nerode_func := f;
        weak_nerode_imply := myhill_suffix
      |}.
    Defined.
    
  End Myhill_Weak_Nerode.

  Section Nerode_To_DFA.
    Variable L: language char.
    Variable f: Nerode_Rel L.

    Definition nerode_to_dfa :=
      {|
        dfa_s := f [::];
        dfa_fin := [pred x | cr f x \in L ];
        dfa_step := [fun x a => f (rcons (cr f x) a)]
      |}.
    
    Lemma nerode_to_dfa_run w: last (f[::]) (dfa_run' nerode_to_dfa (f [::]) w) = f w.
    Proof.
      move: w.
      apply: last_ind => [|w a IHw] //.
      rewrite -{1}cats1 dfa_run'_cat last_cat IHw /=.
      exact: cr_rcons.
    Qed.
      
    Lemma nerode_to_dfa_correct: L =i dfa_lang nerode_to_dfa.
    Proof.
      move => w.
      rewrite /dfa_lang /= -dfa_run_accept nerode_to_dfa_run in_simpl /=.
      by rewrite (cr_mem_L f w).
    Qed.
      
  End Nerode_To_DFA.
  
  Section Minimalization.
    Variable L: language char.
    Variable f_0: Weak_Nerode_Rel L.
    Definition X := f_0.(fin_type).

    Definition succ := [ fun x a => f_0 ((cr f_0 x) ++ [::a]) ].
    
    Definition psucc := [ fun x y => [ fun a => (succ x a, succ y a) ] ].

    Definition distinguishable := [ fun x y => (cr f_0 x) \in L != ((cr f_0 y) \in L) ].

    Definition dist0 := [set x | distinguishable x.1 x.2 ].

    Lemma dist0P x:
      reflect (cr f_0 x.1 \in L <> (cr f_0 x.2 \in L))
              (x \in dist0).
    Proof.
      rewrite /dist0 /= !inE.
      apply: iffP. apply idP.
        by move/eqP.
      by move/eqP.
    Qed.
        
    Lemma dist0NP x:
      reflect (cr f_0 x.1 \in L = (cr f_0 x.2 \in L))
              (x \notin dist0).
    Proof.
      apply: iffP. apply idP.
        move => H. apply/eqP. move: H.
        apply: contraR. move/eqP.
        by move/dist0P.
      move/eqP. apply: contraL. by move/dist0P/eqP.
    Qed.

    Definition distS (dist: {set X*X}) :=
      [set  (x,y) | x in X, y in X & [ exists a, psucc x y a \in dist ] ].

    Lemma distSP (dist: {set X*X}) x y:
      reflect (exists a, psucc x y a \in dist)
              ((x,y) \in distS dist).
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

    Lemma distSNP (dist: {set X*X}) x y:
      reflect (forall a, psucc x y a \notin dist)
              ((x,y) \notin distS dist).
    Proof.
      apply: introP.
        move/distSP => H1 a.
        apply/negP => H2. by eauto.
      move/negbTE/distSP => [a H1] H2.
      absurd (psucc x y a \in dist) => //.
      by apply/negP.
    Qed.
    
    Definition one_step_dist dist := dist0 :|: dist :|: (distS dist).

    Lemma one_step_distP (dist: {set X*X}) x:
      reflect ([\/ x \in dist0, x \in dist | x \in distS dist])
              (x \in one_step_dist dist).
    Proof.
      rewrite /one_step_dist !inE.
      apply: introP.
        move/orP => [/orP [] |]; eauto using or3.
      by move/norP => [] /norP [] /negbTE -> /negbTE -> /negbTE -> [].
    Qed.

    Lemma one_step_distNP (dist: {set X*X}) x:
      reflect ([/\ x \notin dist0, x \notin dist & x \notin distS dist])
              (x \notin one_step_dist dist).
    Proof.
      apply: introP.
        by move/one_step_distP/nand3P/and3P.
      move/negbNE/one_step_distP/nand3P => H1 H2.
      apply: H1. by apply/and3P.
    Qed.
      
    Definition distinct := lfp one_step_dist.

    Notation "x ~!= y" := ((x,y) \in distinct) (at level 70, no associativity).
    Notation "u ~!=_f_0 v" := (f_0(u) ~!= f_0(v)) (at level 70, no associativity).
    Notation "x ~= y" := ((x,y) \notin distinct) (at level 70, no associativity).
    Notation "u ~=_f_0 v" := (f_0(u) ~= f_0(v)) (at level 70, no associativity).

    Lemma distS_mono: mono distS.
    Proof.
      move => s t /subsetP H.
      apply/subsetP.
      move => [x y] /distSP [a H1].
      apply/distSP. exists a.
      exact: H.
    Qed.
      
    Lemma one_step_dist_mono: mono one_step_dist.
    Proof.
      move => s t H. apply/subsetP.
      move => [x y] /one_step_distP [] H1; apply/one_step_distP;
        first by eauto using or3.
        move: (subsetP H _ H1).
        by eauto using or3.
      move/subsetP: (distS_mono H).
      by eauto using or3.
    Qed.

    Lemma equiv0_refl x:
      (x,x) \notin dist0.
    Proof. by rewrite in_set /= eq_refl. Qed.

    Lemma equiv_refl x: x ~= x.
    Proof.
      rewrite /distinct. move: x.
      apply lfp_ind => [|dist IHdist] x.
        by rewrite  in_set.
      apply/one_step_distNP. econstructor => //;
        first by exact: equiv0_refl.
      apply/distSNP => a.
      exact: IHdist.
    Qed.

    Lemma dist_sym x y: distinguishable x y -> distinguishable y x.
    Proof. by rewrite /= eq_sym. Qed.

    Lemma not_dist_sym x y: ~~ distinguishable x y -> ~~ distinguishable y x.
    Proof. apply: contraL. move/dist_sym => H. by apply/negPn. Qed.
    
    Lemma equiv0_sym x y: (x,y) \notin dist0 -> (y,x) \notin dist0.
    Proof. by rewrite /dist0 /= 2!in_set eq_sym. Qed.
    
    Lemma dist0_sym x y: (x,y) \in dist0 -> (y,x) \in dist0.
    Proof. by rewrite /dist0 /= 2!in_set eq_sym. Qed.

    Lemma equiv_sym x y:  x ~= y -> y ~= x.
    Proof.
      move: x y.  
      rewrite /distinct.
      apply lfp_ind => [|s IHs] x y.
        by rewrite 2!in_set.
      move/one_step_distNP => [] H0 H1 H2.
      apply/one_step_distNP. constructor.
          exact: equiv0_sym.
        exact: IHs.
      apply/distSNP => a. 
      move/distSNP in H2. 
      apply: IHs. exact: H2.
    Qed.

    Lemma equiv_trans x y z: x ~= y -> y ~= z -> x ~= z.
    Proof.
      move: x y z.  
      rewrite /distinct.
      apply lfp_ind => [|s IHs] x y z.
        by rewrite 3!in_set.
      move/one_step_distNP => [] /dist0NP H1 H2 /distSNP H3.
      move/one_step_distNP => [] /dist0NP H4 H5 /distSNP H6.
      apply/one_step_distNP. constructor.
          apply/dist0NP. by rewrite H1 H4.
        by apply: IHs; eassumption.
      apply/distSNP => a.
      apply: IHs.
        by eapply H3.
      exact: H6.
    Qed.


    Lemma equiv_suffix_equal u v: u ~=_f_0 v -> suffix_equal L u v.
    Proof.
      move => H w. apply/eqP. move: H.
      apply: contraR.
      elim: w u v => [|a w IHw] u v.
        rewrite 2!cats0.
        rewrite /distinct lfpE -/distinct /one_step_dist => H;
          last by exact: one_step_dist_mono.
        by rewrite /dist0  /= 3!in_set 2!cr_mem_L H.
      move => H.
      rewrite /distinct lfpE -/distinct;
        last by exact: one_step_dist_mono.
      apply/one_step_distP. apply: Or33.
      apply/distSP. exists a.
      apply: IHw.
      by rewrite -2!catA 2!(cr_mem_L_cat f_0).
    Qed.
   
    Lemma distinct_not_suffix_equal u v:
      u ~!=_f_0 v ->
      exists w, u ++ w \in L != (v ++ w \in L). 
    Proof.
      rewrite /distinct.
      move: u v.
      apply lfp_ind => [|dist IHdist] u v.
        by rewrite in_set.
      move/one_step_distP => [].
          move/dist0P => /eqP.
          rewrite !cr_mem_L /= => H.
          exists [::]. by rewrite 2!cats0.
        exact: IHdist.
      move/distSP => [a] /IHdist [w].
      rewrite -2!catA !cr_mem_L_cat.
      by eauto.
    Qed.

    Lemma equivP u v:
      reflect (suffix_equal L u v)
              (u ~=_f_0 v).
    Proof.
      apply: introP.
        exact: equiv_suffix_equal.
      move/negbNE => /distinct_not_suffix_equal [w H] H0.
      move: (H0 w).
      move => H1. move/eqP: H.
      by rewrite H1.
    Qed.
    
    
    Definition equiv_repr x := [set y | x ~= y].

    Lemma equiv_repr_refl x : x \in equiv_repr x.
    Proof. by rewrite in_set equiv_refl. Qed.
    
    Definition X_min := map equiv_repr (enum (fin_type f_0)).

    Lemma equiv_repr_mem x: equiv_repr x \in X_min.
    Proof. apply/mapP. exists x => //. by rewrite mem_enum. Qed.

    Definition f_min w := SeqSub (equiv_repr_mem (f_0 w)).
      
    Lemma f_minP u v:
      reflect (f_min u = f_min v)
              (u ~=_f_0 v).
    Proof.
      apply: iffP.
        apply idP.
        move => H.
        rewrite /f_min /=.
        apply/eqP.
        change ([set x | (f_0 u, x) \notin distinct] == [set x | (f_0 v, x) \notin distinct]).
        apply/eqP.
        apply/setP => x.
        rewrite 2!in_set.
        apply/idP/idP => H0;
          eauto using equiv_sym, equiv_trans.
      move => [] /= /setP H1. move: (H1 (f_0 v)).
      by rewrite equiv_repr_refl in_set => ->.
    Qed.                                            

    Lemma f_min_correct: equiv_suffix L f_min.
    Proof.
      move => u v.
      split.
        move/f_minP.
        exact: equiv_suffix_equal.
     move => H. 
     apply/f_minP.
     by apply/equivP.
    Qed.                                                  

    Lemma f_min_surjective: surjective f_min.
    Proof.
      move => [x Hx].
      move/mapP: (Hx) => [y Hy Hxy].
      exists (cr f_0 y).
      rewrite /f_min.
      change (equiv_repr (f_0 (cr f_0 y)) == x).
      by rewrite Hxy crK.
    Qed.

    Definition f_min_fin: Fin_Eq_Cls :=
      {| fin_surjective := f_min_surjective |}.

    Lemma weak_nerode_to_nerode: Nerode_Rel L.
    Proof. exact
      {|
        nerode_func := f_min_fin; 
        nerode_equiv := f_min_correct
      |}.
    Defined.

  End Minimalization.

  

End MyhillNerode.
