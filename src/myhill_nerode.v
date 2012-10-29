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
    Defined.

    Lemma dfa_to_myhill : Myhill_Rel (dfa_lang A).
    Proof. exact: myhill_lang_eq (dfa_connected_correct A) dfa_to_myhill'. Defined.

    Lemma dfa_to_myhill_size : #|A| >= #|fin_type dfa_to_myhill|.
    Proof.
      exact: dfa_connected_size.
    Qed.

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

    Lemma myhill_to_weak_nerode_size: #|fin_type f| = #|fin_type myhill_to_weak_nerode|.
    Proof. by []. Qed.
    
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

    Lemma nerode_to_dfa_size: #|fin_type f| = #|nerode_to_dfa|.
    Proof. by []. Qed.                                                
      
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
    
    Definition X_min := undup (map equiv_repr (enum (fin_type f_0))).

    Lemma equiv_repr_mem x: equiv_repr x \in X_min.
    Proof. rewrite mem_undup. apply/mapP. exists x => //. by rewrite mem_enum. Qed.

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
      have: x \in map equiv_repr (enum (fin_type f_0)) by rewrite mem_undup in Hx.
      move/mapP => [y Hy Hxy].
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

    Lemma weak_nerode_to_nerode_size: #|fin_type f_0| >= #|fin_type weak_nerode_to_nerode|.
    Proof.
      rewrite /= /X_min /= /equiv_repr card_seq_sub.
        apply: leq_trans.
          by apply size_undup.
        by rewrite size_map -cardE.
      exact: undup_uniq.
    Qed.

  End Minimalization.

  Lemma nerode_lang_eq L1 L2: L1 =i L2 -> Nerode_Rel L1 -> Nerode_Rel L2.
  Proof. move => H [f Hf]. econstructor. move => u v. instantiate (1 := f).
    split. move/Hf => Hs w. by rewrite -!H.
    move => Hs. apply Hf => w. by rewrite !H.
  Defined.

  Lemma eq1i {X: Type} {p q: pred X}: p =1 q <-> p =i q.
  Proof. split; move => H x. rewrite -!topredE /=. by move: (H x). move: (H x);
    by rewrite -!topredE /=. Qed.

  Lemma cons_uniqS {X: eqType} {x: X} {xr: seq X}: uniq (x::xr) -> x \notin xr.
  Proof.
    elim: xr x => [|y xr IHxr] x //.
    move => /= /andP []. rewrite in_cons => /norP [].
    move => H1 H2 /andP [] H3 H4.
    apply/norP. by eauto.
  Qed.
  
  Lemma card_leq_inj (T T': finType) (f: T -> T'): injective f -> #|T| <= #|T'|.
  Proof.
    move Eq: #|T'| => n.
    elim: n T T' f Eq => [|n IHn] T T' f Eq If //.
      case: (pickP T).
        move => x _.
        move/card0_eq: Eq => H0.
        have: (f x \in T') by [].
        by rewrite H0.
      move/eq1i => H1.
      apply: eq_leq.
      exact: eq_card0.

    pose X := behead (enum T').
    have UX: (uniq X).
      apply: subseq_uniq.
      rewrite /X -drop1.
      apply suffix_subseq.
      instantiate (1 := take 1 (enum T')).
      rewrite cat_take_drop.
      exact: enum_uniq.
    have SX: (size X = n) by rewrite size_behead -cardE Eq.
    have SssX: (#|seq_sub_finType X| = n) by rewrite card_seq_sub.
    pose pY := fun y => f y \in X.
    pose Y := (filter pY (enum T)).
    have UY : uniq Y.
      apply: subseq_uniq.
      apply filter_subseq.
      exact: enum_uniq.
    have HYX: forall y, y \in Y -> f y \in X.
      move => y. rewrite /Y.
      by rewrite mem_filter => /andP [].
    pose g  := fun Sy => match Sy with SeqSub y Hy => SeqSub (HYX y Hy) end.
    have Ig: injective g.
      move => [x Hx] [y Hy].
      rewrite /g.
      move => [] /If Hxy.
      move: Hx Hy. rewrite Hxy => Hx Hy.
      have: Hx = Hy by exact: bool_irrelevance.
      by move => ->.
    move ET: #|T| => s.
    case: s ET => [|s] ET //.
    move: (ET) => <-.
    have: size Y <= #|T|.
      rewrite /Y cardE.
      apply size_subseq.
      rewrite enumT.
      exact: filter_subseq.
    have/existsP: [ exists x, x :: X == enum T' ].
      apply/existsP.
      rewrite -(cat_take_drop 1 (enum T')) /X -drop1.
      move: (Eq). rewrite cardE.
      case: (enum T') => [|x xr] // _.
      rewrite take_cons /= cat_take_drop drop0.
      by exists x.
    move => [x /eqP HX].
    have HxX: x \notin X.
      have: uniq (enum T') by exact: enum_uniq.
      rewrite -HX.
      exact: cons_uniqS.
    have Hxz: forall z, reflect (z = x) (z \notin X).
      move => z. apply: iffP. apply idP.
        case_eq (z \in enum T') => //.
          rewrite -HX. rewrite in_cons => /orP [/eqP ->|->] //.
        by rewrite mem_enum //.
      by move => ->.
     
    case: (altP (@existsP _ (fun y => f y == x))).
      move => [y /eqP Hy].
      have HyY: y \notin Y.
        rewrite /Y. rewrite mem_filter mem_enum /pY Hy.
        apply/nandP. by auto.
      have Hyz: forall z, reflect (z = y) (f z \notin X).
        move => z. apply: iffP. apply idP.
          move/Hxz. rewrite -Hy. exact: If.
        move => ->. by rewrite Hy.
      have HY: enum Y = enum (predC1 y).
        apply: eq_enum => z.
        rewrite mem_filter.
        rewrite inE /pY /pred1 /=.
        apply/idP/idP.
          by move/andP => [] /Hyz /eqP.
        move/eqP/Hyz.
        rewrite mem_enum. by move => ->.
      have SYT: size Y = #|T|.-1.
        move: UY. move/card_uniqP => <-.
        rewrite cardE HY -cardE.
        by rewrite cardC1.
      have SssY: (#|seq_sub_finType Y| <= n).
        apply: IHn; eassumption.
      have SY: #|seq_sub_finType Y| = size Y by exact: card_seq_sub.
      move: SssY. rewrite SY.
      by rewrite -SX SYT ET.
    rewrite negb_exists => /forallP H.
    have HY: (Y = enum T).
      rewrite /Y.
      apply/all_filterP.
      apply/allP.
      move => z _. move: (H z).
      by rewrite /pY => /eqP/Hxz.
    have SYT: size Y = #|T| by rewrite HY -cardE.
    have :(#|seq_sub_finType Y| <= n).
      apply: IHn; eassumption.
    have SY: #|seq_sub_finType Y| = size Y by exact: card_seq_sub.
    rewrite SY SYT.
    by move/leqW.
  Qed.

  Lemma nerode_lang_eq_size L1 L2 (f1: Nerode_Rel L1) (f2: Nerode_Rel L2): L1 =i L2 -> #|fin_type f1| = #|fin_type f2|.
  Proof.
    move => HL.
    pose h : fin_type f1 -> fin_type f2 := fun x => (f2 (cr f1 x)).
    pose j : fin_type f2 -> fin_type f1 := fun x => (f1 (cr f2 x)).
    have Ih: (injective h).
      move => x y.
      rewrite /h.
      move/nerode_equiv => H.
      rewrite -(crK f1 x) -(crK f1 y).
      apply/nerode_equiv.
      move => w. rewrite !HL.
      exact: H.
    have Ij: (injective j).
      move => x y.
      rewrite /h.
      move/nerode_equiv => H.
      rewrite -(crK f2 x) -(crK f2 y).
      apply/nerode_equiv.
      move => w. rewrite -!HL.
      exact: H.
    apply/eqP.
    move/card_leq_inj: Ih.
    move/card_leq_inj: Ij.
    by rewrite eqn_leq => -> ->.
  Qed.
  
  Lemma nerode_minimal L (f: Nerode_Rel L) A: dfa_lang A =i L -> #|A| >= #|nerode_to_dfa f|.
  Proof.
    move => H.
    rewrite -nerode_to_dfa_size.
    move: (dfa_to_myhill_size A) => H1.
    move: (myhill_to_weak_nerode_size (dfa_to_myhill A)) => H2.
    rewrite H2 in H1. clear H2.
    move: (weak_nerode_to_nerode_size (myhill_to_weak_nerode (dfa_to_myhill A))) => H2.
    apply: leq_trans; last by apply H1.
    apply: leq_trans; last by apply H2.
    apply: eq_leq.
    apply: nerode_lang_eq_size.
    move => w. symmetry. exact: H.
  Qed.
    
    
    
    

End MyhillNerode.
