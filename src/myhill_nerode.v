Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool finset choice.
Require Import automata misc regexp.
Require Import base.

Set Implicit Arguments.
Import Prenex Implicits.



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

    
    Section Nerode_Inversion.

      Variable f: Nerode_Rel.

      Lemma inv_rcons w a: f (rcons (inv f (f w)) a) = f (rcons w a).
      Proof.
        apply (f.(nerode_equiv)) => u.
        rewrite -2!cats1 -2!catA /=. 
        apply f.(nerode_equiv).
        by rewrite invK.
      Qed.
      
    End Nerode_Inversion.
    

    Section Weak_Nerode.
      
      Definition imply_suffix {X} (f: word -> X) :=
        forall u v, f u = f v -> equal_suffix u v.
      
      Record Weak_Nerode_Rel :=
        {
          weak_nerode_func :> Fin_Eq_Cls;
          weak_nerode_imply: imply_suffix weak_nerode_func
        }.

    End Weak_Nerode.

    Section Weak_Nerode_Inversion.

      Variable f: Weak_Nerode_Rel.

      Lemma inv_mem_L w: inv f (f w) \in L = (w \in L).
      Proof.
        rewrite -{2}(cats0 w).
        erewrite f.(weak_nerode_imply).
          erewrite cats0. reflexivity.
        by rewrite invK.
      Qed.

    End Weak_Nerode_Inversion.
    

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

    Definition ext := [ fun x a => f (rcons (inv f x) a) ].
    
    Definition pext := [ fun x y => [ fun a => (f (rcons (inv f x) a), f (rcons (inv f y) a)) ] ].

    Definition dist := [ fun x y => (inv f x) \in L != ((inv f y) \in L) ].

    Definition distinct0 := [set x | dist (fst x) (snd x) ].

    Definition distinctS (distinct: {set X*X}) :=
      [set  (x,y) | x in X, y in X & [ exists a, pext x y a \in distinct ] ].

    Definition unnamed distinct :=
        distinct0 :|: distinct :|: (distinctS distinct).

    Definition distinct := mu unnamed.
    
    Notation "x ~= y" := ((x,y) \notin distinct) (at level 70, no associativity).


    Lemma distinct_pext x y (distinct: {set _}): (x,y) \in distinctS distinct -> exists a, pext x y a \in distinct.
    Proof.
      move/imset2P => [] x' y' _.
      rewrite !inE /=.
      move/pred0Pn => [a] /=.
      move => H [] H1 H2; do 2!subst.
      by exists a.
    Qed.
    
    Lemma unnamed_mono: mono unnamed.
    Proof.
      move => s t.
      rewrite unlock /= => /existsP H.
      rewrite /unnamed.
      apply/existsP => [] [] x /andP [].
      rewrite 2!topredE.
      rewrite 3!in_set 2!negb_or => /andP [] /andP [] H0 H1 H2.
      rewrite 3!in_set => /orP [/orP [H3|H3]|H3].
          move: H0. by rewrite H3.
        apply: H.
        exists x. rewrite 2!topredE. by rewrite H1 H3.
      destruct x. move/distinct_pext: H3 => [] a H3.
      move: H2.
      rewrite mem_imset2 //= !inE.
      apply/existsP. exists (a).
      case H4: (pext s1 s2 a \in t) => //.
      exfalso. apply H. exists (pext s1 s2 a).
      rewrite 2!topredE. by rewrite H3 H4.
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
      rewrite /distinct.
      move: x.
      apply mu_ind => [|dist IHdist] x.
        by rewrite  in_set.
      rewrite /unnamed /= 2!in_setU 2!negb_or.
      rewrite (IHdist x) equiv0_refl /=.
      apply/imset2P => H. destruct H as [y z _ H1 H2].
      move: H2 H1 => [H3 H4]. do 2!subst.
      rewrite !inE => /existsP [] a.
      apply/negP. rewrite /pext.
      exact: IHdist.
    Qed.

    Lemma dist_sym x y: dist x y -> dist y x.
    Proof. by rewrite /= eq_sym. Qed.

    Lemma not_dist_sym x y: ~~ dist x y -> ~~ dist y x.
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
      rewrite /unnamed 6!in_set 4!negb_or.
      move/andP => [] /andP [] H1 H2 H3.
      rewrite not_dist_sym //= IHs //=.
      apply/negP. move/imset2P => [] x' y' _.
      rewrite !inE /= => /existsP [] a.
      move => H [] H4 H5; do 2!subst;
        move/negP: H3 => H3; apply: H3;
        rewrite mem_imset2 //= !inE;
        apply/existsP; exists a.
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
      rewrite mem_imset2 //= !inE.
      apply/existsP. exists a. apply: contraT => H7.
      move/imset2P: H6 => []. apply/imset2P.
      rewrite mem_imset2 //= !inE.
      apply/existsP. exists a. apply: contraT => H8.
      move: (IHs _ _ _ H7 H8).
      by rewrite H.
    Qed.
      
    Lemma L_distinct u v w: u ++ w \in L != (v ++ w \in L) -> (f u, f v) \in distinct.
    Proof.
      elim: w u v => [|a w IHw] u v.
        rewrite 2!cats0.
        rewrite /distinct muE -/distinct /unnamed => H.
        by rewrite /distinct0 /dist /= 3!in_set 2!inv_mem_L H.
      by exact: unnamed_mono.
      move => H.
      rewrite /distinct muE -/distinct /unnamed.
      rewrite 3!in_set. apply/orP. right.
      rewrite mem_imset2 //= !inE.
      apply/existsP. exists a.
      apply: IHw.
      move: H. apply: contraR => /negPn.
      rewrite -2!cats1 -2!catA cat1s.
      rewrite (weak_nerode_imply f (inv f (f u)) u); last by rewrite invK.
      by rewrite (weak_nerode_imply f (inv f (f v)) v); last by rewrite invK.
      by exact: unnamed_mono.
     Qed.

    Lemma distinct_final x y:
      (x,y) \in distinct ->
      exists w, (inv f x) ++ w \in L != ((inv f y) ++ w \in L). 
    Proof.
      rewrite /distinct.
      move: x y.
      apply mu_ind => [|dist IHdist] x y.
        by rewrite in_set.
      rewrite /unnamed 2!in_setU => /orP [].
        move/orP => [].
          rewrite /distinct0 /Minimalization.dist in_set /= => H.
          exists [::]. by rewrite 2!cats0.
        exact: IHdist.
      move/imset2P => [] x1 y1 _.
      rewrite !inE => /existsP []a H3 [] H4 H5. move: H3.
      move => H3. subst.
      move: (IHdist (pext x1 y1 a).1 (pext x1 y1 a).2 H3) => [w].
      rewrite /pext /= => H4.
      exists (a::w).
      rewrite -cat1s -(inv_mem_L f).
      rewrite 2!catA 2!cats1 inv_mem_L. 
      move: H4. apply: contraR => /negPn/eqP.
      rewrite (weak_nerode_imply f _  (inv f (f (rcons (inv f x1) a)))); last by rewrite invK.
        move => ->.
      by rewrite (weak_nerode_imply f _ (inv f (f (rcons (inv f y1) a)))); last by rewrite invK.
    Qed.
      
    Lemma equiv_final u v w:
      f u ~= f v ->
      u ++ w \in L = (v ++ w \in L).
    Proof. move => H. apply/eqP. move: H. apply: contraR. exact: L_distinct. Qed.

    Lemma distinct_final' x y: (x, y) \in distinct -> ~ equal_suffix L (inv f x)  (inv f y).
    Proof.
      move => /distinct_final [w H] H0.
      move: (H0 w).
      move => H1. move/eqP: H.
      by rewrite H1.
    Qed.
      
    
    Definition dist_repr := fun x => [set y | (x,y) \notin distinct].

    Lemma dist_repr_refl x : x \in dist_repr x.
    Proof. by rewrite in_set equiv_refl. Qed.
    
    Definition X_min := map dist_repr (enum f.(fin_type)).

    Lemma dist_repr_in_X_min x: dist_repr x \in X_min.
    Proof. apply/mapP. exists x => //. by rewrite mem_enum. Qed.

    Definition f_min := fun w => SeqSub _ (dist_repr_in_X_min (f w)).
      
    Lemma f_min_eq_distinct x y: f_min x = f_min y -> (f x, f y) \notin distinct.
    Proof.
      move => [] /= /setP H1. move: (H1 (f y)).
      by rewrite dist_repr_refl in_set => ->.
    Qed.                                            

    Lemma f_min_distinct_eq x y: (f x, f y) \notin distinct -> f_min x = f_min y.
    Proof.
      move => H.
      rewrite /f_min /=.
      apply/eqP.
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
      
      
    Lemma f_min_correct: equiv_suffix L f_min.
    Proof.
      move => x y.
      split.
        move/f_min_eq_distinct.
        move => H w.
        exact: equiv_final.
     move => H. 
     apply f_min_distinct_eq.
     apply/negP => /distinct_final'.
     move => H0. apply H0 => w.
     move: (H w).
     rewrite (weak_nerode_imply f x (inv f (f x))); last by rewrite invK.
     by rewrite (weak_nerode_imply f y (inv f (f y))); last by rewrite invK.
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

    Definition dfa_to_weak_nerode : Weak_Nerode_Rel (dfa_lang A') :=
      myhill_to_weak_nerode dfa_to_myhill.

    Definition dfa_to_nerode' : Nerode_Rel (dfa_lang A') :=
      {|
        nerode_func := {| fin_surjective := f_min_surjective dfa_to_weak_nerode |};
        nerode_equiv := f_min_correct dfa_to_weak_nerode
      |}.

    Lemma nerode_lang_eq L1 L2: L1 =i L2 -> Nerode_Rel L1 -> Nerode_Rel L2.
    Proof.
      move => H.
      move => [f H1].
      econstructor.
      move => u v. split.
        move => H2 w.
        rewrite -!H.
        apply H1.
        eexact H2.
      move => H2.
      apply H1.
      move => w.
      rewrite !H.
      exact: H2.
    Qed.

    Definition dfa_to_nerode : Nerode_Rel (dfa_lang A) :=
      nerode_lang_eq (dfa_connected_correct A) dfa_to_nerode'.

  End DFA_To_Nerode.

  Check dfa_to_nerode.
  
End MyhillNerode.
