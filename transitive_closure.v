Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool.
Require Import automata misc regexp.

Set Implicit Arguments.

(* http://krchowdhary.com/toc/dfa-to-reg-exp.pdf *)



Section AllButLast.
  
  Variable X: Type.
  
  Definition belast (xs: seq X) :=
    (fix belast xs := 
    match xs with
      | [::] => [::]
      | [::x] => [::]
      | x::xs => x::(belast xs)
    end)
    xs.

  Definition allbutlast p : pred (seq X) :=
    fun xs => all p (belast xs).

  Lemma allbutlast_impl (p q: pred X) xs:
    (forall x, p x -> q x) ->
    allbutlast p xs ->
    allbutlast q xs.
  Proof.
    elim: xs => [|x xs IHxs].
      by [].
    case: xs IHxs => [|y xs IHxs].
      by [].
    rewrite /allbutlast /=.
    move => H0 /andP [] /H0 -> /=.
    by move: (IHxs H0). 
  Qed.

  Lemma allbutlast0 p: allbutlast p [::].
  Proof. by rewrite /allbutlast /=. Qed.

  Lemma allbutlast1 p x: allbutlast p [::x].
  Proof. by []. Qed.
  
  Lemma allbutlast_cons (p: pred X) x xs: p x -> allbutlast p xs -> allbutlast p (x::xs).
  Proof.
    elim: xs x => [|y xs IHxs] x //. 
    by rewrite /allbutlast /= => -> /=.
  Qed.

  Lemma allbutlast_cons' p x y xs: allbutlast p (x::y::xs) -> p x && allbutlast p (y::xs).
  Proof.
    elim: xs x => [|z xs IHxs] x //. 
  Qed.
  
  Lemma all_allbutlast p xs: all p xs -> allbutlast p xs.
  Proof.
    elim: xs => [|x xs IHxs] //.
    move => /= /andP [] H0 /IHxs.
    by apply: allbutlast_cons.
  Qed.

  Lemma allbutlast_cons'' p x (xs: seq X): allbutlast p (x::xs) -> (size xs == 0) || (p x && allbutlast p xs). 
  Proof.
    elim: xs x => [|y xs IHxs] x.
      by [].
    by rewrite orFb.    
  Qed.
  
  Lemma all_allbutlast_cat p xs ys: all p xs -> allbutlast p ys -> allbutlast p (xs++ys).
  Proof.
    elim: xs => [|x xs IHxs].
      by rewrite /= => _.
    rewrite /= => /andP [] H0. 
    move => H1 H2. move: (IHxs H1 H2).
    by apply: allbutlast_cons.
  Qed.

  Lemma allbutlast_last p x xs: allbutlast p xs -> p (last x xs) -> all p xs.
  Proof.
    elim: xs x => [|y xs IHxs] x //.
    case: xs IHxs => [|z xs] IHxs.
      by rewrite /allbutlast /= => -> ->.
    move/allbutlast_cons'/andP => [] H0 H1 H2.
    move: (IHxs x H1 H2).
    by rewrite /= H0 => /andP [] ->.
  Qed.
                         
  Lemma allbutlast_pred0 p xs: p =1 pred0 -> allbutlast p xs -> size xs <= 1.
  Proof.
    move => H0.
    elim: xs => [|x xs IHxs] //.
    case: xs IHxs => [|y xs] IHxs //.
    move/allbutlast_cons'.
    move/andP=>[].
    by rewrite (H0 x).
  Qed.

  
End AllButLast.   


  Section Split.
    
  Variable X: eqType.

  Lemma last_neutral (x: X) xs: (last x xs) = (last (last x xs) xs).
  Proof.
    elim: xs x => [|y xs IHxs] x.
      by [].
    by rewrite last_cons last_cons.
  Qed.
    
  Lemma allbutlast_split p (xs: seq X):
    exists xx,
      (xs == flatten xx) &&
      (all (allbutlast p) xx &&
      allbutlast
      (fun xs => if xs is (x::xs) then p (last x xs) == false else false )
      xx).
  Proof.
    elim: xs => [|x xs IHxs].
      exists [::] => //.

    move: IHxs => [] xx /andP [] /eqP Hxs /andP [] H0 H1.
    case: xx Hxs H0 H1 => [|xx [| xx' xxr]] Hxs H0 H1.
        exists [::[::x]].
        rewrite /= Hxs eq_refl /=.
        by [].
      case: xx Hxs H0 H1 => [|y [|y' ys]] Hxs H0 H1.
          exists [::[::x]].
          by rewrite /= Hxs eq_refl.

        case_eq (p x) => H4. 
          exists [::[::x;y]].
          rewrite /= Hxs eq_refl.
          by rewrite allbutlast_cons.

        (* ~ p x *)
        exists [::[::x];[::y]].
        rewrite /= Hxs eq_refl /=.
        rewrite allbutlast_cons => //.
        by rewrite H4.

      case_eq (p x) => H4.
        exists ([::[:: x, y, y' & ys]]).
        rewrite /= Hxs eq_refl /=.
        rewrite allbutlast_cons => //.
        move: H0 => /=.
        by rewrite andbT.

      (* ~ p x *)
      exists ([::[::x] ; [:: y, y' & ys]]).
      rewrite /= Hxs eq_refl /=.
      move: H0. rewrite /= andbT => -> /=.
      rewrite allbutlast_cons => //.
      by rewrite H4.                                   

    case: xx Hxs H0 H1 => [|y [|y' ys]] Hxs H0 H1.
        by [].
      case_eq (p x) => H4.
        exists ([:: [:: x; y], xx' & xxr]).        
        rewrite /= Hxs eq_refl /=.
        rewrite allbutlast_cons => //.
        move: H0 => /= /andP [] -> -> /=.
        move: (allbutlast_cons' _ _ _ _ H1) => /= /andP [] H2 H3.
        by rewrite allbutlast_cons => //.
      (* ~ p x *)
      exists [:: [::x], [::y], xx' & xxr ].                        
      rewrite Hxs eq_refl /=.
      move: H0 => /= /andP [] -> -> /=.
      rewrite allbutlast_cons => //.
      by rewrite /= H4.

    case_eq (p x) => H4.
      exists [:: [:: x, y, y' & ys], xx' & xxr].
      rewrite Hxs eq_refl /=.
      move: H0 => /= /andP [] H2 /andP [] -> ->  /=.
      rewrite allbutlast_cons => //=.
    (* ~ p x *)
    exists [:: [::x], [::y, y' & ys], xx' & xxr ].
    rewrite Hxs eq_refl /=.
    move: H0 => /= /andP [] -> -> /=.
    rewrite allbutlast_cons => //.
    by rewrite H4.                                    
  Qed.

  End Split.

Section TransitiveClosure.

  Variable char: finType.
  Variable A: dfa char.
  
    Section Misc.
      Lemma Plus_dist r s (w: word char): w \in Plus r s = (w \in r) || (w \in s). 
      Proof. by rewrite -topredE. Qed.
      Lemma foldr_Plus r rs (w: word char):
        w \in foldr (@Plus char) r rs = (w \in r) || has (fun r => w \in r) rs. 
      Proof.
        elim: rs r => [|s rs IHrs] r /=. 
          by rewrite orbF.
        rewrite orbCA -IHrs.
        by rewrite -topredE -topredE.
      Qed.
    End Misc.

  Lemma minn_to_ord m n: minn m n <= n.
  Proof. elim: n m => [|n IHn] m /=.
    by rewrite /minn.
    rewrite /minn.
    case_eq (m < n.+1).
    by apply: ltnW.
    move => _. by apply: ltnSn.
  Qed.

  Lemma leq_ltn_gt0 n m: m > 0 -> n <= m.-1 -> n < m.
  Proof.  elim: m n => [|m IHm] n //=. Qed.

  Lemma A_has_states: #|A| > 0.
  apply/card_gt0P.
  by exists (dfa_s0 A).
  Qed.
  
  (* this represents k in 'I_#|A| *)
  Definition k1_ord k := 
    Ordinal (leq_ltn_gt0 _ _ A_has_states (minn_to_ord k #|A|.-1)).

  Lemma k1_ord_lt k: k1_ord k < k.+1.
  Proof.
    rewrite /k1_ord /=.
    case_eq (k <= #|A|.-1) => H0.
      rewrite minnl => //.
    move: (leq_total k #|A|.-1).
    rewrite H0 /= => H1.
    by rewrite minnr.
  Qed.
    
  Fixpoint R (k: nat) (i j: 'I_#|A|) : regular_expression char :=
    match k with
      |   0  => 
            let r := foldr (@Plus _) (Void _) (map (@Atom _) (filter [pred a | dfa_step A (enum_val i) a == (enum_val j)] (enum char))) in
              if i == j then Plus r (Eps _) else r
      | k.+1 =>
          let k' := k1_ord k in
            Plus (
                Conc (R k i k')
                     (Conc (Star (R k k' k')) (R k k' j))
              )
                 (R k i j)
    end.        

  Notation "'R^' k" := (R k) (at level 8).

  
  Definition L (k: nat) (x y: A) : pred (word char) :=
    [pred w | 
    (last x (dfa_run' A x w) == y)
         && allbutlast (fun x => enum_rank x < k) (dfa_run' A x w) 
    ].
  Notation "'L^' k" := (L k) (at level 8).


  Section L.
    Lemma L_monotone k i j w: w \in L^k i j -> w \in L^(k.+1) i j.
    Proof.
      rewrite -2!topredE /= /L /= => /andP [] -> /=.
      apply: allbutlast_impl.
      move => x.
      by apply: (@ltnW ((enum_rank x)) k).
    Qed.

    Lemma L_catL k i j w1 w2:
      w1 \in L^k i (enum_val (k1_ord k)) ->
      w2 \in L^k.+1 (enum_val (k1_ord k)) j ->
      w1++w2 \in L^k.+1 i j.
    Proof.
      rewrite /L -3!topredE /=.
      rewrite dfa_run'_cat.
      move => /andP [] /eqP H0 H1 /andP [] /eqP H2 H3.
      case: w1 H0 H1 => [|v1 w1] H0 H1.
        rewrite /= in H0.
        rewrite H0 /= H2 eq_refl /=.  
        exact: H3.
      rewrite last_cat.
      case: w2 H2 H3 => [|v2 w2] H2 H3.
        rewrite /= in H2.
        rewrite -H2 H0 /= eq_refl /=.
        eapply allbutlast_impl.
        move => x. by eapply (@ltnW ((enum_rank x)) k).
        rewrite cats0.
        exact H1.

      rewrite H0 H2 eq_refl andTb.
      eapply all_allbutlast_cat.
        apply: (allbutlast_last _ i) => //. 
          eapply allbutlast_impl.
          move => x.
          by eapply (@ltnW ((enum_rank x)) k).
        by [].
        rewrite H0. 
        rewrite enum_valK.
        by apply: k1_ord_lt.
      by [].
    Qed.

    Lemma L_catR k i j w1 w2:
      w1 \in L^k.+1 i (enum_val (k1_ord k)) ->
      w2 \in L^k (enum_val (k1_ord k)) j ->
      w1++w2 \in L^k.+1 i j.
    Proof.
      rewrite /L -3!topredE /=.
      rewrite dfa_run'_cat.
      move => /andP [] /eqP H0 H1 /andP [] /eqP H2 H3.
      case: w1 H0 H1 => [|v1 w1] H0 H1.
        rewrite /= in H0.
        rewrite H0 /= H2 eq_refl /=.  
        eapply allbutlast_impl.
        move => x. by eapply (@ltnW ((enum_rank x)) k).
        exact: H3.
      rewrite last_cat.
      case: w2 H2 H3 => [|v2 w2] H2 H3.
        rewrite /= in H2.
        rewrite -H2 H0 /= eq_refl /=.
        rewrite cats0.
        exact H1.

      rewrite H0 H2 eq_refl andTb.
      eapply all_allbutlast_cat.
        apply: (allbutlast_last _ i) => //. 
        rewrite H0. 
        rewrite enum_valK.
        by apply: k1_ord_lt.
        eapply allbutlast_impl.
          move => x.
        by eapply (@ltnW ((enum_rank x)) k).
      by [].
    Qed.
  End L.
            

  Section R.

    Lemma Conc_assoc r s t (w: word char): (w \in Conc r (Conc s t)) = (w \in Conc (Conc r s) t).
    Proof.
      rewrite -topredE -topredE /=.
      apply/concP/concP.
        move => [] v1 Hr [] v23 /concP [] v2 Hs [] v3 Ht H0 H1.
        exists (v1++v2).
        apply/concP.
        exists v1 => //.
          by exists v2.
        exists v3 => //.
        by rewrite -catA H1 H0.

      move => [] v12 /concP [] v1 Hr [] v2 Hs H0 [] v3 Ht H1.
      exists v1 => //.
      exists (v2 ++ v3).
        apply/concP.
        exists v2 => //.
        exists v3 => //.
      by rewrite H1 catA H0.
    Qed.

    Lemma Conc_Star_idem r (w: word char): w \in Conc r (Star r) -> (w \in Star r).
    Proof.
      rewrite -topredE -topredE /=.
      move/concP.
      move => [] v1 H1 [] v2 /starP [] vv H2 H3 H4.
      case: v1 H1 H4 => [|v v1] H1 H4.
        apply/starP.
        exists vv => //.
        by rewrite H4 H3. 
      apply/starP.
      exists ([::(v::v1)]++vv).
        by rewrite /= H2 andbT H1.
      by rewrite H4 H3.
    Qed.

      
    Lemma R_catL k i j w1 w2:
      w1 \in R^k i  (k1_ord k) ->
      w2 \in R^k.+1 (k1_ord k) j ->
      w1++w2 \in R^k.+1 i j.
    Proof.
      rewrite /=.
      move => H0.
      rewrite Plus_dist => /orP [].
        rewrite Conc_assoc.
        rewrite -topredE /=.
        move/concP => [] v1.
        move/Conc_Star_idem => H1 [] v2 H2 H3.
        rewrite Plus_dist.
        apply/orP. left.
        rewrite -topredE /=.
        apply/concP.
        exists w1 => //.
        exists w2 => //.
        apply/concP.
        exists (v1) => //.
        exists (v2) => //.

      rewrite Plus_dist.
      move => H1.
      apply/orP. left.
      rewrite -topredE /=.
      apply/concP.
      exists w1 => //.
      exists w2 => //.
      apply/concP.
      exists [::] => //.
      exists w2 => //.
    Qed.

    Lemma R_nil k i: [::] \in R^k i i.
    Proof.
      elim: k i => [|k IHk] i.
        rewrite /= eq_refl /= Plus_dist -topredE /=.
        apply/orP. by right.
      by rewrite /= Plus_dist IHk orbT.
    Qed.
      
  End R.
  
  Lemma R_L_star k vv:
    
    (forall (i j : 'I_#|A|) (w : word char),
        w \in R^k i j -> w \in L^k (enum_val i) (enum_val j)) ->
     all [predD mem_reg (R^k (k1_ord k) (k1_ord k)) & 
          eps (symbol:=char)] vv ->
     flatten vv \in L^k.+1 (enum_val (k1_ord k)) (enum_val (k1_ord k)).
  Proof.
    move => IHk.
    elim: vv => [|v vv IHvv].
      by rewrite /= -topredE /L /= eq_refl.
    rewrite /= => /andP [] /andP [].
    rewrite -topredE /= /eps /= => H0.
    move => H1.
    move/IHvv.
    apply: L_catL.
    apply: IHk.
    by [].
  Qed.
  
  Lemma R_L k i j w: w \in R^k i j -> w \in L^k (enum_val i) (enum_val j).
   Proof.
    elim: k i j w => [|k IHk] i j w.
      case_eq (i==j) => H0 /=.
        rewrite H0 /=.
        rewrite Plus_dist => /orP [].
          rewrite foldr_Plus => /orP [] //.
          move/hasP => [] r /mapP [] a.
          rewrite mem_filter /= => /andP [] H1 _ ->.
          rewrite -topredE /= /atom /= => /eqP ->.
          by rewrite -topredE /= /L /= H1.
        rewrite -topredE /= /eps /= => /eqP ->.
        move/eqP: H0 => ->.
        by rewrite -topredE /= /L /= eq_refl.
      rewrite H0.
      rewrite foldr_Plus => /orP [] //.
      move/hasP => [] r /mapP [] a.
      rewrite mem_filter /= => /andP [] H1 _ ->.
      rewrite -topredE /= /atom /= => /eqP ->.
      by rewrite -topredE /= /L /= H1.

    rewrite /= Plus_dist => /orP [].
      rewrite -topredE /= => /concP [] w1 /IHk H1 [] w23.
      move => /concP [] w2 H2 [] w3 /IHk H3.
      move => Eq1 Eq2.
      move/starP: H2 => [] vv Hvv Eqvv.
      pose k' := enum_val (k1_ord k).
      assert (w2 \in L^k.+1 k' k').
        rewrite Eqvv.
        by apply: R_L_star.
      rewrite Eq2.
      apply: L_catL => //. 
      rewrite Eq1.
      by apply: L_catR.      
    move/IHk.
    by apply: L_monotone.
  Qed.

  Lemma L_R1 k i j w: 
    (forall (i j : 'I_#|A|) (w : word char),
        w \in L^k (enum_val i) (enum_val j) -> w \in R^k i j) ->
    w \in L^k.+1 (enum_val i) (enum_val j) ->
    w \in R^k.+1 i j.
  Proof.
    move => IHk.
    rewrite /L -topredE [topred _]/=.
    move: (allbutlast_split _ (fun x => enum_rank x < k) (dfa_run' A (enum_val i) w)) => [] xx.
    elim: xx w => [|xs xx IHxx] w.
      destruct w => //.
                      
      rewrite Plus_dist /= => _ /andP [].
      move/eqP/(f_equal enum_rank).
      rewrite 2!enum_valK => ->.
      by rewrite R_nil orbT.

    destruct xs as [|x xs].
      destruct xx as [|ys xx] => //.    
        move/andP => [].
        destruct w as [|a w] => //.
        move => _ _ /= /andP [].
        move/eqP/(f_equal enum_rank).
        rewrite 2!enum_valK => ->.
        by rewrite Plus_dist R_nil orbT.
      by rewrite /allbutlast /= 2!andbF. 
     
    destruct xx as [|ys xx] => //.    
      move/andP => /= [] /eqP H0 /andP [] /andP [] H1 _.
      rewrite -cat_cons in H0.
      move: (dfa_run'_cat' _ _ _ _ _ H0).
      move => [] w1 [] w2 [] H2 [].
      move => H3 H4 H5. 
      destruct w2 => //.
      rewrite cats0 in H2.
      subst.
      move => /andP [] H6 H7.
      assert (w1 \in L^k (enum_val i) (enum_val j)).
        rewrite /L /= -topredE /=.
        rewrite H6 /=.
        by rewrite H3 H1.
      apply/orP. right.
      by apply: IHk.
    rewrite /= => /andP [] /eqP H0.
    rewrite -cat_cons in H0.
    move: (dfa_run'_cat' _ _ _ _ _ H0).
    move => [] [|a w1] [] w2 [] H2 [] //.
    
    /andP [] /andP [] H1 /andP [] H2 H3 H4 /andP [].
      
      
  Lemma L_R k i j w: w \in L^k (enum_val i) (enum_val j) -> w \in R^k i j.
  Proof.
    elim: k i j w => [|k IHk] i j w.
      rewrite -topredE /L /= => /andP [] H0 H1.
      move: (allbutlast_pred0 _ (fun x => ltn0 (enum_rank x)) H1).
      case: w H0 H1 => [|a [|w]] //= /eqP H0 H1 _.
        assert (i==j).
          by rewrite -(enum_valK i) H0 enum_valK.
        rewrite H H0.
        rewrite Plus_dist.
        by rewrite orbT.
      case_eq (i==j) => H2; rewrite H2.
        rewrite Plus_dist orbF.
        rewrite foldr_Plus orFb.
        apply/hasP. exists (Atom a).
          apply/mapP. exists a => //.
          rewrite mem_filter /=.
          by rewrite H0 eq_refl mem_enum. 
        by rewrite -topredE /= /atom /= eq_refl.

      rewrite foldr_Plus orFb.
      apply/hasP. exists (Atom a).
        apply/mapP. exists a => //.
        rewrite mem_filter /=.
        by rewrite H0 eq_refl mem_enum. 
      by rewrite -topredE /= /atom /= eq_refl.

      
    by apply: L_R1.
  Qed.

     
                                                     

      
      rewrite /L /= => /andP [].
      remember (dfa_run' A (enum_val i) w) as xs.
      move => H0 H1.

      move: (allbutlast_split _ (fun x => enum_rank x < k) xs) => [] xx.

      rewrite Plus_dist. 

      rewrite Heqxs.
      elim: xx w xs Heqxs H0 H1 => [|x xx IHxx] w xs Heqxs H0 H1; move => /andP [] /eqP H2 /andP [] H3 H4.
        rewrite Heqxs H2 /= in H0.
        destruct w => //.
        move/eqP/(f_equal enum_rank): H0.
        rewrite 2!enum_valK => ->.
        by rewrite R_nil orbT.


        

      rewrite /= in H2.  
      assert (dfa_run' A (enum_val i) w = x ++ flatten xx).
        symmetry.
        by rewrite -H2 -Heqxs.
        
      move/dfa_run'_cat': (H).
      move => [] w1 [] w2 [] H5 [] H6 H7.
      case: w1 H5 H6 => [|a w1] H5 H6;
        case: x H H3 H4 H2 Heqxs H7 H6 => [|x' x] H H3 H4 H2 Heqxs H7 H6 //.
                                                
        apply allbutlast_cons'' in H4.
        rewrite andFb orbF in H4.
        move/eqP/size0nil in H4.
        assert(i=j).
          rewrite H4 /= in H2.
          rewrite Heqxs H2 /= in H0.
          move/eqP in H0.
          move: H0. move/(f_equal enum_rank).
          by rewrite 2!enum_valK.
        rewrite H8.

        subst. 
        simpl in *.
        destruct w2 => //.
        by rewrite R_nil orbT.
        
      assert ((a::w1) \in L^k (enum_val i) (enum_val (k1_ord k))).
      move: H3.
      
      rewrite /L /= => /andP [] H8 H9.
      rewrite -topredE [topred _]/=.
      simpl in *.
      rewrite H6.
      destruct w => //.
      simpl in H.
      inversion H.
      
      


      