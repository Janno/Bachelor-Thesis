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
    
  Lemma allbutlast_split p y xs:
    p (last y xs) == false -> 
    exists xx,
      (xs == flatten xx) &&
      (all [predD (allbutlast p) & (@eps X)] xx &&
      all (fun xs' => p (last (last y xs) xs') == false) xx).
  Proof.
    elim: xs y => [|x xs IHxs] y.
      exists [::] => //.
    rewrite last_cons.
    move => H0.
    case: (IHxs _ H0) => xx /andP [] /eqP H1 /andP [] H2 H3.

    case_eq (p x) => H4.
      case: xx H1 H2 H3 => [|z xx] /= H1 H2 H3.
        exists [::[::x]].
        rewrite H1 /= eq_refl /=.
        move/eqP in H0.
        by rewrite -H0 H1 /= eq_refl.
      exists ((x::z)::xx).
      rewrite H1 /= eq_refl /=.
      move: H2 => /andP [] /andP [] H5 H6 H7.
      rewrite -topredE /= H7 allbutlast_cons => //.
      move: H3 => /andP [] H8 H9.

      case: z H1 H5 H6 H7 H8 => // z zz H1 H5 H6 H7 H8.
      
      rewrite last_cons in H8.
      by rewrite H8 -H1 H9.
    exists ([::x]::xx). 
    by rewrite /= H4 {1}H1 eq_refl H2 eq_refl H3 /=.
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


    
      