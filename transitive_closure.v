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

  (* p => q -> allbutlast p -> allbutlast q *)
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

  (* if at least one element in xs is actually
     applied to p we can extract that application. *)
  Lemma allbutlast_cons' p x y xs: allbutlast p (x::y::xs) -> p x && allbutlast p (y::xs).
  Proof.
    elim: xs x => [|z xs IHxs] x //. 
  Qed.
  
  (* if p holds everywhere on xs, it also holds
     for all but the last element *)
  Lemma all_allbutlast p xs: all p xs -> allbutlast p xs.
  Proof.
    elim: xs => [|x xs IHxs] //.
    move => /= /andP [] H0 /IHxs.
    by apply: allbutlast_cons.
  Qed.

  (* we can either extract an application of p x or
     x is the last element in x::xs (i.e. xs is empty). *)
  Lemma allbutlast_cons'' p x (xs: seq X): allbutlast p (x::xs) -> (size xs == 0) || (p x && allbutlast p xs). 
  Proof.
    elim: xs x => [|y xs IHxs] x.
      by [].
    by rewrite orFb.    
  Qed.

  (* all .. + allbutlast .. -> allbutlast (.. + ..)  *)
  Lemma all_allbutlast_cat p xs ys: all p xs -> allbutlast p ys -> allbutlast p (xs++ys).
  Proof.
    elim: xs => [|x xs IHxs].
      by rewrite /= => _.
    rewrite /= => /andP [] H0. 
    move => H1 H2. move: (IHxs H1 H2).
    by apply: allbutlast_cons.
  Qed.

  (* with p (last xs) we can extend allbutlast to all. *)
  Lemma allbutlast_last p x xs: allbutlast p xs -> p (last x xs) -> all p xs.
  Proof.
    elim: xs x => [|y xs IHxs] x //.
    case: xs IHxs => [|z xs] IHxs.
      by rewrite /allbutlast /= => -> ->.
    move/allbutlast_cons'/andP => [] H0 H1 H2.
    move: (IHxs x H1 H2).
    by rewrite /= H0 => /andP [] ->.
  Qed.

  (* constant false can only hold for one element or fewer. *)
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


Section TransitiveClosure.

  Variable char: finType.
  Variable A: dfa char.
  
    Section Misc.
      (* easy splitting for the (Plus r s) predicate *)
      Lemma Plus_dist r s (w: word char): w \in Plus r s = (w \in r) || (w \in s). 
      Proof. by rewrite -topredE. Qed.

      (* easy splitting for foldr over Plus *)
      Lemma foldr_Plus r rs (w: word char):
        w \in foldr (@Plus char) r rs = (w \in r) || has (fun r => w \in r) rs. 
      Proof.
        elim: rs r => [|s rs IHrs] r /=. 
          by rewrite orbF.
        rewrite orbCA -IHrs.
        by rewrite -topredE -topredE.
      Qed.
    End Misc.

  (* Some machinery for k:nat -> 'I_#|A| *)
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
  Definition k_ord k := 
    Ordinal (leq_ltn_gt0 _ _ A_has_states (minn_to_ord k #|A|.-1)).

  Lemma k_ord_lt k: k_ord k < k.+1.
  Proof.
    rewrite /k_ord /=.
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
          let k' := k_ord k in
            Plus (
                Conc (R k i k')
                     (Conc (Star (R k k' k')) (R k k' j))
              )
                 (R k i j)
    end.        

  Notation "'R^' k" := (R k) (at level 8).

  Definition L :=
    [fun k: nat =>
       [fun x y: A =>
          [pred w | 
           (last x (dfa_run' A x w) == y)
             && allbutlast (fun x => enum_rank x < k) (dfa_run' A x w) 
          ]
       ]
    ].
  Notation "'L^' k" := (L k) (at level 8).
       
  Section L.
    Lemma L_monotone k i j w: w \in L^k i j -> w \in L^(k.+1) i j.
    Proof.
      rewrite 2!in_simpl /= => /andP [] -> /=.
      apply: allbutlast_impl.
      move => x.
      by apply: (@ltnW ((enum_rank x)) k).
    Qed.

    Lemma L_nil k i : [::] \in L^k i i.
      Proof. by rewrite in_simpl /= eq_refl. Qed.

    Lemma L_nil' k i j: [::] \in L^k i j -> i = j.
    Proof. by rewrite in_simpl /= => /andP [] /eqP ->. Qed.

    
    Lemma L_cons k i j a w:
      (a::w) \in L^k.+1 i j ->
      [::a] \in L^k i (dfa_step A i a) /\
      w \in L^k.+1 (dfa_step A i a) j.
    Proof.
      elim: w k i j a => [|b w IHw] k i j a.
        move/(L_nil' k) => /= H0. 
        firstorder.
          by rewrite H0 in_simpl /= H0 eq_refl.
        rewrite H0 in_simpl.
        exact: L_nil.
      rewrite /= in_simpl /=.
      move/andP => [] H0 H1.
      apply allbutlast_cons' in H1.
      move/andP: H1 => [] H1 H2.
      firstorder; rewrite in_simpl /=.
        by rewrite eq_refl /=.
      by rewrite H0 H2.
    Qed.


    Lemma L_cat k i h j w1 w2:
      enum_rank h < k ->
      w1 \in L^k i h ->
      w2 \in L^k h j ->
      w1++w2 \in L^k i j.
    Proof.
      move => H0 /= /andP [] /eqP H1 H2 /andP [] /eqP H3 H4.
      rewrite in_simpl /=.
      rewrite dfa_run'_cat H1.
      apply/andP. split.
        by rewrite last_cat H1 H3 eq_refl.       
      apply: all_allbutlast_cat.
        apply: allbutlast_last => //.
        rewrite -H1 in H0.
        eassumption.
      exact H4.
    Qed.

    (* Split at k or don't split at all if there is no k *)
    Lemma L_split k i j a w:
      (a::w) \in L^k.+1 i j ->
      (a::w) \in L^k i j \/
      exists w1, exists w2,
        a::w = w1 ++ w2 /\
        w1 != [::] /\
        w1 \in L^k i (enum_val (k_ord k)) /\
        w2 \in L^k.+1 (enum_val (k_ord k)) j.
    Proof.
      elim: w k i j a => [|b w IHw] k i j a.
        move/L_cons => [] H0 H1.
        rewrite /= in H0.
        case_eq (dfa_step A i a == enum_val (k_ord k)) => /eqP H2.
          right.
          exists [::a]. exists [::].
          firstorder.
            by rewrite in_simpl /= H2 eq_refl.
          by rewrite -H2 H1.
        left.
        move/L_nil': H1 <-.
        rewrite in_simpl /=.
        exact: H0.
      move => H.
      move/L_cons: (H) => [] H2.
      move/andP: (H) => [] H0 H1.
      case_eq (dfa_step A i a == enum_val (k_ord k)) => H3.
        move/eqP: H3 => H3.
        (* we go through k at a, we have to split here *)
        move => H4.
        rewrite -H3.
        right.
        by exists [::a]; exists [::b&w] => //.

      (* we do not go through k at a. *)           
      move/IHw => [].
        (* 1) we do not go through k at all *)
        move => H4.
        left.
        rewrite -cat1s.
        move: (allbutlast_cons' _ _ _ _ H1) => /andP [] H5 _.
        apply: (L_cat k i (dfa_step A i a)) => //.
        rewrite ltn_neqAle.
        rewrite -ltnS H5 andbT.
        admit.
        
      (* 2) we have gone through k before *)
      move => [] w1 [] w2 [] H4 [] H5 [] H6 H7.
      right.
      exists [::a & w1]. exists (w2).
      rewrite /= H4.
      split => //. split => //. split => //.
      rewrite -cat1s.
      apply: L_cat; try eassumption.
      admit.
    Qed.
      
    Lemma L_catL k i j w1 w2:
      w1 \in L^k i (enum_val (k_ord k)) ->
      w2 \in L^k.+1 (enum_val (k_ord k)) j ->
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
        by apply: k_ord_lt.
      by [].
    Qed.

    Lemma L_catR k i j w1 w2:
      w1 \in L^k.+1 i (enum_val (k_ord k)) ->
      w2 \in L^k (enum_val (k_ord k)) j ->
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
        by apply: k_ord_lt.
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
      w1 \in R^k i  (k_ord k) ->
      w2 \in R^k.+1 (k_ord k) j ->
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

  (* R_L_star encapsulates the induction over
     the list of words matched by star (R^k k k).
     The first argument is the inductive hypothesis
     obtained from the induction over k in R_L.
   *)
  Lemma R_L_star k vv:
    (forall (i j : 'I_#|A|) (w : word char),
        w \in R^k i j -> w \in L^k (enum_val i) (enum_val j)) ->
     all [predD mem_reg (R^k (k_ord k) (k_ord k)) & 
          eps (symbol:=char)] vv ->
     flatten vv \in L^k.+1 (enum_val (k_ord k)) (enum_val (k_ord k)).
  Proof.
    move => IHk.
    elim: vv => [|v vv IHvv].
      move => H0. by apply: L_nil.
    (* v in L^k k k
       flatten vv in L^k.+1 k k *)
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
        by apply: L_nil.
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
      pose k' := enum_val (k_ord k).
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
   
  Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) :
  ( forall x, ( forall y, f y < f x -> p y) -> p x) -> forall x, p x.
  Admitted.
 
  (* w \in L^k.+1 i j -> w \in R^k.+1 i j *)
  Lemma L_R_1 k i j w:
       (forall (i j : 'I_#|A|) (w : automata.word char),
        w \in L^k (enum_val i) (enum_val j) -> w \in R^k i j) ->
        w \in L^k.+1 (enum_val i) (enum_val j) -> w \in R^k.+1 i j. 
  Proof.
    move => IHk.
    move: w i j.
    apply: (size_induction (size)) => w IHw i j.
    case: w IHw => [|a w] IHw.
      move/L_nil'/(f_equal enum_rank). 
      rewrite 2!enum_valK => ->.
      exact: R_nil.
    move/L_split => [].
      move/IHk.
      rewrite /= Plus_dist => ->.
      by rewrite orbT.
    move => [] w1 [] w2 [] H0 [] H1 [] H2 H3.
    assert (size w1 > 0).
      case: w1 H0 H1 H2 => [|b w1] H0 H1 H2 => //.
    rewrite H0.
    apply: R_catL.
      by apply: IHk.
    apply: IHw => //.
    rewrite H0 size_cat.
    rewrite -{1}(addn0 (size w2)).
    rewrite addnC.    
    by rewrite ltn_add2r.
  Qed.
    
  (* w \in L^k i j -> w \in R^k i j *)
  Lemma L_R k i j w: w \in L^k (enum_val i) (enum_val j) -> w \in R^k i j. 
  Proof.
    elim: k i j w => [|k IHk] i j w.
      assert ((fun x:A => enum_rank x < 0) =1 pred0) => //.
      rewrite in_simpl /= => /andP [] H0 /(allbutlast_pred0 _ H).  
      move: H0. case: w => [|a [|b w]] => /= H0 _ //.
        move/eqP/(f_equal enum_rank) in H0.
        rewrite 2!enum_valK in H0.
        by rewrite H0 eq_refl Plus_dist foldr_Plus 2!in_simpl /= orbT.
      case_eq (i==j) => H1.
        move/eqP in H1.
        rewrite H1 eq_refl /=.
        rewrite Plus_dist foldr_Plus 2!in_simpl orbF /=. 
        apply/hasP. exists (Atom a).
          apply/mapP. exists a => //.
          rewrite mem_filter.
          rewrite H1 in H0.
          by rewrite mem_enum andbT /= H0.
        by rewrite in_simpl /= eq_refl.
      rewrite H1.
      rewrite foldr_Plus orFb.
      apply/hasP. exists (Atom a).
        apply/mapP. exists a => //.
        rewrite mem_filter.
        by rewrite mem_enum andbT /= H0.
      by rewrite in_simpl /= eq_refl.
    by apply: L_R_1.
  Qed.
  
    
    
End TransitiveClosure.
