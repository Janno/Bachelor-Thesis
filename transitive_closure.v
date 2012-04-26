Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool.
Require Import automata misc regexp.

Set Implicit Arguments.

(* http://krchowdhary.com/toc/dfa-to-reg-exp.pdf *)



Section TransitiveClosure.

Variable char: finType.
Variable A: nfa char.



Lemma mem_der_Plus r s w : mem_der (@Plus char r s) w = mem_der r w || mem_der s w.
Proof. elim: w r s => [|a w IHw] r s //=. Qed.

Lemma der_Plus a r s : der a (@Plus char r s) = Plus (der a r) (der a s).
Proof. by []. Qed.

Lemma mem_der_Conc r s (w1 w2: word char) : mem_der r w1 ->  mem_der s w2 ->
mem_der (Conc r s) (w1 ++ w2).
Proof.
elim: w1 r s w2 => [|a w1 IHw1] r s w2 B C /=.
  elim: w2 r s B C => [|b w2 IHw2] /= r s -> //. 
  move => C. rewrite mem_der_Plus.
  by rewrite C orbT.
case: (has_eps r) => /=.
  rewrite mem_der_Plus. by rewrite IHw1 => //.
by apply/IHw1 => //.
Qed.


Lemma der_fold_Plus (r: regular_expression char) rs (a: char): der a (foldr (@Plus char) r rs) = foldr (@Plus char) (der a r) (map (der a) rs).
Proof.
elim: rs r a => [|s rs IHrs] r a //=.
by rewrite IHrs.
Qed.

Lemma mem_der_fold_Plus r rs w: mem_der r w || has (fun r => mem_der r w) rs = mem_der (foldr (@Plus char) r rs) w.
Proof.
  elim: rs r w => [|s rs IHrs] r w.
    apply/orP/idP.
      move => [] //=.
    by firstorder.
  rewrite /= mem_der_Plus.
  apply/orP/idP.
    move => [] H0; apply/orP.
      right. rewrite -IHrs. by rewrite H0.
    apply/orP. move/orP: H0 => [].
      by move => ->.
    rewrite -IHrs => ->.
    apply/or3P. by firstorder.
  move/orP => [].
    move => ->. by firstorder.
  rewrite -IHrs. move/orP => [].
    by firstorder.
  move => ->. right. by rewrite orbT.
Qed.
  
Lemma has_eps_fold_Plus r rs: has_eps r || has (@has_eps _) rs = has_eps (foldr (@Plus char) r rs).
Proof.
  elim: rs r => [|s rs IHrs] r.
    by rewrite orbF.
  simpl. rewrite -(IHrs r).
  by rewrite orbCA.
Qed.

Lemma mem_der_Void w: mem_der (@Void char) w = false.
Proof. elim: w => [|a w IHw] //=. Qed.

Lemma mem_der_Eps w: mem_der (@Eps char) w -> w = [::].
Proof. elim: w => [|a w IHw] //=. by rewrite mem_der_Void. Qed.

Lemma mem_der_Atom a w: mem_der (@Atom char a) w -> w = [::a].
Proof. elim: w a => [|b w IHw] a //=. case_eq (b==a).
  by move/eqP => -> /mem_der_Eps ->.
by rewrite mem_der_Void.
Qed.

Lemma cons_eq a b (w1 w2: word char):
  a::w1 = b::w2 -> a=b /\ w1 = w2.
Proof.
  move => H0.
  move: (f_equal (head a) H0) => /=.
  by move: (f_equal behead H0) => /=.                                   
Qed.
                                    
Lemma mem_der_Conc3 r s w:
(exists w1, exists w2, w1 ++ w2 = w /\ mem_der r w1 /\ mem_der s w2) -> mem_der (@Conc char r s) w.
Proof.
  elim: w r s => [|a w IHw] r s /=.
    move => [] w1 [] w2 [].
    case: w1 => [] //. case: w2 => [] //=.
    by move => _ [] -> ->.
  move => [] w1 [] w2 [].
  case_eq (has_eps r) => H0.
    rewrite mem_der_Plus.
    case: w1 => [|b w1].
      move => /= -> [] _ /= ->.
      by rewrite orbT.
    rewrite cat_cons.
    move/cons_eq => [] -> <- [] H1 H2.
    by rewrite mem_der_Conc.
  case: w1 => [|b w1].
    move => _ [] /=. by rewrite H0. 
  rewrite cat_cons.
  move/cons_eq => [] -> <- [] H1 H2.
  by rewrite mem_der_Conc.  
Qed.


Lemma mem_der_Conc2 r s w: mem_der (@Conc char r s) w -> exists w1, exists w2, w1 ++ w2 = w /\ mem_der r w1 /\ mem_der s w2.
Proof.
  elim: w r s => [|a w IHw] r s /=.
    move => /andP [H0 H1].
    exists [::]. by exists [::].
  case_eq (has_eps r) => H0.
    rewrite mem_der_Plus => /orP [].
      move/IHw => [] w1 [] w2 [] <- [] H1 H2.
      exists (a::w1). exists w2.
      split.
        by [].
      by rewrite /= H1 H2.
    move => H1.
    exists [::]. exists (a::w).
    split.
      by [].
    by rewrite /= H0 H1.
  move/IHw => [] w1 [] w2 [] <- [] H1 H2.
  exists (a::w1). exists w2.
  split.
    by [].
  by rewrite /= H1 H2.
Qed.

Lemma mem_der_Star r w: mem_der (@Star char r) w -> w = [::] \/ mem_der (Conc r (Star r)) w.
Proof.
  elim: w r => [|a w IHw] r /=.
    by firstorder.
  move/mem_der_Conc2 => [] w1 [] w2 [] H0 [] H1 H2.
  right.
  rewrite -H0.
  case_eq (has_eps r) => H3.
    rewrite mem_der_Plus.
    apply/orP. left.
    by rewrite mem_der_Conc.
  by rewrite mem_der_Conc.
Qed.
  
Lemma minn_to_ord m n: minn m n <= n.
Proof. elim: n m => [|n IHn] m /=.
  by rewrite /minn.
rewrite /minn.
case_eq (m < n.+1).
  by apply: ltnW.
move => _. by apply: ltnSn.
Qed.

Lemma noname n m: m > 0 -> n <= m.-1 -> n < m.
Proof.  elim: m n => [|m IHm] n //=. Qed.

Lemma A_has_states: #|A| > 0.
apply/card_gt0P.
by exists (nfa_s0 A).
Qed.
  
(* this represents k in 'I_#|A| *)
Definition k1_ord k := 
  Ordinal (noname _ _ A_has_states (minn_to_ord k #|A|.-1)).
  
Fixpoint R (k: nat) (i j: 'I_#|A|) : regular_expression char :=
match k with
|   0  => 
      let r := foldr (@Plus _) (Void _) (map (@Atom _) (filter [pred a | nfa_step A (enum_val i) a (enum_val j)] (enum char))) in
      if i == j then Plus r (Eps _) else r
| k.+1 =>
    let k' := k1_ord k in
    Plus (
        Conc (R k i k')
             (Conc (Star (R k k' k')) (R k k' j))
        )
        (R k i j)
end.        

Definition nfa_R (k: nat) (i j: 'I_#|A|) : nfa char :=
nfaI
  char
  (A)
  (nfa_s0 A)
  [pred x | x == enum_val j]
  (fun x a y => nfa_step A x a y && ((enum_rank x == i) || (enum_rank x < k)) && ((enum_rank y == j) || (enum_rank y < k))).

Lemma nfa_R_correct2_0 w i j: mem_der (R 0 i j) w -> nfa_accept (nfa_R 0 i j) (enum_val i) w.
Proof.
  elim: w i j => [|a w IHw] i j.
    simpl.
    case_eq (i==j).
      by move/eqP => ->.
    move => H0. rewrite H0.
    rewrite -has_eps_fold_Plus. 
    rewrite orFb.
    move/hasP => [] r.
    by move/mapP => [] a _ ->.
  case_eq (i==j) => /=.
    move/eqP => ->. rewrite eq_refl /=.
    rewrite der_fold_Plus mem_der_Plus.
    rewrite -mem_der_fold_Plus.
    rewrite mem_der_Void.
    rewrite orbF orFb.
    move/hasP => [] r /mapP [] s /mapP [] c.
    rewrite mem_filter /= => /andP [] H0 _.
    move => -> -> /=.
    case_eq (a==c) => /=.
      move/eqP => ->.
      move/mem_der_Eps => H1.
      rewrite H1. rewrite H1 in IHw.
      apply/existsP. exists (enum_val j).
      by rewrite enum_valK eq_refl H0 /= eq_refl.
    by rewrite mem_der_Void.  
  move => H0. rewrite H0.  
  rewrite der_fold_Plus -mem_der_fold_Plus mem_der_Void orFb.
  move/hasP => [] r /mapP [] s /mapP [] c.
  rewrite mem_filter => /= /andP [] H1 _.
  move => -> -> /=.
  case_eq (a==c) => /=.
    move/eqP => ->. move/mem_der_Eps => ->.
    apply/existsP. exists (enum_val j).
    by rewrite 2!enum_valK 2!eq_refl /= H1 eq_refl.
  by rewrite mem_der_Void.  
Qed.

Lemma nfa_R_monotone k w i j x: nfa_accept (nfa_R k i j) x w -> nfa_accept(nfa_R k.+1 i j) x w.
Proof.
  elim: w k i j x => [|a w IHw] k i j x //=.
  move/pred0Pn.
  move => [] y /andP [] /andP [] /andP [] H0 /orP [] H1 /orP [] H2 H3;
  apply/pred0Pn; exists y.
        rewrite H0 H1 H2 /=.
        by apply: IHw.
      rewrite H0 H1 (leqW H2) orbT /=.
      by apply: IHw.
    rewrite H0 (leqW H1) H2 orbT /=.
    by apply: IHw.
  rewrite H0 (leqW H1) (leqW H2) 2!orbT /=.
  by apply: IHw.
Qed.

Lemma enum_rank_ltn (x: A): enum_rank x <= #|A|.-1.
Proof.
  rewrite -(leq_add2r 1) 2!addn1.
  rewrite (prednK A_has_states).
  exact: (ltn_ord (enum_rank x)) => /=.
Qed.  

Lemma k1_ord_leq_k k: nat_of_ord (k1_ord k) <= k.
Proof.
  rewrite /k1_ord.
  case_eq (k <= #|A|.-1) => H0 /=.
    by rewrite (minnl H0).
  move: (leq_total k #|A|.-1).
  rewrite H0 orFb => H1.
  by rewrite (minnr H1).
Qed.
  
Lemma nfa_R_lpath_start k i j x xs a w:
  nfa_lpath (nfa_R k i j) x xs (a::w) ->
  (enum_rank x == i) || (enum_rank x < k).
Proof.
  elim: xs => [|y xs IHxs] //.
  by move => /= /andP [] /andP [] /andP [].
Qed.          

Lemma nfa_R_lpath_empty k i j x xs:
  nfa_lpath (nfa_R k i (k1_ord k)) x xs [::] ->
  nfa_lpath (nfa_R k i j) x xs [::].
Proof.
  elim: xs x => [|y xs IHxs] x //=.
Qed.  

Lemma nfa_R_lpath_empty2 k i j x xs:
  nfa_lpath (nfa_R k i j) x xs [::] ->
  nfa_lpath (nfa_R k i (k1_ord k)) x xs [::].
Proof.
  elim: xs x => [|y xs IHxs] x //=.
Qed.  

Lemma nfa_R_correct2' k i j x xs w : 
  nfa_lpath (nfa_R k i (k1_ord k)) x xs w ->
  nfa_lpath (nfa_R k.+1 i j) x xs w.
Proof.
  elim: w k i j x xs => [|a w IHw] k i j x xs; elim: xs => [|y xs _]  //.
  move => /= /andP [] /andP [] /andP [] H0 /orP [] H2 /orP [] H3 H4;
  rewrite H0 2!ltnS.
        rewrite H2 (eqP H3) (k1_ord_leq_k) orbT /=.
        by apply: IHw.
      rewrite H2 (ltnW H3) orbT /=.
      by apply: IHw.
    rewrite (ltnW H2).
    move/eqP: H3 => /(@f_equal 'I_#|A| nat (@nat_of_ord #|A|)) /eq_leq H3.
    rewrite (leq_trans H3 (k1_ord_leq_k k)) 2!orbT /=.
    by apply: IHw.
  rewrite (ltnW H2) (ltnW H3) 2!orbT /=.
  by apply: IHw.
Qed.        

Lemma nfa_R_correct2'' k i j x xs w : 
  nfa_lpath (nfa_R k (k1_ord k) j) x xs w ->
  nfa_lpath (nfa_R k.+1 i j) x xs w.
Proof.
  elim: w k i j x xs => [|a w IHw] k i j x xs; elim: xs => [|y xs _]  //.
  move => /= /andP [] /andP [] /andP [] H0 /orP [] H2 /orP [] H3 H4;
  rewrite H0 2!ltnS.
        move/eqP: H2 => /(@f_equal 'I_#|A| nat (@nat_of_ord #|A|)) /eq_leq H5.
        rewrite H3 (leq_trans H5 (k1_ord_leq_k k)) orbT /=.
        by apply: IHw.
      move/eqP: H2 => /(@f_equal 'I_#|A| nat (@nat_of_ord #|A|)) /eq_leq H5.
      rewrite (ltnW H3) (leq_trans H5 (k1_ord_leq_k k)) 2!orbT /=.
      by apply: IHw.
    rewrite (ltnW H2) H3 orbT /=.
    by apply: IHw.
  rewrite (ltnW H2) (ltnW H3) 2!orbT /=.
  by apply: IHw.
Qed.

Lemma nfa_R_correct2''' k i j x xs w : 
  nfa_lpath (nfa_R k (k1_ord k) (k1_ord k)) x xs w ->
  nfa_lpath (nfa_R k.+1 i j) x xs w.
Proof.
  elim: w k i j x xs => [|a w IHw] k i j x xs; elim: xs => [|y xs _]  //.
  move => /= /andP [] /andP [] /andP [] H0 /orP [] H2 /orP [] H3 H4;
  rewrite H0 2!ltnS.
        move/eqP: H2 => /(@f_equal 'I_#|A| nat (@nat_of_ord #|A|)) /eq_leq H5.
        rewrite (leq_trans H5 (k1_ord_leq_k k)) orbT /=.
        move/eqP: H3 => /(@f_equal 'I_#|A| nat (@nat_of_ord #|A|)) /eq_leq H6.
        rewrite (leq_trans H6 (k1_ord_leq_k k)) orbT /=.
        by apply: IHw.
      move/eqP: H2 => /(@f_equal 'I_#|A| nat (@nat_of_ord #|A|)) /eq_leq H5.
      rewrite (ltnW H3) (leq_trans H5 (k1_ord_leq_k k)) 2!orbT /=.
      by apply: IHw.
    rewrite (ltnW H2) orbT /=.
    move/eqP: H3 => /(@f_equal 'I_#|A| nat (@nat_of_ord #|A|)) /eq_leq H6.
    rewrite (leq_trans H6 (k1_ord_leq_k k)) orbT /=.
    by apply: IHw.
  rewrite (ltnW H2) (ltnW H3) 2!orbT /=.
  by apply: IHw.
Qed.

(*
Lemma mem_der_Star_ind (p: word char -> Prop) r:
  p [::] ->
  (forall w1 w2, mem_der r w1 -> mem_der (Star r) w2 -> p w2 -> p (w1 ++ w2)) ->
  forall (w: word char), mem_der (Star r) w -> p w.
Proof.
  move => H0 H1 w.
  move/mem_der_Star => [].
    by move => ->.
  move/mem_der_Conc2 => [] w1 [] w2 [] <- [].
  move => H2 H3.
  apply: H1 => //.
          
    
  elim: w2 w1 => [|a w2 IHw2] w1.
    move => H2 H3.
    by apply: H1.
  move => H2 H3.
  move: (mem_der_Conc _ _ w1 (a::w2) H2 H3).    
  rewrite -cat_rcons.
  move/mem_der_Conc2 => [] w3 [] w4 [] .
  apply: IHw2.
*)

(*
Lemma nfa_R_correct2_Star k i j w1 w2:
  (forall (w : word char) (i j : 'I_#|A|),
        mem_der (R k i j) w -> nfa_accept (nfa_R k i j) (enum_val i) w) ->
  mem_der (Star (R k (k1_ord k) (k1_ord k))) (w1 ++ w2) -> exists xs, nfa_lpath (nfa_R k.+1 i j) (enum_val (k1_ord k)) xs (w1 ++ w2) /\ last (enum_val (k1_ord k)) xs = enum_val (k1_ord k).
Proof.
  move => H0.

  elim: w1 w2 i j k H0 => [|a w1 IHw1] w2 i j k H0.
  
  
  elim: w i j => [|a w IHw] i j.
    move => _. by exists [::].
  simpl.
  
  move/mem_der_Conc2 => [] w1 [] w2 [] H1 [].
  rewrite -H1 in IHw. rewrite -H1.
  move => H2.
    assert (mem_der (R k (k1_ord k) (k1_ord k)) (a::w1)) => //.
  
  elim: w2 w1 H1 IHw H2 H => [|b w2 IHw2] w1 H1 IHw H2 H.
    move => _.
    move/nfa_accept_lpath: (H0 _ _ _ H) => [] xs [].
    move/(nfa_R_correct2''' _ i j) => H3.
    move/eqP => H4.
    rewrite cats0. 
    by exists xs.

  move => /= /mem_der_Conc2 [] w3 [] w4 [] H3 [].
    
Admitted.
*)

Lemma R_monotone k i j w: mem_der (R k i j) w -> mem_der (R k.+1 i j) w.
Proof. rewrite /= mem_der_Plus => ->. by rewrite orbT. Qed.

Check seq_ind.

Lemma cat_ind (P: word char -> Prop):
  P [::] ->
  (forall w1 w2, P w2 -> P (w1 ++ w2)) ->
  forall w, P w.
Proof.
  move => H0 H1 w.
  elim: w => [|a w IHw] //.
  rewrite -cat1s.
  by apply: H1.
Qed.


Lemma R0_cons i j a w:
  mem_der (R 0 i j) (a::w) ->
  w = [::] /\ nfa_step (nfa_R 0 i j) (enum_val i) a (enum_val j).
Proof.
  move => /=.
  rewrite fun_if der_Plus der_fold_Plus -map_comp.
  rewrite fun_if if_arg mem_der_Plus -mem_der_fold_Plus mem_der_Void orFb.
  rewrite 2!enum_valK 2!eq_refl /= 2!andbT.
  case_eq (i == j) => H1; rewrite H1.
    move/orP => [] //.
    move/hasP => [] r /mapP [] b. rewrite mem_filter => /andP [] /=.
    case_eq (a == b).
      by move/eqP => -> -> _ -> /mem_der_Eps ->.
    move => _ _ _ ->.
    by rewrite mem_der_Void.
  move/hasP => [] r /mapP [] b. rewrite mem_filter => /andP [] /=.
  case_eq (a == b).
    by move/eqP => -> -> _ -> /mem_der_Eps ->.
  move => _ _ _ ->.
  by rewrite mem_der_Void.
Qed.  
  
Lemma R0_nil i j:
  mem_der (R 0 i j) [::] =
  (j == i).
Proof.
  rewrite /= fun_if -has_eps_fold_Plus /= orbT.
  case_eq (i == j) => H0; rewrite H0.
    by rewrite eq_sym H0.
  apply/hasP/idP.
    by move => /= [] r /mapP [] a _ ->.
  by rewrite eq_sym H0.
Qed.
                     
Lemma R_der_step k i j a w m:
  mem_der (R k i j) (a::w) ->
  nfa_step (nfa_R k i j) (enum_val i) a (enum_val m) ->
  mem_der (R k m j) w.
Proof.
  elim: k w i j a m => [|k IHk] w i j a m H0.
    move: (R0_cons _ _ _ _ H0) => [] H1 H2.
    rewrite H1. rewrite H1 in H0.
    move => /andP [] /andP [] H3 /orP [] H4 /orP [] H5 //.
    rewrite enum_valK in H5.
    by rewrite R0_nil eq_sym H5.
  move: H0. rewrite /= mem_der_Plus.
  move/orP => [].
    case_eq (has_eps (R k i (k1_ord k))) => H0.
    rewrite mem_der_Plus => /orP [].
    move/mem_der_Conc2 => [] w1 [] w2 [] <-.
    
    move => /andP [] /andP [] H3 /orP [] H4 /orP [] H5 //.
           rewrite enum_valk
           
    
      

Lemma R_der k i j a w:
  mem_der (der a (R k i j)) w ->
  mem_der (R k j j) w \/ 
  exists m: 'I_#|A|,
    m < k /\
    mem_der (R k i m) [::a] /\
    mem_der (R k m j) w.
Proof.
  elim: k i j a w => [|k IHk] i j a w.
    move => /=.
    rewrite eq_refl.
    rewrite fun_if der_Plus der_fold_Plus.
    case_eq (i==j) => H0; rewrite H0.
      move/eqP: H0 => ->.
      rewrite mem_der_Plus => /orP [].
        rewrite -mem_der_fold_Plus => /orP [].
          by rewrite mem_der_Void.
        move/hasP => [] r /mapP [] s /mapP [] b.
        rewrite mem_filter => /andP [].
        move => H0 _ -> -> /=.
        case_eq (a == b).
          move => _ /mem_der_Eps -> /=.
          left. by rewrite orbT.
        by rewrite mem_der_Void.
      by rewrite /= mem_der_Void.
    rewrite -mem_der_fold_Plus.
    move/orP => [].
      by rewrite mem_der_Void.
    move/hasP => [] r /mapP [] s /mapP [] b.
    rewrite mem_filter => /andP [].
    move => H1 _ -> -> /=.
    case_eq (a == b).
      move => _ /mem_der_Eps -> /=.
      left. by rewrite orbT.
    by rewrite mem_der_Void.
  rewrite /= mem_der_Plus => /orP [].
    case_eq (has_eps (R k i (k1_ord k))) => H0.
      rewrite mem_der_Plus => /orP [].
        right.
        exists (k1_ord k).
        split.
          by apply: k1_ord_leq_k.
        split.
          
      
      

Lemma nfa_R_correct_Star k w:
  mem_der (Star (R k (k1_ord k) (k1_ord k))) w ->
  w = [::] \/ mem_der (R k.+1 (k1_ord k) (k1_ord k)) w.
Proof.
  (*move: w k. apply: cat_ind => [|w1 w2 IHw] k.*)
  elim: w k => [|a w IHw] k.
  
    move/mem_der_Star => [].
      by firstorder.
    move/mem_der_Conc2 => [] w1 [] w2 [].
    case: w1 => [] //. case: w2 => [] //.
    by firstorder.
  rewrite 1!/= => H0.
  rewrite mem_der_Plus.
  right.
  apply/orP.
  case_eq (has_eps (R k (k1_ord k) (k1_ord k))) => H1.
    left.
    rewrite mem_der_Plus.
    apply/orP. left.
    apply: mem_der_Conc3.
    move/mem_der_Conc2: H0 => [] w1 [] w2 [] <- [] H2 H3.
    exists w1. exists w2.
    firstorder.
    apply: mem_der_Conc3.
    exists w2. exists [::].
    firstorder.
    by rewrite cats0.
  move/mem_der_Conc2: H0 => [] w1 [] w2 [] H2 [] H3 H4.
  rewrite -H2.
  elim: w2 w1 H3 H2 H4 => [|b w2 IHw2] w1 H3 H2 H4.
    right. by rewrite cats0.
  move/mem_der_Star: H4 => [] //=.
  rewrite H1 => /mem_der_Conc2 [] w3 [] w4 [] H4 [] H5 H6.
  
  
  left.
  apply: mem_der_Conc => //=.
   
    
  
Lemma nfa_R_correct2 k w i j: mem_der (R k i j) w -> nfa_accept (nfa_R k i j) (enum_val i) w.
Proof.
  elim: k w i j => [|k IHk] w i j.
    exact: nfa_R_correct2_0.
  simpl.
  rewrite mem_der_Plus.
  move/orP => [].
    move/mem_der_Conc2 => [] w1 [] w2 [] H0 [] /IHk /nfa_accept_lpath [] xs1 [] H1 H2.
    rewrite -H0. clear H0.
    move/mem_der_Conc2 => [] w3 [] w4 [] H3 [] H4 /IHk /nfa_accept_lpath [] xs2 [] H5 H6.
    rewrite -H3. clear H3.
    apply/nfa_accept_cat.
    exists xs1.
    move/eqP: H2 => /= ->.
    move: H1 => /(nfa_R_correct2' _ _ j) => -> /=.
    
    apply/nfa_accept_cat.
    exists xs2.
    apply/andP. split.
      clear H5 H6
    
    
    move: (mem_der_Star _ _ H4) => [].
      move => H7. rewrite H7.
      apply: nfa_lpath_accept.
        eapply nfa_R_correct2''.
        eassumption.
      exact: H6.
    move/mem_der_Conc2 => [] w5 [] w6 [] H7 [] /IHk H8 _.

    apply: mem_der
        
        
      
    
    exists xs2.
      move => ->. case: xs2 H5 H6 => [|x xs2] H5 H6.
      simpl.
          
      
    

  case: w IHw => [|b w] IHw.
    rewrite orFb orbF.
    move/hasP => [] r /mapP [] s /mapP [] c.
    rewrite mem_filter /= => /andP [] H0.
    move => _ -> -> /=.
    case_eq (a==c) => [/eqP ->|] //= _.
    apply/existsP. exists (enum_val j).
    by rewrite enum_valK 2!eq_refl H0.
       
            
     
Lemma nfa_R_correct2 k i j w : mem_der (R k i j) w -> nfa_fin A (enum_val j) -> nfa_accept (nfa_R k i j) (enum_val i) w.
Proof.
  elim: k w i j => [|k IHk] w i j.
    case_eq (i == j).
      move/eqP => ->.
      rewrite /= eq_refl.
      rewrite mem_der_Plus -mem_der_fold_Plus.
      move/orP => [].
        move/orP => [].
        elim: w => [|a w IHw] //=.
        
      

Lemma nfa_R_correct k (i j: 'I_#|A|) w: nfa_fin A (enum_val j) -> nfa_accept (nfa_R k i j) (enum_val i) w -> mem_der (R k i j) w.
Proof.

  elim: k w i j => [|k IHk] w i j.
    elim: w i j => [|a w IHw] i j.
      case_eq (i==j).
        move/eqP => -> H0 _ /=.
        by rewrite eq_refl /= orbT.
      move => H1 H0 /eqP /(f_equal enum_rank).
      rewrite 2!enum_valK => H2. move: H1.
      by rewrite H2 eq_refl.
    move => H0 /existsP [] y /andP [] /andP [] /orP [] H1 H2 H3.
    simpl.
    case_eq (i==j).
      move/eqP => H4. rewrite H4 eq_refl der_Plus der_fold_Plus mem_der_Plus.
      apply/orP. left.
      rewrite -mem_der_fold_Plus.
      apply/orP. right.
      
      apply: mem_der_fold_Plus.
      right.
      rewrite 2!has_map.
      apply/hasP.
      exists a.
      rewrite mem_filter.
      simpl.
      
      
      
      
      
      by rewrite eq_refl /= orbT.
      
  elim: w k i j => [|a w IHw] k i j.
    elim: k i j => [|k IHk] i j //.
    simpl.
    case_eq (i==j).
      move/eqP => -> H0 _.
      by rewrite eq_refl /= orbT.
    move => H1 H0 /eqP /(f_equal enum_rank).
    rewrite 2!enum_valK => H2. move: H1.
    by rewrite H2 eq_refl.
  move => H0 /=.
  move /eqP /(f_equal enum_rank). rewrite 2!enum_valK => ->.
  apply/orP. right.
  apply: IHk.
    exact: H0.
  by rewrite /= eq_refl.
move => H0.
rewrite /nfa_lang /=.
move/existsP => [] y /andP [] /andP [] /orP [] H1 H2 H3.
  apply: IHw.
  
  
  simpl.

  

Lemma R_correct0' x a y : dfa_step A x a = y ->
   has_eps
     (der a
        (foldr (@Plus char) (Void char)
           (map (Atom (symbol:=char))
              (filter
                 [pred a0 : char |
                  dfa_step A (enum_val (enum_rank x)) a0 ==
                  enum_val (enum_rank y)] (enum char))))).
Proof. move => H0.
  rewrite der_fold_Plus.
  apply: has_eps_fold_Plus.
  right. exists (Eps _).
  rewrite /= andbT.
  apply/mapP.
  exists (Atom a).
    apply/mapP.
    exists a.
      by rewrite mem_filter /= 2!enum_rankK H0 eq_refl andTb mem_enum.
    by [].
  by rewrite /= eq_refl.
Qed.
   

Lemma R_correct0 x a y: dfa_step A x a = y -> has_eps (der a (R 0 (enum_rank x) (enum_rank y))).
Proof.
case_eq (x == y) => /=.
  move/eqP => ->. rewrite eq_refl => /=.
  rewrite orbF. exact: R_correct0'.
move => H0.
assert (enum_rank x == enum_rank y = false).
  apply/eqP.
  move/(f_equal enum_val).
  rewrite 2!enum_rankK.
  move => H1. move: H1 H0 => ->. by rewrite eq_refl. 
rewrite H.
exact: R_correct0'.
Qed.

Lemma R_correct1 k x a w y:
  let x' := dfa_step A x a in
  let xs := dfa_run' A x' w in
  all [ pred x | enum_rank x < k] (belast x' xs) ->
  last x' xs = y ->
  mem_der (R k (enum_rank x) (enum_rank y)) (a::w).
Proof.
elim: w k a x y => [|b w IHw] k a x y.
  elim: k a x y => [|k IHk] a x y x' xs H0 H1.
    by apply: R_correct0.
  simpl in H0,H1.
  rewrite -H1.
  rewrite /=. apply/orP. right.
  move: (IHk _ _ _ H0 H1).
  by rewrite -H1.
elim: k w IHw a x y => [|k IHk] w IHw a x y x' xs H0 H1 //.
move: (IHk _ IHw). clear IHk => IHk.
simpl R.
rewrite mem_der_Plus.



assert ([pred x0 | enum_rank x0 < k.+1] =1 [pred x0 : A | (enum_rank x0 < k) || (k == enum_rank x0) ]).
  move => x0.
  rewrite /= leq_eqVlt -{2}(addn1 (enum_rank x0)) -{2}(addn1 k) ltn_add2r.
  rewrite orbC eq_sym.
  case_eq (enum_rank x0 < k) => -> //=.
move: H0.
rewrite (eq_all H).
rewrite all_predI.


move => x' xs H0 H1.
simpl.
elim: k w IHw a x y => [|k IHk] a x y x' xs H0 H1.
   

  
elim: k x a w y => [|k IHk] x a w y.
  elim: w a x y => [|b w IHw] a x y //=.
  move => _.
  exact: R_correct0.
elim: w k IHk a x y => [|b w IHw] k IHk a x y.
  rewrite /dfa_run' /last.
  rewrite /belast => _.
  move => H0.
  apply/orP. right.
  exact: (IHk x a [::] y is_true_true H0).
move => x' xs.
rewrite [last x' xs]/= [all _ _]/=.
move/andP => [] H0 H1 H2.  

(* alternative 1 *)
move: (IHw _ IHk). clear IHw => IHw.

move Eqw': (b::w) => w'.
rewrite /= mem_der_Plus.
move Eqk': (Ordinal (n:=#|A|) (m:=minn k #|A|.-1)
                    (noname (minn k #|A|.-1) #|A| A_has_states
                       (minn_to_ord k #|A|.-1))) => k'.

(* Decide whether the new run goes over the newly
   included state. *)
move: H0. rewrite leq_eqVlt orbC -{1}(addn1 k) -{1}(addn1 (enum_rank x')) ltn_add2r => /orP [].
  move => H0.
  apply/orP. right.
  apply: IHk.
  

case_eq (x' == enum_val k').
  move/eqP => H3.
  rewrite 2!fun_if if_arg.
  case_eq (has_eps (R k (enum_rank x ) k')) => H4.
    rewrite mem_der_Plus.
    rewrite -Eqw'. rewrite (mem_der_Conc _ _ [::b] w).
    rewrite mem_der_Plus.
    rewrite (mem_der_Conc _ _ [::b] w).
    
    apply/orP. left.
    rewrite [der b _]/= .
    
    assert (has_eps (der a (R k (enum_rank x) k'))).
      move: (IHk x a [::] (enum_val k') is_true_true H3).
      by rewrite /= enum_valK.
    rewrite H 2!mem_der_Plus.
    apply/orP. left. apply/orP. left.
    eapply (mem_der_Conc _ _).
    
    





(* alternative 2 *)

move: H0. rewrite leq_eqVlt => /orP [].
  move/eqP/(f_equal predn) => H0. simpl in H0. 
  rewrite /= mem_der_Plus. apply/orP. left.
  move Eqk': (Ordinal (n:=#|A|) (m:=minn k #|A|.-1)
                    (noname (minn k #|A|.-1) #|A| A_has_states
                       (minn_to_ord k #|A|.-1))) => k'.
  rewrite 2!fun_if if_arg der_Plus mem_der_Plus.
  case_eq (has_eps (R k (enum_rank x ) k')) => H3.
    rewrite der_Plus.
    apply/orP. left.
    rewrite [der b _]/= .

    assert (x' = enum_val k').
      rewrite -H0.
    
    assert (has_eps (der a (R k (enum_rank x) k'))).
    move: (IHk x' a [::] (enum_val k') is_true_true).
    
        

  


End TransitiveClosure.



Section StateRemoval.
  
Variable char: finType.
Definition word:= misc.word char.
  
Record re_nfa : Type :=
  re_nfaI {
    re_nfa_state :> finType;
    re_nfa_s0: re_nfa_state;
    re_nfa_fin: pred re_nfa_state;
    re_nfa_re: re_nfa_state -> re_nfa_state -> regular_expression char
    }.

Variable A: nfa char.

Definition nfa_to_re_nfa: re_nfa :=
  re_nfaI
    (option_finType A)
    (Some (nfa_s0 A))
    (fun x => if x is Some x then false else true)
    (fun x y =>
       if x is Some x then
         if y is Some y then
            foldr
              (@Plus char)
              (@Void char)
              (map (@Atom char) (enum [pred a | nfa_step A x a y]))
         else
           if nfa_fin A x then
             (@Eps char)
           else
             @Void char
       else
         if y is Some y then
           @Void char
         else
           @Eps char
    )
    .
    
Section Acceptance.
Variable R: re_nfa.


Definition re_nfa_step: R -> word -> pred R :=
fun x w y => mem_der (re_nfa_re R x y) w.

Lemma size_ind (P: word -> Type):
  (forall w, (forall w', size w' < size w -> P w') -> P w) ->
  forall w, P w.
Proof.
move => H w.
move Heqn: (size w) => n.
assert (size w <= n). by rewrite Heqn.
clear Heqn.
elim: n w H0 => [|n IHn] w.
  rewrite leqn0. move/eqP/size0nil => ->. by apply: H.
rewrite leq_eqVlt.
case_eq (size w == n.+1); case_eq (size w < n.+1) => //.
    move => H1 _ _. by apply: IHn.
  move => _ /eqP H1 _. apply: H.
  rewrite H1. exact: IHn.
move => H1 _ _. by apply: IHn.
Qed.

Lemma sub0 n: n - 0 = n.
elim: n => [|n IHn] //.
Qed.                    

Lemma drop_size_gt0 n (w: word) : size w > 0 -> n > 0 -> size (drop n w) < size w.
Proof.
rewrite size_drop.
move => H.
rewrite leq_eqVlt => /orP [].
  move/eqP => H1. move: H. rewrite -H1 subn1 => H.
  rewrite -(ltn_add2r 1) addn1 prednK -addn1 //.
move => H1.
assert (size w -n < size w - 0).
  apply: ltn_sub2l => //.
  move: H1.
  by apply: ltn_trans.
move: H0.
by rewrite sub0.
Qed.

  
Lemma re_nfa_accept (x: R) (w: word): bool.
Proof.
move: w x. apply: size_ind.
move => [|a w] F x.
  exact: re_nfa_fin x.
exact
(
  existsb n: 'I_(size (a::w)),
    existsb y: R,
      re_nfa_step x (take n.+1 (a::w)) y
    && F (drop n.+1 (a::w)) (drop_size_gt0 _ (a::w) (ltn0Sn _) (ltn0Sn _)) y
).
Defined.

End Acceptance.

Lemma nfa_to_re_nfa_correct1 x w: nfa_accept A x w -> re_nfa_accept (nfa_to_re_nfa) (Some x ) w.
Proof. 
elim: w x => [|a w IHw] x /=.
  move => H0.
  rewrite /re_nfa_accept /size_ind /=.

    
                                          
End StateRemoval.



