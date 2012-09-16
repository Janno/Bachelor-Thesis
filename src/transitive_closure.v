Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool finset.
Require Import Recdef.
Require Import automata misc regexp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* http://krchowdhary.com/toc/dfa-to-reg-exp.pdf *)

(* Size induction. We need this for induction over split lists *)
Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) :
( forall x, ( forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof.
  move => H0 x. apply H0.
  assert (L : forall n y, f y < n -> p y).
    elim => [|n IHn] // y H1.
    apply H0 => z H2.
    apply IHn.
    apply: leq_trans.
      by eassumption.
    by rewrite -ltnS.
  apply: (L (f x)).
Qed.    

Lemma set1UrP (T: finType) (X: {set T}) x: reflect (x |: X = X) (x \in X). 
Proof.
  case H: (x \in X); constructor.
    apply/setP => y. 
    apply/setU1P.
    case H0: (y \in X); firstorder.
    move => [] // H1.
    subst. by rewrite H in H0.
  move => H1. move: H.
  by rewrite -H1 setU11.
Qed.

Section AllButLastDef.
  
  Variable X: Type.
  Variable p: pred X.
  
  Definition belast xs : seq X :=
    (fix belast xs := 
    match xs with
      | [::] => [::]
      | [::x] => [::]
      | x::xs => x::(belast xs)
    end)
    xs.

  Lemma belast_rcons (x: X) xs:
    belast (rcons xs x) = xs.
  Proof.
    elim: xs => [|y xs IHxs] //.
    rewrite rcons_cons /= IHxs.
    destruct xs => //.
  Qed.
                     
  Definition allbutlast : pred (seq X) :=
    fun xs => all p (belast xs).
End AllButLastDef.

Implicit Arguments allbutlast [X].

Section AllButLast.
  Variable X: Type.
  Variable p q: pred X.

  (* p => q -> allbutlast p -> allbutlast q *)
  Lemma allbutlast_impl xs:
    subpred p q ->
    allbutlast p xs ->
    allbutlast q xs.
  Proof.
    elim: xs => [|x xs IHxs] //.
    case: xs IHxs => [|y xs IHxs] //.
    rewrite /allbutlast /=.
    move => H0 /andP [] /H0 -> /=.
    by move: (IHxs H0). 
  Qed.

  Lemma allbutlast_nil: allbutlast p [::] = true.
  Proof. by []. Qed.

  Lemma allbutlast_cons x xs: p x -> allbutlast p xs -> allbutlast p (x::xs).
  Proof.
    elim: xs x => [|y xs IHxs] x //. 
    by rewrite /allbutlast /= => -> /=.
  Qed.

  (* if at least one element in xs is actually
     applied to p we can extract that application. *)
  Lemma allbutlast_cons' x y xs: allbutlast p (x::y::xs) -> p x && allbutlast p (y::xs).
  Proof.
    elim: xs x => [|z xs IHxs] x //. 
  Qed.
  
  (* if p holds everywhere on xs, it also holds
     for all but the last element *)
  Lemma all_allbutlast xs: all p xs -> allbutlast p xs.
  Proof.
    elim: xs => [|x xs IHxs] //.
    move => /= /andP [] H0 /IHxs.
    by apply: allbutlast_cons.
  Qed.

  (* we can either extract an application of p x or
     x is the last element in x::xs (i.e. xs is empty). *)
  Lemma allbutlast_cons'' x (xs: seq X): allbutlast p (x::xs) -> (size xs == 0) || (p x && allbutlast p xs). 
  Proof.
    elim: xs x => [|y xs IHxs] x.
      by [].
    by rewrite orFb.    
  Qed.

  (* all .. + allbutlast .. -> allbutlast (.. + ..)  *)
  Lemma all_allbutlast_cat xs ys: all p xs -> allbutlast p ys -> allbutlast p (xs++ys).
  Proof.
    elim: xs => [|x xs IHxs].
      by rewrite /= => _.
    rewrite /= => /andP [] H0. 
    move => H1 H2. move: (IHxs H1 H2).
    by apply: allbutlast_cons.
  Qed.

  (* This lemma is stronger than all_allbutlast_cat (both directions hold) *)
  Lemma all_allbutlast_cat' xs ys: size ys > 0 -> all p (xs) && allbutlast p ys = allbutlast p (xs++ys).
  Proof.
    move => H0.
    apply/andP/idP.
      move => []. by apply: all_allbutlast_cat.
    elim: xs H0 => [|x xs IHxs] H0 //.
    rewrite cat_cons.
    move/allbutlast_cons'' => /orP [].
      destruct xs, ys => //.
    by move/andP => [] /= -> /(IHxs H0).
  Qed.

  (* with p (last xs) we can extend allbutlast to all. *)
  Lemma allbutlast_last x xs: allbutlast p xs -> p (last x xs) -> all p xs.
  Proof.
    elim: xs x => [|y xs IHxs] x //.
    case: xs IHxs => [|z xs] IHxs.
      by rewrite /allbutlast /= => -> ->.
    move/allbutlast_cons'/andP => [] H0 H1 H2.
    move: (IHxs x H1 H2).
    by rewrite /= H0 => /andP [] ->.
  Qed.

  (* constant false can only hold for one element or fewer. *)
  Lemma allbutlast_pred0 xs: p =1 pred0 -> allbutlast p xs -> size xs <= 1.
  Proof.
    move => H0.
    elim: xs => [|x xs IHxs] //.
    case: xs IHxs => [|y xs] IHxs //.
    move/allbutlast_cons'.
    move/andP=>[].
    by rewrite (H0 x).
  Qed.

  Lemma allbutlast_predI xs: allbutlast (predI p q) xs = allbutlast p xs && allbutlast q xs.
  Proof. by apply: all_predI. Qed.

  Lemma allbutlast_predT (xs: seq X): allbutlast predT xs.
  Proof. by apply: all_predT. Qed.
  
  Lemma eq_allbutlast xs: p =1 q -> allbutlast p xs = allbutlast q xs.
  Proof. move => H0. by apply: eq_all. Qed.

  Lemma allbutlast_take xs n: allbutlast p xs -> allbutlast p (take n xs).
  Proof.
    elim: xs n => [|x xs IHxs] n.
      by [].
    move => H0. 
    destruct n => //.
    move/allbutlast_cons'': (H0) => /orP [].
      by move/eqP/size0nil => ->.
    move/andP => [] /= H1 /IHxs H2.
    by apply: allbutlast_cons.
  Qed.

  Lemma allbutlast_drop xs n: allbutlast p xs -> allbutlast p (drop n xs).
  Proof.
    elim: xs n => [|x xs IHxs] n.
      by [].
    move => H0.
    destruct n => //.
    apply IHxs.
    move/allbutlast_cons''/orP: H0 => [].
      by move/eqP/size0nil => ->.
    by move/andP => [].
  Qed.
  
End AllButLast.   

Section EqTypes.
  Variable X: eqType.
  
  Lemma mem_belast (x: X) xs: x \in belast xs -> x \in xs.
  Proof.
    case/lastP: xs => [|xs y IHxs] //.
    rewrite belast_rcons in IHxs.                                   
    by rewrite mem_rcons in_cons IHxs orbT.
  Qed.

  Lemma belast_index (x: X) xs: x \in belast xs -> index x (belast xs) = index x xs.
  Proof.
    move: xs. apply: last_ind => [|xs y IHxs] //.
    rewrite belast_rcons.
    rewrite -cats1 index_cat.
    by move ->.
  Qed.
  
  Lemma allbutlast_index xs (x: X): allbutlast (predC (pred1 x)) (take (index x xs).+1 xs).
  Proof.
    move: xs.
    apply: last_ind => [|xs y IHxs] //.
    case H1: (x \in xs).
      rewrite -cats1 index_cat H1.
      rewrite -index_mem in H1.
      by rewrite takel_cat.
    rewrite -{2}cats1 take_cat.
    case H2: ((index x (rcons xs y)).+1 < size xs).
      move: (H1). rewrite -index_mem => /negbT. rewrite -ltnNge => H1'.
      by rewrite -cats1 index_cat H1 /= -{2}(addn0 (size xs)) -addnS ltn_add2l ltn0 in H2.
    move/negbT: H2. rewrite -ltnNge => H2.
    move: (H1). rewrite -index_mem => /negbT. rewrite -ltnNge => H1'.
    apply: all_allbutlast_cat.
      apply/allP => z H3 /=. apply/negP => /eqP H4.
      rewrite H4 in H3.
      by rewrite H3 in H1.
    simpl.
    by destruct ((index x (rcons xs y)).+1 - size xs).
  Qed.    
       
End EqTypes.
  
Section TransitiveClosure.

  Variable char: finType.
  Variable A: dfa char.
  
    Section RE_Misc.
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
    End RE_Misc.

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
  by exists (dfa_s A).
  Qed.
  
  (* this represents k in 'I_#|A| *)
  Definition k_ord k := 
    Ordinal (leq_ltn_gt0 A_has_states (minn_to_ord k #|A|.-1)).

  Lemma k_ord_lt k: k_ord k < k.+1.
  Proof.
    rewrite /k_ord /=.
    case H0: (k <= #|A|.-1).
      rewrite minnl => //.
    move: (leq_total k #|A|.-1).
    rewrite H0 /= => H1.
    by rewrite minnr.
  Qed.

  Lemma k_ord_eq k: k <= #|A|.-1 -> k = k_ord k.
  Proof. move => H. by rewrite /= minnl. Qed.

  Definition nPlus : seq (regular_expression char) -> regular_expression char := [fun rs => foldr (@Plus _) (Void _) rs].

  Definition dfa_step_any :=
    [ fun x y => enum ( [pred a | dfa_step A x a == y] ) ].

  Definition R0 :=
    [ fun x y => 
      let r := nPlus (map (@Atom _) (dfa_step_any x y)) in
        if x == y then Plus r (Eps _) else r ].
                                             

  Lemma set_pick_size (X: {set A}) z: [pick z \in X] = Some z -> #|X :\ z| < #|X|.
  Proof.
    case: (pickP _) => // x [] H [] <-.
    by rewrite (cardsD1 x X) H addnC addn1.
  Qed.
    
  Function R (X: {set A}) (x y: A) {measure [fun X => #|X|] X} : regular_expression char :=
    match [pick z \in X] with
    | None =>  R0 x y        
    | Some z =>  let X' := X :\ z in
        Plus (Conc (R X' x z) (Conc (Star (R X' z z)) (R X' z y))) (R X' x y) 
    end.
  Proof.
    move => X x y z /= H; apply/ltP; exact: set_pick_size.
    move => X x y z /= H; apply/ltP; exact: set_pick_size.
    move => X x y z /= H; apply/ltP; exact: set_pick_size.
    move => X x y z /= H; apply/ltP; exact: set_pick_size.
  Defined.
  Functional Scheme R_ind := Induction for R Sort Prop.

  Check R_ind.
  
  Notation "'R^' X" := (R X) (at level 8).
  
  Definition L :=
    [fun X: {set A} => [fun x y: A =>
          [pred w |
           (last x (dfa_run' A x w) == y)
             && allbutlast (mem X) (dfa_run' A x w) 
          ]
       ]
    ].

  Notation "'L^' X" := (L X) (at level 8).
       
  Section L.
    Lemma L_monotone (X: {set A}) (x y z: A): {subset L^X x y <= L^(z |: X) x y}.
    Proof.
      move => w.
      rewrite 2!in_simpl /= => /andP [] -> /=.
      apply: allbutlast_impl.
      move => x' /=.
      exact: (setU1r).
    Qed.

    Lemma L_nil X x y: reflect (x = y) ([::] \in L^X x y).
    Proof.
      case H: ([::] \in L^X x y); constructor; move: H.
        by rewrite in_simpl /= => /andP [] /eqP. 
      rewrite in_simpl /= allbutlast_nil andbT.
      by move/eqP.
    Qed.

    (* Another prerequisite for L_split.
       We can safely concatenate words and not
       leave L^X if the split point is in X. *)
    Lemma L_cat (X: {set A}) x y z w1 w2:
      z \in X ->
      w1 \in L^X x z ->
      w2 \in L^X z y ->
      w1++w2 \in L^X x y.
    Proof.
      move => H0 /= /andP [] /eqP H1 H2 /andP [] /eqP H3 H4.
      rewrite in_simpl /= dfa_run'_cat.
      subst.
      apply/andP. split.
        by rewrite last_cat eq_refl.       
      apply: all_allbutlast_cat => //.
      exact: (allbutlast_last _ H0).
    Qed.

    Lemma setU1_predI (X: {set A}) z: (z \notin X) -> (mem X) =1 predI (mem (z |: X)) (predC (pred1 z)).
    Proof.
      move => H x.
      rewrite /= in_setU1.
      rewrite andbC andb_orr andNb /=.
      apply/idP/idP.
        move => H1.
        apply/andP. split => //.
        apply/negP. move/eqP => H2.
        subst. by rewrite H1 in H.
      by move/andP => [].
    Qed.

    Lemma setC1_pred1 (T: finType) (z: T): mem [set~ z] =1 predC (pred1 z).
    Proof.  move => x. by rewrite /= in_setC1.   Qed.
      
    
    Lemma L_split X x y z a w:
      (a::w) \in L^(z |: X) x y ->
      (a::w) \in L^X x y \/
      exists w1, exists w2,
        a::w = w1 ++ w2 /\
        w1 != [::] /\
        w1 \in L^X x z /\
        w2 \in L^(z |: X) z y.
    Proof.
      move => H0.
      case HX: (z \in X).
        move/set1UrP: HX H0 => ->.
        by left.
      move/eqP in HX.
      move/andP: H0 => [] H0 H1.
      move: H0 H1.
      pose w' := a::w.
      pose xs := dfa_run' A x w'.
      rewrite -/xs=> H0 H1.
      case Hz: (z \in belast xs).
        right.
        have Hz2: z \in xs by (apply: mem_belast; by []).
        move: (Hz) (Hz2).
        pose i := index z xs.
        rewrite -index_mem => Hi. rewrite -index_mem -/i => Hi2.
        have: (i = index z (belast xs)) by (rewrite belast_index; by []).
        (* we split after the first appearance of z, i.e. i+1. *)
        exists (take i.+1 w'). exists (drop i.+1 w').
        have Hw: (take i.+1 w' ++ drop i.+1 w' = w') by rewrite cat_take_drop.
        have Hw1: (take i.+1 w' \in L^X x z).
          rewrite  in_simpl simpl_predE -dfa_run'_take -/xs.
          rewrite -nth_last nth_take size_takel //.
          rewrite  nth_index // eq_refl andTb.
          rewrite (eq_allbutlast _ (setU1_predI HX)).
          rewrite allbutlast_predI.
          apply/andP. split.
            exact: allbutlast_take.
          exact: allbutlast_index.
        firstorder.
        rewrite in_simpl simpl_predE.
        move/andP: (Hw1) => [/eqP Hw1l _].
        rewrite -Hw1l -dfa_run'_drop -last_cat dfa_run'_drop.
        rewrite -dfa_run'_cat Hw -/xs H0 andTb.
        rewrite {1}Hw1l -dfa_run'_drop.
        exact: allbutlast_drop.

      left.
      rewrite /= in_simpl simpl_predE H0 andTb.
      have H2: allbutlast (predI (mem (z |: X)) (predC (pred1 z))) xs.
        rewrite allbutlast_predI H1 andTb.
        move/negbT: Hz.
        by rewrite -has_pred1 -all_predC.
      erewrite eq_allbutlast.
      eexact H2.
      exact: setU1_predI.
    Qed.


    (* w1 \in L^k i k -> w2 \in L^k.+1 k j -> w1++w2 \in L^k.+1 i j *)
    Lemma L_catL X x y z w1 w2:
      w1 \in L^X x z ->
      w2 \in L^(z |: X) z y ->
      w1++w2 \in L^(z |: X) x y.
    Proof.
      rewrite /L 3!in_simpl /=. 
      rewrite dfa_run'_cat.
      move => /andP [] /eqP H0 H1 /andP [] /eqP H2 H3.
      case: w1 H0 H1 => [|v1 w1] H0 H1.
        rewrite /= in H0. rewrite H0 /= H2 eq_refl /=.  
        exact: H3.
      rewrite last_cat.
      case: w2 H2 H3 => [|v2 w2] H2 H3.
        rewrite /= in H2.
        rewrite -H2 H0 /= eq_refl /=.
        eapply allbutlast_impl.
          move => ? /=.
          by eapply setU1r. 
        rewrite cats0.
        exact H1.

      rewrite H0 H2 eq_refl andTb.
      eapply all_allbutlast_cat.
        apply (@allbutlast_last _ _ x) => //. 
          eapply allbutlast_impl.
            move => ? /=.
            by eapply setU1r. 
          by [].
        rewrite H0. 
        exact: setU11.
      by [].
    Qed.

    (* w1 \in L^k.+1 i k -> w2 \in L^k k j -> w1++w2 \in L^k.+1 i j *)
    Lemma L_catR X x y z w1 w2:
      w1 \in L^(z |: X) x z ->
      w2 \in L^X z y ->
      w1++w2 \in L^(z |: X) x y.
    Proof.
      rewrite /L 3!in_simpl /= dfa_run'_cat.
      move => /andP [] /eqP H0 H1 /andP [] /eqP H2 H3.
      case: w1 H0 H1 => [|v1 w1] H0 H1.
        rewrite /= in H0.
        rewrite H0 /= H2 eq_refl /=.  
        eapply allbutlast_impl.
          move => ? /=.
          by eapply setU1r. 
        exact: H3.
      rewrite last_cat.
      case: w2 H2 H3 => [|v2 w2] H2 H3.
        rewrite /= in H2.
        rewrite -H2 H0 /= eq_refl /=.
        rewrite cats0.
        exact H1.

      rewrite H0 H2 eq_refl andTb.
      eapply all_allbutlast_cat.
        apply: (@allbutlast_last _ _ x) => //. 
        rewrite H0. 
        exact: setU11.
        eapply allbutlast_impl.
          move => ? /=.
          by eapply setU1r. 
      by [].
    Qed.
  End L.
            

  Section R.

    (* Associativity of concatenation *)
    Lemma Conc_assoc r s t (w: word char): (w \in Conc r (Conc s t)) = (w \in Conc (Conc r s) t).
    Proof.
      rewrite -2!topredE /=.
      apply/concP/concP.
        move => [] v1 Hr [] v23 /concP [] v2 Hs [] v3 Ht H0 H1.
        exists (v1++v2).
        apply/concP.
        exists v1 => //.
          by exists v2.
        exists v3 => //.
        by rewrite -catA H1 H0.

      move => [] v12 /concP [] v1 Hr [] v2 Hs H0 [] v3 Ht H1.
      exists v1 => //. exists (v2 ++ v3).
        apply/concP.
        exists v2 => //.
        exists v3 => //.
      by rewrite H1 catA H0.
    Qed.

    (* Re-fold for Conc r (Star r) *)
    Lemma Conc_Star_idem r (w: word char): w \in conc r (star r) -> (w \in star r).
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

    (* w1 \in R^k i k -> w2 \in R^k.+1 k j -> w1++w2 \in R^k.+1 i j *) 
    Lemma R_catL (X: {set A}) z x y w1 w2:
      [pick z \in X] = Some z ->
        w1 \in R^(X :\ z) x z ->
        w2 \in R^X z y ->
        w1++w2 \in R^X x y.
    Proof.
      rewrite /= => Hp.
      rewrite (R_equation X z y) Hp.
      move => H0.
      (* see which case of R^k.+1 we are in *)
      rewrite Plus_dist => /orP [].
        (* triple concatenation case *)
        rewrite Conc_assoc -topredE /=.
        move/concP => [] v1.
        move/Conc_Star_idem => H1 [] v2 H2 H3.
        rewrite R_equation Hp.
        rewrite Plus_dist.
        apply/orP. left.
        rewrite -topredE /=.
        apply/concP.
        exists w1 => //.
        exists w2 => //.
        apply/concP.
        exists (v1) => //.
        exists (v2) => //.
                         
      (* basic recursion case *)
      rewrite (R_equation X) Hp.
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

    (* Empty word in all R^k i i *)
    Lemma R_nil X x: [::] \in R^X x x.
    Proof.
      apply R_ind => r [] n H _.
      have Hn: (forall n, n < n.+1)%coq_nat by (move => k; apply/ltP).
      elim: n H => [|n IHn] H.
        move: (H 1 (Hn 0) (fun X => R0)) => /=.
        rewrite /R_F.



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
    (* induction over k *)
    elim: k i j w => [|k IHk] i j w.
      (* k = 0 *)

      (* we only ask if i==j due to the if condition.
         the actual cases are very similar. *)
      case H0: (i==j) => /=.
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

    (* k > 0 *)  

    (* see which case of R^k.+1 we are in *)
    rewrite /= Plus_dist => /orP [].
      (* triple concatenation case.
         we apply IHk where we can and translate
         star (R^k k k) with R_L_star. *)
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
    (* basic recursion case. solved by IHK. *)
    move/IHk.
    by apply: L_monotone.
  Qed.
 
  (* w \in L^k.+1 i j -> w \in R^k.+1 i j.
     The first argument is the inductive hypothesis
     obtained from induction over k in L_R *)
  Lemma L_R_1 k i j w:
       (forall (i j : 'I_#|A|) (w : automata.word char),
        w \in L^k (enum_val i) (enum_val j) -> w \in R^k i j) ->
        w \in L^k.+1 (enum_val i) (enum_val j) -> w \in R^k.+1 i j. 
  Proof.
    move => IHk.
    move: w i j.
    (* we use size induction because we want to use the
       inductive hypothesis for an abitrary suffix later. *)
    apply: (size_induction (size)) => w IHw i j.
    (* destruct w so that we can use L_split, which requires
       at a form of a::w. *)
    case: w IHw => [|a w] IHw.
      move/L_nil'/(f_equal enum_rank). 
      rewrite 2!enum_valK => ->.
      exact: R_nil.
    (* a::w *)
    move/L_split => [].
      (* no k => 2nd case of R^k.+1 i j = R^k i j by IHk *)
      move/IHk.
      rewrite /= Plus_dist => ->.
      by rewrite orbT.
    (* Splitting exists *)
    move => [] w1 [] w2 [] H0 [] H1 [] H2 H3.
    (* We need this later for size induction *)
    assert (size w1 > 0).
      case: w1 H0 H1 H2 => [|b w1] H0 H1 H2 => //.
    rewrite H0.
    (* IHk takes care of the prefix *)
    apply: R_catL.
      by apply: IHk.
    (* IHw takes care of the suffix *)
    apply: IHw => //.
    rewrite H0 size_cat.
    rewrite -{1}(addn0 (size w2)).
    rewrite addnC.    
    by rewrite ltn_add2r.
  Qed.
    
  (* w \in L^k i j -> w \in R^k i j *)
  Lemma L_R k i j w: w \in L^k (enum_val i) (enum_val j) -> w \in R^k i j. 
  Proof.
    (* induction over k.
       we only look at k=0 here,
       L_R_1 takes care of k > 0 *)
    elim: k i j w => [|k IHk] i j w.
      (* < 0 =1 pred0 *)
      assert ((fun x:A => enum_rank x < 0) =1 pred0) => //.
      (* allbutlast pred0 w -> |w| <= 1 *)
      rewrite in_simpl => /andP [] H0 /(allbutlast_pred0 _ H).  
      (* |w| <= 1 -> w = [::] \/ w = [::a] *)
      move: H0. case: w => [|a [|b w]] H0 _ //.
        (* w = [::] -> i = j *)
        move/eqP/(f_equal enum_rank) in H0.
        rewrite 2!enum_valK in H0.
        rewrite H0.
        exact: R_nil.
      (* w = [::a].
         this would be much simpler if we could ignore
         the if expression. *)
      case_eq (i==j) => [/eqP H1| H1].
        (* i = j *)
        rewrite /= H1 eq_refl /=.
        rewrite Plus_dist foldr_Plus 2!in_simpl orbF /=. 
        apply/hasP. exists (Atom a).
          apply/mapP. exists a => //.
          rewrite mem_filter.
          rewrite H1 in H0.
          by rewrite mem_enum andbT /= H0.
        by rewrite in_simpl /= eq_refl.
      (* i != j *)
      rewrite /= H1.
      rewrite foldr_Plus orFb.
      apply/hasP. exists (Atom a).
        apply/mapP. exists a => //.
        rewrite mem_filter.
        by rewrite mem_enum andbT /= H0.
      by rewrite in_simpl /= eq_refl.
    by apply: L_R_1.
  Qed.

  Lemma dfa_L x y: L^#|A| x y =1 [pred w | last x (dfa_run' A x w) == y ].
  Proof.
    move => w /=.
    apply/andP/idP.
      by move => [] H0 H1.
    move => -> /=.
    assert (<_#|A| =1 predT).
      move => n /=.
      by rewrite ltn_ord.
    rewrite (eq_allbutlast _ H).
    firstorder.
    by apply: allbutlast_predT.
  Qed.
                 
  
  Lemma dfa_to_regex: exists r: regular_expression char, dfa_lang A =1 [pred w | w \in r ].
  Proof.
    exists (
        foldr
          (@Plus char)
          (@Void char)
          (map  (fun f => R^(#|A|) (enum_rank (dfa_s A)) (enum_rank f)) (enum (dfa_fin A)))
       ).
    move => w.
    apply/idP/idP.
      rewrite /= -dfa_run_accept => H.
      rewrite foldr_Plus orFb.
      apply/hasP.
      exists (R^#|A| (enum_rank (dfa_s A)) (enum_rank (last (dfa_s A) (dfa_run' A (dfa_s A) w)))).
        apply/mapP.
        exists (last (dfa_s A) (dfa_run' A (dfa_s A) w)) => //.
        by rewrite mem_enum.
      apply/L_R.
      by rewrite in_simpl 2!enum_rankK dfa_L /=.
    rewrite /= foldr_Plus orFb.
    move/hasP => [] r.
    move/mapP => [] f.
    rewrite mem_enum.
    move => H0 -> /R_L.
    rewrite in_simpl dfa_L 2!enum_rankK /=.
    by rewrite -dfa_run_accept => /eqP ->.
  Qed.                                    
    
End TransitiveClosure.
