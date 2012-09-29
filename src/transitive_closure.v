Require Import Recdef.
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype finset.
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
  apply/iffP. by apply idP.
    move => H. apply/setP => y.
    rewrite in_setU1.
    apply/orP/idP; try auto.
    move => [/eqP ->|] //.
  move => <-. by rewrite setU11.
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

  (* with p (last xs) we can extend allbutlast to all. *)
  Lemma allbutlast_last x xs: allbutlast p xs -> p (last x xs) -> all p xs.
  Proof.
    elim: xs x => [|y xs IHxs] x //.
    case: xs IHxs => [|z xs] IHxs.
      by rewrite /allbutlast /= => _ ->.
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

  Definition nPlus : seq (regular_expression char) -> regular_expression char := [fun rs => foldr (@Plus _) (Void _) rs].

  Lemma mem_nPlus (rs: seq _) w:
    reflect (exists2 r: regular_expression char, r \in rs & w \in r)
            (w \in nPlus rs).
  Proof.
    elim: rs => [|s rs IHrs].
      apply introP => //= _.
      by move => [r] .
    apply introP.
      rewrite /nPlus /= -topredE /= /plus /= => /orP [].
        move => Hs.
        exists s => //=.
        by rewrite in_cons eq_refl.
    move/IHrs => [r Hr Hw].
      exists r => //=.
      by rewrite in_cons Hr orbT.
    move => H0 [r Hr Hw].
    apply/negP.
      eexact H0.
    move: Hr. rewrite in_cons => /orP [].
      move/eqP => H1. subst.
      by rewrite /nPlus /= -topredE /= /plus /= Hw.
    move => H1.
    rewrite /nPlus /= -topredE /= /plus /=.
    apply/orP. right.
    apply/IHrs.
    by eauto.
  Qed.
          
  Definition dfa_step_any :=
    [ fun x y => enum ( [pred a | dfa_step A x a == y] ) ].

  
  Definition R0 :=
    [ fun x y => 
      let r := nPlus (map (@Atom _) (dfa_step_any x y)) in
        if x == y then Plus r (Eps _) else r ].
                                             
  Lemma mem_R0 w x y:
    reflect (w = [::] /\ x=y \/ exists2 a, w = [::a] & dfa_step A x a = y)
            (w \in R0 x y). 
  Proof.
    apply/introP.
      rewrite /=. case H: (x == y).
        rewrite -topredE /= /plus /= => /orP [].
          move/mem_nPlus => [r] /mapP [a].
          rewrite /dfa_step_any /= mem_enum in_simpl /= => /eqP <- ->.
          rewrite in_simpl /= => /eqP ->.
          by eauto.
        rewrite in_simpl /= => /eqP.
        move/eqP: H.
        by eauto.
      move/mem_nPlus => [r] /mapP [a].
      rewrite /dfa_step_any /= mem_enum in_simpl /= => /eqP <- ->.
      rewrite in_simpl /= => /eqP ->.
      by eauto.
    move => H [[Hw Hxy]|[a Hw Hxay]].
      subst.
      move: H => /=. rewrite eq_refl -topredE /= /plus /=.
      apply: negP. apply/negPn.
      by rewrite in_simpl orbT.
    apply/negP.
      eexact H.
    rewrite /R0 /=.
    case: (x==y).
      rewrite -topredE /= /plus /=. apply/orP. left.
      apply/mem_nPlus.
      exists (Atom a). apply/mapP. exists a => //.
        by rewrite /dfa_step_any /= mem_enum in_simpl /= Hxay eq_refl.
      by rewrite in_simpl Hw /= eq_refl.
    apply/mem_nPlus.
      exists (Atom a). apply/mapP. exists a => //.
        by rewrite /dfa_step_any /= mem_enum in_simpl /= Hxay eq_refl.
      by rewrite in_simpl Hw /= eq_refl.
  Qed.

  Lemma set_pick_size (X: {set A}) z: [pick z in X] = Some z -> #|X :\ z| < #|X|.
  Proof.
    case: (pickP _) => // x [] H [] <-.
    by rewrite (cardsD1 x X) H addnC addn1.
  Qed.
    
  Function R (X: {set A}) (x y: A) {measure [fun X => #|X|] X} : regular_expression char :=
    match [pick z in X] with
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

  Notation "'R^' X" := (R X) (at level 8).
  
  Definition L (X: {set A}) (x y: A) :=
      [pred w |
       (last x (dfa_run' A x w) == y)
         && allbutlast (mem X) (dfa_run' A x w) 
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
        w = w1 ++ w2 /\
        a::w1 \in L^X x z /\
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
        exists (take i.+1 w). exists (drop i.+1 w).
        have Hw: (take i.+1 w ++ drop i.+1 w = w); first by rewrite cat_take_drop.
        have Hw1: (a::take i.+1 w \in L^X x z).
          rewrite inE /=.
          apply/andP. split.
          rewrite -dfa_run'_take -nth_last nth_take.
          by rewrite size_takel // /i /= /xs nth_index.
          by rewrite size_takel.
          move/eqP/negbT: HX => HX.
          rewrite (eq_allbutlast _ (setU1_predI HX)).
          rewrite allbutlast_predI.
          rewrite -/(dfa_run' A x (a::take i.+1 w)).
          move: (take_cons i.+2) => <-.
          rewrite -dfa_run'_take.
          apply/andP. split.
            exact: allbutlast_take.
          apply: allbutlast_cons.
          exact allbutlast_index.
        firstorder.
        
        rewrite -topredE /=. 
        move/andP: (Hw1) => [/eqP Hw1l _].
        rewrite -Hw1l -dfa_run'_drop. -last_cat dfa_run'_drop.
        rewrite -dfa_run'_cat Hw -/xs H0 andTb.
        rewrite {1}Hw1l -dfa_run'_drop.
        exact: allbutlast_drop.

      left.
      rewrite /= in_simpl H0 andTb.
      have H2: allbutlast (predI (mem (z |: X)) (predC (pred1 z))) xs.
        rewrite allbutlast_predI H1 andTb.
        move/negbT: Hz.
        by rewrite -has_pred1 -all_predC.
      erewrite eq_allbutlast.
      eexact H2.
      apply setU1_predI.
      by move/eqP/negbT: HX.
    Qed.


    Lemma L_cat (X: {set A}) x y z w1 w2:
      z \in X ->
      w1 \in L^X x z ->
      w2 \in L^X z y ->
      w1++w2 \in L^X x y.
    Proof.
      rewrite /L !inE dfa_run'_cat.
      move => H0 /andP [] /eqP H1 H2 /andP [] /eqP H3 H4.
      rewrite last_cat H1 H3 eq_refl /=.
      apply: all_allbutlast_cat; last by done.
      rewrite -H1 in H0.
      apply: (allbutlast_last H2).
      rewrite inE.
      exact H0.
    Qed.
    

    (* w1 \in L^k i k -> w2 \in L^k.+1 k j -> w1++w2 \in L^k.+1 i j *)
    Lemma L_catL X x y z w1 w2:
      w1 \in L^X x z ->
      w2 \in L^(z |: X) z y ->
      w1++w2 \in L^(z |: X) x y.
    Proof.
      move/(L_monotone z).
      apply: L_cat.
      exact: setU11. 
    Qed.

    (* w1 \in L^k.+1 i k -> w2 \in L^k k j -> w1++w2 \in L^k.+1 i j *)
    Lemma L_catR X x y z w1 w2:
      w1 \in L^(z |: X) x z ->
      w2 \in L^X z y ->
      w1++w2 \in L^(z |: X) x y.
    Proof.
      move => H /(L_monotone z).
      move: H.
      apply: L_cat.
      exact: setU11.
    Qed.

    Lemma L_
            
    Lemma L_rec (X: {set A}) x y z:
      z \in X ->
      L^X x y =i plus (conc (L^(X :\ z) x z) (conc (star (L^(X :\ z) z z)) (L^(X :\ z) z y))) (L^(X :\ z) x y).
    Proof.
      move => H w.
      apply/idP/idP.
        move: w X z H x y .
        apply: (size_induction (f:=size)) => w IHw X z H x y .
        destruct w.
          move => Hw.
          rewrite -topredE /plus /=. apply/orP.
          by right. 
        rewrite -{1}(setD1K H).
        move/L_split.
        move Heqn: (s::w) => w'.
        move => [|[w1 [w2 [Hw' [/eqP H1 [Hw1 Hw2]]]]]].
          rewrite -topredE /plus /= => Hw. apply/orP.
          by right.
        have Hsize: (size w2 < size w').
          rewrite Hw' size_cat -{1}(add0n (size w2)) ltn_add2r lt0n => //.
          by apply/nilP.
        rewrite -{1}Heqn in Hsize.
        rewrite setD1K in Hw2 => //.
        move: (IHw w2 Hsize X z H z y Hw2) => H4.
        rewrite -topredE /plus. apply/orP. left.
        apply/concP. exists w1 => //. exists w2 => //.
        apply/concP.
          move: H4.
          rewrite -topredE /plus => /orP [].
          move/concP => [w3 Hw3] [w4].
          move/concP => [w5 Hw5] [w6 Hw6].
          move => Hw4 Hw2'.
          case Hw3nil: (w3==[::]).
            exists w5 => //.
            exists w6 => //. subst.
            by rewrite (eqP Hw3nil).
          exists (w3++w5).
            apply/starP.
            move/starP: Hw5 => [] vv Hvv Hvvf.
            exists (w3::vv).
              by rewrite /= in_simpl /= Hw3nil /= Hw3 Hvv.
            by rewrite Hvvf.
          exists w6 => //.
          by rewrite Hw2' Hw4 catA.
        move => Hw2'.
        exists [::] => //.
        by exists w2 => //.
                          
      rewrite /plus => /orP [].
        move/concP => [w1 Hw1] [w2].
        move/concP => [w3 /starP [vv Hvv Hvvf]] [w4 Hw4] Hw2' Hw.
        subst.
        rewrite catA -(setD1K H).
        have H0: (flatten vv \in L^(X) z z).
          elim: vv Hvv => [|v vv IHvv] Hvv.
            by apply/L_nil.
          rewrite -(setD1K H).
          apply: L_catL.
            by move: Hvv => /= /andP [] /andP [].
          rewrite setD1K => //.
          apply: IHvv => //.
          by move: Hvv => /= /andP [] /andP [].
  
        apply L_catR => //.
        apply L_catL => //.
        rewrite setD1K => //.
  
      rewrite -{2}(setD1K H).
      rewrite simpl_predE.
      apply: L_monotone.
    Qed.              
  End L.

  Lemma conc_eq (l1: language char) l2 l3 l4: l1 =i l2 -> l3 =i l4 -> conc l1 l3 =i conc l2 l4.
  Proof.
    move => H1 H2 w.
    apply/concP/concP; move => [w1 Hw1] [w2 Hw2] Hw.
      exists w1. by rewrite -H1.
      exists w2 => //. by rewrite -H2.
    exists w1. by rewrite H1.
    exists w2 => //. by rewrite H2.
  Qed.

  Lemma star_eq (l1: language char) l2: l1 =i l2 -> star l1 =i star l2.
  Proof.
    move => H1 w.
    apply/starP/starP; move => [] vv H3 H4; exists vv => //.
      erewrite eq_all.
        eexact H3.
      move => x /=.
      by rewrite H1.
    erewrite eq_all.
      eexact H3.
    move => x /=.
    by rewrite H1.
  Qed.

  Lemma orbr2 a b c: a = b -> a || c = b || c.
  Proof.
    by move => ->.
  Qed.
  
  Lemma L_R n (X: {set A}) x y: #|X| = n -> L^X x y =i R^X x y.
  Proof.
    elim: n X x y => [|n IHn] X x y.
      move/cards0_eq => ->.
      rewrite R_equation.
      case: pickP => [z|Hset0].
        by rewrite in_set0.
      move => w.
      apply/idP/mem_R0.
        move/andP => [] H.
        move/(allbutlast_pred0 Hset0).
        destruct w; try destruct w => //;
        move/eqP: H => /=;
        by eauto.
      move => [[-> ->]|[a [-> <-]]].
        by apply/L_nil.
      by rewrite in_simpl /= eq_refl.
    move => HX w.
    rewrite R_equation.
    case: pickP => [z Hz|Hset0].
      have HsizeX: (#|X :\ z| = n).
        move: HX. rewrite (cardsD1 z) Hz add1n.
        by move => [].
      rewrite (L_rec _ _ Hz) -2!topredE /= /plus /=.
      rewrite IHn => //.
      apply: orbr2.
      apply: conc_eq.
        move => v.
        exact: IHn.
      apply: conc_eq.
        apply: star_eq.
        exact: IHn.
      exact: IHn.
    have: (X = set0).
      apply/setP.
      move => v.
      by rewrite Hset0 in_set0.
    move/eqP.
    by rewrite -cards_eq0 HX.
  Qed.        
        
  Lemma dfa_L x y: L^setT x y =i [pred w | last x (dfa_run' A x w) == y ].
  Proof.
    move => w /=.
    apply/andP/idP.
      by move => [] H0 H1.
    rewrite in_simpl => -> /=.
    firstorder.
    erewrite eq_allbutlast.
    apply allbutlast_predT.
    move => z.
    by rewrite /= in_set.
  Qed.
                 
  
  Lemma dfa_to_regex: exists r: regular_expression char, dfa_lang A =i [pred w | w \in r ].
  Proof.
    exists (
        nPlus
          (map  (fun f => R^setT (dfa_s A) (f)) (enum (dfa_fin A)))
       ).
    move => w.
    apply/idP/idP.
      rewrite /= -dfa_run_accept => H.
      apply/mem_nPlus.
      exists (R^setT (dfa_s A) (last (dfa_s A) (dfa_run' A (dfa_s A) w))).
        apply/mapP.
        exists (last (dfa_s A) (dfa_run' A (dfa_s A) w)) => //.
        by rewrite mem_enum.
      rewrite <- (@L_R #|A|).
        by rewrite dfa_L in_simpl.
      by rewrite cardsE.
    move/mem_nPlus => [r].
    move/mapP => [] f.
    rewrite mem_enum.
    move => H0 => ->. rewrite <- (@L_R #|A|).
      by rewrite dfa_L in_simpl -dfa_run_accept => /eqP ->.
    by rewrite cardsE.
  Qed.                                    
    
End TransitiveClosure.
