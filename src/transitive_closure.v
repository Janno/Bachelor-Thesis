Require Import Recdef.
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype finset.
Require Import automata misc regexp re_standard re_fa.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Lemma set1UrP (T: finType) (X: {set T}) x: reflect (x |: X = X) (x \in X). 
Proof.
  apply/iffP. by apply idP.
    move => H. apply/setP => y.
    rewrite in_setU1.
    apply/orP/idP; try auto.
    move => [/eqP ->|] //.
  move => <-. by rewrite setU11.
Qed.      

Lemma plusP {char} r s (w: word char):
  reflect (w \in r \/ w \in s)
          (w \in plus r s).
Proof. rewrite !inE. exact: orP. Qed.

Lemma set_pick_size {F: finType} (X: {set F}) z: [pick z in X] = Some z -> #|X :\ z| < #|X|.
Proof.
  case: (pickP _) => // x [] H [] <-.
  by rewrite (cardsD1 x X) H addnC addn1.
Qed.
    

Lemma setU1_predI {F: finType} (X: {set F}) z: (z \notin X) -> (mem X) =1 predI (mem (z |: X)) (predC (pred1 z)).
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
    
Lemma all_predD {X} (q p: pred X) xs: all (predD q p) xs = all q xs && all (predC p) xs.
Proof. by rewrite all_predI andbC /predC. Qed.


Section AllButLastDef.
  
  Variable X: Type.
  Variable p: pred X.
  
  Fixpoint belast (xs: seq X) :=
    match xs with
      | [::] => [::]
      | [::x] => [::]
      | x::xs => x::(belast xs)
    end.

  Lemma belast_rcons (x: X) xs:
    belast (rcons xs x) = xs.
  Proof.
    elim: xs => [|y xs IHxs] //.
    rewrite rcons_cons /= IHxs.
    destruct xs => //.
  Qed.
                     
  Definition allbutlast xs := all p (belast xs).
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
  
  Lemma allbutlast_cat xs ys: allbutlast p (xs++ys) ->  allbutlast p xs /\ allbutlast p ys.
  Proof.
      elim: xs ys => [|x xs IHxs] ys //.
      rewrite -cat1s -catA cat1s.
      move/allbutlast_cons'' => /orP [].
        move/nilP. by case: xs IHxs; case ys => //.
      move/andP => []. by firstorder using allbutlast_cons.
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
  Proof. exact: all_predI. Qed.
  
  Lemma allbutlast_predD xs: allbutlast (predD p q) xs = allbutlast p xs && allbutlast (predC q) xs.
  Proof. exact: all_predD. Qed.

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
  
Section TransitiveClosure.

  Variable char: finType.
  Variable A: dfa char.

  Definition nPlus rs := foldr (@Plus char) (Void _) rs.

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
          
  Definition dfa_step_any x y := enum ( [pred a | dfa_step A x a == y] ).

  Lemma dfa_step_anyP x y a:
    reflect (dfa_step A x a = y)
            (a \in dfa_step_any x y).
  Proof.
    rewrite /dfa_step_any.
    apply: iffP. apply idP.
      by rewrite mem_enum !inE => /eqP.
    by rewrite mem_enum !inE => ->.
  Qed.
    
  
  Definition R0 x y := let r := nPlus (map (@Atom _) (dfa_step_any x y)) in
        if x == y then Plus r (Eps _) else r.
                                             
  Lemma mem_R0 w x y:
    reflect (w = [::] /\ x=y \/ exists2 a, w = [::a] & dfa_step A x a = y)
            (w \in R0 x y). 
  Proof.
    apply/iffP. apply idP.
      rewrite /R0 /=. case H: (x == y).
        rewrite -topredE /=. move/plusP => [].
          move/mem_nPlus => [r] /mapP [a].
          move/dfa_step_anyP => <- -> /eqP.
          by eauto.
        rewrite in_simpl /= => /eqP.
        move/eqP: H.
        by eauto.
      move/mem_nPlus => [r] /mapP [a].
      move/dfa_step_anyP => <- -> /eqP.
      by eauto.
    move => [[Hw Hxy]|[a Hw Hxay]].
      subst.
      rewrite /R0 /= eq_refl -topredE /=.
      apply/plusP. by eauto.
    rewrite /R0 /=.
    case: (x==y).
      rewrite -topredE /=. apply/plusP. left. 
      apply/mem_nPlus.
      exists (Atom a). apply/mapP. exists a => //.
        by apply/dfa_step_anyP.
      by rewrite !inE Hw /= eq_refl.
    apply/mem_nPlus.
      exists (Atom a). apply/mapP. exists a => //.
        by apply/dfa_step_anyP.
      by rewrite !inE Hw.
  Qed.

  Function R (X: {set A}) (x y: A) {measure [fun X => #|X|] X} :=
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
      [pred w | (last x (dfa_run' A x w) == y)
                && allbutlast (mem X) (dfa_run' A x w) ].

  Notation "'L^' X" := (L X) (at level 8).
     
  
  Lemma LP (X: {set A}) (x y: A) w:
    reflect (last x (dfa_run' A x w) = y /\ allbutlast (mem X) (dfa_run' A x w))
            (w \in L^X x y).
  Proof.
    apply: iffP. apply idP.
      rewrite inE. by move/andP => [] /eqP.
    rewrite inE. by move => [] /eqP -> ->.
  Qed.
  
  Lemma L_monotone (X: {set A}) (x y z: A): {subset L^X x y <= L^(z |: X) x y}.
  Proof.
    move => w.
    rewrite 2!in_simpl /= => /andP [] -> /=.
    apply: allbutlast_impl.
    move => x' /=.
    exact: (setU1r).
  Qed.

  Lemma L_nil X x y: reflect (x = y) ([::] \in L^X x y).
  Proof. apply: iffP; first by apply LP. by move => []. by []. Qed.

  Lemma setC1_pred1 (T: finType) (z: T): mem [set~ z] =1 predC (pred1 z).
  Proof.  move => x. by rewrite /= in_setC1.   Qed.
    
  Lemma run_split x z w: z \in dfa_run' A x w ->
    exists w1, exists w2,
      w = w1++w2 /\
      size w2 < size w /\
      z \notin belast (dfa_run' A x w1) /\
      last x (dfa_run' A x w1) = z.
  Proof.
    case: w => [|a w] //.
    elim: w a x z => [|b w IHw] a x z.
      rewrite !inE => /eqP ->.
      exists [::a]. by exists [::].
    rewrite /= in_cons.
    case: (eqP) => /=.
      exists [::a]. by exists (b::w).
    move/eqP => H0 H1.
    move/IHw: (H1) => [w1 [w2 [H2 H3]]].
    exists (a::w1). exists w2.
    rewrite cat_cons H2. firstorder.
    rewrite /=.
    elim: w1 H2 H H3 H4 => [|c w1 IHw1] H2 H H3 H4 //=.
    rewrite in_cons. apply/norP => //.
  Qed.
  
  Lemma L_split X x y z w:
    w \in L^(z |: X) x y ->
    w \in L^X x y \/
    exists w1, exists w2,
      w = w1 ++ w2 /\
      size w2 < size w /\
      w1 \in L^X x z /\
      w2 \in L^(z |: X) z y.
  Proof.
    move/LP => [H0 H1].
    case HX: (z \in X).
      move/set1UrP: HX H1 => ->.
      left. by apply/LP.
    case Hz: (z \in dfa_run' A x w).
      move/run_split: Hz => [w1 [w2 [H2 [H3 [H4 H5]]]]].
      right. exists w1. exists w2. firstorder.
        apply/LP. firstorder.
        move/negbT/setU1_predI/eq_allbutlast: (HX) => ->.
        rewrite allbutlast_predI /=. apply/andP. split.
          move: H1. rewrite H2 dfa_run'_cat.
          by move/allbutlast_cat => [].
        move: H4. by rewrite -has_pred1 -all_predC.
      apply/LP. firstorder.
        move: H0. rewrite H2.
        by rewrite dfa_run'_cat last_cat H5.
      move: H1. rewrite H2 dfa_run'_cat.
      move/allbutlast_cat => [].
      by rewrite H5.
    left.
    apply/LP. firstorder.
    move/negbT/setU1_predI/eq_allbutlast: (HX) => ->.
    rewrite allbutlast_predI /=. apply/andP. firstorder.
    move/negbT: Hz. rewrite -has_pred1 -all_predC.
    exact: all_allbutlast.
  Qed.

  Lemma L_cat (X: {set A}) x y z w1 w2:
    z \in X ->
    w1 \in L^X x z ->
    w2 \in L^X z y ->
    w1++w2 \in L^X x y.
  Proof.
    move => H /LP [H0 H1] /LP [H2 H3].
    apply/LP. rewrite dfa_run'_cat.
    rewrite last_cat H0 H2 /=. firstorder.
    apply: all_allbutlast_cat; last by done.
    apply: (allbutlast_last); first by done.
    rewrite !inE. instantiate (1:=x). by rewrite H0.
  Qed.

  Lemma L_catL X x y z w1 w2:
    w1 \in L^X x z ->
    w2 \in L^(z |: X) z y ->
    w1++w2 \in L^(z |: X) x y.
  Proof.
    move/(L_monotone z).
    apply: L_cat.
    exact: setU11. 
  Qed.

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
          
  Lemma  L_flatten (X: {set A}) z vv:  all (L^X z z) vv ->
    flatten vv \in L^(z |: X) z z.
  Proof.
    move => Hvv.
      elim: vv Hvv => [|v vv IHvv] Hvv;
        first by apply/L_nil.
      apply: L_catL.
        apply/LP. by move: Hvv =>  /= /andP [] /LP.
      apply: IHvv => //.
      by move: Hvv => /= /andP [] /andP [].
  Qed.
  
  Lemma L_rec (X: {set A}) x y z:
    L^(z |: X) x y =i plus (conc (L^X x z) (conc (star (L^X z z)) (L^X z y)))
                      (L^X x y).
  Proof.
    move => w.
    apply/idP/idP.
      apply/(size_induction size): w x y => w IHw x y.
      destruct w.
        move => Hw. apply/plusP. by right.
      move/L_split => [/LP [H1 H2]|[w1 [w2 [Hw' [H1 [Hw1 Hw2]]]]]].
        apply/plusP. right. by apply/LP.
      move: (IHw w2 H1 z y Hw2) Hw' => H4 ->. clear IHw H1.
      apply/plusP. left.
      apply/concP. exists w1 => //. exists w2 => //.
      apply/concP.
        move/plusP: H4 => [].
          move/concP => [w3 Hw3] [w4].
          move/concP => [w5 Hw5] [w6 Hw6].
          move => Hw4 Hw2'. subst.
          ecase (@nilP _ w3) => [->|/eqP Hw3nil].
            exists w5 => //. by exists w6 => //.
          exists (w3++w5).
          apply/starP. move/starP: Hw5 => [] vv Hvv ->.
          exists (w3::vv); last by done.
          by rewrite /= in_simpl /= Hw3nil /= Hw3.
        rewrite catA. by eauto.
      move => Hw2'.
      exists [::] => //.
      by exists w2 => //.

    move/plusP => []; last exact: L_monotone.
    move/concP => [w1 Hw1] [w2].
    move/concP => [w3 /starP [vv Hvv Hvvf]] [w4 Hw4] Hw2' Hw.
    subst.
    apply: L_catL => //.
      apply: L_catR => //.
    move: Hvv. rewrite all_predD => /andP [H0 H1].
    by apply: L_flatten.
  Qed.              
  

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
      case: pickP => [z|Hset0 w];
        first by rewrite in_set0.
      apply/LP/mem_R0.
        move => [] H.
        move/(allbutlast_pred0 Hset0).
        destruct w; try destruct w => //;
        by eauto.
      move => [[-> ->]|[a [-> <-]]]; last by done.
      apply/LP. by apply/L_nil.
    move => HX w.
    rewrite R_equation.
    case: pickP => [z Hz|Hset0].
      have HsizeX: (#|X :\ z| = n).
        move: HX. rewrite (cardsD1 z) Hz add1n.
        by move => [].
      rewrite -(setD1K Hz).
      rewrite (L_rec _ _) -2!topredE /= /plus /= setD1K => //.
      rewrite !IHn => //.
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
    apply/LP/idP.
      move => []. by rewrite !inE => /eqP.
    rewrite in_simpl => /eqP -> /=.
    firstorder.
    erewrite eq_allbutlast.
    apply allbutlast_predT.
    move => z. by rewrite /setT !inE.
  Qed.
                 
  Definition dfa_to_re: regular_expression char :=
    nPlus (map  (R^setT (dfa_s A)) (enum (dfa_fin A))).
    
  
  Lemma dfa_to_re_correct: dfa_lang A =i dfa_to_re.
  Proof.
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

  Lemma nPlus_standard rs: all (standard char) rs -> standard char (nPlus rs).
  Proof. by elim: rs => [|r rs IHrs]. Qed.

  Lemma R_standard' n (X: {set A}) x y: #|X| = n ->  standard char (R^X x y).
  Proof.
    elim: n X x y => [|n IHn] X x y;
      rewrite R_equation;
      case: (pickP) => //;
      rewrite /R0; case: (x == y) => //;
      move => H0 H1;                                    
      apply: nPlus_standard;
      apply/allP => r;
    by move/mapP => [a] _ ->. 
  Qed.
  
  Lemma R_standard (X: {set A}) x y: standard char (R^X x y).
  Proof. apply: R_standard'. by econstructor. Qed.
  
  Lemma dfa_to_re_standard: standard char dfa_to_re.
  Proof.
    apply: nPlus_standard.
    apply/allP => r.
    move/mapP => [x Fx] ->.
    apply: R_standard.
  Qed.
  
    
End TransitiveClosure.

Section Ext_Standard.
  Variable char: finType.
  Definition ext_re_to_std_re (r: regular_expression char) := dfa_to_re (re_to_dfa r).

  Lemma ext_re_to_std_re_standard r: standard char (ext_re_to_std_re r).
  Proof. by rewrite dfa_to_re_standard. Qed.
  
  Lemma ext_re_to_std_re_correct r: (ext_re_to_std_re r) =i r.
  Proof.
    move => w.
    by rewrite /ext_re_to_std_re -dfa_to_re_correct re_to_dfa_correct.
  Qed.
    
End Ext_Standard.
