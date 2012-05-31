Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun ssrbool finset choice.
Require Import automata misc regexp.
Require Import Program.Equality.

Section MyhillNerode.
  Variable char: finType.
  Definition word:= word char.

  Section Relation.
    Variable X: finType.
    Variable L: language char.

    Definition MH_rel x y := forall z, x++z \in L <-> y++z \in L.

    (* We model finiteness of equivalence classes
     by functions to some finType. *)

    Definition Fin_eq_cls := word -> X.
    
    (* We define what it means to be a refinement
     of the MH relation: *)
    Definition MH_rel_ref (f: Fin_eq_cls) := forall x y, f x = f y -> MH_rel x y.
    
  End Relation.
  
  Section ToDFA.
    Variable L: language char.
    Variable X: finType.
    Variable f: Fin_eq_cls X.
    Variable ref: MH_rel_ref X L f.


    
    Fixpoint repr n: seq word :=
      match n with
      | 0 => [::[::]]
      | n.+1 => flatten (map (fun w => map (fun a => rcons w a) (enum char)) (repr n))
      end.

    Lemma mem_flatten (w: word) ww: w \in flatten ww -> { w' | w' \in ww /\ w \in w' }.
    Proof.
      elim: ww => [|w' ww IHww] //.
      rewrite /= mem_cat.
      case H: (w \in w') => //=.
        move => H0. exists w'.
        by rewrite mem_head.
      move/IHww => [] w'' [] H0 H1.
      exists w''.
      by rewrite in_cons H0 orbT.
    Qed.

    Lemma mem_flatten' (w: word) w' (ww: seq (seq word)): w \in w' -> w' \in ww -> w \in flatten ww.
    Proof.
      elim: ww => [|w'' ww IHww] //.
      rewrite /= in_cons => H0 /orP [/eqP <-|].
        by rewrite mem_cat H0.
      move/(IHww H0) => H1.
      by rewrite mem_cat H1 orbT.
    Qed.
      
    
    Lemma repr_correct n w: w \in repr n <-> size w = n.
    Proof.
      elim: n w => [|n IHn] w.
        split.
          rewrite /= -topredE /=.
          by move/orP => [] // /eqP ->.
        by move/size0nil => ->.
      split.
        rewrite /= => /mem_flatten => [].
        move => [] s [].
        move/mapP => [] v.
        move/IHn => H0 -> /mapP [] c _ ->.
        by rewrite size_rcons H0.
      case/lastP: w => [|w a] //.
      rewrite size_rcons => H0.
      inversion H0. move/IHn: (H1).
      rewrite /= => H2.
      apply: (mem_flatten' _ (map (fun a => rcons w a) (enum char))).
        apply/mapP.
        exists a => //.
        by rewrite mem_enum.
      apply/mapP.
      exists w => //.
      by rewrite H1.
    Qed.

    Definition repr_type n : finType := seq_sub_finType (repr n).

    Lemma exists2_exists (Y: Type) (p q: Y -> Prop): (exists2 x: Y, p x & q x) <-> exists x: Y, p x /\ q x.
    Proof.
      split.
        move => [] x H0 H1.
        by exists x.
      move => [] x [] H0 H1.
      by exists x.
    Qed.

    
    Definition repr_type_word n (w: repr_type n): word.
    Proof.
      inversion w.
      exact ssval.
    Defined.

    Lemma repr_type_word_inj n: injective (repr_type_word n).
    Proof.
      move => x y.
      rewrite /repr_type_word /=.
      case: x. case: y.
      move => x Hx y Hy H0.
      

     Lemma test n x y (Hy: y \in repr n) Hx: y = x -> 
       {| ssval := y; ssvalP := Hy |} = {| ssval := x; ssvalP := Hx |}.
     move => ->.

      
      
      
      
    
    Lemma repr_type_correct n (w: repr_type n): size w = n.

      
    Fixpoint canonical_repr n: finType :=
      match n with
        | 0 => Q
                 
  End ToDFA.
End MyhillNerode.
