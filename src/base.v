(* Author: Christian Doczkal *)
Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ssrfun choice fintype finset path fingraph bigop.
Require Import Relations.
Require Import tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * A least fixed point operator for finType *)

Lemma iter_fix T (F : T -> T) x k n : 
  iter k F x = iter k.+1 F x -> k <= n -> iter n F x = iter n.+1 F x.
Proof.
  move => e. elim: n. rewrite leqn0. by move/eqP<-.
  move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
  move/IH => /= IHe. by rewrite -!IHe.
Qed.

Section FixPoint.
  Variable T :finType.
  Definition set_op := {set T} -> {set T}.
  Definition mono (F : set_op)  := forall p q : {set T} , p \subset q -> F p \subset F q.

  Variable F : {set T} -> {set T}.
  Hypothesis monoF : mono F.

  Definition lfp := iter #|T|.+1 F set0.

  Lemma lfp_ind (P : {set T} -> Type) : P set0 -> (forall s , P s -> P (F s)) -> P lfp.
  Proof.
    move => P0 Pn. rewrite /lfp. set n := #|T|.+1. elim: n => //= n. exact: Pn.
  Qed.

  Lemma iterFsub n : iter n F set0 \subset iter n.+1 F set0.
  Proof.
    elim: n => //=; first by rewrite sub0set.
    move => n IH /=. by apply: monoF.
  Qed.

  Lemma iterFsubn m n : m <= n -> iter m F set0 \subset iter n F set0.
  Proof.
    elim : n; first by rewrite leqn0 ; move/eqP->.
    move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
    move/IH => /= IHe. apply: subset_trans; first apply IHe. exact:iterFsub.
  Qed.
 
  Lemma lfpE : lfp = F lfp.
  Proof.
    have: ~~ [ forall m : 'I_#|T|.+1 , iter m F set0 \proper iter m.+1 F set0 ].
      apply/negP => /forallP H.
      have P : forall n : 'I_#|T|.+1 , exists x : T , x \in iter n.+1 F set0 :\: iter n F set0.
        move => n ; move : (H n). case/properP => _ [x x1 x2]. exists x. by rewrite in_setD x1 x2.
      pose i (o : 'I_#|T|.+1) : T := xchoose (P o).
      have inj_i : injective i. 
        move => o o'. rewrite /i => e. move : (xchooseP (P o)) (xchooseP (P o')).
        rewrite e {e}. set x := xchoose _. move : o o' x => [n pn] [m pm] x.
        rewrite !in_setD /=. case/andP => Hn1 Hn2. case/andP => Hm1 Hm2.
        case (ltngtP n m); last by move/eqP => e'; apply/eqP.
        - move => /iterFsubn /subsetP /(_ x Hn2). by rewrite (negbTE Hm1).
        - move => /iterFsubn /subsetP /(_ x Hm2). by rewrite (negbTE Hn1).
      move : (max_card (fun x => x \in codom i)). by rewrite (card_codom inj_i) /= !card_ord ltnn. 
    rewrite negb_forall. case/existsP => x H.
    have A : iter x F set0 = iter x.+1 F set0. 
      apply/eqP. by rewrite eqEproper iterFsub /= H.
    apply : iter_fix; first apply A. by case:x {H A} => *; auto.
  Qed.
End FixPoint.

