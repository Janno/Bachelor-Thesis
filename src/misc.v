(*
    Authors: Thierry Coquand, Vincent Siles
*)
Require Import ssreflect ssrnat seq ssrbool eqtype fintype choice.

Set Implicit Arguments.


Section Language.

Variable char: finType.
Definition word := seq char.
Definition language := pred word.

End Language.


Lemma ltn_trans_tight m n p : m < n -> n < p -> m < p.-1.
Proof. elim: p n m => [|p IHp ] n m.
  by [].
move => H0. rewrite leq_eqVlt => /orP [].
  move/eqP => <-. exact: H0.
rewrite ltnS => H1. move: (IHp _ _ H0 H1) => /=.
case: p IHp H1 => [|p] IHp H1.
  by [].
by exact: ltnW.
Qed.

Lemma ltn_trans_tight' m n p : m < n -> n < p.-1 -> m < p.-1.
Proof. elim: p n m => [|p IHp ] n m.
  by [].
move => H0. rewrite leq_eqVlt => /orP [].
  move/eqP => <-. apply: leqW. by [].
move/leqW. apply: ltn_trans_tight. by apply: leqW.
Qed.

Lemma size_induction {X : Type} (f : X -> nat) (p: X ->Prop) :
( forall x, ( forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof. intros A x. apply A. induction (f x). by [].
intros y B. apply A. intros z C. apply IHn.
move: C B. apply: ltn_trans_tight. Qed.


