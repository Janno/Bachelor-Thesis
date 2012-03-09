Require Import ssreflect ssrnat seq ssrbool eqtype fintype.

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

Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) :
( forall x, ( forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof. intros A x. apply A. induction (f x). by [].
intros y B. apply A. intros z C. apply IHn.
move: C B. apply: ltn_trans_tight. Qed.


(* seq X helpers. *)
Section Seq.

Variable X: Type.
  
Lemma size_take_bound (w: seq X) n : size (take n w) <= size w.
Proof. elim: n w => [|n IHn] w.
  by rewrite take0.
rewrite size_take.
case_eq (n.+1 < size w).
  apply: leq_trans. apply: leqW. exact: ltnSn.
by [].
Qed.

Lemma size_take_bound' (w: seq X) n : size (take n w) <= n.
Proof. elim: n w => [|n IHn] w.
  by rewrite take0.
rewrite size_take.
case_eq (n.+1 < size w).
  move => _. exact: ltnSn.
move/negbT. by rewrite -leqNgt.
Qed.

Lemma size_take_underflow (w: seq X) n : size (take n w) < n -> size w < n.
Proof. elim: n w => [|n IHn] w.
  by rewrite take0.
rewrite size_take.
case_eq (n.+1 < size w).
  move => _. by rewrite ltnn.
move/negbT. by rewrite -leqNgt.
Qed.

Lemma take_undersize (w: seq X) n k : n <= k -> take n (take k w) = take n w.
Proof. elim: w k n => [|a w IHw] k n.
  by [].
rewrite take_cons. destruct k. 
  by rewrite leqn0 => /eqP ->.
rewrite take_cons. destruct n.
  by [].
move => H0. rewrite IHw.
  by [].
move: H0. rewrite -{1}(addn1 n) -(addn1 k).
by rewrite leq_add2r.
Qed.

Lemma take_oversizeS (w: seq X) n: size w < n -> take n w = take n.-1 w.
Proof. move: w n. apply: last_ind => [|w a IHw] n.
  by [].
rewrite -cats1 => H0. rewrite take_oversize.
  rewrite take_oversize.
    by [].
  destruct n.
    by [].
  by [].
exact: ltnW.
Qed.

End Seq.
