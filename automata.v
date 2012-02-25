Require Import ssreflect ssrbool eqtype fintype finfun seq fingraph.

Set Implicit Arguments.

Section FA.
Variable S: finType.
Definition word := seq S.


Section DFA.
Inductive dfa (Q: finType) (s0: Q) (f: pred Q) : rel (Q * S * Q)  -> Type :=
| dfaI  (d: Q -> S -> Q) : dfa Q s0 f 
(fun x y => 
  let (t, q) := x in 
  let (p, s) := t in 
  let (t', q') := y in 
  let (p', s') := t' in   
  q == p'
).

Section Acceptance.
Variable Q: finType.
Variable s0: Q.
Variable d: Q -> S -> Q.
Variable f: pred Q.
Definition AutR {R} (_: dfa Q s0 f R) := R.

Variable R': rel (Q * S * Q).
Variable A: dfa Q s0 f R'.

Let R := AutR A.

(* dfa A accepts word w starting in state q *)
Fixpoint accept (q: Q) (w: word) :=
match w with
| nil => f q
| a::w' => 
  existsb q': Q, 
  existsb a': S, 
  existsb q'': Q, 
  R (q, a, q') (q', a', q'') && accept q' w'
end.


Definition step (s: Q) (a: S) (s' : Q) : Prop := d s a = s'.
Inductive eat : Q -> seq S -> Q -> Prop :=
| eatNil s : eat s nil s
| eatCons s s'' s' a w : step s a s'' -> eat s'' w s' -> eat s (a::w) s'.
Definition acceptance (w: seq S) : Prop := exists s', eat s0 w s' /\ f s'.


Fixpoint eatc (s: Q) (w: seq S) : Q :=
if w is a :: w' then eatc (d s a) w' else s.
Definition acceptancec (w: seq S) := f (eatc s0 w).

End Acceptance.

End DFA.


Section NFA.
Inductive nfa (Q: finType) (s0: Q) (d: Q -> S -> pred Q) (f: pred Q) : Type :=
| nfaI.

Section Acceptance.
Variable Q: finType.
Variable s0: Q.
Variable d: Q -> S -> pred Q.
Variable f: pred Q.
Variable A: nfa Q s0 d f.

Definition nstep (s: Q) (a: S) (s' : Q) : Prop := d s a s'.
Inductive neat : Q -> seq S -> Q -> Prop :=
| neatNil s : neat s nil s
| neatCons s s'' s' a w : nstep s a s'' -> neat s'' w s' -> neat s (a::w) s'.

Definition nacceptance (w: seq S) : Prop := exists s', neat s0 w s' /\ f s'.


Fixpoint neatc (s: Q) (w: seq S) {struct w} : seq Q :=
if w is a :: w' then 
undup (
  flatten (
    map (fun s' => neatc s' w') (filter (d s a) (enum Q))
  )
)
else [:: s].

Definition nacceptancec (w: seq S) := existsb q : Q, (q \in (neatc s0 w)) && f q.

End Acceptance.
End NFA.


Section PowersetConstruction.
Variable Q: finType.
Variable s0: Q.
Variable d: Q -> S -> pred Q.
Variable f: pred Q.
Variable A: nfa Q s0 d f.

Definition predT (q: Q) := true.
Definition powerset := pffun_on false A predT.
End PowersetConstruction.


End FA.