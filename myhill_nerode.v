Set Implicit Arguments.
Require Import append_induction.
Require Import List.

Section FiniteType.
Variable X: Type.
Variable eqX : forall (x y: X), {x=y} + {x<>y}.

Inductive In : list X -> X -> Prop :=
| InHead l x : In (x::l) x
| InTail l x y : In l y -> In (x::l) y.

Lemma InDecide l (x: X) : {In l x} + {~In l x}.
intros. induction l. right. intros A. inversion A.
destruct (eqX a x). 
  subst. eauto using In.
  destruct IHl. left. eauto using In.
    right. intros A. inversion A; eauto.
Qed.


Definition Inb l x : bool :=
match InDecide l x with
| left _ => true
| right _ => false
end.

Definition map Y f (l: list X) : list Y :=
match l with
| nil => nil
| a::l' => f(a)::map f l'
end.

Definition list_proof (p: X -> Prop) l := map p l. 

Lemma enum_proof (p : X -> Prop) (l: list X) : 
(forall x: X, In l x) ->
(forall x: X, In l x -> p x) ->
forall x: X, p x.
firstorder. Qed.

End FiniteType.


Section MyhillNerode.
Variable Alphabet : Type.
Variable eqAlphabet : forall (a a' : Alphabet), {a = a} + {a <> a'}.
Variable alphabet : list Alphabet.
Variable finiteAlphabet : forall (a: Alphabet), In alphabet a.

Section Language.
Definition Word := list Alphabet.
Definition Language := Word -> Prop.

Variable L : Language.
Variable eqL : forall (w: Word), {L w} + {~L w}.

Definition ext x y z := (L (x++z) /\ ~L (y++z)) \/ (L (y++z) /\ ~L (x++z)).
Definition R x y := ~ exists z, ext x y z.

Lemma R_sym x y : R x y -> R y x.
Proof. firstorder. Qed.

Lemma R_refl x : R x x.
Proof. firstorder. Qed.

Lemma R_trans x y z : R x y -> R y z -> R x z.
Proof. firstorder. Qed.

Lemma ext_decide x y z : {ext x y z} + {~ext x y z}.
Proof. firstorder. Qed.

Lemma R_uni x y : R x y <-> forall z, ~ ext x y z.
Proof. split. intros. intros A. apply H. exists z. exact A.
intros f [z A]. eapply f; eassumption. Qed.

Lemma RDecide x y : {R x y} + {~R x y}.
Proof. 
revert y. apply append_induction.
Qed.

End Language.

End MyhillNerode.