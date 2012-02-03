Set Implicit Arguments.
Require Import List.

Section FiniteType.
Variable X: Type.
Variable eqX : forall (x y: X), {x=y} + {x<>y}.

Inductive In : list X -> X -> Prop :=
| InHead l x : In (x::l) x
| InTail l x y : In l y -> In (x::l) y.

Definition finite := exists l, forall x: X, In l x.

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
