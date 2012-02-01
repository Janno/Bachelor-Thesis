Require Import Coq.Lists.List.
Require Import Omega.

Set Implicit Arguments.

Lemma cons_append : forall (X: Type) (a:X) (l : list X), 
exists l', exists a', (l' ++ a'::nil) = a::l.
intros. induction l.
  exists nil. exists a. trivial.
  destruct IHl as [l' [a' E]].
  destruct l'. inversion E. exists (a::nil). exists a0. trivial.
  inversion E. subst.
  exists (a::a0::l'). exists a'. trivial.
Qed.


Lemma le_O y : O <= y.
Proof. induction y. constructor. constructor. trivial. Qed.

Lemma le_SS x y : x <= y -> S x <= S y.
Proof. induction y. intros. inversion H. subst. constructor.
intros. inversion H. subst. constructor.
subst. constructor. apply IHy. trivial. Qed. 

Lemma le_S x y : S x <= y -> x <= y.
Proof. revert x. induction y; intros. inversion H.
inversion H. subst. constructor. constructor. subst. eauto using le. Qed.

Lemma le_SS' x y : S x <= S y -> x <= y.
Proof. revert y. induction x; intros. inversion H. subst. constructor. apply le_O.
inversion H. constructor. subst. pose proof (le_S H1). trivial. Qed.

Lemma le_trans x y z :
x<=y -> y<=z -> x<=z.
Proof. revert y z. induction z. intros. inversion H0. subst. trivial.
intros. inversion H0. subst. trivial.
constructor. apply IHz; eauto. Qed.
Lemma lt_tran' {x} y {z} :
x < y -> y < z -> S x < z.
Proof. intros A B. eapply le_trans. eapply le_SS. eexact A. exact B. Qed.


Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) :
( forall x, ( forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof. intros A x. apply A. induction (f x). intros. inversion H.
intros y B. apply A. intros z C. apply IHn.
generalize (lt_tran' C B). intros. eauto using le, le_SS'. Qed.

Fixpoint length (X: Type) (l: list X) : nat :=
match l with
| nil => O
| a::l' => S(length l')
end.

Lemma length_app (X: Type) (l1 l2: list X) : length(l1 ++ l2) = length l1 + length l2.
induction l1. trivial.
simpl. rewrite IHl1. trivial. Qed.

Lemma append_induction : forall (X : Type) (P : list X -> Prop),
       P nil ->
       (forall (a : X) (l : list X), P l -> P (l ++ a::nil)) ->
       forall l : list X, P l.
Proof. intros.
eapply (size_induction (@length X)).
intros. induction x. trivial.
assert (P x). apply IHx. intros. apply H1. simpl. constructor. exact H2.
destruct (cons_append a x) as [x' [a' E]]. rewrite <- E.
assert (length (x' ++ a'::nil) = length(a::x)). rewrite E. trivial.
revert H3.
rewrite length_app. unfold length at 2. rewrite <- plus_n_Sm. rewrite <- plus_n_O. intros H3.
assert (P x'). apply H1. rewrite <- H3. constructor.
apply H0. exact H4. Qed.
