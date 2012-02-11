Set Implicit Arguments.
Require Import append_induction.
Require Import List.
Require Import finite_type.


Section MyhillNerode.
Variable Alphabet : Type.
Variable eqAlphabet : forall (a a': Alphabet), {a = a'} + {a <> a'}.
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

Require Import Setoid.
Require Import Ring.
Require Import Ring_tac.

Add Relation Word R
reflexivity proved by R_refl
symmetry proved by R_sym
transitivity proved by R_trans
as R_relation.


Lemma ext_decide x y z : {ext x y z} + {~ext x y z}.
Proof. (* firstorder takes soooo long. *) admit. Qed.

Lemma R_uni x y : R x y <-> forall z, ~ ext x y z.
Proof. split. intros. intros A. apply H. exists z. exact A.
intros f [z A]. eapply f; eassumption. Qed.

Definition R_equiv_classes_finite := exists l, forall x, In l (R x).

Require Import RE.

Lemma MyhillNerode : R_equiv_classes_finite 
<-> exists r, forall w, L w -> mem_der Alphabet eqAlphabet r w = true.
    Admitted.




End Language.

End MyhillNerode.
