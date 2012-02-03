(*** Semantics WS 2011 ***)
(*** Coq Part of Assignment 9 ***)
(*** Solution ***)

Set Implicit Arguments.
Tactic Notation "inv" hyp(A)  := inversion A ; subst ; clear A.

Section Relation.
Variable X : Type.

Definition rel : Type := X -> X -> Prop.

Definition reflexive (r : rel) : Prop :=
forall x, r x x.

Definition symmetric (r : rel) : Prop :=
forall x y, r x y -> r y x.

Definition transitive (r : rel) : Prop :=
forall x y z, r x y -> r y z -> r x z.

Definition functional (r : rel) : Prop :=
forall x y z, r x y -> r x z -> y=z.

Definition reducible (r : rel) (x : X) : Prop :=
exists y, r x y.

Definition normal (r : rel) (x : X) : Prop :=
~ reducible r x.

Definition total (r : rel) : Prop :=
forall x, reducible r x.

Definition rle (r r' : rel) : Prop :=
forall x y, r x y -> r' x y.

Definition req (r r' : rel) : Prop :=
rle r r' /\ rle r' r.

Definition reddec (r : rel) : Prop :=
forall x, reducible r x \/ normal r x.

Goal forall r, reflexive r -> forall x, reducible r x.

Proof. firstorder. Qed.

(** Reflexive Transitive Closure *)

Inductive star (r : rel) : rel :=
| starR x : star r x x
| starS x y z : r x y -> star r y z -> star r x z.

Lemma star_reflexive r :
reflexive (star r).

Proof. intros x. constructor. Qed.

Lemma star_transitive r :
transitive (star r).

Proof. intros x y z A B. induction A ; eauto using star. Qed.

Lemma star_expansive r :
rle r (star r).

Proof. hnf. eauto using star. Qed.

Lemma star_right r x y z :
star r x y -> r y z -> star r x z.

Proof. intros A B. induction A ; eauto using star. Qed.

Lemma star_least r s :
reflexive s -> transitive s -> rle r s -> rle (star r) s.

Proof. intros R T A x y B. induction B ; eauto. Qed.

Lemma star_monotone r r' :
rle r r' -> rle (star r) (star r').

Proof. intros A x y B. induction B ; eauto using star. Qed.

Lemma star_symmetry r :
symmetric r -> symmetric (star r).

Proof. intros A x y B. 
induction B ; eauto using star, star_right. Qed.

Lemma star_idempotent r :
req (star (star r)) (star r).

Proof. split.
apply star_least. apply star_reflexive. apply star_transitive. hnf. trivial.
apply star_expansive. Qed. 

Lemma star_normal r x y :
normal r x -> star r x y -> x = y.

Proof. intros A B. inversion B ; subst ; trivial.
exfalso. apply A. exists y0. assumption. Qed.

Goal forall r x y,
star r x y <-> 
forall s : rel, reflexive s -> transitive s -> rle r s -> s x y.

Proof. split.
intros A s R T B. now induction A ; eauto.
intros A. specialize (A (star r)).
eauto using star_reflexive, star_transitive, star_expansive. Qed.

Lemma star_ind' (r : rel) (x y : X) (p : X -> Prop) :
p y ->
( forall x x', r x x' -> star r x' y -> p x' -> p x) ->
star r x y -> p x.

Proof. intros A B C. induction C ; eauto. Qed.

(** Convertibility and Joinability *)

Definition sym (r : rel) : rel :=
fun x y => r x y \/ r y x.

Definition convertible (r : rel) : rel :=
star (sym r).

Definition joinable (r : rel) (x y : X) : Prop :=
exists z, star r x z /\ star r y z.

Lemma star_convertible r :
rle (star r) (convertible r).

Proof. apply star_monotone ; cbv ; auto. Qed.

Lemma convertible_symmetric r :
symmetric (convertible r).

Proof. apply star_symmetry. firstorder. Qed.

Lemma joinable_convertible r :
rle (joinable r) (convertible r).

Proof. intros x y J.  destruct J as [z [A B]].
apply star_convertible in A.
apply star_convertible, convertible_symmetric in B.
eapply star_transitive ; eassumption. Qed.

Lemma star_joinable r :
rle (star r) (joinable r).

Proof. firstorder using star.  Qed.

Definition Church_Rosser (r : rel) : Prop :=
rle (convertible r) (joinable r).

(** Confluence *)

Definition confluent (r : rel) : Prop := 
forall x y z, star r x y -> star r x z -> joinable r y z.

Definition semi_confluent (r : rel) : Prop :=
forall x y z, r x y -> star r x z -> joinable r y z.

Lemma Church_Rosser_confluent r :
Church_Rosser r -> confluent r.

Proof. intros A x y z B C. apply A.
apply star_convertible, convertible_symmetric in B.
apply star_convertible in C.
eapply star_transitive ; eassumption. Qed.

Lemma confluent_semi_confluent r : confluent r -> semi_confluent r.

Proof. firstorder using star_expansive. Qed.

Lemma semi_confluent_Church_Rosser r :
semi_confluent r -> Church_Rosser r.

Proof. intros A x y B.
induction B. now exists x ; split ; constructor.
destruct IHB as [u [B1 B2]].
destruct H. now exists u ; eauto using star.
assert (C : joinable r x u) by eauto.
destruct C as [v [C1 C2]].
exists v ; firstorder using star_transitive. Qed.

(** Strong Confluence *)

Definition ref (r : rel) : rel :=
fun x y => x=y \/ r x y.

Definition strongly_confluent (r : rel) : Prop :=
forall x y z, r x y -> r x z -> 
exists u, star r y u /\ ref r z u.

Lemma strong_confluence r :
strongly_confluent r -> semi_confluent r.

Proof. intros S x y z A B.
revert y A ; induction B as [x | x z' z] ; intros y A.
now exists y ; eauto using star.
destruct (S x y z' A H)  as [u [S1 S2]].
destruct S2 ; subst.
now exists z ; firstorder using star, star_transitive.
assert (C : joinable r u z) by auto. 
destruct C as [v [C1 C2]].
exists v ; firstorder using star_transitive. Qed.

Goal forall r, functional r -> strongly_confluent r.

Proof. intros r A x y1 y2 B C.
assert (y1=y2) by eauto. subst.
exists y2. firstorder using star. Qed.

Definition diamond (r : rel) : Prop :=
forall x y z, r x y -> r x z -> 
exists u, r y u /\ r z u.

(*** Exercise 9.1 a ***)
Lemma confluent_diamond_star  r :
confluent r <-> diamond (star r).
split; intros A x y z B C.
eapply A; now eauto.
eapply A; now eauto.
Qed.

(*** Exercise 9.1 b ***)
Lemma diamond_strongly_confluent r :
diamond r -> strongly_confluent r.

Proof. intros A x y z B C.
destruct (A x y z B C) as [u [D E]].
exists u. cbv. eauto using star. Qed.

(*** Exercise 9.1 c ***)
Goal forall r, diamond r -> diamond (star r).

Proof. intros r A.
apply diamond_strongly_confluent, 
  strong_confluence,
  semi_confluent_Church_Rosser,
  Church_Rosser_confluent in A.
exact A. Qed.

(** Normal Forms and Normalization *)

Definition normal_form (r : rel) : rel :=
fun x y => star r x y /\ normal r y.

Lemma normal_form_functional (r : rel) :
functional r -> functional (normal_form r).

Proof. intros A x y z [B C] [D E].
induction B ; destruct D ; firstorder.
assert (y=y0) by eauto. subst. auto. Qed.

Lemma confluent_functional_normal_form r :
confluent r -> functional (normal_form r).

Proof. intros A x y z [B1 B2] [C1 C2].
assert (D : joinable r y z) by eauto.
destruct D as [u [D1 D2]].
assert (y = u) by eauto using star_normal.
assert (z = u) by eauto using star_normal.
congruence. Qed.

Inductive normalizes (r : rel) : X -> Prop :=
| normalizesI1 x : normal r x -> normalizes r x
| normalizesI2 x y : r x y -> normalizes r y -> normalizes r x.

Lemma normalizes_normal_form r x :
normalizes r x <-> reducible (normal_form r) x.

Proof. split.
intros A. induction A. 
   exists x. now firstorder using star_reflexive.
   destruct IHA as [z B]. exists z. now firstorder using star.
intros [y [A B]]. induction A ; eauto using normalizes. Qed.

Definition normalizing (r : rel) : Prop :=
forall x, normalizes r x.

Goal forall r,
normalizing r <-> total (normal_form r).

Proof. split ; intros A x ; apply normalizes_normal_form, A. Qed.

Lemma normalizing_confluent r x y :
normalizing r -> confluent r ->
(convertible r x y <-> exists z, normal_form r x z /\ normal_form r y z).

Proof. intros N C. split.
intros A. 
   assert (B: joinable r x y) 
   by (apply semi_confluent_Church_Rosser ; 
       firstorder using star_expansive).
   destruct B as [u [B1 B2]].
   assert (D : reducible (normal_form r) u)
   by (apply normalizes_normal_form ; trivial).
   destruct D as [v [D1 D2]]. exists v.
   now firstorder using star_transitive.
intros [z [[A _] [B _]]].
   apply joinable_convertible. firstorder. Qed.

(** Termination *)

Inductive terminates (r : rel) : X -> Prop :=
| terminatesI x : (forall y, r x y -> terminates r y) -> terminates r x.

Definition terminating (r : rel) : Prop :=
forall x, terminates r x.

Lemma reddec_terminates_normalizes r x :
reddec r -> terminates r x -> normalizes r x.

Proof. intros D T. induction T as [x _ IH].
destruct (D x) ; firstorder using normalizes. Qed.

Lemma functional_normalizes_terminates r x :
functional r -> normalizes r x -> terminates r x.

Proof. intros F N. induction N as [x A|x y A B] ; constructor.
intros y B. exfalso. apply A. now exists y ; trivial.
intros y' C. assert (y=y') by (eapply F ; eauto). subst. trivial. Qed.

Goal forall r, 
reddec r -> terminating r -> total (normal_form r).

Proof. intros r D T x. 
apply normalizes_normal_form, 
  reddec_terminates_normalizes 
  ; auto. Qed.

Definition locally_confluent (r : rel) : Prop :=
forall x y z, r x y -> r x z -> joinable r y z.

Lemma Newman (r : rel) :
terminating r -> locally_confluent r -> confluent r.

Proof. intros T L x. specialize (T x). 
induction T as [x _ IH]. intros y z A B.
destruct A as [x|x y' y]. now exists z ; eauto using star.
destruct B as [x|x z' z]. now exists y ; eauto using star.
assert (C : joinable r y' z') by eauto. (* loc confluenced used *)
destruct C as [u [C1 C2]].
assert (D : joinable r u z) by eauto. (* IH used *)
destruct D as [w [D1 D2]].
assert (E : joinable r y w). 
now apply IH with (y:=y') ; trivial ; eapply star_transitive ; eauto.
destruct E as [w' [E1 E2]].
exists w'. intuition. eapply star_transitive ; eauto. Qed.

(*** Exercise 9.2 ***)
Goal forall (r : rel) (p : X -> Prop) x,
terminates r x ->
(forall x, (forall y, r x y -> p y) -> p x) -> 
p x.

Proof. intros r p x A B. induction A. auto. Qed.

(*** Exercise 9.2 ***)
Goal forall (r : rel) (p : X -> Prop) x,
terminates r x -> 
(forall x, terminates r x -> (forall y, r x y -> p y) -> p x) -> 
p x.

Proof. intros r p x A B. apply B ; trivial. induction A ; eauto. Qed.

(** Transitive Closure Preserves Termination *)

Inductive plus (r : rel) : rel :=
| plusO x y : r x y -> plus r x y
| plusS x x' y : r x x' -> plus r x' y -> plus r x y.

Goal forall r x, terminates r x -> terminates (plus r) x.

Proof. (* tricky *)
intros r x A.
induction A as [x _ IHA]. constructor ; intros y B.
destruct B as [x y B | x x' y B C]. now auto.
apply IHA in B. inversion B. auto. Qed.

(** Composition *)

Definition comp (r s : rel) : rel :=
fun x z => exists y, r x y /\ s y z.

Goal forall r s, functional r -> functional s -> functional (comp r s).

Proof. intros r s A B x y y' [z [C1 C2]] [z' [D1 DS2]].
assert (z=z') by eauto. subst. eauto. Qed.

Goal forall r s, reflexive r -> reflexive s -> reflexive (comp r s).

Proof. firstorder. Qed.

Lemma transitive_rle r s :
rle r s -> transitive s -> rle (comp r s) s.

Proof. firstorder. Qed.

Lemma reflexive_rle r s :
rle r s -> reflexive s -> rle r (comp r s).

Proof. firstorder. Qed.

Goal forall r, req (comp (star r) (star r) ) (star r).

Proof. split. 
apply transitive_rle. hnf ; trivial. apply star_transitive.
apply reflexive_rle. hnf ; trivial. apply star_reflexive. Qed.

Goal forall r, rle (comp (star r) r) (star r).

Proof. intros r x y [x' [A B]].
eauto using star_right. Qed.

(** Inverse *)

Definition inverse (r : rel) : rel :=
fun x y => r y x.

Goal forall r,
rle (star (inverse r)) (star (sym r)).

Proof. firstorder using star_monotone. Qed.

Goal forall r,
symmetric r <-> rle (inverse r) r.

Proof.  cbv. auto. Qed.

End Relation.

(** greater than on nat *)

Require Import Omega.

Lemma complete_induction (p : nat -> Prop) (x : nat) :
(forall x, (forall y, y<x -> p y) -> p x) -> p x.

Proof. intros A. apply A. induction x ; intros y B.
exfalso ; omega.
apply A. intros z C. apply IHx. omega. Qed.

Lemma gt_terminates :
terminating gt.

Proof. intros x. apply complete_induction. clear x. 
intros x A. constructor. exact A. Qed.

(*** Exercise 9.3 ***)
Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) (x : X) :
(forall x, (forall y, f y  < f x -> p y)  -> p x) -> p x.

Proof. intros A. apply A. 
induction (f x) ; intros y B.
(* remember (f x) as n. clear Heqn. induction n ; intros y B. *)
exfalso ; omega.
apply A. intros z C. apply IHn. omega. Qed.

Goal reddec gt.

Proof. intros n. destruct n.
right. intros [x A]. omega.
left. exists 0. omega. Qed.

Goal forall n, normal_form gt n 0.

Proof. split.
induction n. now constructor. 
apply starS with (y:= n). omega. assumption.
intros [x A]. omega. Qed.

Goal req le (star (fun x y => S x = y)).

Proof. split ; intros x y A.
now induction A ; eauto using star, star_right.
induction A ; intuition ; omega. Qed.

(** Embedding forces termination *)

Lemma homomorphism X Y (r : rel X) (s : rel Y) (f : X -> Y) x :
(forall x y, r x y -> s (f x) (f y)) ->
terminates s (f x) -> terminates r x.

Proof. (* setting up the right IH is crucial *)
intros A B.
remember (f x) as u ; revert x Hequ ;  
   induction B as [v _ IH] ; intros x B ; subst. 
constructor. eauto. Qed.

(*** Exercise 9.4 ***)
Lemma size_termination (X : Type) (r : rel X) (f : X -> nat) :
(forall x y, r x y -> f x > f y) -> terminating r.

Proof. intros A x. 
apply homomorphism with (f:=f) (s:=gt) ; trivial.
apply gt_terminates. Qed.

(*** Exercise 9.5 ***)
(** Lexical product preserves termination *)

Definition lex (X Y : Type) (r : rel X) (s : rel Y) : rel (X * Y) :=
fun p q => let (x,y) := p in let (x',y') := q in
r x x' \/ x=x' /\ s y y'.

Lemma lex_terminates (X Y : Type) (r : rel X) (s : rel Y) x y :
terminates r x -> terminating s -> terminates (lex r s) (x,y).

Proof. intros R S. 
revert y ; induction R as [x _ IHR] ; intros y.
specialize (S y).  induction S as [y _ IHS].
constructor. intros [x' y'] [A|[A B]]. 
now eauto. subst x'. apply IHS, B. Qed.

(*** Here is a formalized solution to part (b). It was sufficient to do this on paper. ***)
Goal exists X:Type, exists Y:Type, exists r : rel X, exists s : rel Y, exists x, exists y,
  terminates r x /\ terminates s y /\ ~ terminates (lex r s) (x,y).
exists bool. exists bool.
exists (fun x x' => x = false /\ x' = true).
exists (fun y y' => y = true /\ y' = true).
exists false. exists false.
split.
constructor. intros [|] [A B]. constructor. intros [|] [C D]; discriminate. discriminate.
split.
constructor. intros [|] [A B]; discriminate.
intros A. inversion A. destruct x. inversion H0.
assert (B:lex (fun x x' => x = false /\ x' = true) (fun y y' => y = true /\ y' = true) (false,false) (true,true)) by (simpl; tauto).
generalize (H (true,true) B).
intros C. inversion C. destruct x. inversion H4.
assert (D:lex (fun x x' => x = false /\ x' = true) (fun y y' => y = true /\ y' = true) (true,true) (true,true)) by (simpl; tauto).
assert (E:forall u, terminates (lex (fun x x' => x = false /\ x' = true) (fun y y' => y = true /\ y' = true)) u -> ~lex (fun x x' => x = false /\ x' = true) (fun y y' => y = true /\ y' = true) u u).
intros u E F. generalize F. induction E. apply H8. exact F. exact F.
apply (E (true,true)). assumption. assumption.
Qed.

(*** Exercise 9.6 ***)
(** Infinitely branching trees *)
Inductive tree : Type :=
| treeL : tree
| treeN : (nat -> tree) -> tree.

Definition subtree : rel tree :=
fun s t => match s with 
| treeL => False 
| treeN f => exists n, f n = t
end.

Goal terminating subtree.

Proof. intros s. induction s ; constructor ; simpl. 
now intros s [].
intros s [n A] ; subst. apply H. Qed.

Lemma normal_treeL :
normal subtree treeL.

Proof. firstorder. Qed.

Lemma nf_subtree s :
normal_form subtree s treeL.

Proof.  induction s as [|f IH] ; firstorder.
now constructor.
destruct (IH 0) as [A _].
assert (subtree (treeN f) (f 0)). exists 0. reflexivity.
eauto using star. Qed.

Goal confluent subtree.

Proof. intros x y z A B.
destruct (nf_subtree y) as [C _].
destruct (nf_subtree z) as [D _].
exists treeL ; auto.
Qed.

Goal ~ diamond subtree.
intros A.
set (f1 := fun n:nat => treeL).
set (t1 := treeN f1).
set (f2 := fun n:nat => match n with O => treeL | S _ => t1 end).
set (t2 := treeN f2).
cut (exists t, subtree treeL t /\ subtree t1 t).
now firstorder using normal_treeL.
apply A with (x := t2).
exists 0. split; reflexivity.
exists 1. split; reflexivity.
Qed.

(** Semantic Confluence *)

Section Semantic_Confluence.
Variable X V : Type.
Variable eval : X -> V.
Definition sound (r : rel X) : Prop :=
forall x y, r x y -> eval x = eval y.
Definition complete (r : rel X) : Prop :=
forall x y, normal r x -> normal r y -> 
eval x = eval y -> x = y.

Lemma star_sound (r : rel X) :
sound r -> sound (star r).

Proof. intros S x y A. induction A. reflexivity.
apply S in H. congruence. Qed.

Lemma semantic_confluence (r : rel X) :
sound r -> complete r -> 
normalizing r -> confluent r.

Proof. intros S C N x y z A B.
assert (Ny := N y). apply normalizes_normal_form in Ny.
destruct Ny as [u [Nu Ny]].
assert (Nz := N z). apply normalizes_normal_form in Nz. 
destruct Nz as [v [Nv Nz]].
cut (u=v). now intros e ; subst v ; exists u ; auto.
apply C ; auto.
apply star_sound in S.
apply S in A. apply S in B. apply S in Nu. apply S in Nv.
congruence. Qed.

End Semantic_Confluence.
