Require Import Coq.Lists.List.


Section RE.
Variable A:Type.
Variable eqA: forall a b : A, {a=b} + {~a=b}.
(*Local Notation "a1 == a2" := (eqA a1 a2) (at level 70).*)


Definition word := list A.

Inductive re : Type :=
| Null : re
| Empty : re
| Char (c: A) : re
| Conc (r r':re) : re
| Plus (r r':re) : re
| Star (r:re) : re.


Fixpoint has_empty r :=
match r with
| Null => false
| Empty => true
| Char _ => false
| Plus r s => orb (has_empty r) (has_empty s)
| Star r => true
| Conc r s => andb (has_empty r) (has_empty s)
end.


Fixpoint der r a :=
match r with
| Null => Null
| Empty => Null
| Char a' => if eqA a a' then Empty else Null
| Star r => Conc (der r a) (Star r)
| Plus r s => Plus (der r a) (der s a)
| Conc r s => if has_empty r then Plus (Conc (der r a) s) (der s a) else Conc (der r a) s
end.

Fixpoint wder (w: word ) (r: re) :=
match w with
| nil => r 
| cons a w' =>  wder w' (der r a)
end.
Fixpoint mem_der (r: re) (w: word ) :=
match w with 
| nil => has_empty r
| cons a w' =>  mem_der (der r a) w'
end.

Inductive lang : re -> word -> Prop :=
| langEmpty : lang Empty nil
| langChar a : lang (Char a) (cons a nil)
| langPlusL (r s: re) (w : word) : lang r w -> lang (Plus r s) (w)
| langPlusR (r s: re) (w : word) : lang s w -> lang (Plus r s) (w)
| langConc (r s: re) (w1 w2 : word) : lang r w1 -> lang s w2 -> lang (Conc r s) (w1 ++ w2)
| langStarO (r: re) : lang (Star r) nil
| langStarS (r: re) (w : word) : lang (Conc r (Star r)) w -> lang (Star r) w
.

Lemma mem_der_Null w : mem_der Null w = true -> False.
induction w. discriminate. simpl. eauto. Qed.

Lemma mem_der_Empty w : mem_der Empty w = true -> w = nil.
induction w. reflexivity. simpl. intros B. destruct (mem_der_Null _ B).
Qed.

Lemma mem_der_Char a w : mem_der (Char a) w = true -> w = cons a nil.
induction w. simpl. discriminate.
intros B. simpl in *.
destruct (eqA a0 a). assert (w = nil); eauto using mem_der_Empty. subst. reflexivity.
assert False as []; eauto using mem_der_Null.
Qed.

Lemma mem_der_Plus r1 r2 w: mem_der (Plus r1 r2) w = true -> {mem_der r1 w=true}+{mem_der r2 w=true}.
revert r1 r2 w. fix f 3. destruct w as [|a w]. simpl. destruct (has_empty r1), (has_empty r2); eauto.
simpl. intros B. destruct (f (der r1 a) (der r2 a) w). assumption. eauto. eauto. Qed.


Lemma lang_helper r a w : lang r ((cons a nil) ++ w) -> lang r (cons a w).
simpl. auto. Qed.

Lemma lang_helper2 r w : lang r (nil ++ w) -> lang r w.
simpl. auto. Qed.

Lemma append_nil w : (w ++ @nil A)%list = w.
induction w. eauto.
simpl. rewrite IHw. reflexivity. Qed.

Lemma lang_helper2' r w : lang r (w ++ nil) -> lang r w. 
revert r w. fix f 2. intros r [|a w]. eauto. 
simpl. rewrite append_nil. auto.
Qed.

Lemma has_empty_nil r : has_empty r = true -> lang r nil.
Proof. induction r; try (discriminate || now constructor); 
intros H; simpl in H; 
destruct (has_empty r1), (has_empty r2); try discriminate;
try (
 apply lang_helper2; now constructor;  try discriminate; simpl; eauto using lang
). eauto using lang.
Qed.




Lemma lang_helper_empty r : has_empty r = true -> lang r nil.
induction r; try discriminate. constructor.
simpl. intros. destruct (has_empty r1), (has_empty r2); try discriminate.
apply lang_helper2. constructor; eauto.
simpl. intros. destruct (has_empty r1), (has_empty r2); try discriminate; eauto using lang.
constructor.
Qed.

Lemma mem_der_Conc_Null r w: mem_der (Conc Null r) w = true -> False.
induction w. discriminate.
simpl. eauto.
Qed.

Lemma der_not_Char r a c: der r a <> Char c.
induction r; simpl; try discriminate. destruct (eqA a c0); discriminate.
destruct (has_empty r1); discriminate.
Qed.

Lemma mem_der_Plus' r s w : mem_der r w = true \/ mem_der s w = true -> mem_der (Plus r s) w = true.
revert r s. induction w; intros r s.
simpl. intros [B|B]; rewrite B; try reflexivity. destruct (has_empty r); reflexivity.
simpl. eauto. Qed. 

Lemma append_backwards (a:A) w1 w2: cons a (w1 ++ w2) = ((cons a w1) ++ w2).
reflexivity. Qed.

Lemma lang_der r a w : lang (der r a) w -> lang r (cons a w).
Proof.
revert r a w. fix f 1. intros [] a w; simpl; intros B; try now inversion B.
destruct (eqA a c); inversion B. subst. constructor.
case_eq (has_empty r); intros C; rewrite C in *.
inversion B. subst.
inversion H2. subst. rewrite (append_backwards a w1 w2). constructor. eauto. eauto.
subst. apply lang_helper2. constructor. apply lang_helper_empty. assumption. eauto.
inversion B. subst. rewrite (append_backwards a w1 w2). eauto using lang.
inversion B; subst. constructor. eauto. apply langPlusR. eauto.
inversion B. rewrite (append_backwards a w1 w2). subst.
constructor. constructor. eauto. assumption.
Qed. 


Lemma mem_der_Conc r s w1 w2 : mem_der r w1 = true ->  mem_der s w2 = true ->
mem_der (Conc r s) (w1 ++ w2) = true.
induction w1. simpl. 


Lemma mem_der_lang_agree r w : mem_der r w = true <-> lang r w.
split.
revert w r. fix IHw 1; intros [|a w] r; simpl. apply lang_helper_empty.
remember (der r a) as s.
induction s; intros B. 
(* der r a = Null *) 
destruct (mem_der_Null _ B).
(* der r a = Empty *) 
rewrite (mem_der_Empty _ B). destruct r; try discriminate.
(* r = Char c *)
simpl in Heqs.
destruct (eqA a c) as [C|C]. rewrite C in *. constructor.
discriminate.
(* r = Conc r1 r2 *)
simpl in Heqs. destruct (has_empty r1); discriminate.
(* der r a = Char c *)
symmetry in Heqs.
destruct (der_not_Char _ _ _ Heqs).
(* der r a = Conc s1 s2 *)
rewrite Heqs in B. apply lang_der. apply IHw. assumption.
destruct r; try discriminate; simpl in Heqs.
(* r = Char c *)
destruct (eqA a c); discriminate.
(* r = Conc r1 r2 *)
case_eq (has_empty r1); intros E; rewrite E in Heqs. inversion Heqs. subst.
destruct (mem_der_Plus _ _ _ B) as [C|C].
assert (lang (Conc (der r1 a) r2) w). eauto.
inversion H. subst. rewrite (append_backwards a w1 w2). 
constructor. apply lang_der. assumption. assumption.
apply (langConc _ _ (nil)). apply lang_helper_empty. assumption.
assert (lang r2 (cons a w)). apply lang_der. apply IHw. assumption.
assumption.
discriminate.

(* der r a = Plus r1 r2 *)
inversion Heqs. subst.
destruct (mem_der_Plus _ _ _ B) as [C|C].
apply langPlusL. apply lang_der. apply IHw. assumption.
apply langPlusR. apply lang_der. apply IHw. assumption.

(* der r a = Star s *)
destruct r; try discriminate; simpl in Heqs.
(* r = Char c *)
destruct (eqA a c); discriminate Heqs.
(* r = Star s *)
destruct (has_empty r1); discriminate Heqs.


(* <- *)
intros B. induction B.
(* mem_der Empty nil *)
reflexivity.
(* mem_der (Char a) (a::nil) *)
simpl. destruct (eqA a a). reflexivity. assert False as []. apply n. reflexivity.
(* mem_der (Plus r s) w = true *)
apply mem_der_Plus'. eauto.
apply mem_der_Plus'. eauto.


Qed.


