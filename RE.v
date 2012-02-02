Require Import Coq.Lists.List.

Section RE.
Variable A:Type.
Variable eqA: forall a b : A, {a=b} + {~a=b}.

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

Lemma mem_der_Null w : mem_der Null w = true -> False.
Proof. induction w. discriminate. eauto. Qed.

Lemma mem_der_Empty w : mem_der Empty w = true -> w = nil.
Proof. induction w. reflexivity. simpl. intros B. destruct (mem_der_Null _ B). Qed.

Lemma mem_der_Char a w : mem_der (Char a) w = true -> w = cons a nil.
Proof.
induction w. discriminate.
  simpl. intros B. destruct (eqA a0 a). 
    assert (w = nil) by (eauto using mem_der_Empty). subst. reflexivity.
    elimtype False; eauto using mem_der_Null.
Qed.

Lemma mem_der_Plus r1 r2 w: mem_der (Plus r1 r2) w = true -> {mem_der r1 w=true}+{mem_der r2 w=true}.
Proof.
revert r1 r2 w. fix f 3. destruct w as [|a w]; simpl. 
  destruct (has_empty r1), (has_empty r2); eauto.
  intros B. destruct (f (der r1 a) (der r2 a) w); eauto. 
Qed.

Lemma mem_der_Conc_Null r w: mem_der (Conc Null r) w = true -> False.
Proof.
induction w. discriminate.
simpl. eauto.
Qed.

Lemma der_not_Char r a c: der r a <> Char c.
Proof.
induction r; simpl; try discriminate. destruct (eqA a c0); discriminate.
destruct (has_empty r1); discriminate.
Qed.

Lemma mem_der_Plus' r s w : mem_der r w = true \/ mem_der s w = true -> mem_der (Plus r s) w = true.
Proof.
revert r s. induction w; simpl; intros r s.
  intros [B|B]; rewrite B; try reflexivity. destruct (has_empty r); reflexivity.
  eauto. 
Qed.

Lemma mem_der_Conc r s w1 w2 : mem_der r w1 = true ->  mem_der s w2 = true ->
mem_der (Conc r s) (w1 ++ w2) = true.
Proof.
revert r s w2. induction w1; simpl; intros r s w2 B C.
revert r s B C. induction w2; simpl; intros r s B C. rewrite B,C. reflexivity.
simpl in *. rewrite B. apply mem_der_Plus'. eauto.
case_eq (has_empty r); simpl; intros D.
apply mem_der_Plus'. left. apply IHw1; assumption.
apply IHw1; assumption.
Qed.

(* Intuitive, inductive definition of regular expressions *)
Inductive lang : re -> word -> Prop :=
| langEmpty : lang Empty nil
| langChar a : lang (Char a) (cons a nil)
| langPlusL (r s: re) (w : word) : lang r w -> lang (Plus r s) (w)
| langPlusR (r s: re) (w : word) : lang s w -> lang (Plus r s) (w)
| langConc (r s: re) (w1 w2 : word) : lang r w1 -> lang s w2 -> lang (Conc r s) (w1 ++ w2)
| langStarO (r: re) : lang (Star r) nil
| langStarS (r: re) (w : word) : lang (Conc r (Star r)) w -> lang (Star r) w
.

Lemma lang_nil_w r w : lang r (nil ++ w) -> lang r w.
Proof. simpl. auto. Qed.

Lemma append_nil w : (w ++ @nil A) = w.
Proof. induction w. eauto. simpl. rewrite IHw. reflexivity. Qed.

Lemma lang_w_nil r w : lang r (w ++ nil) -> lang r w. 
Proof. rewrite append_nil; eauto. Qed.

Lemma lang_empty_nil r : has_empty r = true -> lang r nil.
Proof. induction r; try (discriminate || now constructor); simpl; intros H; 
destruct (has_empty r1), (has_empty r2); eauto using lang, lang_w_nil.
Qed.

Lemma append_backwards (a:A) w1 w2: cons a (w1 ++ w2) = ((cons a w1) ++ w2).
Proof. reflexivity. Qed.

Lemma lang_der r a w : lang (der r a) w -> lang r (cons a w).
Proof.
revert a w. induction r; intros a w; simpl; intros B; 
  try now (inversion B; eauto using lang).
(* lang (Char c) (a::w) *) 
  destruct (eqA a c); inversion B; subst; constructor.
(* lang (Conc r1 r2) (a::w) *) 
  case_eq (has_empty r1); intros C; rewrite C in *.
(* has_empty r1 = true *)
    inversion B; subst.
      inversion H2. subst. rewrite (append_backwards a w1 w2). constructor; eauto. 
      apply lang_nil_w. constructor. eauto using lang_empty_nil. eauto.
(* has_empty r1 = false *)
  inversion B; subst. rewrite (append_backwards a w1 w2). eauto using lang.
(* lang (Star r) (a::w) *)
  inversion B; subst. constructor. rewrite (append_backwards). apply langConc; eauto.
Qed. 

Lemma mem_der_lang_agree r w : mem_der r w = true <-> lang r w.
Proof. split.
revert r. induction w; intros r; simpl. apply lang_empty_nil.
remember (der r a) as s. induction s; intros B. 
(* der r a = Null *) 
  destruct (mem_der_Null _ B).

(* der r a = Empty *) 
  rewrite (mem_der_Empty _ B). destruct r; try discriminate.
  (* r = Char c *)
    simpl in Heqs. destruct (eqA a c) as [C|C]. 
      rewrite C in *. constructor.
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
      apply (langConc _ _ (nil)). apply lang_empty_nil. assumption.
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
(* mem_der (Plus r s) w *)
  apply mem_der_Plus'. eauto.
  apply mem_der_Plus'. eauto.
(* mem_der (Conc r s) (w1 ++ w2) *)
  apply mem_der_Conc; assumption.
(* mem_der (Star r) nil *)
  reflexivity.
(* mem_der (Star r) w *)
  induction w. reflexivity.
  inversion B. subst. rewrite H1. simpl in *.
  case_eq (has_empty r); intros C; rewrite C in IHB.
    destruct (mem_der_Plus _ _ _ IHB) as [E|E]; assumption.
    assumption.
Qed.

End RE.