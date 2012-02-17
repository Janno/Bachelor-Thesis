Require Import ssreflect ssrbool eqtype ssrnat.

Require Import Coq.Lists.List.

Section RE.
Variable A:eqType.

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
| Plus r s => (has_empty r) || (has_empty s)
| Star r => true
| Conc r s => (has_empty r) && (has_empty s)
end.

Fixpoint der r a :=
match r with
| Null => Null
| Empty => Null
| Char a' => if a==a' then Empty else Null
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

Lemma mem_der_Null w : mem_der Null w -> False.
Proof. induction w => //. Qed.

Lemma mem_der_Empty w : mem_der Empty w -> w = nil.
Proof. induction w => //. move => B. destruct (mem_der_Null _ B). Qed.

Lemma mem_der_Char a w : mem_der (Char a) w = true -> w = cons a nil.
Proof.
induction w => //=.
case_eq (a0 == a); move/eqP.
  by move => -> /mem_der_Empty -> //.
by move => F /mem_der_Null => //.
Qed.

Lemma mem_der_Plus r1 r2 w: mem_der (Plus r1 r2) w -> {mem_der r1 w}+{mem_der r2 w}.
Proof.
move: r1 r2 w. fix f 3. move=> r1 r2. case; simpl. 
  case_eq (has_empty r1); case_eq (has_empty r2); auto.
  move=> a l B. case: (f (der r1 a) (der r2 a) l); auto. 
Qed.

Lemma mem_der_Conc_Null r w: mem_der (Conc Null r) w -> False.
Proof. induction w => //=. Qed.

Lemma der_not_Char r a c: der r a <> Char c.
Proof.
induction r; simpl; try discriminate. case: (a == c0); discriminate.
case: (has_empty r1); discriminate.
Qed.

Lemma mem_der_Plus' r s w : mem_der r w \/ mem_der s w -> mem_der (Plus r s) w.
Proof.
move: r s. induction w => //=; move=> r s.
  move => [] -> //; case: (has_empty r) => //.
auto. 
Qed.

Lemma mem_der_Conc r s w1 w2 : mem_der r w1 ->  mem_der s w2 ->
mem_der (Conc r s) (w1 ++ w2).
Proof.
move: r s w2. induction w1 => r s w2 B C /=.
  move: r s B C. induction w2 => /= r s -> //. 
  move => C. apply/mem_der_Plus'. by auto. 
case: (has_empty r) => /=.
  apply/mem_der_Plus'. left. by apply/IHw1 => //.
by apply/IHw1 => //.
Qed.


(* Intuitive, inductive definition of regular expression matching *)
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
Proof. by []. Qed.

Lemma append_nil w : (w ++ @nil A) = w.
Proof. induction w => //=. by rewrite IHw => //. Qed.

Lemma lang_w_nil r w : lang r (w ++ nil) -> lang r w. 
Proof. by rewrite append_nil => //. Qed.

Lemma lang_w_nil' r w : lang r (nil ++ w) -> lang r w. 
Proof. by simpl => //. Qed.

Lemma lang_empty_nil r : has_empty r -> lang r nil.
Proof. induction r => /=; try (discriminate || now constructor); move => H;
move: IHr1 IHr2 H; case: (has_empty r1); case: (has_empty r2); 
by eauto using lang_nil_w, lang.
Qed.

Lemma append_backwards (a:A) w1 w2: cons a (w1 ++ w2) = ((cons a w1) ++ w2).
Proof. by []. Qed.

Lemma lang_der r a w : lang (der r a) w -> lang r (cons a w).
Proof.
move: a w. induction r => a w /=;
  try now (move => B; inversion B; eauto using lang).
(* lang (Char c) (a::w) *) 
  case_eq (a == c); move/eqP.
    move => -> B. inversion B. constructor.
  move => F B. inversion B.
(* lang (Conc r1 r2) (a::w) *) 
  case_eq (has_empty r1) => /= C B.
  (* has_empty r1 = true *)
    inversion B; subst.
      inversion H2; subst. rewrite (append_backwards a w1 w2). constructor; eauto. 
      apply lang_w_nil'. constructor. 
        exact: lang_empty_nil. 
      exact: IHr2.
  (* has_empty r1 = false *)
    inversion B; subst. rewrite (append_backwards a w1 w2). eauto using lang.
(* lang (Star r) (a::w) *)
  move => B; inversion B; subst. constructor. rewrite (append_backwards). apply/langConc; auto.
Qed. 

Lemma mem_der_lang_agree r w : mem_der r w = true <-> lang r w.
Proof. split.
move: r. induction w => r /=. 
exact: lang_empty_nil.

remember (der r a) as s. induction s.
(* der r a = Null *) 
  by move => /mem_der_Null.

(* der r a = Empty *) 
  move => /mem_der_Empty. destruct r; try by [].
  (* r = Char c *)
    move : Heqs => /=. case_eq (a==c). 
      move/eqP => -> _ ->. by constructor.
    by [].
  
  (* r = Conc r1 r2 *)
    move: Heqs => /=. case: (has_empty r1); discriminate.

(* der r a = Char c *)
  have: (der r a = Char c). 
    by symmetry in Heqs.
  by move/der_not_Char.

(* der r a = Conc s1 s2 *)
  rewrite Heqs. move/IHw. 
  destruct r; move: Heqs => //=.
  (* r = Char c *)
    by case_eq (a == c).
  (* r = Conc r1 r2 *)
    case_eq (has_empty r1) => E Heqs B; inversion Heqs. inversion B; subst.
      rewrite append_backwards. constructor. by apply/lang_der. 
    by [].
  (* r = Star r *)
    move => Heqs B. inversion Heqs; inversion B; subst.
    rewrite append_backwards. constructor. constructor; [exact: lang_der | by [] ].

(* der r a = Plus r1 r2 *)
  destruct r; move: Heqs => //=.
  (* r = Char c *)
    by case_eq (a == c).
  (* r = Conc r1 r2 *)
    case_eq (has_empty r1) => E Heqs. inversion Heqs; subst.
    (* has_empty r1 = true *)
      move/mem_der_Plus => []. move/IHw => B. inversion B. subst.
      rewrite append_backwards. constructor; [exact: lang_der | by [] ].
    move => B. apply/lang_w_nil'. move/IHw/lang_der : B. move/lang_empty_nil: E.
    exact: langConc.
    (* has_empty r1 = true *)
    inversion Heqs.
  (* r = Plus r1 r2 *)
  move => B. inversion B; subst. 
  move /mem_der_Plus => [] /IHw /lang_der; [exact: langPlusL | exact: langPlusR].

(* der r a = Star s *)
  destruct r; try discriminate; move: Heqs => //=.
  (* r = Char c *)
    by case_eq (a == c).
  (* r = Star s *)
    by case: (has_empty r1).


(* <- *)
move=>B. induction B => //=.
(* mem_der (Char a) (a::nil) *)
  simpl. by rewrite eq_refl.
(* mem_der (Plus r s) w *) 
  apply mem_der_Plus'. by left.
  apply mem_der_Plus'. by right.
(* mem_der (Conc r s) (w1 ++ w2) *)
  by apply mem_der_Conc.
(* mem_der (Star r) w *)
  induction w => //=. 
  inversion B. subst.
  move: IHB => /=. case: (has_empty r).
    by move/mem_der_Plus => [].
  by [].
Qed.





End RE.
