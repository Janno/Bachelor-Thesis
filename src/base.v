(* Author: Christian Doczkal *)
Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ssrfun choice fintype finset path fingraph bigop.
Require Import Relations.
Require Import tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Generic lemmas not in Ssreflect *)

Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p.
Proof. move => Hmn. exact:leq_trans. Qed.

Lemma path_rcons T (e : rel T) p x y  : 
  path e x (rcons p y) = (path e x p && e (last x p) y).
Proof.
  elim: p x y => //=.
  move => z p IHp x y.
  apply/andP/andP ; case.
  - move->. rewrite IHp /=. by case/andP.
  - case/andP => ->. by rewrite IHp => -> ->.
Qed.

Definition xchoose2_sig (T : choiceType) (p q : pred T) : 
  (exists2 x , p x & q x) -> {x : T & p x & q x}.
Proof.
  move => E2. 
  have E : exists x , p x && q x. case : E2 => x ? ?. exists x ; by apply/andP.
  move : (xchooseP E). case/andP => px qx. by exists (xchoose E).
Defined.

Lemma predC_involutive (X:Type) (p : pred X)  x : predC (predC p) x = p x.
Proof. exact: negbK. Qed.

Lemma ex2E X (p q : pred X) : (exists2 x , p x & q x) <-> exists x, p x && q x.
Proof. split => [[x]|[x] /andP [? ?]] *; exists x => //. exact/andP. Qed.

Lemma orS b1 b2 : ( b1 || b2 ) -> {b1} + {b2}.
Proof. case: b1 b2 => [|] [|] //= _; first [by left| by right]. Qed.

Lemma introP' (P:Prop) (b:bool) : (P -> b) -> (b -> P) -> reflect P b.
Proof. case : b => ? ?; by constructor; auto. Qed.

Lemma iffP' (P:Prop) (b:bool) : (P <-> b) -> reflect P b.
Proof. case. apply : introP'. Qed.

Lemma reflectPn P p : reflect P p -> reflect (~ P) (~~ p).
Proof. case => H /=; by constructor; auto. Qed.

Lemma contra' (P Q : Prop) : (P -> Q) -> ~ Q -> ~P. 
Proof. tauto. Qed.

Lemma connectP' (T : finType) (r : rel T) a b : reflect (clos_refl_trans T r a b) (connect r a b).
Proof.
  case e : (connect r a b) ; constructor.
  - case/connectP : e => s. elim : s a ; first by  move => //= a _ -> ; apply : rt_refl.
    move => /= x s IHs a. case/andP => Hr Hp e. apply : rt1n_trans. 
    apply : Relation_Operators.rt1n_trans. done. apply : trans_rt1n. by apply IHs.
  - move/negP : e; apply contra'. elim. apply connect1. apply : connect0. 
    move => x y z _ H1 _ H2. apply: connect_trans; by eauto.
Qed.

Lemma leq1 n : n <= 1 = (n == 0) || (n == 1).
Proof.
  apply/idP/orP; last by case; tsubst.
  case: n => //=. tauto. case => [|n //=]. tauto. 
Qed.

Lemma cards_leq1P (X : finType) (A : {set X}) :
  reflect (forall x y , x \in A -> y \in A -> x = y) (#|A| <= 1).
Proof.
  rewrite leq1. apply: introP'.
  - case e : (#|A| == 0) => //=. apply negbT in e. rewrite cards_eq0 in e.
    case/set0Pn : e => x inA H. apply/cards1P. exists x. apply/eqP. 
    rewrite eqEsubset;splitb;apply/subsetP => y; rewrite in_set1; last by move/eqP->.
    move => inA'. apply/eqP. exact: H.
  - case/orP. rewrite cards_eq0. move/eqP => -> ? ?. by rewrite in_set0.
    move/cards1P => [x ->] y y'. rewrite !in_set1. by move => /eqP -> /eqP ->.
Qed.


(** * Alternative membership for {set seq_sub xs} *)

Implicit Arguments SeqSub [T s].

Section finset.
  Variables (T : choiceType) (xs : seq T).

  Definition msval (X : {set seq_sub xs}) (x : T) := 
  (if x \in xs is true as b return (x \in xs = b -> bool) 
    then fun H => SeqSub x H \in X 
    else xpred0) (refl_equal _).

  Lemma msvalP (X : {set seq_sub xs}) (x : T) : 
    reflect (exists H : x \in xs , SeqSub x H \in X) (msval X x).
  Proof.
    case e : (msval X x); constructor.
    - move : e. rewrite /msval. generalize (refl_equal (x \in xs)).
      have : (x \in xs) || (x \in xs == false) by bcase. case/orP => e'.
      rewrite {2 3} e' => H inX. by exists H.
      rewrite {2 3} (eqP e'). done.
    - move => [H inX]. move/negP : e. apply.
      rewrite /msval. generalize (refl_equal (x \in xs)).
      rewrite {2 3} H => e. by rewrite (bool_irrelevance e H).
  Qed.

  Lemma msvalE x (X : {set seq_sub xs}) H : SeqSub x H \in X = msval X x.
  Proof. 
    apply/idP/msvalP; first by (move => J ; exists H).
    case => H' //. by rewrite (bool_irrelevance H H').
  Qed.
End finset.

Notation "x \in' X" := (msval X x) (at level 20).

(** * Trees 

Finitely branching trees over [countType] are have have again a
[countType] structue
*)

Section TreeCountType.
  Variable X : countType.

  Inductive tree := Node : X -> (seq tree) -> tree.

  Section TreeInd.
    Variable P : tree -> Type.
    Variable P' : seq (tree) -> Type.
    
    Hypothesis Pnil : forall x , P (Node x [::]).
    Hypothesis Pcons : forall x xs, P' xs -> P (Node x xs).
    
    Hypothesis P'nil : P' nil.
    Hypothesis P'cons : forall t ts , P t -> P' ts -> P' (t::ts).
    
    Lemma tree_rect' : forall t , P t.
    Proof.
      fix 1. case => t ts.
      apply : Pcons. elim : ts => [|t' tr]. apply : P'nil. 
      apply : P'cons. apply tree_rect'. 
    Qed.
  End TreeInd.


  Lemma tree_eq_dec : forall (x y : tree) , { x = y } + { x <> y }.
  Proof.
    fix 1. 
    have trees_eq_dec : forall (xs ys : seq tree) , { xs = ys } + { xs <> ys }.
      fix trees_eq_dec 1. case => [|x xs]; case => [|y ys]; try by [left | right].
      case (tree_eq_dec x y). move->. case (trees_eq_dec xs ys). move-> ; by left.
      move => H. right; injection. apply H.   move => H. right; injection => _ . by apply H.
    case => x ts . case => y ts'. case e : (x == y). rewrite (eqP e). 
    case (trees_eq_dec ts ts'); first by move-> ; left. move => H. right. injection. apply H.
    right; injection => _ ?; subst. by rewrite eq_refl in e.
  Qed.
  
  Definition tree_eqMixin  := EqMixin (compareP (@tree_eq_dec)).
  Canonical Structure tree_eqType := Eval hnf in @EqType tree tree_eqMixin.


  Section SimpleTreeInd.
    Variable P : tree -> Type.

    Hypothesis Pnil : forall x , P (Node x [::]).
    Hypothesis Pcons : forall x xs , (forall y , y \in xs -> P y) -> P (Node x xs).

    Lemma simple_tree_rect : forall t , P t.
    Proof.
      apply: (tree_rect' (P' := fun xs => forall y , y \in xs -> P y)) => //.
      move => t ts Pt H y. rewrite in_cons. case/orS => //.  by move/eqP ->. apply: H.
    Qed.
  End SimpleTreeInd.

  Fixpoint t_pickle (t : tree) : seq (X * nat) :=
    let: Node x ts := t in (x, (size ts)) :: flatten (map t_pickle ts).
  
  Fixpoint t_parse (xs : seq (X * nat)) :=
    match xs with
      | [::] => [::]
      | (x,n) :: xr => let: ts := t_parse xr in Node x (take n ts) :: drop n ts
    end.

  Definition t_unpickle := ohead \o t_parse.

  Lemma t_inv : pcancel t_pickle t_unpickle.
  Proof. 
    elim/simple_tree_rect => x xs H.
    rewrite /t_unpickle /=. do 2 f_equal. rewrite /t_unpickle /comp /= in H.
    elim : xs H => //= t ts IHts H.
    Lemma parse_pickle_xs t xs : t_parse (t_pickle t ++ xs) = t :: t_parse xs.
      elim/simple_tree_rect : t xs => x ts IH xs /=. do 2 f_equal. 
      - elim : ts IH => //= ; first by move => H; rewrite take0.
        move => t tr IHtr H. rewrite -catA H //= ; last by rewrite in_cons eq_refl. 
        f_equal. apply : IHtr. move => y Hy xs'. by rewrite H //= in_cons Hy.
      - elim : ts IH => //= ; first by move => H; rewrite drop0.
        move => t tr IHtr H. rewrite -catA H //= ; last by rewrite in_cons eq_refl. 
        apply IHtr. move => y Hy xs'. by rewrite H //= in_cons Hy.
    Qed.
    rewrite parse_pickle_xs /= IHts //=. move => y Hy. by rewrite H //= in_cons Hy.
  Qed.

  Definition tree_countMixin := PcanCountMixin t_inv.
  Definition tree_choiceMixin := CountChoiceMixin tree_countMixin.
  
  Canonical Structure tree_ChoiceType := Eval hnf in ChoiceType tree tree_choiceMixin.
  Canonical Structure tree_CountType := Eval hnf in CountType tree tree_countMixin.

End TreeCountType.

(** * A least fixed point operator for finType *)

Lemma iter_fix T (F : T -> T) x k n : 
  iter k F x = iter k.+1 F x -> k <= n -> iter n F x = iter n.+1 F x.
Proof.
  move => e. elim: n. rewrite leqn0. by move/eqP<-.
  move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
  move/IH => /= IHe. by rewrite -!IHe.
Qed.

Section FixPoint.
  Variable T :finType.
  Definition set_op := {set T} -> {set T}.
  Definition mono (F : set_op)  := forall p q : {set T} , p \subset q -> F p \subset F q.

  Variable F : {set T} -> {set T}.
  Hypothesis monoF : mono F.

  Definition lfp := iter #|T|.+1 F set0.

  Lemma lfp_ind (P : {set T} -> Type) : P set0 -> (forall s , P s -> P (F s)) -> P lfp.
  Proof.
    move => P0 Pn. rewrite /lfp. set n := #|T|.+1. elim: n => //= n. exact: Pn.
  Qed.

  Lemma iterFsub n : iter n F set0 \subset iter n.+1 F set0.
  Proof.
    elim: n => //=; first by rewrite sub0set.
    move => n IH /=. by apply: monoF.
  Qed.

  Lemma iterFsubn m n : m <= n -> iter m F set0 \subset iter n F set0.
  Proof.
    elim : n; first by rewrite leqn0 ; move/eqP->.
    move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
    move/IH => /= IHe. apply: subset_trans; first apply IHe. exact:iterFsub.
  Qed.
 
  Lemma lfpE : lfp = F lfp.
  Proof.
    have: ~~ [ forall m : 'I_#|T|.+1 , iter m F set0 \proper iter m.+1 F set0 ].
      apply/negP => /forallP H.
      have P : forall n : 'I_#|T|.+1 , exists x : T , x \in iter n.+1 F set0 :\: iter n F set0.
        move => n ; move : (H n). case/properP => _ [x x1 x2]. exists x. by rewrite in_setD x1 x2.
      pose i (o : 'I_#|T|.+1) : T := xchoose (P o).
      have inj_i : injective i. 
        move => o o'. rewrite /i => e. move : (xchooseP (P o)) (xchooseP (P o')).
        rewrite e {e}. set x := xchoose _. move : o o' x => [n pn] [m pm] x.
        rewrite !in_setD /=. case/andP => Hn1 Hn2. case/andP => Hm1 Hm2.
        case (ltngtP n m); last by move/eqP => e'; apply/eqP.
        - move => /iterFsubn /subsetP /(_ x Hn2). by rewrite (negbTE Hm1).
        - move => /iterFsubn /subsetP /(_ x Hm2). by rewrite (negbTE Hn1).
      move : (max_card (fun x => x \in codom i)). by rewrite (card_codom inj_i) /= !card_ord ltnn. 
    rewrite negb_forall. case/existsP => x H.
    have A : iter x F set0 = iter x.+1 F set0. 
      apply/eqP. by rewrite eqEproper iterFsub /= H.
    apply : iter_fix; first apply A. by case:x {H A} => *; auto.
  Qed.
End FixPoint.

Inductive norm (X : Type) (R : X -> X -> Prop) : X -> Prop :=
  normI x : (forall y , R x y -> norm R y) -> norm R x.

Definition sn X (R : X -> X -> Prop) := forall x, norm R x.

Lemma normEn (X:finType) (e : rel X) x : ~ norm e x -> [ exists y , e x y ].
Proof.
  move => H. rewrite -[[exists y, _]]negbK negb_exists.
  apply/negP. move/forallP => H'. apply H, normI => y. 
  by rewrite -[e _ _]negbK H'.
Qed.

(** * Decidability *)

Definition decidable X P := forall x : X, {P x} + {~ P x}.
Definition decidable2 X Y R := forall (x : X) (y : Y) , {R x y} + {~ R x y}.

Lemma decidable_reflect X P : 
  decidable P -> {p : pred X & forall x , reflect (P x) (p x)}.
Proof.
  move => dp. exists (fun x => dp x) => x.
  by case e : (dp x); constructor.
Qed.
  
Lemma reflect_decidable X P :
  {p : pred X & forall x , reflect (P x) (p x)} -> decidable P.
Proof. move => [p R] x. by apply : decP. Qed.

(** * Some lemmas, that allow classical reasoning in some circumstances *)

Lemma classicF (P:Prop) : (P -> False) -> (~ P -> False) -> False.
Proof. tauto. Qed.
Implicit Arguments classicF [].

Lemma classicb (P:Prop) (b:bool) : (P -> b) -> (~ P -> b) -> b.
Proof. case : b => //. intuition. Qed.
Implicit Arguments classicb [].

Lemma deMorganb (P Q : Prop) (b : bool) : ((~P \/ ~Q) -> b) <-> (~ (P /\ Q) -> b).
Proof.
  split; last tauto; move => *.
  apply : (classicb P); last tauto. move => ?.
  apply : (classicb Q); last tauto. move => ?.
  exfalso; tauto.
Qed.

Lemma dnb (P : Prop) (b : bool) : (P -> b) <-> (~ ~ P -> b).
Proof.
  split; last tauto; move => *.
  apply : (classicb P); tauto.
Qed.

Lemma deMorganE (X:Type) (P : X -> Prop) : 
  (~ exists x , P x) -> (forall x , ~ P x).
Proof. move => nE x Px. apply nE. by exists x. Qed.

Lemma deMorganAb (X:Type) (p : X -> bool) (b : bool) : 
  ((exists x , ~~ p x) -> b) -> (~ forall x , p x) -> b.
Proof.
  move => H1 H2. 
  apply : (classicb (exists x, ~~ p x)) => //.
  move/deMorganE => H4. exfalso. 
  apply: H2 => x. move : (H4 x). move/negP. by rewrite negbK.
Qed. 

Lemma deMorganE2 (Y: Type) (P Q : Y -> Prop) : 
  ~ (exists2 x, P x & Q x) -> forall x, P x -> ~ Q x.
Proof. move => H x p q. apply: H. by exists x. Qed.


Lemma reflect_DN P p : reflect P p -> ~ ~ P -> P.
Proof. by case. Qed.

Lemma setD1id (T : finType) (A : {set T}) x : A :\ x == A = (x \notin A). 
Proof.
  apply/eqP/idP => [|e]; [move/setDidPl|apply/setDidPl]; 
    rewrite disjoint_sym (@eq_disjoint1 _ x) // => ?; by rewrite in_set.
Qed.


Lemma fin_choice_aux (T : choiceType) T' (d : T') (R : T -> T' -> Prop) (xs : seq T) :
  (forall x, x \in xs -> exists y, R x y) -> exists f , forall x, x \in xs -> R x (f x).
Proof.
  elim: xs. move => _. exists (fun _ => d) => ?. by rewrite in_nil.
  move => x s IH step.
  have/IH: forall x : T, x \in s -> exists y, R x y.
    move => z ins. apply: step. by rewrite in_cons ins orbT.
  case => f Hf. (case: (step x); first by rewrite mem_head) => y Rxy.
  exists (fun z => if z == x then y else f z) => z. 
  rewrite in_cons; case/orP. move/eqP=>e. by rewrite -e ?eq_refl in Rxy *.
  case e: (z == x); first by rewrite (eqP e). exact: Hf.
Qed.  

Lemma cardSmC (X : finType) m : (#|X|= m.+1) -> X.
Proof. rewrite cardE. case e: (enum X) => [|x s] //=. Qed.

Lemma fin_choice (X : finType) Y (R : X -> Y -> Prop) : 
  (forall x : X , exists y , R x y) -> exists f, forall x , R x (f x).
Proof.
  case n : (#|X|) => [|m]. 
  - have F : X -> False. move => x. move : (max_card (pred1 x)). by rewrite card1 n.
    exists (fun x => match F x with end) => x. done.
  - move => step.
    have H : forall x, x \in enum X -> exists y, R x y. by move => *.
    case (step (cardSmC n)) => d.
    move/(fin_choice_aux d) : H => [f Hf].
    exists f => x. apply: Hf. by rewrite mem_enum.
Qed.

