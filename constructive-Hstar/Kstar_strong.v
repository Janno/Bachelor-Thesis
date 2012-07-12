Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice fintype finset path fingraph.
Require Import Relations.

Require Import tactics base. 


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Remark: Except for very minor differences, all differences between this file
and K.v have been marked with BEGIN/END *)

(** * Syntax *)
Definition var := nat.
 
Inductive form := 
  Var  : var -> form
| NegVar : var -> form
| And   : form -> form -> form
| Or    : form -> form -> form
| Box   : form -> form
| Dia   : form -> form
| Bstar : form -> form
| Dstar : form -> form
.

Fixpoint pickle t :=
  match t with 
    | Var n => Node (0,n) [::]
    | NegVar n => Node (1,n) [::]
    | And s t => Node (2,2) [:: pickle s ; pickle t]
    | Or s t => Node (3,3) [:: pickle s ; pickle t]
    | Box s => Node (4,4) [:: pickle s ]
    | Dia s => Node (5,5) [:: pickle s ]
    | Bstar s => Node (6,6) [:: pickle s ]
    | Dstar s =>  Node (7,7) [:: pickle s ]
  end.

Fixpoint unpickle t := 
  match t with
    | Node (O,n) [::] => Some (Var n)
    | Node (1,n) [::] => Some (NegVar n)
    | Node (2,2) [:: s' ; t'] => 
      if unpickle s' is Some s then 
        if unpickle t' is Some t then Some (And s t)
          else None else None
    | Node (3,3) [:: s' ; t'] => 
      if unpickle s' is Some s then 
        if unpickle t' is Some t then Some (Or s t)
          else None else None
    | Node (4,4) [:: s'] => 
      if unpickle s' is Some s then Some (Box s) else None
    | Node (5,5) [:: s'] => 
      if unpickle s' is Some s then Some (Dia s) else None
    | Node (6,6) [:: s'] =>
      if unpickle s' is Some s then Some (Bstar s) else None
    | Node (7,7) [:: s'] =>
      if unpickle s' is Some s then Some (Dstar s) else None
    | _ => None
  end.
      
Lemma inv : pcancel pickle unpickle.
Proof. elim => //=; try solve [ move => ? -> ? -> //= | move => ? -> //= ].
Qed.

Lemma eq_form_dec : forall s t : form , { s = t } + { s <> t}.
Proof. decide equality; apply : eq_comparable. Qed. 

Definition form_eqMixin := EqMixin (compareP eq_form_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.

Definition form_countMixin := PcanCountMixin inv.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin.


(** * Semantics *)

Implicit Arguments clos_refl_trans [A].

Structure model := Model {
  state :> Type;
  trans : rel state;
  label : state -> pred var;
  (* ex_dec : forall p : pred state , {ex p} + {~ ex p} ; *)
  (* trans_star_dec : decidable2 (clos_refl_trans trans) *)
  exs' : pred state -> bool ;
  exsP (p : pred state) : reflect (exists x, p x) (exs' p);
  trans_star : state -> state -> bool;
  trans_starP w v : reflect (clos_refl_trans trans w v) (trans_star w v)
}.

Implicit Types M : model.

Notation "w ---> v" := (trans w v) (at level 35).
Notation "w --->* v" := (trans_star w v) (at level 35).

Lemma trans_star0 M (w : M) : w --->* w.
Proof. apply/trans_starP ; apply rt_refl. Qed.

Lemma trans_star1 M (w v : M) : w ---> v -> w --->* v.
Proof. move => ?. by apply/trans_starP ; apply rt_step. Qed.

Lemma trans_star_trans M (w v v' : M) : w --->* v -> v --->* v' -> w --->* v'.
Proof. do 2 move/trans_starP => ?. by apply/trans_starP ; apply : rt_trans. Qed.

(** ** Quantifiers for models *)

Notation "'exs' w , p" := (exs' (fun w => p)) (at level 200, w ident, right associativity).
Notation "'exs' w : M , p" := (exs' (fun w : M => p)) 
  (at level 200, w ident, right associativity, 
    format "'[' 'exs' '/ '  w  :  M , '/ '  p ']'") : type_scope.

Definition alls M (p : pred M) := ~~ (@exs' M) (fun x => ~~ p x).

Lemma allsP M (p : pred M) : reflect (forall x , p x) (alls p).
Proof.
  case e : (alls p); constructor.
  - move => x. rewrite <- negb_involutive; apply/negP => npx.
    move/negP : e; apply ; apply/exsP. by exists x.
  - move => H. move/negP : e; apply. case/exsP => x. by rewrite H.
Qed.

Notation "'alls' w , p" := (alls (fun w => p)) (at level 200, w ident, right associativity).

Lemma not_all_ex (M : model) (p : pred M) : ~~ (alls w , p w) = exs w, ~~ p w.
Proof.
  apply/idP/idP => H. 
  - rewrite <- negb_involutive. apply/negP => H'. move/negP : H; apply.
    apply/allsP => x. rewrite <- negb_involutive. apply/negP => px . 
    move/negP : H'; apply. apply/exsP. by exists x.
  - apply/allsP. move/exsP : H => [w npa] /(_ w). by apply/negP.
Qed.

Lemma not_ex_all (M : model) (p : pred M) : ~~ (exs w , p w) = alls w, ~~ p w.
Proof.
  apply/idP/allsP => H. 
  move => w. apply/negP => pa. move/negP : H; apply. by apply/exsP ; exists w.
  apply/negP ; case/exsP => w pa. move : (H w). by rewrite pa.
Qed.

(** ** Evaluation *)

Reserved Notation "w |= s" (at level 35).
Fixpoint eval M (w:M) s := 
    match s with
    | Var n => label w n
    | NegVar n => ~~ label w n
    | And s t => w |= s && w |= t
    | Or s t => w |= s || w |= t
    | Box s => alls v , w ---> v ==> v |= s
    | Dia s => exs v , w ---> v && v |= s
    | Bstar s => alls v , w --->* v ==> v |= s
    | Dstar s => exs v , w --->* v && v |= s
  end 
  where "w |= s" := (eval w s).


Definition valid s := forall M (w : M) , w |= s.
Definition sat s := exists M : model, exists w : M , w |= s.
Definition equiv s t := forall M (w:M) , w |= s  =  w |= t.


(** Proposition 6.1 *)

Lemma trans_star_case M (w v : M) : w --->* v -> w = v \/ exists2 v' , w ---> v' & v' --->* v.
Proof.
  - move/trans_starP => H; apply trans_rt1n in H; elim : H; first by left.
    move => {w v} w  v' v wv' _ [H|IH]; right; exists_ v'. by rewrite H trans_star0.
    case : IH => v'' H H'. do 2 apply: trans_star_trans => //. by apply trans_star1.
    by apply trans_star0.
Qed.

Lemma Bstar_Box s : equiv (Bstar s) (And s (Box (Bstar s))).
Proof.
  move => M w => /=. apply/allsP/andP.
  - move => H; split; first by  move : (H w); rewrite trans_star0.
    apply/allsP => v ; apply/implyP => wv; apply/allsP => v'; apply/implyP => vv'.
    move :(H v') ; move/implyP ; apply. apply : trans_star_trans => //. by rewrite trans_star1.
  - move => [H1 H2] v. apply/implyP. 
    case/trans_star_case; first by move<-. case => v' H H'.
    move/allsP : H2. move/(_ v'). rewrite H /=. move/allsP. move/(_ v). by rewrite H'.
Qed.
    
Lemma Dstar_Dia s : equiv (Dstar s) (Or s (Dia (Dstar s))).
Proof.
  move=> M w => /=. apply/exsP/orP.
  - case => v. case/andP => H1 H2. 
    case/trans_star_case : H1; first move->. rewrite H2. by left.
    case => v' wv' v'v. right. apply/exsP; exists v'. rewrite wv' /=.
    apply/exsP ; exists v. by rewrite v'v H2.
  - case => H; first by exists w; rewrite trans_star0.
    case/exsP : H => v' . case/andP => H. case/exsP => v; case/andP => A1 A2.
    exists v. rewrite A2 andbT. apply : trans_star_trans => //. 
    by apply trans_star1.
Qed.

(** ** Negation *)

Fixpoint Neg (s : form) := 
  match s with 
    | Var n => NegVar n
    | NegVar n => Var n
    | And s t => Or (Neg s) (Neg t)
    | Or s t => And (Neg s) (Neg t)
    | Box s => Dia (Neg s)
    | Dia s => Box (Neg s)
    | Bstar s => Dstar (Neg s)
    | Dstar s => Bstar (Neg s)
  end.

(** Proposition 4.1 *)
Lemma Neg_involutive s : Neg (Neg s) = s .
Proof. elim: s => //=; try move => s -> t -> // ; move => s -> //. Qed.

Lemma eval_Neg M (w:M) s : w |= Neg s = ~~ w |= s.
Proof.
  elim : s w => //=. 
  - move => v w. by rewrite negb_involutive.
  - move => s Hs t Ht w. by rewrite negb_andb Hs Ht.
  - move => s Hs t Ht w. by rewrite negb_orb Hs Ht.
  - move => s Hs w. rewrite not_all_ex. 
    apply/exsP/exsP; by case => x H ; exists x ; rewrite negb_imply Hs in H |- *.
  - move => s Hs w. rewrite not_ex_all. 
    apply/allsP/allsP. move => H v. by rewrite negb_andb -implybE -Hs.
    move => H v. by rewrite implybE Hs -negb_andb.
  - move => s Hs w. rewrite not_all_ex. 
    apply/exsP/exsP; by case => x H ; exists x ; rewrite negb_imply Hs in H |- *.
  - move => s Hs w. rewrite not_ex_all. 
    apply/allsP/allsP. move => H v. by rewrite negb_andb -implybE -Hs.
    move => H v. by rewrite implybE Hs -negb_andb.
Qed.

Lemma valid_unsat s : valid s <-> ~ sat (Neg s).
Proof.
  split. 
  - move => va [M [w]] /=. by rewrite eval_Neg va.  
  - move => sa M w. rewrite <- negb_involutive. apply/negP => H.
    apply sa. exists M ; exists w. by rewrite eval_Neg.
Qed.

Lemma equiv_valid s t : equiv s t <-> valid (Or (And s t) (And (Neg s) (Neg t))).
Proof.
   split => H M w.
   - move => /=. case e : (eval w s) ; by rewrite !eval_Neg -H e.
   - move : (H M w) => /=. case/orP ; first by case/andP => -> ->.
     case/andP. rewrite !eval_Neg ; by do 2 move/negbTE ->.
Qed.

Lemma dec_sat_val : decidable sat -> decidable valid.
Proof.
  move => ds s. case (ds (Neg s)).
  - move => H; right ; case : H => M [w] /= H. 
    move/(_ M w). rewrite eval_Neg in H ; by apply/negP.
  - move => H; left => M w. 
    rewrite <- negb_involutive. apply/negP => ne.
    apply H. by exists M; exists w; rewrite eval_Neg.
Qed.


Fixpoint synclos s :=
  s :: match s with
         | Var n => [::]
         | NegVar n => [::]
         | And s t => synclos s ++ synclos t
         | Or s t => synclos s ++ synclos t
         | Box s => synclos s 
         | Dia s => synclos s 
         | Bstar s => Box (Bstar s) :: synclos s
         | Dstar s => Dia (Dstar s) :: synclos s
       end.

Lemma synclos_refl t : t \in synclos t.
Proof. case:t => * //= ; by rewrite in_cons eq_refl. Qed.

Lemma synclos_trans t t' s : t \in synclos t' -> t' \in synclos s -> t \in synclos s.
Proof.
  elim : s => //=;
  try solve [
      move => ? H ; rewrite in_cons in_nil orbF ;move/eqP => e ; by subst
    | (move => w IHw H ; rewrite in_cons ; case/orP ; first (by move => e ; rewrite (eqP e) in H) ;
      rewrite in_cons ; by intuition ; match goal with [ H : _ |- _ ] => rewrite H end)
    | (move => w IHw v IHb H ; rewrite in_cons mem_cat ; case/or3P ; first (by move => e ; rewrite (eqP e) in H) ;
      rewrite in_cons mem_cat ; by intuition ; match goal with [ H : _ |- _ ] => rewrite H end)
  ].
  (* Bstar case *)
  move => v IH sub. rewrite !in_cons. case/or3P.
  tsubst. by rewrite !in_cons in sub.
  tsubst. simpl in sub. rewrite !in_cons in sub.
  case/or4P : sub ; try (move/eqP -> ; by rewrite eq_refl). by move->.
  move => sub'. by rewrite IH.
  (* Dstar case - same as above *)
  move => v IH sub. rewrite !in_cons. case/or3P.
  tsubst. by rewrite !in_cons in sub. 
  tsubst. simpl in sub. rewrite !in_cons in sub.
  case/or4P : sub ; try (move/eqP -> ; by rewrite eq_refl). by move->.
  move => sub'. by rewrite IH.
Qed.

Ltac sc := rewrite /= ?in_cons ?mem_cat ?synclos_refl ?eq_refl.
Ltac synclos := apply : synclos_trans => // ; sc.
Ltac synclos' tmp := apply : synclos_trans ; last by apply tmp ; sc.

Implicit Arguments SeqSub [T s].
Notation "[ss  s ; H ]" := (SeqSub s H) (at level 0).

Section FormulaUniverse.
(* All definitions below are with respect to a global formula [s] *)

Variable s : form.
Definition F := seq_sub (synclos s).

Definition Hcond (t : F) (H : {set F}) := 
  match val t with 
    | NegVar v => ~~ Var v \in' H
    | And u v => u \in' H && v \in' H
    | Or u v  => u \in' H || v \in' H 
    | Bstar u => u \in' H && (Box (Bstar u)) \in' H
    | Dstar u => u \in' H || (Dia (Dstar u)) \in' H
    | _ => true
  end.

Definition hintikka (H : {set F}) : bool := forallb t , (t \in H) ==> Hcond t H.

Definition request (H : {set F}) := [set t : F | Box (val t) \in' H].

Definition HU : {set {set F}} := [set H | hintikka H].

Definition TR (S : {set {set F}}) (H H' : {set F}) := [&& H \in S , H' \in S & request H \subset H'].

Definition Ddia (S : {set {set F}}) : bool :=
  forallb H , (H \in enum (mem S)) ==> 
  forallb t , (t \in H) ==> 
  if val t is Dia u 
    then existsb H', TR S H H' && u \in' H'
    else true.

Definition Ddstar (S : {set {set F}}) : bool :=
  forallb H , (H \in enum (mem S)) ==> 
  forallb t , (t \in H) ==>
  if val t is (Dstar u)
    then existsb H', [&& connect (TR S) H H' , H' \in S & u \in' H']
    else true.

Definition demo (D : {set {set F}}) := [&& Ddia D , Ddstar D & D \subset HU].

Section ModelExistence.
  Variable D : {set {set F}}.
  Hypothesis demoD : demo D.

  Definition stateD := seq_sub (enum (mem D)).
  Definition transD (w:stateD) (v:stateD) := request (val w) \subset (val v).
  Definition labelD (w:stateD) v := Var v \in' (val w).
  
  Definition exsD (p : pred stateD) : bool := negb (pred0b p).
  Definition exsPD (p : pred stateD) : reflect (exists w, p w) (exsD p).
  Proof. exact: existsP. Qed.

  Definition trans_starD (H H' : stateD) := connect transD H H'.
  Definition trans_starPD (H H' : stateD) : reflect (clos_refl_trans transD H H') (trans_starD H H').
  Proof. exact: connectP'. Qed.

  Definition MD := 
    {| 
      state := stateD; 
      trans := transD; 
      label := labelD; 
      exsP := exsPD; 
      trans_starP := trans_starPD 
    |}.

  Canonical Structure stateD_model := MD. (* This makes H : stateD ---> H typecheck *)

  Lemma hintikkaD : forall H, H \in D -> hintikka H.
  Proof.
    case/and3P : (demoD) => D1 D2 D3 H.
    move/(subsetP D3). by rewrite /HU in_set.
  Qed.

  Lemma HC t (H : {set F}) : H \in (enum (mem D)) -> t \in H -> Hcond t H.
  Proof.
    case : t H => t sc H. rewrite mem_enum. move/hintikkaD. move/forall_inP; apply.
  Qed.

  Lemma bstar_trans t sc (H H' : stateD) : 
    [ss Bstar t; sc] \in val H -> H --->* H' -> [ss Bstar t; sc] \in val H'.
  Proof.
    move => J. move/trans_starP => tr. apply trans_rtn1 in tr ; elim : tr J => //.
    move => {H'} H' H'' R tr IH /IH /(HC (ssvalP H')). 
    rewrite /Hcond /=. case/andP => _. case/msvalP => sc' inH'.
    move/subsetP : R ; apply. rewrite /request in_set /=. by rewrite msvalE in inH'.
  Qed.

  Lemma TR_transD (H H' : {set F}) HH HH': 
    TR D H H' -> ([ss H ; HH] : stateD) ---> [ss H' ; HH'].
  Proof. rewrite /TR. by case/and3P. Qed.

  Lemma connectTR_transD (H H' : {set F}) HH HH' : 
    connect (TR D) H H' -> ([ss H ; HH] : stateD) --->* [ss H' ; HH']. 
  Proof.
    move/connectP' => X. elim : X HH HH'. 
    - move => {H H'} H H' R HH HH' ; apply : trans_star1. by apply TR_transD.
    - move => {H H'} H HH HH'. rewrite (bool_irrelevance HH HH'). apply trans_star0.
    - move => {H H'} H H' H'' R IH1 R' IH2 HH HH''.
      have HH' : H' \in enum (mem D). apply trans_rtn1 in R ; case : R => //=.  
        move => ? ?. case/and3P. by rewrite mem_enum.
      apply : trans_star_trans. apply (IH1 HH HH'). apply IH2.
  Qed.

  (** Proposition 4.2 *)
  Lemma model_MD_aux (t : F) (H : stateD) : t \in val H -> H |= (val t).
  Proof.
    case: t H. elim.
      - move => v sc H /=. by rewrite /labelD msvalE.
      - move => v sc H /=. rewrite /labelD /=.
        move/(HC (ssvalP H)). by rewrite /Hcond /=. 
      - move => /= u Hu v Hv sc H /=. move/(HC (ssvalP H)). rewrite /Hcond /=. 
        case/andP => H1 H2. splitb.
        apply : Hu; first by synclos. by move => ? ; rewrite msvalE.
        apply : Hv; first by synclos. by move => ? ; rewrite msvalE.
      - move => /= u Hu v Hv sc H /=. move/(HC (ssvalP H)). rewrite /Hcond /=. 
        case/orP => [H1|H1]. 
        leftb. apply : Hu; first by synclos. by move => ? ; rewrite msvalE.
        rightb. apply : Hv; first by synclos. by move => ? ; rewrite msvalE.
      - move => /= u Hu sc H /= ina. apply/allsP => v. rewrite /transD /request. apply/implyP => R.
        apply : Hu ; first by synclos. move => S1.
        move/subsetP : R ; apply. rewrite in_set. by rewrite msvalE in ina.
      - move => /= u Hu sc H /= ina. case/andP : (demoD). rewrite /Ddia. 
        move/forall_inP => /(_ (val H) (ssvalP H)). 
        move/forallP ; move/(_ (SeqSub (Dia u) sc)). rewrite ina /=. 
        case/existsP => H'. case/andP => H1 H2 H3. case/and3P : (H1) => _ inD _.
        rewrite -mem_enum in inD.
        apply/exsP ; exists (SeqSub H' inD). splitb. by destruct H ; apply : TR_transD.
        by case/msvalP : H2 => sc' X ; apply : Hu.
      - move => /= u Hu sc H /= ina. apply/allsP => H'. rewrite /transD /request. apply/implyP => R.
        move : (bstar_trans ina R). move/(HC (ssvalP H')). rewrite /Hcond /=.
        case/andP ; case/msvalP => sc' inH' _. by apply : Hu.
      - move => /= u Hu sc H /= ina. case/and3P : (demoD) => _. rewrite /Ddstar. 
        move/forall_inP => /(_ (val H) (ssvalP H)).
        move/forallP ; move/(_ (SeqSub (Dstar u) sc)). rewrite ina /=. 
        case/existsP => H'. case/and3P => H1 H2 H3 H4. 
        rewrite -mem_enum in H2. apply/exsP ; exists (SeqSub H' H2).
        splitb ; last by case/msvalP : H3 => sc' X ; apply : Hu.
        by destruct H ; apply connectTR_transD.
  Qed.

  Lemma model_existence (t : F) (H : {set F}) : (t \in H) -> H \in D -> sat (val t).
  Proof.
    move => inH inD.
    exists MD. rewrite -mem_enum in inD. exists (SeqSub H inD).
    by apply model_MD_aux.
  Qed.

End ModelExistence.


Section SmallModelTheorem.  

  Definition H_at M (w : M) := [set t : F | w |= (val t)].

  Lemma H_at_hintikka M (w : M) : hintikka (H_at w).
  Proof.
    apply/forall_inP. case;elim ; try by intros ; rewrite /Hcond.
    - move => v sc inH. rewrite /Hcond /=. rewrite in_set /= in inH.
      apply/negP ; case/msvalP => sc'. rewrite in_set /=. by rewrite (negbTE inH).
    - move => u Hu v Hv sc inH. rewrite /Hcond /=. rewrite in_set /= in inH.
      splitb. 
      + apply/msvalP. have su : u \in synclos s by synclos.
        exists su. rewrite in_set. by case/andP : inH => //=.
      + apply/msvalP. have sv : v \in synclos s by synclos.
        exists sv. rewrite in_set. by case/andP : inH => //=.
    - move => u Hu v Hv sc inH. rewrite /Hcond /=. rewrite in_set /= in inH.
      case/orP : inH => eva. 
      + leftb; apply/msvalP. have su : u \in synclos s by synclos.
        exists su. by rewrite in_set. 
      + rightb; apply/msvalP. have sv : v \in synclos s by synclos.
        exists sv. by rewrite in_set.
    - move => u Hu sc inH. rewrite /Hcond /=. rewrite in_set /= in inH.
      splitb.
      + apply/msvalP. have su : u \in synclos s by synclos.
        exists su. rewrite in_set /=. move/allsP : inH => /(_ w).
        move/implyP; apply. apply/trans_starP. by apply : rt_refl.
      + apply/msvalP. have su : Box (Bstar u) \in synclos s by synclos.
        exists su. rewrite in_set /=. 
        apply/allsP => v. apply/implyP => R.
        apply/allsP => v'. apply/implyP => R'.
        move/allsP : inH => /(_ v') /implyP; apply. 
        apply : trans_star_trans => //. by apply : trans_star1.
    - move => u Hu sc inH. rewrite /Hcond /=. rewrite in_set /= in inH.
      case/exsP : inH => v. case/andP. move/trans_starP => ab.
      apply trans_rt1n in ab; elim : ab => {w Hu v}. 
      + move=> v bu. leftb. have su : u \in synclos s by synclos.
        apply/msvalP. exists su. by rewrite in_set.
      + move => w v v' ab bc _ cu. 
        rightb. have su : Dia (Dstar u) \in synclos s by synclos.
        apply/msvalP. exists su. rewrite in_set /=. 
        apply/exsP ; exists v. rewrite ab /=.
        apply/exsP ; exists v'. rewrite cu andbT. apply/trans_starP. by apply : rt1n_trans.
  Qed.

  Definition D M := [set H | exs w : M , H == H_at w].

  Lemma trans_TR M (w v : M) : w ---> v -> (TR (D M)) (H_at w) (H_at v).
  Proof.
    move => ab. rewrite /TR. 
    apply/and3P ; split.
      + rewrite in_set. by apply/exsP ; exists w.
      + rewrite in_set. by apply/exsP ; exists v.
      + apply/subsetP => t. rewrite /request in_set. case/msvalP => sc'.
        rewrite in_set /=. move/allsP; move/(_ v). by rewrite ab /= in_set.
  Qed.
  
  Lemma trans_star_connect M (w v : M) : w --->* v -> connect (TR (D M)) (H_at w) (H_at v).
  Proof.
    move/trans_starP. induction 1. 
    - apply : connect1. by apply trans_TR.
    - by apply : connect0. 
    - by apply : connect_trans.
  Qed.

  (** Proposition 4.3 *)
  Lemma demoD M : demo (D M).
  Proof.
    rewrite /demo. apply/and3P; split; last 1 first.
    - apply/subsetP => H; rewrite in_set. case/exsP => w. move/eqP->.
      by rewrite in_set H_at_hintikka. 
    - apply/forallP => H. apply/implyP => inD.
      apply/forallP. case;case ; try by  move => /= * ; rewrite implybT.
      move => u sc. apply/implyP => inH /=. 
      rewrite mem_enum in_set in inD. case/exsP : inD => w. move/eqP => ? ; subst.
      rewrite in_set /= in inH. case/exsP : inH => v. case/andP => R bu.
      apply/existsP ; exists (H_at v); splitb ; first by apply trans_TR.
      have sc' : u \in synclos s by synclos.
      apply/msvalP ; exists sc'. by rewrite in_set.
    - apply/forallP => H. apply/implyP => inD.
      apply/forallP. case;case ; try by  move => /= * ; rewrite implybT.
      move => u sc. apply/implyP => inH /=. 
      rewrite mem_enum in_set in inD. case/exsP : inD => w. move/eqP => ? ; subst.
      rewrite in_set /= in inH. case/exsP : inH => v. case/andP => R bu.
      apply/existsP ; exists (H_at v). apply/and3P ; split.
      + by apply : trans_star_connect.
      + rewrite in_set. by apply/exsP ; exists v.
      + have sc' : u \in synclos s by synclos.
        apply/msvalP ; exists sc'. by rewrite in_set.
  Qed.
   
  Theorem small_model_theorem (t : F) : sat (val t) -> 
    exists2 D , demo D & exists2 H , H \in D & t \in H.
  Proof.
    case => M [w aMt]. exists (D M); first by apply demoD. 
    exists (H_at w); last by rewrite in_set. 
    rewrite in_set. by apply/exsP; exists w.
  Qed.

  (** Theorem 4.4 *)
  Theorem decidability (t : F) : 
    sat (val t) <-> existsb D, demo D && existsb H : {set F}, (t \in H) && (H \in D).
  Proof.
    split.
    - move/small_model_theorem => [D' HD [H H1 H2]].
      apply/existsP ; exists D'. rewrite HD /=. 
      apply/existsP ; exists H. by rewrite H2 /=. 
    - case/exists_inP => D' demoE ; case/exists_inP => H. 
      by apply : model_existence.
  Qed.
End SmallModelTheorem.

End FormulaUniverse.

(**  Corollary 4.5 *)
Corollary sat_dec: decidable sat.
Proof.
  move => s. 
  have sc : s \in synclos s by rewrite synclos_refl.
  suff : {sat (val (SeqSub s sc))} + {~ sat (val (SeqSub s sc))} by [].
  eapply decP,iffP',decidability.
Qed.

Corollary valid_dec : decidable valid.
Proof. apply dec_sat_val,sat_dec. Qed.

Corollary equiv_dec : decidable2 equiv.
Proof. 
  move => s t. case (valid_dec (Or (And s t) (And (Neg s) (Neg t)))).
  move/equiv_valid ; auto. move => H. by right ; move/equiv_valid.
Qed.

