Require Import Relations Recdef.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import  choice fintype finfun finset path fingraph bigop.
Require Import tactics base. 


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Characterizations.
  Variables (X : Type) (R : X -> X -> Prop).

  Definition EX (P : X -> Prop) (x : X) : Prop := exists2 y, R x y & P y.
  Definition AX (P : X -> Prop) (x : X) : Prop := forall y, R x y -> P y.

  Inductive EF (P : X -> Prop) (x : X) : Prop := 
  | EF0 : P x -> EF P x
  | EFs y : R x y -> EF P y -> EF P x.

  CoInductive AG (P : X -> Prop) ( x : X) : Prop := 
  | AGs : P x -> (forall y, R x y -> AG P y) -> AG P x.

  Lemma EX_ext P q x : P =1 q -> (EX P x <-> EX q x).
  Proof. 
    move => H; split => [[y wv]|[y wv]]; [rewrite H | rewrite -H]; by exists y.
  Qed.
  
  Lemma EF_ext P q x : P =1 q -> (EF P x <-> EF q x).
  Proof.
    move => H; split; elim => {x} x; try by [rewrite H; apply EF0| rewrite -H; apply EF0];
    move => y wv _ ?; by apply: (EFs wv).
  Qed.

  Hint Resolve rt1n_refl Relation_Operators.rt1n_trans rtn1_refl Relation_Operators.rtn1_trans.

  (** Equivalence to alternative Characterizations *)
  Implicit Arguments clos_refl_trans_1n [A].
  Implicit Arguments clos_refl_trans_n1 [A].
  Lemma EFC P x : EF P x <-> exists2 y, clos_refl_trans_1n R x y & P y.
  Proof.
    split.
    - elim => {x} x; first by exists x => //; auto.
      move => y wv ef [y' vv']. by exists y' => //; eauto.
    - case => y. elim => {x y} x y; first by constructor.
      move => z wv _ IH pz. by apply: EFs; eauto.
  Qed.

  Lemma AGC P x : AG P x <-> forall y, clos_refl_trans_1n R x y -> P y.
  Proof.
    split.
    - move => ag y r. elim: r ag => {x y}. by move => x [].
      by move => x y z xy _ IH [] _ /(_ _ xy).
    - move : x. cofix. move => x H. apply: AGs; first by apply H; auto.
    move => y wv. apply: AGC => z vz. by apply H; eauto.
  Qed.


End Characterizations.


(** * Models *)
Definition var := nat.

Record model := Model {
  state :> Type;
  trans : state -> state -> Prop;
  label : var -> pred state;
  EXb : pred state -> pred state;
  EXbP (p:pred state) w : reflect (EX trans p w) (EXb p w);
  EFb : pred state -> pred state;
  EFbP (p:pred state) w : reflect (EF trans p w) (EFb p w)
}.
Implicit Types M : model.
Prenex Implicits trans.

Section Models.
  Variable M : model.
  Implicit Types (w v : M) (p : pred M).

  Definition AXb p w := ~~ EXb (predC p) w.
  Definition AGb p w := ~~ EFb (predC p) w.

  (** ** Extensionality lemmas *)
  Lemma EXb_ext q p w : p =1 q -> EXb p w = EXb q w. 
  Proof.
   move => H. apply/EXbP/EXbP => E; (apply/EX_ext; last apply E); 
     move => v /=. by rewrite -H. by rewrite H.
  Qed.

  Lemma AXb_ext q p w : p =1 q -> AXb p w = AXb q w. 
  Proof.
    rewrite /AXb => H. rewrite (@EXb_ext (predC q) (predC p)) //.
    by move => x /=; rewrite H.
  Qed.

  Lemma EFb_ext q p w : p =1 q -> EFb p w = EFb q w.
  Proof.
    move => H. apply/EFbP/EFbP => E; (apply/EF_ext; last apply E); 
     move => v /=. by rewrite -H. by rewrite H.
  Qed.

  Lemma AGb_ext q p w : p =1 q -> AGb p w = AGb q w. 
  Proof.
    rewrite /AGb => H. rewrite (@EFb_ext (predC q) (predC p)) //.
    by move => x /=; rewrite H.
  Qed.

  (** ** Defining properties and dualities *)
  Lemma AXP p w : reflect (AX trans p w) (AXb p w).
  Proof.
    apply/introP'. 
    - move => H; apply/negP => /EXbP [v wv] /=. by rewrite (H _ wv).
    - move/negP => H v wv. rewrite -[p v]negb_involutive. 
      apply/negP => npv. apply: H. apply/EXbP ; by exists v.
  Qed.

  Lemma negb_EXb p w : ~~ EXb p w = AXb (predC p) w.
  Proof. by rewrite /AXb (EXb_ext _ (predC_involutive _)). Qed.

  Lemma negb_AXb p w : ~~ AXb p w = EXb (predC p) w.
  Proof. by rewrite negb_involutive. Qed.

  Lemma EF_step p w : ~ EF trans p w -> AX trans (fun v => ~ EF trans p v) w.
  Proof.
    move => H. suff: AXb (fun v => ~~ EFb p v) w. 
      move/AXP => A v wv. apply/(reflectPn (EFbP _ _)). by apply: A.
    rewrite -[AXb _ _]negb_involutive. rewrite /AXb negb_involutive.
    apply/(reflectPn (EXbP _ _)). move => [v wv] /=. rewrite negb_involutive. 
    move/EFbP => E. by eapply H,EFs.
  Qed.

  Lemma AGP_aux p w : ~ EF trans (fun v => predC p v) w -> AG trans p w.
  Proof.
    move: w. cofix. move => w nEFw. apply: AGs. 
    - rewrite -[_ w]negb_involutive. apply/negP => /= H. apply: nEFw. by apply: EF0. 
    - move => v wv. apply: AGP_aux. apply: EF_step => //. by apply nEFw.
  Qed.

  Lemma AGP p w : reflect (AG trans p w) (AGb p w).
  Proof.
    apply/introP. move/(reflectPn (EFbP _ _)); first exact: AGP_aux.
    rewrite negb_involutive => /EFbP. elim => {w} w.
    - move => /= npw. case. by rewrite (negbTE npw).
    - move => v wv _ IH. by move => [?] /(_ _ wv).
  Qed.

  Lemma negb_EFb p w : ~~ EFb p w = AGb (predC p) w.
  Proof. by rewrite /AGb (EFb_ext _ (predC_involutive _)). Qed.
    
  Lemma negb_AGb p w : ~~ AGb p w = EFb (predC p) w. 
  Proof. by rewrite negb_involutive. Qed.
End Models.

(** * Generic construction of finite models *)
Section FiniteModel.
  Variables (T : finType) (e : rel T) (label : var -> pred T).
  Implicit Type p : pred T.

  Definition exb p w := existsb v, e w v && p v.
  Lemma exbP p w : reflect (EX e p w) (exb p w).
  Proof.
    apply: introP; first by case/exists_inP => v wv pv; exists v.
    rewrite /exb negb_exists_in => /forall_inP => H. case => v wv.
    by rewrite (negbTE (H v wv)).
  Qed.

  Definition efb p w := existsb v, connect e w v && p v.
  Lemma efbP p w : reflect (EF e p w) (efb p w).
  Proof.
    apply: introP'.
    - elim => {w} w v. apply/exists_inP; exists w => //. by rewrite connect0.
      move => wv _ /exists_inP [v' vv' pv']. apply/exists_inP; exists v' => //.
      apply: connect_trans => //. by apply: connect1.
    - case/exists_inP => v ; case/connectP => s. elim: s w v.
      + move => ? ? /= _ -> ?; by apply: EF0.
      + move => v' s IH w v /= /andP [wv ps] l pv. apply : EFs => //.
        apply: IH => //. by rewrite -l.
  Qed.
  

End FiniteModel.

(** * Syntax *)
 
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

(** countType and choiceType instances for form *)

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

(** * Evaluation  *)

Fixpoint eval M s := 
  match s with
    | Var v => label v
    | NegVar v => predC (@label M v)
    | And s t => predI (eval M s) (eval M t)
    | Or s t => predU (eval M s) (eval M t)
    | Box s => AXb (eval M s)
    | Dia s => EXb (eval M s)
    | Bstar s => AGb (eval M s)
    | Dstar s => EFb (eval M s)
  end.

Notation "w |= s" := (eval s w) (at level 35).
Notation "w ---> v" := (trans w v) (at level 35).


Definition valid s := forall M (w : M) , w |= s.
Definition sat s := exists M : model, exists w : M , w |= s.
Definition equiv s t := forall M (w:M) , w |= s  =  w |= t.


(** **  Negation *)

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
  - move => s Hs w. rewrite negb_AXb. by apply EXb_ext => ? /=.
  - move => s Hs w. rewrite negb_EXb. by apply AXb_ext => ? /=.
  - move => s Hs w. rewrite negb_AGb. by apply EFb_ext => ? /=.
  - move => s Hs w. rewrite negb_EFb. by apply AGb_ext => ? /=.
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
   - move => /=. case e : (w |= s) ; by rewrite !eval_Neg -H e.
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

(** * Formula Universe 

Most of the theory is developed with respect to a finite formula universe [F],
built from the syntactic closure of some formula [s] *)

Section FormulaUniverse.

Variable s : form.
Definition F := seq_sub (synclos s).
Implicit Type (S : {set {set F}}).

(** * Hintikka sets, Hintikka systems and demos *)

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

Definition HU : {set {set F}} := [set H | hintikka H].

Definition request (H : {set F}) := [set t : F | Box (val t) \in' H].

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

Definition demo (D : {set {set F}}) := [&& Ddia D, Ddstar D & D \subset HU].


(** Strong eliminations in case Ddia / Ddstar is violated -- used for pruning *)

Lemma DdiaNE (S : {set {set F}}) : ~~ Ddia S ->
    { H : {set F} | H \in S /\ exists2 t : form, Dia t \in' H & forall H', TR S H H' -> ~~ t \in' H' }.
Proof.
  rewrite /Ddia.
  rewrite negb_forall_in. move/exists_inP. case/xchoose2_sig => H. rewrite mem_enum => HinS.
  rewrite negb_forall_in. move/existsP => E. exists H; split => //.
  move: E => [u /andP []]. case: u. case => // u sc inH /=.
  rewrite negb_exists_in => /forall_inP => F. rewrite msvalE in inH. by exists u.
Qed.

Lemma connect_TR_S S H H' : H \in S -> connect (TR S) H H' -> H' \in S.
Proof.
  move => inS /connectP [x]. elim: x H H' inS => [H H' inS _ ->|] //= H Hs IH H' H'' inS.
  rewrite {1}/TR. move/andP => [/and3P [_ ? _]]. exact: IH.
Qed.

Lemma DdstarNE (S : {set {set F}}) : ~~ Ddstar S ->
  { H : {set F} | H \in S /\ exists2 t : form,  Dstar t \in' H & forall H', connect (TR S) H H' -> ~~ t \in' H'}.
Proof.
  rewrite /Ddstar.
  rewrite negb_forall_in. move/exists_inP. case/xchoose2_sig => H. rewrite mem_enum => HinS.
  rewrite negb_forall_in. move/existsP => E. exists H; split => //.
  move: E => [u /andP []]. case: u. case => // u sc inH /=.  
  rewrite negb_exists_in => /forall_inP => F. exists u; first by rewrite msvalE in inH.
  move => H' conn. move : (F _ conn). by rewrite (connect_TR_S HinS conn).
Qed.


Section ModelExistence.
  Variable D : {set {set F}}.
  Hypothesis demoD : demo D.

  Definition stateD := seq_sub (enum (mem D)).
  Definition transD (w:stateD) (v:stateD) := TR D (val w) (val v).
  Definition labelD v (w:stateD) := Var v \in' (val w).

  Definition MD := 
    {| 
      state := stateD; 
      trans := transD; 
      label := labelD; 
      EXbP := exbP transD ; 
      EFbP := efbP transD 
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
      - move => /= u Hu sc H /= ina. apply/AXP => H' R.
        apply : Hu ; first by synclos. move => S1. move/and3P : R => [_ _ /subsetP]; apply.
        rewrite in_set. by rewrite msvalE in ina.
      - move => /= u Hu sc H /= ina. case/andP : (demoD). rewrite /Ddia. 
        move/forall_inP => /(_ (val H) (ssvalP H)). 
        move/forallP ; move/(_ (SeqSub (Dia u) sc)). rewrite ina /=. 
        case/existsP => H'. case/andP => H1 H2 H3. case/and3P : (H1) => _ inD _.
        rewrite -mem_enum in inD.
        apply/EXbP ; exists (SeqSub H' inD). by destruct H. 
        by case/msvalP : H2 => sc' X ; apply : Hu.
        (*BEGIN*)
      - move => /= u Hu sc H /= inH. apply/AGP. move: H inH. cofix. move => H inH. 
        move/(HC (ssvalP H)) : inH. rewrite /Hcond. move => /= /andP [Ht HBPt].
        apply: AGs. 
        * apply: Hu; first by synclos. by move => ? ; rewrite msvalE.
        * move => H' R. apply model_MD_aux. move/and3P : R => [_ _ /subsetP]; apply.
          by rewrite in_set. 
      - move => /= u Hu sc H /= inH. apply/EFbP.
        case/and3P : (demoD) => _. rewrite /Ddstar. 
        move/forall_inP => /(_ _ (ssvalP H)).
        move/forall_inP => /(_ _ inH) /= /existsP [H' /and3P [/connectP [p p1 p2] H2 H3] ?].
        elim: p H {inH} H' p1 p2 H2 H3.
        * move => /= H H' _ -> inD /msvalP [sc'] /Hu => ?. exact: EF0. 
        * move => /= H'' Hr IH H H' /andP [tr pth] e inD /msvalP [sc'] inH'. 
          have inD' : H'' \in enum D by case/and3P : tr; rewrite mem_enum.
          have step : transD H [ss _ ; inD'] by destruct H. 
          apply: (EFs step). apply: IH => //=; rewrite -e //. by rewrite msvalE in inH'.        
  Qed.

  Lemma model_existence (t : F) (H : {set F}) : (t \in H) -> H \in D -> sat (val t).
  Proof.
    move => inH inD.
    exists MD. rewrite -mem_enum in inD. exists (SeqSub H inD).
    by apply model_MD_aux.
  Qed.

End ModelExistence.

Notation "w |== A" := (forallb t, (t \in A) ==> w |= val t) (at level 35).
Definition satF (A:{set F}) := exists M : model, exists w : M, w |== A.

Section SmallModelTheorem. 
  (** * Pruning *)
  
  Definition pick_dc S := (if ~~ Ddia S is true as b return ~~ Ddia S = b -> option {set F}
    then fun p => Some (tag (DdiaNE p)) else fun _ => None) (refl_equal _).

  Lemma pick_dcH S: ~~ Ddia S -> exists H , pick_dc S = Some H.
  Proof.
    move => dc. exists (tag (DdiaNE dc)). 
    rewrite /pick_dc; move : (refl_equal _); rewrite {2 3}dc /= => e.
    by rewrite (bool_irrelevance dc e).
  Qed.

  Lemma pick_dcS (S : {set {set F}}) H : 
    pick_dc S = Some H -> H \in S /\ exists2 u , Dia u \in' H & forall H', TR S H H' -> ~~ u \in' H'.
  Proof. 
    - case dc: (~~ Ddia S); rewrite /pick_dc; move : (refl_equal _); rewrite {2 3}dc //=.
      move => {dc} e. case => <- ; exact: (tagged (DdiaNE e)). 
  Qed.

  (* Same for rc *)
  Definition pick_rc S := (if ~~ Ddstar S is true as b return ~~ Ddstar S = b -> option {set F}
    then fun p => Some (tag (DdstarNE p)) else fun _ => None) (refl_equal _).

  Lemma pick_rcH S: ~~ Ddstar S -> exists H , pick_rc S = Some H.
  Proof.
    move => rc. exists (tag (DdstarNE rc)). 
    rewrite /pick_rc; move : (refl_equal _); rewrite {2 3}rc /= => e.
    by rewrite (bool_irrelevance rc e).
  Qed.

  Lemma pick_rcS (S : {set {set F}}) H : 
    pick_rc S = Some H -> H \in S /\ exists2 u , Dstar u \in' H & forall H', connect (TR S) H H' -> ~~ u \in' H'.
  Proof. 
    case rc: (~~ Ddstar S); rewrite /pick_rc; move : (refl_equal _); rewrite {2 3}rc //=.
    move => {rc} e. case => <-; exact: (tagged (DdstarNE e)). 
  Qed.

  Definition step S := if pick_dc S is Some H then S :\ H else
    if pick_rc S is Some H then S :\ H else S.

  Lemma subset_step S : step S \subset S.
  Proof.
    rewrite /step.
    case e : (pick_dc S) => [H|]; first by rewrite subD1set.
    case e' : (pick_rc S) => [H|]; by rewrite ?subD1set ?subxx.
  Qed.

  Lemma step_smaller S : step S != S -> #|step S| < #|S|.
  Proof.
    case: (eqVproper (subset_step S)); first by move ->; rewrite eq_refl.
    by move/proper_card. 
  Qed.

  Function prune (S : {set {set F}}) {measure (fun S => #|S|) S} : {set {set F}} := 
    if step S == S then S else prune (step S).
  Proof. move => S /negbT /step_smaller ?. exact/ltP. Defined.

  Lemma prune_dc S : Ddia (prune S).
  Proof. 
    functional induction (prune S) => //.
    rewrite -[Ddia S]negb_involutive. apply/negP => /pick_dcH [H pH].
    move : e. rewrite /step pH. move/pick_dcS : pH => [H1 H2].
    by rewrite setD1id H1.
  Qed.

  Lemma prune_rc S : Ddstar (prune S).
  Proof. 
    functional induction (prune S) => //. 
    rewrite -[Ddstar S]negb_involutive. apply/negP => /pick_rcH [H pH].
    move : e. rewrite /step pH. case e : (pick_dc S) => [H'|].
    move/pick_dcS : e => [H1 _] ; by rewrite setD1id H1.
    move/pick_rcS : pH => [H1 _]; by rewrite setD1id H1.
  Qed.

  Lemma prune_subset S : prune S \subset S.
  Proof.
    functional induction (prune S) => //. 
    by eauto using subset_trans, subset_step.
  Qed.

  Definition Delta := prune HU.

  Lemma demo_Delta : demo Delta.
  Proof. by rewrite /demo prune_dc prune_rc prune_subset. Qed.
  
  (** ** Pruning preserves the pruning invariant *)  

  Definition H_at M (w : M) := [set t : F | w |= (val t)].
  
  Lemma H_at_sat M (w : M) : w |== H_at w.
  Proof. apply/forall_inP => u. by rewrite /H_at in_set. Qed.
  
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
      case/AGP : inH => sat_u H. splitb. 
      + apply/msvalP. have su : u \in synclos s by synclos.
        exists su. by rewrite in_set.
      + apply/msvalP. have su : Box (Bstar u) \in synclos s by synclos.
        exists su. rewrite in_set /=. apply/AXP => v wv. apply/AGP. exact: H.
    - move => u Hu sc inH. rewrite /Hcond /=. rewrite in_set /= in inH.
      case/EFbP : inH => [sat_u | v wv]. 
      + leftb. apply/msvalP. have su : u \in synclos s by synclos.
        exists su. by rewrite in_set. 
      + move/EFbP => ef. rightb. have su : Dia (Dstar u) \in synclos s by synclos.
        apply/msvalP;exists su. rewrite in_set. by apply/EXbP; exists v.      
  Qed.

  Lemma extension M (w : M) (A : {set F}) : w |== A -> A \subset H_at w.
  Proof. move/forall_inP => H. apply/subsetP => t. rewrite in_set. exact: H. Qed.
  
  Definition invariant (S: {set {set F}})  := 
    S \subset HU /\ forall H, H \in HU -> satF H -> H \in S.

  Lemma inv_sub S : invariant S -> S \subset HU. by case. Qed.
  
  Lemma inv_H_at M (w : M) (S: {set {set F}}) : invariant S -> H_at w \in S.
  Proof.
    case => _ inv. apply: (inv (H_at w)); rewrite ?in_set ?H_at_hintikka //. 
    exists M; exists w. exact: H_at_sat.
  Qed.

  Lemma Ddc_unsat H S u : invariant S ->
    H \in S -> Dia u \in' H -> (forall H' , TR S H H' -> ~~ u \in' H') -> ~ satF H.
  Proof.
    move => inv HinS /msvalP [sc inH] step [M [v]] /forall_inP sat. 
    move: (sat _ inH) => /=. case/EXbP => v' vv' v'u. 
    have/step: TR S H (H_at v'). rewrite /TR HinS inv_H_at //=. apply/subsetP => t0.
    rewrite in_set => /msvalP [sc'] /sat /= /AXP /(_ _ vv'). by rewrite /H_at in_set.
    move/negP; apply. apply/msvalP. have scu : u \in synclos s by synclos. exists scu.
    by rewrite /H_at in_set.
  Qed.

  Lemma trans_TR M (w v : M) (S: {set {set F}}) : invariant S -> w ---> v -> (TR S) (H_at w) (H_at v).
  Proof.
    move => inv ab. rewrite /TR. 
    rewrite !inv_H_at //= /request /H_at. apply/subsetP => t. rewrite !in_set. 
    case/msvalP => sc. rewrite in_set. by move => /= /AXP /(_ _ ab).
  Qed.

  Lemma Drc_unsat H S u : invariant S ->
    H \in S -> Dstar u \in' H -> (forall H' , connect (TR S) H H' -> ~~ u \in' H') -> ~ satF H.
  Proof.
    move => inv HinS /msvalP [sc inH] step [M [w]] /forall_inP sat.
    have scd : Dia (Dstar u) \in synclos s by synclos. 
    have/forall_inP X : hintikka H. move/subsetP: (inv_sub inv) => /(_ _ HinS). by rewrite in_set.
    have: [ss _ ; scd] \in H. move: (X _ inH). rewrite /Hcond /=. case/orP ; last by rewrite msvalE.
      by rewrite (negbTE (step _ (connect0 _ _))).
    move/sat => /= /EXbP [v wv]. move/EFbP => ef.
    have C1 : connect (TR S) H (H_at v). rewrite connect1 // /TR HinS inv_H_at //= /request /H_at.
      apply/subsetP => ?. rewrite !in_set. case/msvalP => sc'. by move/sat => /= /AXP /(_ _ wv).
    suff: exists2 v' : M, connect (TR S) (H_at v) (H_at v') & u \in' H_at v'.
      move => [? C2]. apply/negP ; apply: step. by apply: connect_trans.
    elim: ef.
      - move => v' v't. exists v'; first exact: connect0.
        apply/msvalP. have s1 : u \in synclos s by synclos. exists s1. by rewrite /H_at in_set.
      - move => x y xy ? [z yz zt]. exists z => //. apply: connect_trans => //. 
        apply: connect1. exact: trans_TR.
  Qed.

  Lemma unsat_inv S H : invariant S -> H \in S -> ~ satF H -> invariant (S :\ H).
    move => [sub sat] inS unsat; split; first by eauto using subset_trans, subD1set.
    move => H'. case e: (H' == H); first by rewrite (eqP e); tauto.
    move => *. by rewrite in_setD1 e sat.
  Qed.
        
  (* ** pruning invariant is preserved and leads to a demo *)
  Lemma invariantHU : invariant HU. 
  Proof. split; by rewrite ?subxx. Qed.

  Lemma invariant_step S : invariant S -> invariant (step S).
  Proof.
    move => inv. rewrite /step. case e : (pick_dc S) => [H|].
    - case/pick_dcS : e => [inS [u inH next]]. apply: unsat_inv => //. exact: Ddc_unsat.
    - case e' : (pick_rc S) => [H|] //. 
      case/pick_rcS : e' => [inS [u inH next]]. apply: unsat_inv => //. exact: Drc_unsat.
  Qed.

  Lemma invariant_prune S : invariant S -> invariant (prune S).
  Proof.
    move => invS. functional induction (prune S) => //.
    by auto using invariant_step.
  Qed.

  Lemma invariant_demo S : invariant S -> demo (prune S).
  Proof. move/invariant_prune => [I1 I2]. by rewrite /demo I1 prune_dc prune_rc. Qed.
 

  Theorem demo_theorem (t : F) : sat (val t) -> existsb H, (H \in Delta) && (t \in H).
  Proof.
    case => M [w aMt]. apply/exists_inP; exists (H_at w); last by rewrite in_set.
    move: (invariant_prune invariantHU) => [_ /(_ (H_at w))]; apply.
    by rewrite in_set H_at_hintikka. exists M; exists w; exact: H_at_sat.
  Qed.

  (** Theorem 4.4 *)
  Theorem decidability (t : F) : 
    sat (val t) <-> existsb H, (H \in Delta) && (t \in H).
  Proof.
    split; first exact: demo_theorem. 
    case/exists_inP. move: demo_Delta => *. exact : model_existence.
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

(* 
   Print Assumptions decidability.  

   Note that our work does not rely on any axioms. The axioms reported
   are merely definitions made opaque by module abstraction. 
   https://sympa.msr-inria.inria.fr/sympa/wwsympa-wrapper.fcgi/arc/ssreflect/2011-06/msg00009.html
*)

Corollary valid_dec : decidable valid.
Proof. apply dec_sat_val,sat_dec. Qed.

Corollary equiv_dec : decidable2 equiv.
Proof. 
  move => s t. case (valid_dec (Or (And s t) (And (Neg s) (Neg t)))).
  move/equiv_valid ; auto. move => H. by right ; move/equiv_valid.
Qed.

