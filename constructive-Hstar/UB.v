Require Import Relations Recdef.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice fintype finfun finset path fingraph bigop.
Require Import tactics base. 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Semantics *)

Section Characterizations.
  Variables (X : Type) (e : X -> X -> Prop).

  Definition EX (p : X -> Prop) (w : X) : Prop := exists2 v, e w v & p v.
  Definition AX (p : X -> Prop) (w : X) : Prop := forall v, e w v -> p v.

  Inductive EF (p : X -> Prop) (w : X) : Prop := 
  | EF0 : p w -> EF p w
  | EFs v : e w v -> EF p v -> EF p w.

  CoInductive AG (p : X -> Prop) (w : X) : Prop := 
  | AGs : p w -> (forall v, e w v -> AG p v) -> AG p w.

  Inductive AF (p : X -> Prop) (w : X) : Prop := 
  | AF0 : p w -> AF p w
  | AFs : (forall v, e w v -> AF p v) -> AF p w.
  
  CoInductive EG (p : X -> Prop) : X -> Prop :=
  | EGs w v : p w -> e w v -> EG p v -> EG p w.

  Lemma EX_ext p q w : p =1 q -> (EX p w <-> EX q w).
  Proof. 
    move => H; split => [[v wv]|[v wv]]; [rewrite H | rewrite -H]; by exists v.
  Qed.
  
  Lemma EF_ext p q w : p =1 q -> (EF p w <-> EF q w).
  Proof.
    move => H; split; elim => {w} w; try by [rewrite H; apply EF0| rewrite -H; apply EF0];
    move => v wv _ ?; by apply: (EFs wv).
  Qed.

  Lemma AF_ext p q w : p =1 q -> (AF p w <-> AF q w).
  Proof.
    move => H; split; elim => {w} w; try by [rewrite H;apply AF0 | rewrite -H; apply AF0];
      move => _ IH; by apply AFs.
  Qed.

End Characterizations.

Definition var := nat.

Record model := Model {
  state :> Type;
  trans : state -> state -> Prop;
  label : var -> pred state;
  
  EXb : pred state -> pred state;
  EXbP (p:pred state) w : reflect (EX trans p w) (EXb p w);
  
  EFb : pred state -> pred state;
  EFbP (p:pred state) w : reflect (EF trans p w) (EFb p w);
  
  AFb : pred state -> pred state;
  AFbP (p:pred state) w : reflect (AF trans p w) (AFb p w)
}.

Implicit Type M : model.
Prenex Implicits trans.
Notation "w ---> v" := (trans w v) (at level 35).

Section Dualities.
  Variable M : model.
  Implicit Types (w v : M) (p : pred M).

  (** * Definition of the dual operations *)

  Definition AXb p w := ~~ EXb (predC p) w.
  Definition AGb p w := ~~ EFb (predC p) w.
  Definition EGb p w := ~~ AFb (predC p) w.

  (** ** Extensionality lemmas *)
  Lemma EXb_ext q p w : p =1 q -> EXb p w = EXb q w. 
  Proof.
   move => H. apply/EXbP/EXbP => E; (apply/EX_ext; last apply E); 
     move => v /=. by rewrite -H. by rewrite H.
  Qed.

  Lemma AFb_ext q p w : p =1 q -> AFb p w = AFb q w.
  Proof.
    move => H. apply/AFbP/AFbP => A; (apply/AF_ext; last apply A); 
     move => v /=. by rewrite -H. by rewrite H.
  Qed.

  Lemma EFb_ext q p w : p =1 q -> EFb p w = EFb q w.
  Proof.
    move => H. apply/EFbP/EFbP => E; (apply/EF_ext; last apply E); 
     move => v /=. by rewrite -H. by rewrite H.
  Qed.


  (** ** Proofs of defining properties and dualities *)
  (**  EX/AX  *)

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
  
  (** EF/AG *)
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

  Lemma negb_efb p w : ~~ EFb p w = AGb (predC p) w.
  Proof. by rewrite /AGb (EFb_ext _ (predC_involutive _)). Qed.
    
  Lemma negb_agb p w : ~~ AGb p w = EFb (predC p) w. 
  Proof. by rewrite negb_involutive. Qed.

  (** AF/EG *)
  Lemma AF_step p w : ~ AF trans p w -> EX trans (fun v => ~ AF trans p v) w.
  Proof.
    move => H. suff: EXb (fun v => ~~ AFb p v) w. 
      move/EXbP => [v wv nAFv]. exists_ v. exact/AFbP.
    rewrite -[EXb _ _]negb_involutive. rewrite negb_EXb. 
    apply/negP => /AXP A. apply: H. apply: AFs => v wv. 
    move: (A v wv) => /=. rewrite negb_involutive. exact/AFbP.
  Qed.

  Lemma EGP_aux p w : ~ AF trans (fun v => predC p v) w -> EG trans p w. 
    move: w. cofix. move => w nAFw. case/AF_step : (nAFw) => v wv nAFv.
    apply: EGs => //.
    - rewrite -[p w]negb_involutive; apply/negP => ?. by apply nAFw,AF0.
    - apply: (EGP_aux _ nAFv).
  Qed.

  Lemma EGP p w : reflect (EG trans p w) (EGb p w).
  Proof. 
    apply: introP. 
    move/(reflectPn (AFbP _ _)); first exact: EGP_aux.
    rewrite /EGb negb_involutive. move/AFbP ; elim => {w} w.
    - move => pw H. by case: H pw  => {w} ? ? /= ->.
    - move => _ IH H. case: H IH => {w} w v pw wv eg IH.
      apply: IH. apply wv. apply eg.
  Qed.

  Lemma negb_afb p w : ~~ AFb p w = EGb (predC p) w.
  Proof. by rewrite /EGb (AFb_ext _ (predC_involutive _)). Qed.
  
  Lemma nedb_egb p w : ~~ EGb p w = AFb (predC p) w.
  Proof. by rewrite negb_involutive. Qed.
    
End Dualities.


(** * Syntax for UB and evaluation of formulas to predicates *)

Inductive form :=
  P_   of var          | NP_ of var
| AND_ of form & form  | OR_ of form & form
| EX_  of form         | AX_ of form
| EF_  of form         | AG_ of form
| AF_  of form         | EG_ of form.

Fixpoint eval M (s : form) :=
  match s with
    | P_ v => label v
    | NP_ v => predC (@label M v)
    | AND_ s t => predU (eval M s) (eval M t)
    | OR_ s t => predI (eval M s) (eval M t)
    | EX_ s => EXb (eval M s)
    | AX_ s => AXb (eval M s)
    | EF_ s => EFb (eval M s)
    | AG_ s => AGb (eval M s)
    | AF_ s => AFb (eval M s)
    | EG_ s => EGb (eval M s)
    end.

(** * Generic construction of finite models *)
Section FiniteModel.
  Variables (T : finType) (e : rel T) (label : var -> pred T).                                        
  Implicit Types p q : pred T.

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

  (** afb is defined using a fixed point operator for finite types. See
     base.v for the construction of mu *)
 
  Variable p : pred T.
  Definition F A := A :|: [set x | p x] :|: [set x | forallb y, e x y ==> (y \in A)]. 
  Lemma monoF : mono F.
  Proof.
    rewrite /mono /F => A B /subsetP sub. apply/subsetP => w.
    do 2 rewrite in_setU. case/orP. case/orP.
    - rewrite in_setU => H. leftb. rewrite in_setU. leftb. by apply sub.
    - do 2 rewrite in_setU. by move->.
    - do 2 rewrite in_setU. move => H. rightb. rewrite !in_set in H *.
      apply/forall_inP => x. move/(_ x) : sub. move/forall_inP : H. auto.
  Qed.
 
  Definition afb w := w \in mu F.
  Lemma afbP w : reflect (AF e p w) (afb w).
  Proof.
    apply introP'.
    - rewrite /afb. elim => {w} w pw. 
      + rewrite muE {1}/F. rewrite in_setU. 
        leftb. by rewrite in_setU in_set pw. exact: monoF.
      + move/forall_inP => H. rewrite /afb muE {1}/F. rewrite in_setU.
        rightb. by rewrite in_set. exact: monoF.
    - rewrite /afb. move: w. apply mu_ind. by move => ?; rewrite in_set0.
      move => A IH w. rewrite /F. do 2 rewrite in_setU. case/orP. case/orP.
      - exact: IH.
      - rewrite in_set. move => pw. exact: AF0.
      - rewrite in_set. move/forall_inP => H. apply: AFs => v /H. exact: IH.
  Qed.    
End FiniteModel.