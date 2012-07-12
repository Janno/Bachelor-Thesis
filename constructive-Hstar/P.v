Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype finset.
Require Import tactics base.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Syntax *)

Definition var := nat.
 
Inductive form := 
  Var    : var -> form
| NegVar : var -> form
| And    : form -> form -> form
| Or     : form -> form -> form
.

Lemma eq_form_dec : forall s t : form , { s = t } + { s <> t}.
Proof. decide equality; apply : eq_comparable. Qed.

Definition form_eqMixin := EqMixin (compareP eq_form_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.

(** We need to construct a [countType] instance for [form]. We do this by by
providing an injectiton (and its inverse) into finitely branching trees. This is
required to construct finite types from sequences of formulas *)

Fixpoint pickle t :=
  match t with
    | Var n => Node (0,n) [::]
    | NegVar n => Node (1,n) [::]
    | And s t => Node (2,2) [:: pickle s ; pickle t]
    | Or s t => Node (3,3) [:: pickle s ; pickle t]
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
    | _ => None
  end.

Lemma inv : pcancel pickle unpickle.
Proof. 
  elim => //=; try solve [ move => ? -> ? -> //= | move => ? -> //= ].
Qed.

Definition form_countMixin := PcanCountMixin inv.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin.

(** * Semantics *)

Definition model := var -> bool.

Reserved Notation "M |= s" (at level 35).
Fixpoint eval M s : bool := 
  match s with 
    | Var x => M x
    | NegVar x => ~~ M x
    | And s t => M |= s && M |= t
    | Or s t => M |= s || M |= t
  end 
where "M |= s" := (eval M s).
  
Definition valid s := forall M , M |= s.
Definition sat s := exists M , M |= s.
Definition equiv s t := forall M , M |= s = M |= t.

Fixpoint Neg (s : form) := 
  match s with 
    | Var n => NegVar n
    | NegVar n => Var n
    | And s t => Or (Neg s) (Neg t)
    | Or s t => And (Neg s) (Neg t)
  end.

(** Proposition 4.1 *)
Lemma Neg_involutive s : Neg (Neg s) = s .
Proof. elim: s => //=; try move => s -> t -> // ; move => s -> //. Qed.

Lemma eval_Neg M s : M |= Neg s = ~~ M |= s.
Proof.
  elim : s => //=. 
  - move => v. by rewrite negb_involutive.
  - move => s Hs t Ht. by rewrite negb_andb Hs Ht.
  - move => s Hs t Ht. by rewrite negb_orb Hs Ht.
Qed.

(** Propositon 2.1 *)

Lemma valid_unsat s : valid s <-> ~ sat (Neg s).
Proof.
  split; first by move => va [M] /=; rewrite eval_Neg va.
  move => H M. move/deMorganE : H. move/(_ M). move/negP. 
  by rewrite /= eval_Neg negb_involutive.
Qed.

Lemma equiv_valid s t : equiv s t <-> valid (Or (And s t) (And (Neg s) (Neg t))).
Proof.
   split => H M.
   - move => /=. case e : (M |= s) ; by rewrite !eval_Neg -H e.
   - move : (H M) => /=. case/orP ; first by case/andP => -> ->.
     case/andP. rewrite !eval_Neg. by do 2 move/negbTE ->.
Qed.

Lemma equiv_sat_valid s t : equiv s t -> (sat s <-> sat t) /\ (valid s <-> valid t).
Proof.
  move => e. split. 
  - split ; case => M ; [rewrite ?e | rewrite -?e]; by exists M.
  - split ; move => H M ; by [rewrite -?e | rewrite ?e]. 
Qed.

Lemma dec_sat2valid : decidable sat -> decidable valid.
Proof.
  move => ds s. case (ds (Neg s)).
  - move => H; right ; case : H => M /= H.
    rewrite eval_Neg in H.
    move/(_ M). by apply/negP.
  - move => H; left => M. 
    rewrite <- negb_involutive. apply/negP => ne.
    apply H. exists M. by rewrite eval_Neg.
Qed.

Lemma dec_valid2equiv : decidable valid -> decidable2 equiv.
Proof.
  move => ds s t. case (ds (Or (And s t) (And (Neg s) (Neg t)))).
  move/equiv_valid ; auto. move => H. by right ; move/equiv_valid.
Qed.


(** Syntactic Closuse *)

Fixpoint synclos s :=
  s :: match s with
         | Var n => [::]
         | NegVar s => [::] 
         | And s t => synclos s ++ synclos t
         | Or s t => synclos s ++ synclos t
       end.

Lemma synclos_refl s : s \in synclos s.
Proof. case: s ; move => * //= ; by rewrite in_cons eq_refl. Qed.

Lemma synclos_trans s t u : s \in synclos t -> t \in synclos u -> s \in synclos u.
Proof.
  elim : u => //=.
  - move => v H. rewrite !in_cons !in_nil !orbF. move/eqP => e. subst.
    move : H. by rewrite in_cons in_nil orbF.
  - move => v H. rewrite !in_cons !in_nil !orbF. move/eqP => e. subst.
    move : H. by rewrite in_cons in_nil orbF.
  - move => u Hu u' Hu' H. rewrite !in_cons mem_cat. 
    case/orP; first tsubst. move : H => /=. by rewrite in_cons //.
    rewrite mem_cat. by case/orP => ? ; [rewrite Hu | rewrite Hu']. 
  - move => u Hu u' Hu' H. rewrite !in_cons mem_cat. 
    case/orP; first tsubst. move : H => /=. by rewrite in_cons //.
    rewrite mem_cat. by case/orP => ? ; [rewrite Hu | rewrite Hu'].
Qed.


Ltac synclos := apply : synclos_trans => // ; by rewrite /= in_cons mem_cat synclos_refl.

Implicit Arguments SeqSub [T s].
Notation "[ss  s ; H ]" := (SeqSub s H) (at level 0).
  
Section FormulaUniverse.
  Variable s : form.
  Definition F := seq_sub (synclos s).

  Definition Hcond (t : F) (H : {set F}) := 
    match val t with 
      | NegVar v => ~~ (Var v \in' H)
      | And u v => u \in' H && v \in' H
      | Or u v  => u \in' H || v \in' H
      | _  => true
    end.
  
  Definition hintikka (H : {set F}) : bool := forallb t , (t \in H) ==> Hcond t H.

  (** Proposition 2.4 *)
  Lemma model_existence (t : F) : (existsb H, hintikka H && (t \in H)) -> sat (val t).
  Proof.
    case/exists_inP => H. move/forall_inP => hint inH.
    exists (fun v => Var v \in' H). case : t hint inH ; elim => //=. 
    - move => v ? ?. by rewrite msvalE.
    - move => v Hv IH. by move/IH.
    (* - case => //=. move => v ? S ? hint. move/hint. by rewrite /Hcond /=.  *)
    - move => u Hu v Hv S hint inH. rewrite Hv //. rewrite Hu //.  
      synclos. move => sc. move: (hint _ inH) => /=. case/andP. by rewrite msvalE. 
      synclos. move => sc. move: (hint _ inH) => /=. case/andP. by rewrite msvalE. 
    - move => u Hu v Hv S hint inH. 
      move: (hint _ inH) => /=. case/orP.
      case/msvalP => Su. move/Hu. by move->.
      case/msvalP => Sv. move/Hv. by move->.
  Qed.

  Lemma small_models (t : F) : sat (val t) -> existsb H , hintikka H && (t \in H).
  Proof.
     move => st. apply/existsP. 
     case st => M eMt.
     exists [set s | M |= (val s)]. rewrite in_set eMt andbT.
     apply/forall_inP => u. rewrite in_set /Hcond.
     case : u. case => //=. 
     - move => v sc H. apply/negP => /msvalP => [[sc']]. 
       by rewrite in_set /= (negbTE H).
     - move => u v H. case/andP => nMu nMv ; splitb.
       have S1 : u \in synclos s by synclos.
       apply/msvalP; exists S1. by rewrite in_set /=.
       have S1 : v \in synclos s by synclos.
       apply/msvalP; exists S1. by rewrite in_set /=.
     - move => u v H. case/orP => nM; [leftb|rightb].
       have S1 : u \in synclos s by synclos.
       apply/msvalP; exists S1. by rewrite in_set /=.
       have S1 : v \in synclos s by synclos.
       apply/msvalP; exists S1. by rewrite in_set /=.
  Qed.

  Theorem decidability t : sat (val t) <-> existsb H, hintikka H && (t \in H).
  Proof.
    split ; last apply model_existence. by apply : small_models.
  Qed.
  
End FormulaUniverse.

Corollary sat_dec : decidable sat.
Proof.
  move => s. 
  have sc : s \in synclos s by rewrite synclos_refl.
  suff : {sat (val (SeqSub s sc))} + {~ sat (val (SeqSub s sc))} by [].
  eapply decP,iffP',decidability.
Qed.

Corollary valid_dec : decidable valid.
Proof. apply dec_sat2valid,sat_dec. Qed.

Corollary equic_dec : decidable2 equiv.
Proof. apply dec_valid2equiv,valid_dec. Qed.
  
