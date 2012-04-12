Require Import ssreflect ssrbool ssrnat fintype eqtype seq ssrfun.
Require Import automata misc regexp.

(* http://krchowdhary.com/toc/dfa-to-reg-exp.pdf *)

Section StateRemoval.
  
Variable char: finType.
Definition word:= misc.word char.
  
Record re_nfa : Type :=
  re_nfaI {
    re_nfa_state :> finType;
    re_nfa_s0: re_nfa_state;
    re_nfa_fin: pred re_nfa_state;
    re_nfa_step: re_nfa_state -> word -> pred re_nfa_state
    }.

Variable A: nfa char.

Definition nfa_to_re_nfa: 

  
End StateRemoval.

Section TransitiveClosure.

Variable char: finType.
Variable A: dfa char.

Lemma ord_sub (k: 'I_#|A|): k.-1 < #|A|.
Proof.
move: (leq_pred k) (ltn_ord k). by apply: leq_ltn_trans.
Defined.

Lemma R (k: 'I_(#|A|.+1)) (i j: 'I_#|A|) : regular_expression char.
Proof.
elim: k => [n H].
elim: n i j H => [|n R] i j H.
  case_eq ([pick r | dfa_step A (enum_val i) r == enum_val j ]).
    move => r _.
    case_eq (i==j) => H1.
      exact: Plus (Atom r) (Eps _). 
    exact: Atom r.
  move => _. exact: Void _.
move: (Ordinal H) => k.
assert (n < #|A|).
  move: H. by rewrite -{1}(addn1 n) -(addn1 #|A|) ltn_add2r.
move: (Ordinal H0) => k'. 
exact (Plus (
                  Conc
                    (R i k' (ltnW H0))
                    (
                      Conc
                        (Star (R (Ordinal H0) (Ordinal H0) (ltnW H0)))
                        (R (Ordinal H0) j (ltnW H0))
                    )
                )
                (R i j (ltnW H0))).
Defined.

Lemma mem_der_Void w: mem_der (Void char) w = false.
Proof. elim: w => [|a w IHw] //. Qed.

Lemma mem_der_Eps w: mem_der (Eps char) w -> w = [::].
Proof. elim: w => [|a w IHw] //=. by rewrite mem_der_Void. Qed.

Lemma mem_der_Plus (r1 r2: regular_expression char) w: mem_der (Plus r1 r2) w = mem_der r1 w || mem_der r2 w.
Proof. elim: w r1 r2 => [|a w IHw] r1 r2 //=. Qed.

Lemma mem_der_Atom (a: char) w: mem_der (Atom a) w -> w = [::a].
Proof. elim: w a => [|b w IHw] a //=.
case_eq (b == a).
  by move/eqP => -> /mem_der_Eps ->.
by rewrite mem_der_Void.                     
Qed.

Lemma R_rec (k: 'I_#|A|.+1) i j (H0: k.+1 < #|A|.+1) (H1: k < #|A|):
  let k' := (Ordinal (n:=#|A|.+1) (m:=k.+1) (H0)) in
  let k'' := (Ordinal (n:=#|A|) (m:=k) (H1)) in
  (R k' i j) =
      (Plus (
                  Conc
                    (R k i k'')
                    (
                      Conc
                        (Star (R k k'' k''))
                        (R k k'' j )
                    )
                )
                (R k i j)).
Proof. elim: k i j H0 H1 => [n H2] i j H0 H1.
elim: n i j H2 H0 H1 => [|n IHn] i j H2 H0 H1.
simpl.
assert (H: forall X Y (f: X -> X -> Y) a b x y, a = b -> x = y -> f a x = f b y).
  by move => X Y f x y a b -> ->.

eapply H.
  eapply H.
  
  case: (pickP [pred a | (dfa_step A (enum_val i) a == enum_val j)]).

  
Lemma R_correct2 (k: 'I_#|A|.+1) (i j: 'I_#|A|) a w:
  mem_der (R k i j) (a::w)
  -> (
    let x := dfa_step A (enum_val i) a in
    let xs := dfa_run' A x w in
    all (fun y => enum_rank y < k)
        (belast x xs)
    &&  (enum_rank (last x xs) == j)
  ).
Proof.
elim: k i j w => [k H0] i j w.
elim: k H0 i j w => [|k IHk] H0 i j w.
  simpl.
  case: (pickP [pred a | (dfa_step A (enum_val i) a == enum_val j)]).
    move => r /= /eqP.
    case_eq (i == j).
      move/eqP => ->. rewrite eq_refl.
      simpl.
      case_eq (a == r).
        move/eqP => -> H1.
        rewrite mem_der_Plus => /orP [].
          move/mem_der_Eps => -> /=.
          move/(f_equal enum_rank): H1.
          by rewrite enum_valK => /eqP.
        by rewrite mem_der_Void.
      move => H1 H2.
      rewrite mem_der_Plus => /orP [];
      by rewrite mem_der_Void.
    move => -> /=.
    case_eq (a == r).
      move/eqP => -> H1.
      move/mem_der_Eps => -> /=.
      move/(f_equal enum_rank): H1.
      by rewrite enum_valK => /eqP.
    by rewrite mem_der_Void.
  move => H1.
  by rewrite mem_der_Void.
rewrite /R /ordinal_rect /nat_rect.


    
       
Lemma R_correct1 (k: 'I_#|A|.+1) (i j: 'I_#|A|) a w:
  let x := dfa_step A (enum_val i) a in
  let xs := dfa_run' A x w in
  all
    (fun y => enum_rank y < k)
    (belast x xs)
  -> enum_rank (last x xs) == j
  -> mem_der (R k i j) (a::w).
Proof.
elim: k i j w => [k H0] i j w.
elim: k H0 i j w => [|k IHk] H0 i j w.
  simpl.
  case: (pickP [pred a | (dfa_step A (enum_val i) a == enum_val j)]).
    move => r /= /eqP H1. 
    move: H1. case_eq (i == j) => H2.
      rewrite (eqP H2).
      elim: w i j H2 => [|b w IHw] i j H2 //.
        rewrite eq_refl /=.
        rewrite -{4}(enum_valK j) => H1 _.
        rewrite -{2}H1. move/eqP.
        move/(f_equal enum_val).
        rewrite 2!enum_rankK.
                  
    elim: w i j H2 => [|b w IHw] i j H2 //=.
      

                        
End TransitiveClosure.