(* Author: Christian Doczkal *)
Require Import ssreflect ssrbool eqtype.

(** A slightly extended version of [done] using eassumption and rewriting
logical connectives *)
Ltac done := trivial; hnf in |- *; intros; 
(
  solve [ 
    (do !
      [ solve [ trivial | apply : sym_equal; trivial ]
        | discriminate
        | contradiction 
        | eassumption
        | split 
        | rewrite ?andbT ?andbF ?orbT ?orbF
      ]
    )
    | case not_locked_false_eq_true; assumption
    | match goal with
        | H:~ _ |- _ => solve [ case H; trivial ]
      end 
  ]
).


Ltac bcase := 
  match goal with 
    | [ |- context[ ?b || _ ] ] => case b ; simpl ; try done ; bcase
    | [ |- context[ ?b && _ ] ] => case b ; simpl ; try done ; bcase
    | [ |- context[ ?b ==> _ ] ] => case b ; simpl ; try done ; bcase
  end.

Ltac bcaseHyps := 
  (repeat match goal with 
            | [ H : is_true ?b |- _ ] => move : H ; apply/implyP
          end).

Ltac bcaseH := bcaseHyps ; bcase.

Ltac rightb := apply/orP ; right.
Ltac leftb := apply/orP ; left.
Ltac splitb := apply/andP; split. 

Hint Rewrite orTb orbT andTb andbT : bool.
Ltac simplb := repeat first [progress simpl; progress autorewrite with bool].

Ltac exists_ H := exists H => //=.

Ltac tsubst :=  move/eqP => ?; subst.
