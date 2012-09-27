Require Import ssreflect ssrbool fintype.

Require Import regexp.

Section Standard.
  Variable char: finType.
  
  Fixpoint standard (e: regular_expression char) :=
    match e with
        | Not _ => false
        | And _ _ => false
        | Dot => false
        | _ => true
    end.
End Standard.
