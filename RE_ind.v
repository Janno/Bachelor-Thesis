Require Import RE.

Inductive Der (a: A) : re -> re -> Prop := 
| DerNull : Der a Null Null
| DerEmpty : Der a Empty Null
| DerCharEq a' : a = a' -> Der a (Char a') Empty
| DerCharNeq a' : a <> a' -> Der a (Char a') Null
| DerStar r r' : Der a r r' -> Der a (Star r) (Conc r' (Star r))
| DerPlus r s r' s' : Der a r r' -> Der a s s' 
                          -> Der a (Plus r s) (Plus r' s')
| DerConcEmpty r s r' s' : has_empty r = true -> Der a r r' -> Der a s s' 
                            -> Der a (Conc r s) (Plus (Conc r' s) s')

| DerConcNonEmpty r s r' : has_empty r = false -> Der a r r' 
                         -> Der a (Conc r s) (Conc r' s)
.

Lemma der_Der_agree a r r' : der r a = r' <-> Der a r r'.
Proof. split. 
revert r'. induction r; intros r' B; inversion B; eauto using Der, eqA, has_empty; simpl.
  case_eq (eqA a c); intros; constructor; trivial.
  case_eq (has_empty r1); simpl; intros; constructor; trivial.
    case_eq (der r1 a); case_eq (der r2 a); eauto.
    case_eq (der r1 a); case_eq (der r2 a); eauto.
    case_eq (der r1 a); case_eq (der r2 a); eauto.
  constructor.
    case_eq (der r1 a); case_eq (der r2 a); eauto.
    case_eq (der r1 a); case_eq (der r2 a); eauto.
  constructor.
    case_eq (der r a); eauto.

intros B. induction B; simpl; eauto.
  case_eq (eqA a a'); simpl. trivial. intros H1. destruct (H1 H).
  case_eq (eqA a a'); simpl. intros H1. destruct (H H1). trivial.
  subst. trivial.
  subst. trivial.
  subst. rewrite H. trivial.
  rewrite H. subst. trivial.
Qed.

Lemma Der_star_Null a r' : star (Der a) Null r' -> r' = Null.
Proof. intros B. remember Null as n. induction B. trivial.
subst. inversion H. subst. apply IHB. trivial. Qed.


Lemma Der_star_Empty a r' : star (Der a) Empty r' -> r' = Null \/ r' = Empty.
Proof. induction r'; intros B; try eauto using Der.
inversion B. subst. inversion H0; subst. inversion H. 

remember Null as n. induction B. firstorder.
subst. destruct IHB. firstorder. subst. inversion H. subst. apply IHB. trivial. Qed. 

Lemma derivations_finite r : exists l,forall a r', star (Der a) r r' -> In l r'.
Proof. induction r.
  exists (Null::nil). intros. case_eq (Der_star_Null _ _ H). constructor.
  exists (Null::Empty::nil). intros. inversion H. constructor. constructor.
    inversion H0. subst. case_eq (Der_star_Null _ _ H1). constructor.
  exists (Char c::Null::Empty::nil). intros. inversion H. subst. constructor.
    subst. inversion H0. subst. 




