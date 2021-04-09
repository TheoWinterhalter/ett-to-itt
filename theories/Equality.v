From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation Require Import util Sorts SAst SLiftSubst.

Section Equality.

Context `{Sort_notion : Sorts.notion}.

(*! Equality between terms *)
(* This goes through the definition of a nameless syntax *)

Inductive nlterm : Type :=
| nlRel (n : nat)
| nlSort (s : sort)
| nlProd (A B : nlterm)
| nlLambda (A B t : nlterm)
| nlApp (u : nlterm) (A B v : nlterm)
(* Σ-types *)
| nlSum (A B : nlterm)
| nlPair (A B u v : nlterm)
| nlPi1 (A B p : nlterm)
| nlPi2 (A B p : nlterm)
(* Homogenous equality *)
| nlEq (A u v : nlterm)
| nlRefl (A u : nlterm)
| nlJ (A u P w v p : nlterm)
| nlTransport (T1 T2 p t : nlterm)
(* Heterogenous equality *)
| nlHeq (A a B b : nlterm)
| nlHeqToEq (p : nlterm)
| nlHeqRefl (A a : nlterm)
| nlHeqSym (p : nlterm)
| nlHeqTrans (p q : nlterm)
| nlHeqTransport (p t : nlterm)
| nlCongProd (B1 B2 pA pB : nlterm)
| nlCongLambda (B1 B2 t1 t2 pA pB pt : nlterm)
| nlCongApp (B1 B2 pu pA pB pv : nlterm)
| nlCongSum (B1 B2 pA pB : nlterm)
| nlCongPair (B1 B2 pA pB pu pv : nlterm)
| nlCongPi1 (B1 B2 pA pB pp : nlterm)
| nlCongPi2 (B1 B2 pA pB pp : nlterm)
| nlCongEq (pA pu pv : nlterm)
| nlCongRefl (pA pu : nlterm)
| nlEqToHeq (p : nlterm)
| nlHeqTypeEq (A B p : nlterm)
(* Packing *)
| nlPack (A1 A2 : nlterm)
| nlProjT1 (p : nlterm)
| nlProjT2 (p : nlterm)
| nlProjTe (p : nlterm)
(* External axioms *)
| nlAx (id : ident)
.

Fixpoint nl (t : sterm) : nlterm :=
  match t with
  | sRel n => nlRel n
  | sSort s => nlSort s
  | sProd n A B => nlProd (nl A) (nl B)
  | sLambda n A B t => nlLambda (nl A) (nl B) (nl t)
  | sApp u A B v => nlApp (nl u) (nl A) (nl B) (nl v)
  | sSum n A B => nlSum (nl A) (nl B)
  | sPair A B u v => nlPair (nl A) (nl B) (nl u) (nl v)
  | sPi1 A B p => nlPi1 (nl A) (nl B) (nl p)
  | sPi2 A B p => nlPi2 (nl A) (nl B) (nl p)
  | sEq A u v => nlEq (nl A) (nl u) (nl v)
  | sRefl A u => nlRefl (nl A) (nl u)
  | sJ A u P w v p => nlJ (nl A) (nl u) (nl P) (nl w) (nl v) (nl p)
  | sTransport T1 T2 p t => nlTransport (nl T1) (nl T2) (nl p) (nl t)
  | sHeq A a B b => nlHeq (nl A) (nl a) (nl B) (nl b)
  | sHeqToEq p => nlHeqToEq (nl p)
  | sHeqRefl A a => nlHeqRefl (nl A) (nl a)
  | sHeqSym p => nlHeqSym (nl p)
  | sHeqTrans p q => nlHeqTrans (nl p) (nl q)
  | sHeqTransport p t => nlHeqTransport (nl p) (nl t)
  | sCongProd B1 B2 pA pB => nlCongProd (nl B1) (nl B2) (nl pA) (nl pB)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    nlCongLambda (nl B1) (nl B2) (nl t1) (nl t2) (nl pA) (nl pB) (nl pt)
  | sCongApp B1 B2 pu pA pB pv =>
    nlCongApp (nl B1) (nl B2) (nl pu) (nl pA) (nl pB) (nl pv)
  | sCongSum B1 B2 pA pB => nlCongSum (nl B1) (nl B2) (nl pA) (nl pB)
  | sCongPair B1 B2 pA pB pu pv =>
    nlCongPair (nl B1) (nl B2) (nl pA) (nl pB) (nl pu) (nl pv)
  | sCongPi1 B1 B2 pA pB pp => nlCongPi1 (nl B1) (nl B2) (nl pA) (nl pB) (nl pp)
  | sCongPi2 B1 B2 pA pB pp => nlCongPi2 (nl B1) (nl B2) (nl pA) (nl pB) (nl pp)
  | sCongEq pA pu pv => nlCongEq (nl pA) (nl pu) (nl pv)
  | sCongRefl pA pu => nlCongRefl (nl pA) (nl pu)
  | sEqToHeq p => nlEqToHeq (nl p)
  | sHeqTypeEq A B p => nlHeqTypeEq (nl A) (nl B) (nl p)
  | sPack A1 A2 => nlPack (nl A1) (nl A2)
  | sProjT1 p => nlProjT1 (nl p)
  | sProjT2 p => nlProjT2 (nl p)
  | sProjTe p => nlProjTe (nl p)
  | sAx id => nlAx id
  end.

Section nldec.

  Ltac finish :=
    let h := fresh "h" in
    right ;
    match goal with
    | e : ?t <> ?u |- _ =>
      intro h ; apply e ; now inversion h
    end.

  Ltac fcase c :=
    let e := fresh "e" in
    case c ; intro e ; [subst ; try (left ; reflexivity) | finish].

  Ltac nl_dec_tac nl_dec :=
    repeat match goal with
    | t : nlterm, u : nlterm |- _ => fcase (nl_dec t u)
    | s : sort, z : sort |- _ => fcase (Sorts.eq_dec s z)
    | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
    | i : ident, i' : ident |- _ => fcase (string_dec i i')
    end.

  Fixpoint nl_dec (t u : nlterm) : { t = u } + { t <> u }.
  Proof.
    destruct t ; destruct u ; try (right ; discriminate).
    all: nl_dec_tac nl_dec.
  Defined.

  Definition eq_name (u v : name) : bool :=
    match u, v with
    | nAnon, nAnon => true
    | nNamed i, nNamed j => eq_string i j
    | _, _ => false
    end.

  Lemma eq_string_spec :
    forall x y, reflect (x = y) (eq_string x y).
  Proof.
    intros x y. unfold eq_string.
    destruct string_compare eqn:e.
    - apply string_compare_eq in e. constructor. auto.
    - right. intro n. eapply string_compare_eq in n.
      rewrite n in e. discriminate.
    - right. intro n. eapply string_compare_eq in n.
      rewrite n in e. discriminate.
  Qed.

  Lemma eq_name_spec :
    forall u v, reflect (u = v) (eq_name u v).
  Proof.
    intros u v. destruct u, v. all: simpl.
    - constructor. reflexivity.
    - right. discriminate.
    - right. discriminate.
    - destruct (eq_string_spec i i0).
      + left. subst. reflexivity.
      + right. intro. eapply n. inversion H. auto.
  Qed.

  Definition eq_name_dec (u v : name) : { u = v } + { u <> v }.
  Proof.
    destruct (eq_name_spec u v).
    - left. auto.
    - right. auto.
  Qed.

  Ltac sterm_dec_tac sterm_dec :=
    repeat match goal with
    | t : sterm, u : sterm |- _ => fcase (sterm_dec t u)
    | s : sort, z : sort |- _ => fcase (Sorts.eq_dec s z)
    | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
    | i : ident, i' : ident |- _ => fcase (string_dec i i')
    | n : name, n' : name |- _ => fcase (eq_name_dec n n')
    end.

  Fixpoint sterm_dec (t u : sterm) : { t = u } + { t <> u }.
  Proof.
    destruct t ; destruct u ; try (right ; discriminate).
    all: sterm_dec_tac sterm_dec.
  Qed.

End nldec.

Definition eq_term (t u : sterm) : bool :=
  if nl_dec (nl t) (nl u) then true else false.

Lemma eq_term_spec :
  forall {t u},
    eq_term t u = true <-> nl t = nl u.
Proof.
  intros t u. split.
  - unfold eq_term. case (nl_dec (nl t) (nl u)).
    + intros. assumption.
    + intros. discriminate.
  - unfold eq_term. case (nl_dec (nl t) (nl u)).
    + reflexivity.
    + intros h e. exfalso. apply h. apply e.
Defined.

Fact eq_term_refl :
  forall {t}, eq_term t t = true.
Proof.
  intro t. unfold eq_term.
  case (nl_dec (nl t) (nl t)).
  - intro. reflexivity.
  - intro h. exfalso. apply h. reflexivity.
Defined.

Fact eq_term_sym :
  forall {t u}, eq_term t u = true -> eq_term u t = true.
Proof.
  unfold eq_term.
  intros t u.
  case (nl_dec (nl u) (nl t)) ; intro e.
  - reflexivity.
  - case (nl_dec (nl t) (nl u)) ; intro e'.
    + exfalso. apply e. easy.
    + intro. easy.
Defined.

Fact eq_term_trans :
  forall {t u v}, eq_term t u = true -> eq_term u v = true -> eq_term t v = true.
Proof.
  intros t u v.
  unfold eq_term.
  case (nl_dec (nl t) (nl u)) ; intro e1.
  - intros _. rewrite e1. auto.
  - discriminate.
Defined.

Lemma nl_lift :
  forall {t u n k},
    nl t = nl u ->
    nl (lift n k t) = nl (lift n k u).
Proof.
  intros t u n k.
  case (nl_dec (nl t) (nl u)).
  - intros e _.
    revert u e n k.
    induction t ;
    intros u e m k ; destruct u ; cbn in e ; try discriminate e.
    all:
      try (cbn ; inversion e ;
           repeat (erewrite_assumption by eassumption) ; reflexivity).
  - intros h e. exfalso. apply h. apply e.
Defined.

Lemma eq_term_lift :
  forall {t u n k},
    eq_term t u = true ->
    eq_term (lift n k t) (lift n k u) = true.
Proof.
  intros t u n k h. apply eq_term_spec in h.
  apply eq_term_spec.
  apply nl_lift. assumption.
Defined.

Lemma nl_subst :
  forall {t t' u u' n},
    nl t = nl t' ->
    nl u = nl u' ->
    nl (t{n := u}) = nl (t'{n := u'}).
Proof.
  intros t t' u u' n ht hu. revert t' ht u u' hu n.
  induction t ;
  intros t' ht.
  all: destruct t' ; cbn in ht ; try discriminate ht.
  all: intros u u' hu m.
  all: try (cbn ; inversion ht ;
            repeat (erewrite_assumption by eassumption) ; reflexivity).
  symmetry in ht. inversion ht. subst. clear ht. cbn.
  case_eq (m ?= n) ; intro e ; bprop e.
  + subst. eapply nl_lift. assumption.
  + reflexivity.
  + reflexivity.
Defined.

Corollary eq_term_subst :
  forall {t t' u u' n},
    eq_term t t' = true ->
    eq_term u u' = true ->
    eq_term (t{n := u}) (t'{n := u'}) = true.
Proof.
  intros t t' u u' n ht hu.
  apply eq_term_spec in ht.
  apply eq_term_spec in hu.
  apply eq_term_spec.
  apply nl_subst ; assumption.
Defined.

End Equality.

