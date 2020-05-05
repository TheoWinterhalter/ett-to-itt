(*! ITT Derivations checking *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import utils Ast Typing Checker.
From Translation Require Import util Quotes Sorts SAst SLiftSubst SCommon
     ITyping ITypingInversions ITypingLemmata ITypingAdmissible
     FundamentalLemma Translation FinalTranslation FullQuote.
Import ListNotations.

(* For efficiency reasons we use type in type for examples. *)
Existing Instance Sorts.type_in_type.

Notation Ty := (@sSort Sorts.type_in_type tt).

(* Some admissible lemmata to do memoisation in a way. *)
Lemma type_Prod' :
  forall {Σ Γ n A B},
    Σ ;;; Γ |-i A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i B : Ty) ->
    Σ ;;; Γ |-i sProd n A B : Ty.
Proof.
  intros Σ' Γ n A B hA hB.
  eapply meta_conv.
  - eapply type_Prod.
    + eassumption.
    + apply hB. econstructor ; try eassumption.
      eapply typing_wf. eassumption.
  - reflexivity.
Defined.

Lemma type_Lambda' :
  forall {Σ Γ n n' A B t},
    type_glob Σ ->
    Σ ;;; Γ |-i A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i t : B) ->
    Σ ;;; Γ |-i sLambda n A B t : sProd n' A B.
Proof.
  intros Σ Γ n n' A B t hg hA ht.
  assert (hw : wf Σ (Γ ,, A)).
  { econstructor ; try eassumption.
    eapply typing_wf. eassumption.
  }
  specialize (ht hw). destruct (istype_type hg ht).
  eapply type_Lambda ; eassumption.
Defined.

Lemma type_App' :
  forall {Σ Γ n t A B u},
    type_glob Σ ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sApp t A B u : (B{0 := u})%s.
Proof.
  intros Σ Γ n t A B u hg ht hu.
  destruct (istype_type hg ht).
  destruct (istype_type hg hu).
  ttinv H.
  eapply type_App ; eassumption.
Defined.

Lemma type_Sum' :
  forall {Σ Γ n A B},
    Σ ;;; Γ |-i A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i B : Ty) ->
    Σ ;;; Γ |-i sSum n A B : Ty.
Proof.
  intros Σ' Γ n A B hA hB.
  eapply meta_conv.
  - eapply type_Sum.
    + eassumption.
    + apply hB. econstructor ; try eassumption.
      eapply typing_wf. eassumption.
  - reflexivity.
Defined.

Lemma type_Eq' :
  forall {Σ Γ A u v},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEq A u v : Ty.
Proof.
  intros Σ Γ A u v hg hu hv.
  destruct (istype_type hg hu) as [[] ?].
  eapply meta_conv.
  - eapply type_Eq ; eassumption.
  - reflexivity.
Defined.

Lemma type_Refl' :
  forall {Σ Γ A u},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u hg h.
  destruct (istype_type hg h).
  eapply type_Refl ; eassumption.
Defined.

Lemma type_Sort' :
  forall {Σ Γ},
    wf Σ Γ ->
    Σ ;;; Γ |-i Ty : Ty.
Proof.
  intros Σ Γ h.
  eapply meta_conv.
  - eapply type_Sort. assumption.
  - reflexivity.
Defined.

Lemma wf_snoc' :
  forall {Σ Γ A},
    Σ ;;; Γ |-i A : Ty ->
    wf Σ (Γ ,, A).
Proof.
  intros Σ Γ A h.
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

(* Maybe move somewhere else *)
Ltac ittintro :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-i ?t : ?T =>
    lazymatch t with
    | sRel ?n => refine (@type_Rel Sorts.type_in_type _ _ n _ _)
    | sSort _ => eapply type_Sort'
    | sProd _ _ _ => eapply type_Prod' ; [| intro ]
    | sLambda _ _ _ _ => eapply type_Lambda' ; [ .. | intro ]
    | sApp _ _ _ _ => eapply type_App'
    | sSum _ _ _ => eapply type_Sum' ; [| intro ]
    | sPair _ _ _ _ => eapply type_Pair'
    | sPi1 _ _ _ => eapply type_Pi1'
    | sPi2 _ _ _ => eapply type_Pi2'
    | sEq _ _ _ => eapply type_Eq'
    | sRefl _ _ => eapply type_Refl'
    | sAx _ => eapply type_Ax ; [| lazy ; try reflexivity ]
    | _ => fail "No introduction rule for" t
    end
  | _ => fail "Not applicable"
  end.

Lemma type_glob_cons' :
  forall {Σ d},
    type_glob Σ ->
    fresh_glob (dname d) Σ ->
    (type_glob Σ -> isType Σ [] (dtype d)) ->
    Xcomp (dtype d) ->
    type_glob (d :: Σ).
Proof.
  intros Σ d hg hf hd hx.
  specialize (hd hg).
  econstructor ; eassumption.
Defined.

Ltac glob Σi :=
  first [
    eapply type_glob_nil
  | eapply type_glob_cons' ; [
      idtac
    | repeat (lazy - [Σi] ; econstructor) ; lazy - [Σi]  ; try discriminate
    | intro ; exists tt
    | repeat econstructor
    ]
  ].

Ltac ittcheck1 Σi :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-i ?t : ?T =>
    first [
      eapply meta_conv ; [ ittintro | lazy - [Σi]  ; try reflexivity ]
    | eapply meta_ctx_conv ; [
        eapply meta_conv ; [ ittintro | lazy - [Σi]  ; try reflexivity ]
      | cbn ; try reflexivity
      ]
    ]
  | |- wf ?Σ ?Γ => first [ assumption | eapply wf_snoc' | econstructor ]
  | |- sSort _ = sSort _ => first [ lazy - [Σi]  ; reflexivity | shelve ]
  | |- type_glob _ => first [ assumption | glob ]
  | _ => fail "Not applicable"
  end.

Ltac ittcheck' Σi := ittcheck1 Σi ; try (lazy  - [Σi] ; mylia).

Ltac ittcheck Σi := repeat (ittcheck' Σi).