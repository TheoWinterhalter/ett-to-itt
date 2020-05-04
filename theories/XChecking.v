(*! General utilities to build ETT derivations *)

From Coq Require Import Bool String List BinPos Compare_dec Lia.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import utils Ast Typing Checker.
From Translation Require Import util Quotes Sorts SAst SLiftSubst SCommon
     ITyping ITypingInversions ITypingLemmata ITypingAdmissible XTyping
     FundamentalLemma Translation FinalTranslation FullQuote
     IChecking XTypingLemmata XInversions.

(* For efficiency reasons we use type in type for examples. *)
Existing Instance Sorts.type_in_type.

(* Even when not necessary, we require wf Σ Γ so that we can propagate
   the information that the context is indeed well-formed.
 *)

Lemma xtype_Prod' :
  forall {Σ Γ n A B},
    wf Σ Γ ->
    Σ ;;; Γ |-x A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : Ty) ->
    Σ ;;; Γ |-x sProd n A B : Ty.
Proof.
  intros Σ Γ n A B hw hA hB.
  assert (hwA : wf Σ (Γ ,, A)).
  { econstructor ; eassumption. }
  specialize (hB hwA).
  eapply type_Prod with (s1 := tt) (s2 := tt) ; assumption.
Defined.

Lemma xtype_Lambda' :
  forall {Σ Γ n n' A B t},
    xtype_glob Σ ->
    wf Σ Γ ->
    Σ ;;; Γ |-x A : Ty ->
    (wf Σ (Γ,, A) -> Σ ;;; Γ ,, A |-x t : B) ->
    Σ ;;; Γ |-x sLambda n A B t : sProd n' A B.
Proof.
  intros Σ Γ n n' A B t xhg hw hA ht.
  assert (hwA : wf Σ (Γ ,, A)).
  { econstructor ; eassumption. }
  specialize (ht hwA).
  pose (istype_type xhg hwA ht).
  eapply type_Lambda ; eassumption.
Defined.

Lemma xtype_App' :
  forall {Σ Γ n t A B u},
    xtype_glob Σ ->
    wf Σ Γ ->
    Σ ;;; Γ |-x t : sProd n A B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sApp t A B u : (B{0 := u})%s.
Proof.
  intros Σ Γ n t A B u xhg hw ht hu.
  pose proof (istype_type xhg hw hu) as hA.
  pose proof (istype_type xhg hw ht) as hPi.
  assert (hwA : wf Σ (Γ ,, A)).
  { econstructor ; eassumption. }
  destruct (inversionProd hPi) as [[? ?] ?].
  eapply type_App ; eassumption.
Defined.

Lemma xtype_Sum' :
  forall {Σ Γ n A B},
    wf Σ Γ ->
    Σ ;;; Γ |-x A : Ty ->
    (wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-x B : Ty) ->
    Σ ;;; Γ |-x sSum n A B : Ty.
Proof.
  intros Σ Γ n A B hw hA hB.
  assert (hwA : wf Σ (Γ ,, A)).
  { econstructor ; eassumption. }
  specialize (hB hwA).
  eapply type_Sum with (s1 := tt) (s2 := tt) ; assumption.
Defined.

Lemma xtype_Eq' :
  forall {Σ Γ A u v},
    xtype_glob Σ ->
    wf Σ Γ ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : A ->
    Σ ;;; Γ |-x sEq A u v : Ty.
Proof.
  intros Σ Γ A u v xhg hw hu hv.
  pose proof (istype_type xhg hw hu) as hA.
  eapply type_Eq with (s := tt) ; assumption.
Defined.

Lemma xtype_Refl' :
  forall {Σ Γ A u},
    xtype_glob Σ ->
    wf Σ Γ ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u xhg hw hu.
  pose proof (istype_type xhg hw hu) as hA.
  eapply type_Refl ; eassumption.
Defined.

Lemma xtype_Sort' :
  forall {Σ Γ},
    Σ ;;; Γ |-x Ty : Ty.
Proof.
  intros Σ Γ.
  eapply type_Sort with (s := tt).
Defined.

(* Lemma xwf_snoc' : *)
(*   forall {Σ Γ A}, *)
(*     Σ ;;; Γ |-x A : Ty -> *)
(*     wf Σ (Γ ,, A). *)
(* Proof. *)
(*   intros Σ Γ A h. *)
(*   econstructor. *)
(*   - eapply typing_wf. eassumption. *)
(*   - eassumption. *)
(* Defined. *)

Lemma xtype_glob_cons' :
  forall {Σ d},
    xtype_glob Σ ->
    fresh_glob (dname d) Σ ->
    (xtype_glob Σ -> isType Σ [] (dtype d)) ->
    xtype_glob (d :: Σ).
Proof.
  intros Σ d hg hf hd.
  specialize (hd hg).
  econstructor ; eassumption.
Defined.

Ltac xglob Σi :=
  first [
    eapply xtype_glob_nil
  | eapply xtype_glob_cons' ; [
      idtac
    | repeat (lazy - [Σi]; econstructor) ; lazy - [Σi]; try discriminate
    | intro
    ]
  ].

Ltac ettintro Σi :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-x ?t : ?T =>
    lazymatch t with
    | sRel ?n => refine (@type_Rel Sorts.type_in_type _ _ n _)
    | sSort _ => eapply xtype_Sort'
    | sProd _ _ _ => eapply xtype_Prod' ; [ .. | intro ]
    | sLambda _ _ _ _ => eapply xtype_Lambda' ; [ .. | intro ]
    | sApp _ _ _ _ => eapply xtype_App'
    | sSum _ _ _ => eapply xtype_Sum' ; [ .. | intro ]
    | sPair _ _ _ _ => eapply type_Pair
    | sPi1 _ _ _ => eapply type_Pi1
    | sPi2 _ _ _ => eapply type_Pi2
    | sEq _ _ _ => eapply xtype_Eq'
    | sRefl _ _ => eapply xtype_Refl'
    | sAx _ => eapply type_Ax ; lazy - [Σi] ; try reflexivity
    | _ => fail "No introduction rule for" t
    end
  | _ => fail "Not applicable"
  end.

Ltac ettcheck1 Σi :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-x ?t : ?T =>
    first [
      eapply meta_conv ; [ ettintro Σi | lazy - [Σi] ; reflexivity ]
    | eapply type_conv ; [ ettintro Σi | .. ]
    (* | eapply meta_ctx_conv ; [ *)
    (*     eapply meta_conv ; [ ettintro | lazy ; try reflexivity ] *)
    (*   | cbn ; try reflexivity *)
    (*   ] *)
    ]
  | |- wf ?Σ ?Γ => first [ assumption | econstructor ]
  | |- sSort _ = sSort _ => first [ lazy - [Σi]  ; reflexivity | shelve ]
  | |- type_glob _ => first [ assumption | glob Σi]
  | |- xtype_glob _ => first [ assumption | xglob Σi ]
  | _ => fail "Not applicable"
  end.

Ltac ettcheck' Σi := ettcheck1 Σi; try (lazy - [Σi] ; mylia).

Ltac ettcheck Σi := repeat (ettcheck' Σi).