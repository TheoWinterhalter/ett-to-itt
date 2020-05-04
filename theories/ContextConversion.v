(* Context Conversion  *)

From Coq Require Import Bool String List BinPos Compare_dec Lia.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata.

Section ContextConversion.

Context `{Sort_notion : Sorts.notion}.

Inductive ctxconv : scontext -> scontext -> Type :=
| ctxconv_nil : ctxconv [] []
| ctxconv_cons Γ Δ A B:
    ctxconv Γ Δ ->
    A ≡ B ->
    ctxconv (Γ,, A) (Δ,, B).

Derive Signature for ctxconv.

Fact ctxconv_refl :
  forall {Γ}, ctxconv Γ Γ.
Proof.
  intros Γ. induction Γ.
  - constructor.
  - constructor.
    + assumption.
    + apply conv_refl.
Defined.

Fact ctxconv_length :
  forall {Γ Δ},
    ctxconv Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Γ Δ h. induction h.
  - reflexivity.
  - cbn. f_equal. assumption.
Defined.

End ContextConversion.

Ltac lift_sort :=
  match goal with
  | |- _ ;;; _ |-i lift ?n ?k ?t : ?S => change S with (lift n k S)
  | |- _ ;;; _ |-i ?t { ?n := ?u } : ?S => change S with (S {n := u})
  | |- sSort ?s ≡ lift ?n ?k ?t =>
    change (sSort s) with (lift n k (sSort s))
  | |- sSort ?s ≡ ?t{ ?n := ?u } =>
    change (sSort s) with ((sSort s){ n := u })
  | |- lift ?n ?k ?t ≡ sSort ?s =>
    change (sSort s) with (lift n k (sSort s))
  | |- ?t{ ?n := ?u } ≡ sSort ?s =>
    change (sSort s) with ((sSort s){ n := u })
  end.

Section ctxconv.

  Context `{Sort_notion : Sorts.notion}.

  Fact safe_nth_conv :
    forall {Γ Δ},
      ctxconv Γ Δ ->
      forall n is1 is2,
        safe_nth Γ (exist _ n is1) ≡ safe_nth Δ (exist _ n is2).
  Proof.
    intros Γ Δ h. induction h ; intros n is1 is2.
    - cbn. bang.
    - destruct n.
      + cbn. assumption.
      + cbn. apply IHh.
  Defined.

  Inductive ctxctx Σ : scontext -> scontext -> Prop :=
  | ctxctx_nil : ctxctx Σ [] []
  | ctxctx_cons Γ Δ A B :
      ctxctx Σ Γ Δ ->
      isType Σ Δ A ->
      ctxctx Σ (Γ,, A) (Δ,, B).

  Fact ctxctx_type :
    forall {Σ Γ Δ n} isdecl,
      type_glob Σ ->
      wf Σ Γ ->
      wf Σ Δ ->
      ctxctx Σ Γ Δ ->
      isType Σ Δ (lift0 (S n) (safe_nth Γ (exist _ n isdecl))).
  Proof.
    intros Σ Γ Δ n isdecl hg w1 w2 hc.
    revert n isdecl w1 w2.
    induction hc ; intros n isdecl w1 w2.
    - cbn. bang.
    - destruct n.
      + cbn.
        destruct H.
        dependent destruction w2.
        eexists. lift_sort.
        eapply typing_lift01 ; eassumption.
      + cbn.
        dependent destruction w1.
        dependent destruction w2.
        match goal with
        | |- context [ exist _ _ ?isdecl ] =>
          set (is' := isdecl)
        end.
        destruct (IHhc _ is' w1 w2).
        eexists.
        replace (S (S n)) with (1 + (S n))%nat by mylia.
        rewrite <- liftP3 with (k := 0) by mylia.
        lift_sort. eapply typing_lift01 ; eassumption.
  Defined.

  Ltac tih type_ctxconv' :=
    lazymatch goal with
    | |- _ ;;; (?Δ,, ?A),, ?B |-i _ : _ =>
      eapply type_ctxconv' ; [
        eassumption
      | assumption
      | econstructor ; [
          econstructor ; [ assumption | tih type_ctxconv' ]
        | idtac
        ]
      | econstructor ; [
          econstructor ; [ assumption | eexists ; tih type_ctxconv' ]
        | idtac
        ]
      | econstructor ; [
          econstructor ; [ assumption | apply conv_refl ]
        | apply conv_refl
        ]
      ]
    | |- _ ;;; ?Δ,, ?A |-i _ : _ =>
      eapply type_ctxconv' ; [
        eassumption
      | assumption
      | econstructor ; [ assumption | tih type_ctxconv' ]
      | econstructor ; [ assumption | eexists ; tih type_ctxconv' ]
      | econstructor ; [ assumption | apply conv_refl ]
      ]
    | |- _ ;;; _ |-i _ : _ =>
      eapply type_ctxconv' ; eassumption
    | _ => fail "Not applicable tih"
    end.

  Ltac ih :=
    lazymatch goal with
    | type_ctxconv' :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm),
          Σ;;; Γ |-i t : A ->
          type_glob Σ ->
          wf Σ Δ ->
          ctxctx Σ Γ Δ ->
          ctxconv Γ Δ ->
          Σ;;; Δ |-i t : A
      |- _ => tih type_ctxconv'
    | _ => fail "Cannot find type_ctxconv'"
    end.

  Fixpoint type_ctxconv' {Σ Γ Δ t A} (ht : Σ ;;; Γ |-i t : A) {struct ht} :
    type_glob Σ ->
    wf Σ Δ ->
    ctxctx Σ Γ Δ ->
    ctxconv Γ Δ ->
    Σ ;;; Δ |-i t : A.
  Proof.
    intros hg hw hcc hc. destruct ht.
    all: try (econstructor ; ih).
    - destruct (ctxctx_type isdecl hg H hw hcc).
      eapply type_conv.
      + econstructor. assumption.
      + eassumption.
      + apply lift_conv. apply conv_sym. apply safe_nth_conv. assumption.
    - econstructor. assumption.
    - econstructor.
      + lift_sort. eapply typing_lift01 ; try eassumption ; ih.
      + eapply typing_lift01 ; try eassumption ; ih.
      + refine (type_Rel _ _ _ _ _) ; [| cbn ; mylia ].
        econstructor ; try eassumption. ih.
    - eexists. econstructor.
      + lift_sort. eapply typing_lift01 ; try eassumption ; ih.
      + eapply typing_lift01 ; try eassumption ; ih.
      + refine (type_Rel _ _ _ _ _) ; [| cbn ; mylia ].
        econstructor ; try eassumption. ih.
    - eapply type_HeqTrans with (B0 := B) ; ih.
    - econstructor ; try ih.
      eapply type_ctxconv'.
      + eassumption.
      + assumption.
      + econstructor ; try assumption.
        econstructor ; ih.
      + econstructor ; try assumption.
        eexists ; econstructor ; ih.
      + econstructor ; try assumption.
        apply conv_refl.
    - econstructor ; try ih.
      + eapply type_ctxconv'.
        * eassumption.
        * assumption.
        * econstructor ; try assumption.
          econstructor ; ih.
        * econstructor ; try assumption.
          eexists ; econstructor ; ih.
        * econstructor ; try assumption.
          apply conv_refl.
      + eapply type_ctxconv'.
        * eassumption.
        * assumption.
        * econstructor ; try assumption.
          econstructor ; ih.
        * econstructor ; try assumption.
          eexists ; econstructor ; ih.
        * econstructor ; try assumption.
          apply conv_refl.
    - econstructor ; try ih.
      eapply type_ctxconv'.
      + eassumption.
      + assumption.
      + econstructor ; try assumption.
        econstructor ; ih.
      + econstructor ; try assumption.
        eexists ; econstructor ; ih.
      + econstructor ; try assumption.
        apply conv_refl.
    - econstructor ; try ih.
      eapply type_ctxconv'.
      + eassumption.
      + assumption.
      + econstructor ; try assumption.
        econstructor ; ih.
      + econstructor ; try assumption.
        eexists ; econstructor ; ih.
      + econstructor ; try assumption.
        apply conv_refl.
    - econstructor ; try ih.
      eapply type_ctxconv'.
      + eassumption.
      + assumption.
      + econstructor ; try assumption.
        econstructor ; ih.
      + econstructor ; try assumption.
        eexists ; econstructor ; ih.
      + econstructor ; try assumption.
        apply conv_refl.
    - econstructor ; try ih.
      eapply type_ctxconv'.
      + eassumption.
      + assumption.
      + econstructor ; try assumption.
        econstructor ; ih.
      + econstructor ; try assumption.
        eexists ; econstructor ; ih.
      + econstructor ; try assumption.
        apply conv_refl.
    - econstructor ; try ih.
      eapply type_ctxconv'.
      + eassumption.
      + assumption.
      + econstructor ; try assumption.
        econstructor ; ih.
      + econstructor ; try assumption.
        eexists ; econstructor ; ih.
      + econstructor ; try assumption.
        apply conv_refl.
    - eapply type_ProjT2 with (A3 := A1) ; ih.
    - eapply type_Ax.
      + assumption.
      + assumption.
    - econstructor.
      + ih.
      + ih.
      + assumption.

    Unshelve. rewrite <- ctxconv_length by eassumption. assumption.
  Qed.

  Lemma type_ctxconv {Σ Γ Δ t A} (ht : Σ ;;; Γ |-i t : A) :
    type_glob Σ ->
    wf Σ Δ ->
    ctxconv Γ Δ ->
    Σ ;;; Δ |-i t : A.
  Proof.
    intros hg hw hc.
    eapply type_ctxconv' ; try eassumption.
    assert (w1 : wf Σ Γ).
    { eapply typing_wf. eassumption. }
    clear t A ht. revert hw.
    induction hc ; intro w2.
    - constructor.
    - dependent destruction w1.
      dependent destruction w2.
      econstructor.
      + eapply IHhc ; assumption.
      + eexists. eapply type_ctxconv' ; try eassumption.
        eapply IHhc ; assumption.
  Qed.

End ctxconv.