(* Subject Reduction *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata ContextConversion Uniqueness.
Import ListNotations.

Section subjred.

  Context `{Sort_notion : Sorts.notion}.

  Ltac sr' hg hr IHhr :=
    intros Γ ? ht ;
    ttinv ht ; destruct (istype_type hg ht) ;
    specialize (IHhr _ _ ltac:(eassumption)) ;
    pose proof (conv_red_l _ _ _ hr (conv_refl _)) as heq ;
    (eapply type_conv ; try eassumption) ;
    eapply type_conv ; [
      (econstructor ; try eassumption) ;
      econstructor ; eassumption
    | first [
        econstructor ; eassumption
      | try lift_sort ; eapply typing_subst ; eassumption
      ]
    | try conv rewrite heq ; apply conv_refl
    ].

  Ltac sr :=
    lazymatch goal with
    | [ hg : type_glob ?Σ,
        hr : _ ▷ _,
        ih : forall _ _, _ ;;; _ |-i _ : _ -> _ ;;; _ |-i _ : _
      |- _ ] => sr' hg hr ih
    | _ => fail "Failed to collect assumptions"
    end.

  Ltac canvas' hg hr IHhr :=
    intros Γ ? ht ;
    ttinv ht ; destruct (istype_type hg ht) ;
    try specialize (IHhr _ _ ltac:(eassumption)) ;
    pose proof (conv_red_l _ _ _ hr (conv_refl _)) as heq ;
    (eapply type_conv ; try eassumption) ;
    eapply type_conv ; [
      try ((econstructor ; try eassumption) ;
      econstructor ; eassumption)
    | first [
        econstructor ; eassumption
      | try lift_sort ; eapply typing_subst ; eassumption
      | idtac
      ]
    | try conv rewrite heq ; try apply conv_refl
    ].

  Ltac canvas :=
    lazymatch goal with
    | [ hg : type_glob ?Σ,
        hr : _ ▷ _,
        ih : forall _ _, _ ;;; _ |-i _ : _ -> _ ;;; _ |-i _ : _
      |- _ ] => canvas' hg hr ih
    | _ => fail "Failed to collect assumptions"
    end.

  Theorem subj_red :
    forall {Σ Γ t u T},
      type_glob Σ ->
      t ▷ u ->
      Σ ;;; Γ |-i t : T ->
      Σ ;;; Γ |-i u : T.
  Proof.
    intros Σ Γ t u T hg hr ht. revert Γ T ht.
    induction hr.
    all: try sr.
    - intros Γ T ht.
      destruct (istype_type hg ht).
      ttinv ht. ttinv h1.
      destruct (prod_inv h8).
      eapply type_conv ; try eassumption.
      eapply typing_subst ; try eassumption.
      eapply type_conv ; try eassumption.
      eapply type_ctxconv ; try eassumption.
      + econstructor ; try eassumption.
        eapply typing_wf. eassumption.
      + constructor ; try assumption.
        apply ctxconv_refl.
    - intros Γ T ht.
      destruct (istype_type hg ht).
      ttinv ht. ttinv h3.
      destruct (eq_conv_inv h9) as [? [? ?]].
      eapply type_conv ; try eassumption.
      eapply conv_trans ; try eassumption.
      apply cong_subst.
      + apply conv_sym.
        apply cong_Refl ; assumption.
      + apply substs_conv. eapply conv_trans ; try eassumption.
        apply conv_sym. assumption.
    - intros Γ T' ht.
      destruct (istype_type hg ht).
      ttinv ht. ttinv h0.
      destruct (eq_conv_inv h7) as [? [? ?]].
      eapply type_conv ; try eassumption.
      eapply conv_trans.
      + eapply conv_sym. eassumption.
      + eapply conv_trans ; [| eassumption ]. assumption.
    - intros Γ T ht.
      ttinv ht. destruct (istype_type hg ht).
      specialize (IHhr _ _ ltac:(eassumption)).
      pose proof (conv_red_l _ _ _ hr (conv_refl _)).
      eapply type_conv ; try eassumption.
      eapply type_conv.
      + econstructor ; try eassumption.
        * eapply type_ctxconv ; try eassumption.
          -- econstructor ; try eassumption.
             eapply typing_wf. eassumption.
          -- constructor ; try assumption.
             apply ctxconv_refl.
        * eapply type_ctxconv ; try eassumption.
          -- econstructor ; try eassumption.
             eapply typing_wf. eassumption.
          -- constructor ; try assumption.
             apply ctxconv_refl.
      + econstructor ; eassumption.
      + eapply cong_Prod ;
          try (apply conv_refl) ;
          try assumption ;
          try (apply conv_sym ; assumption).
    - canvas.
      econstructor ; try eassumption.
      + eapply type_ctxconv ; try eassumption.
        * econstructor ; try eassumption.
          eapply typing_wf. eassumption.
        * constructor ; try assumption. apply ctxconv_refl.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          eapply type_ctxconv ; try eassumption.
          -- econstructor ; try eassumption.
             eapply typing_wf. eassumption.
          -- constructor ; try assumption. apply ctxconv_refl.
        * conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
    - intros Γ ? ht.
      ttinv ht. destruct (istype_type hg ht).
      specialize (IHhr _ _ ltac:(eassumption)).
      pose proof (conv_red_l _ _ _ hr (conv_refl _)) as heq.
      eapply type_conv ; try eassumption.
      eapply type_conv.
      + econstructor ; try eassumption ;
        econstructor ; try eassumption.
        * econstructor ; eassumption.
        * conv rewrite heq. apply conv_refl.
      + first [
          econstructor ; eassumption
        | try lift_sort ; eapply typing_subst ; eassumption
        ].
      + eapply subst_conv. apply conv_sym. assumption.
    - canvas.
      apply substs_conv. apply conv_sym. assumption.
    - canvas.
      + econstructor ; try assumption.
        eapply type_ctxconv ; try eassumption.
        * econstructor ; try eassumption.
          eapply typing_wf. eassumption.
        * econstructor ; try eassumption.
          apply ctxconv_refl.
      + econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas.
      + econstructor ; try eassumption.
        eapply type_ctxconv ; try eassumption.
        * econstructor ;  try eassumption.
          eapply typing_wf. eassumption.
        * econstructor ; try eassumption.
          apply ctxconv_refl.
      + econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor ; try eassumption.
      + eapply type_ctxconv ; try eassumption.
        * econstructor ; try eassumption.
          eapply typing_wf. eassumption.
        * econstructor ; try eassumption.
          apply ctxconv_refl.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
      + apply subst_conv. assumption.
    - canvas. econstructor ; try eassumption.
      econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
      + apply substs_conv. assumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                eapply type_ctxconv ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   apply ctxconv_refl.
             ++ eapply cong_Sum ; try eassumption.
                apply conv_refl.
          -- eapply type_ctxconv ; try eassumption.
             ++ econstructor ; try eassumption.
                eapply typing_wf. eassumption.
             ++ econstructor ; try eassumption. apply ctxconv_refl.
        * apply conv_sym. assumption.
      + eassumption.
    - canvas.
      + econstructor ; try eassumption.
        econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * eapply cong_Sum ; try eassumption.
          apply conv_refl.
      + eassumption.
    - canvas. eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                eapply type_ctxconv ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   apply ctxconv_refl.
             ++ apply cong_Sum ; try eassumption. apply conv_refl.
          -- eapply type_ctxconv ; try eassumption.
             ++ econstructor ; try eassumption.
                eapply typing_wf. eassumption.
             ++ econstructor ; try eassumption. apply ctxconv_refl.
        * match goal with
          | |- _ ;;; _ |-i _ : ?S =>
            change S with (S{ 0 := sPi1 A B p })
          end.
          eapply typing_subst ; try eassumption.
          econstructor ; try eassumption.
        * apply substs_conv.
          apply conv_sym. eapply cong_Pi1 ; try apply conv_refl. assumption.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{ 0 := sPi1 A B p })
        end.
        eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- apply cong_Sum ; try eassumption. apply conv_refl.
        * match goal with
          | |- _ ;;; _ |-i _ : ?S =>
            change S with (S{ 0 := sPi1 A B p })
          end.
          eapply typing_subst ; try eassumption.
          econstructor ; try eassumption.
        * apply conv_sym. eapply cong_subst ; try eassumption.
          apply cong_Pi1 ; try apply conv_refl. assumption.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{ 0 := sPi1 A B p })
        end.
        eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
    - canvas.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{ 0 := sPi1 A B p })
        end.
        eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
      + apply substs_conv. apply conv_sym.
        apply cong_Pi1 ; try apply conv_refl. assumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. apply conv_sym.
      apply cong_Eq ; try apply conv_refl ; try assumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; eassumption.
        * econstructor ; eassumption.
        * eapply type_ctxconv ; try eassumption.
          -- econstructor.
             ++ econstructor ; try eassumption.
                eapply typing_wf. eassumption.
             ++ econstructor.
                ** lift_sort. eapply typing_lift01 ; try eassumption.
                ** eapply typing_lift01 ; try eassumption.
                   econstructor ; try eassumption.
                ** refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                   econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
          -- constructor.
             ++ constructor ; try assumption. apply ctxconv_refl.
             ++ apply cong_Eq ; try apply conv_refl.
                apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
          -- apply cong_Eq ; try apply conv_refl. assumption.
        * econstructor ; try eassumption.
          -- match goal with
             | |- _ ;;; _ |-i _ : ?S =>
               change S with (S{1 := u}{0 := sRefl A' u})
             end.
             eapply typing_subst2 ; try eassumption.
             cbn. rewrite !lift_subst, lift00.
             econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ apply conv_sym. apply cong_Eq ; try apply conv_refl.
                assumption.
          -- apply substs_conv. conv rewrite heq. apply conv_refl.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{1 := v}{0 := p})
        end.
        eapply typing_subst2 ; try eassumption.
        cbn. rewrite !lift_subst, lift00.
        assumption.
    - canvas.
      + econstructor ; try eassumption.
        * eapply type_ctxconv ; try eassumption.
          -- econstructor.
             ++ econstructor ; try eassumption.
                eapply typing_wf. eassumption.
             ++ econstructor.
                ** lift_sort. eapply typing_lift01 ; try eassumption.
                ** eapply typing_lift01 ; try eassumption.
                ** refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                   econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
          -- constructor.
             ++ apply ctxconv_refl.
             ++ apply cong_Eq ; try apply conv_refl.
                apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- apply cong_Eq ; try apply conv_refl. assumption.
        * econstructor ; try eassumption.
          -- match goal with
             | |- _ ;;; _ |-i _ : ?S =>
               change S with (S{1 := u'}{0 := sRefl A u'})
             end.
             eapply typing_subst2 ; try eassumption.
             cbn. rewrite !lift_subst, lift00.
             econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ apply conv_sym. apply cong_Eq ; try apply conv_refl.
                assumption.
          -- apply cong_subst.
             ++ conv rewrite heq. apply conv_refl.
             ++ apply substs_conv. assumption.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{1 := v}{0 := p})
        end.
        eapply typing_subst2 ; try eassumption.
        cbn. rewrite !lift_subst, lift00.
        assumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- match goal with
             | |- _ ;;; _ |-i _ : ?S =>
               change S with (S{1 := u}{0 := sRefl A u})
             end.
             eapply typing_subst2 ; try eassumption.
             cbn. rewrite !lift_subst, lift00.
             econstructor ; try eassumption.
          -- apply subst_conv. apply subst_conv. assumption.
        * match goal with
          | |- _ ;;; _ |-i _ : ?S =>
            change S with (S{1 := v}{0 := p})
          end.
          eapply typing_subst2 ; try eassumption.
          cbn. rewrite !lift_subst, lift00.
          assumption.
        * apply subst_conv. apply subst_conv. apply conv_sym. assumption.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{1 := v}{0 := p})
        end.
        eapply typing_subst2 ; try eassumption.
        cbn. rewrite !lift_subst, lift00.
        assumption.
    - canvas.
      match goal with
      | |- _ ;;; _ |-i _ : ?S =>
        change S with (S{1 := v}{0 := p})
      end.
      eapply typing_subst2 ; try eassumption.
      cbn. rewrite !lift_subst, lift00.
      assumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- apply cong_Eq ; try apply conv_refl. assumption.
        * match goal with
          | |- _ ;;; _ |-i _ : ?S =>
            change S with (S{1 := v}{0 := p})
          end.
          eapply typing_subst2 ; try eassumption.
          cbn. rewrite !lift_subst, lift00.
          assumption.
        * apply subst_conv. apply substs_conv. apply conv_sym. assumption.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{1 := v}{0 := p})
        end.
        eapply typing_subst2 ; try eassumption.
        cbn. rewrite !lift_subst, lift00.
        assumption.
    - canvas.
      + match goal with
        | |- _ ;;; _ |-i _ : ?S =>
          change S with (S{1 := v}{0 := p})
        end.
        eapply typing_subst2 ; try eassumption.
        cbn. rewrite !lift_subst, lift00.
        assumption.
      + apply substs_conv. apply conv_sym. assumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             econstructor. eapply typing_wf. eassumption.
          -- apply cong_Eq ; try apply conv_refl. assumption.
        * econstructor ; try eassumption.
      + eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             econstructor. eapply typing_wf. eassumption.
          -- apply cong_Eq ; try apply conv_refl. assumption.
        * apply conv_sym. assumption.
      + eassumption.
    - canvas. eassumption.
    - canvas. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. apply conv_sym.
      apply cong_Heq ; try assumption ; try apply conv_refl.
    - canvas. apply conv_sym.
      apply cong_Heq ; try assumption ; try apply conv_refl.
    - canvas. apply conv_sym. assumption.
    - canvas.
      eapply type_HeqTrans with (B0 := B) (b0 := b) ; try eassumption.
    - canvas.
      eapply type_HeqTrans with (B0 := B) (b0 := b) ; try eassumption.
    - canvas.
      + econstructor.
        * eapply type_HeqTransport ; [ .. | eassumption | eassumption ] ; eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        econstructor ; try eassumption.
    - canvas.
      + econstructor.
        * eapply type_HeqTransport ; [ .. | eassumption | eassumption ] ; eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
        * apply conv_sym. apply cong_Heq ; try apply conv_refl.
          -- assumption.
          -- conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
          -- apply cong_Heq ; try apply conv_refl.
             apply subst_conv. apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
          -- apply cong_Heq ; try apply conv_refl.
             apply subst_conv. apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq. all: try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** eapply typing_subst ; try eassumption.
                   --- eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       *** econstructor ; try eassumption.
                       *** eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** eapply typing_subst ; try eassumption.
                   --- eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq. all: try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq. all: try apply conv_refl.
          -- conv rewrite heq. apply conv_refl.
          -- conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq. all: try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** eapply typing_subst ; try eassumption.
                   --- eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** eapply typing_subst ; try eassumption.
                   --- eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       *** econstructor ; try eassumption.
                       *** eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq. all: try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq. all: try apply conv_refl.
          -- conv rewrite heq. apply conv_refl.
          -- conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ eapply typing_subst ; try eassumption.
                ** eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ eapply typing_subst ; try eassumption.
                ** eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
          -- apply cong_Heq. all: try apply conv_refl.
             apply subst_conv. apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq. all: try apply conv_refl.
          conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ eapply typing_subst ; try eassumption.
                ** eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ eapply typing_subst ; try eassumption.
                ** eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
          -- apply cong_Heq. all: try apply conv_refl.
             apply subst_conv. apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq. all: try apply conv_refl.
          conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq. all: try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := u1).
             econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   --- econstructor ; try eassumption.
                   --- conv rewrite heq. apply conv_refl.
             ++ apply cong_Heq. all: try apply conv_refl.
                conv rewrite heq. apply conv_refl.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ conv rewrite heq. apply conv_refl.
        * econstructor ; try eassumption.
          -- lift_sort. eapply typing_subst ; eassumption.
          -- lift_sort. eapply typing_subst ; eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply conv_sym. apply cong_Heq. all: try apply conv_refl.
          -- apply subst_conv. assumption.
          -- conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * lift_sort. eapply typing_subst ; eassumption.
        * lift_sort. eapply typing_subst ; eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** econstructor. eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq. all: try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := u2).
             econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   --- econstructor ; try eassumption.
                   --- conv rewrite heq. apply conv_refl.
             ++ apply cong_Heq. all: try apply conv_refl.
                conv rewrite heq. apply conv_refl.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ conv rewrite heq. apply conv_refl.
        * econstructor ; try eassumption.
          -- lift_sort. eapply typing_subst ; eassumption.
          -- lift_sort. eapply typing_subst ; eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply conv_sym. apply cong_Heq. all: try apply conv_refl.
          -- apply subst_conv. assumption.
          -- conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * lift_sort. eapply typing_subst ; eassumption.
        * lift_sort. eapply typing_subst ; eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + lift_sort. eapply typing_subst ; eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
          -- apply cong_Heq ; try apply conv_refl.
             apply subst_conv. apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ econstructor. eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
             ++ lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort.
                   eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                     try eassumption.
                   eapply typing_wf. eassumption.
                ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- lift_sort. eapply typing_lift01 ; try eassumption.
                       econstructor ; try eassumption.
                   --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                       eapply typing_wf. eassumption.
          -- apply cong_Heq ; try apply conv_refl.
             apply subst_conv. apply lift_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor. eapply typing_wf. eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor. eapply typing_wf. eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      econstructor ; try eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := v1). econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                ** econstructor ; try eassumption.
                   --- lift_sort. eapply typing_subst ; try eassumption.
                   --- apply subst_conv. assumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. assumption.
          -- econstructor ; try eassumption.
             ++ lift_sort. eapply typing_subst ; eassumption.
             ++ apply subst_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply conv_sym. apply cong_Heq ; try apply conv_refl.
          -- apply cong_Sum ; try apply conv_refl. assumption.
          -- apply cong_Pair ; try apply conv_refl. assumption.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := v2). econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                ** econstructor ; try eassumption.
                   --- lift_sort. eapply typing_subst ; try eassumption.
                   --- apply subst_conv. assumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. assumption.
          -- econstructor ; try eassumption.
             ++ lift_sort. eapply typing_subst ; eassumption.
             ++ apply subst_conv. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply conv_sym. apply cong_Heq ; try apply conv_refl.
          -- apply cong_Sum ; try apply conv_refl. assumption.
          -- apply cong_Pair ; try apply conv_refl. assumption.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := p1). econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   --- econstructor ; try eassumption.
                   --- apply cong_Sum ; try apply conv_refl. assumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply cong_Sum ; try apply conv_refl.
                assumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ apply cong_Sum ; try apply conv_refl. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          apply cong_Pi1 ; try apply conv_refl.
          apply conv_sym. assumption.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := p2). econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   --- econstructor ; try eassumption.
                   --- apply cong_Sum ; try apply conv_refl. assumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply cong_Sum ; try apply conv_refl.
                assumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ apply cong_Sum ; try apply conv_refl. assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          apply cong_Pi1 ; try apply conv_refl.
          apply conv_sym. assumption.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := p1). econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   --- econstructor ; try eassumption.
                   --- apply cong_Sum ; try apply conv_refl. assumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply cong_Sum ; try apply conv_refl.
                assumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ apply cong_Sum ; try apply conv_refl. assumption.
        * econstructor ; try eassumption.
          -- lift_sort. eapply typing_subst ; try eassumption.
             econstructor ; try eassumption.
          -- lift_sort. eapply typing_subst ; try eassumption.
             econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply conv_sym. apply cong_Heq ; try apply conv_refl.
          -- apply cong_subst ; try assumption.
             apply cong_Pi1 ; try apply conv_refl. assumption.
          -- apply cong_Pi2 ; try apply conv_refl. assumption.
      + econstructor ; try eassumption.
        * lift_sort. eapply typing_subst ; try eassumption.
          econstructor ; try eassumption.
        * lift_sort. eapply typing_subst ; try eassumption.
          econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** econstructor ; try eassumption.
                   eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
                ** lift_sort. eapply typing_subst ; try eassumption.
                   --- lift_sort.
                       eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                         try eassumption.
                       eapply typing_wf. eassumption.
                   --- cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ lift_sort. eapply typing_lift01 ; try eassumption.
                           econstructor ; try eassumption.
                       +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                           eapply typing_wf. eassumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply subst_conv. apply lift_conv. assumption.
          -- instantiate (1 := p2). econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                ** econstructor ; try eassumption.
                   --- econstructor ; try eassumption.
                   --- apply cong_Sum ; try apply conv_refl. assumption.
             ++ apply cong_Heq ; try apply conv_refl.
                apply cong_Sum ; try apply conv_refl.
                assumption.
          -- econstructor ; try eassumption.
             ++ econstructor ; try eassumption.
             ++ apply cong_Sum ; try apply conv_refl. assumption.
        * econstructor ; try eassumption.
          -- lift_sort. eapply typing_subst ; try eassumption.
             econstructor ; try eassumption.
          -- lift_sort. eapply typing_subst ; try eassumption.
             econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- econstructor ; try eassumption.
        * apply conv_sym. apply cong_Heq ; try apply conv_refl.
          -- apply cong_subst ; try assumption.
             apply cong_Pi1 ; try apply conv_refl. assumption.
          -- apply cong_Pi2 ; try apply conv_refl. assumption.
      + econstructor ; try eassumption.
        * lift_sort. eapply typing_subst ; try eassumption.
          econstructor ; try eassumption.
        * lift_sort. eapply typing_subst ; try eassumption.
          econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
      + lift_sort. eapply typing_subst ; try eassumption.
        econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor. eapply typing_wf. eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas. econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
      + econstructor ; try eassumption.
    - canvas.
      + eapply type_HeqTypeEq with (u0 := u) (v0 := v) ; try assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             econstructor ; try eassumption.
          -- conv rewrite heq. apply conv_refl.
        * econstructor ; try eassumption.
      + econstructor ; try eassumption.
        econstructor. eapply typing_wf. eassumption.
    - canvas.
      + eapply type_HeqTypeEq with (u0 := u) (v0 := v) ; try assumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
             econstructor ; try eassumption.
          -- conv rewrite heq. apply conv_refl.
        * econstructor ; try eassumption.
      + econstructor ; try eassumption.
        econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor ; try eassumption.
      econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas. econstructor. eapply typing_wf. eassumption.
    - canvas.
      + eassumption.
      + apply conv_sym. assumption.
    - canvas.
      + eapply type_ProjT2 with (A3 := A1) ; try eassumption.
      + eassumption.
    - canvas.
      + econstructor ; try eassumption.
        * eapply type_ProjTe with (A3 := A1) (A4 := A2) ; try eassumption.
        * econstructor ; try eassumption.
          -- econstructor ; try eassumption.
          -- eapply type_ProjT2 with (A3 := A1) ; try eassumption.
        * apply cong_Heq ; try apply conv_refl.
          -- conv rewrite heq. apply conv_refl.
          -- conv rewrite heq. apply conv_refl.
      + econstructor ; try eassumption.
        * econstructor ; try eassumption.
        * eapply type_ProjT2 with (A3 := A1) ; try eassumption.

    Unshelve. all: auto.
  Qed.

End subjred.

Section nltype.

Context `{Sort_notion : Sorts.notion}.

Ltac resolve :=
  match goal with
  | ih : forall u, nl ?t = nl u -> _ ;;; _ |-i u : ?T |- _ ;;; _ |-i ?v : ?T =>
    eapply ih ; eassumption
  end.

Ltac eresolve :=
  match goal with
  | ih : forall u, nl ?t = nl u -> _ ;;; _ |-i u : _, e : nl ?t = nl ?v
    |- _ ;;; _ |-i ?v : _ =>
    eapply ih ; eassumption
  end.

Ltac resolve2 :=
  match goal with
  | ih : forall u, nl ?t = nl u -> _ ;;; ?Γ |-i u : _, e : nl ?t = nl ?v
    |- _ ;;; ?Γ |-i ?v : _ =>
    eapply ih ; eassumption
  | ih : forall u, nl ?t = nl u -> _ ;;; ?Γ,, ?A |-i u : _, e : nl ?t = nl ?v
    |- _ ;;; ?Γ,, ?B |-i ?v : _ =>
    eapply type_ctxconv ; [
      eapply ih ; eassumption
    | assumption
    | econstructor ; [
        eapply typing_wf ; eassumption
      | eresolve
      ]
    | constructor ; [
        apply ctxconv_refl
      | apply conv_eq ; assumption
      ]
    ]
  end.

Ltac disc uu e :=
  match goal with
  | h : _ ≡ _ |- _ => idtac
  | _ => destruct uu ; cbn in e ; try discriminate e ; inversion e ; clear e
  end.

Ltac go :=
  econstructor ; try resolve2 ; try eassumption.

Lemma nl_type :
  forall {Σ Γ t u T},
    type_glob Σ ->
    Σ ;;; Γ |-i t : T ->
    nl t = nl u ->
    Σ ;;; Γ |-i u : T.
Proof.
  intros Σ Γ t u T hg ht e. revert u e.
  induction ht ; intros uu e.
  all: disc uu e.
  all: try (econstructor ; eresolve).
  all: try (econstructor ; resolve2).
  - subst. econstructor. assumption.
  - subst. econstructor. assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
    + econstructor ; eassumption.
    + apply conv_eq. symmetry. cbn. f_equal ; assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      * eapply type_conv.
        -- resolve2.
        -- econstructor ; resolve2.
        -- apply conv_eq. cbn. f_equal ; assumption.
      * eapply type_conv.
        -- resolve2.
        -- resolve2.
        -- apply conv_eq. assumption.
    + lift_sort. eapply typing_subst ; eassumption.
    + apply cong_subst.
      * apply conv_eq. symmetry. assumption.
      * apply conv_eq. symmetry. assumption.
  - go.
    + go.
      * go. go.
      * go.
        -- lift_sort. eapply typing_subst ; try eassumption.
           ++ eapply IHht2. assumption.
           ++ go. apply conv_refl.
        -- apply cong_subst.
           ++ go.
           ++ go.
    + go.
    + apply conv_sym. apply cong_Sum.
      * go.
      * go.
  - go.
    + go. go.
      * go.
      * go. cbn. f_equal ; eassumption.
    + go. auto.
  - go.
    + go. go.
      * go.
      * go. cbn. f_equal ; assumption.
    + match goal with
      | |- _ ;;; _ |-i _ { 0 := ?t } : ?S =>
        change S with (S{ 0 := t })
      end.
      eapply typing_subst ; try eassumption.
      go.
    + go. symmetry. apply nl_subst.
      * assumption.
      * cbn. f_equal ; assumption.
  - econstructor ; try resolve2.
    + eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
    + eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
    + econstructor ; eassumption.
    + apply conv_eq. symmetry. cbn. f_equal ; assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
      * eapply type_conv.
        -- resolve2.
        -- resolve2.
        -- apply conv_eq. assumption.
      * eapply type_ctxconv ; try eassumption.
        -- eapply IHht4. assumption.
        -- econstructor.
           ++ econstructor.
              ** eapply typing_wf. eassumption.
              ** resolve2.
           ++ econstructor.
              ** lift_sort. eapply typing_lift01 ; try eassumption ; resolve2.
              ** eapply typing_lift01 ; try eassumption ; try resolve2.
                 eapply type_conv ; try resolve2.
                 apply conv_eq. assumption.
              ** eapply type_conv.
                 --- econstructor. econstructor ; try resolve2.
                     eapply typing_wf. eassumption.
                 --- lift_sort.
                     eapply typing_lift01 ; try eassumption ; resolve2.
                 --- apply lift_conv. cbn. apply conv_refl.
        -- repeat constructor.
           ++ apply ctxconv_refl.
           ++ assumption.
           ++ cbn. f_equal ; try assumption.
              all: apply nl_lift ; assumption.
      * eapply type_conv.
        -- resolve2.
        -- econstructor ; try resolve2.
           ++ eapply type_conv ; try resolve2.
              apply conv_eq. assumption.
           ++ eapply type_conv ; try resolve2.
              apply conv_eq. assumption.
        -- apply conv_eq. cbn. f_equal ; assumption.
      * eapply type_conv ; try resolve2.
        -- match goal with
           | |- _ ;;; _ |-i _ : ?S =>
             change S with (S{1 := uu2}{0 := sRefl uu1 uu2})
           end.
           eapply typing_subst2 ; try eassumption ; try resolve2.
           ++ eapply IHht4. assumption.
           ++ eapply type_conv ; try resolve2.
              ** econstructor ; try resolve2.
                 eapply type_conv ; try resolve2.
                 apply conv_eq. assumption.
              ** lift_sort.
                 eapply typing_subst ; try eassumption ; try resolve2.
                 econstructor.
                 --- lift_sort. eapply typing_lift01 ; eassumption.
                 --- eapply typing_lift01 ; eassumption.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     econstructor ; try eassumption.
                     eapply typing_wf. eassumption.
              ** cbn. rewrite !lift_subst, lift00.
                 apply conv_eq. cbn. symmetry. f_equal ; assumption.
        -- apply cong_subst.
           ++ apply conv_eq. cbn. f_equal ; assumption.
           ++ apply cong_subst.
              ** apply conv_eq. assumption.
              ** apply conv_eq. assumption.
    + match goal with
      | |- _ ;;; _ |-i _ : ?S =>
        change S with (S{1 := v}{0 := p})
      end.
      eapply typing_subst2 ; try eassumption.
      cbn. rewrite !lift_subst, lift00. assumption.
    + apply cong_subst.
      * apply conv_eq. symmetry. assumption.
      * apply cong_subst.
        -- apply conv_eq. symmetry. assumption.
        -- apply conv_eq. symmetry. assumption.
  - econstructor ; try resolve2.
    + econstructor ; try resolve2.
      * econstructor ; try resolve2.
        -- econstructor ; try resolve2.
           econstructor. eapply typing_wf. eassumption.
        -- apply conv_eq. cbn. f_equal ; assumption.
      * econstructor ; try resolve2.
        apply conv_eq. assumption.
    + eassumption.
    + apply conv_eq. symmetry. assumption.
  - econstructor ; try resolve2.
    + econstructor ; try resolve2.
      apply conv_eq. assumption.
    + econstructor ; try resolve2.
      apply conv_eq. assumption.
  - econstructor ; try resolve2 ; eassumption.
  - go.
    + go. go. apply conv_eq. assumption.
    + go.
    + apply conv_eq. cbn. symmetry. f_equal ; assumption.
  - go.
  - go.
  - go.
    + go.
    + go. go.
    + go. cbn. symmetry. f_equal ; try assumption.
      f_equal ; assumption.
  - go.
    + go. go.
      * go.
        -- go. econstructor.
           ++ eapply typing_wf. eassumption.
           ++ go.
        -- go. econstructor.
           ++ eapply typing_wf. eassumption.
           ++ go.
        -- lift_sort. eapply typing_subst ; try eassumption.
           ++ lift_sort.
              eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                try eassumption.
              ** go.
                 --- go. eapply typing_wf. eassumption.
                 --- apply conv_refl.
              ** eapply typing_wf. eassumption.
           ++ cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                 eapply typing_wf. eassumption.
        -- lift_sort. eapply typing_subst ; try eassumption.
           ++ lift_sort.
              eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                try eassumption.
              ** go.
                 --- go. eapply typing_wf. eassumption.
                 --- apply conv_refl.
              ** eapply typing_wf. eassumption.
           ++ cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                 eapply typing_wf. eassumption.
      * go. cbn. f_equal.
        -- apply nl_subst.
           ++ apply nl_lift. assumption.
           ++ reflexivity.
        -- apply nl_subst.
           ++ apply nl_lift. assumption.
           ++ reflexivity.
    + go.
      * go. eapply typing_wf. eassumption.
      * go. eapply typing_wf. eassumption.
      * go.
      * go.
    + go. cbn. symmetry. f_equal ; f_equal ; assumption.
  - go.
    + go.
      * go.
        -- go.
           ++ go. eapply typing_wf. eassumption.
           ++ go. eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                   try eassumption.
                 --- go.
                     +++ go. go. eapply typing_wf. eassumption.
                     +++ apply conv_refl.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                   try eassumption.
                 --- go.
                     +++ go. go. eapply typing_wf. eassumption.
                     +++ apply conv_refl.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
        -- go. cbn. f_equal.
           ++ apply nl_subst.
              ** apply nl_lift. assumption.
              ** reflexivity.
           ++ apply nl_subst.
              ** apply nl_lift. assumption.
              ** reflexivity.
      * go.
        -- go.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                   try eassumption.
                 --- go.
                     +++ go. go. eapply typing_wf. eassumption.
                     +++ apply conv_refl.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                   try eassumption.
                 --- go.
                     +++ go. go. eapply typing_wf. eassumption.
                     +++ apply conv_refl.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ eapply typing_subst ; try eassumption.
              ** eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                   try eassumption.
                 --- go. apply conv_eq. assumption.
                 --- go.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ eapply typing_subst ; try eassumption.
              ** eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                   try eassumption.
                 --- go. apply conv_eq. assumption.
                 --- go.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
        -- go. cbn. f_equal.
           all: apply nl_subst.
           all: try reflexivity.
           all: apply nl_lift.
           all: assumption.
      * go. go.
      * go. go.
    + go.
      * go.
      * go.
      * go.
      * go.
    + go. cbn. symmetry. f_equal.
      * f_equal ; assumption.
      * f_equal ; assumption.
      * f_equal ; assumption.
      * f_equal ; assumption.
  - go.
    + go.
      * go.
        -- go.
           ++ go. eapply typing_wf. eassumption.
           ++ go. eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                   try eassumption.
                 --- go.
                     +++ go. go. eapply typing_wf. eassumption.
                     +++ apply conv_refl.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                   try eassumption.
                 --- go.
                     +++ go. go. eapply typing_wf. eassumption.
                     +++ apply conv_refl.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ go.
              ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 +++ refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
        -- go. cbn. f_equal.
           all: apply nl_subst ; try reflexivity.
           all: apply nl_lift ; assumption.
      * instantiate (1 := u2). instantiate (2 := u1). go.
        -- go.
           ++ go.
           ++ go.
           ++ go.
              ** go.
              ** go. cbn. f_equal. assumption.
           ++ go.
              ** go.
              ** go. cbn. f_equal. assumption.
        -- go. cbn. f_equal.
           all: f_equal ; assumption.
      * go.
        -- go.
        -- go. cbn. f_equal. assumption.
      * go.
        -- go.
        -- go. cbn. f_equal. assumption.
    + go.
      * lift_sort. eapply typing_subst ; eassumption.
      * lift_sort. eapply typing_subst ; eassumption.
      * go.
      * go.
    + go. cbn. symmetry. f_equal.
      all: try apply nl_subst.
      all: try assumption.
      all: try reflexivity.
      all: f_equal ; assumption.
  - go.
    + go. go.
      * go.
        -- go. econstructor.
           ++ eapply typing_wf. eassumption.
           ++ go.
        -- go. econstructor.
           ++ eapply typing_wf. eassumption.
           ++ go.
        -- lift_sort. eapply typing_subst ; try eassumption.
           ++ lift_sort.
              eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                try eassumption.
              ** go.
                 --- go. eapply typing_wf. eassumption.
                 --- apply conv_refl.
              ** eapply typing_wf. eassumption.
           ++ cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                 eapply typing_wf. eassumption.
        -- lift_sort. eapply typing_subst ; try eassumption.
           ++ lift_sort.
              eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                try eassumption.
              ** go.
                 --- go. eapply typing_wf. eassumption.
                 --- apply conv_refl.
              ** eapply typing_wf. eassumption.
           ++ cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                 eapply typing_wf. eassumption.
      * go. cbn. f_equal.
        -- apply nl_subst.
           ++ apply nl_lift. assumption.
           ++ reflexivity.
        -- apply nl_subst.
           ++ apply nl_lift. assumption.
           ++ reflexivity.
    + go.
      * go. eapply typing_wf. eassumption.
      * go. eapply typing_wf. eassumption.
      * go.
      * go.
    + go. cbn. symmetry. f_equal ; f_equal ; assumption.
  - go.
    + go.
      * go.
        -- go.
           ++ go. eapply typing_wf. eassumption.
           ++ go. eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                   try eassumption.
                 --- apply IHht7. assumption.
                 --- eapply typing_wf. eassumption.
              ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                   try eassumption.
                 --- apply IHht8. assumption.
                 --- eapply typing_wf. eassumption.
              ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
        -- apply cong_Heq ; try apply conv_refl.
           ++ apply subst_conv. apply lift_conv. go.
           ++ apply subst_conv. apply lift_conv. go.
      * instantiate (2 := v1). instantiate (1 := v2).
        go.
        -- go.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              apply IHht7. assumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              apply IHht8. assumption.
           ++ go.
              ** lift_sort. eapply typing_subst ; try eassumption.
                 apply IHht7. assumption.
              ** apply subst_conv. go.
           ++ go.
              ** lift_sort. eapply typing_subst ; try eassumption.
                 apply IHht8. assumption.
              ** apply subst_conv. go.
        -- apply cong_Heq ; try apply conv_refl.
           ++ apply subst_conv. go.
           ++ apply subst_conv. go.
      * go.
        -- lift_sort. eapply typing_subst ; try eassumption.
           apply IHht7. assumption.
        -- apply subst_conv. go.
      * go.
        -- lift_sort. eapply typing_subst ; try eassumption.
           apply IHht8. assumption.
        -- apply subst_conv. go.
    + go.
      * go.
      * go.
      * go.
      * go.
    + apply conv_sym. apply cong_Heq.
      * apply cong_Sum ; try apply conv_refl. go.
      * apply cong_Pair ; try apply conv_refl. go.
      * apply cong_Sum ; try apply conv_refl. go.
      * apply cong_Pair ; try apply conv_refl. go.
  - go.
    + go.
      * go.
        -- go.
           ++ go. eapply typing_wf. eassumption.
           ++ go. eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                   try eassumption.
                 --- apply IHht6. assumption.
                 --- eapply typing_wf. eassumption.
              ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                   try eassumption.
                 --- apply IHht7. assumption.
                 --- eapply typing_wf. eassumption.
              ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
        -- apply cong_Heq ; try apply conv_refl.
           ++ apply subst_conv. apply lift_conv. go.
           ++ apply subst_conv. apply lift_conv. go.
      * go.
        -- instantiate (2 := p2). instantiate (3 := p1).
           go.
           ++ go.
           ++ go.
           ++ go.
              ** go.
              ** apply cong_Sum ; try apply conv_refl. go.
           ++ go.
              ** go.
              ** apply cong_Sum ; try apply conv_refl. go.
        -- apply cong_Heq ; try apply conv_refl.
           ++ apply cong_Sum ; try apply conv_refl. go.
           ++ apply cong_Sum ; try apply conv_refl. go.
      * go.
        -- go.
        -- apply cong_Sum ; try apply conv_refl. go.
      * go.
        -- go.
        -- apply cong_Sum ; try apply conv_refl. go.
    + go.
      * go.
      * go.
    + apply conv_sym. apply cong_Heq ; try apply conv_refl.
      * apply cong_Pi1 ; try apply conv_refl. go.
      * apply cong_Pi1 ; try apply conv_refl. go.
  - go.
    + go.
      * go.
        -- go.
           ++ go. eapply typing_wf. eassumption.
           ++ go. eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                   try eassumption.
                 --- apply IHht6. assumption.
                 --- eapply typing_wf. eassumption.
              ** cbn. eapply type_ProjT1 with (A4 := lift0 1 A2).
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              ** lift_sort.
                 eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                   try eassumption.
                 --- apply IHht7. assumption.
                 --- eapply typing_wf. eassumption.
              ** cbn. eapply type_ProjT2 with (A3 := lift0 1 A1).
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- lift_sort. eapply typing_lift01 ; try eassumption.
                     go.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; mylia).
                     eapply typing_wf. eassumption.
        -- apply cong_Heq ; try apply conv_refl.
           ++ apply subst_conv. apply lift_conv. go.
           ++ apply subst_conv. apply lift_conv. go.
      * go.
        -- instantiate (2 := p2). instantiate (3 := p1).
           go.
           ++ go.
           ++ go.
           ++ go.
              ** go.
              ** apply cong_Sum ; try apply conv_refl. go.
           ++ go.
              ** go.
              ** apply cong_Sum ; try apply conv_refl. go.
        -- apply cong_Heq ; try apply conv_refl.
           ++ apply cong_Sum ; try apply conv_refl. go.
           ++ apply cong_Sum ; try apply conv_refl. go.
      * go.
        -- go.
        -- apply cong_Sum ; try apply conv_refl. go.
      * go.
        -- go.
        -- apply cong_Sum ; try apply conv_refl. go.
    + go.
      * lift_sort. eapply typing_subst ; try eassumption.
        go.
      * lift_sort. eapply typing_subst ; try eassumption.
        go.
      * go.
      * go.
    + apply conv_sym. apply cong_Heq ; try apply conv_refl.
      * apply cong_subst.
        -- apply cong_Pi1 ; try apply conv_refl. go.
        -- go.
      * apply cong_Pi2 ; try apply conv_refl. go.
      * apply cong_subst.
        -- apply cong_Pi1 ; try apply conv_refl. go.
        -- go.
      * apply cong_Pi2 ; try apply conv_refl. go.
  - go.
  - go.
  - go.
  - go.
    + go.
      * instantiate (1 := v). instantiate (1 := u).
        go.
        -- go.
           ++ go. go.
           ++ go. go.
        -- go. cbn. f_equal ; assumption.
      * go. go.
      * go. go.
    + go. go. eapply typing_wf. eassumption.
    + go. cbn. symmetry. f_equal ; assumption.
  - go.
  - go.
  - go.
    + go.
    + go.
      * go.
      * eapply type_ProjT2 with (A3 := A1) ; eassumption.
    + go. symmetry. cbn. f_equal ; try assumption.
      * f_equal. assumption.
      * f_equal. assumption.
  - go. subst. assumption.
  - go.
  Unshelve. all: auto.
  cbn. mylia.
Defined.

End nltype.

Theorem subj_conv `{Sort_notion : Sorts.notion} :
  forall {Σ Γ t u T U},
    type_glob Σ ->
    t ≡ u ->
    Σ ;;; Γ |-i t : T ->
    Σ ;;; Γ |-i u : U ->
    T ≡ U.
Proof.
  intros Σ Γ t u T U hg hr ht hu. revert Γ T U ht hu.
  induction hr ; intros Γ T U ht hu.
  - eapply uniqueness ; try eassumption.
    eapply nl_type ; try eassumption.
    symmetry. assumption.
  - eapply IHhr.
    + eapply subj_red ; eassumption.
    + assumption.
  - eapply IHhr.
    + eassumption.
    + eapply subj_red ; eassumption.
Qed.
