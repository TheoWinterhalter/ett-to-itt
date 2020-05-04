(* Uniqueness of Typing *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata ContextConversion.
Import ListNotations.

Section Uniqueness.

Context `{Sort_notion : Sorts.notion}.

Ltac unitac h1 h2 :=
  ttinv h1 ; ttinv h2 ;
  eapply conv_trans ; [
    eapply conv_sym ; eassumption
  | idtac
  ].

Lemma uniqueness :
  forall {Σ Γ A B u},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    A ≡ B.
Proof.
  intros Σ Γ A B u hg h1 h2.
  revert Γ A B h1 h2.
  induction u ; intros Γ A B h1 h2.
  all: try unitac h1 h2. all: try assumption.
  - cbn in *. erewrite @safe_nth_irr with (isdecl' := is) in h0. assumption.
  - specialize (IHu1 _ _ _ h0 h5).
    specialize (IHu2 _ _ _ h h3).
    eapply conv_trans. 2: eapply h7.
    pose proof (sort_conv_inv IHu1) as e1.
    pose proof (sort_conv_inv IHu2) as e2.
    subst. apply conv_refl.
  - eapply nl_conv ; try eassumption ; reflexivity.
  - specialize (IHu1 _ _ _ h0 h5).
    specialize (IHu2 _ _ _ h h3).
    eapply conv_trans. 2: eapply h7.
    pose proof (sort_conv_inv IHu1) as e1.
    pose proof (sort_conv_inv IHu2) as e2.
    subst. apply conv_refl.
  - eapply conv_trans ; [| exact h11 ].
    apply cong_Sum ; apply conv_refl.
  - specialize (IHu1 _ _ _ h0 h6).
    pose proof (sort_conv_inv IHu1) as e. subst. assumption.
  - specialize (IHu1 _ _ _ h0 h7).
    pose proof (sort_conv_inv IHu1) as e. subst. assumption.
  - specialize (IHu _ _ _ h0 h7).
    pose proof (heq_conv_inv IHu) as e. split_hyps.
    eapply conv_trans. 2: exact h11.
    apply cong_Eq ; assumption.
  - specialize (IHu _ _ _ h5 h11).
    pose proof (heq_conv_inv IHu) as e. split_hyps.
    eapply conv_trans ; [ | exact h13 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h7 h16).
    specialize (IHu2 _ _ _ h8 h17).
    pose proof (heq_conv_inv IHu1) as e1.
    pose proof (heq_conv_inv IHu2) as e2. split_hyps.
    eapply conv_trans ; [ | exact h19 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h4 h9).
    specialize (IHu2 _ _ _ h3 h8).
    pose proof (eq_conv_inv IHu1) as e1. split_hyps.
    eapply conv_trans ; [| exact h11 ].
    apply cong_Heq ; try assumption.
    + apply conv_refl.
    + apply cong_Transport ; try assumption.
      all: apply conv_refl.
  - specialize (IHu3 _ _ _ h0 h9).
    pose proof (heq_conv_inv IHu3) as e3. split_hyps.
    pose proof (sort_conv_inv H). subst.
    assert (hh : Σ ;;; Γ,, A1 |-i u1 : sSort z0).
    { eapply type_ctxconv ; try eassumption.
      - econstructor ; try eassumption.
        eapply typing_wf. eassumption.
      - constructor.
        + apply ctxconv_refl.
        + apply conv_sym. assumption.
    }
    specialize (IHu1 _ _ _ h5 hh).
    pose proof (sort_conv_inv IHu1). subst.
    eapply conv_trans ; [| exact h15 ].
    apply cong_Heq.
    + apply conv_refl.
    + apply cong_Prod ; try assumption.
      apply conv_refl.
    + apply conv_refl.
    + apply cong_Prod ; try assumption. apply conv_refl.
  - specialize (IHu5 _ _ _ h0 h12).
    pose proof (heq_conv_inv IHu5) as e5. split_hyps.
    pose proof (sort_conv_inv H). subst.
    eapply conv_trans ; [| exact h21 ].
    apply cong_Heq ; try assumption.
    + apply cong_Prod ; try assumption. apply conv_refl.
    + apply cong_Lambda ; try assumption. all: apply conv_refl.
    + apply cong_Prod ; try assumption. apply conv_refl.
    + apply cong_Lambda ; try assumption. all: apply conv_refl.
  - specialize (IHu3 _ _ _ h13 h26).
    specialize (IHu4 _ _ _ h h0).
    specialize (IHu6 _ _ _ h12 h25).
    pose proof (heq_conv_inv IHu3).
    pose proof (heq_conv_inv IHu4).
    pose proof (heq_conv_inv IHu6).
    split_hyps.
    eapply conv_trans ; [| exact h16 ].
    apply cong_Heq ; try assumption.
    + apply substs_conv. assumption.
    + apply cong_App ; try assumption. apply conv_refl.
    + apply substs_conv. assumption.
    + apply cong_App ; try assumption. apply conv_refl.
  - specialize (IHu3 _ _ _ h h0).
    pose proof (heq_conv_inv IHu3) as e3. split_hyps.
    pose proof (sort_conv_inv pi1_). subst.
    assert (hh : Σ ;;; Γ,, A1 |-i u1 : sSort z0).
    { eapply type_ctxconv ; try eassumption.
      - econstructor ; try eassumption.
        eapply typing_wf. eassumption.
      - constructor.
        + apply ctxconv_refl.
        + apply conv_sym. assumption.
    }
    specialize (IHu1 _ _ _ h5 hh).
    pose proof (sort_conv_inv IHu1). subst.
    eapply conv_trans ; [| exact h10 ].
    apply cong_Heq.
    + apply conv_refl.
    + apply cong_Sum ; try assumption.
      apply conv_refl.
    + apply conv_refl.
    + apply cong_Sum ; try assumption. apply conv_refl.
  - specialize IHu3 with (1 := h) (2 := h0).
    specialize IHu5 with (1 := h13) (2 := h26).
    specialize IHu6 with (1 := h12) (2 := h25).
    pose proof (heq_conv_inv IHu3).
    pose proof (heq_conv_inv IHu5).
    pose proof (heq_conv_inv IHu6).
    split_hyps.
    eapply conv_trans ; [| exact h16 ].
    apply cong_Heq.
    + apply cong_Sum ; try apply conv_refl. assumption.
    + apply cong_Pair ; try apply conv_refl ; assumption.
    + apply cong_Sum ; try apply conv_refl. assumption.
    + apply cong_Pair ; try apply conv_refl ; assumption.
  - specialize IHu3 with (1 := h0) (2 := h12).
    specialize IHu5 with (1 := h10) (2 := h20).
    pose proof (heq_conv_inv IHu3).
    pose proof (heq_conv_inv IHu5).
    split_hyps.
    eapply conv_trans ; [| exact h13 ].
    apply cong_Heq ; try assumption.
    + apply cong_Pi1 ; try assumption. apply conv_refl.
    + apply cong_Pi1 ; try assumption. apply conv_refl.
  - specialize IHu3 with (1 := h0) (2 := h12).
    specialize IHu5 with (1 := h10) (2 := h20).
    pose proof (heq_conv_inv IHu3).
    pose proof (heq_conv_inv IHu5).
    split_hyps.
    eapply conv_trans ; [| exact h13 ].
    apply cong_Heq ; try assumption.
    + apply substs_conv.
      apply cong_Pi1 ; try assumption. apply conv_refl.
    + apply cong_Pi2 ; try assumption. apply conv_refl.
    + apply substs_conv.
      apply cong_Pi1 ; try assumption. apply conv_refl.
    + apply cong_Pi2 ; try assumption. apply conv_refl.
  - specialize (IHu1 _ _ _ h0 h12).
    specialize (IHu2 _ _ _ h11 h21).
    specialize (IHu3 _ _ _ h10 h20).
    pose proof (heq_conv_inv IHu1).
    pose proof (heq_conv_inv IHu2).
    pose proof (heq_conv_inv IHu3).
    split_hyps. subst.
    pose proof (sort_conv_inv pi1_1). subst.
    eapply conv_trans ; [| exact h13 ].
    apply cong_Heq ; try apply conv_refl.
    + apply cong_Eq ; assumption.
    + apply cong_Eq ; assumption.
  - specialize (IHu1 _ _ _ h h0).
    specialize (IHu2 _ _ _ h8 h15).
    pose proof (heq_conv_inv IHu1).
    pose proof (heq_conv_inv IHu2).
    split_hyps.
    pose proof (sort_conv_inv pi1_0). subst.
    eapply conv_trans ; [| exact h10 ].
    apply cong_Heq.
    + apply cong_Eq ; assumption.
    + apply cong_Refl ; assumption.
    + apply cong_Eq ; assumption.
    + apply cong_Refl ; assumption.
  - specialize (IHu _ _ _ h h0).
    pose proof (eq_conv_inv IHu). split_hyps.
    eapply conv_trans ; [| exact h8 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h7 h13).
    specialize (IHu3 _ _ _ h0 h8).
    apply conv_sym in IHu1. pose proof (sort_conv_inv IHu1). subst.
    pose proof (heq_conv_inv IHu3). split_hyps.
    eapply conv_trans ; [| exact h9 ].
    apply cong_Eq ; assumption.
  - specialize (IHu1 _ _ _ h h0).
    eapply conv_trans ; [| exact h6 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    apply cong_Heq ; try assumption ; apply conv_refl.
  - rewrite h4 in h0. inversion h0. subst. assumption.
Defined.

End Uniqueness.