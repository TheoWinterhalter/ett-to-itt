From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon Conversion ITyping
               ITypingInversions ITypingLemmata Uniqueness SubjectReduction.
Import ListNotations.

Section Admissible.

Context `{Sort_notion : Sorts.notion}.

Lemma sorts_in_sort :
  forall {Σ Γ s1 s2 s3},
    Σ ;;; Γ |-i sSort s1 : sSort s3 ->
    Σ ;;; Γ |-i sSort s2 : sSort s3 ->
    s1 = s2.
Proof.
  intros Σ Γ s1 s2 s3 h1 h2.
  ttinv h1. ttinv h2.
  pose proof (conv_trans h (conv_sym h0)) as eq.
  pose proof (sort_conv_inv eq).
  apply succ_inj. assumption.
Defined.

(* We state some admissible typing rules *)

Lemma heq_sort :
  forall {Σ Γ s1 s2 A B p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i p : sHeq (sSort s1) A (sSort s1) B.
Proof.
  intros Σ Γ s1 s2 A B p hg h.
  destruct (istype_type hg h) as [? i].
  ttinv i.
  ttinv h1. ttinv h0.
  pose proof (conv_trans h4 (conv_sym h6)) as eq.
  pose proof (sort_conv_inv eq).
  assert (s1 = s2) by (apply succ_inj ; assumption).
  subst.
  assumption.
Defined.

Lemma type_HeqToEq' :
  forall {Σ Γ A u v p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A u A v ->
    Σ ;;; Γ |-i sHeqToEq p : sEq A u v.
Proof.
  intros Σ Γ A u v p hg h.
  destruct (istype_type hg h) as [? i].
  ttinv i.
  eapply type_HeqToEq ; eassumption.
Defined.

Fact sort_heq :
  forall {Σ Γ s1 s2 A B e},
    type_glob Σ ->
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i sHeqToEq e : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s1 s2 A B e hg h.
  destruct (istype_type hg h) as [? hty].
  ttinv hty.
  eapply type_HeqToEq' ; try assumption.
  eapply heq_sort ; eassumption.
Defined.

Corollary sort_heq_ex :
  forall {Σ Γ s1 s2 A B e},
    type_glob Σ ->
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    ∑ p, Σ ;;; Γ |-i p : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s A B e hg h.
  eexists. now eapply sort_heq.
Defined.

Lemma type_HeqRefl' :
  forall {Σ Γ A a},
    type_glob Σ ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i sHeqRefl A a : sHeq A a A a.
Proof.
  intros Σ Γ A a hg h.
  destruct (istype_type hg h).
  eapply type_HeqRefl ; eassumption.
Defined.

Lemma type_HeqSym' :
  forall {Σ Γ A a B b p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i sHeqSym p : sHeq B b A a.
Proof.
  intros Σ Γ A a B b p hg h.
  destruct (istype_type hg h) as [? hty].
  ttinv hty.
  now eapply type_HeqSym.
Defined.

Lemma type_HeqTrans' :
  forall {Σ Γ A a B b C c p q},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i q : sHeq B b C c ->
    Σ ;;; Γ |-i sHeqTrans p q : sHeq A a C c.
Proof.
  intros Σ Γ A a B b C c p q hg h1 h2.
  destruct (istype_type hg h1) as [? i1].
  ttinv i1.
  destruct (istype_type hg h2) as [? i2].
  ttinv i2.
  eapply type_HeqTrans. all: try eassumption.
  eapply type_conv.
  - eassumption.
  - eapply type_Sort. eapply typing_wf ; eassumption.
  - apply (uniqueness hg h7 h).
Defined.

Lemma type_HeqTransport' :
  forall {Σ Γ s A B p t},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i sHeqTransport p t : sHeq A t B (sTransport A B p t).
Proof.
  intros Σ Γ s A B p t hg ht hp.
  destruct (istype_type hg hp) as [? i].
  ttinv i.
  eapply type_HeqTransport ; eassumption.
Defined.

Lemma type_Pair' :
  forall {Σ Γ A B u v n s},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ ,, A |-i B : sSort s ->
    Σ ;;; Γ |-i sPair A B u v : sSum n A B.
Proof.
  intros Σ Γ A B u v n s hg hu hv hB.
  destruct (istype_type hg hu) as [? iu].
  eapply type_Pair ; eassumption.
Defined.

Lemma type_Pi1' :
  forall {Σ Γ p n A B},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sSum n A B ->
    Σ ;;; Γ |-i sPi1 A B p : A.
Proof.
  intros Σ Γ p n A B hg h.
  destruct (istype_type hg h) as [? ip]. ttinv ip.
  eapply type_Pi1 ; eassumption.
Defined.

Lemma type_Pi2' :
  forall {Σ Γ p n A B},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sSum n A B ->
    Σ ;;; Γ |-i sPi2 A B p : B{ 0 := sPi1 A B p }.
Proof.
  intros Σ Γ p n A B hg h.
  destruct (istype_type hg h) as [? ip]. ttinv ip.
  eapply type_Pi2 ; eassumption.
Defined.

Lemma type_CongProd'' :
  forall {Σ Γ s z nx ny A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (Sorts.prod_sort s z)) (sProd nx A1 B1)
         (sSort (Sorts.prod_sort s z)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s z nx ny A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  eapply type_CongProd.
  all: eassumption.
Defined.

Lemma prod_sorts :
  forall {Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    (s1 = s2) * (z1 = z2).
Proof.
  intros Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 pA pB hg hpA hpB.
  split.
  - destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
    eapply sorts_in_sort ; eassumption.
  - destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
    eapply sorts_in_sort ; eassumption.
Defined.

Lemma type_CongProd' :
  forall {Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (Sorts.prod_sort s1 z1)) (sProd nx A1 B1)
         (sSort (Sorts.prod_sort s2 z2)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (prod_sorts hg hpA hpB) as [e1 e2].
  subst. rename z2 into z, s2 into s.
  eapply type_CongProd'' ; eassumption.
Defined.

Lemma type_CongLambda'' :
  forall {Σ Γ s z nx ny A1 A2 B1 B2 t1 t2 pA pB pt},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Proof.
  intros Σ Γ s z nx ny A1 A2 B1 B2 t1 t2 pA pB pt
         hg hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpt) as [? ipt]. ttinv ipt.
  eapply type_CongLambda ; eassumption.
Defined.

Lemma type_CongLambda' :
  forall {Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 t1 t2 pA pB pt},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ ,, A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 t1 t2 pA pB pt hg
         hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct (prod_sorts hg hpA hpB) as [e1 e2].
  subst. rename s2 into s, z2 into z.
  eapply type_CongLambda'' ; eassumption.
Defined.

Lemma type_CongApp'' :
  forall {Σ Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 A2 B2 v2).
Proof.
  intros Σ Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpu) as [? ipu]. ttinv ipu.
  destruct (istype_type hg hpv) as [? ipv]. ttinv ipv.
  eapply type_CongApp ; eassumption.
Defined.

Lemma type_CongApp' :
  forall {Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 A2 B2 v2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (prod_sorts hg hpA hpB).
  subst. rename s2 into s, z2 into z.
  eapply type_CongApp'' ; eassumption.
Defined.

Lemma type_CongSum'' :
  forall {Σ Γ s z nx ny A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongSum B1 B2 pA pB :
    sHeq (sSort (Sorts.sum_sort s z)) (sSum nx A1 B1)
         (sSort (Sorts.sum_sort s z)) (sSum ny A2 B2).
Proof.
  intros Σ Γ s z nx ny A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  eapply type_CongSum.
  all: eassumption.
Defined.

Lemma type_CongSum' :
  forall {Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongSum B1 B2 pA pB :
    sHeq (sSort (Sorts.sum_sort s1 z1)) (sSum nx A1 B1)
         (sSort (Sorts.sum_sort s2 z2)) (sSum ny A2 B2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (prod_sorts hg hpA hpB) as [e1 e2].
  subst. rename z2 into z, s2 into s.
  eapply type_CongSum'' ; eassumption.
Defined.

Lemma type_CongPair'' :
  forall {Σ Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq (B1{ 0 := u1 }) v1 (B2{ 0 := u2 }) v2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongPair B1 B2 pA pB pu pv :
    sHeq (sSum nx A1 B1) (sPair A1 B1 u1 v1)
         (sSum ny A2 B2) (sPair A2 B2 u2 v2).
Proof.
  intros Σ Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpu) as [? ipu]. ttinv ipu.
  destruct (istype_type hg hpv) as [? ipv]. ttinv ipv.
  eapply type_CongPair.
  all: eassumption.
Defined.

Lemma type_CongPair' :
  forall {Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq (B1{ 0 := u1 }) v1 (B2{ 0 := u2 }) v2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongPair B1 B2 pA pB pu pv :
    sHeq (sSum nx A1 B1) (sPair A1 B1 u1 v1)
         (sSum ny A2 B2) (sPair A2 B2 u2 v2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpu) as [? ipu]. ttinv ipu.
  destruct (istype_type hg hpv) as [? ipv]. ttinv ipv.
  destruct (prod_sorts hg hpA hpB) as [e1 e2].
  subst.
  eapply type_CongPair''.
  all: eassumption.
Defined.

Lemma type_CongPi1'' :
  forall {Σ Γ nx ny pA s A1 A2 pB z B1 B2 pp p1 p2},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongPi1 B1 B2 pA pB pp : sHeq A1 (sPi1 A1 B1 p1)
                                              A2 (sPi1 A2 B2 p2).
Proof.
  intros Σ Γ nx ny pA s A1 A2 pB z B1 B2 pp p1 p2 hg hpA hpB hpp hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpp) as [? ipp]. ttinv ipp.
  eapply type_CongPi1 ; eassumption.
Defined.

Lemma type_CongPi1' :
  forall {Σ Γ nx ny pA s1 s2 A1 A2 pB z1 z2 B1 B2 pp p1 p2},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongPi1 B1 B2 pA pB pp : sHeq A1 (sPi1 A1 B1 p1)
                                              A2 (sPi1 A2 B2 p2).
Proof.
  intros Σ Γ nx ny pA s1 s2 A1 A2 pB z1 z2 B1 B2 pp p1 p2 hg hpA hpB hpp hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpp) as [? ipp]. ttinv ipp.
  pose proof (sorts_in_sort h5 h3). subst.
  pose proof (sorts_in_sort h0 h). subst.
  eapply type_CongPi1'' ; eassumption.
Defined.

Lemma type_CongPi2'' :
  forall {Σ Γ nx ny pA s A1 A2 pB z B1 B2 pp p1 p2},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongPi2 B1 B2 pA pB pp :
               sHeq (B1{ 0 := sPi1 A1 B1 p1}) (sPi2 A1 B1 p1)
                    (B2{ 0 := sPi1 A2 B2 p2}) (sPi2 A2 B2 p2).
Proof.
  intros Σ Γ nx ny pA s A1 A2 pB z B1 B2 pp p1 p2 hg hpA hpB hpp hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpp) as [? ipp]. ttinv ipp.
  eapply type_CongPi2 ; eassumption.
Defined.

Lemma type_CongPi2' :
  forall {Σ Γ nx ny pA s1 s2 A1 A2 pB z1 z2 B1 B2 pp p1 p2},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongPi2 B1 B2 pA pB pp :
               sHeq (B1{ 0 := sPi1 A1 B1 p1}) (sPi2 A1 B1 p1)
                    (B2{ 0 := sPi1 A2 B2 p2}) (sPi2 A2 B2 p2).
Proof.
  intros Σ Γ nx ny pA s1 s2 A1 A2 pB z1 z2 B1 B2 pp p1 p2 hg hpA hpB hpp hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. ttinv ipA.
  destruct (istype_type hg hpB) as [? ipB]. ttinv ipB.
  destruct (istype_type hg hpp) as [? ipp]. ttinv ipp.
  pose proof (sorts_in_sort h5 h3). subst.
  pose proof (sorts_in_sort h0 h). subst.
  eapply type_CongPi2'' ; eassumption.
Defined.

Lemma type_CongEq'' :
  forall {Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv :
               sHeq (sSort (Sorts.eq_sort s)) (sEq A1 u1 v1)
                    (sSort (Sorts.eq_sort s)) (sEq A2 u2 v2).
Proof.
  intros Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv hg hpA hpu hpv.
  destruct (istype_type hg hpA) as [? iA]. ttinv iA.
  destruct (istype_type hg hpu) as [? iu]. ttinv iu.
  destruct (istype_type hg hpv) as [? iv]. ttinv iv.
  eapply type_CongEq.
  all: assumption.
Defined.

Lemma type_CongEq' :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv
             : sHeq (sSort (Sorts.eq_sort s1)) (sEq A1 u1 v1)
                    (sSort (Sorts.eq_sort s2)) (sEq A2 u2 v2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv hg hpA hpu hpv.
  destruct (istype_type hg hpA) as [? iA]. ttinv iA.
  destruct (istype_type hg hpu) as [? iu]. ttinv iu.
  destruct (istype_type hg hpv) as [? iv]. ttinv iv.
  pose proof (sorts_in_sort h0 h). subst.
  eapply type_CongEq''.
  all: assumption.
Defined.

Lemma type_CongRefl'' :
  forall {Σ Γ s A1 A2 u1 u2 pA pu},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2).
Proof.
  intros Σ Γ s A1 A2 u1 u2 pA pu hg hpA hpu.
  destruct (istype_type hg hpA) as [? iA]. ttinv iA.
  destruct (istype_type hg hpu) as [? iu]. ttinv iu.
  eapply type_CongRefl.
  all: eassumption.
Defined.

Lemma type_CongRefl' :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 pA pu},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 pA pu hg hpA hpu.
  destruct (istype_type hg hpA) as [? iA]. ttinv iA.
  destruct (istype_type hg hpu) as [? iu]. ttinv iu.
  eapply type_CongRefl'' ; try eassumption.
  eapply heq_sort ; eassumption.
Defined.

Lemma type_EqToHeq' :
  forall {Σ Γ A u v p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i sEqToHeq p : sHeq A u A v.
Proof.
  intros Σ Γ A u v p hg h.
  destruct (istype_type hg h) as [? i]. ttinv i.
  eapply type_EqToHeq ; eassumption.
Defined.

Lemma type_ProjT1' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p : A1.
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i]. ttinv i.
  eapply type_ProjT1 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjT2' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p : A2.
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i]. ttinv i.
  eapply type_ProjT2 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjTe' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p : sHeq A1 (sProjT1 p) A2 (sProjT2 p).
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i]. ttinv i.
  eapply type_ProjTe ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_Refl' :
  forall {Σ Γ A u},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u hg h.
  destruct (istype_type hg h) as [? i].
  eapply type_Refl ; eassumption.
Defined.

Lemma type_Transport' :
  forall {Σ Γ s T1 T2 p t},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sEq (sSort s) T1 T2 ->
    Σ ;;; Γ |-i t : T1 ->
    Σ ;;; Γ |-i sTransport T1 T2 p t : T2.
Proof.
  intros Σ Γ s T1 T2 p t hg hp ht.
  destruct (istype_type hg hp) as [? i]. ttinv i.
  eapply type_Transport ; eassumption.
Defined.

Lemma type_HeqTypeEq' :
  forall {Σ Γ A u B v p s},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i sHeqTypeEq A B p : sEq (sSort s) A B.
Proof.
  intros Σ Γ A u B v p s hg hp hA.
  destruct (istype_type hg hp) as [? i]. ttinv i.
  eapply type_HeqTypeEq ; try eassumption.
  pose proof (uniqueness hg h0 hA).
  eapply type_conv ; try eassumption.
  eapply type_Sort. eapply typing_wf. eassumption.
Defined.

End Admissible.