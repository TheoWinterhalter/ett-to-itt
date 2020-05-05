(* Inversion lemmata *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon Conversion ITyping.
Import ListNotations.

Ltac dosplit :=
  lazymatch goal with
  | |- _ /\ _ => split
  | |- _ * _ => split
  end.

Ltac dosplits :=
  repeat dosplit.

Section Inversions.

Context `{Sort_notion : Sorts.notion}.

Lemma inversionRel :
  forall {Σ Γ n T},
    Σ ;;; Γ |-i sRel n : T ->
    exists isdecl,
      let A := lift0 (S n) (safe_nth Γ (exist _ n isdecl)) in
      A ≡ T.
Proof.
  intros Σ Γ n T h. dependent induction h.
  - exists isdecl. apply conv_refl.
  - destruct IHh1 as [isdecl h].
    exists isdecl. eapply conv_trans ; eassumption.
Defined.

Lemma inversionSort :
  forall {Σ Γ s T},
    Σ ;;; Γ |-i sSort s : T ->
    sSort (Sorts.succ s) ≡ T.
Proof.
  intros Σ Γ s T h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans ; eassumption.
Defined.

Lemma inversionProd :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sProd n A B : T ->
    exists s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (sSort (Sorts.prod_sort s1 s2) ≡ T).
Proof.
  intros Σ Γ n A B T h.
  dependent induction h.
  - exists s1, s2. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as [s1 [s2 [? [? ?]]]].
    exists s1, s2. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionLambda :
  forall {Σ Γ na A B t T},
    Σ ;;; Γ |-i sLambda na A B t : T ->
      exists s1 s2 na',
        (Σ ;;; Γ |-i A : sSort s1) /\
        (Σ ;;; Γ ,, A |-i B : sSort s2) /\
        (Σ ;;; Γ ,, A |-i t : B) /\
        (sProd na' A B ≡ T).
Proof.
  intros Σ Γ na A B t T h.
  dependent induction h.
  - exists s1, s2, n'. dosplits ; try assumption.
    apply conv_eq. cbn. reflexivity.
  - destruct IHh1 as (s1 & s2 & na' & ?). split_hyps.
    exists s1, s2, na'. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionApp :
  forall {Σ Γ t A B u T},
    Σ ;;; Γ |-i sApp t A B u : T ->
    exists s1 s2 n,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (Σ ;;; Γ |-i t : sProd n A B) /\
      (Σ ;;; Γ |-i u : A) /\
      (B{ 0 := u } ≡ T).
Proof.
  intros Σ Γ t A B u T h.
  dependent induction h.
  - exists s1, s2, n. dosplits ; try assumption.
    apply conv_refl.
  - destruct IHh1 as (s1 & s2 & n & ?). split_hyps.
    exists s1, s2, n. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionSum :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sSum n A B : T ->
    exists s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (sSort (Sorts.sum_sort s1 s2) ≡ T).
Proof.
  intros Σ Γ n A B T h.
  dependent induction h.
  - exists s1, s2. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as [s1 [s2 [? [? ?]]]].
    exists s1, s2. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionPair :
  forall {Σ Γ A B u v T},
    Σ ;;; Γ |-i sPair A B u v : T ->
    exists n s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : B{ 0 := u }) /\
      (sSum n A B ≡ T).
Proof.
  intros Σ Γ A B u v T h.
  dependent induction h.
  - exists n, s1, s2. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as (n & s1 & s2 & hh). split_hyps.
    exists n, s1, s2. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionPi1 :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-i sPi1 A B p : T ->
    exists n s1 s2,
      (Σ ;;; Γ |-i p : sSum n A B) /\
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (A ≡ T).
Proof.
  intros Σ Γ A B p T h.
  dependent induction h.
  - exists n, s1, s2. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as [n [s1 [s2 [? [? [? ?]]]]]].
    exists n, s1, s2. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionPi2 :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-i sPi2 A B p : T ->
    exists n s1 s2,
      (Σ ;;; Γ |-i p : sSum n A B) /\
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ ,, A |-i B : sSort s2) /\
      (B{ 0 := sPi1 A B p } ≡ T).
Proof.
  intros Σ Γ A B p T h.
  dependent induction h.
  - exists n, s1, s2. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as [n [s1 [s2 [? [? [? ?]]]]]].
    exists n, s1, s2. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionEq :
  forall {Σ Γ A u v T},
    Σ ;;; Γ |-i sEq A u v : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : A) /\
      (sSort (Sorts.eq_sort s) ≡ T).
Proof.
  intros Σ Γ A u v T h.
  dependent induction h.
  - exists s. dosplits ; try assumption.
    apply conv_refl.
  - destruct IHh1 as [s' [? [? [? ?]]]].
    exists s'. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionRefl :
  forall {Σ Γ A u T},
    Σ ;;; Γ |-i sRefl A u : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (sEq A u u ≡ T).
Proof.
  intros Σ Γ A u T h.
  dependent induction h.
  - exists s. dosplits ; try assumption.
    apply conv_refl.
  - destruct IHh1 as [s' [? [? ?]]].
    exists s'. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionJ :
  forall {Σ Γ A u P w v p T},
    Σ ;;; Γ |-i sJ A u P w v p : T ->
    exists s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : A) /\
      (Σ ;;; Γ ,, A ,, (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2) /\
      (Σ ;;; Γ |-i p : sEq A u v) /\
      (Σ ;;; Γ |-i w : (P {1 := u}){0 := sRefl A u}) /\
      (P{1 := v}{0 := p} ≡ T).
Proof.
  intros Σ Γ A u P w v p T h.
  dependent induction h.
  - exists s1, s2. dosplits ; try assumption.
    apply conv_refl.
  - destruct IHh1 as (s1 & s2 & ?).
    split_hyps.
    exists s1, s2. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionTransport :
  forall {Σ Γ A B p t T},
    Σ ;;; Γ |-i sTransport A B p t : T ->
    exists s,
      (Σ ;;; Γ |-i p : sEq (sSort s) A B) /\
      (Σ ;;; Γ |-i t : A) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (B ≡ T).
Proof.
  intros Σ Γ A B p t T h.
  dependent induction h.
  - exists s. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps.
    exists s'. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeq :
  forall {Σ Γ A B a b T},
    Σ ;;; Γ |-i sHeq A a B b : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i a : A) /\
      (Σ ;;; Γ |-i b : B) /\
      (sSort s ≡ T).
Proof.
  intros Σ Γ A B a b T h.
  dependent induction h.
  - exists s. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps.
    exists s'. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionPack :
  forall {Σ Γ A1 A2 T},
    Σ ;;; Γ |-i sPack A1 A2 : T ->
    exists s,
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (sSort s ≡ T).
Proof.
  intros Σ Γ A1 A2 T h.
  dependent induction h.
  - exists s. dosplits ; try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps.
    exists s'. dosplits ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqToEq :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sHeqToEq p : T ->
    exists A u v s,
     (Σ ;;; Γ |-i p : sHeq A u A v) /\
     (Σ ;;; Γ |-i A : sSort s) /\
     (Σ ;;; Γ |-i u : A) /\
     (Σ ;;; Γ |-i v : A) /\
     (sEq A u v ≡ T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists A, u, v, s. dosplits. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (A' & u & v & s' & ?). split_hyps.
    exists A', u, v, s'. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqRefl :
  forall {Σ Γ A a T},
    Σ ;;; Γ |-i sHeqRefl A a : T ->
    exists s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i a : A) /\
      (sHeq A a A a ≡ T).
Proof.
  intros Σ Γ A a T h.
  dependent induction h.
  - exists s. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps. exists s'.
    dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqSym :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sHeqSym p : T ->
    exists A a B b s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i a : A) /\
      (Σ ;;; Γ |-i b : B) /\
      (Σ ;;; Γ |-i p : sHeq A a B b) /\
      (sHeq B b A a ≡ T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists A, a, B, b, s. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & a & B' & b & s' & ?). split_hyps.
    exists A', a, B', b, s'. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqTrans :
  forall {Σ Γ p q T},
    Σ ;;; Γ |-i sHeqTrans p q : T ->
    exists A a B b C c s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i C : sSort s) /\
      (Σ ;;; Γ |-i a : A) /\
      (Σ ;;; Γ |-i b : B) /\
      (Σ ;;; Γ |-i c : C) /\
      (Σ ;;; Γ |-i p : sHeq A a B b) /\
      (Σ ;;; Γ |-i q : sHeq B b C c) /\
      (sHeq A a C c ≡ T).
Proof.
  intros Σ Γ p q T h.
  dependent induction h.
  - exists A, a, B, b, C, c, s. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & a & B' & b & C & c' & s' & hh). split_hyps.
    exists A', a, B', b, C, c', s'. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqTransport :
  forall {Σ Γ p t T},
    Σ ;;; Γ |-i sHeqTransport p t : T ->
    exists A B s,
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i t : A) /\
      (Σ ;;; Γ |-i p : sEq (sSort s) A B) /\
      (sHeq A t B (sTransport A B p t) ≡ T).
Proof.
  intros Σ Γ p t T h.
  dependent induction h.
  - exists A, B, s. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & B' & s' & ?). split_hyps.
    exists A', B', s'. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongProd :
  forall {Σ Γ B1 B2 pA pB T},
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB : T ->
    exists s z nx ny A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (sHeq (sSort (Sorts.prod_sort s z)) (sProd nx A1 B1)
                 (sSort (Sorts.prod_sort s z)) (sProd ny A2 B2)
          ≡ T).
Proof.
  intros Σ Γ B1 B2 pA pB T h.
  dependent induction h.
  - exists s, z, nx, ny, A1, A2. dosplits. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & A1 & A2 & ?).
    split_hyps.
    exists s', z, nx, ny, A1, A2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongLambda :
  forall {Σ Γ B1 B2 t1 t2 pA pB pt T},
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt : T ->
    exists s z nx ny A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                    ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                    ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ ,, A1 |-i t1 : B1) /\
      (Σ ;;; Γ ,, A2 |-i t2 : B2) /\
      (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                 (sProd ny A2 B2) (sLambda ny A2 B2 t2)
          ≡ T).
Proof.
  intros Σ Γ B1 B2 t1 t2 pA pB pt T h.
  dependent induction h.
  - exists s, z, nx, ny, A1, A2. dosplits. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & A1 & A2 & ?). split_hyps.
    exists s', z, nx, ny, A1, A2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongApp :
  forall {Σ Γ B1 B2 pu pA pB pv T},
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv : T ->
    exists s z nx ny A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) /\
      (Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i u1 : sProd nx A1 B1) /\
      (Σ ;;; Γ |-i u2 : sProd ny A2 B2) /\
      (Σ ;;; Γ |-i v1 : A1) /\
      (Σ ;;; Γ |-i v2 : A2) /\
      (sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                 (B2{0 := v2}) (sApp u2 A2 B2 v2)
          ≡ T).
Proof.
  intros Σ Γ B1 B2 pu pA pB pv T h.
  dependent induction h.
  - exists s, z, nx, ny, A1, A2, u1, u2, v1, v2. dosplits.
    all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & ?).
    split_hyps.
    exists s', z, nx, ny, A1, A2, u1, u2, v1, v2. dosplits.
    all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongSum :
  forall {Σ Γ B1 B2 pA pB T},
    Σ ;;; Γ |-i sCongSum B1 B2 pA pB : T ->
    exists s z nx ny A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (sHeq (sSort (Sorts.sum_sort s z)) (sSum nx A1 B1)
                 (sSort (Sorts.sum_sort s z)) (sSum ny A2 B2)
          ≡ T).
Proof.
  intros Σ Γ B1 B2 pA pB T h.
  dependent induction h.
  - exists s, z, nx, ny, A1, A2. dosplits. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & A1 & A2 & ?).
    split_hyps.
    exists s', z, nx, ny, A1, A2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongPair :
  forall {Σ Γ B1 B2 pA pB pu pv T},
    Σ ;;; Γ |-i sCongPair B1 B2 pA pB pu pv : T ->
    exists s z nx ny A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) /\
      (Σ ;;; Γ |-i pv : sHeq (B1{ 0 := u1 }) v1 (B2{ 0 := u2 }) v2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i u1 : A1) /\
      (Σ ;;; Γ |-i u2 : A2) /\
      (Σ ;;; Γ |-i v1 : B1{ 0 := u1 }) /\
      (Σ ;;; Γ |-i v2 : B2{ 0 := u2 }) /\
      (sHeq (sSum nx A1 B1) (sPair A1 B1 u1 v1)
                 (sSum ny A2 B2) (sPair A2 B2 u2 v2)
          ≡ T).
Proof.
  intros Σ Γ B1 B2 pA pB pu pv T h.
  dependent induction h.
  - exists s, z, nx, ny, A1, A2, u1, u2, v1, v2. dosplits. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & ?).
    split_hyps.
    exists s', z, nx, ny, A1, A2, u1, u2, v1, v2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongPi1 :
  forall {Σ Γ B1 B2 pA pB pp T},
    Σ ;;; Γ |-i sCongPi1 B1 B2 pA pB pp : T ->
    exists s z nx ny A1 A2 p1 p2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i p1 : sSum nx A1 B1) /\
      (Σ ;;; Γ |-i p2 : sSum ny A2 B2) /\
      (sHeq A1 (sPi1 A1 B1 p1) A2 (sPi1 A2 B2 p2) ≡ T).
Proof.
  intros Σ Γ B1 B2 pA pB pp T h.
  dependent induction h.
  - exists s, z, nx, ny, A1, A2, p1, p2. dosplits. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & A1 & A2 & p1 & p2 & ?).
    split_hyps.
    exists s', z, nx, ny, A1, A2, p1, p2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongPi2 :
  forall {Σ Γ B1 B2 pA pB pp T},
    Σ ;;; Γ |-i sCongPi2 B1 B2 pA pB pp : T ->
    exists s z nx ny A1 A2 p1 p2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ ,, (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) /\
      (Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ ,, A1 |-i B1 : sSort z) /\
      (Σ ;;; Γ ,, A2 |-i B2 : sSort z) /\
      (Σ ;;; Γ |-i p1 : sSum nx A1 B1) /\
      (Σ ;;; Γ |-i p2 : sSum ny A2 B2) /\
      (sHeq (B1{ 0 := sPi1 A1 B1 p1}) (sPi2 A1 B1 p1)
                  (B2{ 0 := sPi1 A2 B2 p2}) (sPi2 A2 B2 p2)
          ≡ T).
Proof.
  intros Σ Γ B1 B2 pA pB pp T h.
  dependent induction h.
  - exists s, z, nx, ny, A1, A2, p1, p2. dosplits. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & A1 & A2 & p1 & p2 & ?).
    split_hyps.
    exists s', z, nx, ny, A1, A2, p1, p2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongEq :
  forall {Σ Γ pA pu pv T},
    Σ ;;; Γ |-i sCongEq pA pu pv : T ->
    exists s A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) /\
      (Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ |-i u1 : A1) /\
      (Σ ;;; Γ |-i u2 : A2) /\
      (Σ ;;; Γ |-i v1 : A1) /\
      (Σ ;;; Γ |-i v2 : A2) /\
      (sHeq (sSort (Sorts.eq_sort s)) (sEq A1 u1 v1)
            (sSort (Sorts.eq_sort s)) (sEq A2 u2 v2) ≡ T).
Proof.
  intros Σ Γ pA pu pv T h.
  dependent induction h.
  - exists s, A1, A2, u1, u2, v1, v2.
    dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & u1 & u2 & v1 & v2 & ?). split_hyps.
    exists s', A1, A2, u1, u2, v1, v2.
    dosplits. all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongRefl :
  forall {Σ Γ pA pu T},
    Σ ;;; Γ |-i sCongRefl pA pu : T ->
    exists s A1 A2 u1 u2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) /\
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) /\
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ |-i u1 : A1) /\
      (Σ ;;; Γ |-i u2 : A2) /\
      (sHeq (sEq A1 u1 u1) (sRefl A1 u1)
                 (sEq A2 u2 u2) (sRefl A2 u2)
          ≡ T).
Proof.
  intros Σ Γ pA pu T h.
  dependent induction h.
  - exists s, A1, A2, u1, u2.
    dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & u1 & u2 & ?). split_hyps.
    exists s', A1, A2, u1, u2.
    dosplits. all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionEqToHeq :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sEqToHeq p : T ->
    exists A u v s,
      (Σ ;;; Γ |-i p : sEq A u v) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : A) /\
      (sHeq A u A v ≡ T).
Proof.
  intros Σ Γ p T h. dependent induction h.
  - exists A, u, v, s. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & u & v & s' & ?). split_hyps.
    exists A', u, v, s'.
    dosplits. all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqTypeEq :
  forall {Σ Γ A B p T},
    Σ ;;; Γ |-i sHeqTypeEq A B p : T ->
    exists u v s,
      (Σ ;;; Γ |-i p : sHeq A u B v) /\
      (Σ ;;; Γ |-i A : sSort s) /\
      (Σ ;;; Γ |-i B : sSort s) /\
      (Σ ;;; Γ |-i u : A) /\
      (Σ ;;; Γ |-i v : B) /\
      (sEq (sSort s) A B ≡ T).
Proof.
  intros Σ Γ A B p T h.
  dependent induction h.
  - exists u, v, s. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (u &  v & s' & ?). split_hyps.
    exists u, v, s'. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionProjT1 :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjT1 p : T ->
    exists s A1 A2,
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ |-i p : sPack A1 A2) /\
      (A1 ≡ T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists s, A1, A2. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & ?). split_hyps.
    exists s', A1, A2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionProjT2 :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjT2 p : T ->
    exists s A1 A2,
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ |-i p : sPack A1 A2) /\
      (A2 ≡ T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists s, A1, A2. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & ?). split_hyps.
    exists s', A1, A2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionProjTe :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjTe p : T ->
    exists s A1 A2,
      (Σ ;;; Γ |-i A1 : sSort s) /\
      (Σ ;;; Γ |-i A2 : sSort s) /\
      (Σ ;;; Γ |-i p : sPack A1 A2) /\
      (sHeq A1 (sProjT1 p) A2 (sProjT2 p) ≡ T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists s, A1, A2. dosplits. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & ?). split_hyps.
    exists s', A1, A2. dosplits. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionAx :
  forall {Σ Γ id T},
    Σ ;;; Γ |-i sAx id : T ->
    exists ty,
      (lookup_glob Σ id = Some ty) /\
      (ty ≡ T).
Proof.
  intros Σ Γ id T h.
  dependent induction h.
  - exists ty. split ; try assumption. apply conv_refl.
  - destruct IHh1 as [ty ?]. split_hyps.
    exists ty. split ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

End Inversions.

(* Tactic to apply inversion automatically *)

Ltac ttinv h :=
  let s := fresh "s" in
  let s1 := fresh "s1" in
  let s2 := fresh "s2" in
  let z := fresh "z" in
  let his := fresh "is" in
  let nx := fresh "nx" in
  let ny := fresh "ny" in
  let np := fresh "np" in
  let ne := fresh "ne" in
  let na := fresh "na" in
  let A := fresh "A" in
  let B := fresh "B" in
  let C := fresh "C" in
  let A1 := fresh "A1" in
  let A2 := fresh "A2" in
  let B1 := fresh "B1" in
  let B2 := fresh "B2" in
  let u := fresh "u" in
  let v := fresh "v" in
  let u1 := fresh "u1" in
  let u2 := fresh "u2" in
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  let p1 := fresh "p1" in
  let p2 := fresh "p2" in
  let a := fresh "a" in
  let b := fresh "b" in
  let c := fresh "c" in
  let t := fresh "t" in
  let ty := fresh "ty" in
  let univs := fresh "univs" in
  let decl := fresh "decl" in
  let isdecl := fresh "isdecl" in
  let hh := fresh "h" in
  lazymatch type of h with
  | _ ;;; _ |-i ?term : _ =>
    lazymatch term with
    | sRel _ => destruct (inversionRel h) as [his hh]
    | sSort _ => pose proof (inversionSort h) as hh
    | sProd _ _ _ => destruct (inversionProd h) as (s1 & s2 & hh) ; splits_one hh
    | sLambda _ _ _ _ => destruct (inversionLambda h) as (s1 & s2 & na & hh) ;
                        splits_one hh
    | sApp _ _ _ _ => destruct (inversionApp h) as (s1 & s2 & na & hh) ;
                       splits_one hh
    | sSum _ _ _ => destruct (inversionSum h) as (s1 & s2 & hh) ; splits_one hh
    | sPair _ _ _ _ =>
      destruct (inversionPair h) as (nx & s1 & s2 & hh) ; splits_one hh
    | sPi1 _ _ _ =>
      destruct (inversionPi1 h) as (nx & s1 & s2 & hh) ; splits_one hh
    | sPi2 _ _ _ =>
      destruct (inversionPi2 h) as (nx & s1 & s2 & hh) ; splits_one hh
    | sEq _ _ _ => destruct (inversionEq h) as (s & hh) ; splits_one hh
    | sRefl _ _ => destruct (inversionRefl h) as (s & hh) ; splits_one hh
    | sJ _ _ _ _ _ _ => destruct (inversionJ h) as (s1 & s2 & hh) ;
                       splits_one hh
    | sTransport _ _ _ _ => destruct (inversionTransport h) as (s & hh) ;
                           splits_one hh
    | sHeq _ _ _ _ => destruct (inversionHeq h) as (s & hh) ; splits_one hh
    | sHeqToEq _ => destruct (inversionHeqToEq h) as (A & u & v & s & hh) ;
                   splits_one hh
    | sHeqRefl _ _ => destruct (inversionHeqRefl h) as (s & hh) ; splits_one hh
    | sHeqSym _ => destruct (inversionHeqSym h) as (A & a & B & b & s & hh) ;
                  splits_one hh
    | sHeqTrans _ _ =>
      destruct (inversionHeqTrans h) as (A & a & B & b & C & c & s & hh) ;
      splits_one hh
    | sHeqTransport _ _ =>
      destruct (inversionHeqTransport h) as (A & B & s & hh) ;
      splits_one hh
    | sCongProd _ _ _ _ =>
      destruct (inversionCongProd h) as (s & z & nx & ny & A1 & A2 & hh) ;
      splits_one hh
    | sCongLambda _ _ _ _ _ _ _ =>
      destruct (inversionCongLambda h)
        as (s & z & nx & ny & A1 & A2 & hh) ;
      splits_one hh
    | sCongApp _ _ _ _ _ _ =>
      destruct (inversionCongApp h)
        as (s & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongSum _ _ _ _ =>
      destruct (inversionCongSum h) as (s & z & nx & ny & A1 & A2 & hh) ;
      splits_one hh
    | sCongPair _ _ _ _ _ _ =>
      destruct (inversionCongPair h)
        as (s & z & nx & ny & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongPi1 _ _ _ _ _ =>
      destruct (inversionCongPi1 h)
        as (s & z & nx & ny & A1 & A2 & p1 & p2 & hh) ;
      splits_one hh
    | sCongPi2 _ _ _ _ _ =>
      destruct (inversionCongPi2 h)
        as (s & z & nx & ny & A1 & A2 & p1 & p2 & hh) ;
      splits_one hh
    | sCongEq _ _ _ =>
      destruct (inversionCongEq h) as (s & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongRefl _ _ =>
      destruct (inversionCongRefl h) as (s & A1 & A2 & u1 & u2 & hh) ;
      splits_one hh
    | sEqToHeq _ =>
      destruct (inversionEqToHeq h) as (A & u & v & s & hh) ;
      splits_one hh
    | sHeqTypeEq _ _ _ =>
      destruct (inversionHeqTypeEq h) as (u & v & s & hh) ;
      splits_one hh
    | sPack _ _ => destruct (inversionPack h) as (s & hh) ; splits_one hh
    | sProjT1 _ =>
      destruct (inversionProjT1 h) as (s & A1 & A2 & hh) ; splits_one hh
    | sProjT2 _ =>
      destruct (inversionProjT2 h) as (s & A1 & A2 & hh) ; splits_one hh
    | sProjTe _ =>
      destruct (inversionProjTe h) as (s & A1 & A2 & hh) ; splits_one hh
    | sAx _ => destruct (inversionAx h) as [ty hh] ; splits_one hh
    end
  end.
