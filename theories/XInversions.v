(*! Inversion lemmata for ETT *)

From Coq Require Import Bool String List BinPos Compare_dec Lia.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
               XTyping.

Open Scope x_scope.

(* We prove these lemmata in the context of Type in Type
   as they will only be used for examples.
 *)
Existing Instance Sorts.type_in_type.

Notation Ty := (@sSort Sorts.type_in_type tt).

Lemma inversionProd :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-x sProd n A B : T ->
    (Σ ;;; Γ |-x A : Ty) *
    (Σ ;;; Γ ,, A |-x B : Ty) *
    (Σ ;;; Γ |-x Ty ≡ T : Ty).
Proof.
  intros Σ Γ n A B T h.
  dependent induction h.
  - destruct s1, s2.
    split ; [ split | ..] ; try assumption.
    apply eq_reflexivity. econstructor.
  - destruct IHh1 as [[? ?] ?].
    destruct s.
    split ; [ split | ..] ; try assumption.
    eapply eq_transitivity ; eassumption.
Defined.