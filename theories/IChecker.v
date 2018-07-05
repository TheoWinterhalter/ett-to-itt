(*! Incomplete type checker for the type-in-type version of ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import utils Ast LiftSubst Typing Checker.
From Translation Require Import util Quotes Sorts SAst SLiftSubst SCommon
     ITyping ITypingInversions ITypingLemmata ITypingAdmissible
     SubjectReduction.

(* For efficiency reasons we use type in type for examples. *)
Existing Instance Sorts.type_in_type.

Notation Ty := (sSort tt).

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

(* The checker *)
Fixpoint check (Σ : sglobal_context) Γ t A fuel {struct fuel} : bool :=
  match fuel with
  | 0 => false
  | S fuel =>
    match t, A with
    | sRel n, _ =>
      match Nat.ltb_spec0 n #|Γ| with
      | ReflectT _ isdecl =>
        (checkwf Σ Γ fuel) &&
        (Equality.eq_term A (safe_nth Γ (exist _ n isdecl)))
      | _ => false
      end
    | _,_ => false
    end
  end

with checkwf (Σ : sglobal_context) Γ fuel {struct fuel} : bool :=
  match fuel with
  | 0 => false
  | S fuel =>
    match Γ with
    | [] => true
    | A :: Γ =>
      (* (checkwf Σ Γ fuel) && *) (check Σ Γ A Ty fuel)
    end
  end.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := apply cheating.

Fixpoint check_sound Σ Γ t A fuel :
  type_glob Σ ->
  check Σ Γ t A fuel = true ->
  Σ ;;; Γ |-i t : A

with checkwf_sound Σ Γ fuel :
  type_glob Σ ->
  checkwf Σ Γ fuel = true ->
  wf Σ Γ.
Proof.
  - intros hg h. destruct fuel.
    + cbn in h. inversion h.
    + destruct t ; cbn in h ; try discriminate h.
      { destruct (Nat.ltb_spec0 n #|Γ|) as [isdecl |] ; try discriminate h.
        destruct_andb.
        assert (hw : wf Σ Γ).
        { eapply checkwf_sound ; eassumption. }
        eapply type_conv with (s := tt).
        + eapply type_Rel. eassumption.
        + eapply nl_type ; try eassumption.
          2:{ eapply Equality.eq_term_spec.
              eapply Equality.eq_term_sym.
              eassumption.
          }
          clear H H0. revert n isdecl.
          induction hw.
          * cbn. intros n bot. inversion bot.
          * intros n isdecl.
            destruct n.
            -- cbn. cheat.
            -- cheat.
        + cheat.
      }
  - intros hg h. destruct fuel.
    + cbn in h. inversion h.
    + destruct Γ as [| A Γ] ; cbn in h.
      * constructor.
      * eapply wf_snoc'.
        eapply check_sound ; eassumption.
        Unshelve. assumption.
Defined.