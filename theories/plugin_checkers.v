(* Type checkers for ETT and ITT to be used by the plugin *)

Unset Universe Checking.

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import All.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
ITypingAdmissible DecideConversion XTyping Quotes Translation FundamentalLemma
FinalTranslation FullQuote XTypingLemmata IChecking
XChecking Equality plugin_util.
Import MonadNotation.
Import ListNotations.

Open Scope string_scope.
Open Scope x_scope.

Module I := ITyping.

Open Scope s_scope.

(* First we write an ITT checker that will not generate any obligation.
   It will be proven sound but not complete.
   Since ITT derivations are proof-irrelevant, it needs only return a boolean.

   TODO Actually we could write infer directly.

   TODO The fact that we require the hyp on the type forces us to check
   it anyway when it could be simpler...
 *)
Fixpoint _ittcheck (fuel : nat) (Σ : sglobal_context) (Γ : scontext) (t : sterm)
                  (T : sterm) {struct t} : bool :=
  match t with
  | sRel n =>
    match nth_error Γ n with
    | Some B => isconv fuel (lift0 (S n) B) T
    | None => false
    end
  | sSort _ => isconv fuel Ty T
  | sProd n A B =>
    isconv fuel Ty T &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty
  | sLambda n A B t =>
    _ittcheck fuel Σ (Γ,, A) t B &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty &&
    isconv fuel (sProd n A B) T
  | sApp u A B v =>
    _ittcheck fuel Σ Γ u (sProd nAnon A B) &&
    _ittcheck fuel Σ Γ v A &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty &&
    isconv fuel (B{0 := v}) T
  | sSum n A B =>
    isconv fuel Ty T &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,, A) B Ty
  | sPair A B u v =>
    _ittcheck fuel Σ Γ u A &&
    _ittcheck fuel Σ Γ v (B{0 := u}) &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,,A) B Ty &&
    isconv fuel (sSum nAnon A B) T
  | sPi1 A B p =>
    _ittcheck fuel Σ Γ p (sSum nAnon A B) &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,,A) B Ty &&
    isconv fuel A T
  | sPi2 A B p =>
    _ittcheck fuel Σ Γ p (sSum nAnon A B) &&
    _ittcheck fuel Σ Γ A Ty &&
    _ittcheck fuel Σ (Γ,,A) B Ty &&
    isconv fuel (B{0 := sPi1 A B p}) T
  | sEq A u v =>
    _ittcheck fuel Σ Γ u A &&
    _ittcheck fuel Σ Γ v A &&
    _ittcheck fuel Σ Γ A Ty &&
    isconv fuel Ty T
  | sRefl A u =>
    _ittcheck fuel Σ Γ u A &&
    _ittcheck fuel Σ Γ A Ty &&
    isconv fuel (sEq A u u) T
  | sAx id =>
    match lookup_glob Σ id with
    | Some A => isconv fuel A T
    | None => false
    end
  | _ => false
  end.

Lemma _ittcheck_sound :
  forall fuel Σ Γ t A,
    _ittcheck fuel Σ Γ t A = true ->
    type_glob Σ ->
    I.wf Σ Γ ->
    Σ ;;; Γ |-i A : Ty ->
    Σ ;;; Γ |-i t : A.
Proof.
  intros fuel Σ Γ t A h hg hΓ hA.
  revert fuel Γ A h hΓ hA.
  induction t ; intros fuel Γ A h hΓ hA.
  all: cbn in h.
  all: try discriminate h.
  - revert h. case_eq (nth_error Γ n).
    + intros B eq h.
      eapply I.type_conv.
      * eapply I.type_Rel. assumption.
      * eassumption.
      * eapply isconv_sound. erewrite nth_error_Some_safe_nth with (e := eq).
        eassumption.
    + intros _ bot. discriminate bot.
  - destruct s. eapply I.type_conv.
    + econstructor. assumption.
    + eassumption.
    + cbn. eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    assert (Σ;;; Γ |-i t1 : Ty).
    { eapply IHt1 ; try eassumption.
      econstructor. assumption.
    }
    assert (I.wf Σ (Γ,, t1)).
    { econstructor ; eassumption. }
    eapply I.type_conv.
    + econstructor ; try eassumption.
      eapply IHt2 ; try eassumption.
      econstructor. assumption.
    + eassumption.
    + cbn. eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Lambda' ; try assumption.
      * eapply IHt1 ; try eassumption.
        econstructor. assumption.
      * intro hΓ'. eapply IHt3 ; try eassumption.
        eapply IHt2 ; try eassumption.
        econstructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_App' ; try eassumption.
      * eapply IHt1 ; try eassumption.
        eapply type_Prod'.
        -- eapply IHt2 ; try eassumption.
           constructor. assumption.
        -- intro. eapply IHt3 ; try eassumption.
           constructor. assumption.
      * eapply IHt4 ; try eassumption.
        eapply IHt2 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Sum'.
      * eapply IHt1 ; try eassumption.
        constructor. assumption.
      * intro. eapply IHt2 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + assert (Σ ;;; Γ |-i t1 : Ty).
      { eapply IHt1 ; try eassumption.
        constructor. assumption.
      }
      assert (I.wf Σ (Γ,, t1)).
      { econstructor ; eassumption. }
      eapply type_Pair' ; try assumption.
      * eapply IHt3 ; eassumption.
      * eapply IHt4 ; try eassumption.
        lift_sort. eapply ITypingLemmata.typing_subst ; try eassumption.
        -- eapply IHt2 ; try eassumption.
           constructor. assumption.
        -- eapply IHt3 ; eassumption.
      * eapply IHt2 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + assert (Σ ;;; Γ |-i t1 : Ty).
      { eapply IHt1 ; try eassumption.
        constructor. assumption.
      }
      assert (I.wf Σ (Γ,, t1)).
      { econstructor ; eassumption. }
      eapply type_Pi1' ; try assumption.
      eapply IHt3 ; try eassumption.
      eapply type_Sum' ; try eassumption.
      intro. eapply IHt2 ; try eassumption.
      constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + assert (Σ ;;; Γ |-i t1 : Ty).
      { eapply IHt1 ; try eassumption.
        constructor. assumption.
      }
      assert (I.wf Σ (Γ,, t1)).
      { econstructor ; eassumption. }
      eapply type_Pi2' ; try assumption.
      eapply IHt3 ; try eassumption.
      eapply type_Sum' ; try eassumption.
      intro. eapply IHt2 ; try eassumption.
      constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Eq' ; try assumption.
      * eapply IHt2 ; try eassumption.
        eapply IHt1 ; try eassumption.
        constructor. assumption.
      * eapply IHt3 ; try eassumption.
        eapply IHt1 ; try eassumption.
        constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - repeat destruct_andb.
    eapply I.type_conv.
    + eapply type_Refl' ; try assumption.
      eapply IHt2 ; try eassumption.
      eapply IHt1 ; try eassumption.
      constructor. assumption.
    + eassumption.
    + eapply isconv_sound. eassumption.
  - revert h.
    case_eq (lookup_glob Σ id).
    + intros T eq h.
      eapply I.type_conv.
      * eapply I.type_Ax ; eassumption.
      * eassumption.
      * eapply isconv_sound. eassumption.
    + intros _ bot. discriminate bot.
Qed.

Definition ittcheck (fuel : nat) (Σ : sglobal_context) (Γ : scontext) (t : sterm)
           (T : sterm) : bool :=
  _ittcheck fuel Σ Γ T Ty && _ittcheck fuel Σ Γ t T.

Lemma ittcheck_sound :
  forall fuel Σ Γ t A,
    ittcheck fuel Σ Γ t A = true ->
    type_glob Σ ->
    I.wf Σ Γ ->
    Σ ;;; Γ |-i t : A.
Proof.
  intros fuel Σ Γ t A h hg hw.
  unfold ittcheck in h.
  destruct_andb.
  eapply _ittcheck_sound ; try eassumption.
  eapply _ittcheck_sound ; try eassumption.
  econstructor. assumption.
Qed.

Open Scope list_scope.

Notation "s --> t" := (acons s t) (at level 20).
Notation "[< a ; b ; .. ; c >]" :=
  (a (b (.. (c empty) ..))).
Notation "[< a >]" := (a empty).
Notation "[< >]" := (empty).

(* Notation "[< a --> x ; b --> y ; .. ; c --> z >]" := *)
(*   (acons a x (acons b y .. (acons c z empty) ..)). *)

Existing Instance Sorts.type_in_type.

Notation Ty := (@sSort Sorts.type_in_type tt).

(* Useful lemmata *)
Fixpoint Prods (Γ : scontext) (T : sterm) :=
  match Γ with
  | A :: Γ => Prods Γ (sProd nAnon A T)
  | [] => T
  end.

Lemma lift_rel :
  forall {t k}, (lift 1 (S k) t) {k := sRel 0} = t.
Proof.
  intro t. induction t ; intro k.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  destruct n.
  - cbn. case_eq (k ?= 0) ; intro e ; bprop e.
    + subst. reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn. case_eq (k <=? n) ; intro e ; bprop e.
    + cbn. case_eq (k ?= S (S n)) ; intro e1 ; bprop e1 ; try mylia.
      reflexivity.
    + cbn. case_eq (k ?= S n) ; intro e1 ; bprop e1 ; try mylia.
      * subst. f_equal. mylia.
      * reflexivity.
Defined.

Lemma close_goal_ex :
  forall {Γ t T},
    ∑ t', forall {Σ},
    xtype_glob Σ ->
    wf Σ Γ ->
    Σ ;;; [] |-x t : Prods Γ T ->
    Σ ;;; Γ |-x T : Ty ->
    Σ ;;; Γ |-x t' : T.
Proof.
  intros Γ. induction Γ as [| A Γ].
  - intros t T. eexists. intros Σ hg hw h hT. eassumption.
  - intros t T. destruct (IHΓ t (sProd nAnon A T)) as [t' ht'].
    eexists. intros Σ hg hwA h hT. cbn in h.
    inversion hwA. subst. rename X into hw, X0 into hA.
    destruct s. eapply meta_conv.
    + eapply xtype_App'.
      * assumption.
      * assumption.
      * instantiate (2 := lift0 1 A).
        instantiate (1 := lift 1 1 T).
        instantiate (1 := nAnon).
        change (sProd nAnon (lift0 1 A) (lift 1 1 T))
          with (lift0 1 (sProd nAnon A T)).
        eapply typing_lift01.
        -- assumption.
        -- eapply ht' ; try assumption.
           eapply xtype_Prod' ; try assumption.
           intros _. assumption.
        -- instantiate (1 := tt). assumption.
      * instantiate (1 := sRel 0).
        refine (@type_Rel Sorts.type_in_type _ _ 0 _).
        cbn. mylia.
    + eapply lift_rel.
Defined.

Lemma inversionProds :
  forall {Σ Γ T},
    Σ ;;; [] |-x Prods Γ T : Ty ->
    (wf Σ Γ) *
    (Σ ;;; Γ |-x T : Ty).
Proof.
  intros Σ Γ T h. revert T h.
  induction Γ as [| A Γ] ; intros T h.
  - cbn in h. split.
    + constructor.
    + assumption.
  - cbn in h.
    destruct (IHΓ _ h) as [hw hPi].
    destruct (XInversions.inversionProd hPi) as [[? ?] ?].
    split ; try assumption.
    econstructor ; eassumption.
Defined.

Lemma close_goal_ex' :
  forall {Γ t T}, ∑ t', forall {Σ},
    xtype_glob Σ ->
    Σ ;;; [] |-x t : Prods Γ T ->
    Σ ;;; Γ |-x t' : T.
Proof.
  intros Γ t T. eexists. intros Σ hg ht.
  pose proof (istype_type hg (wf_nil _) ht) as hPi.
  destruct (inversionProds hPi) as [hw hT].
  eapply close_goal_ex ; eassumption.
Defined.

Definition closet Γ t T :=
  let '(t' ; _) := @close_goal_ex' Γ t T in t'.

Definition close_goal :
  forall {Σ Γ t T}
    (hg : xtype_glob Σ)
    (h : Σ ;;; [] |-x t : Prods Γ T),
    Σ ;;; Γ |-x closet Γ t T : T.
Proof.
  intros Σ Γ t T h.
  eapply close_goal_ex'.
  assumption.
Defined.

(*
  For ETT we want to be able to build the derivation constructively
  and we should be able to get a set of obligations from it.

  ettconv generates a list (actually none or one) of obligations
  that are necessary to entail the conversion.

  _ettcheck returns either a list of obligations or an error (None)
*)
Definition ettconv Γ A B ob : option (list sterm) :=
  if eq_term A B
  then ret ob
  else ret (Prods Γ (sEq Ty A B) :: ob).

Fixpoint _ettcheck (Σ : sglobal_context) (Γ : scontext) (t : sterm)
                  (T : sterm) {struct t} : option (list sterm) :=
  match t with
  | sRel n =>
    B <- nth_error Γ n ;;
    ettconv Γ (lift0 (S n) B) T []
  | sSort _ => ettconv Γ Ty T []
  | sProd n A B =>
    ob1 <- _ettcheck Σ Γ A Ty ;;
    ob2 <- _ettcheck Σ (Γ,, A) B Ty ;;
    ettconv Γ Ty T (ob1 ++ ob2)
  | sLambda n A B t =>
    ob1 <- _ettcheck Σ (Γ,, A) t B ;;
    ob2 <- _ettcheck Σ Γ A Ty ;;
    ob3 <- _ettcheck Σ (Γ,, A) B Ty ;;
    ettconv Γ (sProd n A B) T (ob1 ++ ob2 ++ ob3)
  | sApp u A B v =>
    ob1 <- _ettcheck Σ Γ u (sProd nAnon A B) ;;
    ob2 <- _ettcheck Σ Γ v A ;;
    ob3 <- _ettcheck Σ Γ A Ty ;;
    ob4 <- _ettcheck Σ (Γ,, A) B Ty ;;
    ettconv Γ (B{0 := v}) T (ob1 ++ ob2 ++ ob3 ++ ob4)
  (* We do not deal with Σ-types, they can be handled by the global context
     instead, as other inductive types are. *)
  (* | sSum n A B => *)
  (*   ob1 <- _ettcheck Σ Γ A Ty ;; *)
  (*   ob2 <- _ettcheck Σ (Γ,, A) B Ty ;; *)
  (*   ettconv Γ Ty T (ob1 ++ ob2) *)
  (* | sPair A B u v => *)
  (*   ob1 <- _ettcheck Σ Γ u A ;; *)
  (*   ob2 <- _ettcheck Σ Γ v (B{0 := u}) ;; *)
  (*   ob3 <- _ettcheck Σ Γ A Ty ;; *)
  (*   ob4 <- _ettcheck Σ (Γ,,A) B Ty ;; *)
  (*   ettconv Γ (sSum nAnon A B) T (ob1 ++ ob2 ++ ob3 ++ ob4) *)
  (* | sPi1 A B p => *)
  (*   ob1 <- _ettcheck Σ Γ p (sSum nAnon A B) ;; *)
  (*   ob2 <- _ettcheck Σ Γ A Ty ;; *)
  (*   ob3 <- _ettcheck Σ (Γ,,A) B Ty ;; *)
  (*   ettconv Γ A T (ob1 ++ ob2 ++ ob3) *)
  (* | sPi2 A B p => *)
  (*   ob1 <- _ettcheck Σ Γ p (sSum nAnon A B) ;; *)
  (*   ob2 <- _ettcheck Σ Γ A Ty ;; *)
  (*   ob3 <- _ettcheck Σ (Γ,,A) B Ty ;; *)
  (*   ettconv Γ (B{0 := sPi1 A B p}) T (ob1 ++ ob2 ++ ob3) *)
  | sEq A u v =>
    ob1 <- _ettcheck Σ Γ u A ;;
    ob2 <- _ettcheck Σ Γ v A ;;
    ob3 <- _ettcheck Σ Γ A Ty ;;
    ettconv Γ Ty T (ob1 ++ ob2 ++ ob3)
  | sRefl A u =>
    ob1 <- _ettcheck Σ Γ u A ;;
    ob2 <- _ettcheck Σ Γ A Ty ;;
    ettconv Γ (sEq A u u) T (ob1 ++ ob2)
  | sAx id =>
    A <- lookup_glob Σ id ;;
    ettconv Γ A T []
  | _ => None
  end.

Notation "s @ t" := (s ++ t)%string (right associativity, at level 60).

Definition decl := Build_glob_decl.

(* For the soundness lemma, we need to write an extend function that takes
   a global context and a list of obligations and put them together using a
   base name for the obligations.
 *)
Fixpoint extendi i (Σ : sglobal_context) name l : sglobal_context :=
  match l with
  | A :: l =>
    extendi (S i) (decl (name @ string_of_nat i) A :: Σ) name l
  | [] => Σ
  end.

Lemma extendi_cons :
  forall {i Σ name A l},
    extendi i Σ name (A :: l) =
    extendi (S i) (decl (name @ string_of_nat i) A :: Σ) name l.
Proof.
  reflexivity.
Defined.

Lemma extendi_comp :
  forall {i Σ name l},
    extendi i Σ name l =
    rev_mapi i (fun i => decl (name @ string_of_nat i)) l ++ Σ.
Proof.
  intros i Σ name l. revert i Σ.
  induction l as [| A l ih ] ; intros i Σ.
  - reflexivity.
  - rewrite extendi_cons. rewrite ih. rewrite rev_mapi_cons.
    apply app_cons_app.
Defined.

Notation extend := (extendi 0).

Open Scope nat_scope.

Inductive allfresh : sglobal_context -> Type :=
| allfresh_nil : allfresh []
| allfresh_cons Σ d : allfresh Σ -> fresh_glob d.(dname) Σ -> allfresh (d :: Σ).

Derive Signature for allfresh.

Lemma lookup_skip :
  forall {Σ na A l},
    let d := decl na A in
    let Σ' := l ++ d :: Σ in
    allfresh Σ' ->
    lookup_glob Σ' na = Some A.
Proof.
  intros Σ na A l d Σ' hf.
  induction l as [| B l ih ] in Σ, na, A, d, Σ', hf |- *.
  - cbn.
    destruct (ident_eq_spec na na).
    + reflexivity.
    + exfalso. auto.
  - cbn.
    subst Σ'. cbn in hf. dependent destruction hf.
    specialize (ih _ _ _ hf). subst d. rewrite ih.
    erewrite ident_neq_fresh ; try eassumption.
    reflexivity.
Defined.

Lemma lookup_extendi :
  forall {Σ name ob i j},
    let Σ' := extendi i Σ name ob in
    allfresh Σ' ->
    j < #|ob| ->
    lookup_glob Σ' (name @ string_of_nat (i + j)) = nth_error ob j.
Proof.
  intros Σ name ob i j Σ' hf hj.
  revert Σ i j Σ' hf hj. induction ob as [| A ob ih ].
  - intros Σ i j Σ' hf hj. cbn in *. inversion hj.
  - intros Σ i j Σ' hf hj. cbn. destruct j.
    + subst Σ'. rewrite extendi_comp.
      rewrite extendi_comp in hf. rewrite rev_mapi_cons in hf.
      replace (i + 0) with i by mylia.
      match goal with
      | |- lookup_glob (?ob ++ ?d' :: _) ?na' = _ =>
        set (l := ob) in * ;
        set (d := d') in * ;
        set (na := na') in *
      end.
      clear - hf. rewrite <- app_cons_app in hf. cbn.
      eapply lookup_skip. assumption.
    + cbn. replace (i + S j) with (S i + j) by mylia.
      eapply ih.
      * assumption.
      * cbn in hj. mylia.
Defined.

Lemma lookup_extend :
  forall {Σ name A obb obe},
    let Σ' := extend Σ name (obb ++ (A :: obe)) in
    allfresh Σ' ->
    lookup_glob Σ' (name @ string_of_nat #|obb|) = Some A.
Proof.
  intros Σ name A obb obe Σ' hf.
  Opaque length.
  change #|obb| with (0 + #|obb|). subst Σ'.
  erewrite lookup_extendi.
  Transparent length.
  - rewrite nth_error_app2 by reflexivity.
    replace (#|obb| - #|obb|) with 0 by mylia.
    reflexivity.
  - assumption.
  - rewrite app_length. cbn. mylia.
Defined.

Lemma xtype_glob_allfresh :
  forall {Σ},
    xtype_glob Σ ->
    allfresh Σ.
Proof.
  intros Σ h. induction h.
  - constructor.
  - constructor.
    + assumption.
    + assumption.
Defined.

Lemma fresh_glob_skip :
  forall {id Σ Ξ},
    fresh_glob id (Ξ ++ Σ) ->
    fresh_glob id Σ.
Proof.
  intros id Σ Ξ h. revert id Σ h.
  induction Ξ as [| d Ξ ih ] ; intros id Σ h.
  - assumption.
  - eapply ih. dependent destruction h. assumption.
Defined.

Lemma lookup_skip_eq :
  forall {Ξ Σ id A},
    lookup_glob Σ id = Some A ->
    allfresh (Ξ ++ Σ) ->
    lookup_glob (Ξ ++ Σ) id = Some A.
Proof.
  intro Ξ. induction Ξ as [| d Ξ ih ] ; intros Σ id A h hf.
  - cbn. assumption.
  - cbn. dependent destruction hf. apply fresh_glob_skip in f.
    erewrite ih ; try eassumption.
    erewrite ident_neq_fresh ; try eassumption.
    reflexivity.
Defined.

Ltac reset H :=
  let v := (eval unfold H in H) in
  subst H ; set (H := v) in *.

(* Ltac discharge :=
  try (intros ;
  match goal with
  | H : None = Some _ |- _ => discriminate H
  end). *)

Ltac discharge :=
  try (intros ; discriminate).

Ltac rewenv Σ H :=
  match type of H with
  | let _ := ?T in _ =>
    replace T with Σ in H ; [
      idtac
    | unfold Σ ; f_equal ; repeat (cbn ; rewrite <- !app_assoc) ; try reflexivity
    ]
  end.

Lemma _ettcheck_sound :
  forall Σ Γ t A ob name obb obe,
    _ettcheck Σ Γ t A = Some ob ->
    let Σ' := extend Σ name (obb ++ ob ++ obe) in
    xtype_glob Σ' ->
    wf Σ' Γ ->
    Σ' ;;; Γ |-x A : Ty ->
    Σ' ;;; Γ |-x t : A.
Proof with discharge.
  intros Σ Γ t A ob name obb obe h Σ' hg hw hA.
  revert Σ Γ A ob name obb obe h Σ' hg hw hA.
  induction t ; intros Σ Γ A ob name obb obe h Σ' hg hw hA.
  all: try discriminate h.
  - cbn in h. revert h. case_eq (nth_error Γ n).
    + intros B eq.
      unfold ettconv. cbn. case_eq (eq_term (lift0 (S n) B) A).
      * intros eq' h. eapply type_conv.
        -- eapply type_Rel.
        -- eassumption.
        -- erewrite nth_error_Some_safe_nth with (e := eq).
           eapply eq_symmetry. eapply eq_alpha ; try assumption.
           symmetry. eapply eq_term_spec. assumption.
      * intros _ h. apply some_inj in h. subst. cbn in Σ'.
        eapply type_conv.
        -- eapply type_Rel.
        -- eassumption.
        -- erewrite nth_error_Some_safe_nth with (e := eq).
           eapply reflection. eapply close_goal ; try eassumption.
           eapply type_Ax. eapply lookup_extend.
           apply xtype_glob_allfresh. assumption.
    + intros _ bot. discriminate bot.
  - simpl in h. destruct s.
    eapply type_conv.
    + eapply xtype_Sort'.
    + eassumption.
    + unfold ettconv in h. revert h.
      case_eq (eq_term Ty A).
      * intros eq h. eapply eq_alpha.
        -- eapply eq_term_spec. assumption.
        -- constructor.
      * intros _ h. apply some_inj in h. subst. cbn in Σ'.
        eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob1 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob2 eq2 h.
    unfold ettconv in h. revert h. case_eq (eq_term Ty A).
    + intros eq h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name obb (ob2 ++ obe) eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ ob1) obe eq2).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      eapply type_conv.
      * eapply xtype_Prod'.
        -- assumption.
        -- eapply IHt1 ; try assumption. constructor.
        -- intro. eapply IHt2 ; try assumption. constructor.
      * eassumption.
      * eapply eq_alpha.
        -- eapply eq_term_spec. assumption.
        -- constructor.
    + intros _ h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ [Prods Γ (sEq Ty Ty A)]) (ob2 ++ obe) eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ (Prods Γ (sEq Ty Ty A) :: ob1)) obe eq2).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      eapply type_conv.
      * eapply xtype_Prod'.
        -- assumption.
        -- eapply IHt1 ; try assumption. constructor.
        -- intro. eapply IHt2 ; try assumption. constructor.
      * eassumption.
      * eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ (Γ,, t1) t3 t2) ...
    intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ...
    intros ob3 eq2. unfold ettconv. case_eq (eq_term (sProd nx t1 t2) A).
    + intros eq h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ ob1) (ob3 ++ obe) eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) obe eq2).
      specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ obe) eq3).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      rewenv Σ' IHt3.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      specialize (IHt3 hg).
      eapply type_conv.
      * eapply xtype_Lambda'.
        -- assumption.
        -- assumption.
        -- eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- intro. eapply IHt3 ; try assumption.
           eapply IHt2 ; try assumption.
           eapply xtype_Sort'.
      * eassumption.
      * eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
    + intros _ h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ (Prods Γ (sEq Ty (sProd nx t1 t2) A)) :: ob1) (ob3 ++ obe) eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ (Prods Γ (sEq Ty (sProd nx t1 t2) A)) :: ob1 ++ ob2) obe eq2).
      specialize (IHt3 _ _ _ _ name (obb ++ [Prods Γ (sEq Ty (sProd nx t1 t2) A)]) (ob2 ++ ob3 ++ obe) eq3).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      rewenv Σ' IHt3.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      specialize (IHt3 hg).
      eapply type_conv.
      * eapply xtype_Lambda'.
        -- assumption.
        -- assumption.
        -- eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- intro. eapply IHt3 ; try assumption.
           eapply IHt2 ; try assumption.
           eapply xtype_Sort'.
      * eassumption.
      * eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t1 (sProd nAnon t2 t3)) ...
    intros ob1 eq1. case_eq (_ettcheck Σ Γ t4 t2) ...
    intros ob2 eq4. case_eq (_ettcheck Σ Γ t2 Ty) ...
    intros ob3 eq2. case_eq (_ettcheck Σ (Γ,, t2) t3 Ty) ...
    intros ob4 eq3. unfold ettconv.
    match goal with
    | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v)
    end.
    + intros eq h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name obb (ob2 ++ ob3 ++ ob4 ++ obe) eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) (ob4 ++ obe) eq2).
      specialize (IHt3 _ _ _ _ name (obb ++ ob1 ++ ob2 ++ ob3) obe eq3).
      specialize (IHt4 _ _ _ _ name (obb ++ ob1) (ob3 ++ ob4 ++ obe) eq4).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      rewenv Σ' IHt3.
      rewenv Σ' IHt4.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      specialize (IHt3 hg).
      specialize (IHt4 hg).
      eapply type_conv.
      * eapply xtype_App' ; try assumption.
        -- eapply IHt1 ; try assumption.
           eapply xtype_Prod' ; try assumption.
           ** eapply IHt2 ; try assumption.
              eapply xtype_Sort'.
           ** intro. eapply IHt3 ; try assumption.
              eapply xtype_Sort'.
        -- eapply IHt4 ; try assumption.
           eapply IHt2 ; try assumption.
           eapply xtype_Sort'.
      * eassumption.
      * eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
    + match goal with
      | |- context [ Prods ?Γ ?A ] => set (obeq := Prods Γ A)
      end.
      intros _ h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ [obeq]) (ob2 ++ ob3 ++ ob4 ++ obe) eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ obeq :: ob1 ++ ob2) (ob4 ++ obe) eq2).
      specialize (IHt3 _ _ _ _ name (obb ++ obeq :: ob1 ++ ob2 ++ ob3) obe eq3).
      specialize (IHt4 _ _ _ _ name (obb ++ obeq :: ob1) (ob3 ++ ob4 ++ obe) eq4).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      rewenv Σ' IHt3.
      rewenv Σ' IHt4.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      specialize (IHt3 hg).
      specialize (IHt4 hg).
      eapply type_conv.
      * eapply xtype_App' ; try assumption.
        -- eapply IHt1 ; try assumption.
           eapply xtype_Prod' ; try assumption.
           ** eapply IHt2 ; try assumption.
              eapply xtype_Sort'.
           ** intro. eapply IHt3 ; try assumption.
              eapply xtype_Sort'.
        -- eapply IHt4 ; try assumption.
           eapply IHt2 ; try assumption.
           eapply xtype_Sort'.
      * eassumption.
      * eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  (* - simpl in h. revert h. *)
  (*   case_eq (_ettcheck Σ Γ t1 Ty) ... *)
  (*   intros ob1 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ... *)
  (*   intros ob2 eq2. unfold ettconv. *)
  (*   match goal with *)
  (*   | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v) *)
  (*   end. *)
  (*   + intros eq h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name obb (ob2 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ ob1) obe eq2). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply xtype_Sum' ; try assumption. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- intro. eapply IHt2 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply eq_symmetry. eapply eq_alpha. *)
  (*       -- symmetry. eapply eq_term_spec. assumption. *)
  (*       -- assumption. *)
  (*   + match goal with *)
  (*     | |- context [ Prods ?Γ ?A ] => set (obeq := Prods Γ A) *)
  (*     end. *)
  (*     intros _ h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name (obb ++ [obeq]) (ob2 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ obeq :: ob1) obe eq2). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply xtype_Sum' ; try assumption. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- intro. eapply IHt2 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply reflection. eapply close_goal ; try eassumption. *)
  (*       eapply type_Ax. eapply lookup_extend. *)
  (*       apply xtype_glob_allfresh. assumption. *)
  (* - simpl in h. revert h. *)
  (*   case_eq (_ettcheck Σ Γ t3 t1) ... *)
  (*   intros ob1 eq3. case_eq (_ettcheck Σ Γ t4 (t2 {0 := t3})) ... *)
  (*   intros ob2 eq4. case_eq (_ettcheck Σ Γ t1 Ty) ... *)
  (*   intros ob3 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ... *)
  (*   intros ob4 eq2. unfold ettconv. *)
  (*   match goal with *)
  (*   | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v) *)
  (*   end. *)
  (*   + intros eq h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name (obb ++ ob1 ++ ob2) (ob4 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2 ++ ob3) obe eq2). *)
  (*     specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ ob4 ++ obe) eq3). *)
  (*     specialize (IHt4 _ _ _ _ name (obb ++ ob1) (ob3 ++ ob4 ++ obe) eq4). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     rewenv Σ' IHt3. *)
  (*     rewenv Σ' IHt4. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     specialize (IHt3 hg). *)
  (*     specialize (IHt4 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply type_Pair ; try assumption. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt2 ; try assumption. *)
  (*          ++ econstructor ; try assumption. *)
  (*             eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*          ++ eapply xtype_Sort'. *)
  (*       -- eapply IHt3 ; try assumption. *)
  (*          eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt4 ; try assumption. *)
  (*          change Ty with (Ty{0 := t3}). *)
  (*          eapply typing_subst ; try assumption. *)
  (*          ++ eapply IHt2 ; try assumption. *)
  (*             ---- econstructor ; try assumption. *)
  (*                  eapply IHt1 ; try assumption. *)
  (*                  eapply xtype_Sort'. *)
  (*             ---- eapply xtype_Sort'. *)
  (*          ++ eapply IHt3 ; try assumption. *)
  (*             eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply eq_symmetry. eapply eq_alpha. *)
  (*       -- symmetry. eapply eq_term_spec. assumption. *)
  (*       -- assumption. *)
  (*   + match goal with *)
  (*     | |- context [ Prods ?Γ ?A ] => set (obeq := Prods Γ A) *)
  (*     end. *)
  (*     intros _ h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name (obb ++ obeq :: ob1 ++ ob2) (ob4 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ obeq :: ob1 ++ ob2 ++ ob3) obe eq2). *)
  (*     specialize (IHt3 _ _ _ _ name (obb ++ [obeq]) (ob2 ++ ob3 ++ ob4 ++ obe) eq3). *)
  (*     specialize (IHt4 _ _ _ _ name (obb ++ obeq :: ob1) (ob3 ++ ob4 ++ obe) eq4). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     rewenv Σ' IHt3. *)
  (*     rewenv Σ' IHt4. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     specialize (IHt3 hg). *)
  (*     specialize (IHt4 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply type_Pair ; try assumption. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt2 ; try assumption. *)
  (*          ++ econstructor ; try assumption. *)
  (*             eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*          ++ eapply xtype_Sort'. *)
  (*       -- eapply IHt3 ; try assumption. *)
  (*          eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt4 ; try assumption. *)
  (*          change Ty with (Ty{0 := t3}). *)
  (*          eapply typing_subst ; try assumption. *)
  (*          ++ eapply IHt2 ; try assumption. *)
  (*             ---- econstructor ; try assumption. *)
  (*                  eapply IHt1 ; try assumption. *)
  (*                  eapply xtype_Sort'. *)
  (*             ---- eapply xtype_Sort'. *)
  (*          ++ eapply IHt3 ; try assumption. *)
  (*             eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply reflection. eapply close_goal ; try eassumption. *)
  (*       eapply type_Ax. eapply lookup_extend. *)
  (*       apply xtype_glob_allfresh. assumption. *)
  (* - simpl in h. revert h. *)
  (*   case_eq (_ettcheck Σ Γ t3 (sSum nAnon t1 t2)) ... *)
  (*   intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ... *)
  (*   intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ... *)
  (*   intros ob3 eq2. unfold ettconv. *)
  (*   match goal with *)
  (*   | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v) *)
  (*   end. *)
  (*   + intros eq h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name (obb ++ ob1) (ob3 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) obe eq2). *)
  (*     specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ obe) eq3). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     rewenv Σ' IHt3. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     specialize (IHt3 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply type_Pi1 ; try assumption. *)
  (*       -- eapply IHt3 ; try assumption. *)
  (*          eapply xtype_Sum' ; try assumption. *)
  (*          ++ eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*          ++ intro. eapply IHt2 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt2 ; try assumption. *)
  (*          ++ econstructor ; try assumption. *)
  (*          eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*          ++ eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply eq_symmetry. eapply eq_alpha. *)
  (*       -- symmetry. eapply eq_term_spec. assumption. *)
  (*       -- assumption. *)
  (*   + match goal with *)
  (*     | |- context [ Prods ?Γ ?A ] => set (obeq := Prods Γ A) *)
  (*     end. *)
  (*     intros _ h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name (obb ++ obeq :: ob1) (ob3 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ obeq :: ob1 ++ ob2) obe eq2). *)
  (*     specialize (IHt3 _ _ _ _ name (obb ++ [obeq]) (ob2 ++ ob3 ++ obe) eq3). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     rewenv Σ' IHt3. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     specialize (IHt3 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply type_Pi1 ; try assumption. *)
  (*       -- eapply IHt3 ; try assumption. *)
  (*          eapply xtype_Sum' ; try assumption. *)
  (*          ++ eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*          ++ intro. eapply IHt2 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt2 ; try assumption. *)
  (*          ++ econstructor ; try assumption. *)
  (*          eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*          ++ eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply reflection. eapply close_goal ; try eassumption. *)
  (*       eapply type_Ax. eapply lookup_extend. *)
  (*       apply xtype_glob_allfresh. assumption. *)
  (* - simpl in h. revert h. *)
  (*   case_eq (_ettcheck Σ Γ t3 (sSum nAnon t1 t2)) ... *)
  (*   intros ob1 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ... *)
  (*   intros ob2 eq1. case_eq (_ettcheck Σ (Γ,, t1) t2 Ty) ... *)
  (*   intros ob3 eq2. unfold ettconv. *)
  (*   match goal with *)
  (*   | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v) *)
  (*   end. *)
  (*   + intros eq h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name (obb ++ ob1) (ob3 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ ob1 ++ ob2) obe eq2). *)
  (*     specialize (IHt3 _ _ _ _ name obb (ob2 ++ ob3 ++ obe) eq3). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     rewenv Σ' IHt3. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     specialize (IHt3 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply type_Pi2 ; try assumption. *)
  (*       -- eapply IHt3 ; try assumption. *)
  (*          eapply xtype_Sum' ; try assumption. *)
  (*          ++ eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*          ++ intro. eapply IHt2 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt2 ; try assumption. *)
  (*          ++ econstructor ; try assumption. *)
  (*             eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*          ++ eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply eq_symmetry. eapply eq_alpha. *)
  (*       -- symmetry. eapply eq_term_spec. assumption. *)
  (*       -- assumption. *)
  (*   + match goal with *)
  (*     | |- context [ Prods ?Γ ?A ] => set (obeq := Prods Γ A) *)
  (*     end. *)
  (*     intros _ h. cbn in h. apply some_inj in h. subst. *)
  (*     specialize (IHt1 _ _ _ _ name (obb ++ obeq :: ob1) (ob3 ++ obe) eq1). *)
  (*     specialize (IHt2 _ _ _ _ name (obb ++ obeq :: ob1 ++ ob2) obe eq2). *)
  (*     specialize (IHt3 _ _ _ _ name (obb ++ [obeq]) (ob2 ++ ob3 ++ obe) eq3). *)
  (*     rewenv Σ' IHt1. *)
  (*     rewenv Σ' IHt2. *)
  (*     rewenv Σ' IHt3. *)
  (*     specialize (IHt1 hg). *)
  (*     specialize (IHt2 hg). *)
  (*     specialize (IHt3 hg). *)
  (*     eapply type_conv. *)
  (*     * eapply type_Pi2 ; try assumption. *)
  (*       -- eapply IHt3 ; try assumption. *)
  (*          eapply xtype_Sum' ; try assumption. *)
  (*          ++ eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*          ++ intro. eapply IHt2 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*       -- eapply IHt1 ; try assumption. *)
  (*          eapply xtype_Sort'. *)
  (*       -- eapply IHt2 ; try assumption. *)
  (*          ++ econstructor ; try assumption. *)
  (*             eapply IHt1 ; try assumption. *)
  (*             eapply xtype_Sort'. *)
  (*          ++ eapply xtype_Sort'. *)
  (*     * eassumption. *)
  (*     * eapply reflection. eapply close_goal ; try eassumption. *)
  (*       eapply type_Ax. eapply lookup_extend. *)
  (*       apply xtype_glob_allfresh. assumption. *)
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t2 t1) ...
    intros ob1 eq2. case_eq (_ettcheck Σ Γ t3 t1) ...
    intros ob2 eq3. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob3 eq1. unfold ettconv.
    match goal with
    | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v)
    end.
    + intros eq h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ ob1 ++ ob2) obe eq1).
      specialize (IHt2 _ _ _ _ name obb (ob2 ++ ob3 ++ obe) eq2).
      specialize (IHt3 _ _ _ _ name (obb ++ ob1) (ob3 ++ obe) eq3).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      rewenv Σ' IHt3.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      specialize (IHt3 hg).
      eapply type_conv.
      * eapply xtype_Eq' ; try assumption.
        -- eapply IHt2 ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- eapply IHt3 ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
      * eassumption.
      * eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
    + match goal with
      | |- context [ Prods ?Γ ?A ] => set (obeq := Prods Γ A)
      end.
      intros _ h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ obeq :: ob1 ++ ob2) obe eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ [obeq]) (ob2 ++ ob3 ++ obe) eq2).
      specialize (IHt3 _ _ _ _ name (obb ++ obeq :: ob1) (ob3 ++ obe) eq3).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      rewenv Σ' IHt3.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      specialize (IHt3 hg).
      eapply type_conv.
      * eapply xtype_Eq' ; try assumption.
        -- eapply IHt2 ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
        -- eapply IHt3 ; try assumption.
           eapply IHt1 ; try assumption.
           eapply xtype_Sort'.
      * eassumption.
      * eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (_ettcheck Σ Γ t2 t1) ...
    intros ob1 eq2. case_eq (_ettcheck Σ Γ t1 Ty) ...
    intros ob2 eq1. unfold ettconv.
    match goal with
    | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v)
    end.
    + intros eq h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ ob1) obe eq1).
      specialize (IHt2 _ _ _ _ name obb (ob2 ++ obe) eq2).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      eapply type_conv.
      * eapply xtype_Refl' ; try assumption.
        eapply IHt2 ; try assumption.
        eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * eassumption.
      * eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
    + match goal with
      | |- context [ Prods ?Γ ?A ] => set (obeq := Prods Γ A)
      end.
      intros _ h. cbn in h. apply some_inj in h. subst.
      specialize (IHt1 _ _ _ _ name (obb ++ obeq :: ob1) obe eq1).
      specialize (IHt2 _ _ _ _ name (obb ++ [obeq]) (ob2 ++ obe) eq2).
      rewenv Σ' IHt1.
      rewenv Σ' IHt2.
      specialize (IHt1 hg).
      specialize (IHt2 hg).
      eapply type_conv.
      * eapply xtype_Refl' ; try assumption.
        eapply IHt2 ; try assumption.
        eapply IHt1 ; try assumption.
        eapply xtype_Sort'.
      * eassumption.
      * eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  - simpl in h. revert h.
    case_eq (lookup_glob Σ id) ...
    intros B eq. cbn. unfold ettconv.
    match goal with
    | |- context [ eq_term ?u ?v ] => case_eq (eq_term u v)
    end.
    + intros eq' h. cbn in h. apply some_inj in h. subst.
      eapply type_conv.
      * eapply type_Ax. revert Σ' hg hw hA.
        rewrite extendi_comp. intros Σ' hg hw hA.
        match goal with
        | _ := ?x ++ _ |- _ => set (Ξ := x) in *
        end. subst Σ'. erewrite lookup_skip_eq ; try eassumption.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
      * eassumption.
      * eapply eq_symmetry. eapply eq_alpha.
        -- symmetry. eapply eq_term_spec. assumption.
        -- assumption.
    + intros _ h. cbn in h. apply some_inj in h. subst.
      eapply type_conv.
      * eapply type_Ax. revert Σ' hg hw hA.
        rewrite extendi_comp. intros Σ' hg hw hA.
        match goal with
        | _ := ?x ++ _ |- _ => set (Ξ := x) in *
        end. subst Σ'. erewrite lookup_skip_eq ; try eassumption.
        -- reflexivity.
        -- apply xtype_glob_allfresh. assumption.
      * eassumption.
      * eapply reflection. eapply close_goal ; try eassumption.
        eapply type_Ax. subst. eapply lookup_extend.
        apply xtype_glob_allfresh. assumption.
  Unshelve. all: exact nAnon.
Defined.

Definition ettcheck (Σ : sglobal_context) (Γ : scontext) (t : sterm) (T : sterm)
  : option (list sterm) :=
  ob1 <- _ettcheck Σ Γ T Ty ;;
  ob2 <- _ettcheck Σ Γ t T ;;
  ret (ob1 ++ ob2).

Ltac discharge ::=
  try (
    intros ; cbn in * ;
    match goal with
    | H : None = Some _ |- _ => discriminate H
    end
  ).

Lemma ettcheck_sound :
  forall {Σ Γ t A ob name},
    ettcheck Σ Γ t A = Some ob ->
    let Σ' := extend Σ name ob in
    xtype_glob Σ' ->
    wf Σ' Γ ->
    Σ' ;;; Γ |-x t : A.
Proof with discharge.
  intros Σ Γ t A ob name eq Σ' hg hw.
  revert eq. unfold ettcheck.
  case_eq (_ettcheck Σ Γ A Ty) ... intros ob1 eq1.
  case_eq (_ettcheck Σ Γ t A) ... intros ob2 eq2.
  cbn. intro eq. inversion eq. clear eq. subst.
  revert Σ' hw hg.
  replace (ob1 ++ ob2) with (ob1 ++ ob2 ++ [])
    by (refine (eq_trans _ (app_nil_r _ (ob1 ++ ob2))) ; apply app_assoc).
  intros Σ' hw hg.
  eapply _ettcheck_sound ; try assumption.
  reset Σ'.
  revert Σ' hw hg.
  replace (ob1 ++ ob2 ++ []) with ([] ++ ob1 ++ ob2)
    by (refine (eq_sym _) ; refine (eq_trans _ (app_nil_r _ (ob1 ++ ob2))) ; apply app_assoc).
  intros Σ' hw hg.
  eapply _ettcheck_sound ; try assumption.
  reset Σ'. eapply xtype_Sort'.
Defined.

Corollary ettcheck_nil_sound :
  forall {Σ t A ob} name,
    ettcheck Σ [] t A = Some ob ->
    let Σ' := extend Σ name ob in
    xtype_glob Σ' ->
    Σ' ;;; [] |-x t : A.
Proof.
  intros Σ t A ob name eq Σ' hg.
  eapply ettcheck_sound ; try assumption.
  constructor.
Defined.

(* Global context should be typable in ITT and as such
   we only check it ETT under no obligations.
 *)
Fixpoint ettcheck_ctx Σ :=
  match Σ with
  | d :: Σ =>
    match ettcheck Σ [] (dtype d) Ty with
    | Some [] => ettcheck_ctx Σ
    | _ => false
    end
  | [] => true
  end.

Ltac discharge ::=
  try (intros ; discriminate).

Lemma ettcheck_ctx_sound :
  forall {Σ},
    ettcheck_ctx Σ = true ->
    allfresh Σ ->
    xtype_glob Σ.
Proof with discharge.
  intro Σ. induction Σ as [| d Σ ih ] ; intros eq hf.
  - constructor.
  - dependent destruction hf.
    revert eq. unfold ettcheck_ctx.
    case_eq (ettcheck Σ [] (dtype d) Ty) ... intros ob eq.
    destruct ob ... intro h.
    econstructor.
    + eapply ih ; assumption.
    + assumption.
    + change Σ with (extend Σ "foo" []).
      eapply ettcheck_nil_sound.
      * assumption.
      * cbn. eapply ih ; assumption.
Defined.

Fixpoint isxcomp (t : sterm) :=
  match t with
  | sRel n => true
  | sSort s => true
  | sProd _ A B => isxcomp A && isxcomp B
  | sLambda _ A B t => isxcomp A && isxcomp B && isxcomp t
  | sApp u A B v => isxcomp A && isxcomp B && isxcomp u && isxcomp v
  | sSum _ A B => isxcomp A && isxcomp B
  | sPair A B u v => isxcomp A && isxcomp B && isxcomp u && isxcomp v
  | sPi1 A B p => isxcomp A && isxcomp B && isxcomp p
  | sPi2 A B p => isxcomp A && isxcomp B && isxcomp p
  | sEq A u v => isxcomp A && isxcomp u && isxcomp v
  | sRefl A u => isxcomp A && isxcomp u
  | sAx _ => true
  | _ => false
  end.

Lemma isxcomp_sound :
  forall {t},
    isxcomp t = true ->
    Xcomp t.
Proof.
  intro t. induction t ; intro eq.
  all: try discriminate eq.
  all: try solve [constructor].
  all: cbn in eq ; repeat destruct_andb ; econstructor ; easy.
Defined.

Fixpoint ittcheck_ctx fuel Σ :=
  match Σ with
  | d :: Σ =>
    isxcomp (dtype d) && ittcheck fuel Σ [] (dtype d) Ty && ittcheck_ctx fuel Σ
  | [] => true
  end.

Lemma ittcheck_ctx_sound :
  forall {fuel Σ},
    ittcheck_ctx fuel Σ = true ->
    allfresh Σ ->
    type_glob Σ.
Proof with discharge.
  intros fuel Σ. induction Σ as [| d Σ ih ] ; intros eq hf.
  - constructor.
  - dependent destruction hf.
    revert eq. unfold ittcheck_ctx.
    case_eq (isxcomp (dtype d)) ... intro e. cbn.
    case_eq (ittcheck fuel Σ [] (dtype d) Ty) ... cbn.
    intros eq h.
    econstructor.
    + eapply ih ; assumption.
    + assumption.
    + eexists. eapply ittcheck_sound.
      * eassumption.
      * eapply ih ; assumption.
      * constructor.
    + eapply isxcomp_sound. assumption.
Defined.

Fixpoint isfresh id Σ :=
  match Σ with
  | d :: Σ => negb (ident_eq (dname d) id) && isfresh id Σ
  | [] => true
  end.

Lemma isfresh_sound :
  forall {id Σ},
    isfresh id Σ = true ->
    fresh_glob id Σ.
Proof.
  intros id Σ. induction Σ as [| d Σ ih ] ; intro h.
  - constructor.
  - cbn in h. destruct_andb.
    econstructor.
    + eapply ih. assumption.
    + destruct (ident_eq_spec (dname d) id).
      * cbn in *. discriminate.
      * assumption.
Defined.

Fixpoint isallfresh Σ :=
  match Σ with
  | d :: Σ => isfresh (dname d) Σ && isallfresh Σ
  | [] => true
  end.

Lemma isallfresh_sound :
  forall {Σ},
    isallfresh Σ = true ->
    allfresh Σ.
Proof.
  intro Σ. induction Σ as [| d Σ ih ] ; intro h.
  - constructor.
  - cbn in h. destruct_andb.
    econstructor.
    + eapply ih. assumption.
    + eapply isfresh_sound. assumption.
Defined.