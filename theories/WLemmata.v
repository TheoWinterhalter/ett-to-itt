From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util WAst WLiftSubst WTyping WTypingInversions WEquality.

Section Lemmata.

Open Scope w_scope.

Context `{Sort_notion : Sorts.notion}.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-w t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Fixpoint lift_context n Γ : wcontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift n #|Γ| A) :: (lift_context n Γ)
  end.

Lemma lift_context_length :
  forall Γ n, #|lift_context n Γ| = #|Γ|.
Proof.
  intro Γ. induction Γ ; intro m.
  - reflexivity.
  - cbn. f_equal. eapply IHΓ.
Defined.

Fact safe_nth_lift_context :
  forall {Γ Δ : wcontext} {n isdecl isdecl'},
    safe_nth (lift_context #|Γ| Δ) (exist _ n isdecl) =
    lift #|Γ| (#|Δ| - n - 1) (safe_nth Δ (exist _ n isdecl')).
Proof.
  intros Γ Δ. induction Δ.
  - cbn. intros. bang.
  - intro n. destruct n ; intros isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by myomega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact lift_context_ex :
  forall {Δ Ξ : wcontext} {n isdecl isdecl'},
    lift0 (S n) (safe_nth (lift_context #|Δ| Ξ) (exist _ n isdecl)) =
    lift #|Δ| #|Ξ| (lift0 (S n) (safe_nth Ξ (exist _ n isdecl'))).
Proof.
  intros Δ Ξ n isdecl isdecl'.
  erewrite safe_nth_lift_context.
  rewrite <- liftP2 by myomega.
  cbn.
  replace (S (n + (#|Ξ| - n - 1)))%nat with #|Ξ|.
  - reflexivity.
  - revert n isdecl isdecl'. induction Ξ ; intros n isdecl isdecl'.
    + cbn. exfalso. abstract easy.
    + cbn. f_equal.
      destruct n.
      * cbn. myomega.
      * cbn. apply IHΞ.
        -- cbn in *. myomega.
        -- cbn in *. myomega.
Defined.

Definition wapp_context (Γ Γ' : wcontext) : wcontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " :=
  (wapp_context Γ Γ')
    (at level 25, Γ' at next level, left associativity) : w_scope.

Lemma meta_conv :
  forall Σ Γ t A B,
    Σ ;;; Γ |-w t : A ->
    A = B ->
    Σ ;;; Γ |-w t : B.
Proof.
  intros Σ Γ t A B h e.
  destruct e. assumption.
Defined.

Lemma meta_ctx_conv :
  forall Σ Γ Δ t A,
    Σ ;;; Γ |-w t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-w t : A.
Proof.
  intros Σ Γ Δ t A H e.
  destruct e. assumption.
Defined.

Fact cat_nil :
  forall {Γ}, Γ ,,, [] = Γ.
Proof.
  reflexivity.
Defined.

Fact nil_cat :
  forall {Γ}, [] ,,, Γ = Γ.
Proof.
  induction Γ.
  - reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact length_cat :
  forall {A} {Γ Δ : list A}, #|Γ ++ Δ| = (#|Γ| + #|Δ|)%nat.
Proof.
  intros A Γ. induction Γ ; intro Δ.
  - cbn. reflexivity.
  - cbn. f_equal. apply IHΓ.
Defined.

Fact safe_nth_S :
  forall {A n} {a : A} {l isdecl},
    ∑ isdecl',
      safe_nth (a :: l) (exist _ (S n) isdecl) =
      safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intros a l isdecl.
  - cbn. eexists. reflexivity.
  - eexists. cbn. reflexivity.
Defined.

Lemma eq_safe_nth' :
  forall {Γ : wcontext} {n a isdecl isdecl'},
    safe_nth (a :: Γ) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n A isdecl isdecl'.
  - exfalso. abstract easy.
  - destruct n.
    + reflexivity.
    + destruct (@safe_nth_S _ (S n) A (a :: Γ) isdecl')
        as [isecl0 eq].
      rewrite eq.
      destruct (@safe_nth_S _ n a Γ isdecl)
        as [isecl1 eq1].
      rewrite eq1.
      apply IHΓ.
Defined.

Lemma eq_safe_nth :
  forall {Γ : wcontext} {n A isdecl isdecl'},
    safe_nth (Γ ,, A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ n A isdecl isdecl'.
  apply eq_safe_nth'.
Defined.

Fact safe_nth_irr :
  forall {A n} {l : list A} {isdecl isdecl'},
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intro l ; destruct l ; intros isdecl isdecl'.
  all: cbn. all: try bang.
  - reflexivity.
  - eapply IHn.
Defined.

Fact safe_nth_cong_irr :
  forall {A n m} {l : list A} {isdecl isdecl'},
    n = m ->
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ m isdecl').
Proof.
  intros A n m l isdecl isdecl' e.
  revert isdecl isdecl'.
  rewrite e. intros isdecl isdecl'.
  apply safe_nth_irr.
Defined.

Fact safe_nth_ge :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n - #|Δ| < #|Γ| },
    n >= #|Δ| ->
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) isdecl').
Proof.
  intros Γ Δ.
  induction Δ ; intros n isdecl isdecl' h.
  - cbn in *. revert isdecl'.
    replace (n - 0) with n by myomega.
    intros isdecl'. apply safe_nth_irr.
  - destruct n.
    + cbn in *. inversion h.
    + cbn. apply IHΔ. cbn in *. myomega.
Defined.

Definition ge_sub {Γ Δ n} (isdecl : n < #|Γ ,,, Δ|) :
  n >= #|Δ| ->  n - #|Δ| < #|Γ|.
Proof.
  intro h.
  rewrite length_cat in isdecl. myomega.
Defined.

Fact safe_nth_ge' :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } (h : n >= #|Δ|),
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) (ge_sub isdecl h)).
Proof.
  intros Γ Δ n isdecl h.
  eapply safe_nth_ge. assumption.
Defined.

Fact safe_nth_lt :
  forall {n Γ Δ} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n < #|Δ| },
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Δ (exist _ n isdecl').
Proof.
  intros n. induction n ; intros Γ Δ isdecl isdecl'.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. reflexivity.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. eapply IHn.
Defined.

Fact ident_neq_fresh :
  forall {Σ id d d'},
    lookup_glob Σ id = Some d' ->
    fresh_glob (dname d) Σ ->
    ident_eq id (dname d) = false.
Proof.
  intro Σ. induction Σ ; intros id d d' h hf.
  - cbn in h. discriminate h.
  - cbn in h. dependent destruction hf.
    case_eq (ident_eq id (dname d0)) ;
    intro e ; rewrite e in h.
    + inversion h as [ h' ]. subst. clear h.
      destruct (ident_eq_spec id (dname d)).
      * subst. destruct (ident_eq_spec (dname d) (dname d')).
        -- exfalso. easy.
        -- easy.
      * reflexivity.
    + eapply IHΣ; eassumption.
Defined.

Fixpoint weak_glob_type {Σ Γ t A} (h : Σ ;;; Γ |-w t : A) :
  forall {d},
    fresh_glob (dname d) Σ ->
    (d::Σ) ;;; Γ |-w t : A

with weak_glob_wf {Σ Γ} (h : wf Σ Γ) :
  forall {d},
    fresh_glob (dname d) Σ ->
    wf (d::Σ) Γ.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intros d' fd'.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                eassumption
               ).
      + eapply type_Ax.
        * eapply weak_glob_wf ; eassumption.
        * cbn. erewrite ident_neq_fresh by eassumption.
          assumption.
      + eapply type_Delta.
        * eapply weak_glob_wf ; eassumption.
        * cbn. erewrite ident_neq_fresh by eassumption.
          assumption.
    }

  (* weak_glob_wf *)
  - { dependent destruction h ; intros fd.
      - constructor.
      - econstructor.
        + apply weak_glob_wf ; assumption.
        + apply weak_glob_type ; eassumption.
    }
Defined.

Corollary weak_glob_isType :
  forall {Σ Γ A} (h : isType Σ Γ A) {d},
    fresh_glob (dname d) Σ ->
    isType (d::Σ) Γ A.
Proof.
  intros Σ Γ A h d hf.
  destruct h as [s h].
  exists s. eapply weak_glob_type ; eassumption.
Defined.

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-w t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat erewrite_assumption ; reflexivity).
  unfold closed_above. case_eq (n <? #|Γ|) ; intro e ; bprop e ; try myomega.
  reflexivity.
Defined.

Fact typed_ax_body :
  forall {Σ}, type_glob Σ ->
  forall {id d},
    lookup_glob Σ id = Some d ->
    Σ ;;; [] |-w dbody d : dtype d.
Proof.
  intros Σ hg. dependent induction hg ; intros id d' h.
  - cbn in h. discriminate h.
  - cbn in h.
    case_eq (ident_eq id (dname d)).
    + intro e. rewrite e in h. inversion h. subst.
      eapply weak_glob_type ; eassumption.
    + intro e. rewrite e in h.
      specialize (IHhg _ _ h).
      eapply weak_glob_type ; eassumption.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-w t : T ->
    closed t.
Proof.
  intros Σ t T h.
  eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

Fact isType_ctxempty_closed : forall {Σ T}, isType Σ [] T -> closed T.
Proof.
  intros Σ T h. destruct h.
  eapply type_ctxempty_closed; eassumption.
Defined.

Lemma isType_lookup_glob {Σ}
  : type_glob Σ -> forall id d, lookup_glob Σ id = Some d -> isType Σ [] (dtype d).
Proof.
  intros wΣ. induction wΣ.
  - intros id d H; inversion H.
  - cbn; intros id d0. case_eq (ident_eq id (dname d)).
    + intros _ e; inversion e; subst.
      eapply weak_glob_isType; eassumption.
    + intros _ H. eapply weak_glob_isType.
      eapply IHwΣ; eassumption. assumption.
Defined.

(* Lemma closed_above_lookup_glob {Σ} *)
(*   : type_glob Σ -> forall id d, lookup_glob Σ id = Some d -> closed (dtype d). *)
(* Proof. *)
(*   intros wΣ. induction wΣ. *)
(*   - intros id d H; inversion H. *)
(*   - cbn; intros id d0. case_eq (ident_eq id (dname d)). *)
(*     intros _ e; inversion e; subst; assumption. *)
(*     intros _ H. eapply IHwΣ. eassumption. *)
(* Defined. *)

Lemma closed_above_safe_nth:
  forall (Σ : wglobal_context) (Γ : wcontext),
    wf Σ Γ -> forall (n : nat) (isdecl : n < #|Γ|), closed_above #|Γ|
      (lift0 (S n) (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))) = true.
Proof.
  intros Σ Γ H. induction H.
  - cbn; intros n isdecl. bang.
  - intros [] isdecl.
    + cbn.
      change (S #|Γ|) with (1+ #|Γ|)%nat.
      erewrite closed_above_lift by omega.
      now eapply type_ctx_closed_above.
    + cbn in *. specialize (IHwf n (lt_S_n _ _ isdecl)).
      erewrite <- (closed_above_lift (n := 1) (k := 0)) in IHwf by omega.
      rewrite liftP3 in IHwf by omega.
      erewrite safe_nth_irr; eassumption.
Defined.


Ltac tcca :=
  match goal with
  | |- _ && _ = _ => apply andb_true_intro; split
  | |- closed_above _ (_ {_ := _}) = _ =>
    eapply closed_above_subst; [omega|cbn|cbn]
  | _ => reflexivity
  | _ => eassumption
  | H : _ ;;; _ |-w ?A : _ |- closed_above _ ?A = _ =>
    eapply type_ctx_closed_above in H
  | H : forall _ _, _ -> _ -> closed_above _ ?A = _ |- closed_above _ ?A = _ =>
    eapply H;[|eassumption]; omega
  | H0 : nl ?t = nl ?A , H : forall _ _ _, closed_above _ ?t = _ -> _ |- closed_above _ ?A = _ =>
    eapply (H _ H0); try eassumption
  | H : _ && _ = _ |- _ => apply andb_prop in H; destruct H
  | _ => rewrite Nat.sub_0_r
  | H : None = Some _ |- _ => inversion H
  end.

Fact closed_above_nk t : forall n k, n <= k ->
  closed_above n t = true -> closed_above k t = true.
Proof.
  induction t; intros; cbn -[leb] in *; repeat tcca.
  apply leb_complete in H0.
  apply leb_correct.
  omega.
Defined.

Fact closed_above_nl t : forall u, nl t = nl u -> forall n,
      closed_above n t = true -> closed_above n u = true.
Proof.
  induction t; cbn -[leb] in *; intros [] e k IH; inversion e;
    cbn -[leb]; repeat tcca.
  subst; assumption.
Qed.

Fact type_ctx_closed_above' :
  forall {Σ Γ t T},
    type_glob Σ ->
    Σ ;;; Γ |-w t : T ->
    closed_above #|Γ| T = true.
Proof.
  intros Σ Γ t T wΣ h.
  induction h; cbn in *; try repeat tcca.
  - eapply closed_above_safe_nth; eassumption.
  - eapply closed_above_nk with (n := 0). omega.
    eapply isType_ctxempty_closed, isType_lookup_glob; eassumption.
  - eapply closed_above_nk with (n := 0). omega.
    eapply isType_ctxempty_closed, isType_lookup_glob; eassumption.
  - eapply closed_above_nk with (n := 0). omega.
    eapply type_ctxempty_closed.
    eapply typed_ax_body. eassumption. eassumption.
  - eapply closed_above_nl; eassumption.
Qed.

Fact type_ctxempty_closed' :
  forall {Σ t T},
    type_glob Σ ->
    Σ ;;; [] |-w t : T ->
    closed T.
Proof.
  intros Σ t T wΣ h.
  eapply @type_ctx_closed_above' with (Γ := []); eassumption.
Defined.




Fact lift_ax_type :
  forall {Σ},
    type_glob Σ ->
    forall {id d},
      lookup_glob Σ id = Some d ->
      forall n k, lift n k (dtype d) = dtype d.
Proof.
  intros Σ hg id ty isd n k.
  eapply closed_lift.
  eapply type_ctxempty_closed'. eassumption. eapply type_Ax.
  constructor. eassumption.
Defined.

Fact lift_ax_body :
  forall {Σ},
    type_glob Σ ->
    forall {id d},
      lookup_glob Σ id = Some d ->
      forall n k, lift n k (dbody d) = dbody d.
Proof.
  intros Σ hg id ty isd n k.
  eapply closed_lift.
  eapply type_ctxempty_closed. eapply typed_ax_body; eassumption.
Defined.

Ltac ih h :=
  lazymatch goal with
  | [ type_lift :
        forall (Σ : wglobal_context) (Γ Δ Ξ : wcontext) (t A : wterm),
          Σ;;; Γ ,,, Ξ |-w t : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-w lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-w ?t : _ |- _ ;;; _ |-w lift _ _ ?t : _ => ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-w t : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-w lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with wf_lift {Σ Γ Δ Ξ} (h : wf Σ (Γ ,,, Ξ)) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  wf Σ (Γ ,,, Δ ,,, lift_context #|Δ| Ξ)
.
Proof.
  - { dependent destruction h ; intros hΣ hwf.
      - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e.
        + rewrite liftP3 by myomega.
          replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by myomega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_lift ; assumption.
          * f_equal. f_equal.
            erewrite 3!safe_nth_ge'
              by (try rewrite lift_context_length ; myomega).
            eapply safe_nth_cong_irr.
            rewrite lift_context_length. myomega.
        + eapply meta_conv.
          * eapply type_Rel. eapply wf_lift ; assumption.
          * erewrite 2!safe_nth_lt.
            eapply lift_context_ex.
      - cbn. apply type_Sort. now apply wf_lift.
      - cbn. eapply type_Prod ; eih.
      - cbn. eapply type_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1.
        eapply type_App with (A := lift #|Δ| #|Ξ| A0) ; eih.
      - cbn. eapply type_Sum ; eih.
      - cbn. eapply type_Pair ; eih.
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1. reflexivity.
      - cbn. eapply type_Pi1 ; eih.
      - cbn.
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1. cbn.
        eapply type_Pi2 ; eih.
      - cbn. apply type_Eq ; eih.
      - cbn. eapply type_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by myomega.
        rewrite substP1.
        cbn. eapply type_J ; try eih.
        + cbn. unfold snoc. cbn.
          f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by myomega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by myomega.
          change (wRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (wRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply type_Transport ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        change (lift #|Δ| #|Ξ| (t0 {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t0 { 0 := u })).
        rewrite 2!substP1.
        eapply type_Beta ; eih.
      - cbn. eapply type_K ; eih.
      - cbn. eapply type_Funext ; eih.
        cbn. f_equal. f_equal.
        + f_equal. replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
        + f_equal. replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
      - cbn. change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by myomega.
        rewrite substP1.
        eapply type_JBeta ; eih.
        + cbn. unfold snoc. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by myomega.
            apply liftP2. myomega.
        + cbn. replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by myomega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by myomega.
          change (wRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (wRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply type_TransportBeta ; eih.
      - cbn. eapply type_PairEta ; eih.
      - cbn. eapply type_ProdExt ; eih.
      - cbn. eapply type_SumExt ; eih.
      - cbn. erewrite lift_ax_type by eassumption.
        eapply type_Ax.
        + now apply wf_lift.
        + assumption.
      - cbn. erewrite lift_ax_type, lift_ax_body by eassumption.
        eapply type_Delta.
        + now apply wf_lift.
        + assumption.
      - eapply type_rename.
        + eih.
        + eapply nl_lift. assumption.
    }

  (* wf_lift *)
  - { intros hg hwf.
      destruct Ξ.
      - cbn. assumption.
      - dependent destruction h.
        cbn. econstructor.
        + apply wf_lift ; assumption.
        + instantiate (1 := s). cbn. change (wSort s) with (lift #|Δ| #|Ξ| (wSort s)).
          apply type_lift ; assumption.
    }

    Unshelve.
    all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
      try rewrite lift_context_length ; myomega.
Defined.

Corollary typing_lift01 :
  forall {Σ Γ t A B s},
    type_glob Σ ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w B : wSort s ->
    Σ ;;; Γ ,, B |-w lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A B s hg ht hB.
  apply (@type_lift _ _ [ B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

Corollary typing_lift02 :
  forall {Σ Γ t A B s C s'},
    type_glob Σ ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w B : wSort s ->
    Σ ;;; Γ ,, B |-w C : wSort s' ->
    Σ ;;; Γ ,, B ,, C |-w lift0 2 t : lift0 2 A.
Proof.
  intros Σ Γ t A B s C s' hg ht hB hC.
  assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift01.
  - assumption.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Corollary typing_lift03 :
  forall {Σ Γ t A B s C s' D s''},
    type_glob Σ ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w B : wSort s ->
    Σ ;;; Γ ,, B |-w C : wSort s' ->
    Σ ;;; Γ ,, B ,, C |-w D : wSort s'' ->
    Σ ;;; Γ ,, B ,, C ,, D |-w lift0 3 t : lift0 3 A.
Proof.
  intros Σ Γ t A B s C s' D s'' hg ht hB hC.
  assert (eq : forall t, lift0 3 t = lift0 2 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift02.
  - assumption.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Corollary typing_lift04 :
  forall {Σ Γ t A B s C s' D s'' E s'''},
    type_glob Σ ->
    Σ ;;; Γ |-w t : A ->
    Σ ;;; Γ |-w B : wSort s ->
    Σ ;;; Γ ,, B |-w C : wSort s' ->
    Σ ;;; Γ ,, B ,, C |-w D : wSort s'' ->
    Σ ;;; Γ ,, B ,, C ,, D |-w E : wSort s''' ->
    Σ ;;; Γ ,, B ,, C ,, D ,, E |-w lift0 4 t : lift0 4 A.
Proof.
  intros Σ Γ t A B s C s' D s'' E s''' hg ht hB hC.
  assert (eq : forall t, lift0 4 t = lift0 2 (lift0 2 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift02.
  - assumption.
  - eapply typing_lift02  ; eassumption.
Defined.


Fact subst_ax_type :
  forall {Σ},
    type_glob Σ ->
    forall {id d},
      lookup_glob Σ id = Some d ->
      forall n u, (dtype d){ n := u } = dtype d.
Proof.
  intros Σ hg id d isd n k.
  eapply closed_subst.
  eapply type_ctxempty_closed'. eassumption. eapply type_Ax.
  constructor. eassumption.
Defined.

Fact subst_ax_body :
  forall {Σ},
    type_glob Σ ->
    forall {id d},
      lookup_glob Σ id = Some d ->
      forall n u, (dbody d){ n := u } = dbody d.
Proof.
  intros Σ hg id d isd n k.
  eapply closed_subst.
  eapply type_ctxempty_closed. eapply typed_ax_body; eassumption.
Defined.

(* Substitution in context *)

Fixpoint subst_context u Δ :=
  match Δ with
  | nil => nil
  | A :: Δ => (A{ #|Δ| := u }) :: (subst_context u Δ)
  end.

Fact subst_context_length :
  forall {u Ξ}, #|subst_context u Ξ| = #|Ξ|.
Proof.
  intros u Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_subst_context :
  forall {Δ : wcontext} {n u isdecl isdecl'},
    (safe_nth (subst_context u Δ) (exist _ n isdecl)) =
    (safe_nth Δ (exist _ n isdecl')) { #|Δ| - S n := u }.
Proof.
  intro Δ. induction Δ.
  - cbn. intros. bang.
  - intro n. destruct n ; intros u isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by myomega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Ltac sh h :=
  lazymatch goal with
  | [ type_subst :
        forall (Σ : wglobal_context) (Γ : list wterm) (Δ : wcontext) (t A : wterm)
          (B u : wterm),
          Σ;;; Γ,, B ,,, Δ |-w t : A ->
          type_glob Σ ->
          Σ;;; Γ |-w u : B ->
          Σ;;; Γ ,,, subst_context u Δ |-w
          t {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, ?B' ,,, ?Δ' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d',, ?d'' |-w _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-w ?t : _ |- _ ;;; _ |-w ?t{ _ := _ } : _ => sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A B u}
  (h : Σ ;;; Γ ,, B ,,, Δ |-w t : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-w u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-w t{ #|Δ| := u } : A{ #|Δ| := u }

with wf_subst {Σ Γ Δ B u}
  (h : wf Σ (Γ ,, B ,,, Δ)) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-w u : B ->
  wf Σ (Γ ,,, subst_context u Δ)
.
Proof.
  (* type_subst *)
  - { intros hg hu.
      dependent destruction h.
      - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
        + assert (h : n >= #|Δ|) by myomega.
          rewrite safe_nth_ge' with (h0 := h).
          assert (n - #|Δ| = 0) by myomega.
          set (ge := ge_sub isdecl h).
          generalize ge.
          rewrite H0. intro ge'.
          cbn. rewrite substP3 by myomega.
          subst.
          replace #|Δ| with #|subst_context u Δ|
            by (now rewrite subst_context_length).
          eapply @type_lift with (Ξ := []) (Δ := subst_context u Δ).
          * cbn. assumption.
          * assumption.
          * eapply wf_subst ; eassumption.
        + assert (h : n >= #|Δ|) by myomega.
          rewrite safe_nth_ge' with (h0 := h).
          set (ge := ge_sub isdecl h).
          destruct n ; try easy.
          rewrite substP3 by myomega.
          generalize ge.
          replace (S n - #|Δ|) with (S (n - #|Δ|)) by myomega.
          cbn. intro ge'.
          eapply meta_conv.
          * eapply type_Rel. eapply wf_subst ; eassumption.
          * erewrite safe_nth_ge'.
            f_equal. eapply safe_nth_cong_irr.
            rewrite subst_context_length. reflexivity.
        + assert (h : n < #|Δ|) by myomega.
          rewrite @safe_nth_lt with (isdecl' := h).
          match goal with
          | |- _ ;;; _ |-w _ : ?t{?d := ?u} =>
            replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
              by (f_equal ; myomega)
          end.
          rewrite substP2 by myomega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_subst ; eassumption.
          * f_equal.
            erewrite safe_nth_lt.
            eapply safe_nth_subst_context.
      - cbn. apply type_Sort. eapply wf_subst ; eassumption.
      - cbn. eapply type_Prod ; esh.
      - cbn. eapply type_Lambda ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite substP4. cbn.
        eapply type_App ; esh.
      - cbn. eapply type_Sum ; esh.
      - cbn. eapply type_Pair ; esh.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. reflexivity.
      - cbn. eapply type_Pi1 ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply type_Pi2 ; esh.
      - cbn. eapply type_Eq ; esh.
      - cbn. eapply type_Refl ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by myomega.
        rewrite substP4.
        eapply type_J ; esh.
        + cbn. unfold snoc. cbn.
          f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
            apply substP2. myomega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
            apply substP2. myomega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by myomega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by myomega.
          change (wRefl (A0 {0 + #|Δ| := u}) (u0 {0 + #|Δ| := u}))
            with ((wRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply type_Transport ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        change ((t0 {0 := u0}) {#|Δ| := u})
          with ((t0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite 2!substP4. cbn.
        eapply type_Beta ; esh.
      - cbn. eapply type_K ; esh.
      - cbn. eapply type_Funext ; esh.
        cbn. f_equal. f_equal.
        + f_equal. replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
          apply substP2. myomega.
        + f_equal. replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
          apply substP2. myomega.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by myomega.
        rewrite substP4.
        eapply type_JBeta ; esh.
        + cbn. unfold snoc. cbn.
          f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
            apply substP2. myomega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by myomega.
            apply substP2. myomega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by myomega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by myomega.
          change (wRefl (A0 {0 + #|Δ| := u}) (u0 {0 + #|Δ| := u}))
            with ((wRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply type_TransportBeta ; esh.
      - cbn. eapply type_PairEta ; esh.
      - cbn. eapply type_ProdExt ; esh.
      - cbn. eapply type_SumExt ; esh.
      - cbn. erewrite subst_ax_type by eassumption.
        eapply type_Ax.
        + now eapply wf_subst.
        + assumption.
      - cbn. erewrite subst_ax_type, subst_ax_body by eassumption.
        eapply type_Delta.
        + now eapply wf_subst.
        + assumption.
      - eapply type_rename.
        + esh.
        + eapply nl_subst.
          * assumption.
          * reflexivity.
    }

  (* wf_subst *)
  - { intros hg hu.
      destruct Δ.
      - cbn. dependent destruction h. assumption.
      - dependent destruction h. cbn. econstructor.
        + eapply wf_subst ; eassumption.
        + esh.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; myomega.
Defined.

Corollary typing_subst :
  forall {Σ Γ t A B u},
    type_glob Σ ->
    Σ ;;; Γ ,, A |-w t : B ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Corollary typing_subst2 :
  forall {Σ Γ t A B C u v},
    type_glob Σ ->
    Σ ;;; Γ ,, A ,, B |-w t : C ->
    Σ ;;; Γ |-w u : A ->
    Σ ;;; Γ |-w v : B{ 0 := u } ->
    Σ ;;; Γ |-w t{ 1 := u }{ 0 := v } : C{ 1 := u }{ 0 := v }.
Proof.
  intros Σ Γ t A B C u v hg ht hu hv.
  eapply @type_subst with (Δ := []).
  - eapply @type_subst with (Δ := [ B ]).
    + exact ht.
    + assumption.
    + assumption.
  - assumption.
  - cbn. assumption.
Defined.

Ltac lift_sort :=
  match goal with
  | |- _ ;;; _ |-w lift ?n ?k ?t : ?S => change S with (lift n k S)
  | |- _ ;;; _ |-w ?t { ?n := ?u } : ?S => change S with (S {n := u})
  end.

Fixpoint nlctx Γ :=
  match Γ with
  | A :: Γ => nlctx Γ,, nl A
  | nil => nil
  end.

Lemma nlctx_length :
  forall {Γ Δ},
    nlctx Γ = nlctx Δ ->
    #|Γ| = #|Δ|.
Proof.
  intro Γ. induction Γ ; intros Δ e.
  - cbn. destruct Δ ; simpl in e ; try discriminate e.
    reflexivity.
  - destruct Δ ; simpl in e ; try discriminate e.
    cbn. f_equal. eapply IHΓ.
    simpl in e. inversion e. reflexivity.
Defined.

Lemma nl_safe_nth :
  forall {Γ Δ n i1 i2},
    nlctx Γ = nlctx Δ ->
    nl (safe_nth Δ (exist _ n i1)) = nl (safe_nth Γ (exist _ n i2)).
Proof.
  intros Γ Δ n i1 i2 e. cbn in *. revert Δ n i1 i2 e.
  induction Γ as [| A Γ ih] ; intros Δ n i1 i2 e.
  - cbn. bang.
  - destruct Δ as [|B Δ] ; simpl in e ; try discriminate e.
    inversion e.
    destruct n.
    + cbn. symmetry. assumption.
    + cbn. eapply ih. assumption.
Defined.

Ltac nleq :=
  repeat (try eapply nl_lift ; try eapply nl_subst) ;
  cbn ; auto ; f_equal ; eauto.

Ltac reih :=
  lazymatch goal with
  | h : _ -> _ -> _ -> nl ?t1 = _ -> _ -> _ ;;; _ |-w _ : _,
    e : nl ?t1 = nl ?t2
    |- _ ;;; _ |-w ?t2 : _ =>
    eapply h ; [
      repeat nleq
    | first [ eassumption | reflexivity ]
    | first [
        eassumption
      | econstructor ; try eassumption ; reih
      ]
    ]
  | h : _ -> _ -> _ -> nl ?t = _ -> _ -> _ ;;; _ |-w _ : _
    |- _ ;;; _ |-w ?t : _ =>
    eapply h ; [
      repeat nleq
    | first [ eassumption | reflexivity ]
    | first [
        eassumption
      | econstructor ; try eassumption ; reih
      ]
    ]
  end.

Lemma rename_typed :
  forall {Σ Γ Δ t u A},
    type_glob Σ ->
    Σ ;;; Γ |-w t : A ->
    nlctx Γ = nlctx Δ ->
    nl t = nl u ->
    wf Σ Δ ->
    Σ ;;; Δ |-w u : A.
Proof.
  intros Σ Γ Δ t u A hg h ex e hw. revert Δ ex u e hw.
  induction h ; intros Δ ex t' e hw.
  all: try solve [
    simpl in e ; destruct t' ; try discriminate e ;
    simpl in e ; inversion e ; subst ; clear e ;
    try solve [
          econstructor ; try eassumption ; try reih ;
          try (econstructor ; [ reih | repeat nleq ])
        ] ;
    try solve [
          econstructor ; [
            econstructor ; try eassumption ;
            try reih ;
            try (econstructor ; [ reih | repeat nleq ])
          | repeat nleq
          ]
        ]
  ].
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + unshelve (econstructor ; eassumption).
      rewrite <- (nlctx_length ex). assumption.
    + eapply nl_lift. eapply nl_safe_nth. assumption.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      eapply IHh4.
      * repeat nleq.
      * eassumption.
      * repeat eapply wf_snoc ; try eassumption ; try reih.
        econstructor ; try lift_sort ; try eapply typing_lift01 ;
        try eassumption ; try reih ;
        try (econstructor ; [ reih | repeat nleq ]).
        try econstructor ; [ econstructor |].
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
        -- cbn. nleq.
    + nleq.
  - simpl in e. destruct t' ; try discriminate e.
    simpl in e. inversion e. subst. clear e.
    econstructor.
    + econstructor ; try eassumption ; try reih ;
      try (econstructor ; [ reih | repeat nleq ]).
      eapply IHh2.
      * repeat nleq.
      * eassumption.
      * repeat eapply wf_snoc ; try eassumption ; try reih.
        econstructor ; try lift_sort ; try eapply typing_lift01 ;
        try eassumption ; try reih ;
        try (econstructor ; [ reih | repeat nleq ]).
        try econstructor ; [ econstructor |].
        -- repeat eapply wf_snoc ; try eassumption ; try reih.
        -- cbn. nleq.
    + repeat nleq.
  - econstructor.
    + eapply IHh ; assumption.
    + assumption.
  Unshelve.
  all: try solve [ constructor ].
  { cbn. auto with arith. }
  { cbn. auto with arith. }
Defined.

Lemma istype_type :
  forall {Σ Γ t T},
    type_glob Σ ->
    Σ ;;; Γ |-w t : T ->
    isType Σ Γ T.
Proof.
  unfold isType. intros Σ Γ t T hg H.
  induction H.
  - revert n isdecl. induction H ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn.
        exists s. change (wSort s) with (lift0 1 (wSort s)).
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHwf n isdecl') as [s' hh].
           exists s'. change (wSort s') with (lift0 1 (wSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t'. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ assumption.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - exists (Sorts.succ (Sorts.succ s)). now apply type_Sort.
  - eexists. apply type_Sort. apply (typing_wf H).
  - destruct IHtyping2. eexists. apply type_Prod ; eassumption.
  - destruct IHtyping1. destruct IHtyping2.
    destruct (inversion_Prod H1) as [s1 [s2 [? [? ?]]]].
    eexists.
    match goal with
    | |- _ ;;; _ |-w _ : ?S =>
      change S with (S{ 0 := u })
    end.
    eapply typing_subst ; eassumption.
  - eexists. econstructor. eapply typing_wf. eassumption.
  - eexists. econstructor ; eassumption.
  - eexists. eassumption.
  - exists s2. change (wSort s2) with ((wSort s2){ 0 := wPi1 A B p }).
    eapply typing_subst ; try eassumption.
    econstructor ; eassumption.
  - eexists. apply type_Sort. apply (typing_wf H).
  - eexists. now apply type_Eq.
  - exists s2.
    change (wSort s2) with ((wSort s2){1 := v}{0 := p}).
    eapply typing_subst2.
    + assumption.
    + eassumption.
    + assumption.
    + cbn. rewrite !lift_subst, lift00.
      assumption.
  - eexists. eassumption.
  - destruct IHtyping1. destruct IHtyping2.
    eexists. econstructor.
    + lift_sort. eapply typing_subst ; eassumption.
    + eapply type_App ; try eassumption.
      eapply type_Lambda ; eassumption.
    + eapply typing_subst ; eassumption.
  - destruct IHtyping1. destruct IHtyping2. destruct IHtyping3.
    eexists. econstructor ; try eassumption.
    econstructor ; eassumption.
  - destruct IHtyping1. destruct IHtyping2. destruct IHtyping3.
    destruct (inversion_Prod H3) as [? [? [? [? ?]]]].
    eexists. econstructor.
    + econstructor ; eassumption.
    + eapply type_rename ; try eassumption.
      reflexivity.
    + eapply type_rename ; try eassumption.
      reflexivity.
  - eexists. eapply type_Eq.
    + match goal with
      | |- _ ;;; _ |-w _ : ?S =>
        change S with (S{1 := u}{0 := wRefl A u})
      end.
      eapply typing_subst2 ; try eassumption.
      cbn. rewrite !lift_subst, lift00.
      econstructor ; eassumption.
    + econstructor ; try eassumption.
      econstructor ; eassumption.
    + assumption.
  - econstructor ; try eassumption.
    econstructor ; try eassumption.
    econstructor ; try eassumption.
    econstructor ; try eassumption.
    econstructor. eapply typing_wf. eassumption.
  - destruct IHtyping as [s hs].
    destruct (inversion_Sum hs) as [? [? [? [? ?]]]].
    eexists. econstructor.
    + econstructor ; eassumption.
    + econstructor ; try eassumption.
      * econstructor ; eassumption.
      * econstructor ; eassumption.
    + econstructor ; try eassumption. reflexivity.
  - destruct IHtyping1 as [? h].
    destruct (inversion_Eq h) as [? [? [? [? ?]]]].
    eexists. econstructor.
    + econstructor. eapply typing_wf ; eassumption.
    + econstructor ; assumption.
    + econstructor ; assumption.
  - destruct IHtyping1 as [? h].
    destruct (inversion_Eq h) as [? [? [? [? ?]]]].
    eexists. econstructor.
    + econstructor. eapply typing_wf ; eassumption.
    + econstructor ; assumption.
    + econstructor ; assumption.
  - pose proof (isType_lookup_glob hg _ _ H0).
    destruct H1 as [s HH]; exists s.
    pose proof (@type_lift _ [] Γ [] _ _ HH hg). cbn in H1.
    rewrite nil_cat in H1.
    now erewrite lift_ax_type in H1 by eassumption.
  - pose proof (isType_lookup_glob hg _ _ H0).
    destruct H1 as [s HH]; exists (Sorts.eq_sort s).
    assert (Σ;;; [] |-w wEq (dtype d) (wAx id) (dbody d)
                     : wSort (Sorts.eq_sort s)). {
      econstructor. assumption.
      eapply type_Ax. constructor. assumption.
      eapply typed_ax_body; eassumption.
    }
    pose proof (@type_lift _ [] Γ [] _ _ H1 hg). cbn in H2.
    rewrite nil_cat in H2.
    erewrite lift_ax_body in H2 by eassumption.
    now erewrite lift_ax_type in H2 by eassumption.
  - destruct IHtyping. eexists.
    eapply rename_typed ; try eassumption.
    + reflexivity.
    + eapply typing_wf. eassumption.
  Unshelve. constructor.
Defined.
End Lemmata.