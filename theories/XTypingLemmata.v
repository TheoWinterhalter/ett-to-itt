(*! Meta-theory for ETT *)

From Coq Require Import Bool String List BinPos Compare_dec PeanoNat Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing AstUtils.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
               XTyping.
Import ListNotations.

Open Scope x_scope.

(* For efficiency reasons we use type in type for examples. *)
Existing Instance Sorts.type_in_type.

Notation Ty := (@sSort Sorts.type_in_type tt).

Section Conv.

Definition isType (Σ : sglobal_context) (Γ : scontext) (t : sterm) :=
  (* ∑ s, Σ ;;; Γ |-x t : sSort s. *)
  Σ ;;; Γ |-x t : Ty.

Inductive xtype_glob : sglobal_context -> Type :=
| xtype_glob_nil : xtype_glob []
| xtype_glob_cons Σ d :
    xtype_glob Σ ->
    fresh_glob (dname d) Σ ->
    isType Σ [] (dtype d) ->
    xtype_glob (d :: Σ).

Derive Signature for type_glob.

Lemma meta_ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-x t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-x t : A.
Proof.
  intros Σ Γ Δ t A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqctx_conv :
  forall {Σ Γ Δ t1 t2 A},
    Σ ;;; Γ |-x t1 ≡ t2 : A ->
    Γ = Δ ->
    Σ ;;; Δ |-x t1 ≡ t2 : A.
Proof.
  intros Σ Γ Δ t1 t2 A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_conv :
  forall {Σ Γ t A B},
    Σ ;;; Γ |-x t : A ->
    A = B ->
    Σ ;;; Γ |-x t : B.
Proof.
  intros Σ Γ t A B h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqconv :
  forall {Σ Γ t t' A B},
    Σ ;;; Γ |-x t ≡ t' : A ->
    A = B ->
    Σ ;;; Γ |-x t ≡ t' : B.
Proof.
  intros Σ Γ t t' A B h e.
  rewrite <- e. exact h.
Defined.

Fixpoint weak_glob_type {Σ Γ t A} (h : Σ ;;; Γ |-x t : A) :
  forall {d},
    fresh_glob (dname d) Σ ->
    (d::Σ) ;;; Γ |-x t : A

with weak_glob_eq_term {Σ Γ u v A} (h : Σ ;;; Γ |-x u ≡ v : A) :
  forall {d},
    fresh_glob (dname d) Σ ->
    (d::Σ) ;;; Γ |-x u ≡ v : A.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ;
                try apply weak_glob_type ;
                try apply weak_glob_eq_term ;
                eassumption
               ).
      eapply type_Ax.
      cbn. erewrite ident_neq_fresh by eassumption.
      assumption.
    }

  (* weak_glob_eq_term *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ;
                try apply weak_glob_type ;
                try apply weak_glob_eq_term ;
                eassumption
               ).
    }
Defined.

Corollary weak_glob_isType :
  forall {Σ Γ A} (h : isType Σ Γ A) {d},
    fresh_glob (dname d) Σ ->
    isType (d::Σ) Γ A.
Proof.
  intros Σ Γ A h d hf.
  eapply weak_glob_type ; eassumption.
Defined.

Fact typed_ax_type :
  forall {Σ}, xtype_glob Σ ->
  forall {id ty},
    lookup_glob Σ id = Some ty ->
    isType Σ [] ty.
Proof.
  intros Σ hg. induction hg ; intros id ty h.
  - discriminate h.
  - cbn in h.
    case_eq (ident_eq id (dname d)).
    + intro e. rewrite e in h. inversion h. subst.
      eapply weak_glob_isType ; eassumption.
    + intro e. rewrite e in h.
      specialize (IHhg _ _ h).
      eapply weak_glob_isType ; eassumption.
Defined.

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-x t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat (erewrite_assumption) ; reflexivity).
  unfold closed_above.
  case_eq (n <? #|Γ|) ; intro e ; bprop e ; try mylia.
  reflexivity.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-x t : T ->
    closed t.
Proof.
  intros Σ t T h.
  unfold closed. eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

Fact lift_ax_type :
  forall {Σ},
    xtype_glob Σ ->
    forall {id ty},
      lookup_glob Σ id = Some ty ->
      forall n k, lift n k ty = ty.
Proof.
  intros Σ hg id ty isd n k.
  eapply closed_lift.
  eapply type_ctxempty_closed.
  eapply typed_ax_type ; eassumption.
Defined.

Fact subst_ax_type :
  forall {Σ},
    xtype_glob Σ ->
    forall {id ty},
      lookup_glob Σ id = Some ty ->
      forall n u, ty{ n := u } = ty.
Proof.
  intros Σ hg id ty isd n k.
  eapply closed_subst.
  eapply type_ctxempty_closed.
  eapply typed_ax_type ; eassumption.
Defined.

End Conv.

Section Lift.

Ltac ih h :=
  lazymatch goal with
  | [ type_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Ξ |-x t : A ->
          xtype_glob Σ ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-x lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A,
      cong_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t1 t2 A : sterm),
          Σ;;; Γ ,,, Ξ |-x t1 ≡ t2 : A ->
          xtype_glob Σ ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-x lift #|Δ| #|Ξ| t1 ≡ lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,,, ?Ξ' |-x _ ≡ _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-x _ ≡ _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-x _ ≡ _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift or cong_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-x ?t : _ |- _ ;;; _ |-x lift _ _ ?t : _ => ih h
  | h : _ ;;; _ |-x ?t ≡ _ : _ |- _ ;;; _ |-x lift _ _ ?t ≡ _ : _ =>
    ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-x t : A) {struct h} :
  xtype_glob Σ ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-x lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with cong_lift {Σ Γ Δ Ξ t1 t2 A} (h : Σ ;;; Γ ,,, Ξ |-x t1 ≡ t2 : A) {struct h} :
  xtype_glob Σ ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-x lift #|Δ| #|Ξ| t1
  ≡ lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A
.
Proof.
  - { dependent destruction h ; intros hΣ.
      - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e.
        + rewrite liftP3 by mylia.
          replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by mylia.
          eapply meta_conv.
          * eapply type_Rel.
          * f_equal. f_equal.
            erewrite 3!safe_nth_ge'
              by (try rewrite lift_context_length ; mylia).
            eapply safe_nth_cong_irr.
            rewrite lift_context_length. mylia.
        + eapply meta_conv.
          * eapply type_Rel.
          * erewrite 2!safe_nth_lt.
            eapply lift_context_ex.
      - cbn. apply type_Sort with (s0 := s).
      - cbn. eapply type_Prod with (s3 := s1) (s4 := s2) ; eih.
      - cbn. eapply type_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1.
        eapply type_App ; eih.
      - cbn. eapply type_Sum with (s3 := s1) (s4 := s2) ; eih.
      - cbn. eapply type_Pair ; eih.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1. reflexivity.
      - cbn. eapply type_Pi1 ; eih.
      - cbn.
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1. cbn.
        eapply type_Pi2 ; eih.
      - cbn. apply type_Eq with (s0 := s) ; eih.
      - cbn. eapply type_Refl ; eih.
      - cbn. eapply type_Ax.
        erewrite lift_ax_type by eassumption. assumption.
      - eapply type_conv ; eih.
    }

  - { intros hg. dependent destruction h.
      - apply eq_reflexivity. apply type_lift ; assumption.
      - apply eq_symmetry. eapply cong_lift ; assumption.
      - eapply eq_transitivity ; eih.
      - change (lift #|Δ| #|Ξ| (t {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t { 0 := u })).
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite 2!substP1. cbn.
        eapply eq_beta ; eih.
      - eapply eq_conv ; eih.
      - cbn. eapply cong_Prod with (s3 := s1) (s4 := s2) ; eih.
      - cbn. eapply cong_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
        rewrite substP1.
        eapply cong_App ; eih.
      - cbn. eapply cong_Sum with (s3 := s1) (s4 := s2) ; eih.
      - cbn. eapply cong_Pair ; eih.
        + change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
            with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
          apply substP1.
        + change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
            with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
          apply substP1.
        + change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
            with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
          rewrite <- substP1. reflexivity.
      - cbn. eapply cong_Pi1 ; eih.
      - cbn.
        change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite !substP1. cbn.
        eapply cong_Pi2 ; eih.
      - cbn. eapply cong_Eq with (s0 := s) ; eih.
      - cbn. eapply cong_Refl ; eih.
      - eapply reflection with (e0 := lift #|Δ| #|Ξ| e). eih.
      - eapply eq_alpha.
        + eapply Equality.nl_lift. assumption.
        + eih.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
       try rewrite lift_context_length ; mylia.

Defined.

End Lift.

Section Subst.

Ltac sh h :=
  lazymatch goal with
  | [ type_subst :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A B u : sterm),
          Σ;;; Γ,, B ,,, Δ |-x t : A ->
          xtype_glob Σ ->
          Σ;;; Γ |-x u : B -> Σ;;; Γ ,,, subst_context u Δ |-x
          t {#|Δ| := u} : A {#|Δ| := u},
     cong_subst :
       forall (Σ : sglobal_context) (Γ Δ : scontext) (t1 t2 A B u : sterm),
         Σ;;; Γ,, B ,,, Δ |-x t1 ≡ t2 : A ->
         xtype_glob Σ ->
         Σ;;; Γ |-x u : B -> Σ;;; Γ ,,, subst_context u Δ |-x
         t1 {#|Δ| := u} ≡ t2 {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, ?B' ,,, ?Δ' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d',, ?d'' |-x _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,, ?B' ,,, ?Δ' |-x _ ≡ _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d' |-x _ ≡ _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d',, ?d'' |-x _ ≡ _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst, cong_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-x ?t : _ |- _ ;;; _ |-x ?t{ _ := _ } : _ => sh h
  | h : _ ;;; _ |-x ?t ≡ _ : _ |- _ ;;; _ |-x ?t{ _ := _ } ≡ _ : _ =>
    sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A B u}
  (h : Σ ;;; Γ ,, B ,,, Δ |-x t : A) {struct h} :
  xtype_glob Σ ->
  Σ ;;; Γ |-x u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-x t{ #|Δ| := u } : A{ #|Δ| := u }

with cong_subst {Σ Γ Δ t1 t2 A B u}
  (h : Σ ;;; Γ ,, B ,,, Δ |-x t1 ≡ t2 : A) {struct h} :
  xtype_glob Σ ->
  Σ ;;; Γ |-x u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-x t1{ #|Δ| := u }
  ≡ t2{ #|Δ| := u } : A{ #|Δ| := u }
.
Proof.
  (* type_subst *)
  - { intros hg hu.
      dependent destruction h.
      - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
        + assert (h : n >= #|Δ|) by mylia.
          rewrite safe_nth_ge' with (h0 := h).
          assert (n - #|Δ| = 0) by mylia.
          set (ge := ge_sub isdecl h).
          generalize ge.
          rewrite H. intro ge'.
          cbn. rewrite substP3 by mylia.
          subst.
          replace #|Δ| with #|subst_context u Δ|
            by (now rewrite subst_context_length).
          eapply @type_lift with (Ξ := []) (Δ := subst_context u Δ).
          * cbn. assumption.
          * assumption.
        + assert (h : n >= #|Δ|) by mylia.
          rewrite safe_nth_ge' with (h0 := h).
          set (ge := ge_sub isdecl h).
          destruct n ; try (exfalso ; abstract easy).
          rewrite substP3 by mylia.
          generalize ge.
          replace (S n - #|Δ|) with (S (n - #|Δ|)) by mylia.
          cbn. intro ge'.
          eapply meta_conv.
          * eapply type_Rel.
          * erewrite safe_nth_ge'.
            f_equal. eapply safe_nth_cong_irr.
            rewrite subst_context_length. reflexivity.
        + assert (h : n < #|Δ|) by mylia.
          rewrite @safe_nth_lt with (isdecl' := h).
          match goal with
          | |- _ ;;; _ |-x _ : ?t{?d := ?u} =>
            replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
              by (f_equal ; mylia)
          end.
          rewrite substP2 by mylia.
          eapply meta_conv.
          * eapply type_Rel.
          * f_equal.
            erewrite safe_nth_lt.
            eapply safe_nth_subst_context.
      - cbn. apply type_Sort with (s0 := s).
      - cbn. eapply type_Prod with (s3 := s1) (s4 := s2) ; esh.
      - cbn. eapply type_Lambda ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite substP4. cbn.
        eapply type_App ; esh.
      - cbn. eapply type_Sum with (s3 := s1) (s4 := s2) ; esh.
      - cbn. eapply type_Pair ; esh.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. reflexivity.
      - cbn. eapply type_Pi1 ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply type_Pi2 ; esh.
      - cbn. eapply type_Eq with (s0 := s) ; esh.
      - cbn. eapply type_Refl ; esh.
      - cbn. erewrite subst_ax_type by eassumption.
        eapply type_Ax.
        assumption.
      - cbn. eapply type_conv ; esh.
    }

  (* cong_subst *)
  - { intros hg hu.
      dependent destruction h.
      - constructor. esh.
      - constructor. esh.
      - eapply eq_transitivity ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply eq_beta ; esh.
      - eapply eq_conv ; esh.
      - cbn. eapply cong_Prod with (s3 := s1) (s4 := s2) ; esh.
      - cbn. eapply cong_Lambda ; esh.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply cong_App ; esh.
      - cbn. eapply cong_Sum with (s3 := s1) (s4 := s2) ; esh.
      - cbn. eapply cong_Pair ; esh.
        + change (#|Δ|) with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
        + change (#|Δ|) with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
        + change (#|Δ|) with (0 + #|Δ|)%nat.
          rewrite substP4. reflexivity.
      - cbn. eapply cong_Pi1 ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply cong_Pi2 ; esh.
      - cbn. eapply cong_Eq with (s0 := s) ; esh.
      - cbn. eapply cong_Refl ; esh.
      - eapply reflection with (e0 := e{#|Δ| := u}). esh.
      - eapply eq_alpha.
        + eapply Equality.nl_subst ; try assumption. reflexivity.
        + esh.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ;
       mylia.
Defined.

End Subst.

Section TypeType.

(* TODO Move *)
Corollary typing_lift01 :
  forall {Σ Γ t A B s},
    xtype_glob Σ ->
    Σ ;;; Γ |-x t : A ->
    Σ ;;; Γ |-x B : sSort s ->
    Σ ;;; Γ ,, B |-x lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A B s hg ht hB.
  apply (@type_lift _ _ [ B ] nil _ _ ht hg).
Defined.

(* TODO Move *)
Corollary typing_subst :
  forall {Σ Γ t A B u},
    xtype_glob Σ ->
    Σ ;;; Γ ,, A |-x t : B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Lemma istype_type :
  forall {Σ Γ t T},
    xtype_glob Σ ->
    wf Σ Γ ->
    Σ ;;; Γ |-x t : T ->
    Σ ;;; Γ |-x T : Ty.
Proof.
  intros Σ Γ t T xhg w h.
  induction h.
  - revert n isdecl. induction w ; intros n isdecl.
    + cbn in isdecl. exfalso. abstract easy.
    + destruct n.
      * cbn. change Ty with (lift0 1 Ty).
        destruct s.
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- cbn in isdecl. mylia.
        -- specialize (IHw n isdecl').
           change Ty with (lift0 1 Ty).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t'. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ assumption.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - destruct s. cbn. eapply type_Sort with (s := tt).
  - cbn. apply type_Sort with (s := tt).
  - eapply type_Prod with (s3 := s1) (s4 := s2) ; eassumption.
  - change Ty with (Ty{ 0 := u }).
    destruct s2.
    eapply typing_subst ; eassumption.
  - econstructor.
  - eapply type_Sum with (s3 := s1) (s4 := s2) ; eassumption.
  - destruct s1. eassumption.
  - change Ty with (Ty{ 0 := sPi1 A B p }).
    destruct s2.
    eapply typing_subst ; try eassumption.
    econstructor ; eassumption.
  - econstructor.
  - eapply type_Eq with (s0 := s) ; eassumption.
  - pose proof (typed_ax_type xhg e) as hh.
    change Ty with (lift #|Γ| #|@nil sterm| Ty).
    replace ty with (lift #|Γ| #|@nil sterm| ty)
      by (erewrite lift_ax_type by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ) ; assumption.
    + cbn. apply nil_cat.
  - destruct s. eassumption.
Defined.

End TypeType.