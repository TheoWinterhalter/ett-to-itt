From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils LiftSubst Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon XTyping Conversion ITyping
               ITypingInversions ITypingLemmata ITypingAdmissible
               Uniqueness SubjectReduction PackLifts FundamentalLemma.

Section Translation.

Open Scope type_scope.
Open Scope x_scope.
Open Scope i_scope.


(*! Translation *)

Fact length_increl : forall {Γ Γ'}, Γ ⊂ Γ' -> #|Γ| = #|Γ'|.
Proof.
  intros Γ Γ' h.
  dependent induction h.
  - reflexivity.
  - cbn. now f_equal.
Defined.

Fact nth_increl :
  forall {Γ Γ'},
    Γ ⊂ Γ' ->
    forall {n} { isdecl : n < #|Γ| } { isdecl' : n < #|Γ'| },
      safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl)
    ⊏ safe_nth Γ' (exist (fun n0 : nat => n0 < #|Γ'|) n isdecl').
Proof.
  intros Γ Γ' e. induction e ; intros m isdecl isdecl'.
  - exfalso. easy.
  - destruct m.
    + cbn. assumption.
    + cbn. apply IHe.
Defined.

Definition trans_snoc {Σ Γ A s Γ' A' s'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s' # ⟦ Γ |--- [A] : sSort s ⟧ ->
  Σ |--i Γ' ,, A' # ⟦ Γ ,, A ⟧.
Proof.
  intros hΓ hA.
  split.
  - constructor ; now destruct hA as [[[? ?] ?] ?].
  - econstructor.
    + now destruct hΓ.
    + now destruct hA as [[[? ?] ?] ?].
Defined.

Definition trans_Prod {Σ Γ n A B s1 s2 Γ' A' B'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s1 # ⟦ Γ |--- [A] : sSort s1 ⟧ ->
  Σ ;;;; Γ' ,, A' |--- [B'] : sSort s2
  # ⟦ Γ ,, A |--- [B]: sSort s2 ⟧ ->
  Σ ;;;; Γ' |--- [sProd n A' B']: sSort (max_sort s1 s2)
  # ⟦ Γ |--- [ sProd n A B]: sSort (max_sort s1 s2) ⟧.
Proof.
  intros hΓ hA hB.
  destruct hΓ. destruct hA as [[? ?] ?]. destruct hB as [[? ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - now constructor.
  - now eapply type_Prod.
Defined.

Definition trans_Sum {Σ Γ n A B s1 s2 Γ' A' B'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s1 # ⟦ Γ |--- [A] : sSort s1 ⟧ ->
  Σ ;;;; Γ' ,, A' |--- [B'] : sSort s2
  # ⟦ Γ ,, A |--- [B]: sSort s2 ⟧ ->
  Σ ;;;; Γ' |--- [sSum n A' B']: sSort (max_sort s1 s2)
  # ⟦ Γ |--- [ sSum n A B]: sSort (max_sort s1 s2) ⟧.
Proof.
  intros hΓ hA hB.
  destruct hΓ. destruct hA as [[? ?] ?]. destruct hB as [[? ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - now constructor.
  - now eapply type_Sum.
Defined.

Definition trans_Eq {Σ Γ A u v s Γ' A' u' v'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s # ⟦ Γ |--- [A] : sSort s ⟧ ->
  Σ ;;;; Γ' |--- [u'] : A' # ⟦ Γ |--- [u] : A ⟧ ->
  Σ ;;;; Γ' |--- [v'] : A' # ⟦ Γ |--- [v] : A ⟧ ->
  Σ ;;;; Γ' |--- [sEq A' u' v'] : sSort s # ⟦ Γ |--- [sEq A u v] : sSort s ⟧.
Proof.
  intros hΓ hA hu hv.
  destruct hA as [[[? ?] ?] ?].
  destruct hu as [[[? ?] ?] ?].
  destruct hv as [[[? ?] ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - constructor ; assumption.
  - apply type_Eq ; assumption.
Defined.

Definition trans_subst {Σ Γ s A B u Γ' A' B' u'} :
  type_glob Σ ->
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ',, A' |--- [B']: sSort s # ⟦ Γ,, A |--- [B]: sSort s ⟧ ->
  Σ ;;;; Γ' |--- [u']: A' # ⟦ Γ |--- [u]: A ⟧ ->
  Σ ;;;; Γ' |--- [B'{ 0 := u' }]: sSort s # ⟦ Γ |--- [B{ 0 := u }]: sSort s ⟧.
Proof.
  intros hg hΓ hB hu.
  destruct hΓ.
  destruct hB as [[[? ?] ?] ?]. destruct hu as [[[? ?] ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - apply inrel_subst ; assumption.
  - lift_sort. eapply typing_subst ; eassumption.
Defined.

(* Maybe put this together with the other translation definitions *)
Definition eqtrans Σ Γ A u v Γ' A' A'' u' v' p' :=
  Γ ⊂ Γ' *
  A ⊏ A' *
  A ⊏ A'' *
  u ⊏ u' *
  v ⊏ v' *
  (Σ ;;; Γ' |-i p' : sHeq A' u' A'' v').

Lemma eqtrans_trans :
  forall {Σ Γ A u v Γ' A' A'' u' v' p'},
    type_glob Σ ->
    eqtrans Σ Γ A u v Γ' A' A'' u' v' p' ->
    (Σ ;;;; Γ' |--- [u'] : A' # ⟦ Γ |--- [u] : A ⟧) *
    (Σ ;;;; Γ' |--- [v'] : A'' # ⟦ Γ |--- [v] : A ⟧).
Proof.
  intros Σ Γ A u v Γ' A' A'' u' v' p' hg h.
  destruct h as [[[[[eΓ eS'] eS''] eA] eB] hp'].
  repeat split ; try assumption.
  all: destruct (istype_type hg hp') as [? hheq].
  all: ttinv hheq.
  all: assumption.
Defined.

(* For optimisation, we remark that we can decide whenever an heterogenous
   equality is reflexivity.
 *)
Inductive isHeqRefl : sterm -> Type :=
| is_HeqRefl A u : isHeqRefl (sHeqRefl A u).

Definition decHeqRefl t : dec (isHeqRefl t).
  refine (
    match t with
    | sHeqRefl A u => inleft (is_HeqRefl A u)
    | _ => inright (fun e => _)
    end
  ). all: inversion e.
Defined.

(* Optimised symmetry *)
Definition optHeqSym p :=
  match p with
  | sHeqRefl A u => sHeqRefl A u
  | _ => sHeqSym p
  end.

Lemma opt_HeqSym :
  forall {Σ Γ A a B b p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i optHeqSym p : sHeq B b A a.
Proof.
  intros Σ Γ A a B b p hg h.
  case (decHeqRefl p).
  - intros i. destruct i as [C c].
    simpl. 
    ttinv h. destruct (heq_conv_inv h2) as [[[eA eu] eA'] ev].
    destruct (istype_type hg h) as [z heq]. ttinv heq.
    eapply type_conv.
    + eapply type_HeqRefl' ; eassumption.
    + eapply type_Heq ; eassumption.
    + apply cong_Heq ; assumption.
  - intros e. destruct p.
    16: exfalso ; apply e ; constructor.
    all: simpl ; apply type_HeqSym' ; assumption.
Defined.


Scheme typing_ind := Induction for XTyping.typing Sort Type
  with wf_ind := Induction for XTyping.wf Sort Type
  with eq_term_ind := Induction for XTyping.eq_term Sort Type.

(* Combined Scheme typing_all from typing_ind , wf_ind , eq_term_ind. *)

Definition typing_all : forall (Σ : sglobal_context)
         (P0 : forall s : scontext, XTyping.wf Σ s -> Type)
         (P : forall (s : scontext) (s0 s1 : sterm),
              Σ;;; s |-x s0 : s1 -> Type)
         (P1 : forall (s : scontext) (s0 s1 s2 : sterm),
               Σ;;; s |-x s0 = s1 : s2 -> Type),
       P0 [] (XTyping.wf_nil Σ) ->
       (forall (Γ : scontext) (A : sterm)
          (s : sort) (w : XTyping.wf Σ Γ),
        P0 Γ w ->
        forall t : Σ;;; Γ |-x A : sSort s,
        P Γ A (sSort s) t ->
        P0 (Γ,, A) (XTyping.wf_snoc Σ Γ A s w t))->
       (forall (Γ : scontext) (n : nat) (w : XTyping.wf Σ Γ),
        P0 Γ w ->
        forall isdecl : n < #|Γ|,
        P Γ (sRel n)
          (lift0 (S n)
             (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl)))
          (XTyping.type_Rel Σ Γ n w isdecl)) ->
       (forall (Γ : scontext) (s : sort) (w : XTyping.wf Σ Γ),
        P0 Γ w ->
        P Γ (sSort s) (sSort (succ_sort s)) (XTyping.type_Sort Σ Γ s w)) ->
       (forall (Γ : scontext) (n : name) (t b : sterm)
          (s1 s2 : sort) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, t |-x b : sSort s2,
        P (Γ,, t) b (sSort s2) t1 ->
        P Γ (sProd n t b) (sSort (max_sort s1 s2))
          (XTyping.type_Prod Σ Γ n t b s1 s2 t0 t1)) ->
       (forall (Γ : scontext) (n n' : name) (t b : sterm)
          (s1 s2 : sort) (bty : sterm) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, t |-x bty : sSort s2,
        P (Γ,, t) bty (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, t |-x b : bty,
        P (Γ,, t) b bty t2 ->
        P Γ (sLambda n t bty b) (sProd n' t bty)
          (XTyping.type_Lambda Σ Γ n n' t b s1 s2 bty t0 t1 t2)) ->
       (forall (Γ : scontext) (n : name) (s1 s2 : sort)
          (t A B u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, A |-x B : sSort s2,
        P (Γ,, A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-x t : sProd n A B,
        P Γ t (sProd n A B) t2 ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A t3 ->
        P Γ (sApp t A B u) (B {0 := u})
          (XTyping.type_App Σ Γ n s1 s2 t A B u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (n : name) (t b : sterm) (s1 s2 : sort)
          (t0 : Σ;;; Γ |-x t : sSort s1),
           P Γ t (sSort s1) t0 ->
           forall t1 : Σ;;; Γ,, t |-x b : sSort s2,
             P (Γ,, t) b (sSort s2) t1 ->
             P Γ (sSum n t b) (sSort (max_sort s1 s2))
               (XTyping.type_Sum Σ Γ n t b s1 s2 t0 t1)) ->
       (forall (Γ : scontext) (n : name) (A B u v : sterm) (s1 s2 : sort)
          (t : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) t ->
        forall t0 : Σ;;; Γ,, A |-x B : sSort s2,
        P (Γ,, A) B (sSort s2) t0 ->
        forall t1 : Σ;;; Γ |-x u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-x v : B {0 := u},
        P Γ v (B {0 := u}) t2 ->
        P Γ (sPair A B u v) (sSum n A B)
          (XTyping.type_Pair Σ Γ n A B u v s1 s2 t t0 t1 t2)) ->
       (forall (Γ : scontext) (n : name) (A B : sterm) (s1 s2 : sort) (p : sterm)
          (t : Σ;;; Γ |-x p : sSum n A B),
           P Γ p (sSum n A B) t ->
           forall t0 : Σ;;; Γ |-x A : sSort s1,
             P Γ A (sSort s1) t0 ->
             forall t1 : Σ;;; Γ,, A |-x B : sSort s2,
               P (Γ,, A) B (sSort s2) t1 ->
               P Γ (sPi1 A B p) A (XTyping.type_Pi1 Σ Γ n A B s1 s2 p t t0 t1)) ->
       (forall (Γ : scontext) (n : name) (A B : sterm) (s1 s2 : sort) (p : sterm)
          (t : Σ;;; Γ |-x p : sSum n A B),
           P Γ p (sSum n A B) t ->
           forall t0 : Σ;;; Γ |-x A : sSort s1,
             P Γ A (sSort s1) t0 ->
             forall t1 : Σ;;; Γ,, A |-x B : sSort s2,
               P (Γ,, A) B (sSort s2) t1 ->
               P Γ (sPi2 A B p) (B {0 := sPi1 A B p})
                 (XTyping.type_Pi2 Σ Γ n A B s1 s2 p t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (A u v : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-x v : A,
        P Γ v A t1 ->
        P Γ (sEq A u v) (sSort s) (XTyping.type_Eq Σ Γ s A u v t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A t0 ->
        P Γ (sRefl A u) (sEq A u u) (XTyping.type_Refl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (id : ident) (ty : sterm) (w : XTyping.wf Σ Γ),
        P0 Γ w -> forall e : lookup_glob Σ id = Some ty,
        P Γ (sAx id) ty (XTyping.type_Ax Σ Γ id ty w e)) ->
       (forall (Γ : scontext) (t A B : sterm) (s : sort)
          (t0 : Σ;;; Γ |-x t : A),
        P Γ t A t0 ->
        forall t1 : Σ;;; Γ |-x B : sSort s,
        P Γ B (sSort s) t1 ->
        forall e : Σ;;; Γ |-x A = B : sSort s,
        P1 Γ A B (sSort s) e ->
        P Γ t B (XTyping.type_conv Σ Γ t A B s t0 t1 e)) ->
       (forall (Γ : scontext) (u A : sterm) (t : Σ;;; Γ |-x u : A),
        P Γ u A t -> P1 Γ u u A (XTyping.eq_reflexivity Σ Γ u A t)) ->
       (forall (Γ : scontext) (u v A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A e -> P1 Γ v u A (XTyping.eq_symmetry Σ Γ u v A e)) ->
       (forall (Γ : scontext) (u v w A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A e ->
        forall e0 : Σ;;; Γ |-x v = w : A,
        P1 Γ v w A e0 -> P1 Γ u w A (XTyping.eq_transitivity Σ Γ u v w A e e0)) ->
       (forall (Γ : scontext) (s1 s2 : sort) (n : name)
          (A B t u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, A |-x B : sSort s2,
        P (Γ,, A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, A |-x t : B,
        P (Γ,, A) t B t2 ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A t3 ->
        P1 Γ (sApp (sLambda n A B t) A B u) (t {0 := u})
          (B {0 := u}) (XTyping.eq_beta Σ Γ s1 s2 n A B t u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 t1 t2 : sterm)
          (e : Σ;;; Γ |-x t1 = t2 : T1),
        P1 Γ t1 t2 T1 e ->
        forall e0 : Σ;;; Γ |-x T1 = T2 : sSort s,
        P1 Γ T1 T2 (sSort s) e0 ->
        P1 Γ t1 t2 T2 (XTyping.eq_conv Σ Γ s T1 T2 t1 t2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, A1) B1 B2 (sSort s2) e0 ->
        forall t : Σ;;; Γ,, A1 |-x B1 : sSort s2,
        P (Γ,, A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, A2 |-x B2 : sSort s2,
        P (Γ,, A2) B2 (sSort s2) t0 ->
        P1 Γ (sProd n1 A1 B1) (sProd n2 A2 B2) (sSort (max_sort s1 s2))
          (XTyping.cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 e e0 t t0)) ->
       (forall (Γ : scontext) (n1 n2 n' : name) (A1 A2 B1 B2 t1 t2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ,, A1 |-x t1 = t2 : B1,
        P1 (Γ,, A1) t1 t2 B1 e1 ->
        forall t : Σ;;; Γ,, A1 |-x B1 : sSort s2,
        P (Γ,, A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, A2 |-x B2 : sSort s2,
        P (Γ,, A2) B2 (sSort s2) t0 ->
        forall t3 : Σ;;; Γ,, A1 |-x t1 : B1,
        P (Γ,, A1) t1 B1 t3 ->
        forall t4 : Σ;;; Γ,, A2 |-x t2 : B2,
        P (Γ,, A2) t2 B2 t4 ->
        P1 Γ (sLambda n1 A1 B1 t1) (sLambda n2 A2 B2 t2)
          (sProd n' A1 B1)
          (XTyping.cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 e e0 e1 t
             t0 t3 t4)) ->
       (forall (Γ : scontext) (n1 n2 : name) (s1 s2 : sort)
          (t1 t2 A1 A2 B1 B2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ |-x t1 = t2 : sProd n1 A1 B1,
        P1 Γ t1 t2 (sProd n1 A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e2 ->
        forall t : Σ;;; Γ,, A1 |-x B1 : sSort s2,
        P (Γ,, A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, A2 |-x B2 : sSort s2,
        P (Γ,, A2) B2 (sSort s2) t0 ->
        forall t3 : Σ;;; Γ |-x t1 : sProd n1 A1 B1,
        P Γ t1 (sProd n1 A1 B1) t3 ->
        forall t4 : Σ;;; Γ |-x t2 : sProd n2 A2 B2,
        P Γ t2 (sProd n2 A2 B2) t4 ->
        forall t5 : Σ;;; Γ |-x u1 : A1,
        P Γ u1 A1 t5 ->
        forall t6 : Σ;;; Γ |-x u2 : A2,
        P Γ u2 A2 t6 ->
        P1 Γ (sApp t1 A1 B1 u1) (sApp t2 A2 B2 u2)
          (B1 {0 := u1})
          (XTyping.cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 e e0 e1 e2
             t t0 t3 t4 t5 t6)) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm) (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, A1) B1 B2 (sSort s2) e0 ->
        forall t : Σ;;; Γ,, A1 |-x B1 : sSort s2,
        P (Γ,, A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, A2 |-x B2 : sSort s2,
        P (Γ,, A2) B2 (sSort s2) t0 ->
        P1 Γ (sSum n1 A1 B1) (sSum n2 A2 B2) (sSort (max_sort s1 s2))
           (XTyping.cong_Sum Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 e e0 t t0)) ->
       (forall (Γ : scontext) (n : name) (A1 A2 B1 B2 u1 u2 v1 v2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e1 ->
        forall e2 : Σ;;; Γ |-x v1 = v2 : B1 {0 := u1},
        P1 Γ v1 v2 (B1 {0 := u1}) e2 ->
        forall t : Σ;;; Γ,, A1 |-x B1 : sSort s2,
        P (Γ,, A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, A2 |-x B2 : sSort s2,
        P (Γ,, A2) B2 (sSort s2) t0 ->
        forall t1 : Σ;;; Γ |-x u1 : A1,
        P Γ u1 A1 t1 ->
        forall t2 : Σ;;; Γ |-x u2 : A2,
        P Γ u2 A2 t2 ->
        forall t3 : Σ;;; Γ |-x v1 : B1 {0 := u1},
        P Γ v1 (B1 {0 := u1}) t3 ->
        forall t4 : Σ;;; Γ |-x v2 : B2 {0 := u2},
        P Γ v2 (B2 {0 := u2}) t4 ->
        P1 Γ (sPair A1 B1 u1 v1) (sPair A2 B2 u2 v2) (sSum n A1 B1)
          (XTyping.cong_Pair Σ Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 e e0 e1 e2 t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (nx ny : name) (A1 A2 B1 B2 : sterm) (s1 s2 : sort)
          (p1 p2 : sterm) (e : Σ;;; Γ |-x p1 = p2 : sSum nx A1 B1),
        P1 Γ p1 p2 (sSum nx A1 B1) e ->
        forall e0 : Σ;;; Γ |-x A1 = A2 : sSort s1,
        P1 Γ A1 A2 (sSort s1) e0 ->
        forall e1 : Σ;;; Γ,, A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, A1) B1 B2 (sSort s2) e1 ->
        forall t : Σ;;; Γ,, A1 |-x B1 : sSort s2,
        P (Γ,, A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, A2 |-x B2 : sSort s2,
        P (Γ,, A2) B2 (sSort s2) t0 ->
        forall t1 : Σ;;; Γ |-x p1 : sSum nx A1 B1,
        P Γ p1 (sSum nx A1 B1) t1 ->
        forall t2 : Σ;;; Γ |-x p2 : sSum ny A2 B2,
        P Γ p2 (sSum ny A2 B2) t2 ->
        P1 Γ (sPi1 A1 B1 p1) (sPi1 A2 B2 p2) A1
           (XTyping.cong_Pi1 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 e e0 e1 t t0 t1 t2)) ->
       (forall (Γ : scontext) (nx ny : name) (A1 A2 B1 B2 : sterm) (s1 s2 : sort)
          (p1 p2 : sterm) (e : Σ;;; Γ |-x p1 = p2 : sSum nx A1 B1),
        P1 Γ p1 p2 (sSum nx A1 B1) e ->
        forall e0 : Σ;;; Γ |-x A1 = A2 : sSort s1,
        P1 Γ A1 A2 (sSort s1) e0 ->
        forall e1 : Σ;;; Γ,, A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, A1) B1 B2 (sSort s2) e1 ->
        forall t : Σ;;; Γ,, A1 |-x B1 : sSort s2,
        P (Γ,, A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, A2 |-x B2 : sSort s2,
        P (Γ,, A2) B2 (sSort s2) t0 ->
        forall t1 : Σ;;; Γ |-x p1 : sSum nx A1 B1,
        P Γ p1 (sSum nx A1 B1) t1 ->
        forall t2 : Σ;;; Γ |-x p2 : sSum ny A2 B2,
        P Γ p2 (sSum ny A2 B2) t2 ->
        P1 Γ (sPi2 A1 B1 p1) (sPi2 A2 B2 p2) (B1 {0 := sPi1 A1 B1 p1})
          (XTyping.cong_Pi2 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 e e0 e1 t t0 t1 t2)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-x v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 ->
        P1 Γ (sEq A1 u1 v1) (sEq A2 u2 v2) (sSort s)
          (XTyping.cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 e e0 e1)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        P1 Γ (sRefl A1 u1) (sRefl A2 u2) (sEq A1 u1 u1)
          (XTyping.cong_Refl Σ Γ s A1 A2 u1 u2 e e0)) ->
       (forall (Γ : scontext) (A u v e : sterm) (t : Σ;;; Γ |-x e : sEq A u v),
        P Γ e (sEq A u v) t -> P1 Γ u v A (reflection Σ Γ A u v e t)) ->
       (forall (s : scontext) (w : XTyping.wf Σ s), P0 s w) *
       (forall (s : scontext) (s0 s1 : sterm) (t : Σ;;; s |-x s0 : s1),
           P s s0 s1 t) *
       (forall (s : scontext) (s0 s1 s2 : sterm) (e : Σ;;; s |-x s0 = s1 : s2),
           P1 s s0 s1 s2 e).
Proof.
  intros; repeat split ; [
  eapply wf_ind | eapply typing_ind | eapply eq_term_ind]; eauto.
Defined.

Definition complete_translation {Σ} :
  type_glob Σ ->
  (forall Γ (h : XTyping.wf Σ Γ), ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧ ) *
  (forall {Γ t A} (h : Σ ;;; Γ |-x t : A)
     {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
      ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧) *
  (forall {Γ u v A} (h : Σ ;;; Γ |-x u = v : A)
     {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
      ∑ A' A'' u' v' p',
        eqtrans Σ Γ A u v Γ' A' A'' u' v' p').
Proof.
  intro hg.
  unshelve refine (
    typing_all
      Σ
      (fun Γ (h : XTyping.wf Σ Γ) =>
         ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧ )
      (fun { Γ t A} (h : Σ ;;; Γ |-x t : A) => forall
           {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
           ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧)
      (fun { Γ u v A} (h : Σ ;;; Γ |-x u = v : A) => forall
           {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
           ∑ A' A'' u' v' p',
         eqtrans Σ Γ A u v Γ' A' A'' u' v' p')
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
   ) ; intros.
  (** context_translation **)

    (* wf_nil *)
    + exists nil. split ; constructor.

    (* wf_snoc *)
    + destruct H as [Γ' hΓ'].
      rename t into hA.
      destruct (H0 _ hΓ') as [T [A' hA']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA') as [T' [[A'' hA''] hh]].
      destruct T' ; try (now inversion hh).
      exists (Γ' ,, A''). now eapply trans_snoc.

  (** type_translation **)

    (* type_Rel *)
    + assert (isdecl' : n < #|Γ'|).
      { destruct hΓ as [iΓ _]. now rewrite <- (length_increl iΓ). }
      exists (lift0 (S n) (safe_nth Γ' (exist _ n isdecl'))), (sRel n).
      repeat split.
      * now destruct hΓ.
      * apply inrel_lift. apply nth_increl. now destruct hΓ.
      * constructor.
      * apply type_Rel. now destruct hΓ.

    (* type_Sort *)
    + exists (sSort (succ_sort s)), (sSort s).
      repeat split.
      * now destruct hΓ.
      * constructor.
      * constructor.
      * apply type_Sort. now destruct hΓ.

    (* type_Prod *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hb') as [T' [[b'' hb''] hh]].
      clear hb' b' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we conclude *)
      exists (sSort (max_sort s1 s2)), (sProd n t'' b'').
      now apply trans_Prod.

    (* type_Lambda *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ ht''))
        as [S' [bty' hbty']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hbty') as [T' [[bty'' hbty''] hh]].
      clear hbty' bty' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the term *)
      destruct (H1 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      destruct (change_type hg hb' hbty'') as [b'' hb''].
      clear hb' S' b'.
      exists (sProd n' t'' bty''), (sLambda n t'' bty'' b'').
      destruct ht'' as [[[? ?] ?] ?].
      destruct hbty'' as [[[? ?] ?] ?].
      destruct hb'' as [[[? ?] ?] ?].
      repeat split.
      * now destruct hΓ.
      * constructor ; eassumption.
      * constructor ; eassumption.
      * eapply type_Lambda ; eassumption.

    (* type_App *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the function *)
      destruct (H1 _ hΓ) as [T'' [t'' ht'']].
      assert (th : type_head (head (sProd n A B))) by constructor.
      destruct (choose_type hg th ht'') as [T' [[t' ht'] hh]].
      clear ht'' t'' T''.
      destruct T' ; inversion hh. subst. clear hh th.
      rename T'1 into A'', T'2 into B''.
      destruct (change_type hg ht' (trans_Prod hΓ hA' hB')) as [t'' ht''].
      clear ht' A'' B'' t'.
      (* Translation of the argument *)
      destruct (H2 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* We now conclude *)
      exists (B'{ 0 := u' }), (sApp t'' A' B' u').
      destruct hΓ.
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht'' as [[[? ?] ?] ?].
      destruct hu' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * now apply inrel_subst.
      * now constructor.
      * eapply type_App ; eassumption.

    (* type_Sum *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hb') as [T' [[b'' hb''] hh]].
      clear hb' b' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we conclude *)
      exists (sSort (max_sort s1 s2)), (sSum n t'' b'').
      now apply trans_Sum.

    (* type_Pair *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the first component *)
      destruct (H1 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* Translation of the second component *)
      destruct (H2 _ hΓ) as [Bv' [v'' hv'']].
      destruct (change_type hg hv'' (trans_subst hg hΓ hB' hu')) as [v' hv'].
      clear hv'' Bv' v''.
      (* Now we conclude *)
      exists (sSum n A' B'), (sPair A' B' u' v').
      destruct hΓ.
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct hu' as [[[? ?] ?] ?].
      destruct hv' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * eapply type_Pair' ; eassumption.

    (* type_Pi1 *)
    + (* Translation of the domain *)
      destruct (H0 _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H1 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the pair *)
      destruct (H _ hΓ) as [T'' [p'' hp'']].
      assert (th : type_head (head (sSum n A B))) by constructor.
      destruct (choose_type hg th hp'') as [T' [[p' hp'] hh]].
      clear hp'' p'' T''.
      destruct T' ; inversion hh. subst. clear hh th.
      rename T'1 into A'', T'2 into B''.
      destruct (change_type hg hp' (trans_Sum hΓ hA' hB')) as [p'' hp''].
      clear hp' A'' B'' p'.
    (* Now we conclude *)
      exists A', (sPi1 A' B' p'').
      destruct hp'' as [[[? ?] ?] hp'].
      destruct hA' as [[[? ?] ?] hA'].
      destruct hB' as [[[? ?] ?] hB'].
      repeat split.
      * assumption.
      * assumption.
      * constructor ; assumption.
      * eapply type_Pi1' ; eassumption.

    (* type_Pi2 *)
    + (* Translation of the domain *)
      destruct (H0 _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H1 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the pair *)
      destruct (H _ hΓ) as [T'' [p'' hp'']].
      assert (th : type_head (head (sSum n A B))) by constructor.
      destruct (choose_type hg th hp'') as [T' [[p' hp'] hh]].
      clear hp'' p'' T''.
      destruct T' ; inversion hh. subst. clear hh th.
      rename T'1 into A'', T'2 into B''.
      destruct (change_type hg hp' (trans_Sum hΓ hA' hB')) as [p'' hp''].
      clear hp' A'' B'' p'.
    (* Now we conclude *)
      exists (B'{ 0 := sPi1 A' B' p'' }), (sPi2 A' B' p'').
      destruct hp'' as [[[? ?] ?] hp'].
      destruct hA' as [[[? ?] ?] hA'].
      destruct hB' as [[[? ?] ?] hB'].
      repeat split.
      * assumption.
      * apply inrel_subst ; try assumption.
        constructor ; assumption.
      * constructor ; assumption.
      * eapply type_Pi2' ; eassumption.

    (* type_Eq *)
    + (* The type *)
      destruct (H _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA'') as [T [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T ; inversion hh. subst. clear hh th.
      (* The first term *)
      destruct (H0 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' u'' A''.
      (* The other term *)
      destruct (H1 _ hΓ) as [A'' [v'' hv'']].
      destruct (change_type hg hv'' hA') as [v' hv'].
      (* Now we conclude *)
      exists (sSort s), (sEq A' u' v').
      apply trans_Eq ; assumption.

    (* type_Refl *)
    + destruct (H0 _ hΓ) as [A' [u' hu']].
      exists (sEq A' u' u'), (sRefl A' u').
      destruct hu' as [[[? ?] ?] hu'].
      destruct hΓ.
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * destruct (istype_type hg hu').
        eapply type_Refl ; eassumption.

    (* type_Ax *)
    + exists ty, (sAx id).
      repeat split.
      * now destruct hΓ.
      * apply inrel_refl.
        eapply xcomp_ax_type ; eassumption.
      * constructor.
      * eapply type_Ax ; try eassumption.
        now destruct hΓ.

    (* type_conv *)
    + (* Translating the conversion *)
      destruct (H1 _ hΓ)
        as [S' [S'' [A'' [B'' [p' h']]]]].
      destruct (eqtrans_trans hg h') as [hA'' hB''].
      destruct h' as [[[[[eΓ eS'] eS''] eA] eB] hp'].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA'') as [T [[A' hA'] hh]].
      (* clear hA'' eS' eA A'' S'. *)
      destruct T ; inversion hh. subst. clear hh.
      destruct (choose_type hg th hB'') as [T [[B' hB'] hh]].
      (* clear hB'' eS'' eB B'' S''. *)
      destruct T ; inversion hh. subst. clear hh th.
      (* Translating the term *)
      destruct (H _ hΓ) as [A''' [t'' ht'']].
      destruct (change_type hg ht'' hA') as [t' ht'].
      assert (hpA : ∑ pA, Σ ;;; Γ' |-i pA : sHeq (sSort s) A' S' A'').
      { destruct hA' as [[_ eA'] hA'].
        destruct hA'' as [_ hA''].
        assert (hr : A' ∼ A'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pA hpA].
        exists pA. apply hpA ; assumption.
      }
      destruct hpA as [pA hpA].
      assert (hpB : ∑ pB, Σ ;;; Γ' |-i pB : sHeq S'' B'' (sSort s) B').
      { destruct hB' as [[_ eB'] hB'].
        destruct hB'' as [_ hB''].
        assert (hr : B'' ∼ B').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pB hpB].
        exists pB. apply hpB ; assumption.
      }
      destruct hpB as [pB hpB].
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq (sSort s) A' (sSort s) B').
      { exists (sHeqTrans pA (sHeqTrans p' pB)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; try eassumption.
      }
      destruct hq as [q hq].
      destruct (sort_heq_ex hg hq) as [e' he'].
      (* Now we conclude *)
      exists B', (sTransport A' B' e' t').
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht' as [[[? ?] ?] ?].
      repeat split ; try assumption.
      * constructor. assumption.
      * eapply type_Transport ; eassumption.

  (** eq_translation **)

    (* eq_reflexivity *)
    + destruct (H _ hΓ) as [A' [u' hu']].
      exists A', A', u', u', (sHeqRefl A' u').
      destruct hu' as [[[? ?] ?] hu'].
      repeat split ; try assumption.
      destruct (istype_type hg hu') as [s' hA'].
      eapply type_HeqRefl ; eassumption.

    (* eq_symmetry *)
    + destruct (H _ hΓ)
        as [A' [A'' [u' [v' [p' h']]]]].
      exists A'', A', v', u', (optHeqSym p').
      destruct h' as [[[[[? ?] ?] ?] ?] hp'].
      repeat split ; try assumption.
      eapply opt_HeqSym ; eassumption.

    (* eq_transitivity *)
    + destruct (H _ hΓ)
        as [A1 [A2 [u1 [v1 [p1 h1']]]]].
      destruct (H0 _ hΓ)
        as [A3 [A4 [v2 [w1 [p2 h2']]]]].
      destruct (eqtrans_trans hg h1') as [hu1 hv1].
      destruct (eqtrans_trans hg h2') as [hv2 hw1].
      destruct h1' as [[[[[? ?] ?] ?] ?] hp1].
      destruct h2' as [[[[[? ?] ?] ?] ?] hp2].
      (* We have a missing link between (v1 : A2) and (v2 : A3) *)
      assert (sim : v1 ∼ v2).
      { eapply trel_trans.
        - eapply trel_sym. eapply inrel_trel. eassumption.
        - apply inrel_trel. assumption.
      }
      destruct hv1 as [_ hv1].
      destruct hv2 as [_ hv2].
      destruct (trel_to_heq Γ' hg sim) as [p3 hp3].
      (* We can conclude *)
      exists A1, A4, u1, w1.
      exists (sHeqTrans p1 (sHeqTrans p3 p2)).
      repeat split ; try assumption.
      specialize (hp3 _ _ hv1 hv2).
      eapply type_HeqTrans' ; try assumption.
      * eassumption.
      * eapply type_HeqTrans' ; eassumption.

    (* eq_beta *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the in-term *)
      destruct (H1 _ (trans_snoc hΓ hA'))
        as [T' [t'' ht'']].
      destruct (change_type hg ht'' hB') as [t' ht'].
      clear ht'' T' t''.
      (* Translation of the argument *)
      destruct (H2 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* Now we conclude using reflexivity *)
      exists (B'{0 := u'}), (B'{0 := u'}).
      exists (sApp (sLambda n A' B' t') A' B' u'), (t'{0 := u'}).
      exists (sHeqRefl (B'{0 := u'}) (t'{0 := u'})).
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht' as [[[? ?] ?] ?].
      destruct hu' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * eapply inrel_subst ; assumption.
      * eapply inrel_subst ; assumption.
      * constructor ; try assumption.
        constructor ; assumption.
      * eapply inrel_subst ; assumption.
      * eapply type_conv.
        -- apply @type_HeqRefl with (s := s2).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ eapply typing_subst ; eassumption.
        -- apply @type_Heq with (s := s2).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ eapply type_App. all: try eassumption.
              eapply type_Lambda. all: eassumption.
           ++ eapply typing_subst ; eassumption.
        -- apply cong_Heq.
           all: try (apply conv_refl).
           eapply conv_red_r ; [| econstructor ].
           apply conv_refl.

    (* eq_conv *)
    + (* Translating the conversion *)
      destruct (H0 _ hΓ)
        as [S' [S'' [T1'' [T2'' [p' h']]]]].
      destruct (eqtrans_trans hg h') as [hT1'' hT2''].
      destruct h' as [[[[[eΓ eS'] eS''] eT1] eT2] hp'].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hT1'') as [T [[T1' hT1'] hh]].
      destruct T ; inversion hh. subst. clear hh.
      destruct (choose_type hg th hT2'') as [T [[T2' hT2'] hh]].
      destruct T ; inversion hh. subst. clear hh th.
      (* Translation the term conversion *)
      destruct (H _ hΓ)
        as [T1''' [T2''' [t1'' [t2'' [q' hq']]]]].
      destruct (eqtrans_trans hg hq') as [ht1'' ht2''].
      destruct (change_type hg ht1'' hT1') as [t1' ht1'].
      destruct (change_type hg ht2'' hT1') as [t2' ht2'].
      (* clear ht1'' ht2'' hq' T1''' T2''' t1'' t2'' q'. *)
      destruct hq' as [[[[[_ eT1'''] eT2'''] et1''] et2''] hq'].
      (* Building the intermediary paths *)
      assert (hpT1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s) T1' S' T1'').
      { destruct hT1' as [[_ eT1'] hT1'].
        destruct hT1'' as [_ hT1''].
        assert (hr : T1' ∼ T1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [p1 hp1].
        exists p1. apply hp1 ; assumption.
      }
      destruct hpT1 as [p1 hp1].
      assert (hp2 : ∑ p2, Σ ;;; Γ' |-i p2 : sHeq S'' T2'' (sSort s) T2').
      { destruct hT2' as [[_ eT2'] hT2'].
        destruct hT2'' as [_ hT2''].
        assert (hr : T2'' ∼ T2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [p2 hp2].
        exists p2. apply hp2 ; assumption.
      }
      destruct hp2 as [p2 hp2].
      assert (he : ∑ e, Σ ;;; Γ' |-i e : sHeq (sSort s) T1' (sSort s) T2').
      { exists (sHeqTrans p1 (sHeqTrans p' p2)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; try eassumption.
      }
      destruct he as [e' he'].
      rename e into eqt.
      destruct (sort_heq_ex hg he') as [e he].
      (* Likewise, we build paths for the terms *)
      assert (hq1 : ∑ q1, Σ ;;; Γ' |-i q1 : sHeq T1' t1' T1''' t1'').
      { destruct ht1' as [[_ et1'] ht1'].
        destruct ht1'' as [_ ht1''].
        assert (hr : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [q1 hq1].
        exists q1. apply hq1 ; assumption.
      }
      destruct hq1 as [q1 hq1].
      assert (hq2 : ∑ q2, Σ ;;; Γ' |-i q2 : sHeq T2''' t2'' T1' t2').
      { destruct ht2' as [[_ et2'] ht2'].
        destruct ht2'' as [_ ht2''].
        assert (hr : t2'' ∼ t2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [q2 hq2].
        exists q2. apply hq2 ; assumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hqq : ∑ qq, Σ ;;; Γ' |-i qq : sHeq T1' t1' T1' t2').
      { exists (sHeqTrans q1 (sHeqTrans q' q2)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; try eassumption.
      }
      destruct hqq as [qq hqq].
      assert (hql : ∑ ql, Σ ;;; Γ' |-i ql : sHeq T2' (sTransport T1' T2' e t1') T1' t1').
      { exists (sHeqSym (sHeqTransport e t1')).
        destruct ht1' as [_ ht1'].
        eapply type_HeqSym' ; try assumption.
        eapply type_HeqTransport' ; eassumption.
      }
      destruct hql as [ql hql].
      assert (hqr : ∑ qr, Σ ;;; Γ' |-i qr : sHeq T1' t2' T2' (sTransport T1' T2' e t2')).
      { exists (sHeqTransport e t2').
        destruct ht2' as [_ ht2'].
        eapply type_HeqTransport' ; eassumption.
      }
      destruct hqr as [qr hqr].
      assert (hqf : ∑ qf, Σ ;;; Γ' |-i qf
                                    : sHeq T2' (sTransport T1' T2' e t1')
                                           T2' (sTransport T1' T2' e t2')).
      { exists (sHeqTrans (sHeqTrans ql qq) qr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - assumption.
      }
      destruct hqf as [qf hqf].
      (* Now we conclude *)
      exists T2', T2', (sTransport T1' T2' e t1'), (sTransport T1' T2' e t2').
      exists qf.
      destruct hT1' as [[[? ?] ?] ?].
      destruct hT2' as [[[? ?] ?] ?].
      destruct ht1' as [[[? ?] ?] ?].
      destruct ht2' as [[[? ?] ?] ?].
      repeat split ; try eassumption.
      * econstructor. assumption.
      * econstructor. assumption.

    (* cong_Prod *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr') as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, A1').
      pose (Γ2 := nil ,, A2').
      pose (Γm := [ (sPack A1' A2') ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil sterm| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil sterm| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H2 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        assert (hr : B2' ∼ tB2).
        { destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p4 hp4].
        exists p4. apply hp4.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* We can finally conclude! *)
      exists (sSort (max_sort s1 s2)), (sSort (max_sort s1 s2)).
      exists (sProd n1 A1' B1'), (sProd n2 A2' tB2).
      exists (sCongProd B1' tB2 p1 p5).
      destruct hA1' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct htB2 as [[[? ?] ?] ?].
      repeat split ; [ try constructor .. |].
      all: try assumption.
      eapply type_CongProd' ; try assumption.
      cbn in hp5. rewrite <- llift_substProj, <- rlift_substProj in hp5.
      rewrite !llift00, !rlift00 in hp5.
      apply hp5.

    (* cong_Lambda *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, A1').
      pose (Γ2 := nil ,, A2').
      pose (Γm := [ sPack A1' A2' ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil sterm| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil sterm| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H3 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        assert (hr : B2' ∼ tB2).
        { destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p4 hp4].
        exists p4. apply hp4.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hp2 p2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_5 B1'' pi2_6 B2''.
      rename p1 into pA, p5 into pB, hp1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now focus on the function terms *)
      destruct (H1 _ (trans_snoc hΓ hA1'))
        as [B1'' [B1''' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [ht1'' ht2''].
      destruct (change_type hg ht1'' hB1') as [t1' ht1'].
      destruct (change_type hg ht2'' hB1') as [t2' ht2'].
      destruct (H5 _ (trans_snoc hΓ hA2'))
        as [B2'' [t2''' ht2''']].
      destruct (change_type hg ht2''' hB2') as [tt2 htt2].
      assert (hq1 : ∑ q1, Σ ;;; Γ' ,, A1' |-i q1 : sHeq B1' t1' B1' t2').
      { destruct h3' as [[[[[? ?] ?] ?] ?] hpt''].
        destruct ht1' as [[_ et1'] ht1'].
        destruct ht1'' as [_ ht1''].
        destruct ht2' as [[_ et2'] ht2'].
        destruct ht2'' as [_ ht2''].
        assert (hr : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : t2'' ∼ t2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pt) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - assumption.
      }
      destruct hq1 as [q1 hq1].
      assert (hq2 : ∑ q2,
        Σ ;;; Δ |-i q2 : sHeq (llift0 #|Γm| B1') (llift0 #|Γm| t1')
                             (llift0 #|Γm| B1') (llift0 #|Γm| t2')
      ).
      { exists (llift0 #|Γm| q1).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq B1' t1' B1' t2'))
        end.
        eapply type_llift0 ; try eassumption.
        assumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hq3 : ∑ q3,
        Σ ;;; Δ |-i q3 : sHeq (llift0 #|Γm| B1') (llift0 #|Γm| t2')
                             (rlift0 #|Γm| B2') (rlift0 #|Γm| tt2)
      ).
      { assert (hr : t2' ∼ tt2).
        { destruct htt2 as [[? ?] ?].
          destruct ht2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p3 hp3].
        exists p3. apply hp3.
        - eassumption.
        - destruct ht2' as [[? ?] ?]. assumption.
        - destruct htt2 as [[? ?] ?]. assumption.
      }
      destruct hq3 as [q3 hq3].
      assert (hq4 : ∑ q4,
        Σ ;;; Δ |-i q4 : sHeq (llift0 #|Γm| B1') (llift0 #|Γm| t1')
                             (rlift0 #|Γm| B2') (rlift0 #|Γm| tt2)
      ).
      { exists (sHeqTrans q2 q3).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hq4 as [qt hqt].
      (* We're almost done.
         However, our translation of (sLambda n2 A2 B2 t2) has to live in
         our translation of (sProd n' A1 B1).
         This is where the path between the two types comes into action.
       *)
      assert (hty : ∑ pty,
        Σ ;;; Γ' |-i pty : sHeq (sSort (max_sort s1 s2)) (sProd n2 A2' B2')
                               (sSort (max_sort s1 s2)) (sProd n1 A1' B1')

      ).
      { exists (sHeqSym (sCongProd B1' B2' pA pB)).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_HeqSym' ; try assumption.
        eapply type_CongProd' ; try assumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct hty as [pty hty].
      destruct (sort_heq_ex hg hty) as [eT heT].
      (* We move the lambda now. *)
      pose (tλ :=
              sTransport (sProd n2 A2' B2') (sProd n1 A1' B1')
                         eT (sLambda n2 A2' B2' tt2)
      ).
      (* Now we conclude *)
      exists (sProd n1 A1' B1'), (sProd n1 A1' B1').
      exists (sLambda n1 A1' B1' t1'), tλ.
      exists (sHeqTrans (sCongLambda B1' B2' t1' tt2 pA pB qt)
                   (sHeqTransport eT (sLambda n2 A2' B2' tt2))).
      destruct ht1' as [[[? ?] ?] ?].
      destruct htt2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans' ; try assumption.
        -- eapply type_CongLambda' ; try eassumption.
           ++ cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
              rewrite !llift00, !rlift00 in hpB.
              apply hpB.
           ++ cbn in hqt. rewrite <- !llift_substProj, <- !rlift_substProj in hqt.
              rewrite !llift00, !rlift00 in hqt.
              apply hqt.
        -- eapply type_HeqTransport' ; try assumption.
           ++ eapply type_Lambda ; eassumption.
           ++ eassumption.

    (* cong_App *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, A1').
      pose (Γ2 := nil ,, A2').
      pose (Γm := [ sPack A1' A2' ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil sterm| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil sterm| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H4 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        assert (hr : B2' ∼ tB2).
        { destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p4 hp4].
        exists p4. apply hp4.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hp2 p2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_1 pi2_2 A1'' A2''.
      rename p1 into pA, p5 into pB, hp1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now translate the functions. *)
      destruct (H1 _ hΓ)
        as [P1 [P1' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [ht1'' ht2''].
      destruct (change_type hg ht1'' (trans_Prod hΓ hA1' hB1')) as [t1' ht1'].
      destruct (change_type hg ht2'' (trans_Prod hΓ hA1' hB1')) as [t2' ht2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (H6 _ hΓ)
        as [P2 [t2''' ht2''']].
      destruct (change_type hg ht2''' (trans_Prod hΓ hA2' hB2')) as [tt2 htt2].
      clear ht2''' t2''' P2.
      assert (hqt : ∑ qt,
        Σ ;;; Γ' |-i qt : sHeq (sProd n1 A1' B1') t1' (sProd n2 A2' B2') tt2
      ).
      { destruct ht1'' as [[[? ?] ?] ?].
        destruct ht2'' as [[[? ?] ?] ?].
        destruct ht1' as [[[? ?] ?] ?].
        destruct ht2' as [[[? ?] ?] ?].
        destruct htt2 as [[[? ?] ?] ?].
        assert (r1 : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r1) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (r2 : t2'' ∼ tt2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r2) as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans pl (sHeqTrans pt pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We then translate the arguments. *)
      destruct (H2 _ hΓ)
        as [A1'' [A1''' [u1'' [u2'' [pu h4']]]]].
      destruct (eqtrans_trans hg h4') as [hu1'' hu2''].
      destruct (change_type hg hu1'' hA1') as [u1' hu1'].
      destruct h4' as [[[[[? ?] ?] ?] ?] hpu].
      destruct (H8 _ hΓ) as [A2'' [u2''' hu2''']].
      destruct (change_type hg hu2''' hA2') as [tu2 htu2].
      clear hu2''' u2''' A2''.
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq A1' u1' A2' tu2).
      { destruct hu1'' as [[[? ?] ?] ?].
        destruct hu2'' as [[[? ?] ?] ?].
        destruct hu1' as [[[? ?] ?] ?].
        destruct htu2 as [[[? ?] ?] ?].
        assert (r1 : u1' ∼ u1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r1) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (r2 : u2'' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r2) as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans pl (sHeqTrans pu pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqu as [qu hqu].
      (* We have an equality between Apps now *)
      assert (happ : ∑ qapp,
        Σ ;;; Γ' |-i qapp : sHeq (B1'{0 := u1'}) (sApp t1' A1' B1' u1')
                                (B2'{0 := tu2}) (sApp tt2 A2' B2' tu2)
      ).
      { exists (sCongApp B1' B2' qt pA pB qu).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_CongApp' ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct happ as [qapp happ].
      (* Finally we translate the right App to put it in the left Prod *)
      rename e into eA.
      pose (e := sHeqTypeEq (B2' {0 := tu2}) (B1'{0 := u1'}) (sHeqSym qapp)).
      pose (tapp := sTransport (B2' {0 := tu2}) (B1'{0 := u1'}) e (sApp tt2 A2' B2' tu2)).
      (* We conclude *)
      exists (B1'{0 := u1'}), (B1'{0 := u1'}).
      exists (sApp t1' A1' B1' u1'), tapp.
      exists (sHeqTrans qapp (sHeqTransport e (sApp tt2 A2' B2' tu2))).
      destruct ht1' as [[[? ?] ?] ?].
      destruct htt2 as [[[? ?] ?] ?].
      destruct hu1' as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * eapply inrel_subst ; assumption.
      * eapply inrel_subst ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans' ; try eassumption.
        eapply type_HeqTransport' ; try assumption.
        -- eapply type_App ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply type_HeqSym' ; eassumption.
           ++ match goal with
              | |- _ ;;; _ |-i _ : ?S =>
                change S with (S {0 := tu2})
              end.
              eapply typing_subst ; eassumption.

    (* cong_Sum *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr') as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, A1').
      pose (Γ2 := nil ,, A2').
      pose (Γm := [ (sPack A1' A2') ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil sterm| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil sterm| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H2 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        assert (hr : B2' ∼ tB2).
        { destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p4 hp4].
        exists p4. apply hp4.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* We can finally conclude! *)
      exists (sSort (max_sort s1 s2)), (sSort (max_sort s1 s2)).
      exists (sSum n1 A1' B1'), (sSum n2 A2' tB2).
      exists (sCongSum B1' tB2 p1 p5).
      destruct hA1' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct htB2 as [[[? ?] ?] ?].
      repeat split ; [ try constructor .. |].
      all: try assumption.
      eapply type_CongSum' ; try assumption.
      cbn in hp5. rewrite <- llift_substProj, <- rlift_substProj in hp5.
      rewrite !llift00, !rlift00 in hp5.
      apply hp5.

    (* cong_Pair *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hq1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hq1 as [q1 hq1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, A1').
      pose (Γ2 := nil ,, A2').
      pose (Γm := [ sPack A1' A2' ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil sterm| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil sterm| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hq2 : ∑ q2, Σ ;;; Γ' ,,, Γ1 |-i q2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| q2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H4 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        assert (hr : B2' ∼ tB2).
        { destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p4 hp4].
        exists p4. apply hp4.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hq2 q2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_1 pi2_2 A1'' A2''.
      rename q1 into pA, p5 into pB, hq1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now translate the first components. *)
      destruct (H1 _ hΓ)
        as [P1 [P1' [u1'' [u2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [hu1'' hu2''].
      destruct (change_type hg hu1'' hA1') as [u1' hu1'].
      destruct (change_type hg hu2'' hA1') as [u2' hu2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpu].
      destruct (H6 _ hΓ)
        as [P2 [u2''' hu2''']].
      destruct (change_type hg hu2''' hA2') as [tu2 htu2].
      clear hu2''' u2''' P2.
      assert (hqt : ∑ qt,
        Σ ;;; Γ' |-i qt : sHeq A1' u1' A2' tu2
      ).
      { destruct hu1'' as [[[? ?] ?] ?].
        destruct hu2'' as [[[? ?] ?] ?].
        destruct hu1' as [[[? ?] ?] ?].
        destruct hu2' as [[[? ?] ?] ?].
        destruct htu2 as [[[? ?] ?] ?].
        assert (r1 : u1' ∼ u1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r1) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (r2 : u2'' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r2) as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans pl (sHeqTrans pt pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We can now translate the second components. *)
      destruct (H2 _ hΓ)
        as [Q1 [Q1' [v1'' [v2'' [pt' h3']]]]].
      destruct (eqtrans_trans hg h3') as [hv1'' hv2''].
      destruct (change_type hg hv1'' (trans_subst hg hΓ hB1' hu1'))
        as [v1' hv1'].
      destruct (change_type hg hv2'' (trans_subst hg hΓ hB1' hu1'))
        as [v2' hv2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpv].
      destruct (H8 _ hΓ)
        as [Q2 [v2''' hv2''']].
      destruct (change_type hg hv2''' (trans_subst hg hΓ hB2' htu2))
        as [tv2 htv2].
      clear hv2''' v2''' Q2.
      assert (hqt' : ∑ qt,
        Σ ;;; Γ' |-i qt : sHeq (B1'{0 := u1'}) v1' (B2'{0 := tu2}) tv2
      ).
      { destruct hv1'' as [[[? ?] ?] ?].
        destruct hv2'' as [[[? ?] ?] ?].
        destruct hv1' as [[[? ?] ?] ?].
        destruct hv2' as [[[? ?] ?] ?].
        destruct htv2 as [[[? ?] ?] ?].
        assert (r1 : v1' ∼ v1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r1) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (r2 : v2'' ∼ tv2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r2) as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans pl (sHeqTrans pt' pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqt' as [qt' hqt'].
      (* We have an equality between Pairs now *)
      assert (hpi : ∑ qpi,
        Σ ;;; Γ' |-i qpi : sHeq (sSum n A1' B1') (sPair A1' B1' u1' v1')
                               (sSum n A2' B2') (sPair A2' B2' tu2 tv2)
      ).
      { exists (sCongPair B1' B2' pA pB qt qt').
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_CongPair' ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct hpi as [qpi hpi].
      (* Finally we translate the right Pair to put it in the left Sum *)
      rename e into eA.
      pose (e := sHeqTypeEq (sSum n A2' B2') (sSum n A1' B1') (sHeqSym qpi)).
      pose (tpi := sTransport (sSum n A2' B2') (sSum n A1' B1') e (sPair A2' B2' tu2 tv2)).
      (* We conclude *)
      exists (sSum n A1' B1'), (sSum n A1' B1').
      exists (sPair A1' B1' u1' v1'), tpi.
      exists (sHeqTrans qpi (sHeqTransport e (sPair A2' B2' tu2 tv2))).
      destruct hu1' as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct hv1' as [[[? ?] ?] ?].
      destruct htv2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans' ; try eassumption.
        eapply type_HeqTransport' ; try assumption.
        -- eapply type_Pair' ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply type_HeqSym' ; eassumption.
           ++ eapply type_Sum ; eassumption.

    (* cong_Pi1 *)
    + (* The domains *)
      destruct (H0 _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H1 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hq1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hq1 as [q1 hq1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, A1').
      pose (Γ2 := nil ,, A2').
      pose (Γm := [ sPack A1' A2' ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil sterm| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil sterm| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hq2 : ∑ q2, Σ ;;; Γ' ,,, Γ1 |-i q2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| q2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H3 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        assert (hr : B2' ∼ tB2).
        { destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p4 hp4].
        exists p4. apply hp4.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hq2 q2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_1 pi2_2 A1'' A2''.
      rename q1 into pA, p5 into pB, hq1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now translate the pairs. *)
      destruct (H _ hΓ)
        as [P1 [P1' [p1'' [p2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [hp1'' hp2''].
      destruct (change_type hg hp1'' (trans_Sum hΓ hA1' hB1')) as [p1' hp1'].
      destruct (change_type hg hp2'' (trans_Sum hΓ hA1' hB1')) as [p2' hp2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (H5 _ hΓ)
        as [P2 [p2''' hp2''']].
      destruct (change_type hg hp2''' (trans_Sum hΓ hA2' hB2')) as [tp2 htp2].
      clear hp2''' p2''' P2.
      assert (hqt : ∑ qt,
        Σ ;;; Γ' |-i qt : sHeq (sSum nx A1' B1') p1' (sSum ny A2' B2') tp2
      ).
      { destruct hp1'' as [[[? ?] ?] ?].
        destruct hp2'' as [[[? ?] ?] ?].
        destruct hp1' as [[[? ?] ?] ?].
        destruct hp2' as [[[? ?] ?] ?].
        destruct htp2 as [[[? ?] ?] ?].
        assert (r1 : p1' ∼ p1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r1) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (r2 : p2'' ∼ tp2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r2) as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans pl (sHeqTrans pt pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We have an equality between Pi1s now *)
      assert (hpi : ∑ qpi,
        Σ ;;; Γ' |-i qpi : sHeq A1' (sPi1 A1' B1' p1')
                               A2' (sPi1 A2' B2' tp2)
      ).
      { exists (sCongPi1 B1' B2' pA pB qt).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_CongPi1' ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct hpi as [qpi hpi].
      (* Finally we translate the right Pi1 to put it in the left Sum *)
      rename e into eA.
      pose (e := sHeqTypeEq A2' A1' (sHeqSym qpi)).
      pose (tpi := sTransport A2' A1' e (sPi1 A2' B2' tp2)).
      (* We conclude *)
      exists A1', A1'.
      exists (sPi1 A1' B1' p1'), tpi.
      exists (sHeqTrans qpi (sHeqTransport e (sPi1 A2' B2' tp2))).
      destruct hp1' as [[[? ?] ?] ?].
      destruct htp2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * assumption.
      * assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans' ; try eassumption.
        eapply type_HeqTransport' ; try assumption.
        -- eapply type_Pi1' ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply type_HeqSym' ; eassumption.
           ++ eassumption.

    (* cong_Pi2 *)
    + (* The domains *)
      destruct (H0 _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H1 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hq1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hq1 as [q1 hq1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, A1').
      pose (Γ2 := nil ,, A2').
      pose (Γm := [ sPack A1' A2' ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil sterm| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil sterm| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hq2 : ∑ q2, Σ ;;; Γ' ,,, Γ1 |-i q2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq (Γ',, A1') hg hr') as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| q2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H3 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        assert (hr : B2' ∼ tB2).
        { destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        }
        edestruct (trel_to_heq' hg hr) as [p4 hp4].
        exists p4. apply hp4.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hq2 q2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_1 pi2_2 A1'' A2''.
      rename q1 into pA, p5 into pB, hq1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now translate the pairs. *)
      destruct (H _ hΓ)
        as [P1 [P1' [p1'' [p2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [hp1'' hp2''].
      destruct (change_type hg hp1'' (trans_Sum hΓ hA1' hB1')) as [p1' hp1'].
      destruct (change_type hg hp2'' (trans_Sum hΓ hA1' hB1')) as [p2' hp2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (H5 _ hΓ)
        as [P2 [p2''' hp2''']].
      destruct (change_type hg hp2''' (trans_Sum hΓ hA2' hB2')) as [tp2 htp2].
      clear hp2''' p2''' P2.
      assert (hqt : ∑ qt,
        Σ ;;; Γ' |-i qt : sHeq (sSum nx A1' B1') p1' (sSum ny A2' B2') tp2
      ).
      { destruct hp1'' as [[[? ?] ?] ?].
        destruct hp2'' as [[[? ?] ?] ?].
        destruct hp1' as [[[? ?] ?] ?].
        destruct hp2' as [[[? ?] ?] ?].
        destruct htp2 as [[[? ?] ?] ?].
        assert (r1 : p1' ∼ p1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r1) as [pl hpl].
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        assert (r2 : p2'' ∼ tp2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq Γ' hg r2) as [pr hpr].
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        exists (sHeqTrans pl (sHeqTrans pt pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We have an equality between Pi1s now *)
      assert (hpi : ∑ qpi,
        Σ ;;; Γ' |-i qpi : sHeq (B1'{ 0 := sPi1 A1' B1' p1' }) (sPi2 A1' B1' p1')
                               (B2'{ 0 := sPi1 A2' B2' tp2 }) (sPi2 A2' B2' tp2)
      ).
      { exists (sCongPi2 B1' B2' pA pB qt).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_CongPi2' ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct hpi as [qpi hpi].
      (* Finally we translate the right Pi1 to put it in the left Sum *)
      rename e into eA.
      pose (e := sHeqTypeEq (B2' {0 := sPi1 A2' B2' tp2}) (B1' {0 := sPi1 A1' B1' p1'}) (sHeqSym qpi)).
      pose (tpi := sTransport (B2' {0 := sPi1 A2' B2' tp2}) (B1' {0 := sPi1 A1' B1' p1'}) e (sPi2 A2' B2' tp2)).
      (* We conclude *)
      exists (B1'{ 0 := sPi1 A1' B1' p1' }), (B1'{ 0 := sPi1 A1' B1' p1' }).
      exists (sPi2 A1' B1' p1'), tpi.
      exists (sHeqTrans qpi (sHeqTransport e (sPi2 A2' B2' tp2))).
      destruct hp1' as [[[? ?] ?] ?].
      destruct htp2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * apply inrel_subst ; try assumption.
        constructor ; assumption.
      * apply inrel_subst ; try assumption.
        constructor ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans' ; try eassumption.
        eapply type_HeqTransport' ; try assumption.
        -- eapply type_Pi2' ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply type_HeqSym' ; eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              eapply type_Pi1' ; eassumption.

    (* cong_Eq *)
    + destruct (H _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (H0 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (H1 _ hΓ)
        as [A1'''' [A1''''' [v1' [v2' [pv h3']]]]].
      destruct (eqtrans_trans hg h1') as [hA1' hA2'].
      destruct (eqtrans_trans hg h2') as [hu1' hu2'].
      destruct (eqtrans_trans hg h3') as [hv1' hv2'].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA].
      destruct h2' as [[[[[? ?] ?] ?] ?] hpu].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpv].
      (* We need to chain translations a lot to use sCongEq *)
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA1') as [T' [[tA1 htA1] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA2') as [T' [[tA2 htA2] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      (* For the types we build the missing hequalities *)
      assert (hp : ∑ p, Σ ;;; Γ' |-i p : sHeq (sSort s) tA1 (sSort s) tA2).
      { destruct hA1' as [_ hA1'].
        destruct htA1 as [[[? ?] ?] htA1].
        assert (sim1 : tA1 ∼ A1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim1) as [p1 hp1].
        specialize (hp1 _ _  htA1 hA1').
        destruct hA2' as [_ hA2'].
        destruct htA2 as [[[? ?] ?] htA2].
        assert (sim2 : A2' ∼ tA2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim2) as [p2 hp2].
        specialize (hp2 _ _ hA2' htA2).
        exists (sHeqTrans p1 (sHeqTrans pA p2)).
        eapply type_HeqTrans' ; try eassumption.
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp as [qA hqA].
      (* Now we need to do the same for the terms *)
      destruct (change_type hg hu1' htA1) as [tu1 htu1].
      destruct (change_type hg hu2' htA1) as [tu2 htu2].
      destruct (change_type hg hv1' htA1) as [tv1 htv1].
      destruct (change_type hg hv2' htA1) as [tv2 htv2].
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq tA1 tu1 tA1 tu2).
      { destruct hu1' as [_ hu1'].
        destruct htu1 as [[[? ?] ?] htu1].
        assert (sim1 : tu1 ∼ u1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim1) as [pl hpl].
        specialize (hpl _ _ htu1 hu1').
        destruct hu2' as [_ hu2'].
        destruct htu2 as [[[? ?] ?] htu2].
        assert (sim2 : u2' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim2) as [pr hpr].
        specialize (hpr _ _ hu2' htu2).
        exists (sHeqTrans (sHeqTrans pl pu) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqu as [qu hqu].
      assert (hqv : ∑ qv, Σ ;;; Γ' |-i qv : sHeq tA1 tv1 tA1 tv2).
      { destruct hv1' as [_ hv1'].
        destruct htv1 as [[[? ?] ?] htv1].
        assert (sim1 : tv1 ∼ v1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim1) as [pl hpl].
        specialize (hpl _ _ htv1 hv1').
        destruct hv2' as [_ hv2'].
        destruct htv2 as [[[? ?] ?] htv2].
        assert (sim2 : v2' ∼ tv2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim2) as [pr hpr].
        specialize (hpr _ _ hv2' htv2).
        exists (sHeqTrans (sHeqTrans pl pv) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqv as [qv hqv].
      (* We move terms back into tA2 *)
      destruct (sort_heq_ex hg hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (sHeqTrans qu (sHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [qu' hqu'].
      pose (ttv2 := sTransport tA1 tA2 eA tv2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tv1 tA2 ttv2).
      { exists (sHeqTrans qv (sHeqTransport eA tv2)).
        destruct htv2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [qv' hqv'].
      exists (sSort s), (sSort s), (sEq tA1 tu1 tv1), (sEq tA2 ttu2 ttv2).
      exists (sCongEq qA qu' qv').
      destruct htu1 as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct htA1 as [[[? ?] ?] ?].
      destruct htA2 as [[[? ?] ?] ?].
      destruct htv1 as [[[? ?] ?] ?].
      destruct htv2 as [[[? ?] ?] ?].
      repeat split ; try eassumption.
      * econstructor ; assumption.
      * econstructor ; try assumption.
        -- econstructor ; eassumption.
        -- econstructor ; eassumption.
      * eapply type_CongEq' ; assumption.

    (* cong_Refl *)
    + destruct (H _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (H0 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (eqtrans_trans hg h1') as [hA1' hA2'].
      destruct (eqtrans_trans hg h2') as [hu1' hu2'].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA].
      destruct h2' as [[[[[? ?] ?] ?] ?] hpu].
      (* The types *)
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA1') as [T' [[tA1 htA1] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA2') as [T' [[tA2 htA2] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (hp : ∑ p, Σ ;;; Γ' |-i p : sHeq (sSort s) tA1 (sSort s) tA2).
      { destruct hA1' as [_ hA1'].
        destruct htA1 as [[[? ?] ?] htA1].
        assert (sim1 : tA1 ∼ A1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim1) as [p1 hp1].
        specialize (hp1 _ _ htA1 hA1').
        destruct hA2' as [_ hA2'].
        destruct htA2 as [[[? ?] ?] htA2].
        assert (sim2 : A2' ∼ tA2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim2) as [p2 hp2].
        specialize (hp2 _ _ hA2' htA2).
        exists (sHeqTrans p1 (sHeqTrans pA p2)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hp as [qA hqA].
      (* The terms *)
      destruct (change_type hg hu1' htA1) as [tu1 htu1].
      destruct (change_type hg hu2' htA1) as [tu2 htu2].
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq tA1 tu1 tA1 tu2).
      { destruct hu1' as [_ hu1'].
        destruct htu1 as [[[? ?] ?] htu1].
        assert (sim1 : tu1 ∼ u1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim1) as [pl hpl].
        specialize (hpl _ _ htu1 hu1').
        destruct hu2' as [_ hu2'].
        destruct htu2 as [[[? ?] ?] htu2].
        assert (sim2 : u2' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq Γ' hg sim2) as [pr hpr].
        specialize (hpr _ _ hu2' htu2).
        exists (sHeqTrans (sHeqTrans pl pu) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqu as [qu hqu].
      (* tu2 isn't in the right place, so we need to chain one last equality. *)
      destruct (sort_heq_ex hg hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (sHeqTrans qu (sHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [q hq].
      (* We're still not there yet as we need to have two translations of the
         same type. *)
      assert (pE : ∑ pE, Σ ;;; Γ' |-i pE : sHeq (sSort s) (sEq tA2 ttu2 ttu2)
                                               (sSort s) (sEq tA1 tu1 tu1)).
      { exists (sHeqSym (sCongEq qA q q)).
        eapply type_HeqSym' ; try assumption.
        eapply type_CongEq' ; eassumption.
      }
      destruct pE as [pE hpE].
      assert (eE : ∑ eE, Σ ;;; Γ' |-i eE : sEq (sSort s) (sEq tA2 ttu2 ttu2)
                                              (sEq tA1 tu1 tu1)).
      { eapply (sort_heq_ex hg hpE). }
      destruct eE as [eE hE].
      pose (trefl2 := sTransport (sEq tA2 ttu2 ttu2)
                                 (sEq tA1 tu1 tu1)
                                 eE (sRefl tA2 ttu2)
           ).
      exists (sEq tA1 tu1 tu1), (sEq tA1 tu1 tu1).
      exists (sRefl tA1 tu1), trefl2.
      exists (sHeqTrans (sCongRefl qA q) (sHeqTransport eE (sRefl tA2 ttu2))).
      destruct htu1 as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct htA1 as [[[? ?] ?] ?].
      destruct htA2 as [[[? ?] ?] ?].
      repeat split.
      all: try assumption.
      all: try (econstructor ; eassumption).
      * econstructor. econstructor.
        -- assumption.
        -- econstructor. assumption.
      * eapply type_HeqTrans' ; try assumption.
        -- eapply type_CongRefl' ; eassumption.
        -- eapply type_HeqTransport' ; try assumption.
           ++ eapply type_Refl' ; try assumption.
              eapply type_Transport' ; eassumption.
           ++ eassumption.

    (* reflection *)
    + destruct (H _ hΓ) as [T' [e'' he'']].
      assert (th : type_head (head (sEq A u v))) by constructor.
      destruct (choose_type hg th he'') as [T'' [[e' he'] hh]].
      destruct T'' ; try (now inversion hh).
      rename T''1 into A', T''2 into u', T''3 into v'.
      clear hh he'' e'' he'' T' th.
      destruct he' as [[[? ieq] ?] he'].
      exists A', A', u', v'.
      exists (sEqToHeq e').
      inversion ieq. subst.
      repeat split ; try eassumption.
      destruct (istype_type hg he') as [? heq].
      ttinv heq.
      eapply type_EqToHeq' ; assumption.

  Unshelve. all: try exact 0. exact nAnon.

Defined.

End Translation.