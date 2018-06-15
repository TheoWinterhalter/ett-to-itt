(*! Defining the reflection-free fragment of ETT and proving that translation
    behaves as the identity on the underlying terms. *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import utils Ast LiftSubst Typing Checker.
From Translation Require Import util Quotes SAst SLiftSubst SCommon ITyping
     ITypingInversions ITypingLemmata ITypingAdmissible Optim XTyping
     FundamentalLemma Translation.

(* Predicate describing the reflection free fragment. *)

Inductive itt_typing Σ : forall Γ t A, Σ ;;; Γ |-x t : A -> Type :=
| itt_Rel Γ n hw isdecl :
    itt_wf _ _ hw ->
    itt_typing _ _ _ _ (type_Rel Σ Γ n hw isdecl)

| itt_Sort Γ s hw :
    itt_wf _ _ hw ->
    itt_typing _ _ _ _ (type_Sort Σ Γ s hw)

| itt_Prod Γ n A B s1 s2 hA hB :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ (type_Prod Σ Γ n A B s1 s2 hA hB)

| itt_Lambda Γ n n' A t s1 s2 B hA hB ht :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ ht ->
    itt_typing _ _ _ _ (type_Lambda Σ Γ n n' A t s1 s2 B hA hB ht)

| itt_App Γ n s1 s2 t A B u hA hB ht hu :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ ht ->
    itt_typing _ _ _ _ hu ->
    itt_typing _ _ _ _ (type_App Σ Γ n s1 s2 t A B u hA hB ht hu)

| itt_Sum Γ n A B s1 s2 hA hB :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ (type_Sum Σ Γ n A B s1 s2 hA hB)

| itt_Pair Γ n A B u v s1 s2 hA hB hu hv :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ hu ->
    itt_typing _ _ _ _ hv ->
    itt_typing _ _ _ _ (type_Pair Σ Γ n A B u v s1 s2 hA hB hu hv)

| itt_Pi1 Γ n A B s1 s2 p hp hA hB :
    itt_typing _ _ _ _ hp ->
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ (type_Pi1 Σ Γ n A B s1 s2 p hp hA hB)

| itt_Pi2 Γ n A B s1 s2 p hp hA hB :
    itt_typing _ _ _ _ hp ->
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ (type_Pi2 Σ Γ n A B s1 s2 p hp hA hB)

| itt_Eq Γ s A u v hA hu hv :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hu ->
    itt_typing _ _ _ _ hv ->
    itt_typing _ _ _ _ (type_Eq Σ Γ s A u v hA hu hv)

| itt_Refl Γ s A u hA hu :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hu ->
    itt_typing _ _ _ _ (type_Refl Σ Γ s A u hA hu)

| itt_Ax Γ id ty hw lk :
    itt_wf _ _ hw ->
    itt_typing _ _ _ _ (type_Ax Σ Γ id ty hw lk)

| itt_conv Γ t A B s ht hB hconv :
    itt_typing _ _ _ _ ht ->
    itt_typing _ _ _ _ hB ->
    itt_eq_term _ _ _ _ _ hconv ->
    itt_typing _ _ _ _ (type_conv Σ Γ t A B s ht hB hconv)

with itt_eq_term Σ : forall Γ t u A, Σ ;;; Γ |-x t = u : A -> Type :=
| itt_reflexivity Γ u A hu :
    itt_typing _ _ _ _ hu ->
    itt_eq_term _ _ _ _ _ (eq_reflexivity Σ Γ u A hu)

| itt_symmetry Γ u v A h :
    itt_eq_term _ _ _ _ _ h ->
    itt_eq_term _ _ _ _ _ (eq_symmetry Σ Γ u v A h)

| itt_transitivity Γ u v w A h1 h2 :
    itt_eq_term _ _ _ _ _ h1 ->
    itt_eq_term _ _ _ _ _ h2 ->
    itt_eq_term _ _ _ _ _ (eq_transitivity Σ Γ u v w A h1 h2)

| itt_beta Γ s1 s2 n A B t u hA hB ht hu :
    itt_typing _ _ _ _ hA ->
    itt_typing _ _ _ _ hB ->
    itt_typing _ _ _ _ ht ->
    itt_typing _ _ _ _ hu ->
    itt_eq_term _ _ _ _ _ (eq_beta Σ Γ s1 s2 n A B t u hA hB ht hu)

| itt_eq_conv Γ s T1 T2 t1 t2 ht hT :
    itt_eq_term _ _ _ _ _ ht ->
    itt_eq_term _ _ _ _ _ hT ->
    itt_eq_term _ _ _ _ _ (eq_conv Σ Γ s T1 T2 t1 t2 ht hT)

| itt_cong_Prod Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2 :
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hB ->
    itt_typing _ _ _ _ hB1 ->
    itt_typing _ _ _ _ hB2 ->
    itt_eq_term _ _ _ _ _ (cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2)

| itt_cong_Lambda Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 hA hB ht hB1 hB2 ht1 ht2 :
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hB ->
    itt_eq_term _ _ _ _ _ ht ->
    itt_typing _ _ _ _ hB1 ->
    itt_typing _ _ _ _ hB2 ->
    itt_typing _ _ _ _ ht1 ->
    itt_typing _ _ _ _ ht2 ->
    itt_eq_term _ _ _ _ _ (cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 hA hB ht hB1 hB2 ht1 ht2)

| itt_cong_App Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 hA hB ht hu hB1 hB2 ht1 ht2 hu1 hu2 :
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hB ->
    itt_eq_term _ _ _ _ _ ht ->
    itt_eq_term _ _ _ _ _ hu ->
    itt_typing _ _ _ _ hB1 ->
    itt_typing _ _ _ _ hB2 ->
    itt_typing _ _ _ _ ht1 ->
    itt_typing _ _ _ _ ht2 ->
    itt_typing _ _ _ _ hu1 ->
    itt_typing _ _ _ _ hu2 ->
    itt_eq_term _ _ _ _ _ (cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 hA hB ht hu hB1 hB2 ht1 ht2 hu1 hu2)

| itt_cong_Sum Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2 :
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hB ->
    itt_typing _ _ _ _ hB1 ->
    itt_typing _ _ _ _ hB2 ->
    itt_eq_term _ _ _ _ _ (cong_Sum Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2)

| itt_cong_Pair Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 hA hB hu hv hB1 hB2 hu1 hu2 hv1 hv2 :
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hB ->
    itt_eq_term _ _ _ _ _ hu ->
    itt_eq_term _ _ _ _ _ hv ->
    itt_typing _ _ _ _ hB1 ->
    itt_typing _ _ _ _ hB2 ->
    itt_typing _ _ _ _ hu1 ->
    itt_typing _ _ _ _ hu2 ->
    itt_typing _ _ _ _ hv1 ->
    itt_typing _ _ _ _ hv2 ->
    itt_eq_term _ _ _ _ _ (cong_Pair Σ Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 hA hB hu hv hB1 hB2 hu1 hu2 hv1 hv2)

| itt_cong_Pi1 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2 :
    itt_eq_term _ _ _ _ _ hp ->
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hB ->
    itt_typing _ _ _ _ hB1 ->
    itt_typing _ _ _ _ hB2 ->
    itt_eq_term _ _ _ _ _ (cong_Pi1 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2)

| itt_cong_Pi2 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2 :
    itt_eq_term _ _ _ _ _ hp ->
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hB ->
    itt_typing _ _ _ _ hB1 ->
    itt_typing _ _ _ _ hB2 ->
    itt_eq_term _ _ _ _ _ (cong_Pi2 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2)

| itt_cong_Eq Γ s A1 A2 u1 u2 v1 v2 hA hu hv :
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hu ->
    itt_eq_term _ _ _ _ _ hv ->
    itt_eq_term _ _ _ _ _ (cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 hA hu hv)

| itt_cong_Refl Γ s A1 A2 u1 u2 hA hu :
    itt_eq_term _ _ _ _ _ hA ->
    itt_eq_term _ _ _ _ _ hu ->
    itt_eq_term _ _ _ _ _ (cong_Refl Σ Γ s A1 A2 u1 u2 hA hu)

with itt_wf Σ : forall Γ, wf Σ Γ -> Type :=
| itt_nil : itt_wf _ _ (wf_nil Σ)
| itt_snoc Γ A s hw hA :
    itt_wf _ _ hw ->
    itt_typing _ _ _ _ hA ->
    itt_wf _ _ (wf_snoc Σ Γ A s hw hA)
.

Arguments itt_typing {_ _ _ _} _.
Arguments itt_eq_term {_ _ _ _ _} _.
Arguments itt_wf {_ _} _.

Derive Signature for itt_typing.
Derive Signature for itt_eq_term.
Derive Signature for itt_wf.


(* We now prove that terms typed in this fragment get translated to
   themselves. *)

(* TODO Move in Translation? *)
Definition type_translation {Σ} hg {Γ t A} h {Γ'} hΓ :=
  pi2_ (pi1_ (@complete_translation Σ hg)) Γ t A h Γ' hΓ.

Definition eq_translation {Σ} hg {Γ u v A} h {Γ'} hΓ :=
  pi2_ (@complete_translation Σ hg) Γ u v A h Γ' hΓ.

Theorem term_identity :
  forall {Σ} (hg : type_glob Σ)
    {Γ t A} (h : Σ ;;; Γ |-x t : A)
    {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
    itt_typing h ->
    let '(A' ; t' ; _) := type_translation hg h hΓ in
    (t = t') * (A = A').
Proof.
  intros Σ hg Γ t A h Γ' hΓ hi.
  induction hi.
  all: try (split ; reflexivity).
  - split.
    + reflexivity.
    + unshelve refine (let isdecl' : n < #|Γ'| := _ in _).
      { destruct hΓ as [iΓ _]. now rewrite <- (length_increl iΓ). }
      match goal with
      | |- ?t = _ => change (t = lift0 (S n) (safe_nth Γ' (exist _ n isdecl')))
      end.
      f_equal.
      (* We probably need to know context translation is also the identity. *)
      admit.
  - split. 
    + (* Problems with computation again. *)
      (* pose (tmA := *)
      (*   let '(S' ; A' ; hA') := type_translation hg hA hΓ in *)
      (*   let th : type_head (head (sSort s1)) := type_headSort s1 in *)
      (*   let '(T' ; ((A'' ; hA''), hh)) := choose_type hg th hA' in *)
      (*   true *)
      (* ). *)
      specialize (IHhi1 hΓ).
      admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Abort.
