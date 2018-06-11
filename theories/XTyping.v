From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import util SAst SLiftSubst SCommon.

Reserved Notation " Σ ;;; Γ '|-x' t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ '|-x' t = u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Inductive typing (Σ : sglobal_context) : scontext -> sterm -> sterm -> Type :=
| type_Rel Γ n :
    wf Σ Γ ->
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-x (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl))

| type_Sort Γ s :
    wf Σ Γ ->
    Σ ;;; Γ |-x (sSort s) : sSort (succ_sort s)

| type_Prod Γ n t b s1 s2 :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, t |-x b : sSort s2 ->
    Σ ;;; Γ |-x (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda Γ n n' t b s1 s2 bty :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, t |-x bty : sSort s2 ->
    Σ ;;; Γ ,, t |-x b : bty ->
    Σ ;;; Γ |-x (sLambda n t bty b) : sProd n' t bty

| type_App Γ n s1 s2 t A B u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x t : sProd n A B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x (sApp t A B u) : B{ 0 := u }

| type_Sum Γ n t b s1 s2 :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, t |-x b : sSort s2 ->
    Σ ;;; Γ |-x (sSum n t b) : sSort (max_sort s1 s2)

| type_Pair Γ n A B u v s1 s2 :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : B{ 0 := u } ->
    Σ ;;; Γ |-x sPair A B u v : sSum n A B

| type_Pi1 Γ n A B s1 s2 p :
    Σ ;;; Γ |-x p : sSum n A B ->
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x sPi1 A B p : A

| type_Pi2 Γ n A B s1 s2 p :
    Σ ;;; Γ |-x p : sSum n A B ->
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x sPi2 A B p : B{ 0 := sPi1 A B p }

| type_Eq Γ s A u v :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : A ->
    Σ ;;; Γ |-x sEq A u v : sSort s

| type_Refl Γ s A u :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sRefl A u : sEq A u u

| type_Ax Γ id ty :
    wf Σ Γ ->
    lookup_glob Σ id = Some ty ->
    Σ ;;; Γ |-x sAx id : ty

| type_conv Γ t A B s :
    Σ ;;; Γ |-x t : A ->
    Σ ;;; Γ |-x B : sSort s ->
    Σ ;;; Γ |-x A = B : sSort s ->
    Σ ;;; Γ |-x t : B

where " Σ ;;; Γ '|-x' t : T " := (@typing Σ Γ t T) : x_scope

with wf (Σ : sglobal_context) : scontext -> Type :=
| wf_nil :
    wf Σ nil

| wf_snoc Γ A s :
    wf Σ Γ ->
    Σ ;;; Γ |-x A : sSort s ->
    wf Σ (Γ ,, A)

with eq_term (Σ : sglobal_context) : scontext -> sterm -> sterm -> sterm -> Type :=
| eq_reflexivity Γ u A :
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x u = u : A

| eq_symmetry Γ u v A :
    Σ ;;; Γ |-x u = v : A ->
    Σ ;;; Γ |-x v = u : A

| eq_transitivity Γ u v w A :
    Σ ;;; Γ |-x u = v : A ->
    Σ ;;; Γ |-x v = w : A ->
    Σ ;;; Γ |-x u = w : A

| eq_beta Γ s1 s2 n A B t u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ ,, A |-x t : B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sApp (sLambda n A B t) A B u = t{ 0 := u } : B{ 0 := u }

| eq_conv Γ s T1 T2 t1 t2 :
    Σ ;;; Γ |-x t1 = t2 : T1 ->
    Σ ;;; Γ |-x T1 = T2 : sSort s ->
    Σ ;;; Γ |-x t1 = t2 : T2

| cong_Prod Γ n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x (sProd n1 A1 B1) = (sProd n2 A2 B2) : sSort (max_sort s1 s2)

| cong_Lambda Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x t1 = t2 : B1 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x t1 : B1 ->
    Σ ;;; Γ ,, A2 |-x t2 : B2 ->
    Σ ;;; Γ |-x (sLambda n1 A1 B1 t1) = (sLambda n2 A2 B2 t2) : sProd n' A1 B1

| cong_App Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-x t1 = t2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x t1 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-x t2 : sProd n2 A2 B2 ->
    Σ ;;; Γ |-x u1 : A1 ->
    Σ ;;; Γ |-x u2 : A2 ->
    Σ ;;; Γ |-x (sApp t1 A1 B1 u1) = (sApp t2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Sum Γ n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x (sSum n1 A1 B1) = (sSum n2 A2 B2) : sSort (max_sort s1 s2)

| cong_Pair Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x v1 = v2 : B1{ 0 := u1 } ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x u1 : A1 ->
    Σ ;;; Γ |-x u2 : A2 ->
    Σ ;;; Γ |-x v1 : B1{ 0 := u1 } ->
    Σ ;;; Γ |-x v2 : B2{ 0 := u2 } ->
    Σ ;;; Γ |-x sPair A1 B1 u1 v1 = sPair A2 B2 u2 v2 : sSum n A1 B1

| cong_Pi1 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 :
    Σ ;;; Γ |-x p1 = p2 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x p1 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x p2 : sSum ny A2 B2 ->
    Σ ;;; Γ |-x sPi1 A1 B1 p1 = sPi1 A2 B2 p2 : A1

| cong_Pi2 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 :
    Σ ;;; Γ |-x p1 = p2 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x p1 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x p2 : sSum ny A2 B2 ->
    Σ ;;; Γ |-x sPi2 A1 B1 p1 = sPi2 A2 B2 p2 : B1{ 0 := sPi1 A1 B1 p1 }

| cong_Eq Γ s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x v1 = v2 : A1 ->
    Σ ;;; Γ |-x sEq A1 u1 v1 = sEq A2 u2 v2 : sSort s

| cong_Refl Γ s A1 A2 u1 u2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x sRefl A1 u1 = sRefl A2 u2 : sEq A1 u1 u1

| reflection Γ A u v e :
    Σ ;;; Γ |-x e : sEq A u v ->
    Σ ;;; Γ |-x u = v : A

where " Σ ;;; Γ '|-x' t = u : T " := (@eq_term Σ Γ t u T) : x_scope.

Delimit Scope x_scope with x.

Open Scope x_scope.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-x t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

(* We devise a restriction of ETT such that we don't need funext to translate
   it. *)
Inductive nice_typing Σ : forall Γ t A, Σ ;;; Γ |-x t : A -> Type :=
| nice_Rel Γ n hw isdecl :
    nice_wf _ _ hw ->
    nice_typing _ _ _ _ (type_Rel Σ Γ n hw isdecl)

| nice_Sort Γ s hw :
    nice_wf _ _ hw ->
    nice_typing _ _ _ _ (type_Sort Σ Γ s hw)

| nice_Prod Γ n A B s1 s2 hA hB :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ (type_Prod Σ Γ n A B s1 s2 hA hB)

| nice_Lambda Γ n n' A t s1 s2 B hA hB ht :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ ht ->
    nice_typing _ _ _ _ (type_Lambda Σ Γ n n' A t s1 s2 B hA hB ht)

| nice_App Γ n s1 s2 t A B u hA hB ht hu :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ ht ->
    nice_typing _ _ _ _ hu ->
    nice_typing _ _ _ _ (type_App Σ Γ n s1 s2 t A B u hA hB ht hu)

| nice_Sum Γ n A B s1 s2 hA hB :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ (type_Sum Σ Γ n A B s1 s2 hA hB)

| nice_Pair Γ n A B u v s1 s2 hA hB hu hv :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ hu ->
    nice_typing _ _ _ _ hv ->
    nice_typing _ _ _ _ (type_Pair Σ Γ n A B u v s1 s2 hA hB hu hv)

| nice_Pi1 Γ n A B s1 s2 p hp hA hB :
    nice_typing _ _ _ _ hp ->
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ (type_Pi1 Σ Γ n A B s1 s2 p hp hA hB)

| nice_Pi2 Γ n A B s1 s2 p hp hA hB :
    nice_typing _ _ _ _ hp ->
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ (type_Pi2 Σ Γ n A B s1 s2 p hp hA hB)

| nice_Eq Γ s A u v hA hu hv :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hu ->
    nice_typing _ _ _ _ hv ->
    nice_typing _ _ _ _ (type_Eq Σ Γ s A u v hA hu hv)

| nice_Refl Γ s A u hA hu :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hu ->
    nice_typing _ _ _ _ (type_Refl Σ Γ s A u hA hu)

| nice_Ax Γ id ty hw lk :
    nice_wf _ _ hw ->
    nice_typing _ _ _ _ (type_Ax Σ Γ id ty hw lk)

| nice_conv Γ t A B s ht hB hconv :
    nice_typing _ _ _ _ ht ->
    nice_typing _ _ _ _ hB ->
    nice_eq_term _ _ _ _ _ hconv ->
    nice_typing _ _ _ _ (type_conv Σ Γ t A B s ht hB hconv)

with nice_eq_term Σ : forall Γ t u A, Σ ;;; Γ |-x t = u : A -> Type :=
| nice_reflexivity Γ u A hu :
    nice_typing _ _ _ _ hu ->
    nice_eq_term _ _ _ _ _ (eq_reflexivity Σ Γ u A hu)

| nice_symmetry Γ u v A h :
    nice_eq_term _ _ _ _ _ h ->
    nice_eq_term _ _ _ _ _ (eq_symmetry Σ Γ u v A h)

| nice_transitivity Γ u v w A h1 h2 :
    nice_eq_term _ _ _ _ _ h1 ->
    nice_eq_term _ _ _ _ _ h2 ->
    nice_eq_term _ _ _ _ _ (eq_transitivity Σ Γ u v w A h1 h2)

| nice_beta Γ s1 s2 n A B t u hA hB ht hu :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ ht ->
    nice_typing _ _ _ _ hu ->
    nice_eq_term _ _ _ _ _ (eq_beta Σ Γ s1 s2 n A B t u hA hB ht hu)

| nice_eq_conv Γ s T1 T2 t1 t2 ht hT :
    nice_eq_term _ _ _ _ _ ht ->
    nice_eq_term _ _ _ _ _ hT ->
    nice_eq_term _ _ _ _ _ (eq_conv Σ Γ s T1 T2 t1 t2 ht hT)

| nice_cong_Prod Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2 :
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hB ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2)

| nice_cong_Lambda Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 hA hB ht hB1 hB2 ht1 ht2 :
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hB ->
    nice_eq_term _ _ _ _ _ ht ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_typing _ _ _ _ ht1 ->
    nice_typing _ _ _ _ ht2 ->
    nice_eq_term _ _ _ _ _ (cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 hA hB ht hB1 hB2 ht1 ht2)

| nice_cong_App Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 hA hB ht hu hB1 hB2 ht1 ht2 hu1 hu2 :
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hB ->
    nice_eq_term _ _ _ _ _ ht ->
    nice_eq_term _ _ _ _ _ hu ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_typing _ _ _ _ ht1 ->
    nice_typing _ _ _ _ ht2 ->
    nice_typing _ _ _ _ hu1 ->
    nice_typing _ _ _ _ hu2 ->
    nice_eq_term _ _ _ _ _ (cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 hA hB ht hu hB1 hB2 ht1 ht2 hu1 hu2)

| nice_cong_Sum Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2 :
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hB ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Sum Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2)

| nice_cong_Pair Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 hA hB hu hv hB1 hB2 hu1 hu2 hv1 hv2 :
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hB ->
    nice_eq_term _ _ _ _ _ hu ->
    nice_eq_term _ _ _ _ _ hv ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_typing _ _ _ _ hu1 ->
    nice_typing _ _ _ _ hu2 ->
    nice_typing _ _ _ _ hv1 ->
    nice_typing _ _ _ _ hv2 ->
    nice_eq_term _ _ _ _ _ (cong_Pair Σ Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 hA hB hu hv hB1 hB2 hu1 hu2 hv1 hv2)

| nice_cong_Pi1 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2 :
    nice_eq_term _ _ _ _ _ hp ->
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hB ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Pi1 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2)

| nice_cong_Pi2 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2 :
    nice_eq_term _ _ _ _ _ hp ->
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hB ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Pi2 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2)

| nice_cong_Eq Γ s A1 A2 u1 u2 v1 v2 hA hu hv :
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hu ->
    nice_eq_term _ _ _ _ _ hv ->
    nice_eq_term _ _ _ _ _ (cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 hA hu hv)

| nice_cong_Refl Γ s A1 A2 u1 u2 hA hu :
    nice_eq_term _ _ _ _ _ hA ->
    nice_eq_term _ _ _ _ _ hu ->
    nice_eq_term _ _ _ _ _ (cong_Refl Σ Γ s A1 A2 u1 u2 hA hu)

| nice_reflection Γ A u v e he :
    nice_typing _ _ _ _ he ->
    nice_eq_term _ _ _ _ _ (reflection Σ Γ A u v e he)

with nice_wf Σ : forall Γ, wf Σ Γ -> Type :=
| nice_nil : nice_wf _ _ (wf_nil Σ)
| nice_snoc Γ A s hw hA :
    nice_wf _ _ hw ->
    nice_typing _ _ _ _ hA ->
    nice_wf _ _ (wf_snoc Σ Γ A s hw hA)
.

Arguments nice_typing {_ _ _ _} _.
Arguments nice_eq_term {_ _ _ _ _} _.
Arguments nice_wf {_ _} _.
