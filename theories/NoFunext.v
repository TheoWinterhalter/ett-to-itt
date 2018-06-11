(* The purpose of this file is to show that we can restrict ETT derivations in
   such a way that we can avoid using funext in the transaltion.
 *)
From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import util SAst SLiftSubst SCommon XTyping.

(* We devise a restriction of ETT such that we don't need funext to translate
   it. *)
Inductive withReflection := maybeReflection | noReflection.

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

| nice_conv Γ t A B s ht hB hconv r :
    nice_typing _ _ _ _ ht ->
    nice_typing _ _ _ _ hB ->
    nice_eq_term _ _ _ _ _ hconv r ->
    nice_typing _ _ _ _ (type_conv Σ Γ t A B s ht hB hconv)

with nice_eq_term Σ : forall Γ t u A, Σ ;;; Γ |-x t = u : A -> withReflection -> Type :=
| nice_reflexivity Γ u A hu r :
    nice_typing _ _ _ _ hu ->
    nice_eq_term _ _ _ _ _ (eq_reflexivity Σ Γ u A hu) r

| nice_symmetry Γ u v A h r :
    nice_eq_term _ _ _ _ _ h r ->
    nice_eq_term _ _ _ _ _ (eq_symmetry Σ Γ u v A h) r

| nice_transitivity Γ u v w A h1 h2 r :
    nice_eq_term _ _ _ _ _ h1 r ->
    nice_eq_term _ _ _ _ _ h2 r ->
    nice_eq_term _ _ _ _ _ (eq_transitivity Σ Γ u v w A h1 h2) r

| nice_beta Γ s1 s2 n A B t u hA hB ht hu r :
    nice_typing _ _ _ _ hA ->
    nice_typing _ _ _ _ hB ->
    nice_typing _ _ _ _ ht ->
    nice_typing _ _ _ _ hu ->
    nice_eq_term _ _ _ _ _ (eq_beta Σ Γ s1 s2 n A B t u hA hB ht hu) r

| nice_eq_conv Γ s T1 T2 t1 t2 ht hT r r' :
    nice_eq_term _ _ _ _ _ ht r ->
    nice_eq_term _ _ _ _ _ hT r ->
    nice_eq_term _ _ _ _ _ (eq_conv Σ Γ s T1 T2 t1 t2 ht hT) r'

| nice_cong_Prod Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2 r :
    nice_eq_term _ _ _ _ _ hA noReflection ->
    nice_eq_term _ _ _ _ _ hB noReflection ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2) r

| nice_cong_Lambda Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 hA hB ht hB1 hB2 ht1 ht2 r :
    nice_eq_term _ _ _ _ _ hA noReflection ->
    nice_eq_term _ _ _ _ _ hB noReflection ->
    nice_eq_term _ _ _ _ _ ht noReflection ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_typing _ _ _ _ ht1 ->
    nice_typing _ _ _ _ ht2 ->
    nice_eq_term _ _ _ _ _ (cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 hA hB ht hB1 hB2 ht1 ht2) r

| nice_cong_App Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 hA hB ht hu hB1 hB2 ht1 ht2 hu1 hu2 r :
    nice_eq_term _ _ _ _ _ hA noReflection ->
    nice_eq_term _ _ _ _ _ hB noReflection ->
    nice_eq_term _ _ _ _ _ ht noReflection -> (* Maybe more optimisation can *)
    nice_eq_term _ _ _ _ _ hu noReflection -> (* be done. *)
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_typing _ _ _ _ ht1 ->
    nice_typing _ _ _ _ ht2 ->
    nice_typing _ _ _ _ hu1 ->
    nice_typing _ _ _ _ hu2 ->
    nice_eq_term _ _ _ _ _ (cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 hA hB ht hu hB1 hB2 ht1 ht2 hu1 hu2) r

| nice_cong_Sum Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2 r :
    nice_eq_term _ _ _ _ _ hA noReflection ->
    nice_eq_term _ _ _ _ _ hB noReflection ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Sum Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 hA hB hB1 hB2) r

| nice_cong_Pair Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 hA hB hu hv hB1 hB2 hu1 hu2 hv1 hv2 r :
    nice_eq_term _ _ _ _ _ hA noReflection ->
    nice_eq_term _ _ _ _ _ hB noReflection ->
    nice_eq_term _ _ _ _ _ hu noReflection ->
    nice_eq_term _ _ _ _ _ hv noReflection ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_typing _ _ _ _ hu1 ->
    nice_typing _ _ _ _ hu2 ->
    nice_typing _ _ _ _ hv1 ->
    nice_typing _ _ _ _ hv2 ->
    nice_eq_term _ _ _ _ _ (cong_Pair Σ Γ n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 hA hB hu hv hB1 hB2 hu1 hu2 hv1 hv2) r

| nice_cong_Pi1 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2 r :
    nice_eq_term _ _ _ _ _ hp noReflection ->
    nice_eq_term _ _ _ _ _ hA noReflection ->
    nice_eq_term _ _ _ _ _ hB noReflection ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Pi1 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2) r

| nice_cong_Pi2 Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2 r :
    nice_eq_term _ _ _ _ _ hp noReflection ->
    nice_eq_term _ _ _ _ _ hA noReflection ->
    nice_eq_term _ _ _ _ _ hB noReflection ->
    nice_typing _ _ _ _ hB1 ->
    nice_typing _ _ _ _ hB2 ->
    nice_eq_term _ _ _ _ _ (cong_Pi2 Σ Γ nx ny A1 A2 B1 B2 s1 s2 p1 p2 hp hA hB hB1 hB2 hp1 hp2) r

| nice_cong_Eq Γ s A1 A2 u1 u2 v1 v2 hA hu hv r :
    nice_eq_term _ _ _ _ _ hA r ->
    nice_eq_term _ _ _ _ _ hu r ->
    nice_eq_term _ _ _ _ _ hv  r->
    nice_eq_term _ _ _ _ _ (cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 hA hu hv) r

| nice_cong_Refl Γ s A1 A2 u1 u2 hA hu r :
    nice_eq_term _ _ _ _ _ hA r ->
    nice_eq_term _ _ _ _ _ hu r ->
    nice_eq_term _ _ _ _ _ (cong_Refl Σ Γ s A1 A2 u1 u2 hA hu) r

| nice_reflection Γ A u v e he :
    nice_typing _ _ _ _ he ->
    nice_eq_term _ _ _ _ _ (reflection Σ Γ A u v e he) maybeReflection

with nice_wf Σ : forall Γ, wf Σ Γ -> Type :=
| nice_nil : nice_wf _ _ (wf_nil Σ)
| nice_snoc Γ A s hw hA :
    nice_wf _ _ hw ->
    nice_typing _ _ _ _ hA ->
    nice_wf _ _ (wf_snoc Σ Γ A s hw hA)
.

Arguments nice_typing {_ _ _ _} _.
Arguments nice_eq_term {_ _ _ _ _} _ _.
Arguments nice_wf {_ _} _.
