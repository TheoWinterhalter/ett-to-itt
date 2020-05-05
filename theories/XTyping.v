From Coq Require Import Bool String List BinPos Compare_dec Lia.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation Require Import util Sorts SAst SLiftSubst SCommon Equality.

Reserved Notation " Σ ;;; Γ '|-x' t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ '|-x' t ≡ u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Section XTyping.

Context `{Sort_notion : Sorts.notion}.

Declare Scope x_scope.

Inductive typing (Σ : sglobal_context) (Γ : scontext) : sterm -> sterm -> Type :=
| type_Rel n :
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-x (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl))

| type_Sort s :
    Σ ;;; Γ |-x (sSort s) : sSort (succ s)

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, t |-x b : sSort s2 ->
    Σ ;;; Γ |-x (sProd n t b) : sSort (Sorts.prod_sort s1 s2)

| type_Lambda n n' t b s1 s2 bty :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, t |-x bty : sSort s2 ->
    Σ ;;; Γ ,, t |-x b : bty ->
    Σ ;;; Γ |-x (sLambda n t bty b) : sProd n' t bty

| type_App n s1 s2 t A B u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x t : sProd n A B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x (sApp t A B u) : B{ 0 := u }

| type_Sum n t b s1 s2 :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, t |-x b : sSort s2 ->
    Σ ;;; Γ |-x (sSum n t b) : sSort (Sorts.sum_sort s1 s2)

| type_Pair n A B u v s1 s2 :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : B{ 0 := u } ->
    Σ ;;; Γ |-x sPair A B u v : sSum n A B

| type_Pi1 n A B s1 s2 p :
    Σ ;;; Γ |-x p : sSum n A B ->
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x sPi1 A B p : A

| type_Pi2 n A B s1 s2 p :
    Σ ;;; Γ |-x p : sSum n A B ->
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ |-x sPi2 A B p : B{ 0 := sPi1 A B p }

| type_Eq s A u v :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : A ->
    Σ ;;; Γ |-x sEq A u v : sSort (Sorts.eq_sort s)

| type_Refl s A u :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sRefl A u : sEq A u u

| type_Ax id ty :
    lookup_glob Σ id = Some ty ->
    Σ ;;; Γ |-x sAx id : ty

| type_conv t A B s :
    Σ ;;; Γ |-x t : A ->
    Σ ;;; Γ |-x B : sSort s ->
    Σ ;;; Γ |-x A ≡ B : sSort s ->
    Σ ;;; Γ |-x t : B

where " Σ ;;; Γ '|-x' t : T " := (@typing Σ Γ t T) : x_scope

with eq_term (Σ : sglobal_context) (Γ : scontext) : sterm -> sterm -> sterm -> Type :=
| eq_reflexivity u A :
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x u ≡ u : A

| eq_symmetry u v A :
    Σ ;;; Γ |-x u ≡ v : A ->
    Σ ;;; Γ |-x v ≡ u : A

| eq_transitivity u v w A :
    Σ ;;; Γ |-x u ≡ v : A ->
    Σ ;;; Γ |-x v ≡ w : A ->
    Σ ;;; Γ |-x u ≡ w : A

| eq_beta s1 s2 n A B t u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, A |-x B : sSort s2 ->
    Σ ;;; Γ ,, A |-x t : B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sApp (sLambda n A B t) A B u ≡ t{ 0 := u } : B{ 0 := u }

| eq_conv s T1 T2 t1 t2 :
    Σ ;;; Γ |-x t1 ≡ t2 : T1 ->
    Σ ;;; Γ |-x T1 ≡ T2 : sSort s ->
    Σ ;;; Γ |-x t1 ≡ t2 : T2

| cong_Prod n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 ≡ B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x (sProd n1 A1 B1) ≡ (sProd n2 A2 B2) :
               sSort (Sorts.prod_sort s1 s2)

| cong_Lambda n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 ≡ B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x t1 ≡ t2 : B1 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x t1 : B1 ->
    Σ ;;; Γ ,, A2 |-x t2 : B2 ->
    Σ ;;; Γ |-x (sLambda n1 A1 B1 t1) ≡ (sLambda n2 A2 B2 t2) : sProd n' A1 B1

| cong_App n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 ≡ B2 : sSort s2 ->
    Σ ;;; Γ |-x t1 ≡ t2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-x u1 ≡ u2 : A1 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x t1 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-x t2 : sProd n2 A2 B2 ->
    Σ ;;; Γ |-x u1 : A1 ->
    Σ ;;; Γ |-x u2 : A2 ->
    Σ ;;; Γ |-x (sApp t1 A1 B1 u1) ≡ (sApp t2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Sum n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 ≡ B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x (sSum n1 A1 B1) ≡ (sSum n2 A2 B2) : sSort (Sorts.sum_sort s1 s2)

| cong_Pair n A1 A2 B1 B2 u1 u2 v1 v2 s1 s2 :
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 ≡ B2 : sSort s2 ->
    Σ ;;; Γ |-x u1 ≡ u2 : A1 ->
    Σ ;;; Γ |-x v1 ≡ v2 : B1{ 0 := u1 } ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x u1 : A1 ->
    Σ ;;; Γ |-x u2 : A2 ->
    Σ ;;; Γ |-x v1 : B1{ 0 := u1 } ->
    Σ ;;; Γ |-x v2 : B2{ 0 := u2 } ->
    Σ ;;; Γ |-x sPair A1 B1 u1 v1 ≡ sPair A2 B2 u2 v2 : sSum n A1 B1

| cong_Pi1 nx ny A1 A2 B1 B2 s1 s2 p1 p2 :
    Σ ;;; Γ |-x p1 ≡ p2 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 ≡ B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x p1 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x p2 : sSum ny A2 B2 ->
    Σ ;;; Γ |-x sPi1 A1 B1 p1 ≡ sPi1 A2 B2 p2 : A1

| cong_Pi2 nx ny A1 A2 B1 B2 s1 s2 p1 p2 :
    Σ ;;; Γ |-x p1 ≡ p2 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s1 ->
    Σ ;;; Γ ,, A1 |-x B1 ≡ B2 : sSort s2 ->
    Σ ;;; Γ ,, A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x p1 : sSum nx A1 B1 ->
    Σ ;;; Γ |-x p2 : sSum ny A2 B2 ->
    Σ ;;; Γ |-x sPi2 A1 B1 p1 ≡ sPi2 A2 B2 p2 : B1{ 0 := sPi1 A1 B1 p1 }

| cong_Eq s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s ->
    Σ ;;; Γ |-x u1 ≡ u2 : A1 ->
    Σ ;;; Γ |-x v1 ≡ v2 : A1 ->
    Σ ;;; Γ |-x sEq A1 u1 v1 ≡ sEq A2 u2 v2 : sSort (Sorts.eq_sort s)

| cong_Refl s A1 A2 u1 u2 :
    Σ ;;; Γ |-x A1 ≡ A2 : sSort s ->
    Σ ;;; Γ |-x u1 ≡ u2 : A1 ->
    Σ ;;; Γ |-x sRefl A1 u1 ≡ sRefl A2 u2 : sEq A1 u1 u1

| reflection A u v e :
    Σ ;;; Γ |-x e : sEq A u v ->
    Σ ;;; Γ |-x u ≡ v : A

| eq_alpha u v A :
    nl u = nl v ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x u ≡ v : A

where " Σ ;;; Γ '|-x' t ≡ u : T " := (@eq_term Σ Γ t u T) : x_scope.

Delimit Scope x_scope with x.

Open Scope x_scope.

Inductive wf (Σ : sglobal_context) : scontext -> Type :=
| wf_nil :
    wf Σ nil

| wf_snoc Γ A s :
    wf Σ Γ ->
    Σ ;;; Γ |-x A : sSort s ->
    wf Σ (Γ ,, A).

Derive Signature for typing.
Derive Signature for wf.
Derive Signature for eq_term.

End XTyping.

Declare Scope x_scope.

Notation " Σ ;;; Γ '|-x' t : T " :=
  (@typing _ Σ Γ t T) (at level 50, Γ, t, T at next level) : x_scope.
Notation " Σ ;;; Γ '|-x' t ≡ u : T " :=
  (@eq_term _ Σ Γ t u T) (at level 50, Γ, t, u, T at next level) : x_scope.