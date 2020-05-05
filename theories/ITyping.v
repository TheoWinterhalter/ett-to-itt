From Coq Require Import Bool String List BinPos Compare_dec Lia.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon Conversion.
Import ListNotations.

Open Scope s_scope.

(*! Typing *)

Declare Scope i_scope.

Section ITyping.

Context `{Sort_notion : Sorts.notion}.

Reserved Notation " Σ ;;; Γ '|-i' t : T " (at level 50, Γ, t, T at next level).

Inductive typing (Σ : sglobal_context) : scontext -> sterm -> sterm -> Prop :=
| type_Rel Γ n :
    wf Σ Γ ->
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-i (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl))

| type_Sort Γ s :
    wf Σ Γ ->
    Σ ;;; Γ |-i (sSort s) : sSort (Sorts.succ s)

| type_Prod Γ n t b s1 s2 :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, t |-i b : sSort s2 ->
    Σ ;;; Γ |-i (sProd n t b) : sSort (Sorts.prod_sort s1 s2)

| type_Lambda Γ n n' t b s1 s2 bty :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, t |-i bty : sSort s2 ->
    Σ ;;; Γ ,, t |-i b : bty ->
    Σ ;;; Γ |-i (sLambda n t bty b) : sProd n' t bty

| type_App Γ n s1 s2 t A B u :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, A |-i B : sSort s2 ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i (sApp t A B u) : B{ 0 := u }

| type_Sum Γ n t b s1 s2 :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, t |-i b : sSort s2 ->
    Σ ;;; Γ |-i (sSum n t b) : sSort (Sorts.sum_sort s1 s2)

| type_Pair Γ n A B u v s1 s2 :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, A |-i B : sSort s2 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i sPair A B u v : sSum n A B

| type_Pi1 Γ n A B s1 s2 p :
    Σ ;;; Γ |-i p : sSum n A B ->
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, A |-i B : sSort s2 ->
    Σ ;;; Γ |-i sPi1 A B p : A

| type_Pi2 Γ n A B s1 s2 p :
    Σ ;;; Γ |-i p : sSum n A B ->
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, A |-i B : sSort s2 ->
    Σ ;;; Γ |-i sPi2 A B p : B{ 0 := sPi1 A B p }

| type_Eq Γ s A u v :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEq A u v : sSort (Sorts.eq_sort s)

| type_Refl Γ s A u :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u

| type_J Γ s1 s2 A u v P p w :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ ,, A ,, (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2 ->
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i w : P{ 1 := u }{ 0 := sRefl A u } ->
    Σ ;;; Γ |-i sJ A u P w v p : P{ 1 := v }{ 0 := p }

| type_Transport Γ s T1 T2 p t :
    Σ ;;; Γ |-i T1 : sSort s ->
    Σ ;;; Γ |-i T2 : sSort s ->
    Σ ;;; Γ |-i p : sEq (sSort s) T1 T2 ->
    Σ ;;; Γ |-i t : T1 ->
    Σ ;;; Γ |-i sTransport T1 T2 p t : T2

| type_Heq Γ A a B b s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i sHeq A a B b : sSort s

| type_HeqToEq Γ A u v p s :
    Σ ;;; Γ |-i p : sHeq A u A v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sHeqToEq p : sEq A u v

| type_HeqRefl Γ A a s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i sHeqRefl A a : sHeq A a A a

| type_HeqSym Γ A a B b p s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i sHeqSym p : sHeq B b A a

| type_HeqTrans Γ A a B b C c p q s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i C : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i c : C ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i q : sHeq B b C c ->
    Σ ;;; Γ |-i sHeqTrans p q : sHeq A a C c

| type_HeqTransport Γ A B p t s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i sHeqTransport p t : sHeq A t B (sTransport A B p t)

| type_CongProd Γ s z nx ny A1 A2 B1 B2 pA pB :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (Sorts.prod_sort s z)) (sProd nx A1 B1)
         (sSort (Sorts.prod_sort s z)) (sProd ny A2 B2)

| type_CongLambda Γ s z nx ny A1 A2 B1 B2 t1 t2 pA pB pt :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2)

| type_CongApp Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i u1 : sProd nx A1 B1 ->
    Σ ;;; Γ |-i u2 : sProd ny A2 B2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 A2 B2 v2)

| type_CongSum Γ s z nx ny A1 A2 B1 B2 pA pB :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongSum B1 B2 pA pB :
    sHeq (sSort (Sorts.sum_sort s z)) (sSum nx A1 B1)
         (sSort (Sorts.sum_sort s z)) (sSum ny A2 B2)

| type_CongPair Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq (B1{ 0 := u1 }) v1 (B2{ 0 := u2 }) v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i v1 : B1{ 0 := u1 } ->
    Σ ;;; Γ |-i v2 : B2{ 0 := u2 } ->
    Σ ;;; Γ |-i sCongPair B1 B2 pA pB pu pv :
    sHeq (sSum nx A1 B1) (sPair A1 B1 u1 v1)
         (sSum ny A2 B2) (sPair A2 B2 u2 v2)

| type_CongPi1 Γ s z nx ny A1 A2 B1 B2 p1 p2 pA pB pp :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i p1 : sSum nx A1 B1 ->
    Σ ;;; Γ |-i p2 : sSum ny A2 B2 ->
    Σ ;;; Γ |-i sCongPi1 B1 B2 pA pB pp : sHeq A1 (sPi1 A1 B1 p1)
                                              A2 (sPi1 A2 B2 p2)

| type_CongPi2 Γ s z nx ny A1 A2 B1 B2 p1 p2 pA pB pp :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pp : sHeq (sSum nx A1 B1) p1 (sSum ny A2 B2) p2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i p1 : sSum nx A1 B1 ->
    Σ ;;; Γ |-i p2 : sSum ny A2 B2 ->
    Σ ;;; Γ |-i sCongPi2 B1 B2 pA pB pp :
               sHeq (B1{ 0 := sPi1 A1 B1 p1}) (sPi2 A1 B1 p1)
                    (B2{ 0 := sPi1 A2 B2 p2}) (sPi2 A2 B2 p2)

| type_CongEq Γ s A1 A2 u1 u2 v1 v2 pA pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv :
               sHeq (sSort (Sorts.eq_sort s)) (sEq A1 u1 v1)
                    (sSort (Sorts.eq_sort s)) (sEq A2 u2 v2)

| type_CongRefl Γ s A1 A2 u1 u2 pA pu :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2)

| type_EqToHeq Γ A u v p s :
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEqToHeq p : sHeq A u A v

| type_HeqTypeEq Γ A u B v p s :
    Σ ;;; Γ |-i p : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B ->
    Σ ;;; Γ |-i sHeqTypeEq A B p : sEq (sSort s) A B

| type_Pack Γ A1 A2 s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i sPack A1 A2 : sSort s

| type_ProjT1 Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p : A1

| type_ProjT2 Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p : A2

| type_ProjTe Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p : sHeq A1 (sProjT1 p) A2 (sProjT2 p)

| type_Ax Γ id ty :
    wf Σ Γ ->
    lookup_glob Σ id = Some ty ->
    Σ ;;; Γ |-i sAx id : ty

| type_conv Γ t A B s :
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    A ≡ B ->
    Σ ;;; Γ |-i t : B

where " Σ ;;; Γ '|-i' t : T " := (@typing Σ Γ t T) : i_scope

with wf (Σ : sglobal_context) : scontext -> Prop :=
| wf_nil :
    wf Σ nil

| wf_snoc s Γ A :
    wf Σ Γ ->
    Σ ;;; Γ |-i A : sSort s ->
    wf Σ (Γ ,, A)
.

End ITyping.

Notation " Σ ;;; Γ '|-i' t : T " :=
  (@typing _ Σ Γ t T) (at level 50, Γ, t, T at next level) : i_scope.

Derive Signature for typing.
Derive Signature for wf.

Delimit Scope i_scope with i.

(* Syntactic restriction.
   We define the notion of ETT compatibility to restrict the syntax
   to the one that is allowed in ETT.
   [TODO Move?]
 *)
Section Xcomp.

Context `{Sort_notion : Sorts.notion}.

Inductive Xcomp : sterm -> Type :=
| xcomp_Rel n : Xcomp (sRel n)
| xcomp_Sort s : Xcomp (sSort s)
| xcomp_Prod na A B :
    Xcomp A ->
    Xcomp B ->
    Xcomp (sProd na A B)
| xcomp_Lambda na A B t :
    Xcomp A ->
    Xcomp B ->
    Xcomp t ->
    Xcomp (sLambda na A B t)
| xcomp_App u A B v :
    Xcomp u ->
    Xcomp A ->
    Xcomp B ->
    Xcomp v ->
    Xcomp (sApp u A B v)
| xcomp_Sum na A B :
    Xcomp A ->
    Xcomp B ->
    Xcomp (sSum na A B)
| xcomp_Pair A B u v :
    Xcomp A ->
    Xcomp B ->
    Xcomp u ->
    Xcomp v ->
    Xcomp (sPair A B u v)
| xcomp_Pi1 A B p :
    Xcomp A ->
    Xcomp B ->
    Xcomp p ->
    Xcomp (sPi1 A B p)
| xcomp_Pi2 A B p :
    Xcomp A ->
    Xcomp B ->
    Xcomp p ->
    Xcomp (sPi2 A B p)
| xcomp_Eq A u v :
    Xcomp A ->
    Xcomp u ->
    Xcomp v ->
    Xcomp (sEq A u v)
| xcomp_Refl A u :
    Xcomp A ->
    Xcomp u ->
    Xcomp (sRefl A u)
| xcomp_Ax id :
    Xcomp (sAx id)
.

End Xcomp.

Derive Signature for Xcomp.

Section Global.

Context `{Sort_notion : Sorts.notion}.

Definition isType (Σ : sglobal_context) (Γ : scontext) (t : sterm) :=
  exists s, Σ ;;; Γ |-i t : sSort s.

Inductive fresh_glob (id : ident) : sglobal_context -> Prop :=
| fresh_glob_nil : fresh_glob id []
| fresh_glob_cons Σ d :
    fresh_glob id Σ ->
    (dname d) <> id ->
    fresh_glob id (d :: Σ).

Inductive type_glob : sglobal_context -> Type :=
| type_glob_nil : type_glob []
| type_glob_cons Σ d :
    type_glob Σ ->
    fresh_glob (dname d) Σ ->
    isType Σ [] (dtype d) ->
    Xcomp (dtype d) ->
    type_glob (d :: Σ).

End Global.

Derive Signature for fresh_glob.
Derive Signature for type_glob.