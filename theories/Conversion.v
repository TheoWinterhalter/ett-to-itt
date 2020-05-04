From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util SAst Equality SLiftSubst SCommon.
Import ListNotations.

Open Scope s_scope.

(*! Reduction. *)

Section Red1.

Context `{Sort_notion : Sorts.notion}.

Inductive red1 : sterm -> sterm -> Prop :=
(*! Computation *)

(** β *)
| red_beta n A B A' B' t u :
    red1 (sApp (sLambda n A B t) A' B' u) (t{ 0 := u })

(** J-Refl *)
| red_JRefl A u P w v A' u' :
    red1 (sJ A u P w v (sRefl A' u')) w

(** Transport of Refl *)
| red_TransportRefl A A' A'' T t :
    red1 (sTransport A A' (sRefl T A'') t) t

(*! Subterm reduction *)

(** Lambda *)
| abs_red_dom na A A' B t :
    red1 A A' ->
    red1 (sLambda na A B t) (sLambda na A' B t)

| abs_red_codom na A B B' t :
    red1 B B' ->
    red1 (sLambda na A B t) (sLambda na A B' t)

| abs_red_body na A B t t' :
    red1 t t' ->
    red1 (sLambda na A B t) (sLambda na A B t')

(** App *)
| app_red_fun u u' A B v :
    red1 u u' ->
    red1 (sApp u A B v) (sApp u' A B v)

| app_red_dom u A A' B v :
    red1 A A' ->
    red1 (sApp u A B v) (sApp u A' B v)

| app_red_codom u A B B' v :
    red1 B B' ->
    red1 (sApp u A B v) (sApp u A B' v)

| app_red_arg u A B v v' :
    red1 v v' ->
    red1 (sApp u A B v) (sApp u A B v')

(** Prod *)
| prod_red_l na na' A A' B :
    red1 A A' ->
    red1 (sProd na A B) (sProd na' A' B)

| prod_red_r na na' A B B' :
    red1 B B' ->
    red1 (sProd na A B) (sProd na' A B')

(** Sum *)
| sum_red_l na na' A A' B :
    red1 A A' ->
    red1 (sSum na A B) (sSum na' A' B)

| sum_red_r na na' A B B' :
    red1 B B' ->
    red1 (sSum na A B) (sSum na' A B')

(** Pair *)
| pair_red_dom A B u v A' :
    red1 A A' ->
    red1 (sPair A B u v) (sPair A' B u v)

| pair_red_cod A B u v B' :
    red1 B B' ->
    red1 (sPair A B u v) (sPair A B' u v)

| pair_red_tm_l A B u v u' :
    red1 u u' ->
    red1 (sPair A B u v) (sPair A B u' v)

| pair_red_tm_r A B u v v' :
    red1 v v' ->
    red1 (sPair A B u v) (sPair A B u v')

(** Pi1 *)
| pi1_red_dom A B p A' :
    red1 A A' ->
    red1 (sPi1 A B p) (sPi1 A' B p)

| pi1_red_cod A B p B' :
    red1 B B' ->
    red1 (sPi1 A B p) (sPi1 A B' p)

| pi1_red_tm A B p p' :
    red1 p p' ->
    red1 (sPi1 A B p) (sPi1 A B p')

(** Pi2 *)
| pi2_red_dom A B p A' :
    red1 A A' ->
    red1 (sPi2 A B p) (sPi2 A' B p)

| pi2_red_cod A B p B' :
    red1 B B' ->
    red1 (sPi2 A B p) (sPi2 A B' p)

| pi2_red_tm A B p p' :
    red1 p p' ->
    red1 (sPi2 A B p) (sPi2 A B p')

(** Eq *)
| eq_red_ty A A' u v :
    red1 A A' ->
    red1 (sEq A u v) (sEq A' u v)

| eq_red_l A u u' v :
    red1 u u' ->
    red1 (sEq A u v) (sEq A u' v)

| eq_red_r A u v v' :
    red1 v v' ->
    red1 (sEq A u v) (sEq A u v')

(** Refl *)
| refl_red_ty A A' u :
    red1 A A' ->
    red1 (sRefl A u) (sRefl A' u)

| refl_red_tm A u u' :
    red1 u u' ->
    red1 (sRefl A u) (sRefl A u')

(** J *)
| j_red_ty A A' u v P p w :
    red1 A A' ->
    red1 (sJ A u P w v p) (sJ A' u P w v p)

| j_red_l A u u' v P p w :
    red1 u u' ->
    red1 (sJ A u P w v p) (sJ A u' P w v p)

| j_red_pred A u v P P' p w :
    red1 P P' ->
    red1 (sJ A u P w v p) (sJ A u P' w v p)

| j_red_prf A u v P p w w' :
    red1 w w' ->
    red1 (sJ A u P w v p) (sJ A u P w' v p)

| j_red_r A u v v' P p w :
    red1 v v' ->
    red1 (sJ A u P w v p) (sJ A u P w v' p)

| j_red_eq A u v P p p' w :
    red1 p p' ->
    red1 (sJ A u P w v p) (sJ A u P w v p')

(** Transport *)
| transport_red_ty_l A A' B p t :
    red1 A A' ->
    red1 (sTransport A B p t) (sTransport A' B p t)

| transport_red_ty_r A B B' p t :
    red1 B B' ->
    red1 (sTransport A B p t) (sTransport A B' p t)

| transport_red_eq A B p p' t :
    red1 p p' ->
    red1 (sTransport A B p t) (sTransport A B p' t)

| transport_red_tm A B p t t' :
    red1 t t' ->
    red1 (sTransport A B p t) (sTransport A B p t')

(** Heq *)
| heq_red_ty_l A A' a B b :
    red1 A A' ->
    red1 (sHeq A a B b) (sHeq A' a B b)

| heq_red_tm_l A a a' B b :
    red1 a a' ->
    red1 (sHeq A a B b) (sHeq A a' B b)

| heq_red_ty_r A a B B' b :
    red1 B B' ->
    red1 (sHeq A a B b) (sHeq A a B' b)

| heq_red_tm_r A a B b b' :
    red1 b b' ->
    red1 (sHeq A a B b) (sHeq A a B b')

(** HeqToEq *)
| heqtoeq_red p p' :
    red1 p p' ->
    red1 (sHeqToEq p) (sHeqToEq p')

(** HeqRefl *)
| heqrefl_red_ty A A' a :
    red1 A A' ->
    red1 (sHeqRefl A a) (sHeqRefl A' a)

| heqrefl_red_tm A a a' :
    red1 a a' ->
    red1 (sHeqRefl A a) (sHeqRefl A a')

(** HeqSym *)
| heqsym_red p p' :
    red1 p p' ->
    red1 (sHeqSym p) (sHeqSym p')

(** HeqTrans *)
| heqtrans_red_l p p' q :
    red1 p p' ->
    red1 (sHeqTrans p q) (sHeqTrans p' q)

| heqtrans_red_r p q q' :
    red1 q q' ->
    red1 (sHeqTrans p q) (sHeqTrans p q')

(** HeqTransport *)
| heqtransport_red_eq p p' t :
    red1 p p' ->
    red1 (sHeqTransport p t) (sHeqTransport p' t)

| heqtransport_red_tm p t t' :
    red1 t t' ->
    red1 (sHeqTransport p t) (sHeqTransport p t')

(** CongProd *)
| congprod_red_ty_l B1 B1' B2 pA pB :
    red1 B1 B1' ->
    red1 (sCongProd B1 B2 pA pB) (sCongProd B1' B2 pA pB)

| congprod_red_ty_r B1 B2 B2' pA pB :
    red1 B2 B2' ->
    red1 (sCongProd B1 B2 pA pB) (sCongProd B1 B2' pA pB)

| congprod_red_tm_l B1 B2 pA pA' pB :
    red1 pA pA' ->
    red1 (sCongProd B1 B2 pA pB) (sCongProd B1 B2 pA' pB)

| congprod_red_tm_r B1 B2 pA pB pB' :
    red1 pB pB' ->
    red1 (sCongProd B1 B2 pA pB) (sCongProd B1 B2 pA pB')

(** CongLambda *)
| conglambda_red_ty_l B1 B2 t1 t2 pA pB pt B1' :
    red1 B1 B1' ->
    red1 (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1' B2 t1 t2 pA pB pt)

| conglambda_red_ty_r B1 B2 t1 t2 pA pB pt B2' :
    red1 B2 B2' ->
    red1 (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2' t1 t2 pA pB pt)

| conglambda_red_tm_l B1 B2 t1 t2 pA pB pt t1' :
    red1 t1 t1' ->
    red1 (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1' t2 pA pB pt)

| conglambda_red_tm_r B1 B2 t1 t2 pA pB pt t2' :
    red1 t2 t2' ->
    red1 (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2' pA pB pt)

| conglambda_red_eq_dom B1 B2 t1 t2 pA pB pt pA' :
    red1 pA pA' ->
    red1 (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2 pA' pB pt)

| conglambda_red_eq_codom B1 B2 t1 t2 pA pB pt pB' :
    red1 pB pB' ->
    red1 (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2 pA pB' pt)

| conglambda_red_eq_tm B1 B2 t1 t2 pA pB pt pt' :
    red1 pt pt' ->
    red1 (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2 pA pB pt')

(** CongApp *)
| congapp_red_ty_l B1 B2 pu pA pB pv B1' :
    red1 B1 B1' ->
    red1 (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1' B2 pu pA pB pv)

| congapp_red_ty_r B1 B2 pu pA pB pv B2' :
    red1 B2 B2' ->
    red1 (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2' pu pA pB pv)

| congapp_red_eq_fun B1 B2 pu pA pB pv pu' :
    red1 pu pu' ->
    red1 (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu' pA pB pv)

| congapp_red_eq_dom B1 B2 pu pA pB pv pA' :
    red1 pA pA' ->
    red1 (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu pA' pB pv)

| congapp_red_eq_codom B1 B2 pu pA pB pv pB' :
    red1 pB pB' ->
    red1 (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu pA pB' pv)

| congapp_red_eq_arg B1 B2 pu pA pB pv pv' :
    red1 pv pv' ->
    red1 (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu pA pB pv')

(** CongSum *)
| congsum_red_ty_l B1 B1' B2 pA pB :
    red1 B1 B1' ->
    red1 (sCongSum B1 B2 pA pB) (sCongSum B1' B2 pA pB)

| congsum_red_ty_r B1 B2 B2' pA pB :
    red1 B2 B2' ->
    red1 (sCongSum B1 B2 pA pB) (sCongSum B1 B2' pA pB)

| congsum_red_tm_l B1 B2 pA pA' pB :
    red1 pA pA' ->
    red1 (sCongSum B1 B2 pA pB) (sCongSum B1 B2 pA' pB)

| congsum_red_tm_r B1 B2 pA pB pB' :
    red1 pB pB' ->
    red1 (sCongSum B1 B2 pA pB) (sCongSum B1 B2 pA pB')

(** CongPair *)
| congpair_red_ty_l B1 B1' B2 pA pB pu pv :
    red1 B1 B1' ->
    red1 (sCongPair B1 B2 pA pB pu pv) (sCongPair B1' B2 pA pB pu pv)

| congpair_red_ty_r B1 B2 B2' pA pB pu pv :
    red1 B2 B2' ->
    red1 (sCongPair B1 B2 pA pB pu pv) (sCongPair B1 B2' pA pB pu pv)

| congpair_red_tm_dom B1 B2 pA pA' pB pu pv :
    red1 pA pA' ->
    red1 (sCongPair B1 B2 pA pB pu pv) (sCongPair B1 B2 pA' pB pu pv)

| congpair_red_tm_cod B1 B2 pA pB pB' pu pv :
    red1 pB pB' ->
    red1 (sCongPair B1 B2 pA pB pu pv) (sCongPair B1 B2 pA pB' pu pv)

| congpair_red_tm_tm_l B1 B2 pA pB pu pv pu' :
    red1 pu pu' ->
    red1 (sCongPair B1 B2 pA pB pu pv) (sCongPair B1 B2 pA pB pu' pv)

| congpair_red_tm_tm_r B1 B2 pA pB pu pv pv' :
    red1 pv pv' ->
    red1 (sCongPair B1 B2 pA pB pu pv) (sCongPair B1 B2 pA pB pu pv')

(** CongPi1 *)
| congpi1_red_ty_l B1 B1' B2 pA pB pp :
    red1 B1 B1' ->
    red1 (sCongPi1 B1 B2 pA pB pp) (sCongPi1 B1' B2 pA pB pp)

| congpi1_red_ty_r B1 B2 B2' pA pB pp :
    red1 B2 B2' ->
    red1 (sCongPi1 B1 B2 pA pB pp) (sCongPi1 B1 B2' pA pB pp)

| congpi1_red_tm_dom B1 B2 pA pA' pB pp :
    red1 pA pA' ->
    red1 (sCongPi1 B1 B2 pA pB pp) (sCongPi1 B1 B2 pA' pB pp)

| congpi1_red_tm_cod B1 B2 pA pB pB' pp :
    red1 pB pB' ->
    red1 (sCongPi1 B1 B2 pA pB pp) (sCongPi1 B1 B2 pA pB' pp)

| congpi1_red_tm_tm B1 B2 pA pB pp pp' :
    red1 pp pp' ->
    red1 (sCongPi1 B1 B2 pA pB pp) (sCongPi1 B1 B2 pA pB pp')

(** CongPi2 *)
| congpi2_red_ty_l B1 B1' B2 pA pB pp :
    red1 B1 B1' ->
    red1 (sCongPi2 B1 B2 pA pB pp) (sCongPi2 B1' B2 pA pB pp)

| congpi2_red_ty_r B1 B2 B2' pA pB pp :
    red1 B2 B2' ->
    red1 (sCongPi2 B1 B2 pA pB pp) (sCongPi2 B1 B2' pA pB pp)

| congpi2_red_tm_dom B1 B2 pA pA' pB pp :
    red1 pA pA' ->
    red1 (sCongPi2 B1 B2 pA pB pp) (sCongPi2 B1 B2 pA' pB pp)

| congpi2_red_tm_cod B1 B2 pA pB pB' pp :
    red1 pB pB' ->
    red1 (sCongPi2 B1 B2 pA pB pp) (sCongPi2 B1 B2 pA pB' pp)

| congpi2_red_tm_tm B1 B2 pA pB pp pp' :
    red1 pp pp' ->
    red1 (sCongPi2 B1 B2 pA pB pp) (sCongPi2 B1 B2 pA pB pp')

(** CongEq *)
| congeq_red_eq_ty pA pu pv pA' :
    red1 pA pA' ->
    red1 (sCongEq pA pu pv) (sCongEq pA' pu pv)

| congeq_red_eq_tm_l pA pu pv pu' :
    red1 pu pu' ->
    red1 (sCongEq pA pu pv) (sCongEq pA pu' pv)

| congeq_red_eq_tm_r pA pu pv pv' :
    red1 pv pv' ->
    red1 (sCongEq pA pu pv) (sCongEq pA pu pv')

(* (** CongRefl *) *)
| congrefl_red_ty pA pu pA' :
    red1 pA pA' ->
    red1 (sCongRefl pA pu) (sCongRefl pA' pu)

| congrefl_red_tm pA pu pu' :
    red1 pu pu' ->
    red1 (sCongRefl pA pu) (sCongRefl pA pu')

(** EqToHeq *)
| eqtoheq_red p p' :
    red1 p p' ->
    red1 (sEqToHeq p) (sEqToHeq p')

(** HeqTypeEq *)
| heqtypeeq_red_ty_l A B p A' :
    red1 A A' ->
    red1 (sHeqTypeEq A B p) (sHeqTypeEq A' B p)

| heqtypeeq_red_ty_r A B p B' :
    red1 B B' ->
    red1 (sHeqTypeEq A B p) (sHeqTypeEq A B' p)

| heqtypeeq_red_prf A B p p' :
    red1 p p' ->
    red1 (sHeqTypeEq A B p) (sHeqTypeEq A B p')

(** Pack *)
| pack_red_l A1 A2 A1' :
    red1 A1 A1' ->
    red1 (sPack A1 A2) (sPack A1' A2)

| pack_red_r A1 A2 A2' :
    red1 A2 A2' ->
    red1 (sPack A1 A2) (sPack A1 A2')

(** ProjT1 *)
| projt1_red p p' :
    red1 p p' ->
    red1 (sProjT1 p) (sProjT1 p')

(** ProjT2 *)
| projt2_red p p' :
    red1 p p' ->
    red1 (sProjT2 p) (sProjT2 p')

(** ProjTe *)
| projte_red p p' :
    red1 p p' ->
    red1 (sProjTe p) (sProjTe p')
.

End Red1.

Derive Signature for red1.

Notation " t ▷ u " :=
  (red1 t u) (at level 50, u at next level).

Section Red.

Context `{Sort_notion : Sorts.notion}.

(* Reflexive and transitive closure of 1-step reduction. *)
Inductive red t : sterm -> Prop :=
| refl_red : red t t
| trans_red u v : red1 t u -> red u v -> red t v.

End Red.

Notation " t ▷⃰ u " :=
  (red t u) (at level 50, u at next level).


Section nlred.

  Context `{Sort_notion : Sorts.notion}.

  (* We have to use this definition to trick Equations into not doing anything
   about this equality.
   *)
  Definition nleq u v := nl u = nl v.

  Derive NoConfusion NoConfusionHom for sterm.

  Ltac nlred :=
    lazymatch goal with
    | h : ?t ▷ ?t', eq : nl ?t = _, ih : forall _ _, ?t ▷ _ -> _ |- _ =>
      destruct (ih _ _ h eq) as [? [? ?]] ;
      eexists ; split ; [
        econstructor ; eassumption
      | unfold nleq ; cbn ; f_equal ; assumption
      ]
    end.

  Lemma nl_red1 :
    forall {t t' u},
      t ▷ u ->
      nleq t t' ->
      exists u', (t' ▷ u') /\ (nleq u u').
  Proof.
    intros t t' u h.
    induction t in u, h, t' |- *.
    all: dependent destruction h.
    all: intros eq.
    all: destruct t' ; unfold nleq in eq ; simpl in eq ; try discriminate eq.
    all: inversion eq ; try nlred.
    - destruct t'1 ; simpl nl in H0 ; try discriminate H0.
      inversion H0.
      eexists. split.
      + eapply red_beta.
      + apply nl_subst ; easy.
    - destruct t'6 ; simpl nl in H5 ; try discriminate H5.
      inversion H5.
      eexists. split.
      + eapply red_JRefl.
      + assumption.
    - destruct t'3 ; simpl nl in H2 ; try discriminate H2.
      inversion H2.
      eexists. split.
      + eapply red_TransportRefl.
      + assumption.
    Unshelve. all: exact nAnon.
  Defined.

End nlred.

(*! Conversion *)

Section Conv.

Context `{Sort_notion : Sorts.notion}.

Declare Scope i_scope.

Reserved Notation " t ≡ u " (at level 50, u at next level).

Inductive conv : sterm -> sterm -> Prop :=
| conv_eq t u : nl t = nl u -> t ≡ u
| conv_red_l t u v : red1 t v -> v ≡ u -> t ≡ u
| conv_red_r t u v : t ≡ v -> red1 u v -> t ≡ u

where " t ≡ u " := (@conv t u) : i_scope.

End Conv.

Notation " t ≡ u " :=
  (@conv _ t u) (at level 50, u at next level) : i_scope.
Derive Signature for conv.

Open Scope i_scope.

Section Conversion.

Context `{Sort_notion : Sorts.notion}.

Lemma conv_refl :
  forall t, t ≡ t.
Proof.
  intros t.
  apply conv_eq. reflexivity.
Defined.

Lemma conv_sym :
  forall {t u},
    t ≡ u ->
    u ≡ t.
Proof.
  intros t u h.
  induction h.
  - apply conv_eq. symmetry. assumption.
  - eapply conv_red_r ; eassumption.
  - eapply conv_red_l ; eassumption.
Defined.

Lemma nl_conv :
  forall {t u t' u'},
    t ≡ u ->
    nl t = nl t' ->
    nl u = nl u' ->
    t' ≡ u'.
Proof.
  intros t u t' u' h. revert t' u'.
  induction h.
  - intros t' u' ht hu.
    apply conv_eq.
    transitivity (nl t).
    + symmetry. assumption.
    + transitivity (nl u) ; assumption.
  - intros t' u' ht hu.
    destruct (nl_red1 H ht) as [t'' [? ?]].
    eapply conv_red_l ; try eassumption.
    eapply IHh ; assumption.
  - intros t' u' ht hu.
    destruct (nl_red1 H hu) as [t'' [? ?]].
    eapply conv_red_r ; try eassumption.
    eapply IHh ; assumption.
Defined.

(* WARNING AXIOM
   The only axiom that we take is transitivity of conversion.
   This should rely on confluence of the reduction which we believe is
   orthogonal to the object of the paper / formalisation.

   Note: This doesn't block any computation. We made sure to put
   typing derivations in ITT in Prop, meaning they are necessarilly
   irrelevant to computation.
 *)
Axiom conv_trans_AXIOM :
  forall {t u v},
    t ≡ u ->
    u ≡ v ->
    t ≡ v.

(* We only use the axiom in the cases that we cannot prove directly. *)
Lemma conv_trans :
  forall {t u v},
    t ≡ u ->
    u ≡ v ->
    t ≡ v.
Proof.
  intros t u v h. revert v.
  induction h ; intros w h2.
  - symmetry in H.
    eapply nl_conv ; try eassumption.
    reflexivity.
  - specialize (IHh _ h2). eapply conv_red_l ; eassumption.
  - dependent induction h2.
    + eapply nl_conv ; [ .. | eassumption ].
      * eapply conv_red_r ; eassumption.
      * reflexivity.
    + eapply conv_trans_AXIOM.
      * eapply conv_red_r ; eassumption.
      * eapply conv_red_l ; eassumption.
    + eapply conv_trans_AXIOM.
      * eapply conv_red_r ; eassumption.
      * eapply conv_red_r ; eassumption.
Defined.

End Conversion.

(*! Congruences for conversion *)

Ltac conv_rewrite_l h :=
  let h' := fresh "h" in
  match type of h with
  | ?A ≡ ?B =>
    lazymatch goal with
    | |- ?lctx ≡ ?rctx =>
      lazymatch lctx with
      | context T [A] =>
        let T1 := context T[A] in
        let T2 := context T[B] in
        assert (h' : T1 ≡ T2) ; [
          clear - h ;
          induction h ; [
            apply conv_eq ; simpl nl ; f_equal ; assumption
          | eapply conv_red_l ; [
              econstructor ; eassumption
            | eassumption
            ]
          | eapply conv_red_r ; [
              eassumption
            | econstructor ; eassumption
            ]
          ]
        | apply (conv_trans h') ; clear h'
        ]
      | _ => fail "Equation doesn't contain " A
      end
    | _ => fail "conv rewrite cannot apply to this goal"
    end
  end.

Ltac conv_rewrite h :=
  (conv_rewrite_l h) + (apply conv_sym ; conv_rewrite_l h ; apply conv_sym).

Ltac conv_rewrite_sym h :=
  let h' := fresh "h" in
  pose proof (conv_sym h) as h' ;
  conv_rewrite h' ;
  clear h'.

(* Ltac conv_rewrites hl := *)
(*   match hl with *)
(*   (* | ?h ?l => conv_rewrite h ; conv_rewrites l *) *)
(*   | ?h => conv_rewrite h *)
(*   end. *)

Tactic Notation "conv" "rewrite" hyp(h) := conv_rewrite h.
(* Tactic Notation "conv" "rewrite" hyp_list(hl) := conv_rewrites hl. *)
(* Tactic Notation "conv" "rewrite" ne_hyp_list(hl) := conv_rewrites hl. *)
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) :=
  conv rewrite h1 ; conv rewrite h2.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) :=
  conv rewrite h1 ; conv rewrite h2, h3.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4, h5.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4, h5, h6.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) "," hyp(h7) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4, h5, h6, h7.

Tactic Notation "conv" "rewrite" "<-" hyp(h) := conv_rewrite_sym h.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) :=
  conv rewrite <- h1 ; conv rewrite <- h2.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4, h5.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4, h5, h6.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) "," hyp(h7) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4, h5, h6, h7.

Section Congruence.

Context `{Sort_notion : Sorts.notion}.

Lemma cong_Heq :
  forall {A a B b A' a' B' b'},
    A ≡ A' ->
    a ≡ a' ->
    B ≡ B' ->
    b ≡ b' ->
    sHeq A a B b ≡ sHeq A' a' B' b'.
Proof.
  intros A a B b A' a' B' b' hA ha hB hb.
  conv rewrite hA, ha, hB, hb.
  apply conv_refl.
Defined.

Lemma cong_Eq :
  forall {A u v A' u' v'},
    A ≡ A' ->
    u ≡ u' ->
    v ≡ v' ->
    sEq A u v ≡ sEq A' u' v'.
Proof.
  intros A u v A' u' v' hA hu hv.
  conv rewrite hA, hu, hv.
  apply conv_refl.
Defined.

Lemma cong_Transport :
  forall {A B p t A' B' p' t'},
    A ≡ A' ->
    B ≡ B' ->
    p ≡ p' ->
    t ≡ t' ->
    sTransport A B p t ≡ sTransport A' B' p' t'.
Proof.
  intros A B p t A' B' p' t' hA hB hp ht.
  conv rewrite hA, hB, hp, ht.
  apply conv_refl.
Defined.

Lemma cong_Prod :
  forall {nx A B nx' A' B'},
    A ≡ A' ->
    B ≡ B' ->
    sProd nx A B ≡ sProd nx' A' B'.
Proof.
  intros nx A B nx' A' B' hA hB.
  conv rewrite hB, hA.
  apply conv_eq. cbn. reflexivity.
Defined.

Lemma cong_Lambda :
  forall {nx A B t nx' A' B' t'},
    A ≡ A' ->
    B ≡ B' ->
    t ≡ t' ->
    sLambda nx A B t ≡ sLambda nx' A' B' t'.
Proof.
  intros nx A B t nx' A' B' t' hA hB ht.
  conv rewrite hB, ht, hA.
  apply conv_eq. cbn. reflexivity.
Defined.

Lemma cong_App :
  forall {u A B v u' A' B' v'},
    A ≡ A' ->
    B ≡ B' ->
    u ≡ u' ->
    v ≡ v' ->
    sApp u A B v ≡ sApp u' A' B' v'.
Proof.
  intros u A B v u' A' B' v' hA hB hu hv.
  conv rewrite hB, hu, hv, hA.
  apply conv_eq. cbn. reflexivity.
Defined.

Lemma cong_Sum :
  forall {nx A B nx' A' B'},
    A ≡ A' ->
    B ≡ B' ->
    sSum nx A B ≡ sSum nx' A' B'.
Proof.
  intros nx A B nx' A' B' hA hB.
  conv rewrite hB, hA.
  apply conv_eq. cbn. reflexivity.
Defined.

Lemma cong_Pair :
  forall {A B u v A' B' u' v'},
    A ≡ A' ->
    B ≡ B' ->
    u ≡ u' ->
    v ≡ v' ->
    sPair A B u v ≡ sPair A' B' u' v'.
Proof.
  intros A B u v A' B' u' v' hA hB hu hv.
  conv rewrite hv, hu, hB, hA.
  apply conv_refl.
Defined.

Lemma cong_Pi1 :
  forall {A B p A' B' p'},
    A ≡ A' ->
    B ≡ B' ->
    p ≡ p' ->
    sPi1 A B p ≡ sPi1 A' B' p'.
Proof.
  intros A B p A' B' p' hA hB hp.
  conv rewrite hp, hB, hA.
  apply conv_refl.
Defined.

Lemma cong_Pi2 :
  forall {A B p A' B' p'},
    A ≡ A' ->
    B ≡ B' ->
    p ≡ p' ->
    sPi2 A B p ≡ sPi2 A' B' p'.
Proof.
  intros A B p A' B' p' hA hB hp.
  conv rewrite hp, hB, hA.
  apply conv_refl.
Defined.

Lemma cong_Refl :
  forall {A u A' u'},
    A ≡ A' ->
    u ≡ u' ->
    sRefl A u ≡ sRefl A' u'.
Proof.
  intros A u A' u' hA hu.
  conv rewrite hA, hu. apply conv_refl.
Defined.

Lemma cong_Pack :
  forall {A1 A2 A1' A2'},
    A1 ≡ A1' ->
    A2 ≡ A2' ->
    sPack A1 A2 ≡ sPack A1' A2'.
Proof.
  intros A1 A2 A1' A2' h1 h2.
  conv rewrite h2, h1.
  apply conv_refl.
Defined.


(** Congruence with lift *)

Lemma meta_red_eq :
  forall {t u u'},
    t ▷ u ->
    u = u' ->
    t ▷ u'.
Proof.
  intros t u u' h e. destruct e. assumption.
Defined.

Fixpoint lift_red1 {n k t1 t2} (h : t1 ▷ t2) :
  lift n k t1 ▷ lift n k t2.
Proof.
  destruct h ; cbn ;
    try match goal with
        | h : ?t ▷ _ |- ?tt ▷ _ =>
          match tt with
          | context [t] =>
            econstructor ;
              eapply lift_red1 ; [ exact h | .. ]
          end
        end.
  - eapply meta_red_eq ; [ econstructor |].
    rewrite <- substP1. cbn. reflexivity.
  - eapply meta_red_eq ; [ econstructor |]. reflexivity.
  - eapply meta_red_eq ; [ econstructor |]. reflexivity.
Defined.

Lemma lift_conv :
  forall {n k t1 t2},
    t1 ≡ t2 ->
    lift n k t1 ≡ lift n k t2.
Proof.
  intros n k t1 t2 h.
  induction h.
  - apply conv_eq. apply nl_lift. assumption.
  - eapply conv_red_l.
    + eapply lift_red1. eassumption.
    + assumption.
  - eapply conv_red_r.
    + eassumption.
    + eapply lift_red1. eassumption.
Defined.

Corollary cong_lift01 :
  forall {t1 t2},
    t1 ≡ t2 ->
    lift0 1 t1 ≡ lift0 1 t2.
Proof.
  intros t1 t2 h.
  apply lift_conv. assumption.
Defined.

(** Congruence with substitution *)

Fixpoint subst_red1 {n t1 t2 u}
  (h : t1 ▷ t2) :
  t1{ n := u } ▷ t2{ n := u }.
Proof.
  destruct h ; cbn ;
    try match goal with
        | h : ?t ▷ _ |- ?tt ▷ _ =>
          match tt with
          | context [t] =>
            econstructor ;
              eapply subst_red1 ; [ exact h | .. ]
          end
        end.
  - eapply meta_red_eq ; [ econstructor |].
    rewrite <- substP4. cbn. reflexivity.
  - eapply meta_red_eq ; [ econstructor |]. reflexivity.
  - eapply meta_red_eq ; [ econstructor |]. reflexivity.
Defined.

Lemma subst_conv :
  forall {n u t1 t2},
    t1 ≡ t2 ->
    t1{ n := u } ≡ t2{ n := u }.
Proof.
  intros n u t1 t2 h.
  induction h.
  - apply conv_eq. apply nl_subst ; [ assumption | reflexivity ].
  - eapply conv_red_l.
    + eapply subst_red1. eassumption.
    + assumption.
  - eapply conv_red_r.
    + eassumption.
    + eapply subst_red1. eassumption.
Defined.


(** Congruence of equal substitutions *)

Lemma red_trans :
  forall {t u v},
    t ▷⃰ u ->
    u ▷⃰ v ->
    t ▷⃰ v.
Proof.
  intros t u v h1 h2. revert v h2.
  induction h1.
  - intros v h2. assumption.
  - intros w h2. specialize (IHh1 w h2).
    econstructor ; eassumption.
Defined.

End Congruence.

Ltac red_rewrite h :=
  let h' := fresh "h" in
  match type of h with
  | ?A ▷⃰ ?B =>
    lazymatch goal with
    | |- ?ctx ▷⃰ _ =>
      lazymatch ctx with
      | context T [A] =>
        let T1 := context T[A] in
        let T2 := context T[B] in
        assert (h' : T1 ▷⃰ T2) ; [
          clear - h ;
          induction h ; [
            constructor
          | econstructor ; [
              econstructor ; eassumption
            | eassumption
            ]
          ]
        | eapply (red_trans h') ; clear h'
        ]
      | _ => fail "Lhs doesn't contain " A
      end
    | _ => fail "red rewrite cannot apply to this goal"
    end
  end.

Tactic Notation "red" "rewrite" hyp(h) := red_rewrite h.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) :=
  red rewrite h1 ; red rewrite h2.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) :=
  red rewrite h1 ; red rewrite h2, h3.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4) :=
  red rewrite h1 ; red rewrite h2, h3, h4.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) :=
  red rewrite h1 ; red rewrite h2, h3, h4, h5.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) :=
  red rewrite h1 ; red rewrite h2, h3, h4, h5, h6.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) "," hyp(h7) :=
  red rewrite h1 ; red rewrite h2, h3, h4, h5, h6, h7.

Section conv_substs.

  Context `{Sort_notion : Sorts.notion}.

  Ltac sp h n :=
    lazymatch goal with
    | hu : _ ▷ _ |- _ =>
      specialize (h n _ _ hu) ;
      cbn in h
    end.

  Ltac spone :=
    match goal with
    | ih : forall n u1 u2, _ -> ?t{n := u1} ≡ _ |- context [ ?t{ ?m := _ } ] =>
      sp ih m
    end.

  Ltac spall :=
    repeat spone.

  Ltac conv_rewrite_assumption :=
    match goal with
    | ih : _ ≡ _ |- _ => conv rewrite ih
    end.

  Ltac conv_rewrite_assumptions :=
    repeat conv_rewrite_assumption.

  Reserved Notation " t == u " (at level 50, u at next level).

  Inductive convbrs :
    list (nat * sterm) -> list (nat * sterm) -> Prop :=
  | convbrs_nil : [] == []
  | convbrs_cons n u v b c :
      u ≡ v ->
      b == c ->
      ((n,u) :: b) == ((n,v) :: c)

  where " t == u " := (@convbrs t u) : i_scope.

  Fact convbrs_length :
    forall {b1 b2},
      b1 == b2 ->
      #|b1| = #|b2|.
  Proof.
    intros b1 b2 h. induction h ; cbn ; easy.
  Defined.

  Lemma convbrs_nth :
    forall {b1 b2 n h1 h2},
      b1 == b2 ->
      let u := safe_nth b1 (exist _ n h1) in
      let v := safe_nth b2 (exist _ n h2) in
      (fst u = fst v) * (snd u ≡ snd v).
  Proof.
    intros b1 b2 n h1 h2 h.
    simpl in h1, h2.
    induction b1 in b2, n, h1, h2, h |- *.
    - cbn in *. lia.
    - destruct b2. 1: cbn in * ; lia.
      destruct n.
      + cbn in *. split.
        * inversion h. reflexivity.
        * inversion h. assumption.
      + cbn in *.
        lazymatch goal with
        | |- context [ safe_nth b1 (exist _ _ ?h) ] =>
          set (h1' := h)
        end.
        lazymatch goal with
        | |- context [ safe_nth b2 (exist _ _ ?h) ] =>
          set (h2' := h)
        end.
        specialize (IHb1 b2 n h1' h2').
        forward IHb1.
        { inversion h. assumption. }
        intuition auto.
  Defined.

  Lemma substs_red1 (t : sterm) :
    forall n {u1 u2},
      u1 ▷ u2 ->
      t{ n := u1 } ≡ t{ n := u2 }.
  Proof.
    induction t ; intros m u1 u2 h.
    all: cbn ; spall ; conv_rewrite_assumptions.
    all: try (apply conv_refl).
    case_eq (m ?= n) ; intro e ; bprop e.
    + eapply lift_conv.
      eapply conv_red_l ; try eassumption. apply conv_refl.
    + apply conv_refl.
    + apply conv_refl.
  Defined.

End conv_substs.

Section Substitution.

Context `{Sort_notion : Sorts.notion}.

Lemma substs_conv :
  forall {n u1 u2 t},
    u1 ≡ u2 ->
    t{ n := u1 } ≡ t{ n := u2 }.
Proof.
  intros n u1 u2 t h.
  induction h.
  - apply conv_eq. apply nl_subst ; [ reflexivity | assumption ].
  - eapply conv_trans ; try eassumption.
    eapply substs_red1. assumption.
  - eapply conv_trans ; try eassumption.
    eapply conv_sym.
    eapply substs_red1. assumption.
Defined.

Corollary cong_subst :
  forall {n u1 u2 t1 t2},
    u1 ≡ u2 ->
    t1 ≡ t2 ->
    t1{ n := u1 } ≡ t2{ n := u2 }.
Proof.
  intros n u1 u2 t1 t2 hu ht.
  eapply conv_trans.
  - eapply substs_conv. eassumption.
  - eapply subst_conv. assumption.
Defined.

End Substitution.

(*! Inversion results about conversion *)

Lemma sort_conv_inv `{Sort_notion : Sorts.notion} :
  forall {s1 s2},
    sSort s1 ≡ sSort s2 ->
    s1 = s2.
Proof.
  intros s1 s2 h. dependent induction h.
  - cbn in H. now inversion H.
  - inversion H.
  - inversion H.
Defined.

Ltac inversion_eq :=
  match goal with
  | H : _ = _ |- _ => inversion H
  end.

Ltac split_hyp ::=
  lazymatch goal with
  | h : _ /\ _ |- _ => destruct h
  | h : _ * _ |- _ => destruct h
  end.

Ltac invconv h :=
  dependent induction h ; [
    cbn in * ; inversion_eq ;
    repeat split ; apply conv_eq ; assumption
  | dependent destruction H ;
    split_hyps ; repeat split ; try assumption ;
    eapply conv_red_l ; eassumption
  | dependent destruction H ;
    split_hyps ; repeat split ; try assumption ;
    eapply conv_red_r ; eassumption
  ].

Section Inversions.

Context `{Sort_notion : Sorts.notion}.

Lemma heq_conv_inv :
  forall {A a B b A' a' B' b'},
    sHeq A a B b ≡ sHeq A' a' B' b' ->
    (A ≡ A') /\
    (a ≡ a') /\
    (B ≡ B') /\
    (b ≡ b').
Proof.
  intros A a B b A' a' B' b' h.
  invconv h.
Defined.

Lemma eq_conv_inv :
  forall {A u v A' u' v'},
    sEq A u v ≡ sEq A' u' v' ->
    (A ≡ A') /\
    (u ≡ u') /\
    (v ≡ v').
Proof.
  intros A u v A' u' v' h.
  invconv h.
Defined.

Lemma pack_conv_inv :
  forall {A1 A2 A1' A2'},
    sPack A1 A2 ≡ sPack A1' A2' ->
    (A1 ≡ A1') /\ (A2 ≡ A2').
Proof.
  intros A1 A2 A1' A2' h.
  invconv h.
Defined.

Lemma prod_inv :
  forall {nx ny A B A' B'},
    sProd nx A B ≡ sProd ny A' B' ->
    (A ≡ A') /\ (B ≡ B').
Proof.
  intros nx ny A B A' B' h.
  invconv h.
Defined.

End Inversions.