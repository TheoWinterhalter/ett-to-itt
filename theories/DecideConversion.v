(* (Semi-)Decide conversion in ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Lia.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util Sorts SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata ContextConversion Uniqueness.

Section Decide.

  Context `{Sort_notion : Sorts.notion}.

  Definition get_or {A B} (x : option A) (get : A -> B) (or : option B) : option B :=
    match x with
    | Some a => Some (get a)
    | None => or
    end.

  Notation "x '>>' a '==>' e '--' b" :=
    (get_or x (fun a => e) b) (at level 100, e at next level, right associativity).

  (* Returns [Some t'] such that [Σ |-i t ▷ t'], or [None] if it cannot be
     reduced.
     Not really applying any strategy except going deeply in the terms.
   *)
  Fixpoint reduce1 (t : sterm) {struct t} : option sterm :=
    match t with
    | sProd n A B =>
      reduce1 A >> A' ==> sProd n A' B --
      reduce1 B >> B' ==> sProd n A B' --
      None
    | sLambda n A B t =>
      reduce1 A >> A' ==> sLambda n A' B t --
      reduce1 B >> B' ==> sLambda n A B' t --
      reduce1 t >> t' ==> sLambda n A B t' --
      None
    | sApp (sLambda n _ _ t) _ _ u =>
      Some (t{ 0 := u })
    | sApp u A B v =>
      reduce1 u >> u' ==> sApp u' A B v --
      reduce1 v >> v' ==> sApp u A B v' --
      reduce1 A >> A' ==> sApp u A' B v --
      reduce1 B >> B' ==> sApp u A B' v --
      None
    | sSum n A B =>
      reduce1 A >> A' ==> sSum n A' B --
      reduce1 B >> B' ==> sSum n A B' --
      None
    (* | sPair *)
    (* | sPi1 *)
    (* | sPi2 *)
    | sEq A u v =>
      reduce1 A >> A' ==> sEq A' u v --
      reduce1 u >> u' ==> sEq A u' v --
      reduce1 v >> v' ==> sEq A u v' --
      None
    | sRefl A u =>
      reduce1 A >> A' ==> sRefl A' u --
      reduce1 u >> u' ==> sRefl A u' --
      None
    (* | sJ *)
    | sTransport _ _ (sRefl _ _) t =>
      Some t
    | sTransport A B p t =>
      reduce1 p >> p' ==> sTransport A B p' t --
      reduce1 t >> t' ==> sTransport A B p t' --
      reduce1 A >> A' ==> sTransport A' B p t --
      reduce1 B >> B' ==> sTransport A B' p t --
      None
    | sHeq A a B b =>
      reduce1 A >> A' ==> sHeq A' a B b --
      reduce1 a >> a' ==> sHeq A a' B b --
      reduce1 B >> B' ==> sHeq A a B' b --
      reduce1 b >> b' ==> sHeq A a B b' --
      None
    | sHeqToEq p =>
      reduce1 p >> p' ==> sHeqToEq p' --
      None
    | sHeqRefl A a =>
      reduce1 A >> A' ==> sHeqRefl A' a --
      reduce1 a >> a' ==> sHeqRefl A a' --
      None
    | sHeqSym p =>
      reduce1 p >> p' ==> sHeqSym p' -- None
    | sHeqTrans p q =>
      reduce1 p >> p' ==> sHeqTrans p' q --
      reduce1 q >> q' ==> sHeqTrans p q' --
      None
    | sHeqTransport p t =>
      reduce1 p >> p' ==> sHeqTransport p' t --
      reduce1 t >> t' ==> sHeqTransport p t' --
      None
    (* | sCongProd *)
    (* | sCongLambda *)
    (* | sCongApp *)
    (* | sCongSum *)
    (* | sCongPair *)
    (* | sCongPi1 *)
    (* | sCongPi2 *)
    (* | sCongEq *)
    (* | sCongRefl *)
    | sEqToHeq p =>
      reduce1 p >> p' ==> sEqToHeq p' -- None
    | sHeqTypeEq A B p =>
      reduce1 p >> p' ==> sHeqTypeEq A B p' --
      reduce1 A >> A' ==> sHeqTypeEq A' B p --
      reduce1 B >> B' ==> sHeqTypeEq A B' p --
      None
    | sProjT1 p =>
      reduce1 p >> p' ==> sProjT1 p' -- None
    | sProjT2 p =>
      reduce1 p >> p' ==> sProjT2 p' -- None
    | sProjTe p =>
      reduce1 p >> p' ==> sProjTe p' -- None
    | _ => None
    end.

  Ltac one_case :=
    lazymatch goal with
    | |- (?d >> _ ==> _ -- _) = _ -> _ =>
      case_eq d ; [
        intros ? ? h ; inversion h ; subst ; clear h ;
        constructor ; solve [ auto ]
      | intros _ ; cbn
      ]
    end.

  Lemma reduce1_sound :
    forall {t u},
      reduce1 t = Some u ->
      t ▷ u.
  Proof.
    intros t u h. revert u h.
    induction t ; intros u h.
    all: try (cbn in h ; discriminate h).
    all: try (revert h ; cbn ; repeat one_case ; discriminate).
    - destruct t1.
      all: try (revert h ; cbn ; repeat one_case ; discriminate).
      cbn in h. inversion h. subst. clear h.
      constructor.
    - destruct t3.
      all: try (revert h ; cbn ; repeat one_case ; discriminate).
      cbn in h. inversion h. subst. clear h.
      constructor.
  Defined.

  (* When it returns [true], we have [Σ |-i u = v].
     It compares the terms first by alpha-conversion, and then reduces the
     first one as much as possible, then the second one.
   *)
  Fixpoint isconv (fuel : nat) (u v : sterm) {struct fuel} : bool :=
    match fuel with
    | 0 => false
    | S fuel =>
      eq_term u v ||
      match reduce1 u with
      | Some u' => isconv fuel u' v
      | None =>
        match reduce1 v with
        | Some v' => isconv fuel u v'
        | None => false
        end
      end
    end.

  Lemma isconv_sound :
    forall {fuel u v},
      isconv fuel u v = true ->
      u ≡ v.
  Proof.
    intros fuel u v h. revert u v h.
    induction fuel ; intros u v h ; try discriminate h.
    cbn in h. apply orb_prop in h. destruct h as [h | h].
    - constructor. unfold eq_term in h.
      destruct (nl_dec (nl u) (nl v)).
      + assumption.
      + discriminate.
    - revert h. case_eq (reduce1 u).
      + intros u' hu h. eapply conv_red_l.
        * eapply reduce1_sound. eassumption.
        * eapply IHfuel. assumption.
      + intros _. case_eq (reduce1 v).
        * intros v' hv h. eapply conv_red_r.
          -- eapply IHfuel. eassumption.
          -- eapply reduce1_sound. assumption.
        * intros _. discriminate.
  Defined.

End Decide.