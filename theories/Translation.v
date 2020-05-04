From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon XTyping Conversion ITyping
               ITypingInversions ITypingLemmata ITypingAdmissible Optim
               Uniqueness SubjectReduction PackLifts FundamentalLemma.
Import ListNotations.

Section Translation.

Context `{Sort_notion : Sorts.notion}.

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
  - exfalso. abstract easy.
  - destruct m.
    + cbn. assumption.
    + cbn. apply IHe.
Defined.

Definition trans_snoc {Σ Γ A s Γ' A' s'} :
  Σ |--i Γ' ∈ ⟦ Γ ⟧ ->
  Σ ;;;; Γ' ⊢ [A'] : sSort s' ∈ ⟦ Γ ⊢ [A] : sSort s ⟧ ->
  Σ |--i Γ' ,, A' ∈ ⟦ Γ ,, A ⟧.
Proof.
  intros hΓ hA.
  split.
  - constructor ; now destruct hA as [[[? ?] ?] ?].
  - econstructor.
    + now destruct hΓ.
    + now destruct hA as [[[? ?] ?] ?].
Defined.

Definition trans_Prod {Σ Γ n A B s1 s2 Γ' A' B'} :
  Σ |--i Γ' ∈ ⟦ Γ ⟧ ->
  Σ ;;;; Γ' ⊢ [A'] : sSort s1 ∈ ⟦ Γ ⊢ [A] : sSort s1 ⟧ ->
  Σ ;;;; Γ' ,, A' ⊢ [B'] : sSort s2
  ∈ ⟦ Γ ,, A ⊢ [B]: sSort s2 ⟧ ->
  Σ ;;;; Γ' ⊢ [sProd n A' B']: sSort (Sorts.prod_sort s1 s2)
  ∈ ⟦ Γ ⊢ [ sProd n A B]: sSort (Sorts.prod_sort s1 s2) ⟧.
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
  Σ |--i Γ' ∈ ⟦ Γ ⟧ ->
  Σ ;;;; Γ' ⊢ [A'] : sSort s1 ∈ ⟦ Γ ⊢ [A] : sSort s1 ⟧ ->
  Σ ;;;; Γ' ,, A' ⊢ [B'] : sSort s2
  ∈ ⟦ Γ ,, A ⊢ [B]: sSort s2 ⟧ ->
  Σ ;;;; Γ' ⊢ [sSum n A' B']: sSort (Sorts.sum_sort s1 s2)
  ∈ ⟦ Γ ⊢ [ sSum n A B]: sSort (Sorts.sum_sort s1 s2) ⟧.
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
  Σ |--i Γ' ∈ ⟦ Γ ⟧ ->
  Σ ;;;; Γ' ⊢ [A'] : sSort s ∈ ⟦ Γ ⊢ [A] : sSort s ⟧ ->
  Σ ;;;; Γ' ⊢ [u'] : A' ∈ ⟦ Γ ⊢ [u] : A ⟧ ->
  Σ ;;;; Γ' ⊢ [v'] : A' ∈ ⟦ Γ ⊢ [v] : A ⟧ ->
  Σ ;;;; Γ' ⊢ [sEq A' u' v'] : sSort (Sorts.eq_sort s)
  ∈ ⟦ Γ ⊢ [sEq A u v] : sSort (Sorts.eq_sort s) ⟧.
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
  Σ |--i Γ' ∈ ⟦ Γ ⟧ ->
  Σ ;;;; Γ',, A' ⊢ [B']: sSort s ∈ ⟦ Γ,, A ⊢ [B]: sSort s ⟧ ->
  Σ ;;;; Γ' ⊢ [u']: A' ∈ ⟦ Γ ⊢ [u]: A ⟧ ->
  Σ ;;;; Γ' ⊢ [B'{ 0 := u' }]: sSort s ∈ ⟦ Γ ⊢ [B{ 0 := u }]: sSort s ⟧.
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
    (Σ ;;;; Γ' ⊢ [u'] : A' ∈ ⟦ Γ ⊢ [u] : A ⟧) *
    (Σ ;;;; Γ' ⊢ [v'] : A'' ∈ ⟦ Γ ⊢ [v] : A ⟧).
Proof.
  intros Σ Γ A u v Γ' A' A'' u' v' p' hg h.
  destruct h as [[[[[eΓ eS'] eS''] eA] eB] hp'].
  repeat split ; try assumption.
  all: destruct (istype_type hg hp') as [? hheq].
  all: ttinv hheq.
  all: assumption.
Defined.

Scheme typing_ind := Induction for XTyping.typing Sort Type
  with eq_term_ind := Induction for XTyping.eq_term Sort Type.

(* Set Printing Depth 100. *)

(* Combined Scheme typing_all from typing_ind , wf_ind , eq_term_ind. *)

Definition typing_all :=
  fun Σ P P0 X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15
    X16 X17 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27 =>
    (typing_ind Sort_notion Σ P P0 X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12
                X13 X14 X15 X16 X17 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27,
     eq_term_ind Sort_notion Σ P P0 X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12
                 X13 X14 X15 X16 X17 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27).

Definition complete_translation {Σ} :
  type_glob Σ ->
  (forall {Γ t A} (h : Σ ;;; Γ |-x t : A)
     {Γ'} (hΓ : Σ |--i Γ' ∈ ⟦ Γ ⟧),
      ∑ A' t', Σ ;;;; Γ' ⊢ [t'] : A' ∈ ⟦ Γ ⊢ [t] : A ⟧) *
  (forall {Γ u v A} (h : Σ ;;; Γ |-x u ≡ v : A)
     {Γ'} (hΓ : Σ |--i Γ' ∈ ⟦ Γ ⟧),
      ∑ A' A'' u' v' p',
        eqtrans Σ Γ A u v Γ' A' A'' u' v' p').
Proof.
  intro hg.
  unshelve refine (
    typing_all
      Σ
      (fun {Γ t A} (h : Σ ;;; Γ |-x t : A) => forall
           {Γ'} (hΓ : Σ |--i Γ' ∈ ⟦ Γ ⟧),
           ∑ A' t', Σ ;;;; Γ' ⊢ [t'] : A' ∈ ⟦ Γ ⊢ [t] : A ⟧)
      (fun {Γ u v A} (h : Σ ;;; Γ |-x u ≡ v : A) => forall
           {Γ'} (hΓ : Σ |--i Γ' ∈ ⟦ Γ ⟧),
           ∑ A' A'' u' v' p',
         eqtrans Σ Γ A u v Γ' A' A'' u' v' p')
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
   ) ; intros.

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
    + exists (sSort (Sorts.succ s)), (sSort s).
      repeat split.
      * now destruct hΓ.
      * constructor.
      * constructor.
      * apply type_Sort. now destruct hΓ.

    (* type_Prod *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hb') as [T' [[b'' hb''] hh]].
      clear hb' b' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we conclude *)
      exists (sSort (Sorts.prod_sort s1 s2)), (sProd n t'' b'').
      now apply trans_Prod.

    (* type_Lambda *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ ht''))
        as [S' [bty' hbty']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hbty') as [T' [[bty'' hbty''] hh]].
      clear hbty' bty' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the term *)
      destruct (X1 _ (trans_snoc hΓ ht''))
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
      destruct (X _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the function *)
      destruct (X1 _ hΓ) as [T'' [t'' ht'']].
      assert (th : type_head (head (sProd n A B))) by constructor.
      destruct (choose_type hg th ht'') as [T' [[t' ht'] hh]].
      clear ht'' t'' T''.
      destruct T' ; inversion hh. subst. clear hh th.
      rename T'1 into A'', T'2 into B''.
      destruct (change_type hg ht' (trans_Prod hΓ hA' hB')) as [t'' ht''].
      clear ht' A'' B'' t'.
      (* Translation of the argument *)
      destruct (X2 _ hΓ) as [A'' [u'' hu'']].
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
      destruct (X _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hb') as [T' [[b'' hb''] hh]].
      clear hb' b' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we conclude *)
      exists (sSort (Sorts.sum_sort s1 s2)), (sSum n t'' b'').
      now apply trans_Sum.

    (* type_Pair *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the first component *)
      destruct (X1 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* Translation of the second component *)
      destruct (X2 _ hΓ) as [Bv' [v'' hv'']].
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
      destruct (X0 _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X1 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the pair *)
      destruct (X _ hΓ) as [T'' [p'' hp'']].
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
      destruct (X0 _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X1 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the pair *)
      destruct (X _ hΓ) as [T'' [p'' hp'']].
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
      destruct (X _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA'') as [T [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T ; inversion hh. subst. clear hh th.
      (* The first term *)
      destruct (X0 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' u'' A''.
      (* The other term *)
      destruct (X1 _ hΓ) as [A'' [v'' hv'']].
      destruct (change_type hg hv'' hA') as [v' hv'].
      (* Now we conclude *)
      exists (sSort (Sorts.eq_sort s)), (sEq A' u' v').
      apply trans_Eq ; assumption.

    (* type_Refl *)
    + destruct (X0 _ hΓ) as [A' [u' hu']].
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
      destruct (X1 _ hΓ)
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
      destruct (X _ hΓ) as [A''' [t'' ht'']].
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
      { exists (optHeqTrans pA (optHeqTrans p' pB)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; try eassumption.
      }
      destruct hq as [q hq].
      destruct (opt_sort_heq_ex hg hq) as [e' he'].
      (* Now we conclude *)
      exists B', (optTransport A' B' e' t').
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht' as [[[? ?] ?] ?].
      repeat split ; try assumption.
      * apply inrel_optTransport. assumption.
      * eapply opt_Transport ; eassumption.

  (** eq_translation **)

    (* eq_reflexivity *)
    + destruct (X _ hΓ) as [A' [u' hu']].
      destruct hu' as [[[? ?] ?] hu'].
      exists A', A', u', u', (sHeqRefl A' u').
      repeat split ; try assumption.
      destruct (istype_type hg hu') as [s' hA'].
      eapply type_HeqRefl ; eassumption.

    (* eq_symmetry *)
    + destruct (X _ hΓ)
        as [A' [A'' [u' [v' [p' h']]]]].
      destruct h' as [[[[[? ?] ?] ?] ?] hp'].
      exists A'', A', v', u', (optHeqSym p').
      repeat split ; try assumption.
      eapply opt_HeqSym ; eassumption.

    (* eq_transitivity *)
    + destruct (X _ hΓ)
        as [A1 [A2 [u1 [v1 [p1 h1']]]]].
      destruct (X0 _ hΓ)
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
      exists (optHeqTrans p1 (optHeqTrans p3 p2)).
      repeat split ; try assumption.
      specialize (hp3 _ _ hv1 hv2).
      eapply opt_HeqTrans ; try assumption.
      * eassumption.
      * eapply opt_HeqTrans ; eassumption.

    (* eq_beta *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the in-term *)
      destruct (X1 _ (trans_snoc hΓ hA'))
        as [T' [t'' ht'']].
      destruct (change_type hg ht'' hB') as [t' ht'].
      clear ht'' T' t''.
      (* Translation of the argument *)
      destruct (X2 _ hΓ) as [A'' [u'' hu'']].
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
      destruct (X0 _ hΓ)
        as [S' [S'' [T1'' [T2'' [p' h']]]]].
      destruct (eqtrans_trans hg h') as [hT1'' hT2''].
      destruct h' as [[[[[eΓ eS'] eS''] eT1] eT2] hp'].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hT1'') as [T [[T1' hT1'] hh]].
      destruct T ; inversion hh. subst. clear hh.
      destruct (choose_type hg th hT2'') as [T [[T2' hT2'] hh]].
      destruct T ; inversion hh. subst. clear hh th.
      (* Translation the term conversion *)
      destruct (X _ hΓ)
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
      { exists (optHeqTrans p1 (optHeqTrans p' p2)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; try eassumption.
      }
      destruct he as [e' he'].
      rename e into eqt.
      destruct (opt_sort_heq_ex hg he') as [e he].
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
      { exists (optHeqTrans q1 (optHeqTrans q' q2)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; try eassumption.
      }
      destruct hqq as [qq hqq].
      assert (hql : ∑ ql, Σ ;;; Γ' |-i ql : sHeq T2' (sTransport T1' T2' e t1') T1' t1').
      { exists (optHeqSym (optHeqTransport e t1')).
        destruct ht1' as [_ ht1'].
        eapply opt_HeqSym ; try assumption.
        eapply opt_HeqTransport ; eassumption.
      }
      destruct hql as [ql hql].
      assert (hqr : ∑ qr, Σ ;;; Γ' |-i qr : sHeq T1' t2' T2' (sTransport T1' T2' e t2')).
      { exists (optHeqTransport e t2').
        destruct ht2' as [_ ht2'].
        eapply opt_HeqTransport ; eassumption.
      }
      destruct hqr as [qr hqr].
      assert (hqf : ∑ qf, Σ ;;; Γ' |-i qf
                                    : sHeq T2' (sTransport T1' T2' e t1')
                                           T2' (sTransport T1' T2' e t2')).
      { exists (optHeqTrans (optHeqTrans ql qq) qr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
      destruct (X _ hΓ)
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
      destruct (X0 _ (trans_snoc hΓ hA1'))
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
        exists (optHeqTrans (optHeqTrans pl pA) pr).
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pB) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        eapply type_llift0 ; eassumption.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X2 _ (trans_snoc hΓ hA2'))
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
      { exists (optHeqTrans p3 p4).
        eapply opt_HeqTrans ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* We can finally conclude! *)
      exists (sSort (Sorts.prod_sort s1 s2)), (sSort (Sorts.prod_sort s1 s2)).
      exists (sProd n1 A1' B1'), (sProd n2 A2' tB2).
      exists (optCongProd B1' tB2 p1 p5).
      destruct hA1' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct htB2 as [[[? ?] ?] ?].
      repeat split ; [ try constructor .. |].
      all: try assumption.
      eapply opt_CongProd ; try assumption.
      cbn in hp5. rewrite <- llift_substProj, <- rlift_substProj in hp5.
      rewrite !llift00, !rlift00 in hp5.
      apply hp5.

    (* cong_Lambda *)
    + (* The domains *)
      destruct (X _ hΓ)
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
      destruct (X0 _ (trans_snoc hΓ hA1'))
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
        exists (optHeqTrans (optHeqTrans pl pA) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pB) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        eapply type_llift0 ; eassumption.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X3 _ (trans_snoc hΓ hA2'))
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
      { exists (optHeqTrans p3 p4).
        eapply opt_HeqTrans ; eassumption.
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
      destruct (X1 _ (trans_snoc hΓ hA1'))
        as [B1'' [B1''' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [ht1'' ht2''].
      destruct (change_type hg ht1'' hB1') as [t1' ht1'].
      destruct (change_type hg ht2'' hB1') as [t2' ht2'].
      destruct (X5 _ (trans_snoc hΓ hA2'))
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
        exists (optHeqTrans (optHeqTrans pl pt) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
      { exists (optHeqTrans q2 q3).
        eapply opt_HeqTrans ; eassumption.
      }
      destruct hq4 as [qt hqt].
      (* We're almost done.
         However, our translation of (sLambda n2 A2 B2 t2) has to live in
         our translation of (sProd n' A1 B1).
         This is where the path between the two types comes into action.
       *)
      assert (hty : ∑ pty,
        Σ ;;; Γ' |-i pty : sHeq (sSort (Sorts.prod_sort s1 s2))
                               (sProd n2 A2' B2')
                               (sSort (Sorts.prod_sort s1 s2))
                               (sProd n1 A1' B1')

      ).
      { exists (optHeqSym (optCongProd B1' B2' pA pB)).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply opt_HeqSym ; try assumption.
        eapply opt_CongProd ; try assumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct hty as [pty hty].
      destruct (opt_sort_heq_ex hg hty) as [eT heT].
      (* We move the lambda now. *)
      pose (tλ :=
              sTransport (sProd n2 A2' B2') (sProd n1 A1' B1')
                         eT (sLambda n2 A2' B2' tt2)
      ).
      (* Now we conclude *)
      exists (sProd n1 A1' B1'), (sProd n1 A1' B1').
      exists (sLambda n1 A1' B1' t1'), tλ.
      exists (optHeqTrans (optCongLambda B1' B2' t1' tt2 pA pB qt)
                   (optHeqTransport eT (sLambda n2 A2' B2' tt2))).
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
      * eapply opt_HeqTrans ; try assumption.
        -- eapply opt_CongLambda ; try eassumption.
           ++ cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
              rewrite !llift00, !rlift00 in hpB.
              apply hpB.
           ++ cbn in hqt. rewrite <- !llift_substProj, <- !rlift_substProj in hqt.
              rewrite !llift00, !rlift00 in hqt.
              apply hqt.
        -- eapply opt_HeqTransport ; try assumption.
           ++ eapply type_Lambda ; eassumption.
           ++ eassumption.

    (* cong_App *)
    + (* The domains *)
      destruct (X _ hΓ)
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
      destruct (X0 _ (trans_snoc hΓ hA1'))
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
        exists (optHeqTrans (optHeqTrans pl pA) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pB) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        eapply type_llift0 ; eassumption.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X4 _ (trans_snoc hΓ hA2'))
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
      { exists (optHeqTrans p3 p4).
        eapply opt_HeqTrans ; eassumption.
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
      destruct (X1 _ hΓ)
        as [P1 [P1' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [ht1'' ht2''].
      destruct (change_type hg ht1'' (trans_Prod hΓ hA1' hB1')) as [t1' ht1'].
      destruct (change_type hg ht2'' (trans_Prod hΓ hA1' hB1')) as [t2' ht2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (X6 _ hΓ)
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
        exists (optHeqTrans pl (optHeqTrans pt pr)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We then translate the arguments. *)
      destruct (X2 _ hΓ)
        as [A1'' [A1''' [u1'' [u2'' [pu h4']]]]].
      destruct (eqtrans_trans hg h4') as [hu1'' hu2''].
      destruct (change_type hg hu1'' hA1') as [u1' hu1'].
      destruct h4' as [[[[[? ?] ?] ?] ?] hpu].
      destruct (X8 _ hΓ) as [A2'' [u2''' hu2''']].
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
        exists (optHeqTrans pl (optHeqTrans pu pr)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; eassumption.
      }
      destruct hqu as [qu hqu].
      (* We have an equality between Apps now *)
      assert (happ : ∑ qapp,
        Σ ;;; Γ' |-i qapp : sHeq (B1'{0 := u1'}) (sApp t1' A1' B1' u1')
                                (B2'{0 := tu2}) (sApp tt2 A2' B2' tu2)
      ).
      { exists (optCongApp B1' B2' qt pA pB qu).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply opt_CongApp ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct happ as [qapp happ].
      (* Finally we translate the right App to put it in the left Prod *)
      rename e into eA.
      pose (e := sHeqTypeEq (B2' {0 := tu2}) (B1'{0 := u1'}) (optHeqSym qapp)).
      pose (tapp := sTransport (B2' {0 := tu2}) (B1'{0 := u1'}) e (sApp tt2 A2' B2' tu2)).
      (* We conclude *)
      exists (B1'{0 := u1'}), (B1'{0 := u1'}).
      exists (sApp t1' A1' B1' u1'), tapp.
      exists (optHeqTrans qapp (optHeqTransport e (sApp tt2 A2' B2' tu2))).
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
      * eapply opt_HeqTrans ; try eassumption.
        eapply opt_HeqTransport ; try assumption.
        -- eapply type_App ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply opt_HeqSym ; eassumption.
           ++ match goal with
              | |- _ ;;; _ |-i _ : ?S =>
                change S with (S {0 := tu2})
              end.
              eapply typing_subst ; eassumption.

    (* cong_Sum *)
    + (* The domains *)
      destruct (X _ hΓ)
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
      destruct (X0 _ (trans_snoc hΓ hA1'))
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
        exists (optHeqTrans (optHeqTrans pl pA) pr).
        specialize (hpl _ _ ltac:(eassumption) ltac:(eassumption)).
        specialize (hpr _ _ ltac:(eassumption) ltac:(eassumption)).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pB) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        eapply type_llift0 ; eassumption.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X2 _ (trans_snoc hΓ hA2'))
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
      { exists (optHeqTrans p3 p4).
        eapply opt_HeqTrans ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* We can finally conclude! *)
      exists (sSort (Sorts.sum_sort s1 s2)), (sSort (Sorts.sum_sort s1 s2)).
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
      destruct (X _ hΓ)
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
      destruct (X0 _ (trans_snoc hΓ hA1'))
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
        exists (optHeqTrans (optHeqTrans pl pA) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pB) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        eapply type_llift0 ; eassumption.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X4 _ (trans_snoc hΓ hA2'))
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
      { exists (optHeqTrans p3 p4).
        eapply opt_HeqTrans ; eassumption.
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
      destruct (X1 _ hΓ)
        as [P1 [P1' [u1'' [u2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [hu1'' hu2''].
      destruct (change_type hg hu1'' hA1') as [u1' hu1'].
      destruct (change_type hg hu2'' hA1') as [u2' hu2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpu].
      destruct (X6 _ hΓ)
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
        exists (optHeqTrans pl (optHeqTrans pt pr)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We can now translate the second components. *)
      destruct (X2 _ hΓ)
        as [Q1 [Q1' [v1'' [v2'' [pt' h3']]]]].
      destruct (eqtrans_trans hg h3') as [hv1'' hv2''].
      destruct (change_type hg hv1'' (trans_subst hg hΓ hB1' hu1'))
        as [v1' hv1'].
      destruct (change_type hg hv2'' (trans_subst hg hΓ hB1' hu1'))
        as [v2' hv2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpv].
      destruct (X8 _ hΓ)
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
        exists (optHeqTrans pl (optHeqTrans pt' pr)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; eassumption.
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
      pose (e := sHeqTypeEq (sSum n A2' B2') (sSum n A1' B1') (optHeqSym qpi)).
      pose (tpi := sTransport (sSum n A2' B2') (sSum n A1' B1') e (sPair A2' B2' tu2 tv2)).
      (* We conclude *)
      exists (sSum n A1' B1'), (sSum n A1' B1').
      exists (sPair A1' B1' u1' v1'), tpi.
      exists (optHeqTrans qpi (optHeqTransport e (sPair A2' B2' tu2 tv2))).
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
      * eapply opt_HeqTrans ; try eassumption.
        eapply opt_HeqTransport ; try assumption.
        -- eapply type_Pair' ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply opt_HeqSym ; eassumption.
           ++ eapply type_Sum ; eassumption.

    (* cong_Pi1 *)
    + (* The domains *)
      destruct (X0 _ hΓ)
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
      destruct (X1 _ (trans_snoc hΓ hA1'))
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
        exists (optHeqTrans (optHeqTrans pl pA) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pB) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        eapply type_llift0 ; eassumption.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X3 _ (trans_snoc hΓ hA2'))
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
      { exists (optHeqTrans p3 p4).
        eapply opt_HeqTrans ; eassumption.
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
      destruct (X _ hΓ)
        as [P1 [P1' [p1'' [p2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [hp1'' hp2''].
      destruct (change_type hg hp1'' (trans_Sum hΓ hA1' hB1')) as [p1' hp1'].
      destruct (change_type hg hp2'' (trans_Sum hΓ hA1' hB1')) as [p2' hp2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (X5 _ hΓ)
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
        exists (optHeqTrans pl (optHeqTrans pt pr)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; eassumption.
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
      pose (e := sHeqTypeEq A2' A1' (optHeqSym qpi)).
      pose (tpi := sTransport A2' A1' e (sPi1 A2' B2' tp2)).
      (* We conclude *)
      exists A1', A1'.
      exists (sPi1 A1' B1' p1'), tpi.
      exists (optHeqTrans qpi (optHeqTransport e (sPi1 A2' B2' tp2))).
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
      * eapply opt_HeqTrans ; try eassumption.
        eapply opt_HeqTransport ; try assumption.
        -- eapply type_Pi1' ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply opt_HeqSym ; eassumption.
           ++ eassumption.

    (* cong_Pi2 *)
    + (* The domains *)
      destruct (X0 _ hΓ)
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
      destruct (X1 _ (trans_snoc hΓ hA1'))
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
        exists (optHeqTrans (optHeqTrans pl pA) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pB) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        eapply type_llift0 ; eassumption.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X3 _ (trans_snoc hΓ hA2'))
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
      { exists (optHeqTrans p3 p4).
        eapply opt_HeqTrans ; eassumption.
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
      destruct (X _ hΓ)
        as [P1 [P1' [p1'' [p2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [hp1'' hp2''].
      destruct (change_type hg hp1'' (trans_Sum hΓ hA1' hB1')) as [p1' hp1'].
      destruct (change_type hg hp2'' (trans_Sum hΓ hA1' hB1')) as [p2' hp2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (X5 _ hΓ)
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
        exists (optHeqTrans pl (optHeqTrans pt pr)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; eassumption.
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
      pose (e := sHeqTypeEq (B2' {0 := sPi1 A2' B2' tp2}) (B1' {0 := sPi1 A1' B1' p1'}) (optHeqSym qpi)).
      pose (tpi := sTransport (B2' {0 := sPi1 A2' B2' tp2}) (B1' {0 := sPi1 A1' B1' p1'}) e (sPi2 A2' B2' tp2)).
      (* We conclude *)
      exists (B1'{ 0 := sPi1 A1' B1' p1' }), (B1'{ 0 := sPi1 A1' B1' p1' }).
      exists (sPi2 A1' B1' p1'), tpi.
      exists (optHeqTrans qpi (optHeqTransport e (sPi2 A2' B2' tp2))).
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
      * eapply opt_HeqTrans ; try eassumption.
        eapply opt_HeqTransport ; try assumption.
        -- eapply type_Pi2' ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply opt_HeqSym ; eassumption.
           ++ lift_sort. eapply typing_subst ; try eassumption.
              eapply type_Pi1' ; eassumption.

    (* cong_Eq *)
    + destruct (X _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (X0 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (X1 _ hΓ)
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
        exists (optHeqTrans p1 (optHeqTrans pA p2)).
        eapply opt_HeqTrans ; try eassumption.
        eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pu) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pv) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
        - eassumption.
      }
      destruct hqv as [qv hqv].
      (* We move terms back into tA2 *)
      destruct (opt_sort_heq_ex hg hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (optHeqTrans qu (optHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTransport ; eassumption.
      }
      destruct hq as [qu' hqu'].
      pose (ttv2 := sTransport tA1 tA2 eA tv2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tv1 tA2 ttv2).
      { exists (optHeqTrans qv (optHeqTransport eA tv2)).
        destruct htv2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTransport ; eassumption.
      }
      destruct hq as [qv' hqv'].
      exists (sSort (Sorts.eq_sort s)), (sSort (Sorts.eq_sort s)).
      exists (sEq tA1 tu1 tv1), (sEq tA2 ttu2 ttv2).
      exists (optCongEq qA qu' qv').
      destruct htu1 as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct htA1 as [[[? ?] ?] ?].
      destruct htA2 as [[[? ?] ?] ?].
      destruct htv1 as [[[? ?] ?] ?].
      destruct htv2 as [[[? ?] ?] ?].
      repeat split ; try eassumption.
      * econstructor ; assumption.
      * econstructor ; assumption.
      * econstructor ; assumption.
      * econstructor ; try assumption.
        -- econstructor ; eassumption.
        -- econstructor ; eassumption.
      * eapply opt_CongEq ; assumption.

    (* cong_Refl *)
    + destruct (X _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (X0 _ hΓ)
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
        exists (optHeqTrans p1 (optHeqTrans pA p2)).
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTrans ; eassumption.
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
        exists (optHeqTrans (optHeqTrans pl pu) pr).
        eapply opt_HeqTrans ; try assumption.
        - eapply opt_HeqTrans ; eassumption.
        - eassumption.
      }
      destruct hqu as [qu hqu].
      (* tu2 isn't in the right place, so we need to chain one last equality. *)
      destruct (opt_sort_heq_ex hg hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (optHeqTrans qu (optHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply opt_HeqTrans ; try assumption.
        - eassumption.
        - eapply opt_HeqTransport ; eassumption.
      }
      destruct hq as [q hq].
      (* We're still not there yet as we need to have two translations of the
         same type. *)
      assert (pE : ∑ pE, Σ ;;; Γ' |-i pE :
                         sHeq (sSort (Sorts.eq_sort s)) (sEq tA2 ttu2 ttu2)
                              (sSort (Sorts.eq_sort s)) (sEq tA1 tu1 tu1)).
      { exists (optHeqSym (optCongEq qA q q)).
        eapply opt_HeqSym ; try assumption.
        eapply opt_CongEq ; eassumption.
      }
      destruct pE as [pE hpE].
      assert (eE : ∑ eE, Σ ;;; Γ' |-i eE :
                         sEq (sSort (Sorts.eq_sort s)) (sEq tA2 ttu2 ttu2)
                             (sEq tA1 tu1 tu1)).
      { eapply (opt_sort_heq_ex hg hpE). }
      destruct eE as [eE hE].
      pose (trefl2 := sTransport (sEq tA2 ttu2 ttu2)
                                 (sEq tA1 tu1 tu1)
                                 eE (sRefl tA2 ttu2)
           ).
      exists (sEq tA1 tu1 tu1), (sEq tA1 tu1 tu1).
      exists (sRefl tA1 tu1), trefl2.
      exists (optHeqTrans (optCongRefl qA q) (optHeqTransport eE (sRefl tA2 ttu2))).
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
      * eapply opt_HeqTrans ; try assumption.
        -- eapply opt_CongRefl ; eassumption.
        -- eapply opt_HeqTransport ; try assumption.
           ++ eapply type_Refl' ; try assumption.
              eapply type_Transport' ; eassumption.
           ++ eassumption.

    (* reflection *)
    + destruct (X _ hΓ) as [T' [e'' he'']].
      assert (th : type_head (head (sEq A u v))) by constructor.
      destruct (choose_type hg th he'') as [T'' [[e' he'] hh]].
      destruct T'' ; try (now inversion hh).
      rename T''1 into A', T''2 into u', T''3 into v'.
      clear hh he'' e'' he'' T' th.
      destruct he' as [[[? ieq] ?] he'].
      exists A', A', u', v'.
      exists (optEqToHeq e').
      inversion ieq. subst.
      repeat split ; try eassumption.
      destruct (istype_type hg he') as [? heq].
      ttinv heq.
      eapply opt_EqToHeq ; assumption.

    (* eq_alpha *)
    + destruct (X _ hΓ) as [A' [u' hu']].
      destruct hu' as [[[? ?] ?] hu'].
      exists A', A', u', u', (sHeqRefl A' u').
      repeat split ; try assumption.
      * eapply inrel_nl ; eassumption.
      * destruct (istype_type hg hu') as [s' hA'].
        eapply type_HeqRefl ; eassumption.

  Unshelve. all: try exact 0. exact nAnon.

Defined.

Theorem context_translation {Σ} :
  type_glob Σ ->
  forall Γ (h : XTyping.wf Σ Γ), ∑ Γ', Σ |--i Γ' ∈ ⟦ Γ ⟧.
Proof.
  intros hg Γ h. induction h.
  (* wf_nil *)
  + exists nil. split ; constructor.

  (* wf_snoc *)
  + destruct IHh as [Γ' hΓ'].
    rename t into hA.
    destruct (fst (complete_translation hg) _ _ _ hA _ hΓ') as [T [A' hA']].
    assert (th : type_head (head (sSort s))) by constructor.
    destruct (choose_type hg th hA') as [T' [[A'' hA''] hh]].
    destruct T' ; try (now inversion hh).
    exists (Γ' ,, A''). now eapply trans_snoc.
Defined.

End Translation.

Section Conservativity.

Context `{Sort_notion : Sorts.notion}.

Corollary conservativity :
  forall {Σ t A s},
    type_glob Σ ->
    Xcomp A ->
    Σ ;;; [] |-i A : sSort s ->
    Σ ;;; [] |-x t : A ->
    ∑ t', Σ ;;; [] |-i t' : A.
Proof.
  intros Σ t A s hg xA hA ht.
  assert (h' : Σ ;;;; [] ⊢ [ A ] : sSort s
             ∈ ⟦ [] ⊢ [ A ] : sSort s ⟧).
  { repeat split.
    - constructor.
    - constructor.
    - apply inrel_refl. assumption.
    - assumption.
  }
  destruct (complete_translation hg) as [thm _].
  destruct (thm _ _ _ ht [] ltac:(repeat constructor)) as [A' [t'' h'']].
  destruct (change_type hg h'' h') as [t' [_ ht']].
  exists t'. assumption.
Defined.

End Conservativity.

Section Consistency.

Local Existing Instance Sorts.nat_sorts.

(* Consistency of ETT relative to consistency of ITT. *)
Corollary consistency :
  forall {Σ t},
    type_glob Σ ->
    Σ ;;; [] |-x t : sProd nAnon (sSort 0) (sRel 0) ->
    ∑ t', Σ ;;; [] |-i t' : sProd nAnon (sSort 0) (sRel 0).
Proof.
  intros Σ t hg h.
  set (T := sProd nAnon (@sSort Sorts.nat_sorts 0) (sRel 0)) in *.
  eapply conservativity.
  all: try eassumption.
  - repeat constructor.
  - instantiate (1 := Sorts.prod_sort 1 0).
    econstructor.
    + econstructor. constructor.
    + refine (type_Rel _ _ _ _ _).
      * repeat econstructor.
      * auto with arith.
Defined.

End Consistency.
