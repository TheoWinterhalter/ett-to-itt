From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast utils Typing AstUtils.
From Translation Require Import util SAst SLiftSubst.
From Translation Require Sorts.
Import ListNotations.

Section Common.

Context `{Sort_notion : Sorts.notion}.

Definition scontext := list sterm.

Definition ssnoc (Γ : scontext) (d : sterm) := d :: Γ.

Notation " Γ ,, d " := (ssnoc Γ d) (at level 20, d at next level) : s_scope.
Delimit Scope s_scope with s.

Record squash (A : Set) : Prop := { _ : A }.

(* Common lemmata *)

(* Lemma max_id : *)
(*   forall s, @Sorts.max Sorts.nat_sorts s s = s. *)
(* Proof. *)
(*   intro s. cbn. auto with arith. *)
(* Defined. *)

(* Lemma max_id : *)
(*   forall s, @Sorts.max Sorts.type_in_type s s = s. *)
(* Proof. *)
(*   intro s. cbn. auto with arith. *)
(* Defined. *)

(* Lemma max_succ_id : *)
(*   forall s, max_sort (succ_sort s) s = succ_sort s. *)
(* Proof. *)
(*   intro s. unfold max_sort, succ_sort. *)
(*   auto with arith. *)
(* Defined. *)

Definition sapp_context (Γ Γ' : scontext) : scontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (sapp_context Γ Γ') (at level 25, Γ' at next level, left associativity) : s_scope.

Fact cat_nil :
  forall {Γ}, Γ ,,, [] = Γ.
Proof.
  reflexivity.
Defined.

Fact nil_cat :
  forall {Γ}, [] ,,, Γ = Γ.
Proof.
  induction Γ.
  - reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact length_cat :
  forall {Γ Δ}, #|Δ ,,, Γ| = (#|Γ| + #|Δ|)%nat.
Proof.
  intros Γ. induction Γ ; intro Δ.
  - cbn. reflexivity.
  - cbn. f_equal. apply IHΓ.
Defined.

Fact safe_nth_S :
  forall {A n} {a : A} {l isdecl},
    ∑ isdecl',
      safe_nth (a :: l) (exist _ (S n) isdecl) =
      safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intros a l isdecl.
  - cbn. eexists. reflexivity.
  - eexists. cbn. reflexivity.
Defined.

Lemma eq_safe_nth' :
  forall {Γ : scontext} {n a isdecl isdecl'},
    safe_nth (a :: Γ) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n A isdecl isdecl'.
  - exfalso. abstract easy.
  - destruct n.
    + reflexivity.
    + destruct (@safe_nth_S _ (S n) A (a :: Γ) isdecl')
        as [isecl0 eq].
      rewrite eq.
      destruct (@safe_nth_S _ n a Γ isdecl)
        as [isecl1 eq1].
      rewrite eq1.
      apply IHΓ.
Defined.

Lemma eq_safe_nth :
  forall {Γ n A isdecl isdecl'},
    safe_nth (Γ ,, A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ n A isdecl isdecl'.
  apply eq_safe_nth'.
Defined.

Fact safe_nth_irr :
  forall {A n} {l : list A} {isdecl isdecl'},
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intro l ; destruct l ; intros isdecl isdecl'.
  all: cbn. all: try bang.
  - reflexivity.
  - eapply IHn.
Defined.

Fact safe_nth_cong_irr :
  forall {A n m} {l : list A} {isdecl isdecl'},
    n = m ->
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ m isdecl').
Proof.
  intros A n m l isdecl isdecl' e.
  revert isdecl isdecl'.
  rewrite e. intros isdecl isdecl'.
  apply safe_nth_irr.
Defined.

Fact safe_nth_ge :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n - #|Δ| < #|Γ| },
    n >= #|Δ| ->
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) isdecl').
Proof.
  intros Γ Δ.
  induction Δ ; intros n isdecl isdecl' h.
  - cbn in *. revert isdecl'.
    replace (n - 0) with n by mylia.
    intros isdecl'. apply safe_nth_irr.
  - destruct n.
    + cbn in *. inversion h.
    + cbn. apply IHΔ. cbn in *. mylia.
Defined.

Definition ge_sub {Γ Δ n} (isdecl : n < #|Γ ,,, Δ|) :
  n >= #|Δ| ->  n - #|Δ| < #|Γ|.
Proof.
  intro h.
  rewrite length_cat in isdecl. mylia.
Defined.

Fact safe_nth_ge' :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } (h : n >= #|Δ|),
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) (ge_sub isdecl h)).
Proof.
  intros Γ Δ n isdecl h.
  eapply safe_nth_ge. assumption.
Defined.

Fact safe_nth_lt :
  forall {n Γ Δ} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n < #|Δ| },
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Δ (exist _ n isdecl').
Proof.
  intros n. induction n ; intros Γ Δ isdecl isdecl'.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. reflexivity.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. eapply IHn.
Defined.

(** Global contexts of axioms
    Basically a list of ITT types.
 *)
Record glob_decl := { dname : ident ; dtype : sterm }.

Definition sglobal_context : Type := list glob_decl.

Fixpoint lookup_glob (Σ : sglobal_context) (id : ident) : option sterm :=
  match Σ with
  | nil => None
  | d :: Σ =>
    if ident_eq id (dname d) then Some (dtype d)
    else lookup_glob Σ id
  end.

(* Lifting of context *)

Fixpoint lift_context n Γ : scontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift n #|Γ| A) :: (lift_context n Γ)
  end.

Fact lift_context0 :
  forall {Γ}, lift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite lift00. rewrite IHΓ. reflexivity.
Defined.

Fact lift_context_length :
  forall {k Ξ}, #|lift_context k Ξ| = #|Ξ|.
Proof.
  intros k Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_lift_context :
  forall {Γ Δ : scontext} {n isdecl isdecl'},
    safe_nth (lift_context #|Γ| Δ) (exist _ n isdecl) =
    lift #|Γ| (#|Δ| - n - 1) (safe_nth Δ (exist _ n isdecl')).
Proof.
  intros Γ Δ. induction Δ.
  - cbn. intros. bang.
  - intro n. destruct n ; intros isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by mylia. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact lift_context_ex :
  forall {Δ Ξ : scontext} {n isdecl isdecl'},
    lift0 (S n) (safe_nth (lift_context #|Δ| Ξ) (exist _ n isdecl)) =
    lift #|Δ| #|Ξ| (lift0 (S n) (safe_nth Ξ (exist _ n isdecl'))).
Proof.
  intros Δ Ξ n isdecl isdecl'.
  erewrite safe_nth_lift_context.
  rewrite <- liftP2 by mylia.
  cbn.
  replace (S (n + (#|Ξ| - n - 1)))%nat with #|Ξ|.
  - reflexivity.
  - revert n isdecl isdecl'. induction Ξ ; intros n isdecl isdecl'.
    + cbn. exfalso. abstract easy.
    + cbn. f_equal.
      destruct n.
      * cbn. mylia.
      * cbn. apply IHΞ.
        -- cbn in *. mylia.
        -- cbn in *. mylia.
Defined.

(* Substitution in context *)

Fixpoint subst_context u Δ :=
  match Δ with
  | nil => nil
  | A :: Δ => (A{ #|Δ| := u }) :: (subst_context u Δ)
  end.

Fact subst_context_length :
  forall {u Ξ}, #|subst_context u Ξ| = #|Ξ|.
Proof.
  intros u Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_subst_context :
  forall {Δ : scontext} {n u isdecl isdecl'},
    (safe_nth (subst_context u Δ) (exist _ n isdecl)) =
    (safe_nth Δ (exist _ n isdecl')) { #|Δ| - S n := u }.
Proof.
  intro Δ. induction Δ.
  - cbn. intros. bang.
  - intro n. destruct n ; intros u isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by mylia. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

End Common.

Delimit Scope s_scope with s.
Notation " Γ ,, d " :=
  (ssnoc Γ d) (at level 20, d at next level) : s_scope.
Notation " Γ  ,,, Γ' " :=
  (sapp_context Γ Γ')
    (at level 25, Γ' at next level, left associativity) : s_scope.