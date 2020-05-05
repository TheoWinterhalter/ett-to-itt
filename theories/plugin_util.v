(* Utility library for plugin *)

Unset Universe Checking.

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import All.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
ITypingAdmissible DecideConversion XTyping Quotes Translation FundamentalLemma
FinalTranslation FullQuote XTypingLemmata IChecking
XChecking Equality.
Import MonadNotation.
Import ListNotations.

Open Scope string_scope.
Open Scope x_scope.

Module I := ITyping.

Open Scope s_scope.

Definition rev_mapi (k : nat) {A B} (f : nat -> A -> B) (l : list A) : list B :=
  let fix aux (i : nat) (l : list A) (acc : list B) : list B :=
    match l with
    | [] => acc
    | x :: l => aux (S i) l (f i x :: acc)
    end
  in aux k l [].

Open Scope list_scope.

Definition app_assoc : forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n :=
fun (A : Type) (l m n : list A) =>
list_ind (fun l0 : list A => l0 ++ m ++ n = (l0 ++ m) ++ n)
  (let H : n = n := eq_refl in
   (let H0 : m = m := eq_refl in (let H1 : A = A := eq_refl in (fun (_ : A = A) (_ : m = m) (_ : n = n) => eq_refl) H1) H0) H)
  (fun (a : A) (l0 : list A) (IHl : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
   let H : l0 ++ m ++ n = (l0 ++ m) ++ n := IHl in
   (let H0 : a = a := eq_refl in
    (let H1 : A = A := eq_refl in
     (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
      eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ m ++ n)) eq_refl) (f_equal (cons a) H4)) H1) H0) H) l.

Lemma rev_mapi_cons :
  forall {A B} {f : nat -> A -> B} {k a l},
    rev_mapi k f (a :: l) = rev_mapi (S k) f l ++ [ f k a ].
Proof.
  intros A B f.
  unfold rev_mapi.
  match goal with
  | |- forall k a l, ?faux _ _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc i, aux i l acc = aux i l [] ++ acc).
  { intro l. induction l ; intros acc i.
    - cbn. reflexivity.
    - cbn.
      pose proof (IHl [f i a] (S i)) as e1.
      pose proof (IHl (f i a :: acc) (S i)) as e2.
      refine (eq_trans e2 _).
      change (f i a :: acc) with ([f i a] ++ acc).
      rewrite e1. apply app_assoc.
  }
  intros k l a.
  apply h.
Defined.

Lemma app_cons_app :
  forall {A} {l1 : list A} {a l2},
    l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  intros A l1. induction l1 as [| b l1 ih ].
  - reflexivity.
  - intros a l2. cbn. rewrite ih. reflexivity.
Defined.

Ltac tryone a a' H :=
  destruct a, a'; simpl in *; try (reflexivity || discriminate).

Lemma ascii_Compare_eq : forall x y, ascii_compare x y = Eq <-> x = y.
Proof.
  destruct x as [a b c d e f g h].
  destruct y as [a' b' c' d' e' f' g' h'].
  split. intros H.
  tryone a a' H;
    tryone b b' H;
    tryone c c' H;
    tryone d d' H;
    tryone e e' H;
    tryone f f' H;
    tryone g g' H;
    tryone h h' H; reflexivity.
  intros H; injection H. intros; subst.
  destruct a', b', c', d', e', f', g', h'; reflexivity.
Defined.

Lemma ascii_compare_Lt x y : ascii_compare x y = Gt <-> ascii_compare y x = Lt.
Proof.
  destruct x as [a b c d e f g h].
  destruct y as [a' b' c' d' e' f' g' h'].
  split.
  intros H.
  tryone a a' H;
    tryone b b' H;
    tryone c c' H;
    tryone d d' H;
    tryone e e' H;
    tryone f f' H;
    tryone g g' H;
    tryone h h' H; try reflexivity.
  intros H.
  tryone a a' H;
    tryone b b' H;
    tryone c c' H;
    tryone d d' H;
    tryone e e' H;
    tryone f f' H;
    tryone g g' H;
    tryone h h' H; try reflexivity.
Defined.

Definition ascii_Compare (x y : Ascii.ascii) : OrderedType.Compare ascii_lt eq x y.
Proof.
  case_eq (ascii_compare x y).
  intros.
  - apply OrderedType.EQ.
    now apply ascii_Compare_eq.
  - intros. apply OrderedType.LT.
    destruct x as [a b c d e f g h].
    destruct y as [a' b' c' d' e' f' g' h'].
    unfold ascii_lt. apply H.
  - intros.
    apply OrderedType.GT. red. now apply ascii_compare_Lt.
Defined.

Definition proj2 {A B : Prop} (H : A /\ B) : B :=
  match H with
  | conj _ H1 => H1
  end.

Lemma string_compare_eq : forall x y : string, string_compare x y = Eq <-> eq x y.
Proof.
  split.
  induction x in y |- *.
  + destruct y. reflexivity.
    discriminate.
  + destruct y. discriminate.
    simpl. destruct (ascii_Compare a a0). red in a1. rewrite a1. discriminate.
    subst a0.
    pose (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
    rewrite e. intros H. specialize (IHx _ H). rewrite IHx. reflexivity.
    red in a1. apply ascii_compare_Lt in a1. rewrite a1. discriminate.
  + intros ->.
    induction y. reflexivity.
    simpl. now rewrite (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
Defined.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq.
  case_eq (string_compare x y).
  all: intro e ; constructor.
  1: apply string_compare_eq ; assumption.
  all: intro bot.
  all: apply string_compare_eq in bot.
  all: rewrite bot in e.
  all: discriminate e.
Defined.

Fact ident_neq_fresh :
  forall {Σ id ty d},
    lookup_glob Σ id = Some ty ->
    fresh_glob (dname d) Σ ->
    ident_eq id (dname d) = false.
Proof.
  intro Σ. induction Σ ; intros id ty d h hf.
  - cbn in h. discriminate h.
  - cbn in h. dependent destruction hf.
    case_eq (ident_eq id (dname a)) ;
    intro e ; rewrite e in h.
    + inversion h as [ h' ]. subst. clear h.
      destruct (ident_eq_spec id (dname d)).
      * subst. destruct (ident_eq_spec (dname d) (dname a)).
        -- exfalso. easy.
        -- easy.
      * reflexivity.
    + eapply IHΣ ; eassumption.
Defined.

Lemma nth_error_app2 A (l : list A) l' n :
  length l <= n ->
  nth_error (l++l') n = nth_error l' (n- length l).
Proof.
  revert l.
  induction n; intros [|a l] H; auto.
  - inversion H.
  - simpl in *. apply IHn. mylia.
Defined.

Open Scope nat_scope.

Definition app_length : forall (A : Type) (l l' : list A), #|l ++ l'| = (#|l| + #|l'|)%nat :=
fun (A : Type) (l : list A) =>
list_ind (fun l0 : list A => forall l' : list A, #|l0 ++ l'| = #|l0| + #|l'|) (fun l' : list A => eq_refl)
  (fun (a : A) (l0 : list A) (IHl : forall l' : list A, #|l0 ++ l'| = #|l0| + #|l'|) (l' : list A) =>
   f_equal_nat nat S #|l0 ++ l'| (#|l0| + #|l'|) (IHl l')) l.

Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    rewrite <- IHl. reflexivity.
Defined.

Definition some_inj (A : Type) (x y : A) (H : Some x = Some y) : x = y :=
  f_equal (fun e : option A =>
             match e with
             | Some a => a
             | None => x
             end) H.

Lemma nth_error_Some_safe_nth A (l : list A) n c :
  forall e : nth_error l n = Some c,
    safe_nth l (exist _ n (nth_error_Some_length e)) = c.
Proof.
  intros H.
  pose proof (nth_error_safe_nth _ _ (nth_error_Some_length H)).
  pose proof (eq_trans (eq_sym H) H0).
  apply some_inj in H1. exact (eq_sym H1).
Defined.

Definition app_nil_r :  forall (A : Type) (l : list A), l ++ [] = l :=
fun (A : Type) (l : list A) =>
list_ind (fun l0 : list A => l0 ++ [] = l0) (let H : A = A := eq_refl in (fun _ : A = A => eq_refl) H)
  (fun (a : A) (l0 : list A) (IHl : l0 ++ [] = l0) =>
   let H : l0 ++ [] = l0 := IHl in
   (let H0 : a = a := eq_refl in
    (let H1 : A = A := eq_refl in
     (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ [] = l0) =>
      eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ [])) eq_refl) (f_equal (cons a) H4)) H1) H0) H) l.