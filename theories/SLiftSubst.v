From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import Ast.
From Translation Require Import util SAst.
From Translation Require Sorts.

Open Scope type_scope.

Fixpoint lift `{Sort_notion : Sorts.notion} n k t : sterm :=
  match t with
  | sRel i => if Nat.leb k i then sRel (n + i) else sRel i
  | sLambda na T V M => sLambda na (lift n k T) (lift n (S k) V) (lift n (S k) M)
  | sApp u A B v =>
    sApp (lift n k u) (lift n k A) (lift n (S k) B) (lift n k v)
  | sProd na A B => sProd na (lift n k A) (lift n (S k) B)
  | sSum na A B => sSum na (lift n k A) (lift n (S k) B)
  | sPair A B u v =>
    sPair (lift n k A) (lift n (S k) B) (lift n k u) (lift n k v)
  | sPi1 A B p => sPi1 (lift n k A) (lift n (S k) B) (lift n k p)
  | sPi2 A B p => sPi2 (lift n k A) (lift n (S k) B) (lift n k p)
  | sEq A u v => sEq (lift n k A) (lift n k u) (lift n k v)
  | sRefl A u => sRefl (lift n k A) (lift n k u)
  | sJ A u P w v p =>
    sJ (lift n k A)
       (lift n k u)
       (lift n (S (S k)) P)
       (lift n k w)
       (lift n k v)
       (lift n k p)
  | sTransport A B p t =>
    sTransport (lift n k A) (lift n k B) (lift n k p) (lift n k t)
  | sHeq A a B b =>
    sHeq (lift n k A) (lift n k a) (lift n k B) (lift n k b)
  | sHeqToEq p => sHeqToEq (lift n k p)
  | sHeqRefl A a => sHeqRefl (lift n k A) (lift n k a)
  | sHeqSym p => sHeqSym (lift n k p)
  | sHeqTrans p q => sHeqTrans (lift n k p) (lift n k q)
  | sHeqTransport p t => sHeqTransport (lift n k p) (lift n k t)
  | sCongProd B1 B2 pA pB =>
    sCongProd (lift n (S k) B1) (lift n (S k) B2)
              (lift n k pA) (lift n (S k) pB)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (lift n (S k) B1) (lift n (S k) B2)
                (lift n (S k) t1) (lift n (S k) t2)
                (lift n k pA) (lift n (S k) pB) (lift n (S k) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (lift n (S k) B1) (lift n (S k) B2)
             (lift n k pu) (lift n k pA) (lift n (S k) pB) (lift n k pv)
  | sCongSum B1 B2 pA pB =>
    sCongSum (lift n (S k) B1) (lift n (S k) B2)
             (lift n k pA) (lift n (S k) pB)
  | sCongPair B1 B2 pA pB pu pv =>
    sCongPair (lift n (S k) B1) (lift n (S k) B2)
              (lift n k pA) (lift n (S k) pB)
              (lift n k pu) (lift n k pv)
  | sCongPi1 B1 B2 pA pB pp =>
    sCongPi1 (lift n (S k) B1) (lift n (S k) B2)
             (lift n k pA) (lift n (S k) pB) (lift n k pp)
  | sCongPi2 B1 B2 pA pB pp =>
    sCongPi2 (lift n (S k) B1) (lift n (S k) B2)
             (lift n k pA) (lift n (S k) pB) (lift n k pp)
  | sCongEq pA pu pv => sCongEq (lift n k pA) (lift n k pu) (lift n k pv)
  | sCongRefl pA pu => sCongRefl (lift n k pA) (lift n k pu)
  | sEqToHeq p => sEqToHeq (lift n k p)
  | sHeqTypeEq A B p => sHeqTypeEq (lift n k A) (lift n k B) (lift n k p)
  | sPack A1 A2 => sPack (lift n k A1) (lift n k A2)
  | sProjT1 p => sProjT1 (lift n k p)
  | sProjT2 p => sProjT2 (lift n k p)
  | sProjTe p => sProjTe (lift n k p)
  | sSort s => sSort s
  | sAx id => sAx id
  end.

Notation lift0 n t := (lift n 0 t).

Fixpoint subst `{Sort_notion : Sorts.notion} t k u :=
  match u with
  | sRel n =>
    match k ?= n with
    | Datatypes.Eq => lift0 k t
    | Gt => sRel n
    | Lt => sRel (pred n)
    end
  | sLambda na T V M =>
    sLambda na (subst t k T) (subst t (S k) V) (subst t (S k) M)
  | sApp u A B v =>
    sApp (subst t k u) (subst t k A) (subst t (S k) B) (subst t k v)
  | sProd na A B => sProd na (subst t k A) (subst t (S k) B)
  | sSum na A B => sSum na (subst t k A) (subst t (S k) B)
  | sPair A B u v =>
    sPair (subst t k A) (subst t (S k) B) (subst t k u) (subst t k v)
  | sPi1 A B p => sPi1 (subst t k A) (subst t (S k) B) (subst t k p)
  | sPi2 A B p => sPi2 (subst t k A) (subst t (S k) B) (subst t k p)
  | sEq A u v => sEq (subst t k A) (subst t k u) (subst t k v)
  | sRefl A u => sRefl (subst t k A) (subst t k u)
  | sJ A u P w v p =>
    sJ (subst t k A)
       (subst t k u)
       (subst t (S (S k)) P)
       (subst t k w)
       (subst t k v)
       (subst t k p)
  | sTransport A B p u =>
    sTransport (subst t k A) (subst t k B) (subst t k p) (subst t k u)
  | sHeq A a B b =>
    sHeq (subst t k A) (subst t k a) (subst t k B) (subst t k b)
  | sHeqToEq p => sHeqToEq (subst t k p)
  | sHeqRefl A a => sHeqRefl (subst t k A) (subst t k a)
  | sHeqSym p => sHeqSym (subst t k p)
  | sHeqTrans p q => sHeqTrans (subst t k p) (subst t k q)
  | sHeqTransport p u => sHeqTransport (subst t k p) (subst t k u)
  | sCongProd B1 B2 pA pB =>
    sCongProd (subst t (S k) B1) (subst t (S k) B2)
              (subst t k pA) (subst t (S k) pB)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (subst t (S k) B1) (subst t (S k) B2)
                (subst t (S k) t1) (subst t (S k) t2)
                (subst t k pA) (subst t (S k) pB) (subst t (S k) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (subst t (S k) B1) (subst t (S k) B2)
             (subst t k pu) (subst t k pA) (subst t (S k) pB) (subst t k pv)
  | sCongSum B1 B2 pA pB =>
    sCongSum (subst t (S k) B1) (subst t (S k) B2)
             (subst t k pA) (subst t (S k) pB)
  | sCongPair B1 B2 pA pB pu pv =>
    sCongPair (subst t (S k) B1) (subst t (S k) B2)
              (subst t k pA) (subst t (S k) pB)
              (subst t k pu) (subst t k pv)
  | sCongPi1 B1 B2 pA pB pp =>
    sCongPi1 (subst t (S k) B1) (subst t (S k) B2)
             (subst t k pA) (subst t (S k) pB) (subst t k pp)
  | sCongPi2 B1 B2 pA pB pp =>
    sCongPi2 (subst t (S k) B1) (subst t (S k) B2)
             (subst t k pA) (subst t (S k) pB) (subst t k pp)
  | sCongEq pA pu pv => sCongEq (subst t k pA) (subst t k pu) (subst t k pv)
  | sCongRefl pA pu => sCongRefl (subst t k pA) (subst t k pu)
  | sEqToHeq p => sEqToHeq (subst t k p)
  | sHeqTypeEq A B p => sHeqTypeEq (subst t k A) (subst t k B) (subst t k p)
  | sPack A1 A2 => sPack (subst t k A1) (subst t k A2)
  | sProjT1 p => sProjT1 (subst t k p)
  | sProjT2 p => sProjT2 (subst t k p)
  | sProjTe p => sProjTe (subst t k p)
  | sSort s => sSort s
  | sAx id => sAx id
  end.

Declare Scope s_scope.

Notation subst0 t u := (subst t 0 u).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity) : s_scope.

Open Scope s_scope.

Section LiftSubst.

Context `{Sort_notion : Sorts.notion}.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)]*)
Definition substl l t :=
  List.fold_left (fun t u => subst0 u t) l t.

(* Notion of closedness *)
Fixpoint closed_above k (t : sterm) :=
  match t with
  | sRel n => n <? k
  | sSort _ => true
  | sProd _ A B => closed_above k A && closed_above (S k) B
  | sLambda _ A B t =>
    closed_above k A && closed_above (S k) B && closed_above (S k) t
  | sApp u A B v =>
    closed_above k u &&
    closed_above k A &&
    closed_above (S k) B &&
    closed_above k v
  | sSum _ A B => closed_above k A && closed_above (S k) B
  | sPair A B u v =>
    closed_above k A && closed_above (S k) B &&
    closed_above k u && closed_above k v
  | sPi1 A B p => closed_above k A && closed_above (S k) B && closed_above k p
  | sPi2 A B p => closed_above k A && closed_above (S k) B && closed_above k p
  | sEq A u v =>
    closed_above k A && closed_above k u && closed_above k v
  | sRefl A u =>
    closed_above k A && closed_above k u
  | sJ A u P w v p =>
    closed_above k A &&
    closed_above k u &&
    closed_above (S (S k)) P &&
    closed_above k w &&
    closed_above k v &&
    closed_above k p
  | sTransport A B p u =>
    closed_above k A &&
    closed_above k B &&
    closed_above k p &&
    closed_above k u
  | sHeq A a B b =>
    closed_above k A &&
    closed_above k a &&
    closed_above k B &&
    closed_above k b
  | sHeqToEq p => closed_above k p
  | sHeqRefl A a => closed_above k A && closed_above k a
  | sHeqSym p => closed_above k p
  | sHeqTrans p q => closed_above k p && closed_above k q
  | sHeqTransport p u => closed_above k p && closed_above k u
  | sCongProd B1 B2 pA pB =>
    closed_above (S k) B1 && closed_above (S k) B2 &&
    closed_above k pA && closed_above (S k) pB
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    closed_above (S k) B1 && closed_above (S k) B2 &&
    closed_above (S k) t1 && closed_above (S k) t2 &&
    closed_above k pA && closed_above (S k) pB && closed_above (S k) pt
  | sCongApp B1 B2 pu pA pB pv =>
    closed_above (S k) B1 && closed_above (S k) B2 &&
    closed_above k pu && closed_above k pA &&
    closed_above (S k) pB && closed_above k pv
  | sCongSum B1 B2 pA pB =>
    closed_above (S k) B1 && closed_above (S k) B2 &&
    closed_above k pA && closed_above (S k) pB
  | sCongPair B1 B2 pA pB pu pv =>
    closed_above (S k) B1 && closed_above (S k) B2 &&
    closed_above k pA && closed_above (S k) pB &&
    closed_above k pu && closed_above k pv
  | sCongPi1 B1 B2 pA pB pp =>
    closed_above (S k) B1 && closed_above (S k) B2 &&
    closed_above k pA && closed_above (S k) pB && closed_above k pp
  | sCongPi2 B1 B2 pA pB pp =>
    closed_above (S k) B1 && closed_above (S k) B2 &&
    closed_above k pA && closed_above (S k) pB && closed_above k pp
  | sCongEq pA pu pv =>
    closed_above k pA && closed_above k pu && closed_above k pv
  | sCongRefl pA pu => closed_above k pA && closed_above k pu
  | sEqToHeq p => closed_above k p
  | sHeqTypeEq A B p => closed_above k A && closed_above k B && closed_above k p
  | sPack A1 A2 => closed_above k A1 && closed_above k A2
  | sProjT1 p => closed_above k p
  | sProjT2 p => closed_above k p
  | sProjTe p => closed_above k p
  | sAx id => true
  end.

Definition closed t := closed_above 0 t = true.

(* Lemmata regarding lifts and subst *)

Lemma lift_lift :
  forall t n m k,
    lift n k (lift m k t) = lift (n+m) k t.
Proof.
  intros t.
  induction t ; intros nn mm kk.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case.
    f_equal. mylia.
  - cbn. rewrite e. reflexivity.
Defined.

Lemma liftP1 :
  forall t i j k, lift k (j+i) (lift j i t) = lift (j+k) i t.
Proof.
  intro t.
  induction t ; intros i j k.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j+i))))%nat with (j + (S (S (S i))))%nat by mylia ;
            try replace (S (S (j+i)))%nat with (j + (S (S i)))%nat by mylia ;
            try replace (S (j+i))%nat with (j + (S i))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case.
    f_equal. mylia.
  - cbn. nat_case.
    reflexivity.
Defined.

Lemma liftP2 :
  forall t i j k n,
    i <= n ->
    lift k (j+n) (lift j i t) = lift j i (lift k n t).
Proof.
  intro t.
  induction t ; intros i j k m H.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by mylia ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by mylia ;
            try replace (S (j + m))%nat with (j + (S m))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - nat_case.
    + cbn. nat_case. nat_case.
      f_equal. mylia.
    + cbn. nat_case. nat_case.
      reflexivity.
  - cbn. nat_case. nat_case.
    cbn. nat_case. reflexivity.
Defined.

Lemma lift_subst :
  forall {t n u},
    (lift 1 n t) {n := u} = t.
Proof.
  intro t.
  induction t ; intros m u.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case. reflexivity.
  - cbn. nat_case. reflexivity.
Defined.

Lemma lift00 :
  forall {t n}, lift 0 n t = t.
Proof.
  intros t. induction t ; intro m.
  all: cbn.
  all: repeat match goal with
           | H : forall n, _ = _ |- _ => rewrite H
           end.
  all: try reflexivity.
  destruct (m <=? n) ; reflexivity.
Defined.

Lemma liftP3 :
  forall t i k j n,
    i <= k ->
    k <= (i+n)%nat ->
    lift j k (lift n i t) = lift (j+n) i t.
Proof.
  intro t. induction t ; intros i k j m ilk kl.
  all: try (cbn ; f_equal ; hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case. f_equal. mylia.
  - cbn. nat_case. reflexivity.
Defined.

Lemma substP1 :
  forall t u i j k,
    lift k (j+i) (t{j := u}) = (lift k (S (j+i)) t){ j := lift k i u }.
Proof.
  intro t. induction t ; intros u i j k.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + i)))) with ((S (S (S j))) + i)%nat by mylia ;
            try replace (S (S (j + i))) with ((S (S j)) + i)%nat by mylia ;
            try replace (S (j + i)) with ((S j) + i)%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn - [Nat.leb]. nat_case.
  - cbn. nat_case. cbn. nat_case.
    nat_case. f_equal. mylia.
  - cbn. nat_case.
    + subst. apply liftP2. mylia.
    + cbn. nat_case. reflexivity.
    + cbn. nat_case. reflexivity.
Defined.

Lemma substP2 :
  forall t u i j n,
    i <= n ->
    (lift j i t){ (j+n)%nat := u } = lift j i (t{ n := u }).
Proof.
  intros t.
  induction t ; intros u i j m h.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by mylia ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by mylia ;
            try replace (S (j + m))%nat with (j + (S m))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case.
    + nat_case. subst. rewrite liftP3 by mylia. reflexivity.
    + nat_case. cbn. nat_case. f_equal. mylia.
    + nat_case. cbn. nat_case. reflexivity.
  - cbn. nat_case. nat_case. cbn. nat_case. reflexivity.
Defined.

Lemma substP3 :
  forall t u i k n,
    i <= k ->
    k <= i + n ->
    (lift (S n) i t){ k := u } = lift n i t.
Proof.
  intro t. induction t ; intros u i k m ilk kls.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by mylia ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by mylia ;
            try replace (S (j + m))%nat with (j + (S m))%nat by mylia ;
            hyp rewrite ; reflexivity).
  cbn. nat_case.
  - cbn. nat_case. reflexivity.
  - cbn. nat_case. reflexivity.
Defined.

Lemma substP4 :
  forall t u v i j,
    t{ i := u }{ i+j := v } = t{ S (i+j) := v}{ i := u{ j := v } }.
Proof.
  intro t ; induction t ; intros u v i j.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (i + j))))%nat with ((S (S (S i))) + j)%nat by mylia ;
            try replace (S (S (i + j)))%nat with ((S (S i)) + j)%nat by mylia ;
            try replace (S (i + j))%nat with ((S i) + j)%nat by mylia ;
            hyp rewrite ; reflexivity
           ).
  cbn - [Nat.compare]. nat_case.
  - subst. nat_case. cbn. nat_case.
    rewrite substP2 by mylia. reflexivity.
  - cbn - [Nat.compare]. nat_case.
    + nat_case. rewrite substP3 by mylia. reflexivity.
    + nat_case. cbn. nat_case. reflexivity.
    + nat_case. cbn. nat_case. reflexivity.
  - cbn - [Nat.compare]. nat_case.
    nat_case. cbn. nat_case. reflexivity.
Defined.

Ltac erewrite_close_above_lift :=
  match goal with
  | H : forall n k l, k <= l -> _ = _ |- _ =>
    erewrite H by mylia
  end.

Lemma closed_above_lift :
  forall {t n k l},
    k <= l ->
    closed_above (n+l) (lift n k t) =
    closed_above l t.
Proof.
  intro t. induction t ; intros m k l h.
  all: try (cbn ;
            try replace (S (S (m+l)))%nat with (m + S (S l))%nat by mylia ;
            try replace (S (m+l))%nat with (m + S l)%nat by mylia ;
            repeat erewrite_close_above_lift ;
            reflexivity).
  unfold lift. nat_case.
  - unfold closed_above.
    nat_case.
    + nat_case. reflexivity.
    + nat_case. reflexivity.
  - unfold closed_above. nat_case. nat_case. reflexivity.
Defined.

Ltac erewrite_close_above_lift_id :=
  match goal with
  | H : forall n k l, _ -> k >= l -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.

Fact closed_above_lift_id :
  forall t n k l,
    closed_above l t = true ->
    k >= l ->
    lift n k t = t.
Proof.
  intro t. induction t ; intros m k l clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_lift_id ;
            reflexivity).
  unfold closed in clo. unfold closed_above in clo.
  bprop clo. cbn. nat_case. reflexivity.
Defined.

Fact closed_lift :
  forall t n k,
    closed t ->
    lift n k t = t.
Proof.
  intros t n k h.
  unfold closed in h.
  eapply closed_above_lift_id.
  - eassumption.
  - mylia.
Defined.

Ltac erewrite_close_above_subst :=
  match goal with
  | H : forall u l n, _ -> _ -> _ -> _ = _ |- _ =>
    erewrite H by (mylia || reflexivity || assumption)
  end.

Lemma closed_above_subst :
  forall {t u l n},
    n <= l ->
    closed_above (S l) t = true ->
    closed_above (l - n) u = true ->
    closed_above l (t{ n := u }) = true.
Proof.
  intro t. induction t ; intros u l m h0 h1 h2.
  all: try (cbn ; cbn in h1 ; repeat destruct_andb ;
            repeat erewrite_close_above_subst ; reflexivity).
  unfold closed_above in h1. bprop h1.
  cbn. nat_case.
  + subst. replace l with (n + (l - n))%nat by mylia.
    rewrite closed_above_lift by mylia. assumption.
  + unfold closed_above. nat_case. reflexivity.
  + unfold closed_above. nat_case. reflexivity.
Defined.

Ltac erewrite_close_above_subst_id :=
  match goal with
  | H : forall n l u, _ -> _ -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.

Fact closed_above_subst_id :
  forall t n l u,
    closed_above l t = true ->
    n >= l ->
    t{ n := u } = t.
Proof.
  intro t. induction t ; intros m l u clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_subst_id ;
            reflexivity).
  unfold closed in clo. unfold closed_above in clo.
  bprop clo. cbn. nat_case. reflexivity.
Defined.

Fact closed_subst :
  forall t n u,
    closed t ->
    t{ n := u } = t.
Proof.
  intros t n u h.
  unfold closed in h.
  eapply closed_above_subst_id.
  - eassumption.
  - mylia.
Defined.

End LiftSubst.

(* Exporting the tactics that were defined inside the section. *)

Ltac erewrite_close_above_lift :=
  match goal with
  | H : forall n k l, k <= l -> _ = _ |- _ =>
    erewrite H by mylia
  end.

Ltac erewrite_close_above_lift_id :=
  match goal with
  | H : forall n k l, _ -> k >= l -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.

Ltac erewrite_close_above_subst :=
  match goal with
  | H : forall u l n, _ -> _ -> _ -> _ = _ |- _ =>
    erewrite H by (mylia || eassumption)
  end.

Ltac erewrite_close_above_subst_id :=
  match goal with
  | H : forall n l u, _ -> _ -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | mylia ])
  end.