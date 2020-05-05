(*! Notion of sort *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
From MetaCoq Require Import Ast.
From Translation Require Import util.

(* We define a notion of Sorts, reminiscent of that of a functional PTS *)
Class notion := {
  sort : Type ;
  succ : sort -> sort ;
  prod_sort : sort -> sort -> sort ;
  sum_sort : sort -> sort -> sort ;
  eq_sort : sort -> sort ;
  eq_dec : forall s z : sort, {s = z} + {s <> z} ;
  succ_inj : forall s z, succ s = succ z -> s = z
}.

#[refine] Local Instance nat_sorts : notion := {|
  sort := nat ;
  succ := S ;
  prod_sort := Nat.max ;
  sum_sort := Nat.max ;
  eq_sort s := s ;
  eq_dec := Nat.eq_dec
|}.
Proof.
  intros s z e. auto with arith.
Defined.

#[refine] Local Instance type_in_type : notion := {|
  sort := unit ;
  succ u := u ;
  prod_sort u v := tt ;
  sum_sort u v := tt ;
  eq_sort s := tt
|}.
Proof.
  - intros [] []. left. reflexivity.
  - intros [] [] _. reflexivity.
Defined.

Inductive univ := sType (n : nat) | sProp.
#[refine] Local Instance fixed_sorts : notion := {|
  sort := univ ;
  succ s :=
    match s with
    | sType n => sType (S n)
    | sProp => sProp
    end ;
  prod_sort s1 s2 :=
    match s1, s2 with
    | sType n, sType m => sType (Nat.max n m)
    | _, sProp => sProp
    | sProp, sType n => sType n
    end ;
  sum_sort s1 s2 :=
    match s1, s2 with
    | sType n, sType m => sType (Nat.max n m)
    | sType n, sProp => sType n
    | sProp, sType n => sType n
    | sProp, sProp => sProp
    end ;
  eq_sort s := s
|}.
Proof.
  - intros s z. decide equality. decide equality.
  - intros s z e.
    destruct s, z ; inversion e ; eauto.
Defined.

Inductive twolevel := F (n : nat) | U (n : nat).
#[refine] Local Instance twolevel_sorts : notion := {|
  sort := twolevel ;
  succ s :=
    match s with
    | U n => U (S n)
    | F n => F (S n)
    end ;
  prod_sort s1 s2 :=
    match s1, s2 with
    | U n, U m => U (Nat.max n m)
    | F n, F m => F (Nat.max n m)
    | U n, F m => U (Nat.max n m)
    | F n, U m => U (Nat.max n m)
    end ;
  sum_sort s1 s2 :=
    match s1, s2 with
    | U n, U m => U (Nat.max n m)
    | F n, F m => F (Nat.max n m)
    | U n, F m => U (Nat.max n m)
    | F n, U m => U (Nat.max n m)
    end ;
  eq_sort s :=
    match s with
    | U n => U n
    | F n => U n
    end
|}.
Proof.
  - intros s z. decide equality ; decide equality.
  - intros s z e.
    destruct s, z ; inversion e ; eauto.
Defined.

