(* This file illustrates the use of the plugin from ett to itt on examples. *)

From MetaCoq Require Import All.
From Translation Require Import Quotes plugin.
Import MonadNotation.
From Coq Require Import String.

Unset Universe Checking.

Open Scope string_scope.

(*! EXAMPLE 1 *)
(*
   Our first example is the identity with a coercion.
   As you can see, the definition fails in ITT/Coq.
   We thus use the notation {! _ !} that allows a term of type A
   to be given in place of any other type B.
   This is ignored by the plugin and as such it allows us to write ETT
   terms directly in Coq.
 *)
Fail Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := x.
Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}.

Run TemplateProgram (Translate ε "pseudoid").
Print pseudoidᵗ.


(*! EXAMPLE 2 *)
(*
   Inductive types.

   For this we take a look at the type of vectors.
   In order to translate an element of vec A n, we first need to add
   vec (and nat) to the context.
 *)
Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

Definition vv := vcons 1 _ vnil.
Time Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      Translate Θ "vv"
).
Print vvᵗ.


(*! EXAMPLE 3 *)
(*
   Reversal of vectors.

   Our plugin doesn't handle fixpoint and pattern-matching so we need
   to write our function with eliminators.
   Same as before we need to add the eliminator (as well as addition on natural
   numbers) to the context.
 *)

Fail Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => rv _ (vcons a m acc))
           n v m acc.

Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.

Opaque vec_rect. Opaque Init.Nat.add.
Definition vrev' :=
  Eval cbv in @vrev.
Transparent vec_rect. Transparent Init.Nat.add.

Time Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      Θ <- TranslateConstant Θ "Nat.add" ;;
      Θ <- TranslateConstant Θ "vec_rect" ;;
      Translate Θ "vrev'"
).
Print vrev'ᵗ.