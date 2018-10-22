(* This file illustrates the use of the plugin from ett to itt on examples. *)

From Template Require Import All.
From Translation Require Import Quotes plugin.
Import MonadNotation.

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

(* Time Run TemplateProgram ( *)
(*       Θ <- TranslateConstant ε "nat" ;; *)
(*       Θ <- TranslateConstant Θ "vec" ;; *)
(*       Θ <- TranslateConstant Θ "Nat.add" ;; *)
(*       Θ <- TranslateConstant Θ "vec_rect" ;; *)
(*       Translate Θ "vrev'" *)
(* ). *)
(* Print vrev'ᵗ. *)

(* Profiling *)

From Equations Require Import Equations DepElimDec.

Definition tmDef ident : forall {A}, A -> TemplateMonad () :=
  fun A x =>
    t <- tmQuote x ;;
    tmMkDefinition ident t.

Time Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      Θ <- TranslateConstant Θ "Nat.add" ;;
      Θ <- TranslateConstant Θ "vec_rect" ;;
      Θ <- tmQuote Θ ;;
      tmMkDefinition "Θ" Θ
).

Time Run TemplateProgram (
       Σ <- getCtx "vrev'" ;;
       tmDef "Σ" Σ
).

Time Run TemplateProgram (
  Σi <- tmEval all (Σi Θ) ;;
  indt <- tmEval all (indt Θ) ;;
  constt <- tmEval all (constt Θ) ;;
  cot <- tmEval all (cot Θ) ;;
  axoc <- tmEval all (axoc Θ) ;;
  tmDef "Σi" Σi ;;
  tmDef "indt" indt ;;
  tmDef "constt" constt ;;
  tmDef "cot" cot ;;
  tmDef "axoc" axoc
).

Definition ident := "vrev'".

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
ITypingAdmissible DecideConversion XTyping Quotes Translation FundamentalLemma
FinalTranslation FullQuote XTypingLemmata IChecking
XChecking Equality plugin_util plugin_checkers.

Time Run TemplateProgram (
  entry <- tmQuoteConstant ident false ;;
  match entry with
  | DefinitionEntry {| definition_entry_body := tm ; definition_entry_type := ty |} =>
    pretm <- tmEval lazy (fullquote (2 ^ 18) Σ [] tm indt constt cot) ;;
    prety <- tmEval lazy (fullquote (2 ^ 18) Σ [] ty indt constt cot) ;;
    tmDef "pretm" pretm ;;
    tmDef "prety" prety
  | _ => tmFail "Expected definition of a Coq constant"
  end
).

Time Run TemplateProgram (
  match pretm, prety with
  | Success tm, Success ty =>
    obname <- tmEval all (ident @ "_obligation_") ;;
    name <- tmEval all (obname @ "0") ;;
    tmDef "obname" obname ;;
    tmDef "name" name ;;
    tmDef "tm" tm ;;
    tmDef "ty" ty ;;
    let ch := ettcheck Σi [] tm ty in
    match ch as o
    return (ch = o -> TemplateMonad ())
    with
    | Some obl => fun (eq : ch = Some obl) => tmDef "ch" ch ;; tmDef "obl" obl ;; tmDef "eq" eq
    | None => fun (_ : ch = None) => tmFail "ETT typechecking failed"
    end eq_refl
  | e1,e2 => tmPrint e1 ;; tmPrint e2 ;; tmFail "Cannot elaborate Coq term to an ETT term"
  end
).

Time Run TemplateProgram (
  tc_obl <- map_tsl Σ axoc obl ;;
  tc_obl <- tmEval lazy tc_obl ;;
  tmDef "tc_obl" tc_obl
).

Time Run TemplateProgram (
  (* axoc <- map_lemma axoc name tc_obl ;; *)
  axoc <- map_lemma axoc "vrev'_obligation_0" tc_obl ;;
  tmDef "axoc2" axoc
).

Time Run TemplateProgram (
  let Σ' := extend Σi obname obl in
  match isallfresh Σ' as b
  return (isallfresh Σ' = b -> TemplateMonad ())
  with
  | true => fun eqf => tmDef "Σ'" Σ' ;; tmDef "eqf" eqf
  | false => fun _ => tmFail "Generated global context has naming conflicts"
  end eq_refl
).
(* This is taking a loooong time to check freshness! *)

Time Run TemplateProgram (
  match ettcheck_ctx Σ' as b
  return (ettcheck_ctx Σ' = b -> TemplateMonad ())
  with
  | true => fun eqcx => tmDef "eqcx" eqcx
  | false => fun _ => tmFail "Generated global context doesn't typecheck in ETT"
  end eq_refl
).

Time Run TemplateProgram (
  let hf := isallfresh_sound eqf in
  let xhg := ettcheck_ctx_sound eqcx hf in
  let der := ettcheck_nil_sound obname (eq : ettcheck Σi [] tm ty = Some obl) xhg in
  tmDef "hf" hf ;;
  tmDef "xhg" xhg ;;
  tmDef "der" der ;;
  match ittcheck_ctx (2 ^ 18) Σ' as b
  return (ittcheck_ctx (2 ^ 18) Σ' = b -> TemplateMonad ())
  with
  | true => fun eqc => tmDef "eqc" eqc
  | false => fun _ => tmFail "Generated global context doesn't typecheck in ITT"
  end eq_refl
).

Time Run TemplateProgram (
  let hg := ittcheck_ctx_sound eqc hf in
  tmDef "hg" hg ;;
  let '(_ ; itt_tm ; _) := type_translation hg der istrans_nil in
  t <- tmEval lazy (tsl_rec (2 ^ 18) Σ [] itt_tm axoc2) ;;
  tmDef "t" t
).

Time Run TemplateProgram (
  match t with
  | FinalTranslation.Success _ t =>
    tname <- tmEval all (ident @ "ᵗ") ;;
    tmMkDefinition tname t ;;
    msg <- tmEval all ("Successfully generated " @ tname) ;;
    tmPrint msg
  | FinalTranslation.Error _ e =>
    msg <- tmEval all ("Cannot translate from ITT to TemplateCoq: " @
          match e with
          | FinalTranslation.NotEnoughFuel => "Not enough fuel"
          | FinalTranslation.TranslationNotFound id => "Not found " @ id
          | FinalTranslation.TranslationNotHandled => "Translation not handled"
          | FinalTranslation.TypingError msg _ => "Typing error - " @ msg
          | FinalTranslation.UnexpectedTranslation s _ _ _ => "Unexpected translation " @ s
          end) ;;
    tmFail msg
  end
).
