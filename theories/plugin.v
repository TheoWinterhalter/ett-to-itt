(* Translation procedure *)
Unset Universe Checking.

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq Require Import All.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping ITypingLemmata
ITypingAdmissible DecideConversion XTyping Quotes Translation FundamentalLemma
FinalTranslation FullQuote XTypingLemmata IChecking
XChecking Equality plugin_util plugin_checkers.
Import MonadNotation.
Import ListNotations.


(* Not Tail-recursive for the time being *)
(* TODO Use monad_map? *)
Fixpoint map_tsl Σ G axoc l {struct l} : TemplateMonad (list term) :=
  match l with
  | t :: l =>
    match tsl_rec (2 ^ 18) Σ G [] t axoc with
    | FinalTranslation.Success t =>
      l <- map_tsl Σ G axoc l ;;
      ret (t :: l)
    | _ => tmFail "Cannot refine obligation into a Coq term"
    end
  | [] => ret []
  end.

(* Ask the user to prove obligations and returns the corresponding association table *)
(* axoc0 could be used as an accumulator but well... *)
Fixpoint map_lemma (axoc0 : assoc term) (name : ident) (l : list term)
  : TemplateMonad (assoc term) :=
  match l with
  | t :: l =>
    ty <- tmUnquoteTyped Type t ;;
    name <- tmFreshName name ;;
    lem <- tmLemma name (ty : Type) ;;
    tlem <- tmQuote lem ;;
    axoc <- map_lemma axoc0 name l ;;
    ret ((name --> tlem) axoc)
  | [] => ret axoc0
  end.

Fact istrans_nil {Σ} :
  ctxtrans Σ nil nil.
Proof.
  split.
  - constructor.
  - constructor.
Defined.

Definition type_translation {Σ} hg {Γ t A} h {Γ'} hΓ :=
  fst (@complete_translation _ Σ hg) Γ t A h Γ' hΓ.

(* Translation context *)
Record tsl_ctx := {
  Σi : sglobal_context ;
  indt : assock sterm ;
  constt : assock sterm ;
  cot : assocn sterm ;
  axoc : assoc term
}.

Definition emptyTC := {|
  Σi := [] ;
  indt := emptyk ;
  constt := emptyk ;
  cot := emptyn ;
  axoc := [< >]
|}.

Notation ε := emptyTC.

Fixpoint tc_ctor_ m (Σ : global_env) (G : universes_graph) ind Θ
  (ctors : list (prod (prod ident term) nat)) : TemplateMonad tsl_ctx :=
  match ctors with
  | t :: l =>
    Θ <- tc_ctor_ (S m) Σ G ind Θ l ;;
    let Σi := Σi Θ in
    let indt := indt Θ in
    let constt := constt Θ in
    let cot := cot Θ in
    let axoc := axoc Θ in
    (* let '(id, ty, m) := t in *)
    let '(pair (pair id ty) _) := t in
    ety <- tmEval lazy (fullquote (2 ^ 18) Σ G [] (LiftSubst.subst1 (tInd ind []) 0 ty) indt constt cot) ;;
    match ety with
    | Success ety =>
      ret {|
          Σi := (decl id ety) :: Σi ;
          indt := indt ;
          constt := constt ;
          cot := aconsn (inductive_mind ind) m (sAx id) cot ;
          axoc := (id --> tConstruct ind m []) axoc
        |}
    | Error e => tmPrint e ;; tmFail "Cannot elaborate to ETT term"
    end
  | [] => ret Θ
  end.

Notation tc_ctor := (tc_ctor_ 0).

(* Get term from ident *)
Definition getTm ident : TemplateMonad term :=
  info <- tmLocate ident ;;
  match info with
  | [ ConstRef kername ] => ret (tConst kername [])
  | [ IndRef ind ] => ret (tInd ind [])
  | [ ConstructRef ind n ] => ret (tConstruct ind n [])
  | _ => tmFail ("Unknown " @ ident)
  end.

(* Get the global context from an ident *)
Definition getCtx (ident : ident) : TemplateMonad global_env :=
  tm <- getTm ident ;;
  q  <- tmUnquote tm ;;
  prog <- tmQuoteRec (my_projT2 q : my_projT1 q) ;;
  ret (Datatypes.fst prog).

(* Note we could optimise by checking the generated context on the go.
   Then we would carry around the proof that it is correct and we would only
   have to check the extension in Translate.
   Definitely TODO
 *)
Definition TranslateConstant Θ ident : TemplateMonad tsl_ctx :=
  Σ <- getCtx ident ;;
  let Σi := Σi Θ in
  let indt := indt Θ in
  let constt := constt Θ in
  let cot := cot Θ in
  let axoc := axoc Θ in
  info <- tmLocate ident ;;
  match info with
  | [ ConstRef kername ] =>
    cbody <- tmQuoteConstant kername false ;;
    ety <- tmEval lazy (fullquote (2 ^ 18) Σ init_graph [] cbody.(cst_type) indt constt cot) ;;
    match ety with
    | Success ety =>
      tmEval all {|
          Σi := (decl ident ety) :: Σi ;
          indt := indt ;
          constt := (aconsk kername (sAx ident)) constt ;
          cot := cot ;
          axoc := (aconsk kername (tConst kername [])) axoc
        |}
    | Error e => tmPrint e ;; tmFail "Cannot elaborate to ETT term"
    end
  | [ IndRef ({| inductive_mind := kername ; inductive_ind := n |} as ind) ] =>
    mind <- tmQuoteInductive kername ;;
    match nth_error (ind_bodies mind) n with
    | Some {| ind_type := ty ; ind_ctors := ctors |} =>
      (* TODO Deal with constructors *)
      ety <- tmEval lazy (fullquote (2 ^ 18) Σ init_graph [] ty indt constt cot) ;;
      match ety with
      | Success ety =>
        Θ <- tmEval all {|
            Σi := (decl kername ety) :: Σi ;
            indt := (kername --> sAx kername) indt ;
            constt := constt ;
            cot := cot ;
            axoc := (kername --> tInd ind []) axoc
          |} ;;
        Θ <- tc_ctor Σ init_graph ind Θ ctors ;;
        tmEval all Θ
      | Error e => tmPrint e ;; tmFail "Cannot elaborate to ETT term"
      end
    | _ => tmFail "Wrong index of inductive"
    end
  | _ => tmFail ("Not a defined constant" @ ident)
  end.

Definition Translate Θ ident : TemplateMonad unit :=
  Σ <- getCtx ident ;;
  Σi <- tmEval all (Σi Θ) ;;
  indt <- tmEval all (indt Θ) ;;
  constt <- tmEval all (constt Θ) ;;
  cot <- tmEval all (cot Θ) ;;
  axoc <- tmEval all (axoc Θ) ;;
  (* First we quote the term to its TC representation *)
  cbody <- tmQuoteConstant ident false ;;
  match cbody with
  | {| cst_type := ty ; cst_body := Some tm |} =>
    (* We get its type and body and elaborate them to ETT terms *)
    pretm <- tmEval lazy (fullquote (2 ^ 18) Σ init_graph [] tm indt constt cot) ;;
    prety <- tmEval lazy (fullquote (2 ^ 18) Σ init_graph [] ty indt constt cot) ;;
    match pretm, prety with
    | Success tm, Success ty =>
      (* We pick the name framework of obligations *)
      obname <- tmEval all (ident @ "_obligation_") ;;
      name <- tmEval all (obname @ "0") ;;
      (* We then typecheck the term in ETT *)
      let ch := ettcheck Σi [] tm ty in
      match ch as o
      return (ch = o -> TemplateMonad unit)
      with
      | Some obl => fun (eq : ch = Some obl) =>
        (* We now have the list of obligations *)
        (* We push them into TC *)
        tc_obl <- map_tsl Σ init_graph axoc obl ;;
        tc_obl <- tmEval lazy tc_obl ;;
        (* We ask the user to prove the obligations in Coq *)
        axoc <- map_lemma axoc name tc_obl ;;
        (* Once they are proven we can safely apply soundness to get an ETT
           derivation, but first we need to check the whole global context *)
        let Σ' := extend Σi obname obl in
        (* First we check freshness of Σ' *)
        match isallfresh Σ' as b
        return (isallfresh Σ' = b -> TemplateMonad unit)
        with
        | true => fun eqf =>
          (* Then we check Σ' in ETT *)
          match ettcheck_ctx Σ' as b
          return (ettcheck_ctx Σ' = b -> TemplateMonad unit)
          with
          | true => fun eqcx =>
            (* We now have a derivation of our term in ETT *)
            let hf := isallfresh_sound eqf in
            let xhg := ettcheck_ctx_sound eqcx hf in
            let der := ettcheck_nil_sound obname eq xhg in
            (* Next we check the global context makes sense in ITT *)
            match ittcheck_ctx (2 ^ 18) Σ' as b
            return (ittcheck_ctx (2 ^ 18) Σ' = b -> TemplateMonad unit)
            with
            | true => fun eqc =>
              let hg := ittcheck_ctx_sound eqc hf in
              let '(_ ; itt_tm ; _) := type_translation hg der istrans_nil in
              t <- tmEval lazy (tsl_rec (2 ^ 18) Σ init_graph [] itt_tm axoc) ;;
              match t with
              | FinalTranslation.Success t =>
                tname <- tmEval all (ident @ "ᵗ") ;;
                tmMkDefinition tname t ;;
                msg <- tmEval all ("Successfully generated " @ tname) ;;
                tmPrint msg
              | FinalTranslation.Error e =>
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
            | false => fun _ => tmFail "Generated global context doesn't typecheck in ITT"
            end eq_refl
          | false => fun _ => tmFail "Generated global context doesn't typecheck in ETT"
          end eq_refl
        | false => fun _ => tmFail "Generated global context has naming conflicts"
        end eq_refl
      | None => fun (_ : ch = None) => tmFail "ETT typechecking failed"
      end eq_refl
    | e1,e2 => tmPrint e1 ;; tmPrint e2 ;; tmFail "Cannot elaborate Coq term to an ETT term"
    end
  | _ => tmFail "Expected definition of a Coq constant"
  end.