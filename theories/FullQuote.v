(* Partial translation From MetaCoqCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Lia.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq
Require Import Ast utils monad_utils Typing Checker.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping Quotes
               FinalTranslation.
Import MonadNotation.


Inductive assocn (A : Type) :=
| emptyn
| aconsn (key : string) (n : nat) (data : A) (t : assocn A).

Arguments emptyn {_}.
Arguments aconsn {_} _ _ _.

Fixpoint assocn_at {A} (key : string) (n : nat) (t : assocn A) {struct t}
  : option A :=
  match t with
  | emptyn => None
  | aconsn k m a r =>
    if (ident_eq key k) && (n =? m) then Some a else assocn_at key n r
  end.

Inductive fq_error :=
| NotEnoughFuel
| NotHandled (t : term)
| TypingError (msg : string) (e : type_error) (Γ : context) (t : term)
| WrongType (wanted : string) (got : term)
| UnknownInductive (id : string)
| UnknownConst (id : string)
| UnknownConstruct (id : string) (n : nat)
.

Inductive fq_result A :=
| Success : A -> fq_result A
| Error : fq_error -> fq_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance fq_monad : Monad fq_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc fq_error fq_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

Close Scope s_scope.

Local Existing Instance Sorts.type_in_type.

Fixpoint fullquote (fuel : nat) (Σ : global_context) (Γ : context) (t : term)
         (indt : assoc sterm) (constt : assoc sterm) (cot : assocn sterm)
         {struct fuel}
  : fq_result sterm :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | tRel n => ret (sRel n)
    | tSort _ => ret (sSort tt)
    | tProd nx A B =>
      A' <- fullquote fuel Σ Γ A indt constt cot ;;
      B' <- fullquote fuel Σ (Γ ,, vass nx A) B indt constt cot ;;
      ret (sProd nx A' B')
    | tLambda nx A t =>
      match infer_hnf fuel Σ (Γ ,, vass nx A) t with
      | Checked B =>
        A' <- fullquote fuel Σ Γ A indt constt cot ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B indt constt cot ;;
        t' <- fullquote fuel Σ (Γ ,, vass nx A) t indt constt cot ;;
        ret (sLambda nx A' B' t')
      | TypeError e => raise (TypingError "Lambda" e (Γ ,, vass nx A) t)
      end
    | tApp (tConst "Translation.Quotes.candidate" []) [ _ ; _ ; t ] =>
      fullquote fuel Σ Γ t indt constt cot
    | tInd {| inductive_mind := id ; inductive_ind := _ |} [] =>
      match assoc_at id indt with
      | Some t => ret t
      | None => raise (UnknownInductive id)
      end
    | tConst id [] =>
      match assoc_at id constt with
      | Some t => ret t
      | None => raise (UnknownConst id)
      end
    | tConstruct {| inductive_mind := id ; inductive_ind := _ |} n [] =>
      match assocn_at id n cot with
      | Some t => ret t
      | None => raise (UnknownConstruct id n)
      end
    | tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} []) [ A ; u ; v ] =>
      A' <- fullquote fuel Σ Γ A indt constt cot ;;
      u' <- fullquote fuel Σ Γ u indt constt cot ;;
      v' <- fullquote fuel Σ Γ v indt constt cot ;;
      ret (sEq A' u' v')
    | tApp u [] =>
      fullquote fuel Σ Γ u indt constt cot
    | tApp u [ v ] =>
      match infer_hnf fuel Σ Γ u with
      | Checked (tProd nx A B) =>
        u' <- fullquote fuel Σ Γ u indt constt cot ;;
        A' <- fullquote fuel Σ Γ A indt constt cot ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B indt constt cot ;;
        v' <- fullquote fuel Σ Γ v indt constt cot ;;
        ret (sApp u' A' B' v')
      | Checked T => raise (WrongType "Prod" T)
      | TypeError e => raise (TypingError "App1" e Γ u)
      end
    | tApp u (v :: l) =>
      fullquote fuel Σ Γ (tApp (tApp u [ v ]) l) indt constt cot
    | tCast t _ _ => fullquote fuel Σ Γ t indt constt cot
    | _ => raise (NotHandled t)
    end
  end.
