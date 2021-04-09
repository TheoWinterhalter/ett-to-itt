(* Partial translation From MetaCoqCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq
Require Import Ast utils monad_utils Typing Checker AstUtils uGraph.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping Quotes
               FinalTranslation.
Import MonadNotation.
Import ListNotations.


Inductive assocn (A : Type) :=
| emptyn
| aconsn (key : kername) (n : nat) (data : A) (t : assocn A).

Arguments emptyn {_}.
Arguments aconsn {_} _ _ _.

Fixpoint assocn_at {A} (key : kername) (n : nat) (t : assocn A) {struct t}
  : option A :=
  match t with
  | emptyn => None
  | aconsn k m a r =>
    if (eq_kername key k) && (n =? m) then Some a else assocn_at key n r
  end.

(* Associative table indexed by kernames *)
Inductive assock (A : Type) :=
| emptyk
| aconsk (key : kername) (data : A) (t : assock A).

Arguments emptyk {_}.
Arguments aconsk {_} _ _.

Fixpoint assock_at {A} (key : kername) (t : assock A) {struct t} : option A :=
  match t with
  | emptyk => None
  | aconsk k a r => if eq_kername key k then Some a else assock_at key r
  end.

Inductive fq_error :=
| NotEnoughFuel
| NotHandled (t : term)
| TypingError (msg : string) (e : type_error) (Γ : context) (t : term)
| WrongType (wanted : string) (got : term)
| UnknownInductive (id : kername)
| UnknownConst (id : kername)
| UnknownConstruct (id : kername) (n : nat)
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

Open Scope string_scope.

Existing Instance default_fuel.

Definition an (a : aname) : name := binder_name a.

Fixpoint fullquote (fuel : nat) (Σ : global_env) (G : universes_graph)
  (Γ : context) (t : term) (indt : assock sterm) (constt : assock sterm)
  (cot : assocn sterm) {struct fuel}
  : fq_result sterm :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | tRel n => ret (sRel n)
    | tSort _ => ret (sSort tt)
    | tProd nx A B =>
      A' <- fullquote fuel Σ G Γ A indt constt cot ;;
      B' <- fullquote fuel Σ G (Γ ,, vass nx A) B indt constt cot ;;
      ret (sProd (an nx) A' B')
    | tLambda nx A t =>
      match infer_hnf Σ G (Γ ,, vass nx A) t with
      | Checked B =>
        A' <- fullquote fuel Σ G Γ A indt constt cot ;;
        B' <- fullquote fuel Σ G (Γ ,, vass nx A) B indt constt cot ;;
        t' <- fullquote fuel Σ G (Γ ,, vass nx A) t indt constt cot ;;
        ret (sLambda (an nx) A' B' t')
      | TypeError e => raise (TypingError "Lambda" e (Γ ,, vass nx A) t)
      end
    | tApp u l =>
      match u, l with
      | tConst id ui, [ A ; B ; t ] =>
        if eq_kername id (MPfile ["Quotes"; "Translation"], "candidate")%core
        then fullquote fuel Σ G Γ t indt constt cot
        else fullquote fuel Σ G Γ (tApp (tApp u [ A ]) [ B ; t ]) indt constt cot
      | tInd {| inductive_mind := id ; inductive_ind := 0 |} ui, [ A ; x ; y ] =>
        if eq_kername id (MPfile ["Logic"; "Init"; "Coq"], "eq")%core
        then
          A' <- fullquote fuel Σ G Γ A indt constt cot ;;
          x' <- fullquote fuel Σ G Γ x indt constt cot ;;
          y' <- fullquote fuel Σ G Γ y indt constt cot ;;
          ret (sEq A' x' y')
        else fullquote fuel Σ G Γ (tApp (tApp u [ A ]) [ x ; y ]) indt constt cot
      | u, [ v ] =>
        match infer_hnf Σ G Γ u with
        | Checked (tProd nx A B) =>
          u' <- fullquote fuel Σ G Γ u indt constt cot ;;
          A' <- fullquote fuel Σ G Γ A indt constt cot ;;
          B' <- fullquote fuel Σ G (Γ ,, vass nx A) B indt constt cot ;;
          v' <- fullquote fuel Σ G Γ v indt constt cot ;;
          ret (sApp u' A' B' v')
        | Checked T => raise (WrongType "Prod" T)
        | TypeError e => raise (TypingError "App1" e Γ u)
        end
      | u, v :: l =>
        fullquote fuel Σ G Γ (tApp (tApp u [ v ]) l) indt constt cot
      | u, [] =>
        fullquote fuel Σ G Γ u indt constt cot
      (* | _ => raise (NotHandled t) *)
      end
    | tInd {| inductive_mind := id ; inductive_ind := _ |} [] =>
      match assock_at id indt with
      | Some t => ret t
      | None => raise (UnknownInductive id)
      end
    | tConst id [] =>
      match assock_at id constt with
      | Some t => ret t
      | None => raise (UnknownConst id)
      end
    | tConstruct {| inductive_mind := id ; inductive_ind := _ |} n [] =>
      match assocn_at id n cot with
      | Some t => ret t
      | None => raise (UnknownConstruct id n)
      end
    | tCast t _ _ => fullquote fuel Σ G Γ t indt constt cot
    | _ => raise (NotHandled t)
    end
  end.
