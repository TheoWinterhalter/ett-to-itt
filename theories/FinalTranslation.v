(* Translation from our special ITT to TemplateCoq itself  *)

From Coq Require Import Bool String List BinPos Compare_dec Lia Arith.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From MetaCoq
Require Import config Ast utils monad_utils Typing Checker AstUtils uGraph.
From Translation
Require Import util Sorts SAst SLiftSubst SCommon ITyping Quotes.
Import MonadNotation.
Import ListNotations.

(* Associative table indexed by strings *)
Inductive assoc (A : Type) :=
| empty
| acons (key : string) (data : A) (t : assoc A).

Arguments empty {_}.
Arguments acons {_} _ _.

Fixpoint assoc_at {A} (key : string) (t : assoc A) {struct t} : option A :=
  match t with
  | empty => None
  | acons k a r => if string_dec key k then Some a else assoc_at key r
  end.

Module T := Typing.

Section Final.

Existing Instance config.type_in_type.
Existing Instance Sorts.type_in_type.

(* From Simon Boulier *)
Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandled
| TypingError (msg : string) (t : type_error)
| UnexpectedTranslation (msg : string) (p : sterm) (p' ty : term)
.

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

(* For now, we'll let TemplateCoq deal with universes on its own. *)
Definition sort_to_universe (s : sort) : Universe.t := Universe.type0.
(* Definition sort_to_universe (s : sort) : Universe.t := []. *)
  (* match s with *)
  (* | 0 => (* Universe.type0 *) [] *)
  (* | S n => [] *)
  (* end. *)

Existing Instance default_fuel.

Definition hnf (Σ : global_env) (Γ : context) (t : term) : typing_result term :=
  r <- hnf_stack Σ Γ t ;;
  ret (zip r).

Definition myret (Σ : global_env) (Γ : context) (t : term) : tsl_result term :=
  Success t.
  (* match hnf Σ Γ t with *)
  (* | Checked t' => Success t' *)
  (* | _ => Error TranslationNotHandled *)
  (* end. *)

(* TODO Use type_of instead *)
Definition infer_hnf (Σ : global_env) (G : universes_graph) Γ t :=
  t' <- infer Σ G Γ t ;;
  hnf Σ Γ t'.

Fixpoint brs_repack (l : list (nat * tsl_result term)) :
  tsl_result (list (prod nat term)) :=
  match l with
  | [] => Success []
  | (n, Success t) :: tl =>
    match brs_repack tl with
    | Success tl' => Success ((pair n t) :: tl')
    | Error e => Error e
    end
  | (_, Error e) :: _ => Error e
  end.

Close Scope s_scope.

Definition rn (n : name) := mkBindAnn n Relevant.

(* It's possible that matching on strings is a terrible idea
  for efficiency, and it should be replaced by decidable equality.
*)
Fixpoint tsl_rec (fuel : nat) (Σ : global_env) (G : universes_graph) (Γ : context) (t : sterm)
         (axt : assoc term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | sRel n => ret (tRel n)
    | sSort s => ret (tSort (sort_to_universe s))
    | sProd n A B =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      B' <- tsl_rec fuel Σ G (Γ ,, vass (rn n) A') B axt ;;
      ret (tProd (rn n) A' B')
    | sLambda n A B t =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      t' <- tsl_rec fuel Σ G (Γ ,, vass (rn n) A') t axt ;;
      ret (tLambda (rn n) A' t')
    | sApp u A B v =>
      u' <- tsl_rec fuel Σ G Γ u axt ;;
      v' <- tsl_rec fuel Σ G Γ v axt ;;
      myret Σ Γ (tApp u' [v'])
    | sSum n A B =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      B' <- tsl_rec fuel Σ G (Γ ,, vass (rn n) A') B axt ;;
      ret (mkSum A' B')
    | sPair A B u v =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      B' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A') B axt ;;
      u' <- tsl_rec fuel Σ G Γ u axt ;;
      v' <- tsl_rec fuel Σ G Γ v axt ;;
      myret Σ Γ (mkPair A' B' u' v')
    | sPi1 A B p =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      B' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A') B axt ;;
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      myret Σ Γ (mkPi1 A' B' p')
    | sPi2 A B p =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      B' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A') B axt ;;
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      myret Σ Γ (mkPi2 A' B' p')
    | sEq A u v =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      u' <- tsl_rec fuel Σ G Γ u axt ;;
      v' <- tsl_rec fuel Σ G Γ v axt ;;
      ret (mkEq A' u' v')
    | sRefl A u =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      u' <- tsl_rec fuel Σ G Γ u axt ;;
      ret (mkRefl A' u')
    | sJ A u P w v p =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      u' <- tsl_rec fuel Σ G Γ u axt ;;
      P' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A' ,, vass nAnon' (mkEq (LiftSubst.lift0 1 A') (LiftSubst.lift0 1 u') (tRel 0))) P axt ;;
      w' <- tsl_rec fuel Σ G Γ w axt ;;
      v' <- tsl_rec fuel Σ G Γ v axt ;;
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      myret Σ Γ (mkJ A' u' P' w' v' p')
    | sTransport T1 T2 p t =>
      T1' <- tsl_rec fuel Σ G Γ T1 axt ;;
      T2' <- tsl_rec fuel Σ G Γ T2 axt ;;
      t' <- tsl_rec fuel Σ G Γ t axt ;;
      (* Final optimisation to remove useless transports *)
      match check_conv Σ G Γ T1' T2' with
      | Checked tt => myret Σ Γ t'
      | _ =>
        p' <- tsl_rec fuel Σ G Γ p axt ;;
        myret Σ Γ (mkTransport T1' T2' p' t')
      end
    | sHeq A a B b =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      B' <- tsl_rec fuel Σ G Γ B axt ;;
      a' <- tsl_rec fuel Σ G Γ a axt ;;
      b' <- tsl_rec fuel Σ G Γ b axt ;;
      ret (mkHeq A' a' B' b')
    | sHeqToEq p =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ A' ; u' ; _ ; v' ]) =>
        myret Σ Γ (mkHeqToHeq A' u' v' p')
      | Checked T => raise (UnexpectedTranslation "HeqToEq" p p' T)
      | TypeError t => raise (TypingError "HeqToEq" t)
      end
    | sHeqRefl A a =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      a' <- tsl_rec fuel Σ G Γ a axt ;;
      myret Σ Γ (mkHeqRefl A' a')
    | sHeqSym p =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ A' ; a' ; B' ; b' ]) =>
        myret Σ Γ (mkHeqSym A' a' B' b' p')
      | Checked T => raise (UnexpectedTranslation "HeqSym" p p' T)
      | TypeError t => raise (TypingError "HeqSym" t)
      end
    | sHeqTrans p q =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      q' <- tsl_rec fuel Σ G Γ q axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ A' ; a' ; B' ; b' ]) =>
        match infer_hnf Σ G Γ q' with
        | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; _ ; C' ; c' ]) =>
          myret Σ Γ (mkHeqTrans A' a' B' b' C' c' p' q')
        | Checked T => raise (UnexpectedTranslation "HeqTrans 1" q q' T)
        | TypeError t => raise (TypingError "HeqTrans 1" t)
        end
      | Checked T => raise (UnexpectedTranslation "HeqTrans 2" p p' T)
      | TypeError t => raise (TypingError "HeqTrans 2" t)
      end
    | sHeqTransport p t =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      t' <- tsl_rec fuel Σ G Γ t axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Logic"; "Init"; "Coq"], "eq")%core 0) _) [ _ ; A' ; B' ]) =>
        myret Σ Γ (mkHeqTransport A' B' p' t')
      | Checked T => raise (UnexpectedTranslation "HeqTransport" p p' T)
      | TypeError t => raise (TypingError "HeqTransport" t)
      end
    | sCongProd B1 B2 pA pB =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      match infer_hnf Σ G Γ pA' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pB axt ;;
        B1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') B1 axt ;;
        B2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') B2 axt ;;
        myret Σ Γ (mkCongProd A1' A2' B1' B2' pA' pB')
      | Checked T => raise (UnexpectedTranslation "CongProd" pA pA' T)
      | TypeError t => raise (TypingError "CongProd" t)
      end
    | sCongLambda B1 B2 t1 t2 pA pB pt =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      match infer_hnf Σ G Γ pA' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pB axt ;;
        pt' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pt axt ;;
        B1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') B1 axt ;;
        B2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') B2 axt ;;
        t1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') t1 axt ;;
        t2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') t2 axt ;;
        myret Σ Γ (mkCongLambda A1' A2' B1' B2' t1' t2' pA' pB' pt')
      | Checked T => raise (UnexpectedTranslation "CongLambda" pA pA' T)
      | TypeError t => raise (TypingError "CongLambda" t)
      end
    | sCongApp B1 B2 pt pA pB pu =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      match infer_hnf Σ G Γ pA' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pB axt ;;
        pt' <- tsl_rec fuel Σ G Γ pt axt ;;
        pu' <- tsl_rec fuel Σ G Γ pu axt ;;
        B1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') B1 axt ;;
        B2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') B2 axt ;;
        match infer_hnf Σ G Γ pt' with
        | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; t1' ; _ ; t2' ]) =>
          match infer_hnf Σ G Γ pu' with
          | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; u1' ; _ ; u2' ]) =>
            myret Σ Γ (mkCongApp A1' A2' B1' B2' t1' t2' u1' u2' pA' pB' pt' pu')
          | Checked T => raise (UnexpectedTranslation "CongApp 1" pu pu' T)
          | TypeError t => raise (TypingError "CongApp 1" t)
          end
        | Checked T => raise (UnexpectedTranslation "CongApp 2" pt pt' T)
        | TypeError t => raise (TypingError "CongApp 2" t)
        end
      | Checked T => raise (UnexpectedTranslation "CongApp 3" pA pA' T)
      | TypeError t => raise (TypingError "CongApp 3" t)
      end
    | sCongSum B1 B2 pA pB =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      match infer_hnf Σ G Γ pA' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pB axt ;;
        B1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') B1 axt ;;
        B2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') B2 axt ;;
        myret Σ Γ (mkCongSum A1' A2' B1' B2' pA' pB')
      | Checked T => raise (UnexpectedTranslation "CongSum" pA pA' T)
      | TypeError t => raise (TypingError "CongSum" t)
      end
    | sCongPair B1 B2 pA pB pu pv =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      match infer_hnf Σ G Γ pA' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pB axt ;;
        B1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') B1 axt ;;
        B2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') B2 axt ;;
        pu' <- tsl_rec fuel Σ G Γ pu axt ;;
        pv' <- tsl_rec fuel Σ G Γ pv axt ;;
        match infer_hnf Σ G Γ pu' with
        | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; u1' ; _ ; u2' ]) =>
          match infer_hnf Σ G Γ pv' with
          | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; v1' ; _ ; v2' ]) =>
            myret Σ Γ (mkCongPair A1' A2' B1' B2' u1' u2' v1' v2' pA' pB' pu' pv')
          | Checked T => raise (UnexpectedTranslation "CongPair 1" pv pv' T)
          | TypeError t => raise (TypingError "CongPair 1" t)
          end
        | Checked T => raise (UnexpectedTranslation "CongPair 2" pu pu' T)
        | TypeError t => raise (TypingError "CongPair 2" t)
        end
      | Checked T => raise (UnexpectedTranslation "CongPair 3" pA pA' T)
      | TypeError t => raise (TypingError "CongPair 3" t)
      end
    | sCongPi1 B1 B2 pA pB pp =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      match infer_hnf Σ G Γ pA' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pB axt ;;
        B1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') B1 axt ;;
        B2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') B2 axt ;;
        pp' <- tsl_rec fuel Σ G Γ pp axt ;;
        match infer_hnf Σ G Γ pp' with
        | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; p1' ; _ ; p2' ]) =>
          myret Σ Γ (mkCongPi1 A1' A2' B1' B2' p1' p2' pA' pB' pp')
        | Checked T => raise (UnexpectedTranslation "CongPi1 1" pp pp' T)
        | TypeError t => raise (TypingError "CongPi1 1" t)
        end
      | Checked T => raise (UnexpectedTranslation "CongPi1 2" pA pA' T)
      | TypeError t => raise (TypingError "CongPi1 2" t)
      end
    | sCongPi2 B1 B2 pA pB pp =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      match infer_hnf Σ G Γ pA' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; A1' ; _ ; A2' ]) =>
        pB' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' (mkPack A1' A2')) pB axt ;;
        B1' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A1') B1 axt ;;
        B2' <- tsl_rec fuel Σ G (Γ ,, vass nAnon' A2') B2 axt ;;
        pp' <- tsl_rec fuel Σ G Γ pp axt ;;
        match infer_hnf Σ G Γ pp' with
        | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; p1' ; _ ; p2' ]) =>
          myret Σ Γ (mkCongPi2 A1' A2' B1' B2' p1' p2' pA' pB' pp')
        | Checked T => raise (UnexpectedTranslation "CongPi2 1" pp pp' T)
        | TypeError t => raise (TypingError "CongPi2 1" t)
        end
      | Checked T => raise (UnexpectedTranslation "CongPi2 2" pA pA' T)
      | TypeError t => raise (TypingError "CongPi2 2" t)
      end
    | sCongEq pA pu pv =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      pu' <- tsl_rec fuel Σ G Γ pu axt ;;
      pv' <- tsl_rec fuel Σ G Γ pv axt ;;
      match infer_hnf Σ G Γ pu' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ A1' ; u1' ; A2' ; u2' ]) =>
        match infer_hnf Σ G Γ pv' with
        | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; v1' ; _ ; v2' ]) =>
          myret Σ Γ (mkCongEq A1' A2' u1' v1' u2' v2' pA' pu' pv')
        | Checked T => raise (UnexpectedTranslation "CongEq 1" pv pv' T)
        | TypeError t => raise (TypingError "CongEq 1" t)
        end
      | Checked T => raise (UnexpectedTranslation "CongEq 2" pu pu' T)
      | TypeError t => raise (TypingError "CongEq 2" t)
      end
    | sCongRefl pA pu =>
      pA' <- tsl_rec fuel Σ G Γ pA axt ;;
      pu' <- tsl_rec fuel Σ G Γ pu axt ;;
      match infer_hnf Σ G Γ pu' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ A1' ; u1' ; A2' ; u2' ]) =>
        myret Σ Γ (mkCongRefl A1' A2' u1' u2' pA' pu')
      | Checked T => raise (UnexpectedTranslation "CongRefl" pu pu' T)
      | TypeError t => raise (TypingError "CongRefl" t)
      end
    | sEqToHeq p =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Logic"; "Init"; "Coq"], "eq")%core 0) _) [ A' ; u' ; v' ]) =>
        myret Σ Γ (mkEqToHeq A' u' v' p')
      | Checked T => raise (UnexpectedTranslation "EqToHeq" p p' T)
      | TypeError t => raise (TypingError "EqToHeq" t)
      end
    | sHeqTypeEq A B p =>
      A' <- tsl_rec fuel Σ G Γ A axt ;;
      B' <- tsl_rec fuel Σ G Γ B axt ;;
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "heq")%core 0) _) [ _ ; u' ; _ ; v' ]) =>
        myret Σ Γ (mkHeqTypeEq A' u' B' v' p')
      | Checked T => raise (UnexpectedTranslation "HeqTypeEq" p p' T)
      | TypeError t => raise (TypingError "HeqTypeEq" t)
      end
    | sPack A1 A2 =>
      A1' <- tsl_rec fuel Σ G Γ A1 axt ;;
      A2' <- tsl_rec fuel Σ G Γ A2 axt ;;
      ret (mkPack A1' A2')
    | sProjT1 p =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "Pack")%core 0) _) [ A1' ; A2' ]) =>
        myret Σ Γ (mkProjT1 A1' A2' p')
      | Checked T => raise (UnexpectedTranslation "ProjT1" p p' T)
      | TypeError t => raise (TypingError "ProjT1" t)
      end
    | sProjT2 p =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "Pack")%core 0) _) [ A1' ; A2' ]) =>
        myret Σ Γ (mkProjT2 A1' A2' p')
      | Checked T => raise (UnexpectedTranslation "ProjT2" p p' T)
      | TypeError t => raise (TypingError "ProjT2" t)
      end
    | sProjTe p =>
      p' <- tsl_rec fuel Σ G Γ p axt ;;
      match infer_hnf Σ G Γ p' with
      | Checked (tApp (tInd (mkInd (MPfile ["Quotes"; "Translation"], "Pack")%core 0) _) [ A1' ; A2' ]) =>
        myret Σ Γ (mkProjTe A1' A2' p')
      | Checked T => raise (UnexpectedTranslation "ProjTe" p p' T)
      | TypeError t => raise (TypingError "ProjTe" t)
      end
    | sAx id =>
      match assoc_at id axt with
      | Some t => myret Σ Γ t
      | None => raise (TranslationNotFound id)
      end
    end
  end.

(* Delimit Scope i_scope with i. *)

Fixpoint tsl_ctx (fuel : nat) (Σ : global_env) (G : universes_graph)
  (Γ : scontext) (axt : assoc term)
  : tsl_result context :=
  match Γ with
  | [] => ret []
  | a :: Γ =>
    Γ' <- tsl_ctx fuel Σ G Γ axt ;;
    A' <- tsl_rec fuel Σ G Γ' a axt ;;
    ret (Γ' ,, vass nAnon' A')
  end.

End Final.
