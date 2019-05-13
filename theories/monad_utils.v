Require Import List.

Set Universe Polymorphism.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Class MonadExc E (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.


Delimit Scope monad_scope with monad.
 
Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.
 
Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity) : monad_scope.
 
Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
  (at level 100, right associativity) : monad_scope.


Instance option_monad : Monad option :=
  {| ret A a := Some a ;
     bind A B m f :=
       match m with
       | Some a => f a
       | None => None
       end
  |}.

Open Scope monad.

Section MapOpt.
  Context {A} (f : A -> option A).

  Fixpoint mapopt (l : list A) : option (list A) :=
    match l with
    | nil => ret nil
    | x :: xs => x' <- f x ;;
                xs' <- mapopt xs ;;
                ret (x' :: xs')
    end.
End MapOpt.

Section MonadOperations.
  Context {T} {M : Monad T}.
  Context {A B} (f : A -> T B).
  Fixpoint monad_map (l : list A)
    : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- f x ;;
                  l' <- monad_map l ;;
                  ret (x' :: l')
       end.

  Context (g : A -> B -> T A).
  Fixpoint monad_fold_left (l : list B) (x : A) : T A
    := match l with
       | nil => ret x
       | y :: l => x' <- g x y ;;
                   monad_fold_left l x'
       end.

  Context (h : nat -> A -> T B).
  Fixpoint monad_map_i_aux (n0 : nat) (l : list A) : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- (h n0 x) ;;
                   l' <- (monad_map_i_aux (S n0) l) ;;
                   ret (x' :: l')
       end.

  Definition monad_map_i := @monad_map_i_aux 0.
End MonadOperations.


(* Error monad *)
Inductive result E A :=
| Success : A -> result E A
| Error : E -> result E A.

Arguments Success {_ _} _.
Arguments Error {_ _} _.

Instance error_monad E : Monad (result E) :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc E : MonadExc E (result E) :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.
