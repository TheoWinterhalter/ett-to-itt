(*! Common syntax to ITT and ETT *)

From MetaCoq Require Import Ast.
From Translation Require Import util Sorts.

Section Ast.

Context `{Sorts.notion}.

Inductive sterm : Type :=
| sRel (n : nat)
| sSort (s : sort)
| sProd (nx : name) (A B : sterm)
| sLambda (nx : name) (A B t : sterm)
| sApp (u A B v : sterm)
(* Σ-types *)
| sSum (nx : name) (A B : sterm)
| sPair (A B u v : sterm)
| sPi1 (A B p : sterm)
| sPi2 (A B p : sterm)
(* Homogenous equality *)
| sEq (A u v : sterm)
| sRefl (A u : sterm)
| sJ (A u P w v p : sterm)
| sTransport (T1 T2 p t : sterm)
(* Heterogenous equality *)
| sHeq (A a B b : sterm)
| sHeqToEq (p : sterm)
| sHeqRefl (A a : sterm)
| sHeqSym (p : sterm)
| sHeqTrans (p q : sterm)
| sHeqTransport (p t : sterm)
| sCongProd (B1 B2 pA pB : sterm)
| sCongLambda (B1 B2 t1 t2 pA pB pt : sterm)
| sCongApp (B1 B2 pu pA pB pv : sterm)
| sCongSum (B1 B2 pA pB : sterm)
| sCongPair (B1 B2 pA pB pu pv : sterm)
| sCongPi1 (B1 B2 pA pB pp : sterm)
| sCongPi2 (B1 B2 pA pB pp : sterm)
| sCongEq (pA pu pv : sterm)
| sCongRefl (pA pu : sterm)
| sEqToHeq (p : sterm)
| sHeqTypeEq (A B p : sterm)
(* Packing *)
| sPack (A1 A2 : sterm)
| sProjT1 (p : sterm)
| sProjT2 (p : sterm)
| sProjTe (p : sterm)
(* External axioms *)
| sAx (id : ident)
.

End Ast.