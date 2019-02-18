# Eliminating Reflection from Type Theory
**A translation from extensional type theory (ETT) to intensional type theory (ITT)**

*Authors:* Théo Winterhalter, Matthieu Sozeau and Nicolas Tabareau

**Quick jump**
- [Installing](#installing)
- [Structure](#structure-of-the-project)

## Overview

This work is a Coq formalisation of a translation from ETT to ITT that can
be interfaced with Coq thanks to the MetaCoq plugin.
Additionally, sorts are handled quite generically (although without cumulativity)
which means in particular that we can have a translation from
Homotopy Type System (HTS) to Two-Level Type Theory (2TT) as a direct application.

ETT differs from ITT by the addition of the **reflection rule**:
```
Γ ⊢ e : u = v
--------------
  Γ ⊢ u ≡ v
```

### Examples (Plugin)

In order to see more clearly what it does, here are a few examples that can be found
in this repository.

#### Identity with a coercion

A toy example of ETT would be to use an equality between types in context to
coerce a term.
```coq
Fail Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := x.
```
This of course fails in Coq / ITT because `A` and `B` are not convertible.
In order to still be able to write our example in Coq we use a notation
reminiscent of Agda `{! _ !}` with an underlying axiom going from any type
to any other. With it we can write:
```coq
Definition pseudoid (A B : Type) (e : A = B) (x : A) : B := {! x !}.
```
Using the power of MetaCoq, we can quote it, translate it using our
translation, and then unquote it to get back a Coq term:
```coq
Run TemplateProgram (Translate ε "pseudoid").
```
which defines
```coq
pseudoidᵗ =
fun (A B : Type) (e : A = B) (x : A) => transport (pseudoid_obligation_0 A B e x) x
     : forall A B : Type, A = B -> A -> B
```
This is what you would expect, and what you would write by hand:
**the use of reflection has been replaced by a transport**.

#### Reversal of vectors

An already more challenging example involves playing around with
inductive types and eliminators (we don't handle fixed points and
pattern-matching).

Consider for this the type of length-indexed lists:
```coq
Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).
```

One more *realistic* example would be the reversal of vectors (using an accumulator):
```coq
Fail Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => rv _ (vcons a m acc))
           n v m acc.
```
Indeed, in ITT, it is not possible to write it directly like this, as we would
do in the non dependent case (lists). This time it has to do with commutativity
of addition: `S n + m` and `n + S m` are not convertible.
We then write the ETT definition below.
```coq
Definition vrev {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  vec_rect A (fun n _ => forall m, vec A m -> vec A (n + m))
           (fun m acc => acc) (fun a n _ rv m acc => {! rv _ (vcons a m acc) !})
           n v m acc.
```
To translate it we must first put its dependencies in the translation context.
```coq
Run TemplateProgram (
      Θ <- TranslateConstant ε "nat" ;;
      Θ <- TranslateConstant Θ "vec" ;;
      Θ <- TranslateConstant Θ "Nat.add" ;;
      Θ <- TranslateConstant Θ "vec_rect" ;;
      Translate Θ "vrev'"
).
```
We then obtain the following translation (after the system solves
automatically 4 equality obligations) with exactly one transport as expected.
```coq
fun (A : Type) (n m : nat) (v : vec A n) (acc : vec A m) =>
vec_rect A
  (fun (n0 : nat) (_ : vec A n0) =>
   forall m0 : nat, vec A m0 -> vec A (n0 + m0))
  (fun (m0 : nat) (acc0 : vec A m0) => acc0)
  (fun (a : A) (n0 : nat) (v0 : vec A n0)
     (rv : forall m0 : nat, vec A m0 -> vec A (n0 + m0))
     (m0 : nat) (acc0 : vec A m0) =>
   transport (vrev_obligation3 A n m v acc a n0 v0 rv m0 acc0)
     (rv (S m0) (vcons a m0 acc0))) n v m acc
     : forall (A : Type) (n m : nat), vec A n -> vec A m -> vec A (n + m)
```

## Installing

### Requirements

This project can be compiled with Coq 8.8.1 and requires
[Equations](http://mattam82.github.io/Coq-Equations/) (version `1.1+8.8`)
and
[MetaCoq](https://github.com/MetaCoq/metacoq/releases/tag/v2.1-beta3).

*Note: If you have trouble installing MetaCoq v2.1-beta3, have a look at [this fix](https://github.com/MetaCoq/metacoq/issues/77#issuecomment-439006141).*

If you want to compile the examples, you also need
[TypingFlags](https://github.com/SimonBoulier/TypingFlags).

### Building

Once you have the dependencies, simply run
```bash
make
```
to build the project (it takes quite some time unfortunately, so you
can use options like `-j4` to speed up a little bit).


## Structure of the project

All of the formalisation can be found in the `theories` directory.

*The file [util.v](theories/util.v)
provides useful lemmata that aren't specific to the formalisation.*

### Syntax

First, [Sorts](theories/Sorts.v) introduces a notion of sort (as a type-class)
stating the basic properties required, and provides different instances
like the natural number hierarchy, type-in-type, or even HTS/2-level TT.
In [SAst](SAst.v) we define the common syntax to both ETT (Extensional type theory)
and ITT (our own version of Itensional type theory with some sugar) in the form of
a simple inductive type `sterm`.
Since terms (`sterm`) are annotated with names—for printing—which are
irrelevant for computation and typing, we define an erasure map `nl : sterm -> nlterm`
in [Equality](theories/Equality.v) from which we derive a decidable equality on `sterm`.
We then define lifting operations, substitution and closedness in [SLiftSubst](SLiftSubst.v).

### Typing

First, in [SCommon](theories/SCommon.v) we define common utility to both ETT and ITT,
namely with the definition of contexts (`scontext`) and global
contexts (`sglobal_context`), the latter containing the declarations of constants.
[Conversion](theories/Conversion.v) is about the untyped conversion used in ITT
(conversion `t ≡ u` is derived from one-step reduction `t ▷ u`) and contains
the **only axiom** of the whole formalisation (stating that conversion
is transitive, this would require us to prove confluence of the
rewriting system, which we deem orthogonal to our proof).
[XTyping](theories/XTyping.v) contains the definition of typing rules of ETT
(`Σ ;;; Γ |-x t : A`), mutually defined with a typed conversion (`Σ ;;; Γ |-x t ≡ u : A`)
and the well-formedness of contexts (`wf Σ Γ`).
[ITyping](theories/ITyping.v) is the same for ITT with the difference that the conversion
isn't mutually defined but instead the one defined in [Conversion](theories/Conversion.v))
and that it also defines a notion of well-formedness of global declarations (`type_glob Σ`).

### Lemmata regarding ITT

In [ITypingInversions](theories/ITypingInversions.v) one can find an inversion lemma for
each constructor of the syntax, together with the tactic `ttinv` to apply the right one.
In [ITypingLemmata](theories/ITypingLemmata.v) are proven a list of different lemmata
regarding ITT, including the fact that whenever we have `Σ ;;; Γ |-i t : A` then `A` is
well sorted and that lifting and substitution preserve typing.
Context conversion and the associated typing preservation lemma are found in
[ContextConversion](theories/ContextConversion.v).
A uniqueness of typing lemma (if `Σ ;;; Γ |-i t :A` and `Σ ;;; Γ |-i t :B` then `A ≡ B`) is proven in
[Uniqueness](theories/Uniqueness.v).
Subject reduction and the corollary that we call subject conversion (whenever two terms are convertible
and well-typed, their types are also convertible) are proven in
[SubjectReduction](theories/SubjectReduction.v).
[ITypingAdmissible](theories/ITypingAdmissible.v) states admissible rules in ITT.

### Translation

[PackLifts](PackLifts.v) defines the lifting operations related to packing. Packing consists
in taking two types `A1` and `A2` and yielding the following record type (where `x ≅ y`
stands for heterogenous equality between `x` and `y`).
```coq
Record Pack A1 A2 := pack {
  ProjT1 : A1 ;
  ProjT2 : A2 ;
  ProjTe : ProjT1 ≅ ProjT2
}.
```
In order to produce terms as small / efficient as possible, we provide
*optimised* versions of some constructors, for instance, transport
between two convertible terms is remapped to identity. Thanks to this, terms that live in ITT should be
translated to themselves syntactically (and not just up to transport).
This is done in [Optim](theories/Optim.v), relying on a (semi-)decision procedure for
conversion in ITT defined in [DecideConversion.v](theories/DecideConversion.v).
[FundamentalLemma](theories/FundamentalLemma.v)
contains the proof of the fundamental lemma, crucial step for our translation.
[Translation](theories/Translation.v)
contains the translation from ETT to ITT.

### Meta Theory of ETT

In order to write ETT derivations more effectively, we develop some of the meta-theory of ETT.
[XInversions](theories/XInversions.v) provides inversion lemmata for ETT while
[XTypingLemmata](theories/XTypingLemmata.v) provides lift and substitution lemmata, along with
the proof that the type in a judgement is well sorted.

### Checking

For type checking, we write one tactic for ITT and one for ETT.
Their respective definitions can be found in
[IChecking](theories/IChecking.v) and [XChecking](theories/XChecking.v).

### MetaCoq and Plugin

To realise the sugar of ITT, we define some constants in [Quotes](theories/Quotes.v)
and then quote them to MetaCoq's inner representation of terms.
The translation from ITT to MetaCoq is done in [FinalTranslation](theories/FinalTranslation.v).
[FullQuote](theories/FullQuote.v)
is for the opposite: generating an ITT term from a MetaCoq (and
thus Coq) term, it is useful to generate examples.

Finally [plugin](theories/plugin.v) defines a plugin using the
TemplateMonad.
It relies on type checkers written in
[plugin_checkers](theories/checker.v)
and some extra utility in [plugin_util](theories/util.v).

**To see the plugin in action, just have a look at [plugin_demo](theories/plugin_demo.v)!**
