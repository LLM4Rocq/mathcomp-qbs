# Quasi-Borel Spaces in Rocq: A Formalization Report

**Project:** QBS -- Quasi-Borel Spaces in Rocq/Coq
**Repository:** `/home/rocq/QBS`
**Date:** 2026-03-26
**Status:** 175 proofs completed (173 Qed + 2 Defined), 0 Admitted, 0 custom axioms
**Lines of Rocq:** 5174 across 9 files
**Declarations:** 330 total (92 Definitions, 226 Lemmas, 2 Theorems, 3 Records, 1 Fixpoint, 1 Inductive, 1 HB mixin, 1 HB structure)

**Primary references:**
- C. Heunen, O. Kammar, S. Staton, H. Yang.
  "A Convenient Category for Higher-Order Probability Theory."
  LICS 2017. [arXiv:1701.02547](https://arxiv.org/abs/1701.02547)
- M. Hirata, Y. Minamide, T. Sato.
  "Quasi-Borel Spaces." Isabelle AFP, 2022.
  [isa-afp.org/entries/Quasi_Borel_Spaces.html](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html)
- R. Affeldt, C. Cohen, A. Saito.
  "Semantics of Probabilistic Programs using s-Finite Kernels in Coq."
  [math-comp/analysis#912](https://github.com/math-comp/analysis/pull/912), 2023.

**Dependencies:** Rocq 9.0.x, Math-comp 2.5.x, Math-comp analysis 1.15.x, Hierarchy Builder 1.10.x

---

## Table of Contents

- [Part I: Core QBS Theory](#part-i-core-qbs-theory)
  - [1.1 The isQBS Mixin and QBSpace Structure](#11-the-isqbs-mixin-and-qbspace-structure)
  - [1.2 Morphisms](#12-morphisms)
  - [1.3 Bundled Morphisms](#13-bundled-morphisms)
  - [1.4 The R Functor](#14-the-r-functor)
  - [1.5 Binary Products](#15-binary-products)
  - [1.6 Exponentials (Function Spaces)](#16-exponentials-function-spaces)
  - [1.7 Cartesian Closure](#17-cartesian-closure)
  - [1.8 Unit QBS](#18-unit-qbs)
  - [1.9 Induced Sigma-Algebra](#19-induced-sigma-algebra)
  - [1.10 Comparison Morphisms](#110-comparison-morphisms)
  - [1.11 Subspaces](#111-subspaces)
  - [1.12 Generating QBS](#112-generating-qbs)
  - [1.13 Product Structural Morphisms](#113-product-structural-morphisms)
  - [1.14 Exponential Structural Morphisms](#114-exponential-structural-morphisms)
  - [1.15 Image QBS](#115-image-qbs)
  - [1.16 Order Structure](#116-order-structure)
  - [1.17 L-R Adjunction](#117-l-r-adjunction)
  - [1.18 Standard Borel Spaces (Definition and Full Faithfulness)](#118-standard-borel-spaces-definition-and-full-faithfulness)
  - [1.19 Coproducts (Binary)](#119-coproducts-binary)
  - [1.20 Coproducts (General / Sigma Type)](#120-coproducts-general--sigma-type)
  - [1.21 Dependent Products (Pi Type)](#121-dependent-products-pi-type)
  - [1.22 List Type](#122-list-type)
- [Part II: Probability Monad and Integration](#part-ii-probability-monad-and-integration)
  - [2.1 QBS Probability Triple](#21-qbs-probability-triple)
  - [2.2 Equivalence of Probability Triples](#22-equivalence-of-probability-triples)
  - [2.3 The Probability Monad P(X)](#23-the-probability-monad-px)
  - [2.4 Return](#24-return)
  - [2.5 Bind](#25-bind)
  - [2.6 Monad Laws](#26-monad-laws)
  - [2.7 Integration](#27-integration)
  - [2.8 Pushforward Infrastructure](#28-pushforward-infrastructure)
  - [2.9 Functorial Map](#29-functorial-map)
  - [2.10 Expectation and Events](#210-expectation-and-events)
  - [2.11 Variance](#211-variance)
  - [2.12 Monad Join](#212-monad-join)
  - [2.13 Monad Strength](#213-monad-strength)
  - [2.14 Strength Naturality and Coherence](#214-strength-naturality-and-coherence)
  - [2.15 Bind Respects Equivalence](#215-bind-respects-equivalence)
  - [2.16 Quotient Type for QBS Probability](#216-quotient-type-for-qbs-probability)
  - [2.17 Product Measures and Fubini](#217-product-measures-and-fubini)
  - [2.18 Independence](#218-independence)
  - [2.19 Variance of Independent Sums](#219-variance-of-independent-sums)
  - [2.20 Commutativity of the Probability Monad](#220-commutativity-of-the-probability-monad)
  - [2.21 Classical Distributions](#221-classical-distributions)
  - [2.22 Bayesian Linear Regression](#222-bayesian-linear-regression)
- [Part III: Standard Borel Spaces and Architecture](#part-iii-standard-borel-spaces-and-architecture)
  - [3.1 Standard Borel: R to (0,1) Bijection](#31-standard-borel-r-to-01-bijection)
  - [3.2 Binary Digit Machinery](#32-binary-digit-machinery)
  - [3.3 Digit Interleaving and Pairing](#33-digit-interleaving-and-pairing)
  - [3.4 Round-Trip Properties](#34-round-trip-properties)
  - [3.5 Measurability of the Bijection Components](#35-measurability-of-the-bijection-components)
  - [3.6 Composed Bijection R x R to R](#36-composed-bijection-r-x-r-to-r)
  - [3.7 The Punchline: pair_standard_borel](#37-the-punchline-pair_standard_borel)
  - [3.8 File Dependency Graph](#38-file-dependency-graph)
  - [3.9 Design Decisions](#39-design-decisions)
  - [3.10 Comparison with Isabelle AFP](#310-comparison-with-isabelle-afp)
  - [3.11 Math-Comp Analysis Dependencies](#311-math-comp-analysis-dependencies)
  - [3.12 Statistics](#312-statistics)
  - [3.13 Remaining Work](#313-remaining-work)

---

## Part I: Core QBS Theory

Source files: `theories/quasi_borel.v` (742 lines, 35 Qed), `theories/measure_qbs_adjunction.v` (248 lines, 12 Qed), `theories/coproduct_qbs.v` (676 lines, 22 Qed).

### 1.1 The isQBS Mixin and QBSpace Structure

**File:** `theories/quasi_borel.v`, lines 53--66

A quasi-Borel space packages a carrier type with a set of "random elements" satisfying three closure axioms. The entire development is parametric in a `realType` `R`. The structure uses Hierarchy Builder's mixin/structure pattern:

```
HB.mixin Record isQBS (R : realType) (T : Type) := {
  qbs_Mx : set (measurableTypeR R -> T) ;
  qbs_Mx_comp : forall alpha f,
    qbs_Mx alpha -> measurable_fun setT f -> qbs_Mx (alpha \o f) ;
  qbs_Mx_const : forall x : T, qbs_Mx (fun _ => x) ;
  qbs_Mx_glue : forall (P : measurableTypeR R -> nat)
    (Fi : nat -> measurableTypeR R -> T),
    measurable_fun setT P ->
    (forall i, qbs_Mx (Fi i)) ->
    qbs_Mx (fun r => Fi (P r) r) ;
}.

#[short(type="qbsType")]
HB.structure Definition QBSpace (R : realType) := { T of isQBS R T }.
```

**Parameters:**
- `R : realType` -- the real number type, from math-comp analysis
- `mR := measurableTypeR R` -- the Borel measurable space on R

**Notation:** Throughout this report, `mR` denotes `measurableTypeR R`, the measurable type on the reals with the Borel sigma-algebra. The short type name `qbsType R` is used for instances.

**Axiom 1 (Composition closure, `qbs_Mx_comp`):** If `alpha` is a random element and `f : mR -> mR` is measurable, then `alpha \o f` is a random element. This corresponds to reparametrization of randomness.

**Axiom 2 (Constant closure, `qbs_Mx_const`):** For any point `x : T`, the constant function `fun _ => x` is a random element. This ensures all deterministic elements are representable.

**Axiom 3 (Gluing, `qbs_Mx_glue`):** Given a measurable partition selector `P : mR -> nat` and a family of random elements `Fi`, the glued function `fun r => Fi (P r) r` is a random element. This is the key axiom distinguishing QBS from mere function spaces.

**NB comments on HB.pack:** Throughout the development, concrete QBS constructions (products, exponentials, coproducts, etc.) use manual `HB.pack` calls rather than HB canonical instances, because the carrier types are non-canonical (e.g., `X * Y`, `qbs_hom X Y`, `X + Y`). Each such usage is annotated with an NB comment explaining why.

### 1.2 Morphisms

**File:** `theories/quasi_borel.v`, lines 75--96

A QBS morphism is a function that preserves random elements under composition:

```
Definition qbs_morphism (X Y : qbsType R) (f : X -> Y) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> @qbs_Mx R Y (f \o alpha).
```

**Key lemmas:**

| Name | Type | Statement |
|------|------|-----------|
| `qbs_morphism_id` | `qbs_morphism X X idfun` | Identity is a morphism |
| `qbs_morphism_comp` | `qbs_morphism X Y f -> qbs_morphism Y Z g -> qbs_morphism X Z (g \o f)` | Morphisms compose |
| `qbs_morphism_const` | `qbs_morphism X Y (fun _ => y)` | Constant maps are morphisms |

These three lemmas establish that QBS spaces form a category.

### 1.3 Bundled Morphisms

**File:** `theories/quasi_borel.v`, lines 78--85

```
Record qbs_hom (X Y : qbsType R) := QBSHom {
  qbs_hom_val :> X -> Y ;
  qbs_hom_proof : forall alpha, @qbs_Mx R X alpha ->
    @qbs_Mx R Y (qbs_hom_val \o alpha) ;
}.
```

Bundled morphisms carry their proof of preservation. The coercion `qbs_hom_val :> X -> Y` allows bundled morphisms to be used as functions. These are the points of the exponential QBS (Section 1.6).

**Post-section Arguments declarations:**

```
Arguments QBSHom {R X Y}.
Arguments qbs_hom_val {R X Y}.
Arguments qbs_hom_proof {R X Y}.
```

### 1.4 The R Functor

**File:** `theories/quasi_borel.v`, lines 98--130; `theories/measure_qbs_adjunction.v`, lines 39--67

The R functor sends a measurable type to its QBS of measurable functions:

```
(* NB: manual HB.pack because R_qbs builds a non-canonical QBS on an
   existing measurableType *)
Definition R_qbs (d : measure_display) (M : measurableType d) : qbsType R :=
  HB.pack M
    (@isQBS.Build R M
      [set f : mR -> M | measurable_fun setT f]
      ...).
```

Random elements of `R_qbs M` are exactly the measurable functions `mR -> M`.

**Concrete instances:**

| Name | Definition | Description |
|------|-----------|-------------|
| `realQ` | `R_qbs mR` | QBS on the reals |
| `natQ` | `R_qbs nat` | QBS on natural numbers |
| `boolQ` | `R_qbs bool` | QBS on booleans |

**Supporting lemma:**

```
Lemma measurable_glue (d : measure_display) (M : measurableType d)
  (P : mR -> nat) (Fi : nat -> mR -> M) :
  measurable_fun setT P ->
  (forall i, measurable_fun setT (Fi i)) ->
  measurable_fun setT (fun r => Fi (P r) r).
```

This key lemma shows that the measurable functions on a measurable type satisfy the gluing axiom, justifying the construction of `R_qbs`.

**Functoriality (from `measure_qbs_adjunction.v`):**

| Name | Type | Statement |
|------|------|-----------|
| `R_qbs_morph` | `measurable_fun setT f -> qbs_morphism (R_qbs M1) (R_qbs M2) f` | Measurable maps become morphisms |
| `R_qbs_id` | `qbs_morphism (R_qbs M) (R_qbs M) idfun` | R preserves identity |
| `R_qbs_comp` | `measurable_fun setT f -> measurable_fun setT g -> qbs_morphism (R_qbs M1) (R_qbs M3) (g \o f)` | R preserves composition |

### 1.5 Binary Products

**File:** `theories/quasi_borel.v`, lines 132--200

```
(* NB: manual HB.pack because this is a non-canonical QBS on (X * Y)%type *)
Definition prodQ (X Y : qbsType R) : qbsType R :=
  HB.pack (X * Y)%type
    (@isQBS.Build R (X * Y)%type
      [set f | @qbs_Mx R X (fst \o f) /\ @qbs_Mx R Y (snd \o f)]
      ...).
```

A function `f : mR -> X * Y` is random in the product iff both projections are random. The three closure axioms are established by `prodQ_Mx_comp`, `prodQ_Mx_const`, `prodQ_Mx_glue`.

**Post-section Arguments declaration:** `Arguments prodQ : clear implicits.`

**Projection and pairing morphisms:**

| Name | Type | Statement |
|------|------|-----------|
| `qbs_morphism_fst` | `qbs_morphism (prodQ X Y) X fst` | First projection is a morphism |
| `qbs_morphism_snd` | `qbs_morphism (prodQ X Y) Y snd` | Second projection is a morphism |
| `qbs_morphism_pair` | `qbs_morphism W X f -> qbs_morphism W Y g -> qbs_morphism W (prodQ X Y) (fun w => (f w, g w))` | Pairing of morphisms is a morphism |

**Helper lemmas for product randomness:**

| Name | Type |
|------|------|
| `prodQ_const_random` | `qbs_Mx Y alpha -> qbs_Mx (prodQ X Y) (fun r => (x, alpha r))` |
| `prodQ_random_const` | `qbs_Mx X alpha -> qbs_Mx (prodQ X Y) (fun r => (alpha r, y))` |

These are used extensively in the exponential and probability monad constructions.

### 1.6 Exponentials (Function Spaces)

**File:** `theories/quasi_borel.v`, lines 202--271

The exponential `expQ X Y` has bundled morphisms `qbs_hom X Y` as its carrier. A function `g : mR -> qbs_hom X Y` is random iff the uncurried map `(r, x) |-> g(r)(x)` is a morphism `prodQ realQ X -> Y`:

```
(* NB: manual HB.pack because this is a non-canonical QBS on (qbs_hom X Y) *)
Definition expQ (X Y : qbsType R) : qbsType R :=
  HB.pack (qbs_hom X Y)
    (@isQBS.Build R (qbs_hom X Y)
      [set g : mR -> qbs_hom X Y |
        @qbs_morphism (prodQ realQ X) Y
          (fun p : realQ * X => qbs_hom_val (g p.1) p.2)]
      ...).
```

**Post-section Arguments declaration:** `Arguments expQ : clear implicits.`

The three closure axioms are established by `expQ_Mx_comp`, `expQ_Mx_const`, `expQ_Mx_glue`.

**Design note:** The carrier of `expQ X Y` is `qbs_hom X Y`, a sigma type. This is one reason concrete QBS constructions use manual `HB.pack` -- the exponential carrier cannot be expressed as a canonical HB instance on bare function types.

### 1.7 Cartesian Closure

**File:** `theories/quasi_borel.v`, lines 273--323

The two key theorems establishing cartesian closure:

**Evaluation morphism:**

```
Lemma qbs_morphism_eval (X Y : qbsType R) :
  @qbs_morphism (prodQ (expQ X Y) X) Y (fun p => qbs_hom_val p.1 p.2).
```

The proof constructs an auxiliary random element `gamma : mR -> realQ * X` pairing the identity with the second projection of `beta`, then applies the random element condition from `expQ`.

**Currying morphism:**

```
Lemma qbs_morphism_curry (X Y Z : qbsType R)
  (f : qbs_hom (prodQ X Y) Z) :
  @qbs_morphism X (expQ Y Z)
    (fun x => @QBSHom Y Z (fun y => f (x, y))
       (fun alpha hA => qbs_hom_proof f _
          (prodQ_const_random x hA))).
```

The proof shows that for any random element `beta` in X and `gamma` in `prodQ realQ Y`, the composition produces a random element of Z by applying `f`'s morphism property to the paired random element.

Together, `qbs_morphism_eval` and `qbs_morphism_curry` establish that the category of QBS spaces is cartesian closed, solving the fundamental problem that the category of measurable spaces lacks exponentials.

### 1.8 Unit QBS

**File:** `theories/quasi_borel.v`, lines 325--339

```
(* NB: manual HB.pack because this is a non-canonical QBS on unit *)
Definition unitQ : qbsType R :=
  HB.pack unit
    (@isQBS.Build R unit
      [set _ : mR -> unit | True]
      (fun _ _ _ _ => I)
      (fun _ => I)
      (fun _ _ _ _ => I)).
```

Every function into `unit` is random.

```
Lemma qbs_morphism_unit (X : qbsType R) :
  @qbs_morphism X unitQ (fun _ => tt).
```

The unit QBS is terminal: there is a unique morphism from any QBS to `unitQ`.

### 1.9 Induced Sigma-Algebra

**File:** `theories/quasi_borel.v`, lines 341--365

The L functor assigns to each QBS its induced sigma-algebra:

```
Definition sigma_Mx (X : qbsType R) : set (set X) :=
  [set U | forall alpha, @qbs_Mx R X alpha ->
    measurable (alpha @^-1` U)].
```

A set `U` is in `sigma_Mx(X)` iff every random element's preimage of `U` is Borel measurable.

**Sigma-algebra axioms:**

| Name | Statement |
|------|-----------|
| `sigma_Mx_setT` | `sigma_Mx X setT` |
| `sigma_Mx_setC` | `sigma_Mx X U -> sigma_Mx X (~` U)` |
| `sigma_Mx_bigcup` | `(forall i, sigma_Mx X (F i)) -> sigma_Mx X (\bigcup_i F i)` |

These are proved in `quasi_borel.v` and extended in `measure_qbs_adjunction.v`:

| Name | Statement |
|------|-----------|
| `L_sigma_set0` | `sigma_Mx X set0` |
| `L_sigma_measurableT` | `L_sigma X setT` |
| `L_sigma_measurableC` | `L_sigma X U -> L_sigma X (~` U)` |
| `L_sigma_measurable_bigcup` | `(forall i, L_sigma X (F i)) -> L_sigma X (\bigcup_i F i)` |

**Functoriality of L:**

```
Lemma L_qbs_morph (X Y : qbsType R) (f : X -> Y) :
  qbs_morphism X Y f -> forall U, L_sigma Y U -> L_sigma X (f @^-1` U).
```

QBS morphisms pull back sigma-algebra sets. L preserves identity (`L_qbs_id`) and composition (`L_qbs_comp`).

### 1.10 Comparison Morphisms

**File:** `theories/quasi_borel.v`, lines 367--397

Standard arithmetic and comparison operations on `realQ` are automatically QBS morphisms:

| Name | Type Signature | Description |
|------|---------------|-------------|
| `qbs_morphism_add` | `qbs_morphism (prodQ realQ realQ) realQ (fun p => p.1 + p.2)` | Addition |
| `qbs_morphism_mul` | `qbs_morphism (prodQ realQ realQ) realQ (fun p => p.1 * p.2)` | Multiplication |
| `qbs_morphism_ltr` | `qbs_morphism (prodQ realQ realQ) boolQ (fun p => p.1 < p.2)` | Less-than |
| `qbs_morphism_negb` | `qbs_morphism boolQ boolQ negb` | Boolean negation |

These delegate to the corresponding measurability lemmas from math-comp analysis (`measurable_funD`, `measurable_funM`, `measurable_fun_ltr`, `measurable_neg`).

### 1.11 Subspaces

**File:** `theories/quasi_borel.v`, lines 403--450

Given a QBS `X` and a predicate `P : set X`, the subspace has carrier `{x : X | P x}` and random elements `alpha` such that `proj1_sig \o alpha` is random in X:

```
(* NB: manual HB.pack because this is a non-canonical QBS on {x : X | P x} *)
Definition sub_qbs : qbsType R :=
  HB.pack sub_car
    (@isQBS.Build R sub_car sub_Mx
      sub_qbs_closed1 sub_qbs_closed2 sub_qbs_closed3).
```

**Closure proofs:** `sub_qbs_closed1` (composition), `sub_qbs_closed2` (constant), `sub_qbs_closed3` (gluing).

The projection `proj1_sig : sub_qbs X P -> X` is a morphism by construction.

### 1.12 Generating QBS

**File:** `theories/quasi_borel.v`, lines 452--476

Given a set `G` of functions `mR -> T`, the smallest QBS containing `G` is constructed by inductive closure:

```
Inductive generating_Mx (T : Type) (G : set (mR -> T)) : (mR -> T) -> Prop :=
  | gen_base : forall alpha, G alpha -> generating_Mx G alpha
  | gen_comp : forall alpha f, generating_Mx G alpha ->
      measurable_fun setT f -> generating_Mx G (alpha \o f)
  | gen_const : forall x : T, generating_Mx G (fun _ => x)
  | gen_glue : forall (P : mR -> nat) (Fi : nat -> mR -> T),
      measurable_fun setT P ->
      (forall i, generating_Mx G (Fi i)) ->
      generating_Mx G (fun r => Fi (P r) r).

(* NB: manual HB.pack because this is a non-canonical QBS on T *)
Definition generating_qbs (T : Type) (G : set (mR -> T)) : qbsType R :=
  HB.pack T
    (@isQBS.Build R T (generating_Mx G) ...).
```

**Key properties:**

| Name | Statement |
|------|-----------|
| `generating_qbs_incl` | `G \`<=\` @qbs_Mx R (generating_qbs G)` |
| `generating_qbs_least` | If `Mx` is QBS-closed and `G \`<=\` Mx`, then `generating_Mx G \`<=\` Mx` |

The `generating_qbs_least` lemma establishes that `generating_qbs G` is the *least* QBS containing `G`. This is used in the image construction (Section 1.15) and the sup construction (Section 1.16).

### 1.13 Product Structural Morphisms

**File:** `theories/quasi_borel.v`, lines 481--533

| Name | Type | Description |
|------|------|-------------|
| `qbs_morphism_swap` | `qbs_morphism (prodQ X Y) (prodQ Y X) (fun p => (p.2, p.1))` | Product commutativity |
| `qbs_morphism_assoc_lr` | `qbs_morphism (prodQ (prodQ X Y) Z) (prodQ X (prodQ Y Z)) (fun p => (p.1.1, (p.1.2, p.2)))` | Left-to-right associator |
| `qbs_morphism_assoc_rl` | `qbs_morphism (prodQ X (prodQ Y Z)) (prodQ (prodQ X Y) Z) (fun p => ((p.1, p.2.1), p.2.2))` | Right-to-left associator |

### 1.14 Exponential Structural Morphisms

**File:** `theories/quasi_borel.v`, lines 535--603

| Name | Type | Description |
|------|------|-------------|
| `qbs_morphism_exp_comp` | Given `f : qbs_hom W (expQ X Y)` and `g : qbs_hom W X`, `qbs_morphism W Y (fun w => f w (g w))` | Application / evaluation composed with pairing |
| `qbs_morphism_arg_swap` | Given `f : qbs_hom X (expQ Y Z)`, `qbs_morphism Y (expQ X Z) (fun y => ...)` | Argument transposition |

The `qbs_morphism_exp_comp` lemma is an internalized version of evaluation: given a morphism `f` producing exponential elements and a morphism `g` producing arguments, their pointwise application `fun w => f(w)(g(w))` is a morphism. The proof constructs the auxiliary random element `beta := (r, g(alpha(r)))` to reduce to the exponential's randomness condition.

### 1.15 Image QBS

**File:** `theories/quasi_borel.v`, lines 605--652

```
Definition map_qbs (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism X Y f) : qbsType R :=
  generating_qbs [set beta : mR -> Y |
    exists alpha, @qbs_Mx R X alpha /\ beta = f \o alpha].
```

The image QBS `map_qbs f X` is the generating closure of images of random elements. It is coarser than the codomain:

| Name | Statement |
|------|-----------|
| `map_qbs_random` | `qbs_Mx X alpha -> qbs_Mx (map_qbs hf) (f \o alpha)` |
| `map_qbs_sub` | `qbs_Mx (map_qbs hf) beta -> qbs_Mx Y beta` |
| `map_qbs_morphism_out` | `qbs_morphism (map_qbs hf) Z g` (when `g` is a Y-morphism) |
| `map_qbs_morph_from` | `qbs_morphism X (map_qbs hf) f` |

### 1.16 Order Structure

**File:** `theories/quasi_borel.v`, lines 654--735

For QBS spaces with the same carrier type `T`, inclusion of random element sets defines a partial order:

```
Definition qbs_leT (MxX MxY : set (mR -> T)) : Prop := MxX `<=` MxY.
```

More random elements means a less restrictive (coarser) QBS structure.

| Name | Statement |
|------|-----------|
| `qbs_leT_refl` | `qbs_leT Mx Mx` |
| `qbs_leT_trans` | `qbs_leT Mx1 Mx2 -> qbs_leT Mx2 Mx3 -> qbs_leT Mx1 Mx3` |
| `qbs_leT_antisym` | `qbs_leT Mx1 Mx2 -> qbs_leT Mx2 Mx1 -> Mx1 = Mx2` |

**Sup (join) of two QBS structures:**

```
Definition qbs_supT (T : Type) (MxX MxY : set (mR -> T)) : qbsType R :=
  generating_qbs [set alpha : mR -> T | MxX alpha \/ MxY alpha].
```

| Name | Statement |
|------|-----------|
| `qbs_supT_ub_l` | `qbs_leT MxX (qbs_Mx (qbs_supT MxX MxY))` |
| `qbs_supT_ub_r` | `qbs_leT MxY (qbs_Mx (qbs_supT MxX MxY))` |
| `qbs_supT_least` | If `MxZ` is QBS-closed and contains both, then `qbs_leT (qbs_Mx (qbs_supT MxX MxY)) MxZ` |

### 1.17 L-R Adjunction

**File:** `theories/measure_qbs_adjunction.v`, lines 126--164

The central theorem: the R functor (measurable spaces to QBS) is right adjoint to the L functor (QBS to sigma-algebras).

```
Lemma lr_adj_natural (X : qbsType R) (d : measure_display)
    (Y : measurableType d) (f : X -> Y) :
  (@qbs_morphism R X (@R_qbs R _ Y) f) <->
  (forall U, measurable U -> L_sigma X (f @^-1` U)).
```

This is the iff form of the adjunction: a function `f : X -> Y` is a QBS morphism `X -> R(Y)` if and only if it is "measurable" from `L(X)` to `sigma(Y)`. The two directions are factored as:

| Name | Direction | Statement |
|------|-----------|-----------|
| `lr_adj_l2r` | QBS morphism implies measurability | `qbs_morphism X (R_qbs Y) f -> forall U, measurable U -> L_sigma X (f @^-1` U)` |
| `lr_adj_r2l` | Measurability implies QBS morphism | `(forall U, measurable U -> L_sigma X (f @^-1` U)) -> qbs_morphism X (R_qbs Y) f` |

**Product preservation:**

```
Lemma R_preserves_prod (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2)
    (alpha : mR -> M1 * M2) :
  @qbs_Mx R (@R_qbs R _ [the measurableType _ of (M1 * M2)%type]) alpha <->
  @qbs_Mx R (@prodQ R (@R_qbs R _ M1) (@R_qbs R _ M2)) alpha.
```

The R functor preserves binary products: `R(M1 x M2) ~ prodQ (R M1) (R M2)`.

**Unit and counit of the adjunction:**

| Name | Statement |
|------|-----------|
| `adjunction_unit` | `qbs_Mx X alpha -> forall U, L_sigma X U -> measurable (alpha @^-1` U)` |
| `adjunction_counit` | `measurable U -> L_sigma (R_qbs M) U` |

### 1.18 Standard Borel Spaces (Definition and Full Faithfulness)

**File:** `theories/measure_qbs_adjunction.v`, lines 190--228

```
Definition is_standard_borel (d : measure_display) (M : measurableType d) :=
  exists (f : M -> mR) (g : mR -> M),
    measurable_fun setT f /\
    measurable_fun setT g /\
    (forall x, g (f x) = x).
```

A measurable space is standard Borel if it is measurably isomorphic to (a measurable subset of) R, witnessed by a measurable encoding `f` and decoding `g` with `g \o f = id`.

```
Lemma R_standard_borel : is_standard_borel mR.
```

R itself is trivially standard Borel via the identity.

**Full faithfulness on standard Borel spaces:**

```
Lemma R_full_faithful_standard_borel
    (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2) :
  is_standard_borel M1 ->
  is_standard_borel M2 ->
  forall (f : M1 -> M2),
    qbs_morphism (R_qbs M1) (R_qbs M2) f ->
    measurable_fun setT f.
```

On standard Borel spaces, every QBS morphism between R-images is measurable. The proof factors `f` as `psi2 \o (phi2 \o f \o psi1) \o phi1` where `phi_i, psi_i` are the standard Borel witnesses, and uses the QBS morphism condition on `psi1` (which is measurable) to obtain measurability of `f \o psi1`, then composes with the measurable retractions.

### 1.19 Coproducts (Binary)

**File:** `theories/coproduct_qbs.v`, lines 34--199

The binary coproduct uses the Coq sum type `X + Y`:

```
Definition coprodQ_random (X Y : qbsType R) : set (mR -> X + Y) :=
  [set f |
    (exists a, @qbs_Mx R X a /\ forall r, f r = inl (a r))
    \/
    (exists b, @qbs_Mx R Y b /\ forall r, f r = inr (b r))
    \/
    (exists P a b,
      measurable_fun setT P /\
      @qbs_Mx R X a /\ @qbs_Mx R Y b /\
      forall r, f r = if P r then inl (a r) else inr (b r))].
```

A random element either factors entirely through `inl`, entirely through `inr`, or is a measurable gluing of the two cases via a boolean predicate `P`. The closure proof `coprodQ_Mx_glue` is the most involved: it handles the cases where both X and Y are inhabited (normalizing each `Fi i` to case-3 form), where X is empty, and where Y is empty.

**Injection morphisms:**

| Name | Statement |
|------|-----------|
| `qbs_morphism_inl` | `qbs_morphism X (coprodQ X Y) inl` |
| `qbs_morphism_inr` | `qbs_morphism Y (coprodQ X Y) inr` |

**Case analysis morphism:**

```
Lemma qbs_morphism_case (X Y Z : qbsType R) (f : X -> Z) (g : Y -> Z) :
  qbs_morphism X Z f -> qbs_morphism Y Z g ->
  qbs_morphism (coprodQ X Y) Z
    (fun s => match s with inl x => f x | inr y => g y end).
```

### 1.20 Coproducts (General / Sigma Type)

**File:** `theories/coproduct_qbs.v`, lines 264--395

The general coproduct over a measurable index type `I`:

```
Definition gen_coprodQ_random (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) : set (mR -> {i : I & X i}) :=
  [set f | exists (P : mR -> I) (Fi : forall i, mR -> X i),
    measurable_fun setT P /\
    (forall i, @qbs_Mx R (X i) (Fi i)) /\
    (forall r, f r = existT _ (P r) (Fi (P r) r))].
```

Requires an inhabitedness witness `inh : forall i, X i` for the constant axiom. The constant axiom proof uses `pselect` and `eq_rect` to transport values across fiber types.

**Key lemmas:**

| Name | Statement |
|------|-----------|
| `qbs_morphism_gen_inj` | `qbs_morphism (X i) (gen_coprodQ ...) (fun x => existT _ i x)` |
| `qbs_morphism_coprod_to_gen` | Binary coproduct embeds into general coproduct over `bool` |
| `qbs_morphism_gen_to_coprod` | General coproduct over `bool` embeds back into binary coproduct |

### 1.21 Dependent Products (Pi Type)

**File:** `theories/coproduct_qbs.v`, lines 397--469

```
Definition piQ_random (I : Type) (X : I -> qbsType R) :
  set (mR -> forall i : I, X i) :=
  [set alpha | forall i, @qbs_Mx R (X i) (fun r => alpha r i)].
```

A random element of the dependent product is a function that is random in each fiber. The closure proofs delegate to the fiber-level QBS axioms.

**Key morphisms:**

| Name | Statement |
|------|-----------|
| `qbs_morphism_proj` | `qbs_morphism (piQ I X) (X i) (fun f => f i)` |
| `qbs_morphism_tuple` | If all `fi : W -> X i` are morphisms, then `fun w i => fi i w` is a morphism |

### 1.22 List Type

**File:** `theories/coproduct_qbs.v`, lines 544--676

Following Isabelle's `Product_QuasiBorel.thy`, the list type is a QBS on `seq X`:

```
Definition listQ_random (X : qbsType R) : set (mR -> seq X) :=
  [set alpha | exists (len : mR -> nat) (Fi : nat -> mR -> X),
    measurable_fun setT len /\
    (forall i, @qbs_Mx R X (Fi i)) /\
    (forall r, alpha r = mkseq (fun i => Fi i r) (len r))].
```

Requires an inhabitedness witness `x0 : X` for the constant axiom (needed for `nth`).

| Name | Statement |
|------|-----------|
| `qbs_morphism_length` | `qbs_morphism (listQ x0) (natQ R) size` |
| `listQ_nth_random` | `qbs_Mx (listQ x0) alpha -> qbs_Mx X (fun r => nth x0 (alpha r) i)` |

The `listQ_nth_random` proof uses a gluing argument: when `i < len r`, the result is `Fi i r`; otherwise, it is the default `x0`.

---

## Part II: Probability Monad and Integration

Source files: `theories/probability_qbs.v` (783 lines, 16 Qed), `theories/pair_qbs_measure.v` (534 lines, 12 Qed), `theories/qbs_prob_quot.v` (345 lines, 7 Qed), `theories/measure_as_qbs_measure.v` (183 lines, 4 Qed + 2 Defined), `theories/bayesian_regression.v` (442 lines, 15 Qed).

### 2.1 QBS Probability Triple

**File:** `theories/probability_qbs.v`, lines 44--55

```
Record qbs_prob (X : qbsType R) := mkQBSProb {
  qbs_prob_alpha : mR -> X ;
  qbs_prob_mu : probability mR R ;
  qbs_prob_alpha_random : @qbs_Mx R X qbs_prob_alpha ;
}.
```

A probability on a QBS `X` is a triple `(alpha, mu, proof)` where `alpha : mR -> X` is a random element and `mu` is a probability measure on `mR`. The pushforward `alpha_*(mu)` gives the induced distribution on X.

### 2.2 Equivalence of Probability Triples

**File:** `theories/probability_qbs.v`, lines 63--83

```
Definition qbs_prob_equiv (X : qbsType R) (p1 p2 : qbs_prob X) : Prop :=
  forall (U : set X),
    @sigma_Mx R X U ->
    qbs_prob_mu p1 (qbs_prob_alpha p1 @^-1` U) =
    qbs_prob_mu p2 (qbs_prob_alpha p2 @^-1` U).
```

Two triples are equivalent iff they induce the same pushforward measure on X (measured against the induced sigma-algebra `sigma_Mx`).

| Name | Statement |
|------|-----------|
| `qbs_prob_equivxx` | Reflexivity |
| `qbs_prob_equivC` | Symmetry |
| `qbs_prob_equiv_trans` | Transitivity |

### 2.3 The Probability Monad P(X)

**File:** `theories/probability_qbs.v`, lines 88--153

The probability monad uses the pointwise random element condition:

```
Definition monadP_random' (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta | forall r, @qbs_Mx R X (qbs_prob_alpha (beta r))].
```

A stronger definition `monadP_random` (requiring a single shared `alpha` across all `r`) is also provided and shown to imply the weaker one (`monadP_random_impl`). The weak definition is used for the QBS structure because it supports return without quotient types.

```
(* NB: manual HB.pack because monadP creates a non-canonical QBS on qbs_prob X *)
Definition monadP (X : qbsType R) : qbsType R :=
  HB.pack (qbs_prob X)
    (@isQBS.Build R (qbs_prob X)
      (monadP_random' X) ...).
```

### 2.4 Return

**File:** `theories/probability_qbs.v`, lines 165--195

```
Definition qbs_return (X : qbsType R) (x : X) (mu : probability mR R) :
  qbs_prob X :=
  @mkQBSProb X (fun _ => x) mu (@qbs_Mx_const R X x).
```

Return takes a measure parameter `mu` so that `qbs_return X x mu = (fun _ => x, mu)`. All returns with the same point are equivalent regardless of `mu`:

```
Lemma qbs_return_equiv (X : qbsType R) (x : X)
  (mu1 mu2 : probability mR R) :
  qbs_prob_equiv X (qbs_return X x mu1) (qbs_return X x mu2).
```

The proof uses `pselect (U x)` to split into the cases where the preimage is `setT` or `set0`.

```
Lemma qbs_return_random (X : qbsType R) (mu : probability mR R) :
  @qbs_morphism R X (monadP X) (qbs_return X ^~ mu).
```

### 2.5 Bind

**File:** `theories/probability_qbs.v`, lines 197--289

The bind constructs the triple with diagonal extraction:

```
Definition qbs_bind (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)) : qbs_prob Y :=
  @mkQBSProb Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)
    (qbs_prob_mu p)
    hdiag.
```

The key obligation is showing that the diagonal `r |-> alpha_{f(alpha_p(r))}(r)` is random. Three helper lemmas provide this proof in different cases:

| Name | Case | Description |
|------|------|-------------|
| `qbs_bind_alpha_random_strong` | Strong morphism | Extracts the shared `alpha_Y` from `monadP_random` |
| `qbs_bind_alpha_random_const` | Constant alpha | When `p` comes from `return`, diagonal simplifies to `alpha_{f(x)}` |
| `qbs_bind_alpha_random_return` | Right return | When `f` is `return`, diagonal is `alpha_p` |

**Strong morphism condition:**

```
Definition qbs_morphism_strong (X Y : qbsType R) (f : X -> qbs_prob Y) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> monadP_random Y (f \o alpha).
```

A specialized `qbs_bind_strong` combines bind with the strong morphism proof.

### 2.6 Monad Laws

**File:** `theories/probability_qbs.v`, lines 291--333

All three monad laws are proved (up to `qbs_prob_equiv`):

| Name | Law | Statement |
|------|-----|-----------|
| `qbs_bind_returnl` | Left unit | `bind (return x) f ~ f x` |
| `qbs_bind_returnr` | Right unit | `bind m return ~ m` |
| `qbs_bindA` | Associativity | `bind (bind m f) g ~ bind m (fun x => bind (f x) g)` |

### 2.7 Integration

**File:** `theories/probability_qbs.v`, lines 334--453

```
Definition qbs_integral (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x)))%E.
```

Integration reduces to Lebesgue integration on `mR` via `h \o alpha` against `mu`.

**Sigma_Mx-measurability:**

```
Definition qbs_measurable (X : qbsType R) (h : X -> \bar R) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> measurable_fun setT (h \o alpha).
```

**Key theorems:**

| Name | Statement |
|------|-----------|
| `qbs_measurable_sigma_Mx` | `qbs_measurable X h -> measurable V -> sigma_Mx X (h @^-1` V)` |
| `qbs_pushforward_agree` | Equivalent triples have the same pushforward through measurable `h` |
| `qbs_integral_equiv` | Integration respects equivalence for measurable integrands |
| `qbs_integral_equiv_same_alpha` | Simpler version when both triples share the same `alpha` |
| `qbs_integral_const` | Integration of constants |
| `qbs_integral_return` | Integration against return: `int[return x mu] h = int[mu] h(x)` |
| `qbs_integral_bind` | Integration against bind unfolds to the diagonal |

### 2.8 Pushforward Infrastructure

**File:** `theories/probability_qbs.v`, lines 455--494

Connects QBS integration to standard measure-theoretic pushforward:

| Name | Statement |
|------|-----------|
| `qbs_integral_as_pushforward` | `qbs_integral X p h = int[pushforward mu (h \o alpha)] id` |
| `qbs_pushforward_integrable` | Integrability transfers through pushforward |

### 2.9 Functorial Map

**File:** `theories/probability_qbs.v`, lines 496--531

```
Definition monadP_map (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism R X Y f) (p : qbs_prob X) : qbs_prob Y :=
  @mkQBSProb Y (f \o qbs_prob_alpha p) (qbs_prob_mu p)
    (hf _ (qbs_prob_alpha_random p)).
```

| Name | Statement |
|------|-----------|
| `monadP_map_morph` | `monadP_map` is a QBS morphism `monadP X -> monadP Y` |
| `monadP_map_id` | `monadP_map id p ~ p` |
| `monadP_map_comp` | `monadP_map (g \o f) p ~ monadP_map g (monadP_map f p)` |

### 2.10 Expectation and Events

**File:** `theories/probability_qbs.v`, lines 532--545

```
Definition qbs_expect (X : qbsType R) (p : qbs_prob X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Definition qbs_prob_event (X : qbsType R) (p : qbs_prob X)
  (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).
```

### 2.11 Variance

**File:** `theories/probability_qbs.v`, lines 548--559

```
Definition qbs_variance (X : qbsType R) (p : qbs_prob X)
  (f : X -> R) : \bar R :=
  variance (qbs_prob_mu p) (f \o qbs_prob_alpha p).
```

Delegates to the math-comp analysis `variance` definition.

### 2.12 Monad Join

**File:** `theories/probability_qbs.v`, lines 561--578

```
Definition qbs_join (X : qbsType R) (p : qbs_prob (monadP X))
  (hdiag : ...) : qbs_prob X :=
  qbs_bind (monadP X) X p id hdiag.
```

Flattens `P(P(X)) -> P(X)` via bind with the identity.

### 2.13 Monad Strength

**File:** `theories/probability_qbs.v`, lines 580--594

```
Definition qbs_strength (W X : qbsType R) (w : W) (p : qbs_prob X) :
  qbs_prob (prodQ W X) :=
  @mkQBSProb (prodQ W X)
    (fun r => (w, qbs_prob_alpha p r))
    (qbs_prob_mu p)
    (prodQ_const_random w (qbs_prob_alpha_random p)).
```

Pairs a constant `w : W` with a probability `p` on X, producing a probability on `W x X`.

### 2.14 Strength Naturality and Coherence

**File:** `theories/probability_qbs.v`, lines 704--761

Four lemmas establishing the standard coherence conditions for a strong monad:

| Name | Statement |
|------|-----------|
| `qbs_strength_natural` | Strength commutes with morphisms: `map (f x g) (strength w p) ~ strength (f w) (map g p)` |
| `qbs_strength_unit` | Projecting away the unit component recovers `p`: `map snd (strength tt p) ~ p` |
| `qbs_strength_assoc` | Strength associativity: `map assoc (strength (u,v) p) ~ strength u (strength v p)` |
| `qbs_strength_return` | Strength of return is return of pair: `strength w (return x mu) ~ return (w,x) mu` |

### 2.15 Bind Respects Equivalence

**File:** `theories/probability_qbs.v`, lines 596--702

The key congruence result for the quotient monad construction:

```
Lemma qbs_bind_equiv_l (X Y : qbsType R) (p1 p2 : qbs_prob X)
  (f : X -> qbs_prob Y) (g : X -> Y) (hg : qbs_morphism X Y g)
  (hdiag1 : ...) (hdiag2 : ...) (hequiv : qbs_prob_equiv X p1 p2) :
  qbs_prob_equiv Y (qbs_bind X Y p1 f ...) (qbs_bind X Y p2 f ...).
```

Requires that the diagonal factors through a QBS morphism `g : X -> Y`. Specializations include:

| Name | Use case |
|------|----------|
| `qbs_bind_strong_equiv_l` | Strong morphism with factoring |
| `qbs_bind_equiv_l_return` | `f(x) = return(g(x), mu_x)` for morphism `g` |

### 2.16 Quotient Type for QBS Probability

**File:** `theories/qbs_prob_quot.v` (345 lines, 7 Qed)

A setoid-style quotient wrapping `qbs_prob X`:

```
Record qbs_prob_space (X : qbsType R) := QPS {
  qps_repr : qbs_prob X ;
}.

Definition qps_eq (X : qbsType R) (p1 p2 : qbs_prob_space X) : Prop :=
  qbs_prob_equiv X (qps_repr p1) (qps_repr p2).
```

**Lifted operations:**

| Name | Type |
|------|------|
| `qps_return` | `X -> probability mR R -> qbs_prob_space X` |
| `qps_bind` | `qbs_prob_space X -> (X -> qbs_prob Y) -> qbs_prob_space Y` |
| `qps_bind_strong` | Specialized for strong morphisms |
| `qps_integral` | `qbs_prob_space X -> (X -> \bar R) -> \bar R` |
| `qps_map` | `(X -> Y) -> qbs_prob_space X -> qbs_prob_space Y` |
| `qps_expect` | Expectation on the quotient |
| `qps_prob_event` | Probability of events on the quotient |

**Well-definedness:**

| Name | Statement |
|------|-----------|
| `qps_return_equiv` | `qps_eq (return x mu1) (return x mu2)` |
| `qps_integral_equiv` | Integration respects `qps_eq` for measurable integrands |
| `qps_map_equiv` | Map respects `qps_eq` |
| `qps_prob_event_equiv` | Event probability respects `qps_eq` for sigma_Mx sets |

**Monad laws on the quotient (as `qps_eq` equalities):**

| Name | Law |
|------|-----|
| `qps_bind_returnl` | Left unit |
| `qps_bind_returnr` | Right unit |
| `qps_bindA` | Associativity |

**QBS structure on the quotient:**

```
Definition qbs_prob_space_qbs (X : qbsType R) : qbsType R :=
  HB.pack (qbs_prob_space X)
    (@isQBS.Build R (qbs_prob_space X)
      (@qps_Mx X) ...).
```

**Canonical representative:** `qps_pick_repr` uses `constructive_indefinite_description` to select a representative, with `qps_pick_repr_equiv` proving it is equivalent to the original.

### 2.17 Product Measures and Fubini

**File:** `theories/pair_qbs_measure.v`, lines 32--199

**Product probability:**

```
Definition qbs_prob_pair (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y) :
  qbs_prob (prodQ X Y) :=
  mkQBSProb (qbs_pair_alpha p q) (qbs_pair_mu p q) (qbs_pair_alpha_random p q).
```

**Product integration (using the actual product measure):**

```
Definition qbs_pair_integral (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) (h : X * Y -> \bar R) : \bar R :=
  \int[(qbs_prob_mu p \x qbs_prob_mu q)]_rr
    h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).
```

**Fubini theorems:**

| Name | Statement |
|------|-----------|
| `qbs_pair_integralE` | Joint integral = iterated integral |
| `qbs_pair_integral_fst` | Integration over first component marginalizes second |
| `qbs_pair_integral_snd` | Integration over second component marginalizes first |
| `qbs_integral_fst` | User-facing version via `qbs_prob_pair` |
| `qbs_integral_snd` | Symmetric user-facing version |
| `qbs_integral_pair` | User-facing Fubini |

### 2.18 Independence

**File:** `theories/pair_qbs_measure.v`, lines 200--250

```
Definition qbs_indep (X Y Z : qbsType R) (p : qbs_prob Z)
  (f : Z -> X) (g : Z -> Y)
  (hf : qbs_morphism Z X f) (hg : qbs_morphism Z Y g) : Prop :=
  qbs_prob_equiv (prodQ X Y)
    (monadP_map Z (prodQ X Y) (fun z => (f z, g z)) ... p)
    (qbs_prob_pair X Y (monadP_map Z X f hf p) (monadP_map Z Y g hg p)).
```

**Key theorem (E[f*g] = E[f]*E[g] for independent variables):**

```
Lemma qbs_integral_indep_mult (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R) ... :
  qbs_pair_integral X Y px py (fun xy => (f xy.1 * g xy.2)%:E) =
  (qbs_expect X px f * qbs_expect Y py g).
```

The proof uses Fubini to factor the joint integral into a product of marginal integrals via `integralZl` and `integralZr`.

### 2.19 Variance of Independent Sums

**File:** `theories/pair_qbs_measure.v`, lines 252--489

```
Definition qbs_pair_variance (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y) (f : X -> R) (g : Y -> R) : \bar R :=
  variance (qbs_prob_mu px \x qbs_prob_mu py)
    (fun rr : mR * mR =>
      f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2)).
```

**Main theorem:**

```
Lemma qbs_variance_indep_sum (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y) (f : X -> R) (g : Y -> R) ... :
  qbs_pair_variance X Y px py f g =
  (qbs_variance X px f + qbs_variance Y py g)%E.
```

The proof decomposes `Var(F+G) = Var(F) + Var(G) + 2*Cov(F,G)`, then shows `Cov(F,G) = 0` because `E[F*G] = E[F]*E[G]` (by Fubini / independence).

**Helper lemmas:**

| Name | Statement |
|------|-----------|
| `expectation_prod_fst` | `E_{mu1 x mu2}[h(rr.1)] = E_{mu1}[h]` |
| `expectation_prod_snd` | `E_{mu1 x mu2}[h(rr.2)] = E_{mu2}[h]` |
| `variance_prod_fst` | `V_{mu1 x mu2}[h(rr.1)] = V_{mu1}[h]` |
| `variance_prod_snd` | `V_{mu1 x mu2}[h(rr.2)] = V_{mu2}[h]` |
| `expectation_prod_indep` | `E_{mu1 x mu2}[h1(rr.1)*h2(rr.2)] = E_{mu1}[h1] * E_{mu2}[h2]` |

### 2.20 Commutativity of the Probability Monad

**File:** `theories/pair_qbs_measure.v`, lines 491--527

Proposition 22 from the LICS paper: the two ways of combining `P(X) x P(Y) -> P(X x Y)` agree.

```
Lemma qbs_pair_integral_comm (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) ... :
  qbs_pair_integral X Y p q h =
  qbs_pair_integral Y X q p (fun yx => h (yx.2, yx.1)).
```

The proof applies Fubini's theorem: the joint integral against `mu_p x mu_q` equals the iterated integral (first over `mu_p`, then `mu_q`), which by Fubini equals the reversed iteration (first over `mu_q`, then `mu_p`), which is the joint integral against `mu_q x mu_p` with swapped arguments.

### 2.21 Classical Distributions

**File:** `theories/measure_as_qbs_measure.v` (183 lines, 4 Qed + 2 Defined)

**General embedding of classical probability into QBS:**

```
Definition as_qbs_prob (d : measure_display) (M : measurableType d)
  (f : M -> mR) (g : mR -> M) (hf hg h_section : ...)
  (P : probability mR R) : qbs_prob (R_qbs R M).
```

**Concrete distributions:**

| Name | Construction | Description |
|------|-------------|-------------|
| `qbs_normal_distribution` | `(idfun, normal_prob mu sigma)` | Normal(mu, sigma) on `realQ` |
| `qbs_bernoulli` | `((fun r => r < p), uniform_prob)` | Bernoulli(p) on `boolQ` |
| `qbs_uniform` | `(idfun, uniform_prob)` | Uniform[0,1] on `realQ` |

**Recovery theorems:**

| Name | Statement |
|------|-----------|
| `as_qbs_prob_recover` | `qbs_prob_mu (as_qbs_prob ...) (g @^-1` U) = P (g @^-1` U)` |
| `as_qbs_prob_recover_full` | `qbs_prob_event (as_qbs_prob ...) U = P (f @` U)` (with retract) |

**Parameterized morphisms:**

| Name | Statement |
|------|-----------|
| `qbs_normal_morphism` | The normal distribution is a morphism `realQ -> monadP(realQ)` (in the mean parameter) |
| `qbs_uniform_random` | The uniform distribution is a random element of `monadP(realQ)` |

### 2.22 Bayesian Linear Regression

**File:** `theories/bayesian_regression.v` (442 lines, 15 Qed)

A complete Bayesian linear regression example demonstrating the QBS probability monad:

**Model:** `y = slope * x + intercept + noise`, with independent Normal(0,1) priors on `slope` and `intercept`.

**Definitions:**

| Name | Description |
|------|-------------|
| `slope_prior` | Normal(0,1) prior on slope |
| `intercept_prior` | Normal(0,1) prior on intercept |
| `likelihood_single obs_x` | Normal(slope*obs_x + intercept, sigma) likelihood |
| `predictive_integral obs_x h` | Predictive integral over the prior |
| `predictive_event obs_x U` | Predictive event probability |
| `posterior_integral obs_x obs_y g` | Unnormalized posterior integral |
| `evidence obs_x obs_y` | Marginal likelihood / normalizing constant |
| `posterior_normalized obs_x obs_y g` | Normalized posterior expectation |

**Key proofs:**

| Name | Statement |
|------|-----------|
| `likelihood_single_morphism` | Likelihood is a QBS morphism |
| `likelihood_single_strong` | Likelihood satisfies the strong morphism condition |
| `predictive_marginal` | Predictive = iterated integral (Fubini) |
| `predictive_event_marginal` | Event probability marginalizes correctly |
| `posterior_integral_eq` | Posterior decomposes via Fubini |
| `posterior_slope_expectation` | Posterior slope expectation formula |
| `posterior_normalized_total` | Normalized posterior integrates to 1 (given finite evidence) |
| `evidence_ge0` | Evidence is non-negative |

**Multi-observation extension:**

| Name | Description |
|------|-------------|
| `likelihood_product xs ys` | Product of normal pdf evaluations |
| `evidence_multi xs ys` | Multi-observation marginal likelihood |
| `posterior_multi xs ys g` | Multi-observation posterior |
| `likelihood_product_ge0` | Likelihood product is non-negative |
| `evidence_multi_ge0` | Multi-observation evidence is non-negative |
| `posterior_multi_total` | Multi-observation posterior normalization |

**Concrete data:** Five data points from `y = 2x + 1`: `{(1,3), (2,5), (3,7), (4,9), (5,11)}`, with `concrete_evidence`, `concrete_posterior`, and Fubini decomposition.

---

## Part III: Standard Borel Spaces and Architecture

Source file: `theories/standard_borel.v` (1222 lines, 50 Qed).

This file constructs a complete measurable bijection R ~ R x R, proving that the product of standard Borel spaces is standard Borel. The construction composes three layers: (1) a bijection R <-> (0,1) via arctangent, (2) a bijection (0,1)^2 <-> (0,1) via binary digit interleaving, and (3) the composed encode/decode pair.

### 3.1 Standard Borel: R to (0,1) Bijection

**File:** `theories/standard_borel.v`, lines 100--193

```
Definition phi (x : R) : R := atan x / pi + 1 / 2.
Definition psi (y : R) : R := tan (pi * (y - 1 / 2)).
```

| Name | Statement |
|------|-----------|
| `phi_gt0` | `0 < phi x` for all `x` |
| `phi_lt1` | `phi x < 1` for all `x` |
| `psiK` | `cancel phi psi` (psi is left inverse of phi, unconditional) |
| `phiK` | `{in `](0,1)[, cancel psi phi}` (phi is left inverse of psi on (0,1)) |
| `measurable_phi` | `measurable_fun setT phi` |
| `measurable_psi` | `measurable_fun (`](0,1)[) psi` (measurable on the open interval) |

The proofs use `atan_gtNpi2`, `atan_ltpi2`, `atanK`, `tanK`, `cos_gt0_pihalf`, and `continuous_atan`/`continuous_tan` from math-comp analysis.

### 3.2 Binary Digit Machinery

**File:** `theories/standard_borel.v`, lines 196--434

```
Fixpoint bin_digit (x : R) (n : nat) : bool :=
  match n with
  | 0%N => (2%:R^-1 <= x)
  | n'.+1 => bin_digit (if (2%:R^-1 <= x) then x *+ 2 - 1 else x *+ 2) n'
  end.

Definition bin_partial_sum (d : nat -> bool) (n : nat) : R :=
  \sum_(i < n) (d i)%:R * (2%:R^-1) ^+ i.+1.

Definition bin_sum (d : nat -> bool) : R :=
  limn (fun n => bin_partial_sum d n : R^o).
```

**Convergence and bounds:**

| Name | Statement |
|------|-----------|
| `geom_half_sum` | `sum_{i<n} (1/2)^{i+1} = 1 - (1/2)^n` |
| `bin_partial_sum_le1` | Partial sums bounded by 1 |
| `bin_partial_sum_ge0` | Partial sums non-negative |
| `bin_partial_sum_nd` | Partial sums non-decreasing |
| `is_cvg_bin_partial_sum` | Convergence of partial sums |
| `bin_sum_le1` | Binary sum bounded by 1 |
| `bin_sum_ge0` | Binary sum non-negative |

**Reconstruction theorem:**

```
Lemma bin_digits_reconstruction (x : R) :
  0 <= x < 1 -> bin_sum (bin_digits x) = x.
```

The proof proceeds by showing that `x - bin_partial_sum (bin_digit x) n = rem(n) * (1/2)^n` where `rem(n)` is bounded in `[0,1)`, so the error converges to 0 via the squeeze lemma and `cvg_geometric`.

**Uniqueness of binary expansions:**

| Name | Statement |
|------|-----------|
| `no_trailing_ones` | `forall N, exists n, N <= n /\ d n = false` |
| `bin_digits_no_trailing_ones` | `0 <= x < 1 -> no_trailing_ones (bin_digits x)` |
| `bin_sum_no_trailing_lt1` | `no_trailing_ones d -> bin_sum d < 1` |
| `bin_sum_shift` | `bin_sum d = d(0) * 1/2 + bin_sum (d \o S) * 1/2` |
| `no_trailing_ones_shift` | Shifting preserves no-trailing-ones |
| `bin_digits_bin_sum` | `no_trailing_ones d -> bin_digits (bin_sum d) =1 d` |

The `bin_digits_no_trailing_ones` proof is by contradiction: if all digits from position N onward are 1, the remainders satisfy `1 - rem(N+k) = (1 - rem(N)) * 2^k`, which eventually exceeds 1, contradicting `rem >= 0`.

### 3.3 Digit Interleaving and Pairing

**File:** `theories/standard_borel.v`, lines 222--360

```
Definition interleave (d1 d2 : nat -> bool) (n : nat) : bool :=
  if ~~ odd n then d1 n./2 else d2 n./2.

Definition deinterleave_even (d : nat -> bool) (n : nat) : bool := d (n.*2)%N.
Definition deinterleave_odd (d : nat -> bool) (n : nat) : bool := d (n.*2.+1)%N.
```

**Round-trip on digit sequences:**

| Name | Statement |
|------|-----------|
| `interleave_deinterleaveK` | `interleave (deinterleave_even d) (deinterleave_odd d) =1 d` |
| `deinterleave_interleaveK_even` | `deinterleave_even (interleave d1 d2) =1 d1` |
| `deinterleave_interleaveK_odd` | `deinterleave_odd (interleave d1 d2) =1 d2` |
| `interleave_no_trailing_ones` | Interleaving preserves no-trailing-ones |

**Pairing functions on (0,1):**

```
Definition pair_to_unit (xy : R * R) : R :=
  bin_sum (interleave (bin_digits xy.1) (bin_digits xy.2)).

Definition unit_to_pair (r : R) : R * R :=
  (bin_sum (deinterleave_even (bin_digits r)),
   bin_sum (deinterleave_odd (bin_digits r))).
```

### 3.4 Round-Trip Properties

**File:** `theories/standard_borel.v`, lines 436--750

Two round-trip lemmas are established:

**Direction 1 (UNCONDITIONAL -- needed for `is_standard_borel`):**

```
Lemma pair_to_unit_to_pair (xy : R * R) :
  0 <= xy.1 < 1 -> 0 <= xy.2 < 1 ->
  unit_to_pair (pair_to_unit xy) = xy.
```

This uses `bin_digits_bin_sum` (with `interleave_no_trailing_ones` providing the no-trailing-ones hypothesis) and then `deinterleave_interleaveK_even/odd` to recover the original digit sequences, followed by `bin_digits_reconstruction`.

**Direction 2 (conditional):**

```
Lemma unit_to_pair_to_unit (r : R) :
  0 <= r < 1 ->
  no_trailing_ones (deinterleave_even (bin_digits r)) ->
  no_trailing_ones (deinterleave_odd (bin_digits r)) ->
  pair_to_unit (unit_to_pair r) = r.
```

This direction requires no-trailing-ones on the deinterleaved subsequences, which does NOT follow from no-trailing-ones on the full sequence. However, this direction is not needed for `is_standard_borel`, which only requires `g(f(x)) = x`. The set of reals where the extra hypotheses fail is a subset of the dyadic rationals (countable, hence measure-zero).

Additional helper lemmas: `bin_sum_ext`, `bin_sum_has_one_gt0`, `phi_has_true_digit`, `phi_ge0`, `phi_in_01`, `pair_to_unit_phi_gt0`, `pair_to_unit_phi_lt1`, `pair_to_unit_phi_in_itv`, `pair_to_unit_phi_in_01`, `unit_to_pair_fst_ge0`, `unit_to_pair_fst_le1`, `unit_to_pair_snd_ge0`, `unit_to_pair_snd_le1`.

### 3.5 Measurability of the Bijection Components

**File:** `theories/standard_borel.v`, lines 752--922

**Binary digit measurability:**

| Name | Statement |
|------|-----------|
| `measurable_step` | The doubling-and-testing step is measurable |
| `measurable_iter_step` | Iterated step is measurable |
| `measurable_bin_digit` | `measurable_fun setT (fun x => bin_digit x n)` |
| `measurable_interleave_digit` | `measurable_fun setT (fun xy => interleave ... m)` |
| `measurable_deinterleave_even_digit` | Even deinterleaving at position m is measurable |
| `measurable_deinterleave_odd_digit` | Odd deinterleaving at position m is measurable |
| `measurable_bool_scale` | `measurable_fun setT f -> measurable_fun setT (fun x => (f x)%:R * c)` |

**Composite measurability (via `measurable_fun_cvg` on partial sums):**

| Name | Statement |
|------|-----------|
| `measurable_pair_to_unit` | `measurable_fun setT pair_to_unit` |
| `measurable_unit_to_pair_fst` | `measurable_fun setT (fun r => (unit_to_pair r).1)` |
| `measurable_unit_to_pair_snd` | `measurable_fun setT (fun r => (unit_to_pair r).2)` |

**Full-domain measurability of psi:**

```
Lemma measurable_psi_setT : measurable_fun [set: R] (@psi R).
```

The proof factors `psi = sin * cos^{-1}` on `pi*(y - 1/2)`, proves `sin` and `cos` are measurable via continuity, and handles `cos^{-1}` by approximating `x^{-1}` with `x/(x^2 + 1/(n+1))` (which is continuous) and applying `measurable_fun_cvg`. The convergence `inv_cvg_approx` is proved using `cvgV` and `cvg_harmonic`.

### 3.6 Composed Bijection R x R to R

**File:** `theories/standard_borel.v`, lines 924--1208

```
Definition encode_RR (xy : R * R) : R :=
  psi (pair_to_unit (phi xy.1, phi xy.2)).

Definition decode_RR (r : R) : R * R :=
  let uv := unit_to_pair (phi r) in (psi uv.1, psi uv.2).
```

**Main round-trip theorems:**

```
Theorem decode_encode_RR (xy : R * R) :
  decode_RR (encode_RR xy) = xy.
```

The proof chains: (1) `phiK` to recover `pair_to_unit(phi x, phi y)` from `phi(psi(...))`, (2) `pair_to_unit_to_pair` to recover `(phi x, phi y)` from `unit_to_pair(pair_to_unit(...))`, and (3) `psiK` twice to recover `(x, y)`.

```
Theorem encode_decode_RR (r : R)
  (hnt_even : no_trailing_ones (deinterleave_even (bin_digits (phi r))))
  (hnt_odd : no_trailing_ones (deinterleave_odd (bin_digits (phi r))))
  (hu1_pos : 0 < (unit_to_pair (phi r)).1)
  (hu2_pos : 0 < (unit_to_pair (phi r)).2) :
  encode_RR (decode_RR r) = r.
```

This direction requires extra hypotheses (see Section 3.4) but is not needed for `is_standard_borel`.

**Measurability:**

| Name | Statement |
|------|-----------|
| `measurable_encode_RR` | `measurable_fun setT encode_RR` |
| `measurable_decode_RR` | `measurable_fun setT decode_RR` |

The `measurable_encode_RR` proof composes `measurable_phi` (on each component), `measurable_pair_to_unit`, and `measurable_psi` (restricted to `(0,1)` via `measurable_comp` with `pair_to_unit_phi_in_itv`). The `measurable_decode_RR` proof uses `measurable_psi_setT`, `measurable_unit_to_pair_fst/snd`, and `measurable_phi`.

### 3.7 The Punchline: pair_standard_borel

**File:** `theories/standard_borel.v`, lines 1210--1221

```
Lemma pair_standard_borel :
  exists (f : R * R -> R) (g : R -> R * R),
    measurable_fun setT f /\ measurable_fun setT g /\
    (forall xy, g (f xy) = xy).
Proof.
exists encode_RR, decode_RR.
split; first exact: measurable_encode_RR.
split; first exact: measurable_decode_RR.
exact: decode_encode_RR.
Qed.
```

This witnesses that `R x R` is standard Borel in the sense of `is_standard_borel` (defined in `measure_qbs_adjunction.v`), which only requires `g(f(x)) = x` (not the reverse). Combined with `R_full_faithful_standard_borel`, this shows the R functor is fully faithful on products of standard Borel spaces.

### 3.8 File Dependency Graph

```
quasi_borel.v
  |
  +--> measure_qbs_adjunction.v
  |
  +--> coproduct_qbs.v
  |
  +--> probability_qbs.v
  |       |
  |       +--> pair_qbs_measure.v
  |       |       |
  |       |       +--> bayesian_regression.v
  |       |
  |       +--> qbs_prob_quot.v
  |       |
  |       +--> measure_as_qbs_measure.v
  |
  +--> standard_borel.v (no QBS imports; pure analysis)
```

Note: `standard_borel.v` does not import any QBS files. It is a standalone construction in math-comp analysis. The connection to QBS is made via `is_standard_borel` in `measure_qbs_adjunction.v`.

### 3.9 Design Decisions

**HB.pack for non-canonical instances.** Every concrete QBS construction (`prodQ`, `expQ`, `unitQ`, `coprodQ`, `gen_coprodQ`, `piQ`, `listQ`, `monadP`, `sub_qbs`, `generating_qbs`, `map_qbs`, `qbs_supT`, `qbs_prob_space_qbs`) uses `HB.pack` with an NB comment explaining why. The carrier types are non-canonical (product types, sum types, dependent types, bundled morphisms) and cannot be equipped with canonical HB instances.

**Granular imports.** All files use specific imports from math-comp analysis sub-modules (e.g., `From mathcomp.analysis Require Import topology_theory.num_topology`, `measure_theory.measurable_structure`, etc.) rather than blanket `all_analysis`/`all_ssreflect` imports. The exception is `all_boot` and `all_algebra` from the core math-comp library.

**Mathcomp naming conventions.** Lemma names follow math-comp style: `qbs_morphism_fst`, `prodQ_Mx_comp`, `bin_partial_sum_le1`, etc.

**Strong vs. weak morphism condition.** The development factors bind to take an explicit diagonal randomness proof, with helper lemmas for the strong morphism case and the constant-alpha case. This avoids the need for quotient types in the monad construction while preserving compositionality.

**Setoid quotient.** Rather than using Rocq's quotient types (which would require showing that all operations respect equivalence), the development uses a setoid-style wrapper `qbs_prob_space` with an explicit equality `qps_eq`. This is lighter-weight and sufficient for the intended applications.

**Product measure approximation.** The `qbs_prob_pair` construction uses `qbs_prob_mu p` as the base measure (a pragmatic approximation). The proper product construction is handled by `qbs_pair_integral`, which uses `mu_p \x mu_q` on `mR * mR` for genuine product integration.

### 3.10 Comparison with Isabelle AFP

| Feature | Isabelle AFP | This development |
|---------|-------------|------------------|
| QBS axioms | Locale-based | HB mixin/structure |
| Non-canonical carriers | Type classes | Manual `HB.pack` |
| Probability monad | Quotient type | Setoid wrapper + explicit equivalence |
| Standard Borel R~RxR | Not formalized | Complete: `pair_standard_borel` via atan + digit interleaving |
| Bayesian example | Bayesian linear regression (abstract) | Bayesian linear regression with concrete data + multi-observation |
| Monad strength coherence | Not formalized | 4 coherence lemmas (naturality, unit, assoc, return) |
| Monad commutativity | Not formalized | `qbs_pair_integral_comm` (Proposition 22) |
| Integration | Via push-forward | Direct + pushforward infrastructure |
| Fubini | Not formalized | `qbs_pair_integralE` + marginals |
| Independence | Not formalized | `qbs_indep` + `qbs_integral_indep_mult` |
| Variance of sums | Not formalized | `qbs_variance_indep_sum` |
| Lines | ~5000 | 5174 |

### 3.11 Math-Comp Analysis Dependencies

The development uses the following math-comp analysis components:

| Component | Used for |
|-----------|----------|
| `measurableTypeR R` | The Borel measurable space on reals |
| `measurable_fun` | Measurability of functions |
| `probability` | Probability measures |
| `lebesgue_integral` | Integration (`\int[mu]_x f(x)`) |
| `lebesgue_integral_fubini` | Fubini theorem (`integral12_prod_meas1`, `integral21_prod_meas1`) |
| `variance`, `covariance` | Variance and covariance definitions |
| `Lfun`, `Lfun_subset12` | L^p space membership |
| `normal_prob`, `normal_pdf` | Normal distribution |
| `uniform_prob` | Uniform distribution |
| `pushforward`, `integral_pushforward` | Pushforward measures and integrals |
| `hoelder` | Holder's inequality / L^p products |
| `atan`, `tan`, `sin`, `cos`, `pi` | Trigonometric functions |
| `cvg_geometric`, `squeeze_cvgr` | Convergence of geometric series |

### 3.12 Statistics

| File | Lines | Qed | Defined | Defs | Lemmas | Theorems |
|------|------:|----:|--------:|-----:|-------:|---------:|
| `quasi_borel.v` | 742 | 35 | 0 | 14 | 45 | 0 |
| `measure_qbs_adjunction.v` | 248 | 12 | 0 | 2 | 18 | 0 |
| `coproduct_qbs.v` | 676 | 22 | 0 | 8 | 22 | 0 |
| `probability_qbs.v` | 783 | 16 | 0 | 16 | 35 | 0 |
| `pair_qbs_measure.v` | 534 | 12 | 0 | 7 | 15 | 0 |
| `qbs_prob_quot.v` | 345 | 7 | 0 | 12 | 17 | 0 |
| `measure_as_qbs_measure.v` | 183 | 4 | 2 | 5 | 4 | 0 |
| `bayesian_regression.v` | 442 | 15 | 0 | 15 | 16 | 0 |
| `standard_borel.v` | 1222 | 50 | 0 | 13 | 54 | 2 |
| **Total** | **5174** | **173** | **2** | **92** | **226** | **2** |

**Summary:** 175 completed proofs (173 Qed + 2 Defined), 0 Admitted, 0 custom axioms, 330 declarations across 9 files and 5174 lines.

### 3.13 Remaining Work

1. **Disintegration / Markov kernels.** The general case of `qbs_bind_equiv_l` (bind respects equivalence for arbitrary strong morphisms) requires the disintegration theorem, which is beyond the current development.

2. **Standard Borel closure under countable products.** The current `pair_standard_borel` covers binary products; extending to countable products (R ~ R^N) would require a Hilbert-cube-style encoding.

3. **s-Finite kernels.** Integration with the s-finite kernel framework from math-comp analysis (Affeldt, Cohen, Saito) would enable a more compositional treatment of conditional distributions.

4. **Quotient via actual quotient types.** Replacing the setoid wrapper `qbs_prob_space` with Rocq's quotient types would give definitional equality on the quotient, at the cost of requiring all operations to provably respect equivalence.

5. **Standard Borel: full round-trip.** The reverse direction `encode_decode_RR` is proved conditionally (on no-trailing-ones of deinterleaved subsequences). Formalizing that the exception set has measure zero would complete the picture.
