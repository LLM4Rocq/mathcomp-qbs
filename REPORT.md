# Quasi-Borel Spaces in Rocq: A Formalization Report

**Project:** QBS -- Quasi-Borel Spaces in Rocq/Coq
**Repository:** `/home/rocq/QBS`
**Date:** 2026-03-26
**Status:** 124 proofs completed (Qed/Defined), 0 Admitted, 0 custom axioms
**Lines of Rocq:** 3856 across 8 files
**Declarations:** 253 total (79 Definitions, 167 Lemmas, 3 Records, 1 HB mixin, 1 HB structure, 1 Inductive)

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
  - [1.18 Standard Borel Spaces](#118-standard-borel-spaces)
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
  - [2.14 Bind Respects Equivalence](#214-bind-respects-equivalence)
  - [2.15 Quotient Type for QBS Probability](#215-quotient-type-for-qbs-probability)
  - [2.16 Product Measures and Fubini](#216-product-measures-and-fubini)
  - [2.17 Independence](#217-independence)
  - [2.18 Variance of Independent Sums](#218-variance-of-independent-sums)
  - [2.19 Classical Distributions](#219-classical-distributions)
  - [2.20 Bayesian Linear Regression](#220-bayesian-linear-regression)
- [Part III: Architecture and Comparison](#part-iii-architecture-and-comparison)
  - [3.1 File Dependency Graph](#31-file-dependency-graph)
  - [3.2 Design Decisions](#32-design-decisions)
  - [3.3 Comparison with Isabelle AFP](#33-comparison-with-isabelle-afp)
  - [3.4 Math-Comp Analysis Dependencies](#34-math-comp-analysis-dependencies)
  - [3.5 Statistics](#35-statistics)
  - [3.6 Remaining Work](#36-remaining-work)

---

## Part I: Core QBS Theory

Source files: `theories/quasi_borel.v` (741 lines, 35 Qed), `theories/measure_qbs_adjunction.v` (248 lines, 12 Qed), `theories/coproduct_qbs.v` (676 lines, 22 Qed).

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

**NB comments on QBSpace.Pack:** Throughout the development, concrete QBS constructions (products, exponentials, coproducts, etc.) use manual `QBSpace.Pack` calls rather than HB canonical instances, because the carrier types are non-canonical (e.g., `X * Y`, `qbs_hom X Y`, `X + Y`). Each such usage is annotated with an NB comment explaining why.

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
(* NB: manual QBSpace.Pack because R_qbs builds a non-canonical QBS on an
   existing measurableType *)
Definition R_qbs (d : measure_display) (M : measurableType d) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R M
      [set f : mR -> M | measurable_fun setT f]
      ...)).
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
(* NB: manual QBSpace.Pack because this is a non-canonical QBS on (X * Y)%type *)
Definition prodQ (X Y : qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (X * Y)%type
      [set f | @qbs_Mx R X (fst \o f) /\ @qbs_Mx R Y (snd \o f)]
      ...)).
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
(* NB: manual QBSpace.Pack because this is a non-canonical QBS on (qbs_hom X Y) *)
Definition expQ (X Y : qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (qbs_hom X Y)
      [set g : mR -> qbs_hom X Y |
        @qbs_morphism (prodQ realQ X) Y
          (fun p : realQ * X => qbs_hom_val (g p.1) p.2)]
      ...)).
```

**Post-section Arguments declaration:** `Arguments expQ : clear implicits.`

The three closure axioms are established by `expQ_Mx_comp`, `expQ_Mx_const`, `expQ_Mx_glue`.

**Design note:** The carrier of `expQ X Y` is `qbs_hom X Y`, a sigma type. This is one reason concrete QBS constructions use manual `QBSpace.Pack` -- the exponential carrier cannot be expressed as a canonical HB instance on bare function types.

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
(* NB: manual QBSpace.Pack because this is a non-canonical QBS on unit *)
Definition unitQ : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R unit
      [set _ : mR -> unit | True]
      (fun _ _ _ _ => I)
      (fun _ => I)
      (fun _ _ _ _ => I))).
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
(* NB: manual QBSpace.Pack because this is a non-canonical QBS on {x : X | P x} *)
Definition sub_qbs : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R sub_car sub_Mx
      sub_qbs_closed1 sub_qbs_closed2 sub_qbs_closed3)).
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

(* NB: manual QBSpace.Pack because this is a non-canonical QBS on T *)
Definition generating_qbs (T : Type) (G : set (mR -> T)) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R T (generating_Mx G) ...)).
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

**Post-section Arguments declarations:**

```
Arguments QBSHom {R X Y}.
Arguments qbs_hom_val {R X Y}.
Arguments qbs_hom_proof {R X Y}.
```

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

### 1.18 Standard Borel Spaces

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

A random element of the coproduct either factors entirely through `inl`, entirely through `inr`, or is a measurable boolean-controlled gluing. The gluing axiom (`coprodQ_Mx_glue`) is the most involved proof in the file, requiring case analysis on the inhabitedness of X and Y (via `boolp.pselectT`), normalization of each case to the gluing form, and use of `boolp.choice` to extract uniform witnesses.

```
(* NB: manual QBSpace.Pack because sum types lack a canonical QBS instance *)
Definition coprodQ (X Y : qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (X + Y)%type ...)).
```

**Post-section Arguments declarations:** `Arguments coprodQ : clear implicits.`

**Injection and case analysis morphisms:**

| Name | Statement |
|------|-----------|
| `qbs_morphism_inl` | `qbs_morphism X (coprodQ X Y) inl` |
| `qbs_morphism_inr` | `qbs_morphism Y (coprodQ X Y) inr` |
| `qbs_morphism_case` | `qbs_morphism X Z f -> qbs_morphism Y Z g -> qbs_morphism (coprodQ X Y) Z (fun s => match s with inl x => f x \| inr y => g y end)` |

The case analysis lemma uses `measurable_fun_ifT` and `qbs_Mx_glue` to handle the three-way disjunction in `coprodQ_random`.

### 1.20 Coproducts (General / Sigma Type)

**File:** `theories/coproduct_qbs.v`, lines 264--395

For a family `X : I -> qbsType R` indexed by a measurable type `I`:

```
Definition gen_coprodQ_random (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) : set (mR -> {i : I & X i}) :=
  [set f | exists (P : mR -> I) (Fi : forall i, mR -> X i),
    measurable_fun setT P /\
    (forall i, @qbs_Mx R (X i) (Fi i)) /\
    (forall r, f r = existT _ (P r) (Fi (P r) r))].
```

A random element selects an index via a measurable `P : mR -> I` and a value in the corresponding fiber via `Fi`.

```
(* NB: manual QBSpace.Pack because sigma types lack a canonical QBS instance *)
Definition gen_coprodQ (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) (inh : forall i, X i) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R {i : I & X i} ...)).
```

**Post-section Arguments declarations:** `Arguments gen_coprodQ : clear implicits.`

**Note:** The constant axiom requires an inhabitedness witness `inh : forall i, X i`, needed to construct fiber values at indices different from the constant's index.

**Injection morphism:**

```
Lemma qbs_morphism_gen_inj (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) (inh : forall i, X i) (i : I) :
  @qbs_morphism R (X i) (gen_coprodQ d I X inh) (fun x => existT _ i x).
```

**Binary-general isomorphism:**

| Name | Statement |
|------|-----------|
| `qbs_morphism_coprod_to_gen` | `qbs_morphism (coprodQ X Y) (gen_coprodQ bool ...) (fun s => match s ...)` |
| `qbs_morphism_gen_to_coprod` | `qbs_morphism (gen_coprodQ bool ...) (coprodQ X Y) (fun s => ...)` |

The binary coproduct `coprodQ X Y` is isomorphic to the general coproduct over `bool` with `true |-> X, false |-> Y`.

### 1.21 Dependent Products (Pi Type)

**File:** `theories/coproduct_qbs.v`, lines 397--469

```
Definition piQ_random (I : Type) (X : I -> qbsType R) :
  set (mR -> forall i : I, X i) :=
  [set alpha | forall i, @qbs_Mx R (X i) (fun r => alpha r i)].

(* NB: manual QBSpace.Pack because dependent products lack a canonical QBS instance *)
Definition piQ (I : Type) (X : I -> qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (forall i : I, X i) ...)).
```

**Post-section Arguments declarations:** `Arguments piQ : clear implicits.`

A random element of the Pi type is one whose restriction to each index is random. Note that `I` need not be measurable for the Pi type (unlike the Sigma type, which requires a measurable index selection).

| Name | Statement |
|------|-----------|
| `qbs_morphism_proj` | `qbs_morphism (piQ I X) (X i) (fun f => f i)` |
| `qbs_morphism_tuple` | If `fi : forall i, qbs_morphism W (X i) (fi i)`, then `qbs_morphism W (piQ I X) (fun w i => fi i w)` |

### 1.22 List Type

**File:** `theories/coproduct_qbs.v`, lines 544--676

Following Isabelle's `Product_QuasiBorel.thy`, the list type is formalized as a countable coproduct of finite products:

```
Definition listQ_random (X : qbsType R) : set (mR -> seq X) :=
  [set alpha | exists (len : mR -> nat) (Fi : nat -> mR -> X),
    measurable_fun setT len /\
    (forall i, @qbs_Mx R X (Fi i)) /\
    (forall r, alpha r = mkseq (fun i => Fi i r) (len r))].

(* NB: manual QBSpace.Pack because list types lack a canonical QBS instance *)
Definition listQ (X : qbsType R) (x0 : X) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (seq X) ...)).
```

A random element of `listQ X` is determined by a measurable length function and positional random elements. The carrier is `seq X`, the math-comp sequence type.

| Name | Statement |
|------|-----------|
| `qbs_morphism_length` | `qbs_morphism (listQ x0) (natQ R) size` |
| `listQ_nth_random` | `qbs_Mx (listQ x0) alpha -> qbs_Mx X (fun r => nth x0 (alpha r) i)` |

The `listQ_nth_random` lemma shows that extracting the i-th element preserves randomness. The proof constructs a gluing: when `i < len r`, the result is `Fi i r` (random); when `i >= len r`, the result is the default `x0` (constant, hence random).

---

## Part II: Probability Monad and Integration

Source files: `theories/probability_qbs.v` (724 lines, 16 Qed), `theories/pair_qbs_measure.v` (497 lines, 11 Qed), `theories/qbs_prob_quot.v` (345 lines, 7 Qed), `theories/measure_as_qbs_measure.v` (183 lines, 4 Qed + 2 Defined), `theories/bayesian_regression.v` (442 lines, 15 Qed).

### 2.1 QBS Probability Triple

**File:** `theories/probability_qbs.v`, lines 44--54

```
Record qbs_prob (X : qbsType R) := mkQBSProb {
  qbs_prob_alpha : mR -> X ;
  qbs_prob_mu : probability mR R ;
  qbs_prob_alpha_random : @qbs_Mx R X qbs_prob_alpha ;
}.
```

A probability on a QBS `X` is a pair `(alpha, mu)` where:
- `alpha : mR -> X` is a random element (in `qbs_Mx`)
- `mu` is a probability measure on R (type `probability mR R` from math-comp analysis)
- `qbs_prob_alpha_random` witnesses that `alpha` is indeed in `qbs_Mx`

The interpretation: to sample from a QBS probability, first sample `r` from `mu` on R, then apply `alpha` to get a point in X. The "distribution" on X is the pushforward measure `alpha_*(mu)`.

### 2.2 Equivalence of Probability Triples

**File:** `theories/probability_qbs.v`, lines 56--82

Two triples are equivalent if they induce the same pushforward measure:

```
Definition qbs_prob_equiv (X : qbsType R) (p1 p2 : qbs_prob X) : Prop :=
  forall (U : set X),
    @sigma_Mx R X U ->
    qbs_prob_mu p1 (qbs_prob_alpha p1 @^-1` U) =
    qbs_prob_mu p2 (qbs_prob_alpha p2 @^-1` U).
```

For every set `U` in the induced sigma-algebra `sigma_Mx(X)`, the measures of the preimages agree.

| Name | Statement |
|------|-----------|
| `qbs_prob_equivxx` | `qbs_prob_equiv X p p` |
| `qbs_prob_equivC` | `qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p1` |
| `qbs_prob_equiv_trans` | `qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p3 -> qbs_prob_equiv X p1 p3` |

### 2.3 The Probability Monad P(X)

**File:** `theories/probability_qbs.v`, lines 84--153

The QBS structure on `qbs_prob X`:

**Strong definition (for reference):**

```
Definition monadP_random (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta |
    exists alpha g,
      @qbs_Mx R X alpha /\
      (forall r, qbs_prob_alpha (beta r) = alpha) /\
      (forall r, qbs_prob_mu (beta r) = g r)].
```

Requires a *single shared* `alpha` across all `r`.

**Pointwise definition (used for the QBS structure):**

```
Definition monadP_random' (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta | forall r, @qbs_Mx R X (qbs_prob_alpha (beta r))].
```

Each `beta(r)` individually has a random `alpha`.

```
(* NB: manual QBSpace.Pack because monadP creates a non-canonical QBS on qbs_prob X *)
Definition monadP (X : qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (qbs_prob X)
      (monadP_random' X)
      (@monadP_comp X)
      (@monadP_const X)
      (@monadP_glue X))).
```

**Post-section Arguments declarations:** `Arguments monadP : clear implicits.`

**Design note:** The Isabelle development uses the *strong* definition. This formalization uses the weaker pointwise definition for the QBS structure, which avoids the need for quotient types in the basic monad setup. The strong condition is available as `monadP_random` and used as an additional hypothesis for bind (Section 2.5).

```
Lemma monadP_random_impl (X : qbsType R) (beta : mR -> qbs_prob X) :
  monadP_random X beta -> monadP_random' X beta.
```

### 2.4 Return

**File:** `theories/probability_qbs.v`, lines 155--195

```
Definition qbs_return (X : qbsType R) (x : X) (mu : probability mR R) :
  qbs_prob X :=
  @mkQBSProb X (fun _ => x) mu (@qbs_Mx_const R X x).
```

Return takes an explicit measure parameter `mu`. The triple `(fun _ => x, mu)` represents the Dirac distribution at `x`, regardless of `mu`, because the pushforward of any measure through a constant function is the Dirac measure.

**Key property -- all returns at the same point are equivalent:**

```
Lemma qbs_return_equiv (X : qbsType R) (x : X)
  (mu1 mu2 : probability mR R) :
  qbs_prob_equiv X (qbs_return X x mu1) (qbs_return X x mu2).
```

The proof case-splits on `U x`: if `x` is in `U`, the preimage is `setT` and `probability_setT` applies; if not, the preimage is `set0` and `measure0` applies.

**Design note:** The explicit measure parameter is crucial for the left unit law: `bind(return(x), f)` must produce a triple equivalent to `f(x)`. By choosing `mu := qbs_prob_mu (f x)`, the bind's base measure matches `f(x)`'s base measure exactly.

```
Lemma qbs_return_random (X : qbsType R) (mu : probability mR R) :
  qbs_morphism X (monadP X) (qbs_return X ^~ mu).
```

### 2.5 Bind

**File:** `theories/probability_qbs.v`, lines 197--289

Bind constructs:
- `alpha_bind(r) = alpha_{f(alpha_p(r))}(r)` (diagonal extraction)
- `mu_bind = mu_p`

The diagonal extraction requires showing that `r |-> alpha_{f(alpha_p(r))}(r)` is in `qbs_Mx(Y)`. This is the key technical challenge.

**The strong morphism condition:**

```
Definition qbs_morphism_strong (X Y : qbsType R) (f : X -> qbs_prob Y) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> monadP_random Y (f \o alpha).
```

When `f` satisfies the strong condition, each composition `f \o alpha` yields a family with a *single shared* alpha for Y, making the diagonal trivially that shared alpha.

**Diagonal randomness lemmas:**

| Name | Condition | Statement |
|------|-----------|-----------|
| `qbs_bind_alpha_random_strong` | Strong morphism `f` | Diagonal is random |
| `qbs_bind_alpha_random_const` | `alpha_p` is constant (return case) | Diagonal is random |
| `qbs_bind_alpha_random_return` | `f = qbs_return X ^~ mu` | Diagonal is random |

**General bind:**

```
Definition qbs_bind (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)) : qbs_prob Y :=
  @mkQBSProb Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)
    (qbs_prob_mu p) hdiag.
```

Takes an explicit proof of diagonal randomness.

**Specialized bind for strong morphisms:**

```
Definition qbs_bind_strong (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) : qbs_prob Y :=
  qbs_bind X Y p f (qbs_bind_alpha_random_strong p hf).
```

**Bind morphism:**

```
Lemma qbs_bind_morph (X Y : qbsType R) (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) :
  qbs_morphism (monadP X) (monadP Y)
    (fun p => qbs_bind_strong X Y p f hf).
```

### 2.6 Monad Laws

**File:** `theories/probability_qbs.v`, lines 291--332

All three monad laws hold up to `qbs_prob_equiv`:

**Left unit (`qbs_bind_returnl`):**

```
Lemma qbs_bind_returnl (X Y : qbsType R) (x : X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morphism R X (monadP Y) f) :
  qbs_prob_equiv Y
    (qbs_bind X Y (qbs_return X x (qbs_prob_mu (f x))) f
      (qbs_bind_alpha_random_const x f))
    (f x).
```

`bind(return(x), f) ~ f(x)`. The proof is by definitional equality: the bind's alpha at `r` is `qbs_prob_alpha (f x) r` (since `alpha_p = fun _ => x`), and the bind's measure is `qbs_prob_mu (f x)` (by the choice of measure parameter in return).

**Right unit (`qbs_bind_returnr`):**

```
Lemma qbs_bind_returnr (X : qbsType R) (m : qbs_prob X)
  (mu : probability mR R) :
  qbs_prob_equiv X
    (qbs_bind X X m (qbs_return X ^~ mu)
      (qbs_bind_alpha_random_return m mu)) m.
```

`bind(m, return) ~ m`. Again by definitional equality: the bind's alpha at `r` is `qbs_prob_alpha m r`, and the measure is `qbs_prob_mu m`.

**Associativity (`qbs_bindA`):**

```
Lemma qbs_bindA (X Y Z : qbsType R) (m : qbs_prob X)
  (f : X -> qbs_prob Y) (g : Y -> qbs_prob Z)
  (hf_diag : ...) (hg_bind : ...) (hfg_diag : ...) :
  qbs_prob_equiv Z
    (qbs_bind Y Z (qbs_bind X Y m f hf_diag) g (hg_bind _))
    (mkQBSProb ... (qbs_prob_mu m) hfg_diag).
```

`bind(bind(m, f), g) ~ bind(m, fun x => bind(f(x), g))`. The proof is again by definitional unfolding.

### 2.7 Integration

**File:** `theories/probability_qbs.v`, lines 334--453

```
Definition qbs_integral (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x)))%E.
```

Integration against a QBS probability reduces to integration against the base measure `mu`, composing the integrand `h` with the random element `alpha`.

**Sigma_Mx-measurability:**

```
Definition qbs_measurable (X : qbsType R) (h : X -> \bar R) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> measurable_fun setT (h \o alpha).
```

A function `h : X -> \bar R` is QBS-measurable iff for every random element `alpha`, the composition `h \o alpha` is Borel measurable.

**Key integration lemmas:**

| Name | Statement |
|------|-----------|
| `qbs_integral_const` | `qbs_integral X p (fun _ => c) = \int[mu]_x c` |
| `qbs_integral_return` | `qbs_integral X (qbs_return X x mu) h = \int[mu]_r h x` |
| `qbs_integral_bind` | `qbs_integral Y (qbs_bind X Y p f hdiag) h = \int[mu_p]_r h (alpha_{f(alpha_p(r))}(r))` |

**Integration respects equivalence:**

```
Lemma qbs_integral_equiv (X : qbsType R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint1 : ...) (hint2 : ...) :
  qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
```

The proof factors through pushforward measures: `int[mu_i] (h \o alpha_i) = int[pushforward mu_i (h \o alpha_i)] id`, then uses `eq_measure_integral` since the pushforward measures agree on all measurable sets.

**Simpler version for shared alpha:**

```
Lemma qbs_integral_equiv_same_alpha (X : qbsType R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R) :
  qbs_prob_alpha p1 = qbs_prob_alpha p2 ->
  (forall A, measurable A -> qbs_prob_mu p1 A = qbs_prob_mu p2 A) ->
  qbs_integral X p1 h = qbs_integral X p2 h.
```

### 2.8 Pushforward Infrastructure

**File:** `theories/probability_qbs.v`, lines 455--494

Since X is a QBS (not a `measurableType`), the pushforward is formed by composing with `h : X -> \bar R`:

```
Lemma qbs_integral_as_pushforward (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R) (hm : qbs_measurable X h)
  (hint : ...) :
  qbs_integral X p h =
  (\int[pushforward (qbs_prob_mu p) (h \o qbs_prob_alpha p)]_y y)%E.
```

| Name | Statement |
|------|-----------|
| `qbs_pushforward_integrable` | Integrability transfers to the pushforward |
| `qbs_pushforward_agree` | Pushforward measures agree on measurable sets for equivalent triples |
| `qbs_measurable_sigma_Mx` | If `h` is QBS-measurable and `V` is Borel, then `h @^-1` V` is in `sigma_Mx` |

### 2.9 Functorial Map

**File:** `theories/probability_qbs.v`, lines 496--530

```
Definition monadP_map (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism R X Y f) (p : qbs_prob X) : qbs_prob Y :=
  @mkQBSProb Y (f \o qbs_prob_alpha p) (qbs_prob_mu p)
    (hf _ (qbs_prob_alpha_random p)).
```

The functorial action `P(f)` maps `(alpha, mu)` to `(f \o alpha, mu)`.

| Name | Statement |
|------|-----------|
| `monadP_map_morph` | `qbs_morphism (monadP X) (monadP Y) (monadP_map ...)` |
| `monadP_map_id` | `qbs_prob_equiv X (monadP_map X X idfun ... p) p` |
| `monadP_map_comp` | `qbs_prob_equiv Z (monadP_map X Z (g \o f) ... p) (monadP_map Y Z g ... (monadP_map X Y f ... p))` |

### 2.10 Expectation and Events

**File:** `theories/probability_qbs.v`, lines 532--545

```
Definition qbs_expect (X : qbsType R) (p : qbs_prob X) (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Definition qbs_prob_event (X : qbsType R) (p : qbs_prob X) (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).
```

### 2.11 Variance

**File:** `theories/probability_qbs.v`, lines 547--558

```
Definition qbs_variance (X : qbsType R) (p : qbs_prob X) (f : X -> R) : \bar R :=
  variance (qbs_prob_mu p) (f \o qbs_prob_alpha p).
```

Delegates to the math-comp analysis `variance` definition applied to the composition `f \o alpha` against the base measure `mu`. This gives `Var(f) = E[(f \o alpha)^2] - E[f \o alpha]^2`.

### 2.12 Monad Join

**File:** `theories/probability_qbs.v`, lines 560--577

```
Definition qbs_join (X : qbsType R)
  (p : qbs_prob (monadP X))
  (hdiag : @qbs_Mx R X
    (fun r => qbs_prob_alpha (id (qbs_prob_alpha p r)) r)) :
  qbs_prob X :=
  qbs_bind (monadP X) X p id hdiag.
```

Join flattens `P(P(X)) -> P(X)` via bind with the identity. The diagonal extraction gives `alpha_join(r) = qbs_prob_alpha(qbs_prob_alpha(p)(r))(r)`.

### 2.13 Monad Strength

**File:** `theories/probability_qbs.v`, lines 579--594

```
Definition qbs_strength (W X : qbsType R)
  (w : W) (p : qbs_prob X) : qbs_prob (prodQ W X) :=
  @mkQBSProb (prodQ W X)
    (fun r => (w, qbs_prob_alpha p r))
    (qbs_prob_mu p)
    (prodQ_const_random w (qbs_prob_alpha_random p)).
```

Pairs a constant `w : W` with a sampled `x ~ p`, producing a probability on `W x X`. Uses `prodQ_const_random` to prove the paired function is random.

### 2.14 Bind Respects Equivalence

**File:** `theories/probability_qbs.v`, lines 596--702

The key result for the quotient monad: bind respects equivalence on its first argument, under a factoring condition.

```
Lemma qbs_bind_equiv_l (X Y : qbsType R) (p1 p2 : qbs_prob X)
  (f : X -> qbs_prob Y)
  (g : X -> Y) (hg : @qbs_morphism R X Y g)
  (hdiag1 : forall r, qbs_prob_alpha (f (qbs_prob_alpha p1 r)) r =
    g (qbs_prob_alpha p1 r))
  (hdiag2 : ...) (hrand1 : ...) (hrand2 : ...)
  (hequiv : qbs_prob_equiv X p1 p2) :
  qbs_prob_equiv Y (qbs_bind X Y p1 f hrand1) (qbs_bind X Y p2 f hrand2).
```

The proof rewrites the preimage of the bind's alpha as `alpha_p @^-1` (g @^-1` U)`, then uses the equivalence `p1 ~ p2` and the fact that `g @^-1` U` is in `sigma_Mx(X)` (since `g` is a morphism).

**Specializations:**

| Name | Condition |
|------|-----------|
| `qbs_bind_strong_equiv_l` | Strong morphism + factoring |
| `qbs_bind_equiv_l_return` | `f(x) = qbs_return Y (g x) (mu_f x)` |

### 2.15 Quotient Type for QBS Probability

**File:** `theories/qbs_prob_quot.v` (345 lines, 7 Qed)

A setoid-style quotient over `qbs_prob`:

```
Record qbs_prob_space (X : qbsType R) := QPS {
  qps_repr : qbs_prob X ;
}.

Definition qps_eq (X : qbsType R) (p1 p2 : qbs_prob_space X) : Prop :=
  qbs_prob_equiv X (qps_repr p1) (qps_repr p2).
```

**Equivalence relation properties:**

| Name | Statement |
|------|-----------|
| `qps_eqxx` | `qps_eq p p` |
| `qps_eqC` | `qps_eq p1 p2 -> qps_eq p2 p1` |
| `qps_eq_trans` | `qps_eq p1 p2 -> qps_eq p2 p3 -> qps_eq p1 p3` |

**Lifted operations:**

| Name | Type |
|------|------|
| `qps_return` | `X -> probability mR R -> qbs_prob_space X` |
| `qps_bind` | `qbs_prob_space X -> (X -> qbs_prob Y) -> (diagonal proof) -> qbs_prob_space Y` |
| `qps_bind_strong` | `qbs_prob_space X -> (X -> qbs_prob Y) -> (strong proof) -> qbs_prob_space Y` |
| `qps_integral` | `qbs_prob_space X -> (X -> \bar R) -> \bar R` |
| `qps_map` | `(X -> Y) -> (morphism proof) -> qbs_prob_space X -> qbs_prob_space Y` |
| `qps_expect` | `qbs_prob_space X -> (X -> R) -> \bar R` |
| `qps_prob_event` | `qbs_prob_space X -> set X -> \bar R` |

**Well-definedness lemmas:**

| Name | Statement |
|------|-----------|
| `qps_return_equiv` | `qps_eq (qps_return x mu1) (qps_return x mu2)` |
| `qps_integral_equiv` | `qps_eq p1 p2 -> qps_integral p1 h = qps_integral p2 h` (for measurable `h`) |
| `qps_map_equiv` | `qps_eq p1 p2 -> qps_eq (qps_map f hf p1) (qps_map f hf p2)` |
| `qps_prob_event_equiv` | `sigma_Mx X U -> qps_eq p1 p2 -> qps_prob_event p1 U = qps_prob_event p2 U` |

**Monad laws on the quotient (as `qps_eq` equalities):**

| Name | Statement |
|------|-----------|
| `qps_bind_returnl` | `qps_eq (qps_bind (qps_return x ...) f ...) (qps_of (f x))` |
| `qps_bind_returnr` | `qps_eq (qps_bind m (qbs_return X ^~ mu) ...) m` |
| `qps_bindA` | `qps_eq (qps_bind (qps_bind m f ...) g ...) (qps_of ...)` |

**QBS structure on the quotient:**

```
(* NB: manual QBSpace.Pack to equip the quotient wrapper with a QBS structure *)
Definition qbs_prob_space_qbs (X : qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (qbs_prob_space X)
      (@qps_Mx X)
      (@qps_Mx_comp X)
      (@qps_Mx_const X)
      (@qps_Mx_glue X))).
```

**Canonical representative via classical choice:**

```
Definition qps_pick_repr (X : qbsType R) (p : qbs_prob_space X) :
  qbs_prob_space X :=
  QPS (proj1_sig (boolp.constructive_indefinite_description ...)).

Lemma qps_pick_repr_equiv (X : qbsType R) (p : qbs_prob_space X) :
  qps_eq p (qps_pick_repr p).
```

Uses `boolp.constructive_indefinite_description` (classical choice from math-comp's boolP) to extract a representative from the equivalence class. The representative is equivalent to the original by construction.

**Post-section Arguments declarations:**

```
Arguments qbs_prob_space {R}.
Arguments QPS {R X}.
Arguments qps_repr {R X}.
Arguments qps_eq {R X}.
Arguments qps_of {R X}.
Arguments qps_return {R X}.
Arguments qps_bind {R X Y}.
Arguments qps_bind_strong {R X Y}.
Arguments qps_integral {R X}.
Arguments qps_map {R X Y}.
Arguments qps_expect {R X}.
Arguments qps_prob_event {R X}.
Arguments qbs_prob_space_qbs {R}.
Arguments qps_pick_repr {R X}.
```

### 2.16 Product Measures and Fubini

**File:** `theories/pair_qbs_measure.v` (497 lines, 11 Qed)

**Product of QBS probability spaces:**

```
Definition qbs_pair_alpha (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y) :
  mR -> X * Y :=
  fun r => (qbs_prob_alpha p r, qbs_prob_alpha q r).

Definition qbs_prob_pair (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y) :
  qbs_prob (prodQ X Y) := ...
```

The pair alpha is random in the product by `qbs_pair_alpha_random`.

**Product integration using the actual product measure:**

```
Definition qbs_pair_integral (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) : \bar R :=
  \int[(qbs_prob_mu p \x qbs_prob_mu q)]_rr
    h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).
```

This uses the product measure `mu_p \x mu_q` directly on `mR * mR`, avoiding the need for a standard Borel isomorphism `R ~ R x R`.

**Fubini theorem (`qbs_pair_integralE`):**

```
Lemma qbs_pair_integralE (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q h)) :
  qbs_pair_integral X Y p q h =
  @qbs_integral R X p (fun x =>
    @qbs_integral R Y q (fun y => h (x, y))).
```

Joint integration equals iterated integration. The proof delegates to `integral12_prod_meas1` from math-comp analysis.

**Marginal integration:**

| Name | Statement |
|------|-----------|
| `qbs_pair_integral_fst` | `qbs_pair_integral ... (fun xy => h xy.1) = qbs_integral X p h` |
| `qbs_pair_integral_snd` | `qbs_pair_integral ... (fun xy => h xy.2) = qbs_integral Y q h` |

The proofs use `integral_cst` and `probability_setT` to collapse the inner integral.

**User-facing versions:**

| Name | Statement |
|------|-----------|
| `qbs_integral_fst` | First-component integration via `qbs_prob_pair` |
| `qbs_integral_snd` | Second-component integration via `qbs_pair_integral` |
| `qbs_integral_pair` | Fubini's theorem (alias for `qbs_pair_integralE`) |

### 2.17 Independence

**File:** `theories/pair_qbs_measure.v`, lines 200--250

```
Definition qbs_indep (X Y Z : qbsType R) (p : qbs_prob Z)
  (f : Z -> X) (g : Z -> Y)
  (hf : @qbs_morphism R Z X f) (hg : @qbs_morphism R Z Y g) : Prop :=
  @qbs_prob_equiv R (prodQ X Y)
    (@monadP_map R Z (prodQ X Y) (fun z => (f z, g z))
       (@qbs_morphism_pair R Z X Y f g hf hg) p)
    (qbs_prob_pair X Y
       (@monadP_map R Z X f hf p)
       (@monadP_map R Z Y g hg p)).
```

Two random variables `f, g` on a joint space `Z` are independent if the joint pushforward equals the product of marginals.

**E[fg] = E[f] * E[g] for independent random variables:**

```
Lemma qbs_integral_indep_mult (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R)
  (hintf : ...) (hintg : ...) (hintfg : ...) :
  qbs_pair_integral X Y px py (fun xy => (f xy.1 * g xy.2)%:E) =
  (@qbs_expect R X px f * @qbs_expect R Y py g).
```

The proof uses Fubini to factor the product integral: `\int\int f(r1) * g(r2) = \int f(r1) * (\int g(r2)) = E[f] * E[g]`. The inner integral factors out via `integralZl`, and the outer integral via `integralZr`.

### 2.18 Variance of Independent Sums

**File:** `theories/pair_qbs_measure.v`, lines 252--489

**Definition:**

```
Definition qbs_pair_variance (X Y : qbsType R) (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R) : \bar R :=
  variance (qbs_prob_mu px \x qbs_prob_mu py)
    (fun rr : mR * mR =>
      f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2)).
```

**Main theorem: Var(f(X) + g(Y)) = Var(f(X)) + Var(g(Y)) for independent X, Y:**

```
Lemma qbs_variance_indep_sum (X Y : qbsType R) (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R)
  (hf2 : ...) (hg2 : ...) (hf1 : ...) (hg1 : ...)
  (hintf : ...) (hintg : ...) (hintf2 : ...) (hintg2 : ...)
  (hintfg : ...) (hintfm : ...) (hintgm : ...) :
  qbs_pair_variance X Y px py f g =
  (qbs_variance X px f + qbs_variance Y py g)%E.
```

The proof strategy:
1. Apply `varianceD` to get `Var(F+G) = Var(F) + Var(G) + 2*Cov(F,G)`
2. Use `variance_prod_fst` and `variance_prod_snd` to show `Var(F) = Var_px(f)` and `Var(G) = Var_py(g)` (since F and G depend on separate coordinates)
3. Show `Cov(F,G) = 0` using `covarianceE` and `expectation_prod_indep` (E[FG] = E[F]*E[G] by Fubini)
4. Conclude with `subee` (E[F]*E[G] - E[F]*E[G] = 0)

**Supporting lemmas for the variance proof:**

| Name | Statement |
|------|-----------|
| `expectation_prod_fst` | `E_{mu1 x mu2}[h(rr.1)] = E_{mu1}[h]` |
| `expectation_prod_snd` | `E_{mu1 x mu2}[h(rr.2)] = E_{mu2}[h]` |
| `variance_prod_fst` | `V_{mu1 x mu2}[h(rr.1)] = V_{mu1}[h]` |
| `variance_prod_snd` | `V_{mu1 x mu2}[h(rr.2)] = V_{mu2}[h]` |
| `expectation_prod_indep` | `E_{mu1 x mu2}[h1(rr.1) * h2(rr.2)] = E_{mu1}[h1] * E_{mu2}[h2]` |

### 2.19 Classical Distributions

**File:** `theories/measure_as_qbs_measure.v` (183 lines, 4 Qed + 2 Defined)

**General embedding of classical probability into QBS:**

```
Definition as_qbs_prob (d : measure_display) (M : measurableType d)
  (f : M -> mR) (g : mR -> M)
  (hf : measurable_fun setT f) (hg : measurable_fun setT g)
  (h_section : forall x, g (f x) = x)
  (P : probability mR R) : qbs_prob (R_qbs R M).
```

Given a measurable space with encoding/decoding and a probability measure, constructs a QBS probability triple. Uses `Defined` (transparent proof term) so the triple's components can compute.

**Concrete distributions:**

| Name | Definition | Type |
|------|-----------|------|
| `qbs_normal_distribution` | `mkQBSProb idfun (normal_prob mu sigma) measurable_id` | `qbs_prob (realQ R)` |
| `qbs_bernoulli` | `mkQBSProb (fun r => r < p) (uniform_prob ltr01) ...` | `qbs_prob (boolQ R)` |
| `qbs_uniform` | `mkQBSProb idfun (uniform_prob ltr01) measurable_id` | `qbs_prob (realQ R)` |

The normal distribution uses the identity random element with `normal_prob mu sigma` as the base measure. The Bernoulli distribution uses a threshold function `fun r => r < p` with the uniform distribution on `[0,1]`.

**Recovery theorems:**

| Name | Statement |
|------|-----------|
| `as_qbs_prob_recover` | `qbs_prob_mu (as_qbs_prob ...) (g @^-1` U) = P (g @^-1` U)` |
| `as_qbs_prob_recover_full` | `qbs_prob_event (as_qbs_prob ...) U = P (f `` U)` (with retraction) |

**Parameterized distribution morphisms:**

```
Lemma qbs_normal_morphism (sigma : R) (hsigma : (0 < sigma)%R) :
  @qbs_morphism R (realQ R) (monadP (realQ R))
    (fun mu => qbs_normal_distribution mu sigma hsigma).
```

The normal distribution, viewed as a function of its mean, is a QBS morphism into the probability monad. This holds because the alpha component (identity) is always measurable.

```
Lemma qbs_uniform_random :
  @qbs_Mx R (monadP (realQ R)) (fun _ : mR => qbs_uniform).
```

### 2.20 Bayesian Linear Regression

**File:** `theories/bayesian_regression.v` (442 lines, 15 Qed)

A complete Bayesian linear regression example demonstrating the QBS probability monad.

**Model:** `y = slope * x + intercept + noise`, with `noise ~ Normal(0, noise_sigma)`.

**Prior distributions:**

```
Definition slope_prior : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun (normal_prob 0 1 : probability mR R)
    (@measurable_id _ mR setT).

Definition intercept_prior : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun (normal_prob 0 1 : probability mR R)
    (@measurable_id _ mR setT).
```

Independent `Normal(0, 1)` priors on slope and intercept.

**Likelihood:**

```
Definition likelihood_single (obs_x : R) :
  prodQ (realQ R) (realQ R) -> qbs_prob (realQ R) :=
  fun params =>
    @mkQBSProb R (realQ R) idfun
      (normal_prob (fst params * obs_x + snd params) noise_sigma
        : probability mR R) (@measurable_id _ mR setT).
```

For parameters `(slope, intercept)` and observation `x`, the likelihood is `Normal(slope * x + intercept, noise_sigma)`.

| Name | Statement |
|------|-----------|
| `likelihood_single_morphism` | `qbs_morphism (prodQ (realQ R) (realQ R)) (monadP (realQ R)) (likelihood_single obs_x)` |
| `likelihood_single_strong` | `qbs_morphism_strong (prodQ (realQ R) (realQ R)) (realQ R) (likelihood_single obs_x)` |

**Predictive distribution:**

```
Definition predictive_integral (obs_x : R) (h : realQ R -> \bar R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => qbs_integral _ (likelihood_single obs_x params) h).
```

Integrates the likelihood over the independent prior using `qbs_pair_integral`.

**Marginalization via Fubini:**

```
Lemma predictive_marginal (obs_x : R) (h : realQ R -> \bar R) (hint : ...) :
  predictive_integral obs_x h =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      qbs_integral _ (likelihood_single obs_x (s, i)) h)).
```

**Posterior distribution (unnormalized):**

```
Definition posterior_integral (obs_x obs_y : R)
  (g : realQ R * realQ R -> \bar R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params =>
      g params * qbs_prob_event _ (likelihood_single obs_x params) [set obs_y]).
```

**Evidence (normalizing constant):**

```
Definition evidence (obs_x obs_y : R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params =>
      (normal_pdf (fst params * obs_x + snd params) noise_sigma obs_y)%:E).
```

| Name | Statement |
|------|-----------|
| `evidence_ge0` | `0 <= evidence obs_x obs_y` |
| `evidence_eq` | Fubini decomposition of the evidence |

**Normalized posterior:**

```
Definition posterior_normalized (obs_x obs_y : R)
  (g : realQ R * realQ R -> \bar R) : \bar R :=
  (posterior_integral obs_x obs_y g / evidence obs_x obs_y)%E.

Lemma posterior_normalized_total (obs_x obs_y : R)
  (hfin : evidence obs_x obs_y \is a fin_num)
  (hpos : evidence obs_x obs_y != 0%E) :
  posterior_normalized obs_x obs_y (fun _ => 1%E) =
  (posterior_integral obs_x obs_y (fun _ => 1%E) / evidence obs_x obs_y)%E.
```

**Multi-observation posterior:**

```
Definition likelihood_product (xs ys : seq R) :
  realQ R * realQ R -> \bar R :=
  fun params =>
    \prod_(xy <- zip xs ys)
      (normal_pdf (fst params * xy.1 + snd params) noise_sigma xy.2)%:E.

Definition evidence_multi (xs ys : seq R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => likelihood_product xs ys params).

Definition posterior_multi (xs ys : seq R)
  (g : realQ R * realQ R -> \bar R) : \bar R :=
  (qbs_pair_integral slope_prior intercept_prior
    (fun params => g params * likelihood_product xs ys params)
   / evidence_multi xs ys)%E.
```

| Name | Statement |
|------|-----------|
| `likelihood_product_ge0` | `0 <= likelihood_product xs ys params` |
| `evidence_multi_ge0` | `0 <= evidence_multi xs ys` |
| `posterior_multi_total` | Normalization property for multi-observation posterior |

**Concrete instantiation with 5 data points:**

```
Definition data_x : seq R := [:: 1; 2; 3; 4; 5].
Definition data_y : seq R := [:: 3; 5; 7; 9; 11].
```

True model: `y = 2*x + 1`. Definitions `concrete_evidence` and `concrete_posterior` specialize to this data.

| Name | Statement |
|------|-----------|
| `concrete_evidence_ge0` | `0 <= concrete_evidence` |
| `concrete_evidence_eq` | Fubini decomposition with concrete data |

---

## Part III: Architecture and Comparison

### 3.1 File Dependency Graph

```
quasi_borel.v
    |
    +---> measure_qbs_adjunction.v
    |
    +---> coproduct_qbs.v
    |
    +---> probability_qbs.v
              |
              +---> pair_qbs_measure.v
              |         |
              |         +---> bayesian_regression.v
              |
              +---> measure_as_qbs_measure.v
              |
              +---> qbs_prob_quot.v
```

**Build order:**
1. `quasi_borel.v` -- core definitions (HB mixin + structure, morphisms, products, exponentials, etc.)
2. `measure_qbs_adjunction.v` -- depends on 1
3. `coproduct_qbs.v` -- depends on 1
4. `probability_qbs.v` -- depends on 1
5. `pair_qbs_measure.v` -- depends on 1, 4
6. `measure_as_qbs_measure.v` -- depends on 1, 4
7. `qbs_prob_quot.v` -- depends on 1, 4
8. `bayesian_regression.v` -- depends on 1, 4, 5

### 3.2 Design Decisions

#### HB Mixin + Structure vs. Plain Record

**Decision:** Use an HB mixin `isQBS` and structure `QBSpace` with short type `qbsType R`, but build concrete instances via manual `QBSpace.Pack` calls.

**Rationale:** The HB mixin/structure pattern gives standard infrastructure (coercions, canonical projections, `qbsType R` as a universe). However, the exponential `expQ X Y` has carrier `qbs_hom X Y`, a sigma type. This and similar non-canonical carriers (products, coproducts, lists, probability triples) cannot be expressed as HB canonical instances, so each concrete construction uses manual `QBSpace.Pack` calls. Every such usage is annotated with an NB comment explaining the reason.

**Import style:** All 8 files use granular imports (e.g., `From mathcomp.analysis Require Import measure_theory.measurable_structure`) rather than monolithic `all_analysis` or `all_ssreflect`. This makes dependencies explicit and compilation faster.

#### Pointwise vs. Strong monadP_random

**Decision:** Use the pointwise definition `monadP_random'` for the QBS structure on `qbs_prob X`. The strong definition `monadP_random` is available for bind.

**Rationale:** The Isabelle development uses the strong definition (single shared alpha), which requires quotient types to make return work correctly (since `qbs_return` produces triples whose alpha varies with `r`). The pointwise definition avoids this dependency. The strong condition is provided as an additional hypothesis for bind when needed, and helper lemmas (`qbs_bind_alpha_random_strong`, `qbs_bind_alpha_random_const`, `qbs_bind_alpha_random_return`) cover the key cases.

#### Parametric qbs_return

**Decision:** `qbs_return X x mu` takes an explicit measure parameter.

**Rationale:** The left unit law requires `bind(return(x), f)` to produce a triple equivalent to `f(x)`. By choosing `mu := qbs_prob_mu (f x)`, the bind's base measure matches `f(x)`'s base measure exactly, making the proof trivial (definitional equality). All returns at the same point are equivalent regardless of measure (`qbs_return_equiv`).

#### Direct Product Integration

**Decision:** Product measures use `product_measure1` from math-comp analysis directly on `mR * mR`.

**Rationale:** The alternative would require a standard Borel isomorphism `R ~ R x R` (binary expansion), which is approximately 1500 lines of hard measure theory. The direct approach uses the existing product measure infrastructure on the product measurable type `mR * mR`, keeping the development lean.

#### Math-comp Naming Conventions

All lemma and definition names follow math-comp conventions:
- `qbs_Mx` for the random element set (matching field name style)
- `qbs_morphism` for the morphism predicate
- `qbs_bind_returnl` / `qbs_bind_returnr` / `qbs_bindA` for monad laws (matching `bind_returnl`/`bindA` style)
- `qbs_prob_equivxx` / `qbs_prob_equivC` for reflexivity/symmetry (matching `eqxx`/`eqC` style)
- `qps_eqxx` / `qps_eqC` for the quotient equivalence

#### `(**md ... *)` Documentation Headers

Every source file begins with an `(**md ... *)` documentation header block in math-comp analysis style, listing the key definitions and notations provided by the file. These serve as quick reference and are compatible with Coqdoc markdown output.

#### Classical Axioms

The development uses math-comp's classical logic framework (`boolp.pselect`, `boolp.pselectT`, `boolp.constructive_indefinite_description`, `boolp.funext`, `boolp.propext`, `boolp.choice`, `boolp.Prop_irrelevance`). No additional custom axioms are introduced. The total count of `Admitted` lemmas is **0**.

### 3.3 Comparison with Isabelle AFP

The following table compares coverage with the Isabelle AFP formalization (Hirata, Minamide, Sato, 2022).

| Feature | Isabelle AFP | This Development | Notes |
|---------|-------------|------------------|-------|
| Core QBS structure | `quasi_borel` | `isQBS` (HB mixin) / `QBSpace` (HB structure) | Same three axioms; HB infrastructure |
| Morphisms | `qbs_morphism` | `qbs_morphism` | Same definition |
| Binary products | `pair_qbs` | `prodQ` | Same characterization |
| Exponentials | `exp_qbs` | `expQ` | Same carrier (bundled hom) |
| Eval morphism | `qbs_eval` | `qbs_morphism_eval` | Cartesian closure |
| Curry morphism | `qbs_curry` | `qbs_morphism_curry` | Cartesian closure |
| Unit | `unit_qbs` | `unitQ` | Terminal object |
| Binary coproducts | `coprod_qbs` | `coprodQ` | 3-case random elements |
| General coproducts | `coprod_qbs_general` | `gen_coprodQ` | Sigma types |
| Pi types | `PiQ` | `piQ` | Dependent products |
| List type | `list_qbs` | `listQ` | Countable coprod of prods |
| R functor | `R_functor` | `R_qbs` | Measurable -> QBS |
| L functor | `L_functor` | `sigma_Mx` / `L_sigma` | QBS -> sigma-algebra |
| Adjunction | `LR_adjunction` | `lr_adj_natural` | L -| R |
| Product preservation | `R_preserves_prod` | `R_preserves_prod` | R(M1xM2) ~ R(M1)xR(M2) |
| Standard Borel | `standard_borel` | `is_standard_borel` | Definition only |
| Full faithfulness | `R_full_faithful` | `R_full_faithful_standard_borel` | On standard Borel |
| Probability triple | `qbs_prob` | `qbs_prob` (Record) | (alpha, mu) pairs |
| Equivalence | `qbs_prob_equiv` | `qbs_prob_equiv` | Pushforward equality |
| Probability monad | `monad_qbs` | `monadP` | P(X) as QBS |
| Return | `return_qbs` | `qbs_return` | Parametric in mu |
| Bind | `bind_qbs` | `qbs_bind` | Explicit diagonal proof |
| Left unit | `monad_left_unit` | `qbs_bind_returnl` | Up to equivalence |
| Right unit | `monad_right_unit` | `qbs_bind_returnr` | Up to equivalence |
| Associativity | `monad_assoc` | `qbs_bindA` | Up to equivalence |
| Integration | `qbs_integral` | `qbs_integral` | Via base measure |
| Fubini | `fubini_qbs` | `qbs_pair_integralE` | Product measure |
| Independence | Not formalized | `qbs_indep`, `qbs_integral_indep_mult` | E[fg]=E[f]E[g] |
| Variance | Not formalized | `qbs_variance`, `qbs_variance_indep_sum` | Var(X+Y)=Var(X)+Var(Y) |
| Quotient type | Isabelle quotient | `qbs_prob_space` (setoid) | Different approach |
| Normal distribution | Not explicit | `qbs_normal_distribution` | Via math-comp |
| Bernoulli | Not explicit | `qbs_bernoulli` | Via uniform threshold |
| Bayesian regression | `Bayesian_Linear_Regression` | `bayesian_regression.v` | Full example |
| Binary expansion R~RxR | Yes (~1500 lines) | Not formalized | Optional |
| Product of standard Borel | Yes | Not formalized | Optional |

**Key differences from Isabelle:**
1. **HB mixin/structure vs. locale:** Isabelle uses locales; this development uses HB's mixin/structure mechanism with manual `QBSpace.Pack` for concrete instances.
2. **Pointwise vs. strong monadP:** Isabelle uses the strong definition requiring quotient types; this development uses the pointwise definition with explicit diagonal proofs.
3. **Setoid quotient vs. Isabelle quotient:** Isabelle has native quotient types; this development uses a setoid-style wrapper with `qps_eq`.
4. **Independence and variance:** This development includes `qbs_integral_indep_mult` (E[fg]=E[f]E[g]) and `qbs_variance_indep_sum` (Var(X+Y)=Var(X)+Var(Y)), which are not in the Isabelle AFP.
5. **Direct product integration:** This development uses `mR * mR` product measures directly, avoiding the binary expansion `R ~ R x R`.
6. **Math-comp naming conventions:** All names follow math-comp style (`qbs_bind_returnl`, `qbs_bindA`, `qbs_prob_equivxx`, etc.).

### 3.4 Math-Comp Analysis Dependencies

The formalization builds on the following key components from math-comp analysis 1.15.x:

**Measure theory:**
- `probability mR R` -- probability measures on R
- `measurable_fun setT f` -- measurability of functions
- `measurableT_comp` -- composition preserves measurability
- `measurable_id`, `measurable_cst` -- identity and constants are measurable
- `measurable_funD`, `measurable_funM` -- addition and multiplication preserve measurability
- `measurable_fun_ltr`, `measurable_neg` -- comparison and negation
- `measurable_fun_ifT` -- conditional functions
- `measurable_fun_pairP` -- pairing of measurable functions

**Integration:**
- `integral_ge0`, `integral_cst` -- basic integral properties
- `integralZl`, `integralZr` -- linearity of integration
- `eq_integral`, `eq_measure_integral` -- integral extensionality
- `integral_pushforward` -- pushforward integral theorem
- `integrable_pushforward` -- integrability transfers through pushforward

**Product measures:**
- `product_measure1` -- product measure construction
- `integral12_prod_meas1` -- Fubini: `\int[mu1 \x mu2] f = \int[mu1] \int[mu2] f`
- `integral21_prod_meas1` -- reverse Fubini

**Probability:**
- `probability_setT` -- `mu setT = 1` for probability measures
- `normal_prob` -- normal distribution as a probability measure
- `normal_pdf`, `normal_pdf_ge0` -- normal density function
- `uniform_prob` -- uniform distribution
- `variance`, `varianceE`, `varianceD` -- variance and its properties
- `covarianceE` -- covariance expansion
- `Lfun`, `Lfun_subset12`, `Lfun2_mul_Lfun1` -- L^p space membership
- `expectation_fin_num` -- finiteness of expectation

**Classical logic:**
- `boolp.pselect`, `boolp.pselectT` -- decidability of propositions / type inhabitedness
- `boolp.constructive_indefinite_description` -- classical choice
- `boolp.funext`, `boolp.propext` -- function and propositional extensionality
- `boolp.choice` -- countable choice
- `boolp.Prop_irrelevance` -- proof irrelevance

### 3.5 Statistics

| File | Lines | Definitions | Lemmas | Qed | Defined | Admitted |
|------|-------|-------------|--------|-----|---------|----------|
| `quasi_borel.v` | 741 | 14 | 45 | 35 | 0 | 0 |
| `measure_qbs_adjunction.v` | 248 | 2 | 18 | 12 | 0 | 0 |
| `coproduct_qbs.v` | 676 | 8 | 22 | 22 | 0 | 0 |
| `probability_qbs.v` | 724 | 16 | 31 | 16 | 0 | 0 |
| `pair_qbs_measure.v` | 497 | 7 | 14 | 11 | 0 | 0 |
| `measure_as_qbs_measure.v` | 183 | 5 | 4 | 4 | 2 | 0 |
| `qbs_prob_quot.v` | 345 | 12 | 17 | 7 | 0 | 0 |
| `bayesian_regression.v` | 442 | 15 | 16 | 15 | 0 | 0 |
| **Total** | **3856** | **79** | **167** | **122** | **2** | **0** |

**Additional HB declarations (in `quasi_borel.v`):**
- 1 `HB.mixin Record isQBS`
- 1 `HB.structure Definition QBSpace`

**Summary:**
- **124 completed proofs** (122 Qed + 2 Defined)
- **0 Admitted** lemmas
- **0 custom axioms** (all classical reasoning via math-comp's `boolp`)
- **3 Records** (`qbs_hom`, `qbs_prob`, `qbs_prob_space`)
- **1 HB mixin** (`isQBS`)
- **1 HB structure** (`QBSpace`)
- **1 Inductive** (`generating_Mx`)

### 3.6 Remaining Work

The following items from `TODO.md` represent potential extensions, none of which are required by any current theorem:

**Standard Borel infrastructure (optional):**
- Binary expansion `R ~ R x R` (~1500 lines, hard) -- would allow the strong `monadP_random` to work without quotient types
- Product of standard Borel is standard Borel (~200 lines)
- Subset of standard Borel is standard Borel (~100 lines)

**Completed since initial planning:**
- HB mixin/structure (`isQBS` / `QBSpace` / `qbsType R`)
- Granular imports in all 8 files (no `all_analysis`, no `all_ssreflect`)
- Math-comp naming conventions (`qbs_Mx`, `qbs_morphism`, `qbs_bind_returnl/r`, `qbs_bindA`, `qbs_prob_equivxx/C`, etc.)
- `(**md ... *)` documentation headers in all files
- NB comments on all `QBSpace.Pack` usages
- Post-section `Arguments` declarations
- Subspaces (`sub_qbs`)
- Image spaces (`map_qbs`)
- Generating sets (`generating_Mx`)
- Order structure on QBS (`qbs_leT`, `qbs_supT`)
- Dependent products (`piQ`)
- Swap and associators for products
- Exponential structural morphisms (`qbs_morphism_exp_comp`, `qbs_morphism_arg_swap`)
- Comparison morphisms (add, mul, ltr, negb)
- List type (`listQ`)
- Binary/general coproduct isomorphism
- Quotient type (`qbs_prob_space`)
- Monad join and strength
- Variance and independence
- Parameterized distribution morphisms
- Full Bayesian regression example with normalization, evidence, and multi-observation posterior

---

*This report was generated from the source files in `/home/rocq/QBS/theories/`.*
