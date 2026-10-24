# Quasi-Borel Spaces in Rocq: A Formalization Report

**Project:** QBS -- Quasi-Borel Spaces in Rocq
**Repository:** https://github.com/LLM4Rocq/mathcomp-qbs
**Date:** 2026-10-23
**Status:** 402 proofs (397 Qed + 5 Defined), **0 Admitted**, 0 custom axioms
**Lines of Rocq:** 6,370 across 14 files

> **Note**: The higher-order PPL development (`ppl_qbs.v`,
> `ppl_kernel.v`, `showcase/ppl_examples.v`) is on the `ppl`
> branch as future work. This report covers only the QBS
> foundations and the Bayesian regression showcase, as ported
> to MathComp 2.6 (branch `port-mathcomp-2.6`).
**Compatibility:** Rocq (rocq-core) >= 9.2, Math-comp 2.6, Math-comp analysis 1.18

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

**Dependencies:** Rocq (rocq-core >= 9.2), Math-comp 2.6, Math-comp analysis 1.18, Hierarchy Builder 1.10, Math-comp algebra-tactics (master branch; there is no release for Math-comp 2.6 yet) for `ring`/`field`

Throughout, HKSY refers to the LICS 2017 paper above; "Prop. n" and "Thm. n" refer to its numbering.

---

## Table of Contents

- [Part I: Core QBS Theory](#part-i-core-qbs-theory)
  - [1.1 The isQBS Mixin and QBSpace Structure](#11-the-isqbs-mixin-and-qbspace-structure)
  - [1.2 Morphisms](#12-morphisms)
  - [1.3 Bundled Morphisms and Category Laws](#13-bundled-morphisms-and-category-laws)
  - [1.4 The R Functor](#14-the-r-functor)
  - [1.5 Binary Products](#15-binary-products)
  - [1.6 Exponentials (Function Spaces)](#16-exponentials-function-spaces)
  - [1.7 Cartesian Closure](#17-cartesian-closure)
  - [1.8 Unit QBS](#18-unit-qbs)
  - [1.9 Induced Sigma-Algebra and the L Functor](#19-induced-sigma-algebra-and-the-l-functor)
  - [1.10 The L -| R Adjunction (HKSY Prop. 15)](#110-the-l---r-adjunction-hksy-prop-15)
  - [1.11 Standard Borel Spaces (HKSY Prop. 15(2))](#111-standard-borel-spaces-hksy-prop-152)
  - [1.12 Comparison Morphisms](#112-comparison-morphisms)
  - [1.13 Subspaces](#113-subspaces)
  - [1.14 Generating QBS](#114-generating-qbs)
  - [1.15 Image QBS](#115-image-qbs)
  - [1.16 Order Structure](#116-order-structure)
  - [1.17 Coproducts (Binary)](#117-coproducts-binary)
  - [1.18 Countable Coproducts (HKSY Prop. 17)](#118-countable-coproducts-hksy-prop-17)
  - [1.19 Dependent Products (Pi Type)](#119-dependent-products-pi-type)
  - [1.20 List Type](#120-list-type)
- [Part II: Probability Monad and Integration](#part-ii-probability-monad-and-integration)
  - [2.1 Representatives and the Quotient](#21-representatives-and-the-quotient)
  - [2.2 Equality of Probabilities](#22-equality-of-probabilities)
  - [2.3 Integration](#23-integration)
  - [2.4 The Law of a QBS Probability (HKSY eq. (3))](#24-the-law-of-a-qbs-probability-hksy-eq-3)
  - [2.5 Expectation and Variance](#25-expectation-and-variance)
  - [2.6 Integrability, Integral Arithmetic and Probability Inequalities](#26-integrability-integral-arithmetic-and-probability-inequalities)
  - [2.7 The Probability Monad P(X)](#27-the-probability-monad-px)
  - [2.8 Return](#28-return)
  - [2.9 Bind](#29-bind)
  - [2.10 Monad Laws](#210-monad-laws)
  - [2.11 Functorial Map](#211-functorial-map)
  - [2.12 Monad Join](#212-monad-join)
  - [2.13 Monad Strength](#213-monad-strength)
  - [2.14 Integration as a Morphism and Internal Bind (HKSY Thm. 21)](#214-integration-as-a-morphism-and-internal-bind-hksy-thm-21)
  - [2.15 Monadic Product and Commutativity (HKSY Prop. 22(2))](#215-monadic-product-and-commutativity-hksy-prop-222)
  - [2.16 Normalisation (HKSY Sec. VI)](#216-normalisation-hksy-sec-vi)
  - [2.17 Product Measures and Fubini](#217-product-measures-and-fubini)
  - [2.18 Independence](#218-independence)
  - [2.19 Variance of Independent Sums](#219-variance-of-independent-sums)
  - [2.20 Comparison with the Giry Monad (HKSY Prop. 22(3), 23)](#220-comparison-with-the-giry-monad-hksy-prop-223-23)
  - [2.21 Standard Distributions](#221-standard-distributions)
  - [2.22 Bayesian Linear Regression](#222-bayesian-linear-regression)
- [Part III: Standard Borel Spaces (R × R as a Retract of R)](#part-iii-standard-borel-spaces-r--r-as-a-retract-of-r)
  - [3.1 Standard Borel: R to (0,1) Bijection](#31-standard-borel-r-to-01-bijection)
  - [3.2 Binary Digit Machinery](#32-binary-digit-machinery)
  - [3.3 Digit Interleaving and Pairing](#33-digit-interleaving-and-pairing)
  - [3.4 Round-Trip Properties](#34-round-trip-properties)
  - [3.5 Measurability of the Bijection Components](#35-measurability-of-the-bijection-components)
  - [3.6 Composed Retraction R x R to R](#36-composed-retraction-r-x-r-to-r)
  - [3.7 The Punchline: pair_standard_borel](#37-the-punchline-pair_standard_borel)
- [Part IV: Architecture and Project Status](#part-iv-architecture-and-project-status)
  - [4.1 File Dependency Graph](#41-file-dependency-graph)
  - [4.2 Design Decisions](#42-design-decisions)
  - [4.3 Comparison with Isabelle AFP](#43-comparison-with-isabelle-afp)
  - [4.4 Statistics](#44-statistics)
  - [4.5 Honest Limitations](#45-honest-limitations)
  - [4.6 Remaining Work](#46-remaining-work)

---

## Part I: Core QBS Theory

Source files: `theories/measurable_aux.v` (81 lines, 3 Qed), `theories/quasi_borel.v` (887 lines, 62 Qed), `theories/measure_qbs_adjunction.v` (311 lines, 14 Qed + 5 Defined), `theories/coproduct_qbs.v` (721 lines, 44 Qed).

### 1.1 The isQBS Mixin and QBSpace Structure

**File:** `theories/quasi_borel.v`

A quasi-Borel space packages a carrier type with a set of "random elements" satisfying three closure axioms. The entire development is parametric in a `realType` `R`. The structure uses Hierarchy Builder's mixin/structure pattern:

```
HB.mixin Record isQBS (R : realType) (T : Type) := {
  qbs_Mx : set (measurableTypeR R -> T) ;
  qbs_Mx_comp : forall alpha
    (f : {mfun measurableTypeR R >-> measurableTypeR R}),
    qbs_Mx alpha -> qbs_Mx (alpha \o f) ;
  qbs_Mx_const : forall x : T, qbs_Mx (fun _ => x) ;
  qbs_Mx_glue : forall (P : {mfun measurableTypeR R >-> nat})
    (Fi : nat -> measurableTypeR R -> T),
    (forall i, qbs_Mx (Fi i)) ->
    qbs_Mx (fun r => Fi (P r) r) }.

#[short(type="qbsType")]
HB.structure Definition QBSpace (R : realType) := { T of isQBS R T }.
```

**Parameters:**
- `R : realType` -- the real number type, from math-comp analysis
- `mR := measurableTypeR R` -- the Borel measurable space on R

**Notation:** Throughout this report, `mR` denotes `measurableTypeR R`, the measurable type on the reals with the Borel sigma-algebra. The short type name `qbsType R` is used for instances.

**Axiom 1 (Composition closure, `qbs_Mx_comp`):** If `alpha` is a random element and `f : {mfun mR >-> mR}` is a bundled measurable function, then `alpha \o f` is a random element. This corresponds to reparametrization of randomness.

**Axiom 2 (Constant closure, `qbs_Mx_const`):** For any point `x : T`, the constant function `fun _ => x` is a random element. This ensures all deterministic elements are representable.

**Axiom 3 (Gluing, `qbs_Mx_glue`):** Given a measurable partition selector `P : {mfun mR >-> nat}` and a family of random elements `Fi`, the glued function `fun r => Fi (P r) r` is a random element. This is the key axiom distinguishing QBS from mere function spaces.

Since the axioms take bundled measurable functions, two convenience wrappers accept bare `measurable_fun setT` proofs: `qbs_Mx_compT` and `qbs_Mx_glueT`. A third, `measurable_glue`, states that a measurable selector glued with a measurable family is measurable (the domain is an arbitrary `measurableType`, not only R). `qbs_morphism` is defined before the `isQBSMorphism` mixin, which only wraps the proposition `qbs_morphism f`. The subspace `subQ X P` comes with the bundled projection `qbs_sval : qbsHomType (subQ X P) X`.

**NB comments on HB.pack:** Concrete QBS constructions (products, exponentials, coproducts, etc.) are given as `HB.instance` on the carrier type and wrapped in a named definition (`prodQ`, `expQ`, ...), because the carrier types are non-canonical (e.g., `X * Y`, `qbsHomType X Y`, `X + Y`). Where the instance would be ambiguous (e.g. `generatingQ`, which needs a generator set), it is declared on an alias type.

### 1.2 Morphisms

**File:** `theories/quasi_borel.v`

A QBS morphism is a function that preserves random elements under composition:

```
Definition qbs_morphism (X Y : qbsType R) (f : X -> Y) : Prop :=
  forall alpha, qbs_Mx alpha -> qbs_Mx (f \o alpha).
```

### 1.3 Bundled Morphisms and Category Laws

**File:** `theories/quasi_borel.v`

Morphisms are bundled as an HB structure, so that they can be used as plain functions through a coercion and be arguments of other constructions (e.g. the points of an exponential):

```
HB.mixin Record isQBSMorphism (R : realType) (X Y : qbsType R)
    (f : X -> Y) := {
  qbs_hom_proof : forall alpha, qbs_Mx (s := X) alpha ->
    qbs_Mx (s := Y) (f \o alpha)
}.

#[short(type="qbsHomType")]
HB.structure Definition QBSHom (R : realType) (X Y : qbsType R) :=
  {f of @isQBSMorphism R X Y f}.
```

The category structure is given by bundled morphisms `qbs_id`, `qbs_comp f g` (which is `g \o f`) and `qbs_const X y`. Bundled morphisms are equal iff they are pointwise equal:

```
Lemma qbs_homeqP (X Y : qbsType R) (f g : qbsHomType X Y) :
  f = g <-> f =1 g.
```

| Name | Statement |
|------|-----------|
| `qbs_1comp` / `qbs_comp1` | Identity is a left / right unit for `qbs_comp` (stated as `qbs_comp (qbs_id X) f = f` and `qbs_comp f (qbs_id Y) = f`) |
| `qbs_compA` | `qbs_comp f (qbs_comp g h) = qbs_comp (qbs_comp f g) h` |

These establish that QBS spaces form a category, with equalities between bundled morphisms (not just pointwise equalities).

### 1.4 The R Functor

**File:** `theories/quasi_borel.v`; `theories/measure_qbs_adjunction.v`

The R functor sends a measurable type to its QBS of measurable functions. Its random elements are the measurable functions `mR -> M`:

```
Section measQ_instance.
Context d (M : measurableType d).
Let Mx := [set f : mR -> M | measurable_fun setT f].
...
HB.instance Definition _ := @isQBS.Build R M Mx ax1 ax2 ax3.
Definition measQ : qbsType R := M.
End measQ_instance.
```

**Concrete instances:**

```
Definition realQ : qbsType R := measQ mR.
Definition natQ : qbsType R := measQ nat.
Definition boolQ : qbsType R := measQ bool.
```

In `measure_qbs_adjunction.v`, R is shown to be functorial and product-preserving:

```
Lemma measQ_morphism d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (f : {mfun M1 >-> M2}) :
  qbs_morphism (X := measQ R M1) (Y := measQ R M2) f.

Lemma qbs_Mx_measQ_prod d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (alpha : mR -> M1 * M2) :
  qbs_Mx (s := measQ R (M1 * M2)%type) alpha <->
  qbs_Mx (s := prodQ (measQ R M1) (measQ R M2)) alpha.
```

### 1.5 Binary Products

**File:** `theories/quasi_borel.v`

The product QBS on `X * Y` has as random elements the maps whose two components are random:

```
HB.instance Definition _ :=
  @isQBS.Build R (X * Y)%type
    [set f : mR -> X * Y | qbs_Mx (fun r => (f r).1) /\
                           qbs_Mx (fun r => (f r).2)]
    (@prodQ_Mx_comp X Y)
    (@prodQ_Mx_const X Y)
    (@prodQ_Mx_glue X Y).
Definition prodQ : qbsType R := (X * Y)%type.
```

The structural morphisms are bundled: `qbs_fst X Y : qbsHomType (prodQ X Y) X`, `qbs_snd X Y`, and the pairing `qbs_pair f g : qbsHomType W (prodQ X Y)` of `f : qbsHomType W X` and `g : qbsHomType W Y`. The lemma `qbs_Mx_pair_cstl` states that a constant paired with a random element is random in the product.

### 1.6 Exponentials (Function Spaces)

**File:** `theories/quasi_borel.v`

The carrier of `expQ X Y` is `qbsHomType X Y` (bundled morphisms). A function `g : mR -> qbsHomType X Y` is random iff the uncurried map `(r, x) |-> g r x` is a morphism `prodQ realQ X -> Y`:

```
HB.instance Definition _ :=
  @isQBS.Build R (qbsHomType X Y)
    [set g : mR -> qbsHomType X Y |
      qbs_morphism (fun p : realQ * X => (g p.1 : X -> Y) p.2)]
    (@expQ_Mx_comp X Y)
    (@expQ_Mx_const X Y)
    (@expQ_Mx_glue X Y).
Definition expQ : qbsType R := qbsHomType X Y.
```

### 1.7 Cartesian Closure

**File:** `theories/quasi_borel.v`

Evaluation is a bundled morphism `qbs_eval X Y : qbsHomType (prodQ (expQ X Y) X) Y`. Currying comes in two flavours: `qbs_curry f x : qbsHomType Y Z` fixes the first argument, and `qbs_curry_morph f : qbsHomType X (expQ Y Z)` is the full transpose of `f : qbsHomType (prodQ X Y) Z`. Uncurrying and pointwise application are defined from the structural morphisms:

```
Definition qbs_uncurry (X Y Z : qbsType R) (g : qbsHomType X (expQ Y Z)) :
    qbsHomType (prodQ X Y) Z :=
  qbs_comp (qbs_pair (qbs_comp (qbs_fst X Y) g) (qbs_snd X Y)) (qbs_eval Y Z).

Definition qbs_exp_comp (W X Y : qbsType R) (f : qbsHomType W (expQ X Y))
    (g : qbsHomType W X) : qbsHomType W Y :=
  qbs_comp (qbs_pair f g) (qbs_eval X Y).
```

The universal property of exponentials is proved as equalities of bundled morphisms:

| Name | Statement |
|------|-----------|
| `qbs_curry_morphE` | `qbs_curry_morph f x y = f (x, y)` |
| `qbs_uncurryE` | `qbs_uncurry g (x, y) = g x y` |
| `qbs_curryK` | `cancel (@qbs_curry_morph X Y Z) (@qbs_uncurry X Y Z)` (beta) |
| `qbs_uncurryK` | `cancel (@qbs_uncurry X Y Z) (@qbs_curry_morph X Y Z)` (eta) |
| `qbs_curry_morph_uniq` | `qbs_uncurry g = f -> g = qbs_curry_morph f` (uniqueness of the transpose) |

Currying and uncurrying are themselves morphisms between exponentials, so the bijection is internal:

```
Definition qbs_curry_exp : qbsHomType (expQ (prodQ X Y) Z)
  (expQ X (expQ Y Z)) := C.
Definition qbs_uncurry_exp : qbsHomType (expQ X (expQ Y Z))
  (expQ (prodQ X Y) Z) := U.
```

### 1.8 Unit QBS

**File:** `theories/quasi_borel.v`

`unitQ` has every function `mR -> unit` as a random element. It is terminal: `qbs_unit X : qbsHomType X unitQ` is the (unique) morphism into it.

```
HB.instance Definition _ :=
  @isQBS.Build R unit
    [set _ : mR -> unit | True]
    (fun _ _ _ => I)
    (fun _ => I)
    (fun _ _ _ => I).
Definition unitQ : qbsType R := unit.
```

### 1.9 Induced Sigma-Algebra and the L Functor

**File:** `theories/quasi_borel.v`

Every QBS carries a sigma-algebra: a set is measurable iff all random elements pull it back to a Borel set.

```
Definition sigma_Mx (X : qbsType R) : set (set X) :=
  [set U | forall alpha, qbs_Mx alpha ->
    measurable (alpha @^-1` U)].
```

The lemmas `sigma_MxT`, `sigma_Mx0`, `sigma_MxC` and `sigma_Mx_bigcup` show that `sigma_Mx X` is a sigma-algebra. This is packaged as a `measurableType`, the functor L of HKSY Prop. 15:

```
Definition qbs_meas : Type := X.
HB.instance Definition _ :=
  @isMeasurable.Build (sigma_display (@sigma_Mx X)) qbs_meas (@sigma_Mx X)
    (@sigma_Mx0 X) (@sigma_MxC X) (@sigma_Mx_bigcup X).
Lemma qbs_measE (U : set qbs_meas) : measurable U = sigma_Mx (X := X) U.
```

so that the standard mathcomp-analysis machinery (measures, integrals, `measurable_fun`) applies directly to `qbs_meas X`. Random elements are measurable into `L X` (the unit of the adjunction):

```
Lemma qbs_Mx_measurable (a : mR -> X) :
  qbs_Mx a -> measurable_fun [set: mR] (a : mR -> qbs_meas).
```

### 1.10 The L -| R Adjunction (HKSY Prop. 15)

**File:** `theories/quasi_borel.v`; `theories/measure_qbs_adjunction.v`

The adjunction L -| R is the statement that QBS morphisms into `measQ M` are exactly the measurable maps out of `L X`:

```
Lemma qbs_morphism_measurableP d (M : measurableType d) (f : X -> M) :
  qbs_morphism (X := X) (Y := measQ M) f <->
  measurable_fun [set: qbs_meas] (f : qbs_meas -> M).
```

This is HKSY Prop. 15(1). `measure_qbs_adjunction.v` adds the action of L on morphisms and the counit:

```
Lemma qbs_morphism_measurable (X Y : qbsType R) (f : X -> Y) :
  qbs_morphism f ->
  measurable_fun [set: qbs_meas X] (f : qbs_meas X -> qbs_meas Y).

Lemma sigma_Mx_measQ d (M : measurableType d) (U : set M) :
  measurable U -> sigma_Mx (X := measQ R M) U.

Lemma adjunction_counit d (M : measurableType d) :
  measurable_fun [set: qbs_meas (measQ R M)] (idfun : _ -> M).
```

**Galois connection (AFP `rl_order_adjunction`).** Underneath the adjunction is an order adjunction between sets of random elements and sigma-algebras on a fixed carrier. Both maps are antitone and form a Galois connection:

```
Definition sigma_of (T : Type) (Mx : set (mR -> T)) : set (set T) :=
  [set U | forall a, Mx a -> measurable (a @^-1` U)].

Definition Mx_of (T : Type) (S : set (set T)) : set (mR -> T) :=
  [set a | forall U, S U -> measurable (a @^-1` U)].

Lemma sigma_of_antitone (T : Type) (Mx1 Mx2 : set (mR -> T)) :
  Mx1 `<=` Mx2 -> sigma_of Mx2 `<=` sigma_of Mx1.

Lemma Mx_of_antitone (T : Type) (S1 S2 : set (set T)) :
  S1 `<=` S2 -> Mx_of S2 `<=` Mx_of S1.

Lemma sigma_of_Mx_of (T : Type) (S : set (set T)) (Mx : set (mR -> T)) :
  S `<=` sigma_of Mx <-> Mx `<=` Mx_of S.
```

`sigma_of` lives in `quasi_borel.v`, and `sigma_Mx X` is defined as `sigma_of qbs_Mx` (so the former lemma `sigma_MxE` is no longer needed). Instances: `qbs_Mx_measQ : qbs_Mx (s := measQ R M) = Mx_of (@measurable _ M)` and `qbs_Mx_sub_Mx_of : qbs_Mx (s := X) `<=` Mx_of (sigma_Mx (X := X))`.

### 1.11 Standard Borel Spaces (HKSY Prop. 15(2))

**File:** `theories/measure_qbs_adjunction.v`

A measurable space is standard Borel here if it is a measurable retract of R. This is witnessed by data (`encode`, `decode`, and a retraction proof):

```
Record standard_borel_wit d
    (M : measurableType d) := StandardBorelWit {
  sb_encode : {mfun M >-> mR} ;
  sb_decode : {mfun mR >-> M} ;
  sb_encodeK : cancel sb_encode sb_decode
}.
```

Witnesses are given for R, nat, bool, the extended reals `\bar R` (via `contract`/`expand`), and products:

```
Definition R_standard_borel : standard_borel_wit mR.
Definition nat_standard_borel : standard_borel_wit nat.
Definition bool_standard_borel : standard_borel_wit bool.
Definition ereal_standard_borel : standard_borel_wit (\bar R).
Definition prod_standard_borel d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (sb1 : standard_borel_wit M1) (sb2 : standard_borel_wit M2) :
  standard_borel_wit (M1 * M2)%type.
```

`prod_standard_borel` uses `encode_RR`/`decode_RR` from `standard_borel.v` (Part III). It computes on variables (it is built from the two projections), so the encode/decode of a pair reduces definitionally. The extended-real QBS is `measQ R (\bar R)`.

R is full on standard Borel domains, and on standard Borel spaces the sigma-algebra induced by the random elements is the original one:

```
Lemma measQ_full d1 d2 (M1 : measurableType d1) (M2 : measurableType d2)
    (sb : standard_borel_wit M1) (f : M1 -> M2) :
  qbs_morphism (X := measQ R M1) (Y := measQ R M2) f ->
  measurable_fun setT f.

Lemma sigma_Mx_standard_borelP d
    (M : measurableType d) (sb : standard_borel_wit M) :
  forall U : set M, sigma_Mx (X := measQ R M) U <-> measurable U.
```

### 1.12 Comparison Morphisms

**File:** `theories/quasi_borel.v`

Measurable operations on R are QBS morphisms via `measQ`. Addition and multiplication are bundled:

```
Definition qbs_add : qbsHomType (prodQ realQ realQ) realQ
Definition qbs_mul : qbsHomType (prodQ realQ realQ) realQ
```

`qbs_hom_of (f : X -> Y) (hf : qbs_morphism f)` bundles a morphism. In `coproduct_qbs.v`, further concrete morphisms are bundled this way: boolean `qbs_negb`, `qbs_andb`, `qbs_orb`, `qbs_implb`, the strict orders `qbs_ltr : prodQ realQ realQ -> boolQ` and `qbs_ltn : prodQ natQ natQ -> boolQ`, argument swap `qbs_arg_swap : expQ X (expQ Y Z) -> expQ Y (expQ X Z)` (`qbs_arg_swapE : qbs_arg_swap f y x = f x y`), composition `qbs_exp_compose : prodQ (expQ X Y) (expQ Y Z) -> expQ X Z` and `qbs_case_exp : prodQ (expQ X Z) (expQ Y Z) -> expQ (coprodQ X Y) Z` (with `qbs_case f g` the copairing, `qbs_case_inl`, `qbs_case_inr`, `qbs_case_expE`). The helper lemmas `qbs_Mx_if` and `qbs_Mx_app` (a random family of morphisms applied to a random element is random) support them.

Every function out of a countable discrete space is a morphism (`quasi_borel.v`):

```
Lemma natQ_morphism (X : qbsType R) (f : natQ -> X) : qbs_morphism f.
Lemma boolQ_morphism (X : qbsType R) (f : boolQ -> X) : qbs_morphism f.
```

### 1.13 Subspaces

**File:** `theories/quasi_borel.v`

For a predicate `P : set X`, `subQ X P` has carrier `{x : X | P x}` and the random elements `alpha` with `proj1_sig \o alpha` random in `X`.

### 1.14 Generating QBS

**File:** `theories/quasi_borel.v`

Given a set `G` of functions `mR -> T`, `generatingQ G` is the smallest QBS containing `G`, defined as the inductive closure under the three axioms:

```
Inductive generating_Mx (T : Type) (G : set (mR -> T))
  : (mR -> T) -> Prop :=
  | generating_Mx_base : forall alpha, G alpha -> generating_Mx G alpha
  | generating_Mx_comp : forall alpha (f : {mfun mR >-> mR}),
      generating_Mx G alpha ->
      generating_Mx G (alpha \o f)
  | generating_Mx_const : forall x : T, generating_Mx G (fun _ => x)
  | generating_Mx_glue : forall (P : {mfun mR >-> nat})
      (Fi : nat -> mR -> T),
      (forall i, generating_Mx G (Fi i)) ->
      generating_Mx G (fun r => Fi (P r) r).
```

The instance is declared on an alias `qbs_generating_type := T` (declaring it on `T` itself would make every type a `qbsType` with an undetermined generator). The lemma `generatingQ_incl` states `G `<=` qbs_Mx (s := generatingQ G)`, and `generatingQ_least` states that `generating_Mx G` is contained in every closed set containing `G` (a single `qbs_closed Mx` hypothesis).

### 1.15 Image QBS

**File:** `theories/quasi_borel.v`

For a morphism `f : X -> Y`, `mapQ f` is the QBS on `Y` generated by `{f \o alpha | alpha random in X}` (using `generatingQ`, so constants are included even when `f` is not surjective).

| Name | Statement |
|------|-----------|
| `mapQ_random` | `f \o alpha` is random in `mapQ f` when `alpha` is random in `X` |
| `mapQ_sub` | random elements of `mapQ f` are random in `Y` |
| `mapQ_morphism_in` | `f : X -> mapQ f` is a morphism |
| `mapQ_morphism_out` | `g : Y -> Z` is a morphism out of `mapQ f` when it is a morphism out of `Y` |

### 1.16 Order Structure

**File:** `theories/quasi_borel.v`

Following Isabelle, the order on QBS structures on a fixed carrier `T` is inclusion of the sets of random elements:

```
Definition qbs_le (MxX MxY : set (mR -> T)) : Prop :=
  MxX `<=` MxY.
```

with `qbs_le_refl`, `qbs_le_trans` and `qbs_le_anti`. The join of two sets of random elements is `qbs_sup MxX MxY := generatingQ [set alpha | MxX alpha \/ MxY alpha]`, with `qbs_sup_ub_l`, `qbs_sup_ub_r` and `qbs_sup_least` (least upper bound among closed sets, taking a single `qbs_closed` hypothesis).

**Infimum, top, bottom (AFP lattice of QBS structures).** A set of maps is closed when it satisfies the three QBS axioms:

```
Definition qbs_closed (T : Type) (Mx : set (mR -> T)) : Prop :=
  [/\ forall alpha (f : {mfun mR >-> mR}), Mx alpha -> Mx (alpha \o f),
      forall x : T, Mx (fun _ => x) &
      forall (P : {mfun mR >-> nat}) (Fi : nat -> mR -> T),
        (forall i, Mx (Fi i)) -> Mx (fun r => Fi (P r) r)].
```

`qbs_closed_Mx` (the random elements of a QBS are closed) and `qbs_closedI` (closure under `` `&` ``) give the infimum `qbs_inf MxX MxY := generatingQ (MxX `&` MxY)`, with `qbs_inf_lb_l`, `qbs_inf_lb_r`, `qbs_inf_greatest` and `qbs_inf_Mx`. The top structure `qbs_top T` (all maps `mR -> T` random, an instance on the alias `qbs_top_type`) satisfies `qbs_top_ub`; the bottom `qbs_bot T := generatingQ set0` satisfies `qbs_bot_lb`.

The empty QBS is `emptyQ := qbs_top void`. `qbs_Mx0P : qbs_Mx (s := X) = set0 <-> (X -> False)` and it is initial:

```
Definition qbs_void : qbsHomType emptyQ X
Lemma emptyQ_initial (X : qbsType R) (f g : emptyQ -> X) : f = g.
```

### 1.17 Coproducts (Binary)

**File:** `theories/coproduct_qbs.v`

A function `f : mR -> X + Y` is random iff (the set of random elements is the section-local definition `coprodQ_random`, not exported) it factors through `inl`, through `inr`, or is a measurable gluing of an `inl`-part and an `inr`-part via a measurable boolean predicate:

```
(* section-local *)
Definition coprodQ_random (X Y : qbsType R) : set (mR -> X + Y) :=
  [set f |
    (exists a : mR -> X,
      qbs_Mx a /\ forall r, f r = inl (a r))
    \/
    (exists b : mR -> Y,
      qbs_Mx b /\ forall r, f r = inr (b r))
    \/
    (exists (P : mR -> bool) (a : mR -> X) (b : mR -> Y),
      measurable_fun setT P /\
      qbs_Mx a /\
      qbs_Mx b /\
      forall r, f r = if P r then inl (a r) else inr (b r))].
```

`coprodQ X Y` is the resulting QBS on `X + Y`. The injections `qbs_morphism_inl`, `qbs_morphism_inr` and the case analysis `qbs_morphism_case` (for morphisms `f : X -> Z`, `g : Y -> Z`) are morphisms.

### 1.18 Countable Coproducts (HKSY Prop. 17)

**File:** `theories/coproduct_qbs.v`

For a family `X : nat -> qbsType R`, the countable coproduct `sigmaQ X` has carrier `{n & X n}`. A map `f : mR -> {n & X n}` is random iff its index is measurable and, for every index `i` that occurs, `f` agrees on the corresponding part with `(i, a_i)` for a random element `a_i` of `X i`. Fibres that do not occur impose nothing, so empty fibres are allowed.

```
Definition sigmaQ_random (X : nat -> qbsType R) : set (mR -> {n & X n}) :=
  [set f | measurable_fun [set: mR] (fun r => projT1 (f r)) /\
    forall i, (exists r, projT1 (f r) = i) ->
      exists2 a : mR -> X i, qbs_Mx a &
        forall r, projT1 (f r) = i -> f r = existT X i (a r)].
```

The universal property is given by injections and copairing:

```
Lemma qbs_morphism_sigma_inj (i : nat) :
  qbs_morphism (X := X i) (Y := sigmaQ X) (existT X i).

Definition sigma_case Z (f : forall i, X i -> Z) (x : sigmaQ X) : Z :=
  f (projT1 x) (projT2 x).

Lemma qbs_morphism_sigma_case Z (f : forall i, qbsHomType (X i) Z) :
  qbs_morphism (X := sigmaQ X) (Y := Z) (sigma_case f).

Lemma sigma_caseE Z (f : forall i, X i -> Z) i (x : X i) :
  sigma_case f (existT X i x) = f i x.

Lemma sigma_case_eta Z (h : sigmaQ X -> Z) :
  h = sigma_case (fun i x => h (existT X i x)).
```

Copairing is also a morphism with a parameter:

```
Lemma qbs_morphism_sigma_case_prod (W Z : qbsType R) (X : nat -> qbsType R)
  (f : forall i, qbsHomType (prodQ W (X i)) Z) :
  qbs_morphism (X := prodQ W (sigmaQ X)) (Y := Z)
    (fun p => f (projT1 p.2) (p.1, projT2 p.2)).
```

### 1.19 Dependent Products (Pi Type)

**File:** `theories/coproduct_qbs.v`

For a family `X : I -> qbsType R`, `piQ I X` has carrier `forall i, X i`, and `alpha` is random iff `fun r => alpha r i` is random in `X i` for every `i`. (The set of random elements is the section-local `piQ_random`.) The projection `qbs_morphism_proj` and tupling `qbs_morphism_tuple` are morphisms.

### 1.20 List Type

**File:** `theories/coproduct_qbs.v`

Lists are the countable coproduct of the finite powers, as in HKSY Sec. IV:

```
Definition listQ (X : qbsType R) : qbsType R :=
  sigmaQ (fun n => piQ 'I_n (fun=> X)).

Lemma qbs_morphism_size (X : qbsType R) :
  qbs_morphism (X := listQ X) (Y := natQ R) (fun l => projT1 l).
```

**Constructors and conversion.** `list_mk n (a : 'I_n -> X)` builds a list, `qbs_nil` is the empty list and `list_cons` prepends an element. Conversions with `seq X` are mutually inverse, and the constructors correspond to the `seq` ones:

```
Definition seq_of_list (l : listQ X) : seq X
Definition list_of_seq (s : seq X) : listQ X
Lemma list_of_seqK : cancel list_of_seq seq_of_list.
Lemma seq_of_listK : cancel seq_of_list list_of_seq.
Lemma seq_of_list_nil : seq_of_list qbs_nil = [::].
Lemma seq_of_list_cons x l :
  seq_of_list (qbs_cons (x, l)) = x :: seq_of_list l.
```

`qbs_morphism_cons` shows that `list_cons` is a morphism `prodQ X (listQ X) -> listQ X`, bundled as `qbs_cons`.

**Recursion (AFP `rec_list_morphism`).** `list_rec b f` is the structural recursor, with computation rules

```
Lemma list_rec_nil b f : list_rec b f (qbs_nil X) = b.
Lemma list_rec_cons b f x l :
  list_rec b f (qbs_cons (x, l)) = f x l (list_rec b f l).
```

It is a morphism, uniformly in a parameter `W` (via `qbs_morphism_sigma_case_prod`, after induction on the length):

```
Lemma qbs_morphism_list_rec (W : qbsType R) (b : qbsHomType W Y)
  (F : qbsHomType (prodQ W (prodQ X (prodQ (listQ X) Y))) Y) :
  qbs_morphism (X := prodQ W (listQ X)) (Y := Y)
    (fun p => list_rec (b p.1) (fun x l y => F (p.1, (x, (l, y)))) p.2).
```

`list_rec_hom : qbsHomType Y (expQ step_ty (expQ (listQ X) Y))` (with `list_rec_homE`) shows that the recursor is itself a morphism in the base case and the step.

---

## Part II: Probability Monad and Integration

Source files: `theories/probability_qbs.v` (594 lines, 42 Qed), `theories/qbs_monad.v` (715 lines, 61 Qed), `theories/qbs_monad_integral.v` (171 lines, 8 Qed), `theories/qbs_normalize.v` (279 lines, 18 Qed), `theories/pair_qbs_measure.v` (389 lines, 20 Qed), `theories/qbs_giry.v` (135 lines, 8 Qed), `theories/normal_centred.v` (300 lines, 16 Qed), `theories/measure_as_qbs_measure.v` (282 lines, 13 Qed), `theories/showcase/bayesian_regression.v` (474 lines, 29 Qed).

### 2.1 Representatives and the Quotient

**File:** `theories/probability_qbs.v`

A probability on a QBS `X` is represented by a pair `(alpha, mu)`: a random element `alpha : mR -> X` (the record also stores the proof that `alpha` is in `qbs_Mx`) and a probability measure `mu` on `mR`. The pushforward `alpha_*(mu)` gives the induced distribution on X.

```
Record qbs_preprob X := QBSPreProb {
  preprob_alpha : mR -> X ;
  preprob_mu : probability mR R ;
  preprob_alpha_random : qbs_Mx preprob_alpha }.
```

Two representatives are equivalent iff they induce the same measure on `sigma_Mx` sets (the sigma-algebra induced by the random elements):

```
Definition preprob_equiv X (p1 p2 : qbs_preprob X) : Prop :=
  forall U, sigma_Mx U ->
    preprob_mu p1 (preprob_alpha p1 @^-1` U) =
    preprob_mu p2 (preprob_alpha p2 @^-1` U).
```

This is an equivalence relation (`preprob_equiv_rel`), and the probabilities on `X` are the *quotient* of the representatives by it, built with mathcomp's `generic_quotient`, as the almost-everywhere classes of `hoelder.v` (and as in the Lean QBS library):

```
Definition qbs_prob X : Type := {eq_quot (@preprob_equiv_rel X)}.

Definition qbs_prob_alpha X (p : qbs_prob X) : mR -> X :=
  preprob_alpha (repr p).
Definition qbs_prob_mu X (p : qbs_prob X) : probability mR R :=
  preprob_mu (repr p).

Definition mkQBSProb X (alpha : mR -> X) (mu : probability mR R)
    (halpha : qbs_Mx alpha) : qbs_prob X :=
  \pi_(qbs_prob X) (QBSPreProb mu halpha).
```

`qbs_prob_alpha p` and `qbs_prob_mu p` read a chosen representative of the class `p` (`repr p`), and `mkQBSProb alpha mu ha` is the class of a pair. Everything defined from them (events, integrals of `qbs_measurable` functions) does not depend on the choice of representative (Sections 2.2 and 2.3). As in the Isabelle development, where HOL has no dependent types, the probabilities are a quotient; the difference is that the space `X` is a type parameter here, so the quotient is of pairs rather than of triples `(X, alpha, mu)`.

### 2.2 Equality of Probabilities

**File:** `theories/probability_qbs.v`

The probability of an event is computed on a representative:

```
Definition qbs_prob_event (X : qbsType R) (p : qbs_prob X)
  (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).
```

On a class given by a pair, it is computed on the pair, and two probabilities are equal iff they agree on `sigma_Mx` sets:

```
Lemma qbs_prob_event_mk (X : qbsType R) (alpha : mR -> X)
    (mu : probability mR R) (halpha : qbs_Mx alpha) (U : set X) :
  sigma_Mx U ->
  qbs_prob_event X (mkQBSProb mu halpha) U = mu (alpha @^-1` U).

Lemma qbs_prob_eqP (X : qbsType R) (p1 p2 : qbs_prob X) :
  p1 = p2 <->
  forall U, sigma_Mx U -> qbs_prob_event X p1 U = qbs_prob_event X p2 U.

Lemma qbs_probK (X : qbsType R) (p : qbs_prob X) :
  mkQBSProb (qbs_prob_mu p) (qbs_prob_alpha_random p) = p.
```

`qbs_prob_eqP` is the tool for all the equalities below: a law between probabilities is proved by comparing the probabilities of `sigma_Mx` events.

### 2.3 Integration

**File:** `theories/probability_qbs.v`

Integration against a QBS probability goes through the base measure:

```
Definition qbs_integral (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x)))%E.

Definition qbs_measurable (X : qbsType R) (h : X -> \bar R) : Prop :=
  forall alpha, qbs_Mx (s := X) alpha ->
    measurable_fun setT (fun r => h (alpha r)).
```

A function `h` is `qbs_measurable` iff it is measurable on every random element; `qbs_measurable_sigma_Mx` shows that preimages of measurable sets are `sigma_Mx` sets, and `qbs_measurable_measQ` and `qbs_measurable_comp` give measurable functions on `measQ M` and compositions with morphisms. The integral of a `qbs_measurable` function only depends on the measure of `sigma_Mx` sets, hence on the equivalence class of a representative:

```
Lemma integral_sigma_Mx (X : Type) (a1 a2 : mR -> X)
    (m1 m2 : {measure set mR -> \bar R}%R) (k : X -> \bar R) :
  qbs_Mx a1 -> qbs_Mx a2 ->
  (forall U, sigma_Mx U -> m1 (a1 @^-1` U) = m2 (a2 @^-1` U)) ->
  qbs_measurable X k -> \int[m1]_r k (a1 r) = \int[m2]_r k (a2 r).
```

(The nonnegative core is `ge0_integral_sigma_Mx`.) In particular integration against the class of a pair is integration against the pair:

```
Lemma qbs_integral_mk (X : qbsType R) (alpha : mR -> X)
    (mu : probability mR R) (halpha : qbs_Mx alpha) (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_integral X (mkQBSProb mu halpha) h = (\int[mu]_r h (alpha r))%E.
```

### 2.4 The Law of a QBS Probability (HKSY eq. (3))

**File:** `theories/probability_qbs.v`

Using the measurable structure on `L X = qbs_meas X`, a QBS probability has a law, a genuine probability measure:

```
Lemma qbs_measurableP (X : qbsType R) (h : X -> \bar R) :
  qbs_measurable X h <->
  measurable_fun [set: qbs_meas X] (h : qbs_meas X -> \bar R).

Definition qbs_law (X : qbsType R) (p : qbs_prob X) :
    probability (qbs_meas X) R :=
  distribution (qbs_prob_mu p) (qbs_prob_alpha_mfun p).

Lemma qbs_lawE (X : qbsType R) (p : qbs_prob X) (A : set X) :
  qbs_law p A = qbs_prob_event X p A.

Lemma qbs_prob_eq_lawP (X : qbsType R) (p1 p2 : qbs_prob X) :
  p1 = p2 <->
  (forall A : set (qbs_meas X), measurable A -> qbs_law p1 A = qbs_law p2 A).

Lemma qbs_integral_law (X : qbsType R) (p : qbs_prob X) (h : X -> \bar R) :
  qbs_measurable X h -> qbs_integral X p h = (\int[qbs_law p]_x h x)%E.
```

Equality of probabilities is thus equality of laws, and QBS integration is Lebesgue integration against the law (`ge0_qbs_integral_law` is the nonnegative version).

### 2.5 Expectation and Variance

**File:** `theories/probability_qbs.v`

```
Definition qbs_expect (X : qbsType R) (p : qbs_prob X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Definition qbs_variance (X : qbsType R) (p : qbs_prob X)
  (f : X -> R) : \bar R :=
  variance (qbs_prob_mu p) (f \o qbs_prob_alpha p).
```

QBS expectation is the mathcomp-analysis expectation on the law:

```
Lemma qbs_expectE (X : qbsType R) (p : qbs_prob X)
    (f : {mfun qbs_meas X >-> R}) :
  qbs_expect X p f = ('E_(qbs_law p)[f])%E.
```

The variance is the integral of the squared centred function, and for `qbs_measurable` functions it is computed on any pair:

```
Lemma qbs_varianceE_integral (X : qbsType R) (p : qbs_prob X) (h : X -> R) :
  qbs_variance X p h =
  qbs_integral X p (fun x => ((h x - fine (qbs_expect X p h)) *
                              (h x - fine (qbs_expect X p h)))%R%:E).

Lemma qbs_variance_mk (X : qbsType R) (alpha : mR -> X)
    (mu : probability mR R) (halpha : qbs_Mx alpha) (h : X -> R) :
  qbs_measurable X (fun x => (h x)%:E) ->
  qbs_variance X (mkQBSProb mu halpha) h = variance mu (h \o alpha).
```

### 2.6 Integrability, Integral Arithmetic and Probability Inequalities

**File:** `theories/probability_qbs.v`

```
Definition qbs_integrable (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :=
  (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p).
```

| Name | Statement |
|------|-----------|
| `qbs_varianceE` | `Var(h) = E[h^2] - E[h]^2` (for `h` in `Lfun 2`) |
| `qbs_varianceZ` | `Var(a h) = a^2 Var(h)` |
| `qbs_variance_affine` | `Var(a * h + b) = a^2 * Var(h)` (for `h` in `Lfun 2`) |
| `qbs_integralE` | `qbs_integral X p h = qbs_integral X p h^\+ - qbs_integral X p h^\-` |
| `qbs_integral_funeneg_lty` | If `h` is integrable then the integral of its negative part is `< +oo` |
| `qbs_integrable_cst`, `qbs_integral_cst` | Constants are integrable; `qbs_integral X p (fun=> c) = c` |
| `qbs_integrable_mk` | For measurable `h`: `qbs_integrable X (mkQBSProb mu halpha) h <-> mu.-integrable setT (h \o alpha)` |
| `qbs_integrableP` | For measurable `h`: `qbs_integrable X p h <-> qbs_integral X p (fun x => `|h x|) < +oo` |
| `qbs_integrable_abseP` | Integrability of `h` and of `abse \o h` coincide (for measurable `h`) |
| `qbs_integrableMr` | Integrability is stable under bounded `qbs_measurable` multipliers |
| `qbs_integrable_bounded` | Bounded `qbs_measurable` real functions are integrable |
| `qbs_integrable_sqrB` | Squares of `k - c` for `k` in `Lfun 2` are integrable |
| `qbs_integral_le` | Monotonicity for integrable functions: `f <= g` pointwise implies `qbs_integral X p f <= qbs_integral X p g` |
| `ge0_qbs_integral_le` | The same for nonnegative measurable functions |

The Markov and Chebyshev inequalities are lifted to QBS probabilities, with the hypothesis that `h` is `qbs_measurable`. `qbs_rv` builds a `{RV (qbs_prob_mu p) >-> R}` from a measurable composition.

```
Lemma qbs_markov (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (f : R -> R) (eps : R)
    (hm : qbs_measurable X (fun x => (h x)%:E))
    (heps : (0 < eps)%R)
    (hmf : measurable_fun [set: R] f)
    (hf0 : forall r, (0 <= r)%R -> (0 <= f r)%R)
    (hfnd : {in Num.nneg &, {homo f : x y / (x <= y)%R}}) :
  (f eps)%:E * qbs_prob_event X p [set x | (eps <= `|h x|)%R] <=
  qbs_integral X p (fun x => (f `|h x|)%:E).

Lemma qbs_chebyshev (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (eps : R)
    (hm : qbs_measurable X (fun x => (h x)%:E))
    (heps : (0 < eps)%R) :
  qbs_prob_event X p [set x | (eps <= `|h x - fine (qbs_expect X p h)|)%R] <=
  (eps ^- 2)%:E * qbs_variance X p h.
```

### 2.7 The Probability Monad P(X)

**File:** `theories/qbs_monad.v`

Following HKSY, the random elements of `P(X)` are the maps `r |-> [alpha, g r]` for a *single* random element `alpha` of `X` and a measurable map `g : R -> giry R` into probability measures (the Giry space of mathcomp-analysis). This is the strong (shared-`alpha`) condition; unlike a pointwise condition, it makes `qbs_bind` total. The carrier is `qbs_prob X` itself:

```
Record qbs_prob_rep X (b : mR -> qbs_prob X) (a : mR -> X) (g : mR -> G) :
    Prop := QbsProbRep {
  qbs_rep_random : qbs_Mx a ;
  qbs_rep_measurable : measurable_fun [set: mR] g ;
  qbs_rep_mass : forall r, g r [set: mR] = 1 ;
  qbs_rep_event : forall r U, sigma_Mx U ->
    qbs_prob_event X (b r) U = g r (a @^-1` U) }.

Definition monadP_random X : set (mR -> qbs_prob X) :=
  [set b | exists a g, qbs_prob_rep b a g].

HB.instance Definition _ X :=
  isQBS.Build R (qbs_prob X) (@monadP_comp X) (@monadP_const X)
    (@monadP_glue X).
```

Here `G := giry mR R`, and `qbs_prob_rep b a g` says that `b r` is represented by `[a, g r]` for every `r`. Since probabilities are classes, no saturation of random elements with respect to equivalence is needed. `monadP_random_event` shows that the probability of a `sigma_Mx` event is measurable in `r`; for a morphism `f : X -> qbs_prob Y` this is `qbs_measurable_event` (`x |-> qbs_prob_event Y (f x) U` is QBS-measurable). The glue axiom (`monadP_glue`) decodes the selector with the retraction `encode_RR_mR`/`decode_RR_mR` from `standard_borel.v`.

The file also defines a small helper `giry_prob m m1`, the probability measure `m : giry T R` given a proof `m1` that `m` has total mass 1, with `giry_bindE` and `giry_bind_setT` for the Giry bind.

### 2.8 Return

**File:** `theories/qbs_monad.v`

```
Definition qbs_return X (x : X) : qbs_prob X :=
  mkQBSProb (fun=> x) (\d_(0 : mR))%R (qbs_Mx_const x).

Lemma qbs_return_event X (x : X) (U : set X) : sigma_Mx U ->
  qbs_prob_event X (qbs_return x) U = (x \in U)%:R%:E.

Lemma qbs_return_morphism X : qbs_morphism (X := X) (Y := qbs_prob X)
  (@qbs_return X).

Lemma qbs_return_integral X (x : X) (h : X -> \bar R) : qbs_measurable X h ->
  qbs_integral X (qbs_return x) h = h x.
```

`qbs_returnQ X : qbsHomType X (qbs_prob X)` is the bundled version.

### 2.9 Bind

**File:** `theories/qbs_monad.v`

For `p : qbs_prob X` and a *bundled morphism* `f : qbsHomType X (qbs_prob Y)`, bind is defined without any side condition: `f \o alpha_p` is random in `P(Y)`, so it has a representation `[a, g]`, and the bound measure is the Giry bind of `mu_p` with `g` (computed on the representative of `p`).

```
Definition qbs_bind : qbs_prob Y :=
  mkQBSProb bind_a (giry_prob bind_mu1) (qbs_rep_random bind_rep).

Lemma ge0_qbs_integral_bind (h : Y -> \bar R) :
  qbs_measurable Y h -> (forall y, 0 <= h y) ->
  qbs_integral Y qbs_bind h =
  qbs_integral X p (fun x => qbs_integral Y (f x) h).

Lemma qbs_bind_event (U : set Y) : sigma_Mx U ->
  qbs_prob_event Y qbs_bind U =
  qbs_integral X p (fun x => qbs_prob_event Y (f x) U).
```

Bind with a fixed continuation is itself a morphism, and the bundled version is `qbs_bindQ`:

```
Lemma qbs_bind_morphism X Y Z (f : qbsHomType X (qbs_prob Y))
    (g : qbsHomType Y (qbs_prob Z)) :
  qbs_morphism (X := X) (Y := qbs_prob Z) (fun x => qbs_bind (f x) g).

Definition qbs_bindQ X Y Z (f : qbsHomType X (qbs_prob Y))
    (g : qbsHomType Y (qbs_prob Z)) : qbsHomType X (qbs_prob Z) :=
  HB.pack (fun x => qbs_bind (f x) g)
    (isQBSMorphism.Build R X (qbs_prob Z) _ (qbs_bind_morphism f g)).
```

### 2.10 Monad Laws

**File:** `theories/qbs_monad.v`

Since probabilities are classes, the monad laws are equalities. Each is proved with `qbs_prob_eqP` by comparing the probabilities of `sigma_Mx` events, using `qbs_bind_event`, `qbs_return_event` and `qbs_return_integral`:

```
Lemma qbs_bind_returnl X Y (x : X) (f : qbsHomType X (qbs_prob Y)) :
  qbs_bind (qbs_return x) f = f x.

Lemma qbs_bind_returnr X (p : qbs_prob X) : qbs_bind p (qbs_returnQ X) = p.

Lemma qbs_bindA X Y Z (p : qbs_prob X) (f : qbsHomType X (qbs_prob Y))
    (g : qbsHomType Y (qbs_prob Z)) :
  qbs_bind (qbs_bind p f) g = qbs_bind p (qbs_bindQ f g).

Lemma eq_qbs_bind X Y (p : qbs_prob X) (f g : qbsHomType X (qbs_prob Y)) :
  f =1 g -> qbs_bind p f = qbs_bind p g.
```

`eq_qbs_bind` replaces the congruence lemmas of an up-to-equivalence development: bind is well defined on classes by construction, and the only congruence needed is pointwise equality of continuations. The event probability of a probability is also an integral, `qbs_prob_event_integral` (`qbs_prob_event X p U = qbs_integral X p (fun x => (x \in U)%:R%:E)` for `sigma_Mx U`).

### 2.11 Functorial Map

**File:** `theories/qbs_monad.v`

Map is the pushforward of the random element along a bundled morphism, keeping the base measure:

```
Definition monadP_map X Y (f : qbsHomType X Y) (p : qbs_prob X) :
    qbs_prob Y :=
  mkQBSProb (f \o qbs_prob_alpha p) (qbs_prob_mu p)
    (qbs_hom_proof _ (qbs_prob_alpha_random p)).
```

| Name | Statement |
|------|-----------|
| `monadP_map_event` | `qbs_prob_event Y (monadP_map f p) U = qbs_prob_event X p (f @^-1` U)` for `sigma_Mx U` |
| `monadP_map_integral` | `qbs_integral Y (monadP_map f p) h = qbs_integral X p (h \o f)` for `qbs_measurable Y h` |
| `monadP_map_integrable` | `qbs_integrable Y (monadP_map f p) h <-> qbs_integrable X p (h \o f)` for `qbs_measurable Y h` |
| `monadP_map_variance` | `qbs_variance Y (monadP_map f p) h = qbs_variance X p (h \o f)` |
| `monadP_map_morphism` | `monadP_map f` is a morphism `qbs_prob X -> qbs_prob Y` (an HB instance) |
| `sigma_Mx_preimage` | Preimages of `sigma_Mx` sets under morphisms are `sigma_Mx` sets |
| `monadP_map_id` | `monadP_map (qbs_id X) p = p` |
| `monadP_map_comp` | `monadP_map (qbs_comp f g) p = monadP_map g (monadP_map f p)` |
| `monadP_map_bind` | `monadP_map f p = qbs_bind p (qbs_comp f (qbs_returnQ Y))` |
| `qbs_bind_map` | `qbs_bind (monadP_map g p) f = qbs_bind p (qbs_comp g f)` |

### 2.12 Monad Join

**File:** `theories/qbs_monad.v`

```
Definition qbs_join X (pp : qbs_prob (qbs_prob X)) : qbs_prob X :=
  qbs_bind pp (qbs_id (qbs_prob X)).
```

`qbs_join_morphism` shows join is a morphism (with a bundled version `qbs_joinQ X`). The monad coherence laws are equalities:

| Name | Statement |
|------|-----------|
| `qbs_join_return` | `qbs_join (qbs_return p) = p` |
| `qbs_join_map_return` | `qbs_join (monadP_map (qbs_returnQ X) p) = p` |
| `qbs_join_assoc` | `qbs_join (qbs_join P) = qbs_join (monadP_map (qbs_joinQ X) P)` |

### 2.13 Monad Strength

**File:** `theories/qbs_monad.v`

```
Definition qbs_strength W X (wp : W * qbs_prob X) : qbs_prob (prodQ W X) :=
  mkQBSProb (fun r => (wp.1, qbs_prob_alpha wp.2 r))
    (qbs_prob_mu wp.2) (qbs_Mx_pair_cstl wp.1 (qbs_prob_alpha_random wp.2)).
```

| Name | Statement |
|------|-----------|
| `qbs_strength_event` | `qbs_prob_event _ (qbs_strength (w, p)) U = qbs_prob_event X p [set x | U (w, x)]` for `sigma_Mx U` |
| `qbs_strength_integral` | `qbs_integral _ (qbs_strength (w, p)) h = qbs_integral X p (fun x => h (w, x))` for `qbs_measurable _ h` |
| `qbs_strength_morphism` | Strength is a morphism `prodQ W (qbs_prob X) -> qbs_prob (prodQ W X)` (bundled as `qbs_strengthQ`) |
| `qbs_strength_return` | `qbs_strength (w, qbs_return x) = qbs_return (w, x)` |
| `qbs_strength_natural` | Naturality in both arguments |
| `qbs_strength_snd` | `monadP_map (qbs_snd W X) (qbs_strength (w, p)) = p` |
| `qbs_strength_assoc` | `qbs_strength (u, qbs_strength (w, p)) = monadP_map (qbs_assoc U W X) (qbs_strength ((u, w), p))` |
| `qbs_strength_join` | `qbs_strength (w, qbs_join P) = qbs_join (monadP_map (qbs_strengthQ W X) (qbs_strength (w, P)))` |

Here `qbs_assoc U W X : qbsHomType (prodQ (prodQ U W) X) (prodQ U (prodQ W X))` is the associator. With `qbs_strength_snd`, `qbs_strength_assoc`, `qbs_strength_return` and `qbs_strength_join`, the laws of a strong monad are complete.

The proof that strength is a morphism uses `measurable_giry_xsection` (measurability of `r |-> g r (xsection C r)`, a kernel-section lemma) and `sigma_Mx_section`.

### 2.14 Integration as a Morphism and Internal Bind (HKSY Thm. 21)

**File:** `theories/qbs_monad.v`

Integrating a fixed nonnegative measurable function is a morphism from `P(X)` into the QBS of extended reals (HKSY Sec. V-C):

```
Lemma ge0_qbs_integral_morphism X (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, 0 <= h x) ->
  qbs_morphism (X := qbs_prob X) (Y := measQ R (\bar R))
    (fun p => qbs_integral X p h).
```

`ge0_qbs_measurable_integral` states that for a morphism `f : qbsHomType X (qbs_prob Y)` and a nonnegative `qbs_measurable` `h`, the map `x |-> qbs_integral Y (f x) h` is `qbs_measurable`.

Bind is internal: a single morphism `P(X) * (X => P(Y)) -> P(Y)`, obtained from strength and evaluation:

```
Definition qbs_bind_internal X Y :
    qbsHomType (prodQ (qbs_prob X) (expQ X (qbs_prob Y))) (qbs_prob Y) :=
  qbs_bindQ (qbs_comp (qbs_swap _ _) (qbs_strengthQ _ _))
    (qbs_eval X (qbs_prob Y)).

Lemma qbs_bind_internalE X Y (p : qbs_prob X) (f : qbsHomType X (qbs_prob Y)) :
  qbs_bind_internal X Y (p, f) = qbs_bind p f.
```

**Integrals through return and bind** (`theories/qbs_monad_integral.v`, after the end of `Monad_QuasiBorel.thy` in the AFP). Integrability against a Dirac probability is `qbs_integrable_returnP` and `qbs_integrable_return`; integrals, integrability and variance of `qbs_bind p (qbs_comp g (qbs_returnQ Y))` reduce to the pushforward by `monadP_map_bind` and `monadP_map_integral`, `monadP_map_integrable`, `monadP_map_variance` (`qbs_monad.v`). The integral of an integrable function against a bind is the integral of the inner integrals; the signed integral map is a morphism, and so are the parametric integrals:

```
Lemma qbs_integral_bind (h : Y -> \bar R) :
  qbs_measurable Y h -> qbs_integrable Y (qbs_bind p f) h ->
  qbs_integral Y (qbs_bind p f) h =
  qbs_integral X p (fun x => qbs_integral Y (f x) h).

Lemma qbs_integral_morphism X (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_morphism (X := qbs_prob X) (Y := measQ R (\bar R))
    (fun p => qbs_integral X p h).

Lemma qbs_integral_param X Y (L : qbsHomType X (qbs_prob Y))
    (h : prodQ X Y -> \bar R) :
  qbs_measurable (prodQ X Y) h ->
  qbs_morphism (X := X) (Y := measQ R (\bar R))
    (fun x => qbs_integral Y (L x) (fun y => h (x, y))).
```

`qbs_integral_bind_bounded` is the same identity for bounded measurable real functions, and `qbs_integral_param_snd` is the symmetric parametric integral.

### 2.15 Monadic Product and Commutativity (HKSY Prop. 22(2))

**File:** `theories/qbs_monad.v`

The monadic product of `p : qbs_prob X` and `q : qbs_prob Y` is bind followed by strength:

```
Definition qbs_swap X Y : qbsHomType (prodQ X Y) (prodQ Y X) :=
  qbs_pair (qbs_snd X Y) (qbs_fst X Y).

Definition monadP_pair X Y (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  qbs_bind p (qbs_comp (qbs_pair (qbs_id X) (qbs_const X q)) (qbs_strengthQ X Y)).

Lemma monadP_pair_event X Y (p : qbs_prob X) (q : qbs_prob Y) (U : set (prodQ X Y)) :
  sigma_Mx U ->
  qbs_prob_event _ (monadP_pair p q) U =
  \int[qbs_prob_mu p]_r qbs_prob_mu q
    [set t | U (qbs_prob_alpha p r, qbs_prob_alpha q t)].
```

Commutativity says that the order of drawing does not matter. It is proved from Fubini-Tonelli on the seeds, once the set of pairs of seeds landing in `U` is known to be measurable (`measurable_seeds`):

```
Lemma monadP_pair_comm :
  monadP_pair p q = monadP_map (qbs_swap Y X) (monadP_pair q p).

Lemma qbs_bind_comm X Y Z (p : qbs_prob X) (q : qbs_prob Y)
    (f : qbsHomType (prodQ X Y) (qbs_prob Z)) :
  qbs_bind (monadP_pair p q) f =
  qbs_bind (monadP_pair q p) (qbs_comp (qbs_swap Y X) f).
```

### 2.16 Normalisation (HKSY Sec. VI)

**File:** `theories/qbs_normalize.v`

Normalisation `norm : P(X * R) -> P(X) + error` takes a probability on pairs `(x, w)` and reweights by the weight `max(0, w)`. The evidence is the integral of the weight against the probability, and the density of a pair `(alpha, mu)` is the base measure weighted by the weight of `alpha`:

```
Definition qbs_pweight (xw : X * R) : \bar R := (maxr 0 xw.2)%:E.

Definition qbs_evidence p : \bar R := qbs_integral _ p qbs_pweight.

Definition qbs_pdensity (ha : qbs_Mx alpha) (A : set mR) : \bar R :=
  \int[mu]_(r in A) qbs_pweight (alpha r).

Definition qbs_density p : set mR -> \bar R :=
  qbs_pdensity (qbs_prob_mu p) (qbs_prob_alpha_random p).
```

`qbs_pdensity` and `qbs_density p` are registered as measures. The normalised probability uses mathcomp-analysis' `mnormalize`, and `qbs_normalize` fails when the evidence is zero or infinite:

```
Definition qbs_normalize_prob p : qbs_prob X :=
  mkQBSProb (fun r => (qbs_prob_alpha p r).1)
    (mnormalize (qbs_density p) (qbs_prob_mu p))
    (qbs_prob_alpha_fst_random p).

Definition qbs_normalize p : option (qbs_prob X) :=
  if 0 < qbs_evidence p < +oo
  then Some (qbs_normalize_prob p) else None.
```

| Name | Statement |
|------|-----------|
| `qbs_pweight_ge0`, `qbs_measurable_weight` | The weight is nonnegative and `qbs_measurable` |
| `qbs_pdensityT`, `qbs_densityT` | `qbs_pdensity mu ha [set: mR] = \int[mu]_r qbs_pweight (alpha r)` and `qbs_density p [set: mR] = qbs_evidence p` |
| `qbs_evidence_degen` | If the evidence is not in `(0, +oo)` then it is `0` or `+oo` |
| `qbs_prob_alpha_fst_random` | The first component of the alpha of a probability on `X * R` is a random element of `X` |
| `indic_maxr_ge0` | `0 <= \1_U x * maxr 0 w` (helper for the weighted integrals) |
| `qbs_evidence_ge0` | `0 <= qbs_evidence p` |
| `qbs_pdensity_preimage` | `qbs_pdensity mu ha ((fun r => (alpha r).1) @^-1` U) = \int[mu]_r ((\1_U (alpha r).1 : R) * maxr 0 (alpha r).2)%:E` |
| `qbs_normalize_event_degen` | In the degenerate case (evidence zero or infinite), `qbs_prob_event X (qbs_normalize_prob p) U = qbs_prob_event _ p (fst @^-1` U)` for `sigma_Mx U` |
| `qbs_normalize_prob_event_mk` | The events of the normalisation of the class of a pair `(alpha, mu)`: `qbs_prob_event X (qbs_normalize_prob (mkQBSProb alpha mu ha)) U = mnormalize (qbs_pdensity mu ha) mu ((fun r => (alpha r).1) @^-1` U)` for `sigma_Mx U`, degenerate cases included |

Since probabilities are classes, normalisation is well defined without any invariance lemma; `qbs_normalize_prob_event_mk` is the computation rule used to prove that the normaliser is a morphism.

```
Lemma qbs_normalize_event p (U : set X) : sigma_Mx U ->
  0 < qbs_evidence p < +oo ->
  qbs_prob_event X (qbs_normalize_prob p) U =
  qbs_integral _ p (fun xw => ((\1_U xw.1 : R) * maxr 0 xw.2)%:E) *
  (fine (qbs_evidence p))^-1%:E.
```

The normalised probability of `U` is the weighted probability of `U` divided by the evidence.

**The normaliser as a QBS morphism (AFP `norm_qbs_measure_morphism`).** The total version maps into the coproduct `P(X) + 1`, with the unit summand for the degenerate case, and is a morphism:

```
Definition qbs_normalize_sum p : coprodQ (qbs_prob X) (unitQ R) :=
  if (0 < qbs_evidence p) && (qbs_evidence p < +oo)
  then inl (qbs_normalize_prob p) else inr tt.

Lemma qbs_normalize_sumE p : qbs_normalize_sum p =
  if qbs_normalize p is Some q then inl q else inr tt.

Lemma qbs_normalize_morphism :
  qbs_morphism (X := qbs_prob (prodQ X (realQ R)))
    (Y := coprodQ (qbs_prob X) (unitQ R)) qbs_normalize_sum.

Definition qbs_normalizeQ :
    qbsHomType (qbs_prob (prodQ X (realQ R))) (coprodQ (qbs_prob X) (unitQ R)).
```

### 2.17 Product Measures and Fubini

**File:** `theories/pair_qbs_measure.v`

The product of `p : qbs_prob X` and `q : qbs_prob Y` is a probability on `prodQ X Y`. Since the base measure must live on `mR`, the product measure `mu_p \x mu_q` on `mR * mR` is pushed through the retraction `encode_RR_mR` of `standard_borel.v`:

```
Definition qbs_pair_alpha (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r =>
    let uv := @decode_RR_mR R r in
    (qbs_prob_alpha p uv.1, qbs_prob_alpha q uv.2).

Definition qbs_prob_pair (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha p q)
    (qbs_pair_mu_build p q)
    (qbs_pair_alpha_random p q).
```

The probability of a `sigma_Mx` event is the product measure of the set of seed pairs landing in it (`qbs_prob_pair_event`), and `qbs_prob_pair` is *equal* to the monadic product of Section 2.15:

```
Lemma qbs_prob_pairE (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y) :
  monadP_pair p q = qbs_prob_pair p q.
```

The integrals below are stated on `monadP_pair p q` and reduce, through `qbs_prob_pairE`, to integrals against the product measure `mu_p \x mu_q`, where Fubini applies. `qbs_pair_fun p q h` is `(r1, r2) |-> h (alpha_p r1, alpha_q r2)`; the hypothesis `mh` is that `h` is `qbs_measurable (prodQ X Y)`.

| Name | Statement |
|------|-----------|
| `integral_prod_fst` / `integral_prod_snd` | On `mu1 \x mu2`, integrating a function of one coordinate gives the marginal integral |
| `integral_prod_mul` | `\int (h1 r1 * h2 r2) d(mu1 \x mu2) = \int h1 dmu1 * \int h2 dmu2` |
| `monadP_pair_integrable` | `qbs_integrable (prodQ X Y) (monadP_pair p q) h` iff `qbs_pair_fun p q h` is integrable for `mu_p \x mu_q` |
| `monadP_pair_integral` | Integral against `monadP_pair p q` = integral of `qbs_pair_fun p q h` against `mu_p \x mu_q` (if the latter is integrable) |
| `monadP_pair_iterated` | If `h` is `qbs_integrable` against `monadP_pair p q`, the integral is the iterated QBS integral `qbs_integral X p (fun x => qbs_integral Y q (fun y => h (x, y)))` (Fubini) |
| `monadP_pair_mul` | `E[f x * g y] = E[f] * E[g]` against `monadP_pair p q`, for `f`, `g` and `f x * g y` `qbs_integrable` and `f x * g y` `qbs_measurable` |

### 2.18 Independence

**File:** `theories/pair_qbs_measure.v`

Independence of two morphisms out of a common probability space is defined through the monadic product: the joint law equals the product of the marginals.

```
Definition qbs_indep (X Y Z : qbsType R) (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y) : Prop :=
  monadP_map (qbs_pair f g) p = monadP_pair (monadP_map f p) (monadP_map g p).
```

On Borel rectangles this gives the classical product rule:

```
Lemma qbs_indep_rect (Z : qbsType R) (p : qbs_prob Z)
    (f g : qbsHomType Z (realQ R)) (A B : set mR) :
  measurable A -> measurable B -> qbs_indep p f g ->
  qbs_prob_event Z p [set z | A (f z) /\ B (g z)] =
  qbs_prob_event Z p (f @^-1` A) * qbs_prob_event Z p (g @^-1` B).
```

and the product rule for expectations of real-valued test functions:

```
Lemma qbs_integral_indepM (X Y Z : qbsType R) (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y) (phi : X -> R) (psi : Y -> R) :
  qbs_indep p f g ->
  qbs_measurable X (EFin \o phi) -> qbs_measurable Y (EFin \o psi) ->
  qbs_integrable Z p (EFin \o (phi \o f)) ->
  qbs_integrable Z p (EFin \o (psi \o g)) ->
  qbs_integrable Z p (fun z => (phi (f z) * psi (g z))%:E) ->
  qbs_expect Z p (fun z => phi (f z) * psi (g z))%R =
  qbs_expect Z p (phi \o f) * qbs_expect Z p (psi \o g).
```

The proof rewrites the integral along the equality given by independence and applies `monadP_pair_mul`.

### 2.19 Variance of Independent Sums

**File:** `theories/pair_qbs_measure.v`

```
Definition qbs_pair_variance (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R) : \bar R :=
  variance (qbs_prob_mu px \x qbs_prob_mu py)
    (fun rr : mR * mR =>
      (f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2))%R).
```

The main theorem `qbs_pair_varianceD` states `Var(f(x) + g(y)) = Var_px(f) + Var_py(g)` on the product measure, assuming only that `f o alpha_px` and `g o alpha_py` are in `L2` (on the marginals and on the product); the integrability conditions follow from these:

```
  qbs_pair_variance px py f g =
  (qbs_variance X px f + qbs_variance Y py g)%E.
```

It rests on `integral_prod_fst`, `integral_prod_snd` and `integral_prod_mul`.

### 2.20 Comparison with the Giry Monad (HKSY Prop. 22(3), 23)

**File:** `theories/qbs_giry.v`

A QBS probability on `measQ M` induces a probability measure on `M`, its distribution. For `M` standard Borel, the comparison is faithful and preserves bind:

```
Definition qbs_to_giry (p : qbs_prob (measQ R M)) : probability M R :=
  distribution (qbs_prob_mu p) (qbs_prob_alpha_mfunR p).

Lemma qbs_to_giryE (p : qbs_prob (measQ R M)) (A : set M) :
  qbs_to_giry p A = qbs_prob_event (measQ R M) p A.

Lemma qbs_integral_giry (p : qbs_prob (measQ R M)) (f : M -> \bar R) :
  measurable_fun [set: M] f ->
  (qbs_prob_mu p).-integrable [set: mR] (f \o qbs_prob_alpha p) ->
  qbs_integral (measQ R M) p f = \int[qbs_to_giry p]_y f y.

Lemma qbs_to_giry_inj (p1 p2 : qbs_prob (measQ R M)) :
  (forall A, measurable A -> qbs_to_giry p1 A = qbs_to_giry p2 A) ->
  p1 = p2.

Lemma qbs_to_giry_bind d' (M' : measurableType d') (p : qbs_prob (measQ R M))
    (f : qbsHomType (measQ R M) (qbs_prob (measQ R M'))) (A : set M') :
  measurable A ->
  qbs_to_giry (qbs_bind p f : qbs_prob _) A =
  \int[qbs_to_giry p]_x qbs_to_giry (f x : qbs_prob _) A.
```

(`qbs_to_giry_inj` and `qbs_to_giry_bind` are stated for `M` with a `standard_borel_wit`.) Further lemmas, for measurable `A`: `qbs_to_giry_return` (return goes to the Dirac measure), and `qbs_to_giry_map` (map goes to pushforward).

Conversely, a probability measure `P` on `M` yields a QBS probability on `R(M)` from a measurable `encode : M -> R` with measurable left inverse `decode`, and the two constructions are mutually inverse:

```
Definition giry_to_qbs (P : probability M R) : qbs_prob (measQ R M) :=
  mkQBSProb decode (distribution P encode) (measurable_funP decode).

Lemma qbs_to_giryK (P : probability M R) (A : set M) : measurable A ->
  qbs_to_giry (giry_to_qbs P) A = P A.

Lemma giry_to_qbsK (p : qbs_prob (measQ R M)) :
  giry_to_qbs (qbs_to_giry p) = p.
```

### 2.21 Standard Distributions

**File:** `theories/measure_as_qbs_measure.v`

Standard distributions as QBS probabilities (the general embedding of a probability measure on a standard Borel space is `giry_to_qbs`). A probability measure `P` on `mR` is the class of the pair `(idfun, P)`:

```
Let qbs_of_prob (P : probability mR R) : qbs_prob (realQ R) :=
  mkQBSProb (X := realQ R) idfun P (@measurable_id _ mR setT).

Definition qbs_normal_distribution m s : qbs_prob (realQ R) :=
  qbs_of_prob (normal_prob m s).

Definition qbs_bernoulli p : qbs_prob (boolQ R) :=
  mkQBSProb (X := boolQ R) (fun r : mR => r < p)
    (uniform_prob ltr01 : probability mR R) (measurable_ltr p).

Definition qbs_interval_uniform (a b : R) (ab : a < b) : qbs_prob (realQ R) :=
  qbs_of_prob (uniform_prob ab).

Definition qbs_uniform : qbs_prob (realQ R) := qbs_interval_uniform ltr01.
```

The map `mu |-> N(mu, sigma)` is a morphism `realQ -> qbs_prob realQ` (`qbs_normal_morphism`), bundled as `qbs_normalQ sigma`. Integration against the normal distribution is integration against `normal_prob`:

```
Lemma qbs_integral_normal m s (h : R -> \bar R) :
  qbs_measurable (realQ R) h ->
  qbs_integral (realQ R) (qbs_normal_distribution m s) h =
  (\int[normal_prob m s]_x h x)%E.
```

Expectation lemmas:

```
Lemma qbs_expect_bernoulli (p : R) (hp0 : 0 <= p) (hp1 : p <= 1) :
  qbs_expect (boolQ R) (qbs_bernoulli p) (fun b : bool => b%:R) = p%:E.

Lemma qbs_expect_uniform :
  qbs_expect (realQ R) qbs_uniform (fun x => x) = (2%:R^-1)%:E.

Lemma qbs_expect_interval_uniform (a b : R) (ab : a < b) :
  qbs_expect (realQ R) (qbs_interval_uniform ab) (fun x => x) =
  ((a + b) / 2)%:E.

Lemma uniform_prob_lt (p : R) : 0 <= p <= 1 ->
  uniform_prob ltr01 [set r : mR | (r < p)%R] = p%:E.

Lemma qbs_bernoulli_event (p : R) (hp0 : 0 <= p) (hp1 : p <= 1)
    (A : set bool) :
  qbs_prob_event (boolQ R) (qbs_bernoulli p) A = bernoulli_prob p A.

Lemma qbs_expect_normal (mu sigma : R) : sigma != 0 ->
  qbs_expect (realQ R) (qbs_normal_distribution mu sigma)
    (fun x => x) = mu%:E.
```

Its proof uses `integral_normal_mean` (`normal_centred.v`), the mean of the normal law:

```
Lemma integral_normal_mean m s : s != 0 ->
  \int[normal_prob m s]_x x%:E = m%:E.
```

The analytic facts it needs are proved in `theories/normal_centred.v`:

```coq
Lemma integrable_normal_centred (m s : R) : s != 0 ->
  (@lebesgue_measure R).-integrable setT
    (fun x : R => ((x - m) * normal_pdf m s x)%:E).
Lemma integral_normal_centred (m s : R) : s != 0 ->
  (\int[@lebesgue_measure R]_x ((x - m) * normal_pdf m s x)%:E = 0)%E.
Lemma ge0_integral_normal_prob (m s : R) (f : R -> \bar R) :
  (forall x, (0 <= f x)%E) -> measurable_fun setT f ->
  (\int[normal_prob m s]_x f x =
   \int[mu]_x (f x * (normal_pdf m s x)%:E))%E.
Lemma normal_prob_abs_lty (m s : R) : s != 0 ->
  (\int[normal_prob m s]_x `|x%:E| < +oo)%E.
```

On each half-line around `m`, the integral of `(x - m) * pdf` is `±s^2 * normal_peak s`, computed by the FTC with antiderivative `-s^2 * normal_pdf m s` (`ge0_continuous_FTC2y`, and `ge0_integration_by_substitutionNy` for the left half-line). `ge0_integral_normal_prob` is the nonnegative version of `integral_normal_prob`, obtained from the Radon–Nikodym change of variables.

### 2.22 Bayesian Linear Regression

**File:** `theories/showcase/bayesian_regression.v` (474 lines, 29 Qed)

Following HKSY Sec. VI and the Isabelle AFP development (Bayesian_Linear_Regression.thy) by Hirata, Minamide, Sato, the prior is a probability on the *function space* `R => R`.

**Model:** `y = s * x + b + noise`, noise ~ N(0, 1/2); the parameters `s, b` are iid N(0, 3). Data: (1, 2.5), (2, 3.8), (3, 4.5), (4, 6.2), (5, 8.0).

**Prior.** The parameter prior is a monadic product, which is mapped to functions through the curried line `lin`:

```
Definition nu : qbs_prob RQ := qbs_normal_distribution 0 3.
Definition prior2 : qbs_prob W := monadP_pair nu nu.

Definition lin : qbsHomType W F := qbs_curry_morph lin_uncurried.
Lemma linE (s b r : R) : lin (s, b) r = s * r + b.

Definition prior : qbs_prob F := monadP_map lin prior2.
```

(here `W := prodQ RQ RQ` and `F := expQ RQ RQ`).

**Program.** The likelihood `obs_fun f` is the product of the five Gaussian densities of the data at `f 1, ..., f 5`; it is a QBS morphism `obs : qbsHomType F RQ`. The program is the normalisation of the prior weighted by the likelihood:

```
Definition wprior : qbs_prob (prodQ F RQ) :=
  monadP_map (qbs_pair (qbs_id F) obs) prior.
Definition program : option (qbs_prob F) := qbs_normalize wprior.
```

**Posterior in closed form.** Completing the square gives explicit parameters (`post_s_mean`, `post_s_var`, `post_b_mean s`, `post_b_var`) and a constant `evidence_const`:

```
Definition evidence_const : R :=
  4 * Num.sqrt 2 / (pi ^+ 2 * Num.sqrt (29 * 2309 * pi)) *
  expR (- (11 * 11 * (138 * 100 + 41) / (25 * 29 * 2309))).

Definition posterior2 : qbs_prob W :=
  qbs_bind
    (qbs_normal_distribution post_s_mean (Num.sqrt post_s_var) : qbs_prob _)
    (qbs_comp (qbs_pair (qbs_id RQ)
      (qbs_comp post_b_meanQ (qbs_normalQ (Num.sqrt post_b_var))))
      (qbs_strengthQ RQ RQ)).
Definition posterior : qbs_prob F := monadP_map lin posterior2.
```

| Name | Statement |
|------|-----------|
| `obs_prior_factor` | Prior density times likelihood is `evidence_const` times the posterior density (completing the square) |
| `prior2_integral` / `posterior2_integral` | Integrals against `prior2` / `posterior2` are iterated integrals against the Gaussians |
| `factor_integral` | `\int[N(0,3)]_s \int[N(0,3)]_b (h (s, b) * obs2 s b) = evidence_const * \int[post]_s \int[post(s)]_b h (s, b)` for `h` with values in [0, 1] |
| `wprior_evidence` | `qbs_evidence wprior = evidence_const%:E` (closed-form evidence) |
| `program_posterior` | **Main theorem** |

```
Lemma wprior_evidence : qbs_evidence wprior = evidence_const%:E.

Theorem program_posterior : program = Some posterior.
```

The theorem says that the program succeeds (the evidence is positive and finite, as it equals `evidence_const`), and that the resulting QBS probability on functions *is* the explicit Gaussian posterior: an equality, proved with `qbs_prob_eqP` by comparing the probabilities of `sigma_Mx` events.

---


## Part III: Standard Borel Spaces (R × R as a Retract of R)

Source file: `theories/standard_borel.v` (1,031 lines, 59 Qed).

This file constructs a measurable retraction of R × R onto R: a measurable `encode_RR : R × R -> R` with a measurable left inverse `decode_RR`. This is exactly what the characterisation of standard Borel spaces as retracts of R (HKSY Prop. 5) needs, and it shows that the product of standard Borel spaces is standard Borel. `encode_RR` is not surjective (binary expansions ending in infinitely many 1s are missed), so this is a retraction, not an isomorphism. The construction composes three layers: (1) a bijection R ↔ (0,1) via arctangent, (2) a map (0,1)² -> (0,1) by binary digit interleaving with a left inverse, and (3) the composed encode/decode pair. The retraction is used by `qbs_monad.v` (gluing of random elements of P(X)) and `pair_qbs_measure.v` (product probability pairs), and by `prod_standard_borel` in `measure_qbs_adjunction.v`.

### 3.1 Standard Borel: R to (0,1) Bijection

```
Definition atan01 (x : R) : R := atan x / pi + 1 / 2.
Definition tan01 (y : R) : R := tan (pi * (y - 1 / 2)).
```

| Name | Statement |
|------|-----------|
| `atan01_gt0` | `0 < atan01 x` for all `x` |
| `atan01_lt1` | `atan01 x < 1` for all `x` |
| `atan01K` | `cancel atan01 tan01` (tan01 is a left inverse of atan01, unconditional) |
| `tan01K` | `{in `](0,1)[, cancel tan01 atan01}` (atan01 is a left inverse of tan01 on (0,1)) |
| `measurable_atan01` | `measurable_fun setT atan01` |
| `measurable_tan01_setT` | `measurable_fun setT tan01` (measurable on all of R) |

The proofs use `atan_gtNpi2`, `atan_ltpi2`, `atanK`, `tanK`, `cos_gt0_pihalf`, and `continuous_atan`/`continuous_tan` from math-comp analysis.

### 3.2 Binary Digit Machinery

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
| `bin_step`, `bin_rem`, `bin_remS` | The doubling step `y |-> if 1/2 <= y then 2y - 1 else 2y`, its `n`-th iterate `bin_rem x n`, and the unfolding `bin_rem x n.+1 = bin_step (bin_rem x n)` |
| `bin_digit_rem`, `bin_rem_itv` | `bin_digit x n = (1/2 <= bin_rem x n)`; `0 <= x < 1 -> 0 <= bin_rem x n < 1` |
| `measurable_bin_step`, `measurable_bin_rem`, `measurable_bin_sum` | Measurability of the step, of `x |-> bin_rem x n`, and of `bin_sum` of a family of measurable digit functions |

**Reconstruction theorem:**

```
Lemma bin_digits_reconstruction (x : R) :
  0 <= x < 1 -> bin_sum (bin_digit x) = x.
```

The proof proceeds by showing that `x - bin_partial_sum (bin_digit x) n = rem(n) * (1/2)^n` where `rem(n)` is bounded in `[0,1)`, so the error converges to 0 via the squeeze lemma and `cvg_geometric`.

**Uniqueness of binary expansions:**

| Name | Statement |
|------|-----------|
| `no_trailing_ones` | `forall N, exists n, N <= n /\ d n = false` |
| `bin_digits_no_trailing_ones` | `0 <= x < 1 -> no_trailing_ones (bin_digit x)` |
| `bin_sum_no_trailing_lt1` | `no_trailing_ones d -> bin_sum d < 1` |
| `bin_sum_shift` | `bin_sum d = d(0) * 1/2 + bin_sum (d \o S) * 1/2` |
| `no_trailing_ones_shift` | Shifting preserves no-trailing-ones |
| `bin_digits_bin_sum` | `no_trailing_ones d -> bin_digit (bin_sum d) =1 d` |

The `bin_digits_no_trailing_ones` proof is by contradiction: if all digits from position N onward are 1, the remainders satisfy `1 - rem(N+k) = (1 - rem(N)) * 2^k`, which eventually exceeds 1, contradicting `rem >= 0`.

### 3.3 Digit Interleaving and Pairing

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
  bin_sum (interleave (bin_digit xy.1) (bin_digit xy.2)).

Definition unit_to_pair (r : R) : R * R :=
  (bin_sum (deinterleave_even (bin_digit r)),
   bin_sum (deinterleave_odd (bin_digit r))).
```

### 3.4 Round-Trip Properties

Two round-trip lemmas are established:

**Direction 1 (UNCONDITIONAL -- needed for `standard_borel_wit`):**

```
Lemma pair_to_unitK (xy : R * R) :
  0 <= xy.1 < 1 -> 0 <= xy.2 < 1 ->
  unit_to_pair (pair_to_unit xy) = xy.
```

This uses `bin_digits_bin_sum` (with `interleave_no_trailing_ones` providing the no-trailing-ones hypothesis) and then `deinterleave_interleaveK_even/odd` to recover the original digit sequences, followed by `bin_digits_reconstruction`.

**Direction 2 (conditional):**

```
Lemma unit_to_pairK (r : R) :
  0 <= r < 1 ->
  no_trailing_ones (deinterleave_even (bin_digit r)) ->
  no_trailing_ones (deinterleave_odd (bin_digit r)) ->
  pair_to_unit (unit_to_pair r) = r.
```

This direction requires no-trailing-ones on the deinterleaved subsequences, which does NOT follow from no-trailing-ones on the full sequence. However, this direction is not needed for `standard_borel_wit`, which only requires `g(f(x)) = x`. The set of reals where the extra hypotheses fail is a subset of the dyadic rationals (countable, hence measure-zero).

Additional helper lemmas: `bin_sum_ext`, `bin_sum_has_one_gt0`, `atan01_has_true_digit`, `atan01_ge0`, `atan01_in_01`, `pair_to_unit_atan01_gt0`, `pair_to_unit_atan01_lt1`, `pair_to_unit_atan01_in_itv`.

### 3.5 Measurability of the Bijection Components

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

**Full-domain measurability of tan01:**

```
Lemma measurable_tan01_setT : measurable_fun [set: R] (@tan01 R).
```

The proof factors `tan01 = sin * cos^{-1}` on `pi*(y - 1/2)`, proves `sin` and `cos` are measurable via continuity, and handles `cos^{-1}` by approximating `x^{-1}` with `x/(x^2 + 1/(n+1))` (which is continuous) and applying `measurable_fun_cvg`. The convergence `inv_cvg_approx` is proved using `cvgV` and `cvg_harmonic`.

### 3.6 Composed Retraction R x R to R

```
Definition encode_RR (xy : R * R) : R :=
  tan01 (pair_to_unit (atan01 xy.1, atan01 xy.2)).

Definition decode_RR (r : R) : R * R :=
  let uv := unit_to_pair (atan01 r) in (tan01 uv.1, tan01 uv.2).
```

**Main round-trip theorems:**

```
Theorem encode_RRK (xy : R * R) :
  decode_RR (encode_RR xy) = xy.
```

The proof chains: (1) `tan01K` to recover `pair_to_unit(atan01 x, atan01 y)` from `atan01(tan01(...))`, (2) `pair_to_unitK` to recover `(atan01 x, atan01 y)` from `unit_to_pair(pair_to_unit(...))`, and (3) `atan01K` twice to recover `(x, y)`.

```
Theorem decode_RRK (r : R)
  (hnt_even : no_trailing_ones (deinterleave_even (bin_digit (atan01 r))))
  (hnt_odd : no_trailing_ones (deinterleave_odd (bin_digit (atan01 r))))
  (hu1_pos : 0 < (unit_to_pair (atan01 r)).1)
  (hu2_pos : 0 < (unit_to_pair (atan01 r)).2) :
  encode_RR (decode_RR r) = r.
```

This direction requires extra hypotheses (see Section 3.4) but is not needed for `standard_borel_wit`.

**Measurability:**

| Name | Statement |
|------|-----------|
| `measurable_encode_RR` | `measurable_fun setT encode_RR` |
| `measurable_decode_RR` | `measurable_fun setT decode_RR` |

The `measurable_encode_RR` proof composes `measurable_atan01` (on each component), `measurable_pair_to_unit`, and `measurable_tan01_setT`. The `measurable_decode_RR` proof also uses `measurable_tan01_setT`, `measurable_unit_to_pair_fst/snd`, and `measurable_atan01`.

### 3.7 The Punchline: pair_standard_borel

```
Lemma pair_standard_borel :
  exists (f : R * R -> R) (g : R -> R * R),
    measurable_fun setT f /\ measurable_fun setT g /\
    (forall xy, g (f xy) = xy).
Proof.
exists encode_RR, decode_RR.
split; first exact: measurable_encode_RR.
split; first exact: measurable_decode_RR.
exact: encode_RRK.
Qed.
```

This witnesses that `R x R` is standard Borel in the sense of `standard_borel_wit` (defined in `measure_qbs_adjunction.v`, Section 1.11), which only requires a measurable retraction `g(f(x)) = x` (not the reverse). It is packaged as `prod_standard_borel` there, and combined with `measQ_full` it shows the R functor is full on products of standard Borel spaces. For use with product measures, the file also provides `encode_RR_mR`, `decode_RR_mR`, `encode_RR_mRK` (the same maps on `measurableTypeR R`) and relies on `measurable_aux.v` (`measurable_truncn`, used to decode the index when gluing probabilities, together with `measurable_invr` and `measurable_fun_nat_discrete`, now live there).

---

## Part IV: Architecture and Project Status

### 4.1 File Dependency Graph

```
measurable_aux.v (standalone measurability lemmas, no QBS imports)
  |
  +--> standard_borel.v (standalone analysis)
  |
  +--> quasi_borel.v
          |
          +--> coproduct_qbs.v
          |
          +--> measure_qbs_adjunction.v  (also imports standard_borel.v)
          |       |
          |       +--> qbs_giry.v  (also imports probability_qbs.v, qbs_monad.v)
          |
          +--> probability_qbs.v
                  |
                  +--> qbs_monad.v  (also imports standard_borel.v)
                          |
                          +--> qbs_monad_integral.v
                          |
                          +--> qbs_normalize.v  (also imports coproduct_qbs.v)
                          |
                                          +--> pair_qbs_measure.v  (also imports standard_borel.v)
                          |
                          +--> measure_as_qbs_measure.v
                                  |
                                  +--> showcase/bayesian_regression.v
                                       (also imports qbs_normalize.v)

(`measurable_aux.v` is also imported directly by `probability_qbs.v`,
`qbs_monad.v`, `qbs_normalize.v`, `measure_as_qbs_measure.v` and
`measure_qbs_adjunction.v`.)
```

### 4.2 Design Decisions

**Instances plus named definitions.** Concrete QBS constructions (`prodQ`, `expQ`, `unitQ`, `coprodQ`, `sigmaQ`, `piQ`, `qbs_prob`, etc.) are declared with `HB.instance` on their (non-canonical) carrier types, and then exposed through a named definition of type `qbsType R`. Morphisms are bundled in the HB structure `qbsHomType`, which makes category laws and the universal properties statable as equalities (`qbs_homeqP`).

**Shared-alpha probability monad.** The random elements of `P(X)` are the maps `r |-> [alpha, g r]` with a single random element `alpha` and a measurable family `g` of Giry probabilities, as in HKSY. Bind takes a bundled morphism `X -> P(Y)` and is total, defined from the Giry bind of mathcomp-analysis; no diagonal-randomness side condition is needed.

**L as a measurableType.** The functor L is realised as `qbs_meas X`, a `measurableType` with the sigma-algebra `sigma_Mx X`. The adjunction L -| R is then a lemma about `measurable_fun` (`qbs_morphism_measurableP`), and laws of QBS probabilities are transported to genuine probability measures through `qbs_law`.

**Probabilities are a quotient.** `qbs_prob X` is the quotient (`{eq_quot ...}`, mathcomp's `generic_quotient`, as the a.e. classes of `hoelder.v`) of the representatives `qbs_preprob X`, pairs `(alpha, mu)`, by `preprob_equiv`: the pairs agree on the measure of `sigma_Mx` sets. Return, bind, map and strength are defined on a representative, and the monad, strength and commutativity laws are equalities, proved with `qbs_prob_eqP` from computation lemmas on events (`qbs_return_event`, `qbs_bind_event`, `monadP_map_event`, `qbs_strength_event`). Integrals of `qbs_measurable` functions do not depend on the representative (`integral_sigma_Mx`), and `qbs_prob_event_mk`, `qbs_integral_mk`, `qbs_integrable_mk`, `qbs_variance_mk` compute on the class of a pair `mkQBSProb alpha mu ha`. No congruence lemmas are needed.

**Product measure via the retraction R x R -> R.** `qbs_pair_mu_build` pushes the product measure `mu_p \x mu_q` through `encode_RR_mR` from `standard_borel.v`. Integrals against the resulting product reduce to integrals against `mu_p \x mu_q` (`monadP_pair_integral`), where Fubini applies. The same retraction decodes the selector in the glue axiom of `P(X)` and the product-closure of standard Borel spaces.

**Universe management.** The `\o` composition operator inside `[set ...]` comprehensions was replaced with explicit lambdas in a few places to avoid universe inconsistencies between `algebra_tactics.ring` and the QBS type hierarchy.

### 4.3 Comparison with Isabelle AFP

| Feature | Isabelle AFP | This development |
|---------|-------------|------------------|
| QBS axioms | Locale-based | HB mixin/structure |
| Probability monad | `quotient_type` of triples `(X, alpha, mu)` (HOL has no dependent types) | `qbs_prob X` is the quotient of the pairs `(alpha, mu)` (representatives `qbs_preprob X`) by `preprob_equiv`; the space `X` is the type parameter; laws are equalities |
| Cartesian closure | Present | `qbs_curryK`, `qbs_uncurryK`, `qbs_curry_morph_uniq` |
| L -| R adjunction | Present | `qbs_morphism_measurableP` (L as a `measurableType`) |
| Countable coproducts / lists | Present | `sigmaQ` / `sigma_case` / `listQ`, `qbs_cons`, `list_rec`, `qbs_morphism_list_rec` (AFP `rec_list_morphism`) |
| Lattice of QBS structures | Present | `qbs_sup`, `qbs_inf`, `qbs_top`, `qbs_bot`, `emptyQ` (initial) |
| Order adjunction (`rl_order_adjunction`) | Present | `sigma_of_Mx_of` (Galois connection `sigma_of` / `Mx_of`) |
| Concrete morphisms | Present | `qbs_negb/andb/orb/implb`, `qbs_ltr`, `qbs_ltn`, `qbs_case`, `qbs_arg_swap`, `qbs_exp_compose`, `natQ_morphism`, `boolQ_morphism` |
| Standard Borel R≅R×R | Not formalized | `pair_standard_borel` (retraction, via atan + digit interleaving) |
| Bayesian regression | Function-space prior | Function-space prior `prior : qbs_prob (expQ RQ RQ)`, closed-form posterior |
| Program correctness | `program_result` (Inl) | `program_posterior` (`program = Some posterior`) |
| Evidence | Explicit closed form `evidence_const` | `wprior_evidence` |
| Monad strength, join | Not formalized | `qbs_strength*` (snd, assoc, return, join), `qbs_join*` lemmas |
| Internal bind (HKSY Thm. 21) | Not formalized | `qbs_bind_internal` |
| Commutativity (HKSY Prop. 22(2)) | Not formalized | `monadP_pair_comm`, `qbs_bind_comm` |
| Fubini on QBS | Not formalized | `monadP_pair_iterated` + marginals |
| Independence | Not formalized | `qbs_indep`, `qbs_indep_rect`, `qbs_integral_indepM` |
| QBS↔Giry bridge | Not formalized | `qbs_to_giry` / `giry_to_qbs`, `qbs_to_giry_bind` |
| Normalizer | Not formalized | `qbs_normalize` + `qbs_normalize_event`, `qbs_normalize_prob_event_mk`, `qbs_normalize_morphism` (AFP `norm_qbs_measure_morphism`) |
| Integral arithmetic | Not formalized | `qbs_integrable`, `qbs_integrableP`, `qbs_integral_le`, `qbs_integral_bind` (`qbs_monad_integral.v`) |
| Probability ineq. | Not formalized | `qbs_markov` + `qbs_chebyshev` |
| Variance | Not formalized | `qbs_varianceE` + `qbs_varianceZ`, `qbs_variance_affine`, `qbs_variance_mk` |
| E[distributions] | Not formalized | `qbs_expect_normal` (from `integral_normal_mean`) / `bernoulli` / `uniform`, `qbs_expect_interval_uniform` (Uniform(a,b)), `qbs_bernoulli_event` |
| Standard Borel inst. | Not formalized | R, nat, bool, prod, ereal |
| Lines | ~5000 | 6,370 |

### 4.4 Statistics

| File | Lines | Proofs |
|------|------:|-------:|
| `measurable_aux.v` | 81 | 3 |
| `quasi_borel.v` | 887 | 62 |
| `measure_qbs_adjunction.v` | 311 | 19 |
| `coproduct_qbs.v` | 721 | 44 |
| `probability_qbs.v` | 594 | 42 |
| `qbs_monad.v` | 715 | 61 |
| `qbs_monad_integral.v` | 171 | 8 |
| `qbs_normalize.v` | 279 | 18 |
| `pair_qbs_measure.v` | 389 | 20 |
| `qbs_giry.v` | 135 | 8 |
| `normal_centred.v` | 300 | 16 |
| `measure_as_qbs_measure.v` | 282 | 13 |
| `standard_borel.v` | 1,031 | 59 |
| `showcase/bayesian_regression.v` | 474 | 29 |
| **Total** | **6,370** | **402** |

The 402 proofs are 397 `Qed` and 5 `Defined` (the standard Borel witnesses in `measure_qbs_adjunction.v`). **0 Admitted**, 0 custom axioms.

### 4.5 Honest Limitations

The formalization is honest about its scope. These limitations are
documented in the source files and in this report, not hidden:

1. **`monadP_pair_iterated` is iterated integration on a
   specific product measure**, not full Fubini. It works for the
   QBS product measure constructed via the retraction R×R -> R, not for
   arbitrary product measures.

2. **`monadP_pair_mul` is product-measure
   factorization, not statistical independence.** It states
   `E[f(x) g(y)] = E[f]E[g]` for the monadic product of two
   probabilities, which is a tautology of products. The genuine
   independence factorization is `qbs_integral_indepM`,
   which uses the `qbs_indep` predicate (the joint law
   `monadP_map (qbs_pair f g) p` is the product `monadP_pair` of the
   marginals) and recovers
   `E_p[phi (f z) * psi (g z)] = E_p[phi (f z)] * E_p[psi (g z)]`
   from independence of `f` and `g`.

3. **`standard_borel_wit` is a retract-of-R witness**, not the classical
   Polish-space characterization. It matches HKSY Prop. 5, but it is
   packaged as data (`sb_encode`, `sb_decode`, `sb_encodeK`) rather than
   as a predicate.

4. **`qbs_normalize` returns `option`** and returns `None` when
   the evidence is zero or infinite. Programs using normalization
   must check or prove the success case; `bayesian_regression.v` does
   so in `program_posterior` (the evidence is the explicit constant `evidence_const`).

5. **`qbs_to_giry_inj` and `qbs_to_giry_bind` need a `standard_borel_wit`**
   for the underlying measurable space, as in HKSY Prop. 23.

### 4.6 Remaining Work

1. **De Finetti theorem.** The de Finetti theorem of HKSY (exchangeable sequences as mixtures of i.i.d. sequences) is not formalised.

2. **Standard Borel closure under countable products.** Extending `pair_standard_borel` to R ~ R^N via Hilbert-cube encoding.

3. **s-Finite kernels.** Integration with the s-finite kernel framework from math-comp analysis (Affeldt, Cohen, Saito).

4. **Standard Borel full round-trip.** The reverse `decode_RRK` is conditional on `no_trailing_ones` of the deinterleaved digit sequences. Formalizing that the exception set has measure zero would complete it.
