# Quasi-Borel Spaces in Rocq: A Formalization Report

**Project:** QBS -- Quasi-Borel Spaces in Rocq
**Repository:** https://github.com/LLM4Rocq/mathcomp-qbs
**Date:** 2026-10-23
**Status:** 322 proofs (317 Qed + 5 Defined), **0 Admitted**, 0 custom axioms
**Lines of Rocq:** 6,226 across 13 files

> **Note**: The higher-order PPL development (`ppl_qbs.v`,
> `ppl_kernel.v`, `showcase/ppl_examples.v`) is on the `ppl`
> branch as future work. This report covers only the QBS
> foundations and the Bayesian regression showcase, as ported
> to MathComp 2.6 (branch `port-mathcomp-2.6`).
**Compatibility:** Rocq 9.2, Math-comp 2.6, Math-comp analysis 1.18

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

**Dependencies:** Rocq 9.2, Math-comp 2.6, Math-comp analysis 1.18, Hierarchy Builder 1.10, Math-comp algebra-tactics (master branch; there is no release for Math-comp 2.6 yet) for `ring`/`field`

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
  - [2.1 QBS Probability Triple](#21-qbs-probability-triple)
  - [2.2 Equivalence of Probability Triples](#22-equivalence-of-probability-triples)
  - [2.3 Integration](#23-integration)
  - [2.4 The Law of a QBS Probability (HKSY eq. (3))](#24-the-law-of-a-qbs-probability-hksy-eq-3)
  - [2.5 Expectation, Events and Variance](#25-expectation-events-and-variance)
  - [2.6 Integrability, Integral Arithmetic and Probability Inequalities](#26-integrability-integral-arithmetic-and-probability-inequalities)
  - [2.7 The Probability Monad P(X)](#27-the-probability-monad-px)
  - [2.8 Return](#28-return)
  - [2.9 Bind](#29-bind)
  - [2.10 Monad Laws](#210-monad-laws)
  - [2.11 Functorial Map](#211-functorial-map)
  - [2.12 Congruence](#212-congruence)
  - [2.13 Monad Join](#213-monad-join)
  - [2.14 Monad Strength](#214-monad-strength)
  - [2.15 Integration as a Morphism and Internal Bind (HKSY Thm. 21)](#215-integration-as-a-morphism-and-internal-bind-hksy-thm-21)
  - [2.16 Monadic Product and Commutativity (HKSY Prop. 22(2))](#216-monadic-product-and-commutativity-hksy-prop-222)
  - [2.17 Normalisation (HKSY Sec. VI)](#217-normalisation-hksy-sec-vi)
  - [2.18 Quotient Type for QBS Probability](#218-quotient-type-for-qbs-probability)
  - [2.19 Product Measures and Fubini](#219-product-measures-and-fubini)
  - [2.20 Independence](#220-independence)
  - [2.21 Variance of Independent Sums](#221-variance-of-independent-sums)
  - [2.22 Comparison with the Giry Monad (HKSY Prop. 22(3), 23)](#222-comparison-with-the-giry-monad-hksy-prop-223-23)
  - [2.23 Standard Distributions](#223-standard-distributions)
  - [2.24 Bayesian Linear Regression](#224-bayesian-linear-regression)
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

Source files: `theories/quasi_borel.v` (821 lines, 49 Qed), `theories/measure_qbs_adjunction.v` (332 lines, 9 Qed + 5 Defined), `theories/coproduct_qbs.v` (464 lines, 19 Qed).

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

Since the axioms take bundled measurable functions, two convenience wrappers accept bare `measurable_fun setT` proofs: `qbs_Mx_compT` and `qbs_Mx_glueT`. A third, `measurable_glue`, states that a measurable selector glued with a measurable family is measurable.

**NB comments on HB.pack:** Concrete QBS constructions (products, exponentials, coproducts, etc.) are given as `HB.instance` on the carrier type and wrapped in a named definition (`prodQ`, `expQ`, ...), because the carrier types are non-canonical (e.g., `X * Y`, `qbsHomType X Y`, `X + Y`). Where the instance would be ambiguous (e.g. `generating_qbs`, which needs a generator set), it is declared on an alias type.

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
| `qbs_comp1` / `qbs_1comp` | Identity is a left / right unit for `qbs_comp` (stated as `qbs_comp (qbs_id X) f = f` and `qbs_comp f (qbs_id Y) = f`) |
| `qbs_compA` | `qbs_comp f (qbs_comp g h) = qbs_comp (qbs_comp f g) h` |

These establish that QBS spaces form a category, with equalities between bundled morphisms (not just pointwise equalities).

### 1.4 The R Functor

**File:** `theories/quasi_borel.v`; `theories/measure_qbs_adjunction.v`

The R functor sends a measurable type to its QBS of measurable functions. Its random elements are the measurable functions `mR -> M`:

```
Section R_qbs_instance.
Context d (M : measurableType d).
Let Mx := [set f : mR -> M | measurable_fun setT f].
...
HB.instance Definition _ := @isQBS.Build R M Mx ax1 ax2 ax3.
Definition R_qbs : qbsType R := M.
End R_qbs_instance.
```

**Concrete instances:**

```
Definition realQ : qbsType R := R_qbs mR.
Definition natQ : qbsType R := R_qbs nat.
Definition boolQ : qbsType R := R_qbs bool.
```

In `measure_qbs_adjunction.v`, R is shown to be functorial and product-preserving:

```
Lemma R_qbs_morphism d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (f : {mfun M1 >-> M2}) :
  qbs_morphism (X := R_qbs R M1) (Y := R_qbs R M2) f.

Lemma R_preserves_prod d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (alpha : mR -> M1 * M2) :
  qbs_Mx (s := R_qbs R (M1 * M2)%type) alpha <->
  qbs_Mx (s := prodQ (R_qbs R M1) (R_qbs R M2)) alpha.
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

The structural morphisms are bundled: `qbs_fst X Y : qbsHomType (prodQ X Y) X`, `qbs_snd X Y`, and the pairing `qbs_pair f g : qbsHomType W (prodQ X Y)` of `f : qbsHomType W X` and `g : qbsHomType W Y`. The lemma `prodQ_const_random` states that a constant paired with a random element is random in the product.

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

The lemmas `sigma_Mx_setT`, `sigma_Mx_set0`, `sigma_Mx_setC` and `sigma_Mx_bigcup` show that `sigma_Mx X` is a sigma-algebra. This is packaged as a `measurableType`, the functor L of HKSY Prop. 15:

```
Definition qbs_meas : Type := X.
HB.instance Definition _ :=
  @isMeasurable.Build (sigma_display (@sigma_Mx X)) qbs_meas (@sigma_Mx X)
    (@sigma_Mx_set0 X) (@sigma_Mx_setC X) (@sigma_Mx_bigcup X).
Lemma qbs_measE (U : set qbs_meas) : measurable U = sigma_Mx (X := X) U.
```

so that the standard mathcomp-analysis machinery (measures, integrals, `measurable_fun`) applies directly to `qbs_meas X`. Random elements are measurable into `L X` (the unit of the adjunction):

```
Lemma qbs_Mx_measurable (a : mR -> X) :
  qbs_Mx a -> measurable_fun [set: mR] (a : mR -> qbs_meas).
```

### 1.10 The L -| R Adjunction (HKSY Prop. 15)

**File:** `theories/quasi_borel.v`; `theories/measure_qbs_adjunction.v`

The adjunction L -| R is the statement that QBS morphisms into `R_qbs M` are exactly the measurable maps out of `L X`:

```
Lemma qbs_morphism_measurableP d (M : measurableType d) (f : X -> M) :
  qbs_morphism (X := X) (Y := R_qbs M) f <->
  measurable_fun [set: qbs_meas] (f : qbs_meas -> M).
```

This is HKSY Prop. 15(1). `measure_qbs_adjunction.v` adds the action of L on morphisms and the counit:

```
Lemma qbs_morphism_measurable (X Y : qbsType R) (f : X -> Y) :
  qbs_morphism f ->
  measurable_fun [set: qbs_meas X] (f : qbs_meas X -> qbs_meas Y).

Lemma sigma_Mx_measurable d (M : measurableType d) (U : set M) :
  measurable U -> sigma_Mx (X := R_qbs R M) U.

Lemma adjunction_counit d (M : measurableType d) :
  measurable_fun [set: qbs_meas (R_qbs R M)] (idfun : _ -> M).
```

### 1.11 Standard Borel Spaces (HKSY Prop. 15(2))

**File:** `theories/measure_qbs_adjunction.v`

A measurable space is standard Borel here if it is a measurable retract of R. This is witnessed by data (`encode`, `decode`, and a retraction proof):

```
Record standard_borel_wit d
    (M : measurableType d) := StandardBorelWit {
  sb_encode : {mfun M >-> mR} ;
  sb_decode : {mfun mR >-> M} ;
  sb_retractK : cancel sb_encode sb_decode
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

`prod_standard_borel` uses `encode_RR`/`decode_RR` from `standard_borel.v` (Part III). The extended-real QBS is `erealQ := R_qbs R (\bar R)`.

R is full on standard Borel domains, and on standard Borel spaces the sigma-algebra induced by the random elements is the original one:

```
Lemma R_qbs_full d1 d2 (M1 : measurableType d1) (M2 : measurableType d2)
    (sb : standard_borel_wit M1) (f : M1 -> M2) :
  qbs_morphism (X := R_qbs R M1) (Y := R_qbs R M2) f ->
  measurable_fun setT f.

Lemma sigma_Mx_standard_borel d
    (M : measurableType d) (sb : standard_borel_wit M) :
  forall U : set M, sigma_Mx (X := R_qbs R M) U <-> measurable U.
```

### 1.12 Comparison Morphisms

**File:** `theories/quasi_borel.v`

Measurable operations on R are QBS morphisms via `R_qbs`. Addition and multiplication are bundled:

```
Definition qbs_add : qbsHomType (prodQ realQ realQ) realQ
Definition qbs_mul : qbsHomType (prodQ realQ realQ) realQ
```

### 1.13 Subspaces

**File:** `theories/quasi_borel.v`

For a predicate `P : set X`, `sub_qbs X P` has carrier `{x : X | P x}` and the random elements `alpha` with `proj1_sig \o alpha` random in `X`.

### 1.14 Generating QBS

**File:** `theories/quasi_borel.v`

Given a set `G` of functions `mR -> T`, `generating_qbs G` is the smallest QBS containing `G`, defined as the inductive closure under the three axioms:

```
Inductive generating_Mx (T : Type) (G : set (mR -> T))
  : (mR -> T) -> Prop :=
  | gen_base : forall alpha, G alpha -> generating_Mx G alpha
  | gen_comp : forall alpha (f : {mfun mR >-> mR}),
      generating_Mx G alpha ->
      generating_Mx G (alpha \o f)
  | gen_const : forall x : T, generating_Mx G (fun _ => x)
  | gen_glue : forall (P : {mfun mR >-> nat})
      (Fi : nat -> mR -> T),
      (forall i, generating_Mx G (Fi i)) ->
      generating_Mx G (fun r => Fi (P r) r).
```

The instance is declared on an alias `generating_type := T` (declaring it on `T` itself would make every type a `qbsType` with an undetermined generator). The lemma `generating_qbs_incl` states `G `<=` qbs_Mx (s := generating_qbs G)`, and `generating_qbs_least` states that `generating_Mx G` is contained in every closed set containing `G`.

### 1.15 Image QBS

**File:** `theories/quasi_borel.v`

For a morphism `f : X -> Y`, `map_qbs hf` is the QBS on `Y` generated by `{f \o alpha | alpha random in X}` (using `generating_qbs`, so constants are included even when `f` is not surjective).

| Name | Statement |
|------|-----------|
| `map_qbs_random` | `f \o alpha` is random in `map_qbs hf` when `alpha` is random in `X` |
| `map_qbs_sub` | random elements of `map_qbs hf` are random in `Y` |
| `map_qbs_morph_from` | `f : X -> map_qbs hf` is a morphism |
| `map_qbs_morphism_out` | `g : Y -> Z` is a morphism out of `map_qbs hf` when it is a morphism out of `Y` |

### 1.16 Order Structure

**File:** `theories/quasi_borel.v`

Following Isabelle, the order on QBS structures on a fixed carrier `T` is inclusion of the sets of random elements:

```
Definition qbs_leT (MxX MxY : set (mR -> T)) : Prop :=
  MxX `<=` MxY.
```

with `qbs_leT_refl`, `qbs_leT_trans` and `qbs_leT_antisym`. The join of two sets of random elements is `qbs_supT MxX MxY := generating_qbs [set alpha | MxX alpha \/ MxY alpha]`, with `qbs_supT_ub_l`, `qbs_supT_ub_r` and `qbs_supT_least` (least upper bound among closed sets).

### 1.17 Coproducts (Binary)

**File:** `theories/coproduct_qbs.v`

A function `f : mR -> X + Y` is random iff it factors through `inl`, through `inr`, or is a measurable gluing of an `inl`-part and an `inr`-part via a measurable boolean predicate:

```
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

Lemma sigma_case_uniq Z (h : sigmaQ X -> Z) :
  h = sigma_case (fun i x => h (existT X i x)).
```

### 1.19 Dependent Products (Pi Type)

**File:** `theories/coproduct_qbs.v`

For a family `X : I -> qbsType R`, `piQ I X` has carrier `forall i, X i`, and `alpha` is random iff `fun r => alpha r i` is random in `X i` for every `i`. The projection `qbs_morphism_proj` and tupling `qbs_morphism_tuple` are morphisms.

### 1.20 List Type

**File:** `theories/coproduct_qbs.v`

Lists are the countable coproduct of the finite powers, as in HKSY Sec. IV:

```
Definition listQ (X : qbsType R) : qbsType R :=
  sigmaQ (fun n => piQ 'I_n (fun=> X)).

Lemma qbs_morphism_size (X : qbsType R) :
  qbs_morphism (X := listQ X) (Y := natQ R) (fun l => projT1 l).
```

---

## Part II: Probability Monad and Integration

Source files: `theories/probability_qbs.v` (483 lines, 26 Qed), `theories/qbs_monad.v` (679 lines, 56 Qed), `theories/qbs_normalize.v` (161 lines, 12 Qed), `theories/qbs_quotient.v` (194 lines, 19 Qed), `theories/pair_qbs_measure.v` (770 lines, 21 Qed), `theories/qbs_giry.v` (132 lines, 9 Qed), `theories/normal_centred.v` (280 lines, 14 Qed), `theories/measure_as_qbs_measure.v` (197 lines, 4 Qed), `theories/showcase/bayesian_regression.v` (426 lines, 22 Qed).

### 2.1 QBS Probability Triple

**File:** `theories/probability_qbs.v`

```
Record qbs_prob (X : qbsType R) := mkQBSProb {
  qbs_prob_alpha : mR -> X ;
  qbs_prob_mu : probability mR R ;
  qbs_prob_alpha_random : qbs_Mx (s := X) qbs_prob_alpha }.
```

A probability on a QBS `X` is a triple `(alpha, mu, proof)` where `alpha : mR -> X` is a random element and `mu` is a probability measure on `mR`. The pushforward `alpha_*(mu)` gives the induced distribution on X.

### 2.2 Equivalence of Probability Triples

**File:** `theories/probability_qbs.v`

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
| `qbs_prob_equiv_sym` | Symmetry |
| `qbs_prob_equiv_trans` | Transitivity |

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

A function `h` is `qbs_measurable` iff it is measurable on every random element; `qbs_measurable_sigma_Mx` shows that preimages of measurable sets are `sigma_Mx` sets. Integration respects equivalence for measurable integrands:

```
Lemma qbs_integral_equiv (X : qbsType R) (p1 p2 : qbs_prob X)
    (h : X -> \bar R) :
  qbs_measurable X h -> qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
```

(The nonnegative core is `ge0_integral_sigma_Mx`. `qbs_integral_equiv_same_alpha` is the simpler case of a shared `alpha`.) The pushforward formulation is `qbs_integral_as_pushforward` and `qbs_pushforward_integrable`.

### 2.4 The Law of a QBS Probability (HKSY eq. (3))

**File:** `theories/probability_qbs.v`

Using the measurable structure on `L X = qbs_meas X`, a QBS probability has a law, a genuine probability measure:

```
Lemma qbs_measurableE (X : qbsType R) (h : X -> \bar R) :
  qbs_measurable X h <->
  measurable_fun [set: qbs_meas X] (h : qbs_meas X -> \bar R).

Definition qbs_law (X : qbsType R) (p : qbs_prob X) :
    probability (qbs_meas X) R :=
  distribution (qbs_prob_mu p) (qbs_prob_alpha_mfun p).

Lemma qbs_lawE (X : qbsType R) (p : qbs_prob X) (A : set X) :
  qbs_law p A = qbs_prob_mu p (qbs_prob_alpha p @^-1` A).

Lemma qbs_prob_equivE (X : qbsType R) (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 <->
  (forall A : set (qbs_meas X), measurable A -> qbs_law p1 A = qbs_law p2 A).

Lemma qbs_integral_law (X : qbsType R) (p : qbs_prob X) (h : X -> \bar R) :
  qbs_measurable X h -> qbs_integral X p h = (\int[qbs_law p]_x h x)%E.
```

Equivalence of probabilities is thus equality of laws, and QBS integration is Lebesgue integration against the law (`ge0_qbs_integral_law` is the nonnegative version).

### 2.5 Expectation, Events and Variance

**File:** `theories/probability_qbs.v`

```
Definition qbs_expect (X : qbsType R) (p : qbs_prob X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Definition qbs_prob_event (X : qbsType R) (p : qbs_prob X)
  (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).

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

### 2.6 Integrability, Integral Arithmetic and Probability Inequalities

**File:** `theories/probability_qbs.v`

```
Definition qbs_integrable (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :=
  (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p).
```

| Name | Statement |
|------|-----------|
| `qbs_integrableD` / `qbs_integrableB` | Closure under `\+` / `\-` |
| `qbs_integrableN` | Closure under negation |
| `qbs_integrableZl` | Closure under scalar multiplication `k%:E * f x` |
| `qbs_integralD` / `qbs_integralB` | Integral of a sum / difference (under integrability) |
| `qbs_integralZl` | `qbs_integral X p (fun x => k%:E * f x) = k%:E * qbs_integral X p f` |
| `qbs_varianceE` | `Var(h) = E[h^2] - E[h]^2` (for `h` in `Lfun 2`) |
| `qbs_varianceZ` | `Var(a h) = a^2 Var(h)` |

The Markov and Chebyshev inequalities are lifted to QBS probabilities. `qbs_rv` builds a `{RV (qbs_prob_mu p) >-> R}` from a measurable composition.

```
Lemma qbs_markov (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (f : R -> R) (eps : R)
    (hm : measurable_fun setT (h \o qbs_prob_alpha p))
    (heps : (0 < eps)%R)
    (hmf : measurable_fun [set: R] f)
    (hf0 : forall r, (0 <= r)%R -> (0 <= f r)%R)
    (hfnd : {in Num.nneg &, {homo f : x y / (x <= y)%R}}) :
  (f eps)%:E * qbs_prob_event X p [set x | eps%:E <= `|(h x)%:E|] <=
  qbs_integral X p (fun x => ((f \o normr \o h) x)%:E).

Lemma qbs_chebyshev (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (eps : R)
    (hm : measurable_fun setT (h \o qbs_prob_alpha p))
    (heps : (0 < eps)%R) :
  qbs_prob_mu p
    [set x | (eps <= `|h (qbs_prob_alpha p x) -
      fine (qbs_expect X p h)|)%R] <=
  (eps ^- 2)%:E * qbs_variance X p h.
```

### 2.7 The Probability Monad P(X)

**File:** `theories/qbs_monad.v`

Following HKSY, the random elements of `P(X)` are the maps `r |-> [alpha, g r]` for a *single* random element `alpha` of `X` and a measurable map `g : R -> giry R` into probability measures (the Giry space of mathcomp-analysis). This is the strong (shared-`alpha`) condition; unlike a pointwise condition, it makes `qbs_bind` total. The carrier is `qbs_prob X` itself:

```
Record qbs_prob_rep X (b : mR -> qbs_prob X) (a : mR -> X) (g : mR -> G) :
    Prop := QbsProbRep {
  rep_random : qbs_Mx a ;
  rep_measurable : measurable_fun [set: mR] g ;
  rep_mass : forall r, g r [set: mR] = 1 ;
  rep_event : forall r U, sigma_Mx U ->
    qbs_prob_event X (b r) U = g r (a @^-1` U) }.

Definition monadP_random X : set (mR -> qbs_prob X) :=
  [set b | exists a g, qbs_prob_rep b a g].

Definition monadP X : Type := qbs_prob X.
HB.instance Definition _ X :=
  @isQBS.Build R (monadP X) (monadP_random X)
    (@monadP_comp X) (@monadP_const X) (@monadP_glue X).
```

Here `G := giry mR R`, and `qbs_prob_rep b a g` says that `b r` is represented by `[a, g r]` for every `r`. Random elements are saturated with respect to pointwise equivalence (`monadP_random_equiv`), and `monadP_random_event` shows that the probability of a `sigma_Mx` event is measurable in `r`. The glue axiom (`monadP_glue`) decodes the selector with the retraction `encode_RR_mR`/`decode_RR_mR` from `standard_borel.v`.

The file also defines a small helper `giry_prob m m1`, the probability measure `m : giry T R` given a proof `m1` that `m` has total mass 1, with `giry_bindE` and `giry_bind_setT` for the Giry bind.

### 2.8 Return

**File:** `theories/qbs_monad.v`

```
Definition qbs_return X (x : X) : monadP X :=
  @mkQBSProb R X (fun=> x) (\d_(0 : mR))%R (qbs_Mx_const x).

Lemma qbs_return_event X (x : X) (U : set X) :
  qbs_prob_event X (qbs_return x) U = (x \in U)%:R%:E.

Lemma qbs_return_morphism X : qbs_morphism (X := X) (Y := monadP X)
  (@qbs_return X).

Lemma qbs_return_integral X (x : X) (h : X -> \bar R) :
  qbs_integral X (qbs_return x) h = h x.
```

`qbs_returnQ X : qbsHomType X (monadP X)` is the bundled version.

### 2.9 Bind

**File:** `theories/qbs_monad.v`

For `p : qbs_prob X` and a *bundled morphism* `f : qbsHomType X (monadP Y)`, bind is defined without any side condition: `f \o alpha_p` is random in `P(Y)`, so it has a representation `[a, g]`, and the bound measure is the Giry bind of `mu_p` with `g`.

```
Definition qbs_bind : monadP Y :=
  @mkQBSProb R Y bind_a (giry_prob bind_mu1) (rep_random bind_rep).

Lemma qbs_bind_integral (h : Y -> \bar R) :
  qbs_measurable Y h -> (forall y, 0 <= h y) ->
  qbs_integral Y qbs_bind h =
  \int[qbs_prob_mu p]_r qbs_integral Y (f (qbs_prob_alpha p r)) h.

Lemma qbs_bind_event (U : set Y) : sigma_Mx U ->
  qbs_prob_event Y qbs_bind U =
  \int[qbs_prob_mu p]_r qbs_prob_event Y (f (qbs_prob_alpha p r)) U.
```

Bind with a fixed continuation is itself a morphism, and the bundled version is `qbs_bindQ`:

```
Lemma qbs_bind_morphism X Y Z (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) :
  qbs_morphism (X := X) (Y := monadP Z) (fun x => qbs_bind (f x) g).

Definition qbs_bindQ X Y Z (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) : qbsHomType X (monadP Z) :=
  HB.pack (fun x => qbs_bind (f x) g)
    (isQBSMorphism.Build R X (monadP Z) _ (qbs_bind_morphism f g)).
```

### 2.10 Monad Laws

**File:** `theories/qbs_monad.v`

```
Lemma qbs_bind_returnl X Y (x : X) (f : qbsHomType X (monadP Y)) :
  qbs_prob_equiv Y (qbs_bind (qbs_return x) f) (f x).

Lemma qbs_bind_returnr X (p : qbs_prob X) :
  qbs_prob_equiv X (qbs_bind p (qbs_returnQ X)) p.

Lemma qbs_bindA X Y Z (p : qbs_prob X) (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) :
  qbs_prob_equiv Z (qbs_bind (qbs_bind p f) g) (qbs_bind p (qbs_bindQ f g)).
```

The laws hold up to `qbs_prob_equiv`; on the quotient type of Section 2.17 they become equalities.

### 2.11 Functorial Map

**File:** `theories/qbs_monad.v`

Map is the pushforward of the random element along a bundled morphism, keeping the base measure:

```
Definition monadP_map X Y (f : qbsHomType X Y) (p : monadP X) :
    monadP Y :=
  @mkQBSProb R Y (f \o qbs_prob_alpha p) (qbs_prob_mu p)
    (qbs_hom_proof _ (qbs_prob_alpha_random p)).
```

| Name | Statement |
|------|-----------|
| `monadP_map_event` | `qbs_prob_event Y (monadP_map f p) U = qbs_prob_event X p (f @^-1` U)` |
| `monadP_map_morphism` | `monadP_map f` is a morphism `monadP X -> monadP Y` (an HB instance) |
| `sigma_Mx_preimage` | Preimages of `sigma_Mx` sets under morphisms are `sigma_Mx` sets |
| `monadP_map_id` | `monadP_map (qbs_id X) p = p` (propositional equality) |
| `monadP_map_comp` | `monadP_map (qbs_comp f g) p = monadP_map g (monadP_map f p)` (propositional equality) |
| `monadP_map_bind` | Map is bind with `return \o f`, up to equivalence |
| `qbs_prob_eqP` | Two triples with equal `alpha` and `mu` are equal |
| `qbs_bind_map` | `bind (map g p) f ~ bind p (g ; f)` |

### 2.12 Congruence

**File:** `theories/qbs_monad.v`

Since bind is total, it is a congruence for equivalence in both arguments, with no side conditions:

```
Lemma qbs_bind_equiv_l X Y (p1 p2 : qbs_prob X) (f : qbsHomType X (monadP Y)) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv Y (qbs_bind p1 f) (qbs_bind p2 f).

Lemma qbs_bind_equiv_r X Y (p : qbs_prob X) (f g : qbsHomType X (monadP Y)) :
  (forall x, qbs_prob_equiv Y (f x) (g x)) ->
  qbs_prob_equiv Y (qbs_bind p f) (qbs_bind p g).

Lemma monadP_map_equiv X Y (f : qbsHomType X Y) (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 ->
  qbs_prob_equiv Y (monadP_map f p1) (monadP_map f p2).
```

The integral version is `ge0_qbs_integral_equiv`.

### 2.13 Monad Join

**File:** `theories/qbs_monad.v`

```
Definition qbs_join X (pp : monadP (monadP X)) : monadP X :=
  qbs_bind pp (qbs_id (monadP X)).
```

`qbs_join_morphism` shows join is a morphism (with a bundled version `qbs_joinQ X`). The monad coherence laws hold up to equivalence:

| Name | Statement |
|------|-----------|
| `qbs_join_return` | `join (return p) ~ p` |
| `qbs_join_map_return` | `join (map return p) ~ p` |
| `qbs_join_assoc` | `join (join P) ~ join (map join P)` |

### 2.14 Monad Strength

**File:** `theories/qbs_monad.v`

```
Definition qbs_strength W X (wp : W * monadP X) : monadP (prodQ W X) :=
  @mkQBSProb R (prodQ W X) (fun r => (wp.1, qbs_prob_alpha wp.2 r))
    (qbs_prob_mu wp.2) (prodQ_const_random wp.1 (qbs_prob_alpha_random wp.2)).
```

| Name | Statement |
|------|-----------|
| `qbs_strength_event` | `qbs_prob_event _ (qbs_strength (w, p)) U = qbs_prob_event X p [set x | U (w, x)]` |
| `qbs_strength_morphism` | Strength is a morphism `prodQ W (monadP X) -> monadP (prodQ W X)` (bundled as `qbs_strengthQ`) |
| `qbs_strength_return` | `qbs_strength (w, qbs_return x) = qbs_return (w, x)` |
| `qbs_strength_natural` | Naturality in both arguments |
| `qbs_strength_snd` | `monadP_map (qbs_snd W X) (qbs_strength (w, p)) = p` |

The proof that strength is a morphism uses `measurable_giry_xsection` (measurability of `r |-> g r (xsection C r)`, a kernel-section lemma) and `sigma_Mx_section`.

### 2.15 Integration as a Morphism and Internal Bind (HKSY Thm. 21)

**File:** `theories/qbs_monad.v`

Integrating a fixed nonnegative measurable function is a morphism from `P(X)` into the QBS of extended reals (HKSY Sec. V-C):

```
Lemma qbs_integral_morphism X (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, 0 <= h x) ->
  qbs_morphism (X := monadP X) (Y := R_qbs R (\bar R))
    (fun p => qbs_integral X p h).
```

Bind is internal: a single morphism `P(X) * (X => P(Y)) -> P(Y)`, obtained from strength and evaluation:

```
Definition qbs_bind_internal X Y :
    qbsHomType (prodQ (monadP X) (expQ X (monadP Y))) (monadP Y) :=
  qbs_bindQ (qbs_comp (qbs_pair (qbs_snd _ _) (qbs_fst _ _))
    (qbs_strengthQ _ _)) (qbs_eval X (monadP Y)).

Lemma qbs_bind_internalE X Y (p : monadP X) (f : qbsHomType X (monadP Y)) :
  qbs_prob_equiv Y (qbs_bind_internal X Y (p, f)) (qbs_bind p f).
```

### 2.16 Monadic Product and Commutativity (HKSY Prop. 22(2))

**File:** `theories/qbs_monad.v`

The monadic product of `p : monadP X` and `q : monadP Y` is bind followed by strength:

```
Definition qbs_swap X Y : qbsHomType (prodQ X Y) (prodQ Y X) :=
  qbs_pair (qbs_snd X Y) (qbs_fst X Y).

Definition qbs_pairP X Y (p : monadP X) (q : monadP Y) : monadP (prodQ X Y) :=
  qbs_bind p (qbs_comp (qbs_pair (qbs_id X) (qbs_const X q)) (qbs_strengthQ X Y)).

Lemma qbs_pairP_event X Y (p : monadP X) (q : monadP Y) (U : set (prodQ X Y)) :
  sigma_Mx U ->
  qbs_prob_event _ (qbs_pairP p q) U =
  \int[qbs_prob_mu p]_r qbs_prob_mu q
    [set t | U (qbs_prob_alpha p r, qbs_prob_alpha q t)].
```

Commutativity says that the order of drawing does not matter. It is proved from Fubini-Tonelli on the seeds, once the set of pairs of seeds landing in `U` is known to be measurable (`measurable_seeds`):

```
Lemma qbs_pairP_comm :
  qbs_prob_equiv (prodQ X Y) (qbs_pairP p q) (monadP_map (qbs_swap Y X) (qbs_pairP q p)).

Lemma qbs_bind_comm X Y Z (p : monadP X) (q : monadP Y)
    (f : qbsHomType (prodQ X Y) (monadP Z)) :
  qbs_prob_equiv Z (qbs_bind (qbs_pairP p q) f)
    (qbs_bind (qbs_pairP q p) (qbs_comp (qbs_swap Y X) f)).
```

### 2.17 Normalisation (HKSY Sec. VI)

**File:** `theories/qbs_normalize.v`

Normalisation `norm : P(X * R) -> P(X) + error` takes a probability on pairs `(x, w)` and reweights by the weight `max(0, w)`:

```
Definition qbs_weight p (r : mR) : \bar R :=
  (maxr 0 (qbs_prob_alpha p r).2)%:E.

Definition qbs_evidence p : \bar R := \int[qbs_prob_mu p]_r qbs_weight p r.

Definition qbs_density (A : set mR) : \bar R :=
  \int[qbs_prob_mu p]_(r in A) qbs_weight p r.
```

`qbs_density p` is registered as a measure (the base measure weighted by `qbs_weight p`). The normalised probability uses mathcomp-analysis' `mnormalize`, and `qbs_normalize` fails when the evidence is zero or infinite:

```
Definition qbs_normalize_prob p : qbs_prob X :=
  @mkQBSProb R X (fun r => (qbs_prob_alpha p r).1)
    (mnormalize (qbs_density p) (qbs_prob_mu p))
    (qbs_normalize_alpha_random p).

Definition qbs_normalize p : option (qbs_prob X) :=
  if (0 < qbs_evidence p) && (qbs_evidence p < +oo)
  then Some (qbs_normalize_prob p) else None.
```

| Name | Statement |
|------|-----------|
| `qbs_weight_ge0`, `measurable_qbs_weight` | The weight is nonnegative and measurable |
| `qbs_densityT` | `qbs_density p [set: mR] = qbs_evidence p` |
| `qbs_normalize_event` | The normalised probability of `U` is the weighted probability of `U` divided by the evidence |
| `qbs_evidence_equiv` | Evidence is invariant under equivalence |
| `qbs_normalize_equiv` | Normalisation is well defined on equivalence classes (both `Some` and equivalent, or both `None`) |

```
Lemma qbs_normalize_event p (U : set X) :
  0 < qbs_evidence p < +oo -> sigma_Mx U ->
  qbs_prob_event X (qbs_normalize_prob p) U =
  qbs_integral _ p (fun xw => ((\1_U xw.1 : R) * maxr 0 xw.2)%:E) *
  (fine (qbs_evidence p))^-1%:E.
```

### 2.18 Quotient Type for QBS Probability

**File:** `theories/qbs_quotient.v`

`qbs_prob X` is quotiented by `qbs_prob_equiv` using mathcomp's `generic_quotient`, following the almost-everywhere-equality quotient of `hoelder.v`:

```
Definition qbs_equiv_op : rel (qbs_prob X) :=
  fun p1 p2 => `[< qbs_prob_equiv X p1 p2 >].

Definition qbs_quot : Type := {eq_quot qbs_prob_equiv_canonical}.
```

| Name | Statement |
|------|-----------|
| `qbs_prob_equivP` | `reflect (qbs_prob_equiv X p1 p2) (p1 == p2 %[mod qbs_quot])` |
| `qbs_quot_eqP` | Equivalent triples have equal classes |
| `qbs_prob_equiv_repr` | The representative of a class is equivalent to the triple |

The quotient is itself a QBS (HKSY Sec. V-D(a)): its random elements are the maps whose representatives are random in `P(X)`. The projection `qbs_quot_pi_morphism` and `qbs_quot_repr_morphism` are morphisms.

The monad operations descend to the quotient:

```
Definition quot_return (x : X) : qbs_quot X := \pi_(qbs_quot X) (qbs_return x : qbs_prob X).
Definition quot_bind (q : qbs_quot X) (f : qbsHomType X (monadP Y)) :
  qbs_quot Y := \pi_(qbs_quot Y) (qbs_bind (repr q) f : qbs_prob Y).
Definition quot_map (f : qbsHomType X Y) (q : qbs_quot X) : qbs_quot Y :=
  \pi_(qbs_quot Y) (monadP_map f (repr q) : qbs_prob Y).
Definition quot_integral (q : qbs_quot X) (h : X -> \bar R) : \bar R :=
  qbs_integral X (repr q) h.
```

and the monad laws hold as *equalities*:

```
Lemma quot_bind_returnl X Y (x : X) (f : qbsHomType X (monadP Y)) :
  quot_bind (quot_return x) f = \pi_(qbs_quot Y) (f x : qbs_prob Y).
Lemma quot_bind_returnr X (q : qbs_quot X) : quot_bind q (qbs_returnQ X) = q.
Lemma quot_bindA X Y Z (q : qbs_quot X) (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) :
  quot_bind (quot_bind q f) g = quot_bind q (qbs_bindQ f g).
Lemma quot_map_id X (q : qbs_quot X) : quot_map (qbs_id X) q = q.
Lemma quot_map_comp X Y Z (f : qbsHomType X Y) (g : qbsHomType Y Z)
    (q : qbs_quot X) :
  quot_map (qbs_comp f g) q = quot_map g (quot_map f q).
```

The computation lemmas `quot_bindE` and `quot_mapE` relate the lifted operations to the triple-level ones on `\pi p`, and `ge0_quot_integralE` does the same for integration.

### 2.19 Product Measures and Fubini

**File:** `theories/pair_qbs_measure.v`

The product of `p : qbs_prob X` and `q : qbs_prob Y` is a probability on `prodQ X Y`. Since the base measure must live on `mR`, the product measure `mu_p \x mu_q` on `mR * mR` is pushed through the retraction `encode_RR_mR` of `standard_borel.v`:

```
Definition qbs_pair_alpha (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r =>
    let uv := @decode_RR_mR R r in
    (qbs_prob_alpha p uv.1, qbs_prob_alpha q uv.2).

Definition qbs_pair_mu (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : probability mR R :=
  qbs_pair_mu_build p q.

Definition qbs_prob_pair (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha p q)
    (qbs_pair_mu p q)
    (qbs_pair_alpha_random p q).
```

This agrees with the monadic product of Section 2.16:

```
Lemma qbs_prob_pairE (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y) :
  qbs_prob_equiv (prodQ X Y) (qbs_pairP (p : monadP X) (q : monadP Y))
    (qbs_prob_pair X Y p q).
```

For integration, `qbs_pair_integral` works directly on `mR * mR`, with no encoding:

```
Definition qbs_pair_integral (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) : \bar R :=
  \int[(qbs_prob_mu p \x qbs_prob_mu q)]_rr
    h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).
```

| Name | Statement |
|------|-----------|
| `qbs_pair_integral_iterated` | Joint integral on `mu_p \x mu_q` = iterated QBS integral (under integrability) |
| `qbs_pair_integral_fst` / `qbs_pair_integral_snd` | Integrating a function of one component recovers the marginal integral |
| `qbs_pair_integral_comm` | Integrating `h` against `mu_p \x mu_q` = integrating `h \o swap` against `mu_q \x mu_p` |
| `qbs_prob_pair_measure_eq_bind` | Integral against `qbs_prob_pair p q` = iterated QBS integral |
| `qbs_pair_integral_factorization` | `E[f x * g y] = E[f] * E[g]` on a product measure |

`qbs_pair_integral_iterated` is iterated integration on this specific product measure, not full Fubini on arbitrary products. `qbs_pair_integral_factorization` is a statement about product measures (the two factors depend on disjoint coordinates), not about statistical independence; the genuine independence statement is in the next section.

### 2.20 Independence

**File:** `theories/pair_qbs_measure.v`

Independence of two morphisms out of a common probability space is defined through the product construction: the joint law equals the product of the marginals.

```
Definition qbs_indep (X Y Z : qbsType R) (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y) : Prop :=
  qbs_prob_equiv (prodQ X Y) (monadP_map (qbs_pair f g) p)
    (qbs_prob_pair X Y (monadP_map f p) (monadP_map g p)).
```

On Borel rectangles this gives the classical product rule:

```
Lemma qbs_indep_rect (Z : qbsType R) (p : qbs_prob Z)
    (f g : qbsHomType Z (realQ R)) (A B : set mR) :
  measurable A -> measurable B -> qbs_indep _ _ _ p f g ->
  qbs_prob_event Z p [set z | A (f z) /\ B (g z)] =
  qbs_prob_event Z p (f @^-1` A) * qbs_prob_event Z p (g @^-1` B).
```

and the product rule for expectations of real-valued test functions:

```
Lemma qbs_integral_indep_factorization (X Y Z : qbsType R)
    (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y)
    (phi : X -> R) (psi : Y -> R)
    (hindep : qbs_indep X Y Z p f g)
    (hmeas : qbs_measurable (prodQ X Y)
       (fun xy : X * Y => (phi xy.1 * psi xy.2)%:E))
    (hintphi : ...) (hintpsi : ...) (hintjoint : ...) (hintprod : ...) :
  qbs_integral Z p (fun z => (phi (f z) * psi (g z))%:E) =
  qbs_expect X (monadP_map f p) phi * qbs_expect Y (monadP_map g p) psi.
```

(the four `h...` hypotheses are integrability conditions, abbreviated here; see the source for their statements).

### 2.21 Variance of Independent Sums

**File:** `theories/pair_qbs_measure.v`

```
Definition qbs_pair_variance (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R) : \bar R :=
  variance (qbs_prob_mu px \x qbs_prob_mu py)
    (fun rr : mR * mR =>
      (f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2))%R).
```

The main theorem `qbs_variance_indep_sum` states `Var(f(x) + g(y)) = Var_px(f) + Var_py(g)` on the product measure, with `L2` and integrability hypotheses:

```
  qbs_pair_variance X Y px py f g =
  (qbs_variance X px f + qbs_variance Y py g)%E.
```

It rests on four helper lemmas about a function of one coordinate of a product measure, `expectation_prod_fst`, `expectation_prod_snd`, `variance_prod_fst`, `variance_prod_snd`, and on `expectation_prod_indep` (`E[h1(r1) h2(r2)] = E[h1] E[h2]`).

### 2.22 Comparison with the Giry Monad (HKSY Prop. 22(3), 23)

**File:** `theories/qbs_giry.v`

A QBS probability on `R_qbs M` induces a probability measure on `M`, its distribution. For `M` standard Borel, the comparison is faithful and preserves bind:

```
Definition qbs_to_giry (p : qbs_prob (R_qbs R M)) : probability M R :=
  distribution (qbs_prob_mu p) (qbs_prob_alpha_mfun p).

Lemma qbs_to_giryE (p : qbs_prob (R_qbs R M)) (A : set M) :
  qbs_to_giry p A = qbs_prob_event (R_qbs R M) p A.

Lemma qbs_integral_giry (p : qbs_prob (R_qbs R M)) (f : M -> \bar R) :
  measurable_fun [set: M] f ->
  (qbs_prob_mu p).-integrable [set: mR] (f \o qbs_prob_alpha p) ->
  qbs_integral (R_qbs R M) p f = \int[qbs_to_giry p]_y f y.

Lemma qbs_to_giry_inj (p1 p2 : qbs_prob (R_qbs R M)) :
  (forall A, measurable A -> qbs_to_giry p1 A = qbs_to_giry p2 A) ->
  qbs_prob_equiv (R_qbs R M) p1 p2.

Lemma qbs_to_giry_bind d' (M' : measurableType d') (p : qbs_prob (R_qbs R M))
    (f : qbsHomType (R_qbs R M) (monadP (R_qbs R M'))) (A : set M') :
  measurable A ->
  qbs_to_giry (qbs_bind p f : qbs_prob _) A =
  \int[qbs_to_giry p]_x qbs_to_giry (f x : qbs_prob _) A.
```

(`qbs_to_giry_inj` and `qbs_to_giry_bind` are stated for `M` with a `standard_borel_wit`.) Further lemmas: `qbs_prob_equiv_giry` (equivalent probabilities have the same distribution), `qbs_to_giry_return` (return goes to the Dirac measure), and `qbs_to_giry_map` (map goes to pushforward).

Conversely, a probability measure `P` on `M` yields a QBS probability on `R(M)` from a measurable `encode : M -> R` with measurable left inverse `decode`, and the two constructions are mutually inverse up to equivalence:

```
Definition giry_to_qbs (P : probability M R) : qbs_prob (R_qbs R M) :=
  @mkQBSProb R (R_qbs R M) decode (distribution P encode) decode_meas.

Lemma qbs_to_giryK (P : probability M R) (A : set M) :
  qbs_to_giry (giry_to_qbs P) A = P A.

Lemma giry_to_qbsK (p : qbs_prob (R_qbs R M)) :
  qbs_prob_equiv (R_qbs R M) (giry_to_qbs (qbs_to_giry p)) p.
```

### 2.23 Standard Distributions

**File:** `theories/measure_as_qbs_measure.v`

Standard distributions as QBS probabilities (the general embedding of a probability measure on a standard Borel space is `giry_to_qbs`):

```
Definition qbs_normal_distribution (mu sigma : R) : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (normal_prob mu sigma : probability mR R)
    (@measurable_id _ mR setT).

Definition qbs_bernoulli
  (p : R) (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) : qbs_prob (boolQ R) :=
  @mkQBSProb R (boolQ R) (fun r : mR => (r < p)%R)
    (uniform_prob ltr01 : probability mR R)
    (measurable_fun_ltr
      (@measurable_id _ mR setT)
      (@measurable_cst _ _ mR mR setT p)).

Definition qbs_uniform : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (uniform_prob ltr01 : probability mR R)
    (@measurable_id _ mR setT).
```

The map `mu |-> N(mu, sigma)` is a morphism `realQ -> monadP realQ` (`qbs_normal_morphism`), bundled as `qbs_normalQ sigma`.

Expectation lemmas:

```
Lemma qbs_expect_bernoulli (p : R) (hp0 : 0 <= p) (hp1 : p <= 1) :
  qbs_expect (boolQ R) (qbs_bernoulli p hp0 hp1) (fun b : bool => b%:R) = p%:E.

Lemma qbs_expect_uniform :
  qbs_expect (realQ R) qbs_uniform (fun x => x) = (2%:R^-1)%:E.

Lemma qbs_expect_normal (mu sigma : R) : sigma != 0 ->
  qbs_expect (realQ R) (qbs_normal_distribution mu sigma)
    (fun x => x) = mu%:E.
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

### 2.24 Bayesian Linear Regression

**File:** `theories/showcase/bayesian_regression.v` (426 lines, 22 Qed)

Following HKSY Sec. VI and the Isabelle AFP development (Bayesian_Linear_Regression.thy) by Hirata, Minamide, Sato, the prior is a probability on the *function space* `R => R`.

**Model:** `y = s * x + b + noise`, noise ~ N(0, 1/2); the parameters `s, b` are iid N(0, 3). Data: (1, 2.5), (2, 3.8), (3, 4.5), (4, 6.2), (5, 8.0).

**Prior.** The parameter prior is a monadic product, which is mapped to functions through the curried line `lin`:

```
Definition nu : monadP RQ := qbs_normal_distribution 0 3.
Definition prior2 : monadP W := qbs_pairP nu nu.

Definition lin : qbsHomType W F := qbs_curry_morph lin_uncurried.
Lemma linE (s b r : R) : lin (s, b) r = s * r + b.

Definition prior : monadP F := monadP_map lin prior2.
```

(here `W := prodQ RQ RQ` and `F := expQ RQ RQ`).

**Program.** The likelihood `obs_fun f` is the product of the five Gaussian densities of the data at `f 1, ..., f 5`; it is a QBS morphism `obs : qbsHomType F RQ`. The program is the normalisation of the prior weighted by the likelihood:

```
Definition wprior : monadP (prodQ F RQ) :=
  monadP_map (qbs_pair (qbs_id F) obs) prior.
Definition program : option (qbs_prob F) := qbs_normalize wprior.
```

**Posterior in closed form.** Completing the square gives explicit parameters (`post_s_mean`, `post_s_var`, `post_b_mean s`, `post_b_var`) and a constant `C`:

```
Definition C : R :=
  4 * Num.sqrt 2 / (pi ^+ 2 * Num.sqrt (29 * 2309 * pi)) *
  expR (- (11 * 11 * (138 * 100 + 41) / (25 * 29 * 2309))).

Definition posterior2 : monadP W :=
  qbs_bind
    (qbs_normal_distribution post_s_mean (Num.sqrt post_s_var) : monadP _)
    (qbs_comp (qbs_pair (qbs_id RQ)
      (qbs_comp post_b_meanQ (qbs_normalQ (Num.sqrt post_b_var))))
      (qbs_strengthQ RQ RQ)).
Definition posterior : monadP F := monadP_map lin posterior2.
```

| Name | Statement |
|------|-----------|
| `obs_prior_factor` | Prior density times likelihood is `C` times the posterior density (completing the square) |
| `prior2_integral` / `posterior2_integral` | Integrals against `prior2` / `posterior2` are iterated integrals against the Gaussians |
| `factor_integral` | `\int[N(0,3)]_s \int[N(0,3)]_b (h (s, b) * obs2 s b) = C * \int[post]_s \int[post(s)]_b h (s, b)` for `h` with values in [0, 1] |
| `wprior_evidence` | `qbs_evidence wprior = C%:E` (closed-form evidence) |
| `program_posterior` | **Main theorem** |

```
Lemma wprior_evidence : qbs_evidence wprior = C%:E.

Theorem program_posterior :
  exists q, program = Some q /\ qbs_prob_equiv F q posterior.
```

The theorem says that the program succeeds (the evidence is positive and finite, as it equals `C`), and that the resulting QBS probability on functions is equivalent to the explicit Gaussian posterior.

---


## Part III: Standard Borel Spaces (R × R as a Retract of R)

Source file: `theories/standard_borel.v` (1,287 lines, 57 Qed).

This file constructs a measurable retraction of R × R onto R: a measurable `encode_RR : R × R -> R` with a measurable left inverse `decode_RR`. This is exactly what the characterisation of standard Borel spaces as retracts of R (HKSY Prop. 5) needs, and it shows that the product of standard Borel spaces is standard Borel. `encode_RR` is not surjective (binary expansions ending in infinitely many 1s are missed), so this is a retraction, not an isomorphism. The construction composes three layers: (1) a bijection R ↔ (0,1) via arctangent, (2) a map (0,1)² -> (0,1) by binary digit interleaving with a left inverse, and (3) the composed encode/decode pair. The retraction is used by `qbs_monad.v` (gluing of random elements of P(X)) and `pair_qbs_measure.v` (product probability triples), and by `prod_standard_borel` in `measure_qbs_adjunction.v`.

### 3.1 Standard Borel: R to (0,1) Bijection

```
Definition phi (x : R) : R := atan x / pi + 1 / 2.
Definition psi (y : R) : R := tan (pi * (y - 1 / 2)).
```

| Name | Statement |
|------|-----------|
| `phi_gt0` | `0 < phi x` for all `x` |
| `phi_lt1` | `phi x < 1` for all `x` |
| `phiK` | `cancel phi psi` (psi is a left inverse of phi, unconditional) |
| `psiK` | `{in `](0,1)[, cancel psi phi}` (phi is a left inverse of psi on (0,1)) |
| `measurable_phi` | `measurable_fun setT phi` |
| `measurable_psi` | `measurable_fun (`](0,1)[) psi` (measurable on the open interval) |

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
  no_trailing_ones (deinterleave_even (bin_digits r)) ->
  no_trailing_ones (deinterleave_odd (bin_digits r)) ->
  pair_to_unit (unit_to_pair r) = r.
```

This direction requires no-trailing-ones on the deinterleaved subsequences, which does NOT follow from no-trailing-ones on the full sequence. However, this direction is not needed for `standard_borel_wit`, which only requires `g(f(x)) = x`. The set of reals where the extra hypotheses fail is a subset of the dyadic rationals (countable, hence measure-zero).

Additional helper lemmas: `bin_sum_ext`, `bin_sum_has_one_gt0`, `phi_has_true_digit`, `phi_ge0`, `phi_in_01`, `pair_to_unit_phi_gt0`, `pair_to_unit_phi_lt1`, `pair_to_unit_phi_in_itv`.

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

**Full-domain measurability of psi:**

```
Lemma measurable_psi_setT : measurable_fun [set: R] (@psi R).
```

The proof factors `psi = sin * cos^{-1}` on `pi*(y - 1/2)`, proves `sin` and `cos` are measurable via continuity, and handles `cos^{-1}` by approximating `x^{-1}` with `x/(x^2 + 1/(n+1))` (which is continuous) and applying `measurable_fun_cvg`. The convergence `inv_cvg_approx` is proved using `cvgV` and `cvg_harmonic`.

### 3.6 Composed Retraction R x R to R

```
Definition encode_RR (xy : R * R) : R :=
  psi (pair_to_unit (phi xy.1, phi xy.2)).

Definition decode_RR (r : R) : R * R :=
  let uv := unit_to_pair (phi r) in (psi uv.1, psi uv.2).
```

**Main round-trip theorems:**

```
Theorem encode_RRK (xy : R * R) :
  decode_RR (encode_RR xy) = xy.
```

The proof chains: (1) `psiK` to recover `pair_to_unit(phi x, phi y)` from `phi(psi(...))`, (2) `pair_to_unitK` to recover `(phi x, phi y)` from `unit_to_pair(pair_to_unit(...))`, and (3) `phiK` twice to recover `(x, y)`.

```
Theorem decode_RRK (r : R)
  (hnt_even : no_trailing_ones (deinterleave_even (bin_digits (phi r))))
  (hnt_odd : no_trailing_ones (deinterleave_odd (bin_digits (phi r))))
  (hu1_pos : 0 < (unit_to_pair (phi r)).1)
  (hu2_pos : 0 < (unit_to_pair (phi r)).2) :
  encode_RR (decode_RR r) = r.
```

This direction requires extra hypotheses (see Section 3.4) but is not needed for `standard_borel_wit`.

**Measurability:**

| Name | Statement |
|------|-----------|
| `measurable_encode_RR` | `measurable_fun setT encode_RR` |
| `measurable_decode_RR` | `measurable_fun setT decode_RR` |

The `measurable_encode_RR` proof composes `measurable_phi` (on each component), `measurable_pair_to_unit`, and `measurable_psi` (restricted to `(0,1)` via `measurable_comp` with `pair_to_unit_phi_in_itv`). The `measurable_decode_RR` proof uses `measurable_psi_setT`, `measurable_unit_to_pair_fst/snd`, and `measurable_phi`.

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

This witnesses that `R x R` is standard Borel in the sense of `standard_borel_wit` (defined in `measure_qbs_adjunction.v`, Section 1.11), which only requires a measurable retraction `g(f(x)) = x` (not the reverse). It is packaged as `prod_standard_borel` there, and combined with `R_qbs_full` it shows the R functor is full on products of standard Borel spaces. For use with product measures, the file also provides `encode_RR_mR`, `decode_RR_mR`, `encode_RR_mRK` (the same maps on `measurableTypeR R`) and `measurable_truncn` (used to decode the index when gluing probabilities).

---

## Part IV: Architecture and Project Status

### 4.1 File Dependency Graph

```
standard_borel.v (standalone analysis, no QBS imports)

quasi_borel.v
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
                  +--> qbs_normalize.v
                  |
                  +--> qbs_quotient.v
                  |
                  +--> pair_qbs_measure.v  (also imports standard_borel.v)
                  |
                  +--> measure_as_qbs_measure.v
                          |
                          +--> showcase/bayesian_regression.v
                               (also imports qbs_normalize.v)
```

### 4.2 Design Decisions

**Instances plus named definitions.** Concrete QBS constructions (`prodQ`, `expQ`, `unitQ`, `coprodQ`, `sigmaQ`, `piQ`, `monadP`, etc.) are declared with `HB.instance` on their (non-canonical) carrier types, and then exposed through a named definition of type `qbsType R`. Morphisms are bundled in the HB structure `qbsHomType`, which makes category laws and the universal properties statable as equalities (`qbs_homeqP`).

**Shared-alpha probability monad.** The random elements of `P(X)` are the maps `r |-> [alpha, g r]` with a single random element `alpha` and a measurable family `g` of Giry probabilities, as in HKSY. Bind takes a bundled morphism `X -> P(Y)` and is total, defined from the Giry bind of mathcomp-analysis; no diagonal-randomness side condition is needed.

**L as a measurableType.** The functor L is realised as `qbs_meas X`, a `measurableType` with the sigma-algebra `sigma_Mx X`. The adjunction L -| R is then a lemma about `measurable_fun` (`qbs_morphism_measurableP`), and laws of QBS probabilities are transported to genuine probability measures through `qbs_law`.

**Setoid first, quotient second.** The monad laws are proved up to `qbs_prob_equiv` on `qbs_prob X`, and the quotient `qbs_quot X` (`qbs_quotient.v`) restates them as equalities. Congruence of bind and map for equivalence is proved unconditionally.

**Product measure via the retraction R x R -> R.** `qbs_pair_mu` pushes the product measure `mu_p \x mu_q` through `encode_RR_mR` from `standard_borel.v`. The `qbs_pair_integral` function works directly on `mR * mR` for genuine product integration via Fubini. The same retraction decodes the selector in the glue axiom of `P(X)` and the product-closure of standard Borel spaces.

**Universe management.** The `\o` composition operator inside `[set ...]` comprehensions was replaced with explicit lambdas in a few places to avoid universe inconsistencies between `algebra_tactics.ring` and the QBS type hierarchy.

### 4.3 Comparison with Isabelle AFP

| Feature | Isabelle AFP | This development |
|---------|-------------|------------------|
| QBS axioms | Locale-based | HB mixin/structure |
| Probability monad | Quotient type | Triples with equivalence `qbs_prob_equiv`, plus `qbs_quot` quotient with laws as equalities |
| Cartesian closure | Present | `qbs_curryK`, `qbs_uncurryK`, `qbs_curry_morph_uniq` |
| L -| R adjunction | Present | `qbs_morphism_measurableP` (L as a `measurableType`) |
| Countable coproducts / lists | Present | `sigmaQ` / `sigma_case` / `listQ` |
| Standard Borel R≅R×R | Not formalized | `pair_standard_borel` (retraction, via atan + digit interleaving) |
| Bayesian regression | Function-space prior | Function-space prior `prior : monadP (expQ RQ RQ)`, closed-form posterior |
| Program correctness | `program_result` (Inl) | `program_posterior` (program = `Some q`, `q` equivalent to the posterior) |
| Evidence | Explicit closed form C | `wprior_evidence` (evidence = `C`) |
| Monad strength, join | Not formalized | `qbs_strength*`, `qbs_join*` lemmas |
| Internal bind (HKSY Thm. 21) | Not formalized | `qbs_bind_internal` |
| Commutativity (HKSY Prop. 22(2)) | Not formalized | `qbs_pairP_comm`, `qbs_bind_comm` |
| Fubini on QBS | Not formalized | `qbs_pair_integral_iterated` + marginals |
| Independence | Not formalized | `qbs_indep`, `qbs_indep_rect`, `qbs_integral_indep_factorization` |
| QBS↔Giry bridge | Not formalized | `qbs_to_giry` / `giry_to_qbs`, `qbs_to_giry_bind` |
| Normalizer | Not formalized | `qbs_normalize` + `qbs_normalize_event`, `qbs_normalize_equiv` |
| Integral arithmetic | Not formalized | `qbs_integralD/B/Zl` + `qbs_integrable` |
| Probability ineq. | Not formalized | `qbs_markov` + `qbs_chebyshev` |
| Variance | Not formalized | `qbs_varianceE` + `qbs_varianceZ` |
| E[distributions] | Not formalized | `qbs_expect_normal` / `bernoulli` / `uniform` |
| Standard Borel inst. | Not formalized | R, nat, bool, prod, ereal |
| Lines | ~5000 | 6,226 |

### 4.4 Statistics

| File | Lines | Proofs |
|------|------:|-------:|
| `quasi_borel.v` | 821 | 49 |
| `measure_qbs_adjunction.v` | 332 | 14 |
| `coproduct_qbs.v` | 464 | 19 |
| `probability_qbs.v` | 483 | 26 |
| `qbs_monad.v` | 679 | 56 |
| `qbs_normalize.v` | 161 | 12 |
| `qbs_quotient.v` | 194 | 19 |
| `pair_qbs_measure.v` | 770 | 21 |
| `qbs_giry.v` | 132 | 9 |
| `normal_centred.v` | 280 | 14 |
| `measure_as_qbs_measure.v` | 197 | 4 |
| `standard_borel.v` | 1,287 | 57 |
| `showcase/bayesian_regression.v` | 426 | 22 |
| **Total** | **6,226** | **322** |

The 322 proofs are 317 `Qed` and 5 `Defined` (the standard Borel witnesses in `measure_qbs_adjunction.v`). **0 Admitted**, 0 custom axioms.

### 4.5 Honest Limitations

The formalization is honest about its scope. These limitations are
documented in the source files and in this report, not hidden:

1. **Monad laws are stated up to equivalence on triples.** On `qbs_prob X`
   the three laws (`qbs_bind_returnl`, `qbs_bind_returnr`, `qbs_bindA`) hold
   up to `qbs_prob_equiv`, not propositional equality. They are equalities
   on the quotient `qbs_quot X` (`quot_bind_returnl`, `quot_bind_returnr`,
   `quot_bindA`), but `monadP X` itself is not quotiented, so its QBS
   structure is on triples.

2. **`qbs_pair_integral_iterated` is iterated integration on a
   specific product measure**, not full Fubini. It works for the
   QBS product measure constructed via the retraction R×R -> R, not for
   arbitrary product measures.

3. **`qbs_pair_integral_factorization` is product-measure
   factorization, not statistical independence.** It states
   `E[fg] = E[f]E[g]` when `f` and `g` depend on disjoint coordinates of
   a product measure, which is a tautology of products. The genuine
   independence factorization is `qbs_integral_indep_factorization`,
   which uses the `qbs_indep` predicate (via `qbs_prob_equiv` on the
   pushforward) and recovers
   `E_p[(phi (f z)) * (psi (g z))] = E[phi (f z)] * E[psi (g z)]`
   from independence of `f` and `g`.

4. **`standard_borel_wit` is a retract-of-R witness**, not the classical
   Polish-space characterization. It matches HKSY Prop. 5, but it is
   packaged as data (`sb_encode`, `sb_decode`, `sb_retractK`) rather than
   as a predicate.

5. **`qbs_normalize` returns `option`** and returns `None` when
   the evidence is zero or infinite. Programs using normalization
   must check or prove the success case; `bayesian_regression.v` does
   so in `program_posterior` (the evidence is the explicit constant `C`).

6. **`qbs_to_giry_inj` and `qbs_to_giry_bind` need a `standard_borel_wit`**
   for the underlying measurable space, as in HKSY Prop. 23.

### 4.6 Remaining Work

1. **Normalizer as QBS morphism.** `qbs_normalize` is well defined on equivalence classes (`qbs_normalize_equiv`), but it is not yet proved to be a QBS morphism from `P(X * R)` into the option of `P(X)`.

2. **Standard Borel closure under countable products.** Extending `pair_standard_borel` to R ~ R^N via Hilbert-cube encoding.

3. **s-Finite kernels.** Integration with the s-finite kernel framework from math-comp analysis (Affeldt, Cohen, Saito).

4. **Standard Borel full round-trip.** The reverse `decode_RRK` is conditional on `no_trailing_ones` of the deinterleaved digit sequences. Formalizing that the exception set has measure zero would complete it.
