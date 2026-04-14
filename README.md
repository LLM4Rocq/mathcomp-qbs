# Quasi-Borel Spaces in Rocq

[Blueprint](https://llm4rocq.github.io/mathcomp-qbs/)

This formalization was developed with
[Claude Opus 4.6](https://claude.ai/claude-code) using
[Rocq-MCP](https://github.com/LLM4Rocq/rocq-mcp) for interactive
proof development. Claude wrote all ~17,000 lines of Rocq code (700+
proofs, 0 Admitted) with guidance from a human collaborator who
provided mathematical direction and design decisions.

A formalization of Quasi-Borel Spaces (QBS) in Rocq using
[math-comp analysis](https://github.com/math-comp/analysis),
providing a cartesian-closed category for higher-order probabilistic
programming semantics.

## Overview

**700+ proofs, 0 Admitted, 0 custom axioms, ~17,000 lines across 30 files.**

> **Note**: This is the `ppl` branch, extending `main` with a
> higher-order PPL, s-finite kernel bridge, quotient-based monad,
> and fallback-free first-order semantics.
> The `main` branch (12 files, 410 proofs) contains the QBS
> foundations + Bayesian regression showcase for mathcomp submission.

Quasi-Borel spaces solve a fundamental problem: the category of
measurable spaces is not cartesian closed, which prevents giving
semantics to higher-order probabilistic programs. QBS replaces
measurable sets with "random elements" (morphisms from R), yielding a
cartesian-closed category with a well-behaved probability monad.

This formalization follows:
- ["A Convenient Category for Higher-Order Probability Theory"](https://arxiv.org/abs/1701.02547)
  by Heunen, Kammar, Staton, Yang (LICS 2017)
- The [Isabelle AFP formalization](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html)
  by Hirata, Minamide, Sato

## Files

### Core QBS theory

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `quasi_borel.v` | 750 | 47 | HB mixin/structure, morphisms, products, exponentials, cartesian closure (β/η rules) |
| `measure_qbs_adjunction.v` | 525 | 27 | L⊣R hom-set bijection, standard Borel, full faithfulness |
| `coproduct_qbs.v` | 720 | 25 | Binary/general coproducts, dependent products, list type |
| `probability_qbs.v` | 1,328 | 63 | Probability monad: return, bind, 3 monad laws (setoid), strength, normalizer |
| `pair_qbs_measure.v` | 604 | 17 | Product measures via R≅R×R, iterated integration, factorization |
| `qbs_prob_quot.v` | 333 | 17 | Setoid quotient for probability triples |
| `measure_as_qbs_measure.v` | 289 | 10 | Normal, Bernoulli, uniform distributions, E[Normal]=μ |

### Bridges and analysis

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `qbs_giry.v` | 201 | 12 | QBS↔Giry monad connection, integral correspondence |
| `qbs_kernel.v` | 449 | 21 | QBS↔s-finite kernel bridge, Dirac kernels, composition |
| `standard_borel.v` | 1,282 | 60 | R↔(0,1) via atan, digit interleaving, R≅R×R |
| `normal_algebra.v` | 1,310 | 77 | Product of Gaussians, normalizing constant computation |

### Higher-order PPL semantics

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `ppl_qbs.v` | 1,032 | 32 | Intrinsically-typed PPL with function types, sums, sampling, kernel-based bind |
| `ppl_kernel.v` | 312 | 20 | Bridge: first-order PPL programs lift to s-finite kernels |
| `ppl_coincidence.v` | 568 | 12 | First-order QBS denotation = kernel composition (kcomp) |

### Kernel bridge and Fubini

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `measurable_prob.v` | 482 | 18 | Measurable structure on pprobability, evaluation maps |
| `measurable_normal_prob_sigma.v` | 141 | 6 | `m ↦ normal_prob m σ` is measurable (unconditional, via Tonelli) |
| `qbs_fubini.v` | 455 | 13 | Fubini on QBS via kernel measurability analysis (conditional on kernel measurability) |
| `qbs_strong_kernel.v` | 612 | 15 | Strengthened strong condition → probability kernel |
| `qbs_bind_kernel.v` | 414 | 6 | Kernel-based bind without diagonal proofs (conditional on `mu_kb_sigma_additive`) |
| `qbs_kernel_bridge.v` | 463 | 15 | Wiring: `qbs_morphism_strong_meas` + `mu_kb_sigma_additive` → kernel bind and monad laws |
| `monadP_analysis.v` | 225 | 0 | Impact analysis of monadP_random strengthening |

### Quotient monad and first-order semantics

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `qbs_quotient.v` | 305 | 13 | Proper mathcomp quotient `{eq_quot qbs_prob_equiv}`, monad laws as equalities |
| `qbs_quot_bind.v` | 324 | 12 | Giry-level bind on quotient for standard Borel, sigma-additivity via MCT |
| `qps_bind_exists_std_borel.v` | 392 | 15 | `qps_bind_exists` proved for strong/const/return + standard Borel cases |
| `qps_bind_wd_proof.v` | 170 | 2 | `qps_bind_classical_wd` for standard Borel via Giry bridge |
| `ppl_quot_semantics.v` | 847 | 27 | Fallback-free `expr_sem_quot` (conditional on `qps_bind_exists`) |
| `ppl_fo_semantics.v` | 876 | 28 | First-order PPL: all types standard Borel, no fallback (WIP) |
| `expr_strong_meas.v` | 345 | 28 | Formal proof: `qbs_return` CANNOT satisfy `monadP_random` (strong) |

### Showcase

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `showcase/bayesian_regression.v` | 926 | 34 | Bayesian linear regression with explicit normalizing constant |
| `showcase/ppl_examples.v` | 564 | 20 | Distributions over function spaces, Bayesian inference over linear functions |

## Key results

- **Cartesian closure**: `qbs_morphism_eval`, `qbs_morphism_curry`,
  `qbs_morphism_curry_eval` (β), `qbs_morphism_eval_curry` (η)
- **L⊣R hom-set bijection**: `lr_adj_iff` (a single-object
  biconditional, not a full categorical naturality theorem)
- **Full faithfulness**: `R_full_faithful_standard_borel`
- **Probability monad**: `qbs_bind_returnl`, `qbs_bind_returnr`, `qbs_bindA`
- **Iterated integration on product measures**: `qbs_pair_integral_iterated`
  (Fubini for the specific QBS product measure construction)
- **Product-measure factorization**: `qbs_pair_integral_factorization`
  (E[fg] = E[f]E[g] when f, g depend on disjoint coordinates of a
  product measure; this is a tautology of products, not a general
  independence theorem)
- **QBS↔Giry**: `qbs_to_giry`, `qbs_integral_giry`
- **R≅R×R**: `pair_standard_borel`, `encode_RRK`
- **Normalizer**: `qbs_normalize`, `qbs_normalize_total`, `qbs_normalize_integral`
- **Distributions**: `qbs_expect_normal`, `qbs_expect_bernoulli`, `qbs_expect_uniform`
- **Bayesian regression**: `evidence_value`, `program_integrates_to_1`
- **Normal density**: `normal_pdf_times` (product of Gaussians)
- **S-finite kernel bridge**: `qbs_prob_sfinite`, `qbs_morph_kdirac`, `kernel_integration`
- **Measurability of normal sampling**: `measurable_normal_prob_sigma`
  (unconditional: `m ↦ normal_prob m σ` is measurable, proved via Tonelli)
- **Kernel-based bind**: `qbs_bind_kernel_meas`
  (conditional on `qbs_morphism_strong_meas` and `mu_kb_sigma_additive`;
  eliminates diagonal proofs but requires the strengthened strong morphism
  condition and sigma-additivity of kernel composition)
- **First-order coincidence**: `ppl_coincidence` (QBS denotation corresponds
  to kernel composition for return and sampling constructors; conditional on
  denotation equation hypotheses and measure extraction measurability)
- **Higher-order PPL**: `expr`, `expr_morphism` (function types via QBS exponentials)
- **Quotient monad**: `qbs_quotient` — proper mathcomp quotient with monad
  laws as genuine equalities (not setoid), using `generic_quotient.v`
- **Return impossibility**: `expr_strong_meas` — formal proof that
  `qbs_return` cannot satisfy `monadP_random` (strong) for non-trivial
  types, justifying the quotient approach
- **Fallback-free PPL**: `expr_sem_quot` — all bind cases handled
  uniformly via quotient bind (conditional on `qps_bind_exists`);
  `qps_bind_exists` proved for strong, constant, return, and
  standard Borel cases; the general higher-order case requires
  HKSY Theorem 22.4 (not yet formalized)

## Limitations

The formalization is honest about its scope. Key limitations:

- **Probability monad uses the pointwise random-element condition**
  (`monadP_random_pw`), not the strong shared condition. As a result,
  `qbs_bind` requires an explicit diagonal-randomness proof and the
  three monad laws (`qbs_bind_returnl`, `qbs_bind_returnr`, `qbs_bindA`)
  are stated up to `qbs_prob_equiv` (setoid equivalence). Congruence
  for `qbs_bind` is provided in special cases (`qbs_bind_equiv_l`,
  `qbs_bind_strong_equiv_l`, `qbs_bind_equiv_l_return`); a fully
  unconditional congruence would require disintegration.

- **`lr_adj_iff` is a hom-set bijection**, not a full categorical
  naturality statement. The functorial naturality squares are not
  proved.

- **Standard Borel** is defined via the existence of an
  encode/decode pair, not via the classical Polish-space
  characterization.

- **`qbs_normalize` returns `option`** and may return `None` when
  the evidence is zero or infinite. Programs using normalization
  must check or prove the success case.

- **PPL bind faithfulness**: `expr_sem` dispatches non-canonical bind
  forms to `morph_bind_fallback` (a constant placeholder). The quotient
  variant `expr_sem_quot` (in `ppl_quot_semantics.v`) eliminates the
  fallback entirely, but is conditional on `qps_bind_exists` — proved
  for strong, constant, return, and standard Borel target cases.
  For higher-order target types (`expQ`), `qps_bind_exists` requires
  HKSY Theorem 22.4 (not yet formalized). The first-order fragment
  (`ppl_fo_semantics.v`, WIP) has no fallback for all first-order types.

- **The quotient monad** (`qbs_quotient.v`) gives monad laws as genuine
  equalities. On the quotient, `qps_bind_classical_wd` (well-definedness)
  is proved for standard Borel types via the Giry bridge. The general
  case requires `kernel_diagonal_identity` (disintegration / HKSY 22.4).

- **`qbs_expect_normal`** (E[Normal(μ,σ)] = μ) currently requires
  three analytic hypotheses (identity integrability against
  normal_prob, odd-function integrability, odd integral = 0). These
  are standard analytic facts not yet in mathcomp-analysis.

## Requirements

- Rocq 9.0.x -- 9.1.x
- Math-comp 2.5.x
- Math-comp analysis 1.15.x -- 1.16.x
- Hierarchy Builder 1.10.x
- Math-comp algebra-tactics 1.2.x (for `ring`/`field`)

### Installation

```bash
opam install coq-mathcomp-analysis coq-mathcomp-algebra-tactics
```

## Building

```bash
coq_makefile -f _CoqProject -o Makefile
make -j4
```

## References

- C. Heunen, O. Kammar, S. Staton, H. Yang.
  [A Convenient Category for Higher-Order Probability Theory](https://arxiv.org/abs/1701.02547).
  LICS 2017.
- M. Hirata, Y. Minamide, T. Sato.
  [Quasi-Borel Spaces (Isabelle AFP)](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html).
  2022.
- R. Affeldt, C. Cohen, A. Saito.
  [Semantics of Probabilistic Programs using s-Finite Kernels in Coq](https://github.com/math-comp/analysis/pull/912).
  2023.

## License

CeCILL-C
