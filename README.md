# Quasi-Borel Spaces in Rocq

[Blueprint](https://llm4rocq.github.io/mathcomp-qbs/)

This formalization was developed with
[Claude Opus 4.6](https://claude.ai/claude-code) using
[Rocq-MCP](https://github.com/LLM4Rocq/rocq-mcp) for interactive
proof development. Claude wrote all 8,913 lines of Rocq code (412
proofs, 0 Admitted) with guidance from a human collaborator who
provided mathematical direction and design decisions.

A formalization of Quasi-Borel Spaces (QBS) in Rocq using
[math-comp analysis](https://github.com/math-comp/analysis),
providing a cartesian-closed category for higher-order probabilistic
programming semantics.

## Overview

**412 proofs, 0 Admitted, 0 custom axioms, 8,913 lines across 13 files.**

> **Note**: A higher-order PPL with denotational semantics in QBS
> (`ppl_qbs.v`, `ppl_kernel.v`, `showcase/ppl_examples.v`) is
> developed on the [`ppl`](../../tree/ppl) branch as future work.
> See `PLAN.md` for the roadmap.

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
| `quasi_borel.v` | 714 | 36 | HB structure via Section+`HB.instance`, morphisms, products, exponentials, cartesian closure (β/η) |
| `measure_qbs_adjunction.v` | 520 | 27 | L⊣R hom-set bijection, standard Borel (`{mfun}`), full faithfulness |
| `coproduct_qbs.v` | 716 | 25 | Binary/general coproducts, dependent products, list type |
| `probability_qbs.v` | 1,328 | 63 | Probability monad: return, bind, 3 monad laws (setoid), strength, normalizer |
| `pair_qbs_measure.v` | 604 | 17 | Product measures via R≅R×R, iterated integration, factorization |
| `qbs_prob_quot.v` | 312 | 17 | Setoid quotient for probability triples |
| `measure_as_qbs_measure.v` | 287 | 10 | Normal, Bernoulli, uniform distributions, E[Normal]=μ |
| `qbs_quotient.v` | 310 | 13 | Mathcomp quotient type for QBS probability spaces |

### Bridges and analysis

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `qbs_giry.v` | 194 | 12 | QBS↔Giry monad connection, integral correspondence |
| `qbs_kernel.v` | 419 | 21 | QBS↔s-finite kernel bridge, Dirac kernels, composition |
| `standard_borel.v` | 1,276 | 60 | R↔(0,1) via atan, digit interleaving, R≅R×R |
| `normal_algebra.v` | 1,307 | 77 | Product of Gaussians, normalizing constant computation |

### Showcase

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `showcase/bayesian_regression.v` | 926 | 34 | Bayesian linear regression with explicit normalizing constant |

## Key results

- **Cartesian closure**: `qbs_eval`, `qbs_curry`, `qbs_curry_morph`,
  `qbs_curry_eval` (β), `qbs_eval_curry` (η)
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
