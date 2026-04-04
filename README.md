# Quasi-Borel Spaces in Rocq

A formalization of Quasi-Borel Spaces (QBS) in Rocq using
[math-comp analysis](https://github.com/math-comp/analysis),
providing a cartesian-closed category for higher-order probabilistic
programming semantics.

## Overview

**332 proofs, 0 Admitted, 0 custom axioms, 6,820 lines across 11 files.**

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
| `quasi_borel.v` | 714 | 45 | HB mixin/structure, morphisms, products, exponentials, cartesian closure |
| `measure_qbs_adjunction.v` | 238 | 18 | L-|R adjunction, standard Borel, full faithfulness |
| `coproduct_qbs.v` | 681 | 22 | Binary/general coproducts, dependent products, list type |
| `probability_qbs.v` | 737 | 35 | Probability monad: return, bind, 3 monad laws, strength |
| `pair_qbs_measure.v` | 537 | 16 | Product measures via R≅R×R, Fubini, independence |
| `qbs_prob_quot.v` | 331 | 17 | Setoid quotient for probability triples |
| `measure_as_qbs_measure.v` | 176 | 6 | Normal, Bernoulli, uniform distributions |

### Bridges and analysis

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `qbs_giry.v` | 208 | 12 | QBS↔Giry monad connection, integral correspondence |
| `standard_borel.v` | 1,256 | 60 | R↔(0,1) via atan, digit interleaving, R≅R×R |
| `normal_algebra.v` | 1,298 | 77 | Product of Gaussians, normalizing constant computation |

### Showcase

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `showcase/bayesian_regression.v` | 644 | 24 | Bayesian linear regression (matching Isabelle AFP) |

## Key results

- **Cartesian closure**: `qbs_morphism_eval`, `qbs_morphism_curry`
- **L-|R adjunction**: `lr_adj_natural`
- **Full faithfulness**: `R_full_faithful_standard_borel`
- **Probability monad**: `qbs_bind_returnl`, `qbs_bind_returnr`, `qbs_bindA`
- **Fubini**: `qbs_pair_integralE`
- **Independence**: `qbs_integral_indep_mult` (E[fg] = E[f]E[g])
- **QBS↔Giry**: `qbs_to_giry`, `qbs_integral_giry`
- **R≅R×R**: `pair_standard_borel`, `encode_RRK`
- **Bayesian regression**: `evidence_value`, `program_integrates_to_1`
- **Normal density**: `normal_pdf_times` (product of Gaussians)

## Requirements

- Rocq 9.0.x
- Math-comp 2.5.x
- Math-comp analysis 1.15.x
- Hierarchy Builder 1.10.x
- Math-comp algebra-tactics 1.2.x (for `ring`/`field`)

### Installation

```bash
opam install coq-mathcomp-analysis.1.15.0 coq-mathcomp-algebra-tactics
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
