# Quasi-Borel Spaces in Rocq

A formalization of Quasi-Borel Spaces (QBS) in Rocq/Coq using
[math-comp analysis](https://github.com/math-comp/analysis),
providing a cartesian-closed category for higher-order probabilistic
programming semantics.

## Overview

**94 lemmas proved, 0 Admitted, 0 custom axioms.**

Quasi-Borel spaces solve a fundamental problem: the category of
measurable spaces is not cartesian closed (no function space object),
which prevents giving semantics to higher-order probabilistic programs.
QBS replaces measurable sets with "random elements" (morphisms from R),
yielding a cartesian-closed category with a well-behaved probability
monad.

This formalization follows:
- The paper ["A Convenient Category for Higher-Order Probability Theory"](https://arxiv.org/abs/1701.02547)
  by Heunen, Kammar, Staton, Yang (LICS 2017)
- The [Isabelle AFP formalization](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html)
  by Hirata, Minamide, Sato

Built on math-comp analysis, in particular the measure theory, kernel,
and Fubini infrastructure. Designed to complement the s-finite kernel
approach to probabilistic programming semantics from
[math-comp/analysis#912](https://github.com/math-comp/analysis/pull/912).

## Files

| File | Qed | Description |
|------|-----|-------------|
| `quasi_borel.v` | 20 | Core QBS record, morphisms, binary products, exponentials (cartesian closure), unit, sigma-algebra |
| `measure_qbs_adjunction.v` | 18 | R/L functors, L-|R adjunction, product preservation, standard Borel definition, full faithfulness |
| `coproduct_qbs.v` | 10 | Binary coproducts (sum types), general coproducts (sigma types), injection morphisms, case analysis |
| `probability_qbs.v` | 29 | Probability monad P(X): return, bind, all 3 monad laws, integration, pushforward infrastructure |
| `pair_qbs_measure.v` | 9 | Product measures via Fubini, marginal integrals, E[fg]=E[f]E[g] for independence |
| `measure_as_qbs_measure.v` | 2 | Embedding classical probability into QBS: Bernoulli, normal, uniform distributions |
| `bayesian_regression.v` | 6 | Bayesian linear regression example: prior, likelihood, predictive distribution |

## Key results

- **Cartesian closure**: `qbs_eval_morph` (evaluation) and `qbs_curry_morph` (currying)
- **Adjunction**: `lr_adj_natural` (L -| R between measurable spaces and QBS)
- **Full faithfulness**: `R_full_faithful_standard_borel` (on standard Borel spaces)
- **Probability monad**: `qbs_monad_left_unit`, `qbs_monad_right_unit`, `qbs_monad_assoc`
- **Fubini**: `qbs_pair_integral_eq` (iterated = joint integration)
- **Independence**: `qbs_integral_indep_mult` (E[fg] = E[f]E[g])

## Requirements

- Rocq 9.0.x
- Math-comp 2.5.x
- Math-comp analysis 1.15.x
- Hierarchy Builder 1.10.x

### Installation

```bash
opam switch create QBS ocaml.4.14.2+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-prover.9.0.0 coq-mathcomp-analysis.1.15.0 coq-hierarchy-builder.1.10.2
```

## Building

```bash
make -j4
```

Or file by file (in dependency order):

```bash
coqc -Q theories QBS theories/quasi_borel.v
coqc -Q theories QBS theories/measure_qbs_adjunction.v
coqc -Q theories QBS theories/coproduct_qbs.v
coqc -Q theories QBS theories/probability_qbs.v
coqc -Q theories QBS theories/pair_qbs_measure.v
coqc -Q theories QBS theories/measure_as_qbs_measure.v
coqc -Q theories QBS theories/bayesian_regression.v
```

## Design decisions

**Bundled `Record qbs` (not HB typeclass).** The exponential `expQ X Y` has
carrier = bundled morphisms `qbs_hom X Y`, a sigma type. This can't be
expressed as an HB instance on bare function types.

**Pointwise `monadP_random'` for the QBS structure.** The probability monad
uses a pointwise condition (each `qbs_prob_alpha(beta(r))` is individually
in Mx) rather than the strong shared-alpha condition from Isabelle. The
strong condition (`qbs_morph_strong`) is available as an additional property
for bind.

**Parametric `qbs_return`.** Return takes an explicit measure parameter,
enabling the left unit law. All returns with the same point are equivalent
regardless of measure (proved as `qbs_return_equiv`).

**Direct product integration on mR x mR.** Product measures use
`product_measure1` from math-comp analysis directly on the product
measurable space, avoiding the need for a standard Borel isomorphism
R ~ R x R.

## References

- C. Heunen, O. Kammar, S. Staton, H. Yang.
  [A Convenient Category for Higher-Order Probability Theory](https://arxiv.org/abs/1701.02547).
  LICS 2017.
- M. Hirata, Y. Minamide, T. Sato.
  [Quasi-Borel Spaces (Isabelle AFP)](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html). 2022.
- R. Affeldt, C. Cohen, A. Saito.
  [Semantics of Probabilistic Programs using s-Finite Kernels in Coq](https://github.com/math-comp/analysis/pull/912). 2023.

## License

BSD-3-Clause
