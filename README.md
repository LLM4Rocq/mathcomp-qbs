# Quasi-Borel Spaces in Rocq

[Blueprint](https://llm4rocq.github.io/mathcomp-qbs/)

This formalization was developed by Claude (Opus 5.5, with Sonnet 5.5
subagents), using
[rocq-mcp-evolve](https://github.com/LLM4Rocq/rocq-mcp-evolve) for
interactive proof development, with guidance from a human collaborator
who provided the mathematical direction and the design decisions.

A formalization of Quasi-Borel Spaces (QBS) in Rocq using
[math-comp analysis](https://github.com/math-comp/analysis),
providing a cartesian-closed category for higher-order probabilistic
programming semantics.

## Overview

This formalization follows:
- ["A Convenient Category for Higher-Order Probability Theory"](https://arxiv.org/abs/1701.02547)
  by Heunen, Kammar, Staton, Yang (LICS 2017), referred to as HKSY
- The [Isabelle AFP formalization](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html)
  by Hirata, Minamide, Sato

## Files and key results

### Core QBS theory

| File | Result | Paper | Rocq |
|------|--------|-------|------|
| `measurable_aux.v` | Auxiliary measurability lemmas | — | `measurable_invr`, `measurable_fun_nat_discrete`, `measurable_truncn` |
| `quasi_borel.v` | Cartesian closure | HKSY Prop. 16 | `qbs_curry_morph`, `qbs_uncurry`, `qbs_curryK` (β), `qbs_uncurryK` (η), `qbs_curry_morph_uniq` |
| | L ⊣ R, with L X = (X, `sigma_Mx`) | HKSY Prop. 15(1) | `qbs_morphism_measurableP` |
| | Lattice of QBS structures, empty QBS | — | `qbs_inf`, `qbs_top`, `qbs_bot`, `emptyQ` |
| `measure_qbs_adjunction.v` | Counit of L ⊣ R | HKSY Prop. 15(1) | `adjunction_counit` |
| | R is full on standard Borel domains | HKSY Prop. 15(2) | `measQ_full`, `sigma_Mx_standard_borelP` |
| | Galois connection | — | `sigma_of_Mx_of` |
| `coproduct_qbs.v` | Countable coproducts | HKSY Prop. 17 | `sigmaQ`, `sigma_case`, `sigma_case_eta` |
| | Lists, recursion as a morphism | HKSY Sec. IV | `qbs_nil`, `qbs_cons`, `list_rec`, `qbs_morphism_list_rec`, `list_rec_hom`, `seq_of_listK`, `list_of_seqK` |
| `standard_borel.v` | R ≅ R × R (retraction) | HKSY Prop. 5 | `pair_standard_borel`, `encode_RRK` |

### Probability

| File | Result | Paper | Rocq |
|------|--------|-------|------|
| `probability_qbs.v` | Probabilities: quotient of the pairs (alpha, mu), equal iff equal on `sigma_Mx` sets | HKSY Sec. V | `probQ`, `preprob_equiv`, `qbs_eqP` |
| | Law, integration, expectation, variance | HKSY eq. (3) | `qbs_integral_law`, `qbs_expectE` (expectation is `'E` on the law), `qbs_integrableP`, `qbs_integral_le`, `qbs_variance_affine` |
| `qbs_monad.v` | Monad laws (equalities) | HKSY Sec. V | `qbs_return`, `qbs_bind`, `qbs_bind_returnl`, `qbs_bind_returnr`, `qbs_bindA`, `qbs_map`, `qbs_join` |
| | Strength and its laws | HKSY Sec. V | `strength`, `strength_snd`, `strength_assoc`, `strength_return`, `strength_join` |
| | Integration is a morphism, internal bind | HKSY Sec. V-C, Thm. 21 | `ge0_qbs_morphism_integral`, `qbs_bind_internal` |
| | Commutativity | HKSY Prop. 22(2) | `qbs_prod_comm`, `qbs_bind_comm` |
| `qbs_normalize.v` | Normaliser, as a morphism into P(X) + 1 | HKSY Sec. VI | `normalize`, `normalize_event`, `normalize_prob_event_mk`, `qbs_morphism_normalize`, `normalizeQ` |
| `qbs_monad_integral.v` | Signed integrals through return and bind | — | `qbs_integral_bind`, `qbs_morphism_integral` |
| `qbs_giry.v` | QBS ↔ Giry | HKSY Prop. 22(3), 23 | `to_giry`, `qbs_integral_giry`, `to_giry_inj`, `to_giry_bind` |
| `pair_qbs_measure.v` | Fubini, independence, variance of independent sums | — | `qbs_prod_iterated`, `indep_rect` (product rule), `qbs_integral_indepM` (E[fg] = E[f]E[g]), `qbs_prod_varianceD` |
| `normal_centred.v` | Mean of the normal law | — | `integral_normal_mean` |
| `measure_as_qbs_measure.v` | Normal, Bernoulli and uniform distributions | — | `qbs_expect_normal`, `qbs_expect_bernoulli`, `qbs_bernoulli_event`, `qbs_expect_interval_uniform`, `qbs_uniformQ : intervalQ -> P(R)` |

### Showcase

| File | Result | Paper | Rocq |
|------|--------|-------|------|
| `showcase/bayesian_regression.v` | Bayesian regression: explicit Gaussian posterior on R => R, closed-form evidence | HKSY Sec. VI | `program_posterior` (`program = Some posterior`), `wprior_evidence` |

## Limitations

- **Standard Borel** is defined via the existence of an
  encode/decode pair, not via the classical Polish-space
  characterization.

- **`normalize` returns `option`**: it returns `None` when the
  evidence is zero or infinite (`normalize_sum` is the same map into
  P(X) + 1).

- **Not formalised from HKSY**: the de Finetti theorem and the
  random-functions example.

## Requirements

- Rocq 9.2 or 9.3 (tested with 9.2.0; 9.2 is needed for `Abbreviation`)
- MathComp 2.6.x
- MathComp analysis 1.18.x
- Hierarchy Builder 1.10.x
- MathComp algebra-tactics (for `ring`/`field`). No release supports
  MathComp 2.6 yet: `coq-qbs.opam` pins a commit of its `master` branch
  (`pin-depends`), whose opam file still bounds `coq-mathcomp-ssreflect`
  below 2.5, hence `OPAMIGNORECONSTRAINTS` below.

### Installation

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
OPAMIGNORECONSTRAINTS=coq-mathcomp-ssreflect \
  opam install --deps-only .
```

## Building

```bash
rocq makefile -f _CoqProject -o Makefile
make -j4
```

`REPORT.md` describes the formalization in detail, and the
[blueprint](https://llm4rocq.github.io/mathcomp-qbs/) maps the
mathematical statements to the Rocq lemmas.

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
