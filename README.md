# Quasi-Borel Spaces in Rocq

[Blueprint](https://llm4rocq.github.io/mathcomp-qbs/)

This formalization was developed with
[Claude Opus 4.6](https://claude.ai/claude-code) using
[Rocq-MCP](https://github.com/LLM4Rocq/rocq-mcp) for interactive
proof development, with guidance from a human collaborator who
provided mathematical direction and design decisions. It was then
ported to MathComp 2.6 / analysis 1.18 and refactored (notably the
probability monad, now the one of HKSY) with Claude Opus 5.5 using
[rocq-mcp-evolve](https://github.com/LLM4Rocq/rocq-mcp-evolve).

A formalization of Quasi-Borel Spaces (QBS) in Rocq using
[math-comp analysis](https://github.com/math-comp/analysis),
providing a cartesian-closed category for higher-order probabilistic
programming semantics.

## Overview

**411 proofs, 0 Admitted, 0 custom axioms, 7,402 lines across 14 files.**

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
  by Heunen, Kammar, Staton, Yang (LICS 2017), referred to as HKSY
- The [Isabelle AFP formalization](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html)
  by Hirata, Minamide, Sato

## Files

### Core QBS theory

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `quasi_borel.v` | 948 | 61 | HB structure, morphisms, products, exponentials, cartesian closure, the L functor (`qbs_meas`) and L ⊣ R, lattice of QBS structures, empty QBS |
| `measure_qbs_adjunction.v` | 380 | 20 | Counit of L ⊣ R, standard Borel spaces, R is full on standard Borel domains, order adjunction |
| `coproduct_qbs.v` | 864 | 45 | Binary and countable coproducts (HKSY Prop. 17), dependent products, lists with cons and recursion, concrete morphisms |
| `standard_borel.v` | 1,287 | 57 | R ≅ (0,1) via atan, digit interleaving, R ≅ R × R |

### Probability

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `probability_qbs.v` | 689 | 47 | Probability triples, equivalence, integration and integrability, law, expectation, variance |
| `qbs_monad.v` | 705 | 58 | The HKSY probability monad: return, bind, laws, map, join, strength and its laws, commutativity |
| `qbs_normalize.v` | 267 | 18 | Normalisation of weighted probabilities (HKSY Sec. VI), as a morphism P(X × R) → P(X) + 1 |
| `qbs_monad_integral.v` | 201 | 11 | Integrals, integrability and variance through return and bind |
| `qbs_quotient.v` | 194 | 19 | Quotient of probability triples; monad laws as equalities |
| `qbs_giry.v` | 132 | 9 | Comparison with the Giry monad |
| `pair_qbs_measure.v` | 770 | 21 | Product measures via R ≅ R × R, iterated integration, independence |
| `normal_centred.v` | 280 | 14 | Centred first moment of the normal density, change of variables for `normal_prob` |
| `measure_as_qbs_measure.v` | 259 | 9 | Normal, Bernoulli and uniform (on any [a, b]) distributions, their expectations, Bernoulli law |

### Showcase

| File | Lines | Proofs | Description |
|------|------:|-------:|-------------|
| `showcase/bayesian_regression.v` | 426 | 22 | Bayesian linear regression (HKSY Sec. VI) with closed-form posterior |

## Key results

- **Cartesian closure**: `qbs_curry_morph`, `qbs_uncurry`, `qbs_curryK` (β),
  `qbs_uncurryK` (η), `qbs_curry_morph_uniq`
- **L ⊣ R** (HKSY Prop. 15(1)): `qbs_morphism_measurableP`, where
  `qbs_meas X` is X with the sigma-algebra `sigma_Mx`; counit
  `adjunction_counit`
- **R is full on standard Borel domains**: `R_qbs_full`,
  `sigma_Mx_standard_borel`
- **Countable coproducts** (HKSY Prop. 17): `sigmaQ`, `sigma_case`,
  `sigma_case_uniq`
- **Probability monad**: `qbs_return`, `qbs_bind`, laws
  `qbs_bind_returnl`, `qbs_bind_returnr`, `qbs_bindA`; `monadP_map`,
  `qbs_join`, `qbs_strength` with its laws `qbs_strength_snd`,
  `qbs_strength_assoc`, `qbs_strength_return`, `qbs_strength_join`;
  internal bind `qbs_bind_internal`
  (HKSY Thm. 21); commutativity `qbs_pairP_comm`, `qbs_bind_comm`
  (HKSY Prop. 22(2))
- **Quotient**: on the quotient type `qbs_quot` the monad laws hold
  as equalities
- **QBS ↔ Giry**: `qbs_to_giry`, `qbs_integral_giry`, and on standard
  Borel spaces `qbs_to_giry_inj`, `qbs_to_giry_bind`
- **Integration**: `qbs_integral_law`, `qbs_expectE` (expectation is
  `'E` on the law)
- **Independence**: `qbs_indep_rect` (product rule),
  `qbs_integral_indep_factorization` (E[fg] = E[f]E[g])
- **R ≅ R × R**: `pair_standard_borel`, `encode_RRK`
- **Normaliser**: `qbs_normalize`, `qbs_normalize_event`,
  `qbs_normalize_equiv`; as a morphism into P(X) + 1:
  `qbs_normalize_morphism`, `qbs_normalizeQ`
- **Lists**: `qbs_nil`, `qbs_cons`, recursion `list_rec` as a morphism
  (`qbs_morphism_list_rec`, internal `list_rec_hom`), bijection with
  `seq` (`seq_of_listK`, `list_of_seqK`)
- **Order structure**: meet/top/bottom of QBS structures (`qbs_infT`,
  `qbs_topT`, `qbs_botT`), empty QBS `emptyQ`, Galois connection
  `sigma_of_Mx_of`, functions out of `natQ`/`boolQ` are morphisms
- **Integration**: `qbs_integrableP`, `qbs_integral_le`,
  `qbs_variance_affine`, signed `qbs_integral_bind`
- **Distributions**: `qbs_expect_bernoulli`, `qbs_bernoulli_law`,
  `qbs_expect_interval_uniform`, `qbs_expect_normal`
- **Bayesian regression**: `program_posterior` (the program normalises
  to an explicit Gaussian posterior on functions R => R),
  `wprior_evidence` (closed-form evidence)

## Limitations

- **Monad laws hold up to `qbs_prob_equiv`** on the raw triples
  (`monadP`); they are equalities on the quotient `qbs_quot`.

- **Standard Borel** is defined via the existence of an
  encode/decode pair, not via the classical Polish-space
  characterization.

- **`qbs_normalize` returns `option`**: it returns `None` when the
  evidence is zero or infinite (`qbs_normalize_sum` is the same map into
  P(X) + 1).

- **Not formalised from HKSY**: the de Finetti theorem and the
  random-functions example.

## Requirements

- Rocq 9.2 (tested with 9.2.0; the opam file allows 9.0 -- 9.3)
- Math-comp 2.6.x
- Math-comp analysis 1.18.x
- Hierarchy Builder 1.10.x
- Math-comp algebra-tactics (for `ring`/`field`). No release supports
  Math-comp 2.6 yet: install the `master` branch with its
  `coq-mathcomp-ssreflect` upper bound relaxed.

### Installation

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-mathcomp-analysis.1.18.0
opam pin add coq-mathcomp-algebra-tactics <path-to-patched-algebra-tactics>
```

## Building

```bash
rocq makefile -f _CoqProject -o Makefile
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
