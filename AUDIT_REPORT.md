# QBS Codebase Style Audit — Consolidated Punch List

**Date:** 2026-05-05
**Scope:** 12 theory files, ~7940 lines, audited per
`mathcomp-rocq-guide` (sections 22-33 + playbook).
**Method:** 8 parallel agents producing per-finding punch lists keyed
to section numbers in `~/.claude/skills/mathcomp-rocq-guide/reference.md`.

This supersedes the previous AUDIT_REPORT.md (which dates to before
the recent cleanup commits a166c8e..a295144).

---

## 0. Density summary

| File | Lines | Findings | Per 100 LoC |
|---|---|---|---|
| quasi_borel.v | 708 | ~55 | 7.8 |
| coproduct_qbs.v | 713 | ~85 | 11.9 |
| measure_qbs_adjunction.v | 507 | ~57 | 11.2 |
| qbs_giry.v | 193 | ~24 | 12.4 |
| measure_as_qbs_measure.v | 287 | ~32 | 11.1 |
| pair_qbs_measure.v | 601 | ~28 | 4.7 |
| probability_qbs.v | 1324 | ~85 | 6.4 |
| normal_algebra.v | 1291 | ~85 | 6.6 |
| standard_borel.v | 1276 | ~85 | 6.7 |
| qbs_kernel.v | 418 | ~30 | 7.2 |
| qbs_prob_quot.v | 312 | ~22 | 7.1 |
| qbs_quotient.v | 310 | ~20 | 6.5 |

**Total: ~600 findings across 7940 lines (~7.5 / 100 LoC).**

The codebase is in moderate shape post-cleanup-passes: structural rules
(line length, `Open Scope`, naming heads) are mostly met. **Residual
dominant problems are idiomatic concision and incomplete migrations.**

---

## Tier 1 — Cross-cutting fixes (do first; each kills 20+ findings)

### CC-1. Add `Import` clauses; drop qualifiers and Local-Notation workarounds
- **measure_qbs_adjunction.v:230-232** — three `Local Notation` aliases
  (`truncnP`, `interval_open`, `contractK`) papering over missing imports.
  Add `Import archimedean.Num.Theory.`,
  `From mathcomp Require Import num_normedtype.`, drop the aliases.
- **probability_qbs.v:1241-1272** — six `Radon_Nikodym_SigmaFinite.X`
  qualified uses; add `Import charge.Radon_Nikodym_SigmaFinite.`
- **qbs_prob_quot.v:31** — `Import boolp.` placed AFTER the standard
  preamble; move into preamble.

### CC-2. Add `Implicit Types` declarations (every file is missing them)
**Single biggest win in the codebase.** Adding
`Implicit Types (X Y : qbsType R) (p : qbs_prob _) ...` (file-appropriate
set) at section top would shave ~150 annotation lines from
probability_qbs.v alone, and ~30+ each from normal_algebra.v,
standard_borel.v, measure_qbs_adjunction.v.

### CC-3. Fix `Variable (X : foo)` → `Variables` plural form (§14)
- **quasi_borel.v** lines 101, 110, 267, 374-375, 431, 492, 632
- **probability_qbs.v** 1078-1079, 1144

### CC-4. Finish `@`-discipline migration (§25)
The recent commit 6f421b8 started but didn't finish:
- **quasi_borel.v:79-80, 133, 142** — record-field type and 2 proof
  sites still use `@qbs_Mx R X`.
- **coproduct_qbs.v** — 30+ `@qbs_Mx R X` / `@qbs_morphism R X Y` sites
  in lemma statements.
- **probability_qbs.v** — 28 sites still use `@qbs_Mx R X` form.

Strip `@`, switch to keyed-implicit form `qbs_Mx (X := X)`, OR drop
entirely if `R, X` already implicit.

### CC-5. Fix 2-subgoal bullets (§27.8) — pure mechanical
- **quasi_borel.v** 159-161, 222-225, 650-651
- **coproduct_qbs.v** multiple
- **standard_borel.v** 418-425, 589-611, 674-704, 756-766, 1219-1236
- **normal_algebra.v** 87-101
- **measure_qbs_adjunction.v** 265-280

Replace `- foo. - bar.` with two-space indent + bare statement.

---

## Tier 2 — High-impact per-file fixes

### probability_qbs.v
- **L1196-1203** stray blank line in `qbs_normalize_total`; closing
  `rewrite -integral_cst //=.` not `by`-prefixed.
- **L74, L79** classic `move=> H ... ; rewrite H` antipattern (§27.1)
  in trivial reflexivity/transitivity proofs.
- **L421-424, L776-779, L989-992, L1014-1020** — eight
  `have -> : X by [].` over definitional equalities (§22.1). Per
  playbook, deletable.
- **15+ post-`End` `Arguments ... : clear implicits.`** (L206-209,
  L373-375, L531-532, L630-635, L892, L1063, L1298-1299) duplicate
  in-section declarations — playbook §3 false-positive risk; verify each.
- **L1234-1235** — `(normalize_mu ... : measure mR R)` ascription on
  canonical instance — drop.

### coproduct_qbs.v
- **§8 violation** — curly-brace sub-proofs at L247, L252, L257, L264.
  Replace with `have heq: ... by ...`.
- **§14 violation** — capital `H`/`Hh`/`abs` names at L63-64, L355,
  L359, L361, L424, L430, L434, L436, L458. Rename.
- **L107, L110, L123-124, L363, L438** — `exfalso; exact: ...`;
  replace with `by case: ...`.
- **L361-362, L436-437** — `have -> : H = erefl by exact: Prop_irrelevance. by [].`
  collapses to `by rewrite (Prop_irrelevance H erefl).`
- **§27.6** — 8+ blocks of form
  `have foo : forall i, P. move=> i; exact: ...` should be
  `have foo : forall i, P := fun i => ...` (saves ~24 lines).

### standard_borel.v
- **L1226-1233** — five consecutive
  `rewrite (_ : E = E'); last by [].` blocks, all definitional.
  Removable; ~10 lines disappear.
- **L1092** — `by destruct xy.` — replace with `by case: xy.`
- **L1166-1180** `inv_cvg_approx` — `suff -> : ... = const 0` →
  `under eq_cvg do rewrite mul0r; exact: cvg_cst.`
- **L138, L165, L1046, L1083, L1120, L1122, L1146** — `(0:R)`
  annotations (~7 sites). Drop `:R`.
- **L320 `is_cvg_*`** — flagged but is mathcomp convention; keep.

### normal_algebra.v
- **§22.1 duplication** — `sqrtr (n%:R / m%:R : R) != 0` proof
  copy-pasted 5+ times (L690-692, L706-708, L717-719, L1159-1167);
  also `phase2_W**_neq0` 4× verbatim. Extract helpers.
- **L897, L995, L1095** — `forall K1 : R,` *inside* a Lemma conclusion;
  should be a Lemma parameter.
- **L108-116** `gaussian_prod_mu/sigma/scalar` — thin Definition
  wrappers unfolded at every call site (`rewrite /gaussian_prod_scalar`
  × 8). Convert to `Notation`.
- **L100-101, L222, L559, L756, L860, L958, L1058** —
  `field. by rewrite hS.` should be `by field; rewrite hS.`

### measure_qbs_adjunction.v
- **§10 naming** — `L_sigma_measurableT/C/_bigcup` should be
  `L_sigma_setT/setC/bigcup`; `L_qbs_morph` etc. use `_morph`
  abbreviation; `R_preserves_prod` is verb-like;
  `R_full_faithful_standard_borel` overly verbose.
- **L172-180** — `Record standard_borel_wit` snake_case where
  PascalCase expected (§13).
- **L434-500** — 64-line `have he_meas` body should be extracted as
  `Local Lemma`.
- **§29.5** — 10 sites with `rewrite eqEsubset; split => …`;
  prefer `rewrite predeqE`.

### qbs_giry.v
- **L151, L155, L172** — `measurable A` and `hU` hypotheses introduced
  and never used; drop premise or replace with `_`.
- **L188** — `@integral_pushforward _ _ _ M R …` with 9 positional
  args; strip `@` + use keyed implicits.

### measure_as_qbs_measure.v
- **L48-59** — `as_qbs_prob_realQ` has 3 dead parameters (`encode`,
  `h_encode_meas`, `h_section`); also uses `Qed.` (opaque) inconsistent
  with `as_qbs_prob` (`Defined.`).
- **L191-193, L266-280** — four
  `rewrite (_ : ... = ...); last first. by apply: funext ...` blocks;
  textbook `under eq_integral do rewrite ...` candidates (§29.1).

### pair_qbs_measure.v
- **L188, L209, L315, L337, L365, L394, L496, L498** — eight
  `(@probability_setT _ _ _ mu)` sites; fix at source via
  `Arguments probability_setT mu.` upstream.
- **L426-451** `qbs_variance_indep_sum` — eleven hypotheses; refactor.
- **L96-98, L140-143** — `qbs_pair_mu`, `qbs_pair_fun` thin wrappers;
  convert to `Notation`.

### qbs_kernel.v / qbs_prob_quot.v / qbs_quotient.v
- **qbs_kernel.v:160** — `qbs_morph_is_measurable` — `is_` on a
  non-predicate; rename to `qbs_morph_measurable` (§32.1).
- **qbs_quotient.v:198-202, qbs_prob_quot.v:152-155** — same
  `have hpreimg ... by move=> p.` antipattern (definitional preimage
  rewrite); delete entirely.
- **qbs_quotient.v:109, 111, 120, 261, 264** — `@pi_subdef _ qbs_quot p`
  where `Local Notation piX` would apply; lift the notation.
- **qbs_quotient.v:146-147, 180-181, 241-242** — three duplicated
  `Local Notation piX/piY` blocks; lift.
- **qbs_prob_quot.v:259, 264, 274** — `%E` delimiters that vanish under
  a missing `Local Open Scope ereal_scope.` declaration.

---

## Tier 3 — Confirmed false positives (do not apply)

These were flagged by audits but should be **kept**:

- **HB Builder calls**: `@isQBS.Build R X ...`, `@QBSHom.Pack R ...`
  — `@` is required (playbook §1).
- **`@dirac _ _ x R U`** — playbook §6: more concise than keyed
  alternative.
- **`Import order.Order.POrderTheory`** in **Import lines** — playbook
  §23.1 (lowercase file form is correct in Imports).
- **`is_cvg_*`** lemma names — established mathcomp-analysis convention
  (`is_cvgD`, `is_cvgM`, `is_cvg_geometric`).
- **In-section `Arguments : clear implicits.`** — playbook §3:
  post-section duplicate often *changes* semantics.
- **Type-inference-anchoring wrappers** — playbook §4: see
  `phase1_sqrtr_var1_neq0`-style specializations.
- **`measurableT_comp` with explicit args** — playbook §7: per-site;
  some sites need them for unification.

---

## Suggested order of operations

1. **CC-2 (Implicit Types)** — biggest single win.
2. **CC-1 (imports / Local Notation aliases)** — 10+ sites resolved.
3. **CC-5 (2-subgoal bullets)** — pure mechanical.
4. **CC-3 (Variable→Variables)** — pure mechanical.
5. **CC-4 (`@`-discipline migration finish)** — per-site verify.
6. **Tier 2 per-file fixes** — start with low-risk bookkeeping
   (probability_qbs.v stray blank line, qbs_giry.v unused hypotheses),
   then `have -> : E by [].` deletions (per playbook §22.1,
   build-verify each).
7. **Tier 2 naming renames** — last; audit external uses first.
