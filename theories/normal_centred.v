(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra boolp reals ereal topology
  classical_sets normedtype sequences numfun measure measurable_realfun
  lebesgue_measure lebesgue_integral probability exp derive realfun ftc.

(**md**************************************************************************)
(* # Centred first moment of the normal density                               *)
(*                                                                            *)
(* (x - m) * normal_pdf m s x is integrable on R and its integral is 0: on    *)
(* each half-line around m its integral is +-s^2 * normal_peak s, computed by *)
(* the FTC with the antiderivative -s^2 * normal_pdf m s.                     *)
(*                                                                            *)
(* ```                                                                        *)
(*   integrable_normal_centred == (x - m) * pdf is Lebesgue integrable        *)
(*     integral_normal_centred == \int (x - m) * pdf = 0                      *)
(*    ge0_integral_normal_prob == change of variables for nonnegative f       *)
(*      integral_normal_mean == \int x d(normal_prob m s) = m                 *)
(*         normal_prob_abs_lty == \int |x| d(normal_prob m s) < +oo           *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Import MeasurableR.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Abbreviation mu := lebesgue_measure.

Section normal_centred.
Context {R : realType}.
Implicit Types m s x : R.

Let cvg_normal_pdf m s : s != 0 ->
  normal_pdf m s x @[x --> +oo] --> (0 : R).
Proof.
move=> s0; rewrite (normal_pdfE m s0).
rewrite -[X in _ --> X](mulr0 (normal_peak s)).
apply: cvgM; first exact: cvg_cst.
have s2 : 0 < (s ^+ 2 *+ 2)^-1 :> R.
  by rewrite invr_gt0 mulrn_wgt0// exprn_even_gt0.
have cy : ((x - m) ^+ 2 * (s ^+ 2 *+ 2)^-1) @[x --> +oo] --> +oo.
  apply: gt0_cvgMly => //.
  have h1 : (x - m) @[x --> +oo] --> +oo by exact: cvg_addrr.
  exact: cvg_comp h1 cvgr_expr2.
rewrite /normal_fun; under eq_fun => x do rewrite mulNr.
exact: cvg_comp cy cvgr_expR.
Qed.

Let is_derive_normal_exponent m s x : s != 0 ->
  is_derive x 1 (fun y : R => - (y - m) ^+ 2 / (s ^+ 2 *+ 2))
    (- (x - m) / s ^+ 2).
Proof.
move=> s0.
have s2 : s ^+ 2 != 0 by rewrite expf_neq0.
have h1 := is_deriveN (is_deriveX 2
  (is_deriveB (is_derive_id x 1) (is_derive_cst m x 1))).
have h2 := is_deriveM (g := fun _ : R => (s ^+ 2 *+ 2)^-1) h1
  (is_derive_cst (s ^+ 2 *+ 2)^-1 x 1).
have h3 : is_derive x 1 (fun y : R => - (y - m) ^+ 2 / (s ^+ 2 *+ 2)) _ := h2.
apply: (is_derive_eq h3).
rewrite /= /GRing.scale/= mulr0 add0r subr0 mulr1 expr1 mulr2n.
change ((s ^+ 2 + s ^+ 2)^-1 * - (2 * (x - m)) = - (x - m) / s ^+ 2).
have two : (2 : R) != 0 by rewrite pnatr_eq0.
rewrite -[s ^+ 2 + s ^+ 2]mulr2n -mulr_natr invfM.
by field.
Qed.

Let is_derive_normal_antiderivative m s x : s != 0 ->
  is_derive x 1 (fun x => (- (s ^+ 2) * normal_pdf m s x)%R)
    ((x - m) * normal_pdf m s x)%R.
Proof.
move=> s0; rewrite (normal_pdfE m s0).
have s2 : s ^+ 2 != 0 by rewrite expf_neq0.
have hu := is_derive_normal_exponent m s x s0.
have he := is_derive1_comp (is_derive_expR _) hu.
have hf := is_deriveM (f := fun _ : R => - s ^+ 2 * normal_peak s)
  (is_derive_cst (- s ^+ 2 * normal_peak s) x 1) he.
have hf' : is_derive x 1 (fun y : R => (- s ^+ 2 * normal_peak s) *
    expR (- (y - m) ^+ 2 / (s ^+ 2 *+ 2)))
  ((- s ^+ 2 * normal_peak s) *: (expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2)) *
    (- (x - m) / s ^+ 2)) +
   (expR (- (x - m) ^+ 2 / (s ^+ 2 *+ 2))) *: 0) := hf.
under eq_fun => y do rewrite /normal_fun mulrA.
apply: (is_derive_eq hf').
rewrite /= scaler0 addr0 /GRing.scale/= /normal_fun.
by field.
Qed.

Let normal_pdfxx m s : s != 0 -> normal_pdf m s m = normal_peak s.
Proof.
by move=> s0; rewrite /normal_pdf (negbTE s0) NormalPdf0.normal_pdf0xx.
Qed.

Let continuous_normal_centred m s : s != 0 ->
  continuous (fun x => (x - m) * normal_pdf m s x).
Proof.
move=> s0 x; apply: cvgM; first by apply: cvgB; [exact: cvg_id|exact: cvg_cst].
exact: continuous_normal_pdf.
Qed.

Let integral_normal_centred_right m s : s != 0 ->
  (\int[mu]_(x in `[m, +oo[) ((x - m) * normal_pdf m s x)%:E =
   (s ^+ 2 * normal_peak s)%:E)%E.
Proof.
move=> s0.
rewrite (@ge0_continuous_FTC2y R (fun x => (x - m) * normal_pdf m s x)
  (fun x => - (s ^+ 2) * normal_pdf m s x) m 0).
- by move=> x mx; rewrite mulr_ge0// ?normal_pdf_ge0// subr_ge0.
- by apply: continuous_subspaceT; exact: continuous_normal_centred.
- have := cvg_normal_pdf m s s0 => h.
  rewrite -[X in _ --> X](mulr0 (- (s ^+ 2))).
  by apply: cvgM; [exact: cvg_cst|exact: h].
- by move=> x _; case: (is_derive_normal_antiderivative m s x s0).
- apply: cvg_at_right_filter.
  by apply: cvgM; [exact: cvg_cst|exact: continuous_normal_pdf].
- move=> x _; rewrite derive1E.
  by case: (is_derive_normal_antiderivative m s x s0) => _ ->.
- by rewrite normal_pdfxx// -EFinB sub0r mulNr opprK.
Qed.

Let normal_pdfN m s x : s != 0 ->
  normal_pdf m s (- x) = normal_pdf (- m) s x.
Proof.
by move=> s0; rewrite !normal_pdfE// -(normal_funN (- m) s x) opprK.
Qed.

Let integral_normal_centred_left m s : s != 0 ->
  (\int[mu]_(x in `]-oo, m]) ((m - x) * normal_pdf m s x)%:E =
   (s ^+ 2 * normal_peak s)%:E)%E.
Proof.
move=> s0.
have := @ge0_integration_by_substitutionNy R
  (fun x => (m - x) * normal_pdf m s x) (- m).
rewrite opprK => ->.
- apply: continuous_subspaceT => x.
  apply: cvgM; first by apply: cvgB; [exact: cvg_cst|exact: cvg_id].
  exact: continuous_normal_pdf.
- move=> x; rewrite in_itv/= => xm.
  by rewrite mulr_ge0 ?normal_pdf_ge0// subr_ge0 ltW.
- rewrite -(integral_normal_centred_right (- m) s s0).
  apply: eq_integral => x _; congr EFin.
  by rewrite /= normal_pdfN// !opprK [m + x]addrC.
Qed.

Let measurable_normal_centred m s : s != 0 ->
  measurable_fun setT (fun x : R => ((x - m) * normal_pdf m s x)%:E).
Proof.
move=> s0; apply/measurable_EFinP.
exact: continuous_measurable_fun (continuous_normal_centred m s s0).
Qed.

Let setT_split m : [set: R] = `]-oo, m]%classic `|` `]m, +oo[%classic.
Proof.
apply/seteqP; split => // x _; rewrite /= !in_itv/= andbT.
by case: (leP x m); [left|right].
Qed.

Let disj_split m : [disjoint `]-oo, m]%classic & `]m, +oo[%classic].
Proof.
rewrite disj_set2E; apply/eqP; rewrite -subset0 => x/= [].
by rewrite !in_itv/= andbT => /[swap] /le_lt_trans /[apply]; rewrite ltxx.
Qed.

Lemma integrable_normal_centred m s : s != 0 ->
  mu.-integrable setT (fun x => ((x - m) * normal_pdf m s x)%:E).
Proof.
move=> s0; have mg := measurable_normal_centred m s s0.
apply/integrableP; split => //.
have TAB := setT_split m.
have dAB := disj_split m.
have mabs : measurable_fun setT
    (fun x : R => `|((x - m) * normal_pdf m s x)%:E|%E).
  by apply: measurableT_comp.
have eA : (\int[mu]_(x in `]-oo, m]%classic) `|((x - m) * normal_pdf m s x)%:E|
    = (s ^+ 2 * normal_peak s)%:E)%E.
  rewrite -(integral_normal_centred_left m s s0).
  apply: eq_integral => x; rewrite inE/= in_itv/= => xm.
  rewrite normrM (ger0_norm (normal_pdf_ge0 _ _ _)).
  by rewrite ler0_norm ?subr_le0// opprB.
have eB : (\int[mu]_(x in `]m, +oo[%classic) `|((x - m) * normal_pdf m s x)%:E|
    = (s ^+ 2 * normal_peak s)%:E)%E.
  rewrite -(integral_normal_centred_right m s s0).
  rewrite integral_itvob_itvcb.
    exact: measurable_funTS mabs.
  apply: eq_integral => x; rewrite inE/= in_itv/= andbT => xm.
  have xm' : 0 <= x - m by rewrite subr_ge0.
  by rewrite normrM (ger0_norm (normal_pdf_ge0 _ _ _)) (ger0_norm xm').
rewrite TAB ge0_integral_setU//=.
- by rewrite -TAB.
- by move=> x _; rewrite lee_fin normr_ge0.
by rewrite eA eB -EFinD ltry.
Qed.

Lemma integral_normal_centred m s : s != 0 ->
  (\int[mu]_x ((x - m) * normal_pdf m s x)%:E = 0)%E.
Proof.
move=> s0; have mg := measurable_normal_centred m s s0.
have TAB := setT_split m.
have dAB := disj_split m.
have eA : (\int[mu]_(x in `]-oo, m]%classic) ((x - m) * normal_pdf m s x)%:E
    = - (s ^+ 2 * normal_peak s)%:E)%E.
  rewrite -(integral_normal_centred_left m s s0) -integral_ge0N.
    move=> x; rewrite /= in_itv/= => xm.
    by rewrite lee_fin mulr_ge0// ?normal_pdf_ge0// subr_ge0.
  apply: eq_integral => x; rewrite inE/= in_itv/= => xm.
  by rewrite -mulNr opprB.
have eB : (\int[mu]_(x in `]m, +oo[%classic) ((x - m) * normal_pdf m s x)%:E
    = (s ^+ 2 * normal_peak s)%:E)%E.
  rewrite -(integral_normal_centred_right m s s0).
  rewrite integral_itvob_itvcb//.
  exact: measurable_funTS mg.
rewrite TAB integral_setU//=; first by rewrite -TAB.
by rewrite eA eB addeC subee.
Qed.

Lemma ge0_integral_normal_prob m s (f : R -> \bar R) :
  (forall x, (0 <= f x)%E) -> measurable_fun setT f ->
  (\int[normal_prob m s]_x f x =
   \int[mu]_x (f x * (normal_pdf m s x)%:E))%E.
Proof.
move=> f0 mf; have nd := normal_prob_dominates m s.
(* no ge0 version of the change of variables is public upstream *)
rewrite -(Radon_Nikodym_SigmaFinite.change_of_variables nd)//.
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //.
  exact: measurable_int (Radon_Nikodym_SigmaFinite.f_integrable nd).
- apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
- have h := ae_eq_trans (ae_eq_Radon_Nikodym_SigmaFinite nd measurableT)
    (normal_pdf_uniq_ae m s).
  exact: (ae_eqe_mul2l f h).
Qed.

Lemma normal_prob_abs_lty m s : s != 0 ->
  (\int[normal_prob m s]_x `|x%:E| < +oo)%E.
Proof.
move=> s0; rewrite ge0_integral_normal_prob//.
- by move=> x; exact: abse_ge0.
- by apply: measurableT_comp => //; exact/measurable_EFinP.
have hc := integrable_normal_centred m s s0.
apply: (@le_lt_trans _ _ (\int[mu]_x (`|((x - m) * normal_pdf m s x)%:E| +
    (`|m| * normal_pdf m s x)%:E))%E).
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite mule_ge0 ?abse_ge0 ?lee_fin ?normal_pdf_ge0.
  - apply: emeasurable_funM.
      by apply: measurableT_comp => //; exact/measurable_EFinP.
    by apply/measurable_EFinP; exact: measurable_normal_pdf.
  - apply: emeasurable_funD.
      by apply: measurableT_comp => //; exact: measurable_int hc.
    apply/measurable_EFinP; apply: measurable_funM => //.
    exact: measurable_normal_pdf.
  - move=> x _ /=; rewrite -EFinM -EFinD lee_fin normrM.
    rewrite (ger0_norm (normal_pdf_ge0 _ _ _)) -mulrDl.
    rewrite ler_wpM2r ?normal_pdf_ge0//.
    by rewrite -{1}(subrK m x) ler_normD.
rewrite ge0_integralD//.
- by move=> x _; exact: abse_ge0.
- by apply: measurableT_comp => //; exact: measurable_int hc.
- by move=> x _; rewrite lee_fin mulr_ge0 ?normal_pdf_ge0.
- apply/measurable_EFinP; apply: measurable_funM => //.
  exact: measurable_normal_pdf.
apply: lte_add_pinfty; first by case/integrableP: hc.
under eq_integral do rewrite EFinM.
rewrite integralZl// ?integral_normal_pdf ?mule1 ?ltry//.
exact: integrable_normal_pdf.
Qed.

Lemma integral_normal_mean m s : s != 0 ->
  (\int[normal_prob m s]_x x%:E = m%:E)%E.
Proof.
move=> s0; have id_int := normal_prob_abs_lty m s s0.
have hc := integrable_normal_centred m s s0.
have hp := integrable_normal_pdf m s.
rewrite integral_normal_prob//=; first by apply/integrableP; split.
under eq_integral do rewrite -EFinM.
(* x * pdf = m * pdf + (x - m) * pdf *)
under eq_integral do rewrite -[x in x * _](subrK m) mulrDl EFinD.
have hm : mu.-integrable setT (fun x => (m * normal_pdf m s x)%:E).
  under eq_fun do rewrite EFinM.
  exact: integrableZl.
rewrite (integralD measurableT hc hm) integral_normal_centred// add0e.
under eq_integral do rewrite EFinM.
by rewrite integralZl// integral_normal_pdf// mule1.
Qed.

End normal_centred.
