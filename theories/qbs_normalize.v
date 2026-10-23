(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology classical_sets
  boolp numfun measure measurable_realfun lebesgue_measure lebesgue_integral
  lebesgue_stieltjes_measure probability.
From QBS Require Import quasi_borel probability_qbs qbs_monad.

(**md**************************************************************************)
(* # Normalisation of weighted QBS probabilities (HKSY Sec. VI)               *)
(*                                                                            *)
(* norm : P(X * R) -> P(X) + error. The weight of a pair (x, w) is max(0, w). *)
(* The normalised probability reweights the base measure by the weight and    *)
(* normalises it with mathcomp-analysis' mnormalize; normalisation fails when *)
(* the evidence is 0 or infinite.                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*        qbs_weight p r == max(0, w) where (x, w) = alpha_p r                *)
(*      qbs_evidence p == \int qbs_weight p d mu_p                            *)
(* qbs_normalize_prob p == the normalised probability on X                    *)
(*      qbs_normalize p == Some (qbs_normalize_prob p) if the evidence is     *)
(*                         positive and finite, None otherwise                *)
(* ```                                                                        *)
(******************************************************************************)

Import order.Order.TTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_normalize.
Variable R : realType.
Local Notation mR := (measurableTypeR R).
Variable X : qbsType R.
Implicit Types p : qbs_prob (prodQ X (realQ R)).

Definition qbs_weight p (r : mR) : \bar R :=
  (maxr 0 (qbs_prob_alpha p r).2)%:E.

Lemma qbs_weight_ge0 p r : 0 <= qbs_weight p r.
Proof. by rewrite lee_fin le_max lexx. Qed.

Lemma measurable_qbs_weight p : measurable_fun [set: mR] (qbs_weight p).
Proof.
apply/measurable_EFinP; apply: measurable_maxr; first exact: measurable_cst.
by have [_] := qbs_prob_alpha_random p.
Qed.

Definition qbs_evidence p : \bar R := \int[qbs_prob_mu p]_r qbs_weight p r.

Lemma qbs_measurable_weight :
  qbs_measurable (prodQ X (realQ R)) (fun xw => (maxr 0 xw.2)%:E).
Proof.
move=> b [_ hb2]; apply/measurable_EFinP.
by apply: measurable_maxr; [exact: measurable_cst|exact: hb2].
Qed.

Lemma qbs_evidence_equiv p1 p2 :
  qbs_prob_equiv _ p1 p2 -> qbs_evidence p1 = qbs_evidence p2.
Proof.
move=> e; rewrite /qbs_evidence.
rewrite -[LHS]/(qbs_integral _ p1 (fun xw => (maxr 0 xw.2)%:E)).
rewrite -[RHS]/(qbs_integral _ p2 (fun xw => (maxr 0 xw.2)%:E)).
apply: ge0_qbs_integral_equiv e; first exact: qbs_measurable_weight.
by move=> xw; rewrite lee_fin le_max lexx.
Qed.

Section density.
Variable p : qbs_prob (prodQ X (realQ R)).

Definition qbs_density (A : set mR) : \bar R :=
  \int[qbs_prob_mu p]_(r in A) qbs_weight p r.

Let density0 : qbs_density set0 = 0.
Proof. by rewrite /qbs_density integral_set0. Qed.

Let density_ge0 A : 0 <= qbs_density A.
Proof. by apply: integral_ge0 => r _; exact: qbs_weight_ge0. Qed.

Let density_sigma : semi_sigma_additive qbs_density.
Proof.
apply: semi_sigma_additive_nng_induced; first exact: measurable_qbs_weight.
exact: qbs_weight_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ qbs_density
  density0 density_ge0 density_sigma.

End density.

Lemma qbs_normalize_alpha_random p :
  qbs_Mx (s := X) (fun r => (qbs_prob_alpha p r).1).
Proof. by have [] := qbs_prob_alpha_random p. Qed.

Definition qbs_normalize_prob p : qbs_prob X :=
  @mkQBSProb R X (fun r => (qbs_prob_alpha p r).1)
    (mnormalize (qbs_density p) (qbs_prob_mu p))
    (qbs_normalize_alpha_random p).

Definition qbs_normalize p : option (qbs_prob X) :=
  if (0 < qbs_evidence p) && (qbs_evidence p < +oo)
  then Some (qbs_normalize_prob p) else None.

Lemma qbs_densityT p : qbs_density p [set: mR] = qbs_evidence p.
Proof. by []. Qed.

(** The normalised probability of U is the weighted probability of U
    divided by the evidence. *)
Lemma qbs_normalize_event p (U : set X) :
  0 < qbs_evidence p < +oo -> sigma_Mx U ->
  qbs_prob_event X (qbs_normalize_prob p) U =
  qbs_integral _ p (fun xw => ((\1_U xw.1 : R) * maxr 0 xw.2)%:E) *
  (fine (qbs_evidence p))^-1%:E.
Proof.
move=> /andP[ev0 evoo] mU.
rewrite /qbs_prob_event /= /mnormalize.
case: ifPn => [/orP[] /eqP h|_].
- by move: ev0; rewrite -[qbs_evidence p]/(qbs_density p [set: mR]) h ltxx.
- by move: evoo; rewrite -[qbs_evidence p]/(qbs_density p [set: mR]) h ltxx.
congr (_ * _).
rewrite -[LHS]/(\int[qbs_prob_mu p]_(r in (fun r : mR =>
  (qbs_prob_alpha p r).1) @^-1` U) qbs_weight p r).
rewrite integral_mkcond /qbs_integral.
apply: eq_integral => r _; rewrite /functions.patch /qbs_weight indicE.
have -> : (r \in (fun r0 : mR => (qbs_prob_alpha p r0).1) @^-1` U) =
    ((qbs_prob_alpha p r).1 \in U) by apply/idP/idP; rewrite !inE.
by case: (_ \in U); rewrite ?mul1r ?mul0r.
Qed.

Lemma qbs_measurable_weighted_indic (U : set X) : sigma_Mx U ->
  qbs_measurable (prodQ X (realQ R))
    (fun xw => ((\1_U xw.1 : R) * maxr 0 xw.2)%:E).
Proof.
move=> mU b [hb1 hb2]; apply/measurable_EFinP; apply: measurable_funM.
  rewrite (_ : (fun r => _) = (\1_((fun r => (b r).1) @^-1` U))%R).
    by apply/funext => r; rewrite !indicE.
  exact: measurable_indic (mU _ hb1).
by apply: measurable_maxr; [exact: measurable_cst|exact: hb2].
Qed.

(** Normalisation is well defined on equivalence classes. *)
Lemma qbs_normalize_equiv p1 p2 : qbs_prob_equiv _ p1 p2 ->
  match qbs_normalize p1, qbs_normalize p2 with
  | Some q1, Some q2 => qbs_prob_equiv X q1 q2
  | None, None => True
  | _, _ => False
  end.
Proof.
move=> e; rewrite /qbs_normalize -(qbs_evidence_equiv e).
case: ifPn => // hev U mU.
rewrite -[LHS]/(qbs_prob_event _ _ _) -[RHS]/(qbs_prob_event _ _ _).
rewrite !qbs_normalize_event// -?(qbs_evidence_equiv e)//; congr (_ * _).
apply: ge0_qbs_integral_equiv e; first exact: qbs_measurable_weighted_indic.
by move=> xw; rewrite lee_fin mulr_ge0 ?le_max ?lexx ?orbT// indicE ler0n.
Qed.

End qbs_normalize.
