(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot order functions algebra reals ereal topology
  classical_sets boolp numfun measure measurable_realfun lebesgue_measure
  lebesgue_integral lebesgue_stieltjes_measure probability giry.
From QBS Require Import quasi_borel coproduct_qbs probability_qbs qbs_monad.

(**md**************************************************************************)
(* # Normalisation of weighted QBS probabilities (HKSY Sec. VI)               *)
(*                                                                            *)
(* norm : P(X * R) -> P(X) + error. The weight of a pair (x, w) is max(0, w). *)
(* The normalised probability reweights the base measure by the weight and    *)
(* normalises it with mathcomp-analysis' mnormalize; normalisation fails when *)
(* the evidence is 0 or infinite.                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*         qbs_pweight == (x, w) |-> max(0, w) as an extended real            *)
(*       qbs_weight p r == qbs_pweight (alpha_p r)                            *)
(*     qbs_evidence p == \int qbs_weight p d mu_p                             *)
(*      qbs_density p == the measure A |-> \int_A qbs_weight p d mu_p         *)
(* qbs_normalize_prob p == the normalised probability on X                    *)
(*      qbs_normalize p == Some (qbs_normalize_prob p) if the evidence is     *)
(*                         positive and finite, None otherwise                *)
(*  qbs_normalize_sum p == the same, as an element of P(X) + 1                *)
(*       qbs_normalizeQ == qbs_normalize_sum as a QBS morphism                *)
(*                         P(X * R) -> P(X) + 1 (qbs_normalize_morphism)      *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_normalize.
Variable R : realType.
Local Abbreviation mR := (measurableTypeR R).
Variable X : qbsType R.
Implicit Types p : qbs_prob (prodQ X (realQ R)).

Definition qbs_pweight (xw : X * R) : \bar R := (maxr 0 xw.2)%:E.

Lemma qbs_pweight_ge0 xw : 0 <= qbs_pweight xw.
Proof. by rewrite lee_fin le_max lexx. Qed.

Lemma qbs_measurable_weight :
  qbs_measurable (prodQ X (realQ R)) qbs_pweight.
Proof.
move=> b [_ hb2]; apply/measurable_EFinP.
by apply: measurable_maxr => //; exact: measurable_cst.
Qed.

Definition qbs_weight p : mR -> \bar R := qbs_pweight \o qbs_prob_alpha p.

Lemma qbs_weight_ge0 p r : 0 <= qbs_weight p r.
Proof. exact: qbs_pweight_ge0. Qed.

Lemma measurable_qbs_weight p : measurable_fun [set: mR] (qbs_weight p).
Proof. exact: qbs_measurable_weight (qbs_prob_alpha_random p). Qed.

Definition qbs_evidence p : \bar R := \int[qbs_prob_mu p]_r qbs_weight p r.

Lemma qbs_evidence_ge0 p : 0 <= qbs_evidence p.
Proof. by apply: integral_ge0 => r _; exact: qbs_weight_ge0. Qed.

Lemma qbs_evidence_equiv p1 p2 :
  qbs_prob_equiv _ p1 p2 -> qbs_evidence p1 = qbs_evidence p2.
Proof.
move=> e.
exact: (ge0_qbs_integral_equiv qbs_measurable_weight qbs_pweight_ge0 e).
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
  mkQBSProb (fun r => (qbs_prob_alpha p r).1)
    (mnormalize (qbs_density p) (qbs_prob_mu p))
    (qbs_normalize_alpha_random p).

Definition qbs_normalize p : option (qbs_prob X) :=
  if 0 < qbs_evidence p < +oo
  then Some (qbs_normalize_prob p) else None.

Lemma qbs_densityT p : qbs_density p [set: mR] = qbs_evidence p.
Proof. by []. Qed.

Lemma qbs_evidence_degen p :
  ~~ (0 < qbs_evidence p < +oo) -> qbs_evidence p = 0 \/ qbs_evidence p = +oo.
Proof.
have := qbs_evidence_ge0 p; rewrite le_eqVlt => /orP[/eqP<-|ev0]; first by left.
rewrite ev0 /= -leNgt leye_eq => /eqP; by right.
Qed.

(** The normalised probability of U is the weighted probability of U
    divided by the evidence. *)
Lemma qbs_normalize_event p (U : set X) :
  0 < qbs_evidence p < +oo ->
  qbs_prob_event X (qbs_normalize_prob p) U =
  qbs_integral _ p (fun xw => ((\1_U xw.1 : R) * maxr 0 xw.2)%:E) *
  (fine (qbs_evidence p))^-1%:E.
Proof.
move=> /andP[ev0 evoo].
rewrite /qbs_prob_event /= /mnormalize.
case: ifPn => [/orP[] /eqP h|_].
- by move: ev0; rewrite -qbs_densityT h ltxx.
- by move: evoo; rewrite -qbs_densityT h ltxx.
congr (_ * _).
rewrite -[LHS]/(\int[qbs_prob_mu p]_(r in (fun r : mR =>
  (qbs_prob_alpha p r).1) @^-1` U) qbs_weight p r).
rewrite integral_mkcond /qbs_integral.
apply: eq_integral => r _; rewrite patchE /qbs_weight indicE.
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

Lemma qbs_normalize_event_degen p (U : set X) :
  ~~ (0 < qbs_evidence p < +oo) ->
  qbs_prob_event X (qbs_normalize_prob p) U =
  qbs_prob_event _ p (fst @^-1` U).
Proof.
move=> /qbs_evidence_degen hev.
rewrite /qbs_prob_event /= /mnormalize.
case: ifPn => // /norP[/eqP h0 /eqP hoo].
by exfalso; case: hev => hev; [apply: h0 | apply: hoo]; exact: hev.
Qed.

(** Normalisation respects equivalence, degenerate cases included. *)
Lemma qbs_normalize_prob_equiv p1 p2 : qbs_prob_equiv _ p1 p2 ->
  qbs_prob_equiv X (qbs_normalize_prob p1) (qbs_normalize_prob p2).
Proof.
move=> e U mU.
rewrite -[LHS]/(qbs_prob_event _ _ _) -[RHS]/(qbs_prob_event _ _ _).
have [hev|hev] := boolP (0 < qbs_evidence p1 < +oo).
  rewrite !qbs_normalize_event -?(qbs_evidence_equiv e)//; congr (_ * _).
  apply: ge0_qbs_integral_equiv e; first exact: qbs_measurable_weighted_indic.
  by move=> xw; rewrite lee_fin mulr_ge0 ?le_max ?lexx ?orbT// indicE ler0n.
rewrite !qbs_normalize_event_degen -?(qbs_evidence_equiv e)//.
exact: e _ (sigma_Mx_preimage (qbs_fst X (realQ R)) mU).
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
by case: ifPn => // _; exact: qbs_normalize_prob_equiv.
Qed.

(** Normalisation as a total map into P(X) + 1 (HKSY Sec. VI). *)
Definition qbs_normalize_sum p : coprodQ (monadP X) (unitQ R) :=
  if qbs_normalize p is Some q then inl q else inr tt.

Lemma qbs_normalize_sumE p : qbs_normalize_sum p =
  if qbs_normalize p is Some q then inl q else inr tt.
Proof. by []. Qed.

Lemma qbs_normalize_morphism :
  qbs_morphism (X := monadP (prodQ X (realQ R)))
    (Y := coprodQ (monadP X) (unitQ R)) qbs_normalize_sum.
Proof.
move=> b hb; have [a [g [ha mg g1 hbe]]] := hb.
pose pr r : qbs_prob (prodQ X (realQ R)) := mkQBSProb a (giry_prob (g1 r)) ha.
have epr r : qbs_prob_equiv _ (b r) (pr r) by move=> U mU; exact: hbe.
pose P r := 0 < qbs_evidence (b r) < +oo.
have mev : measurable_fun [set: mR] (fun r => qbs_evidence (b r)).
  exact: (ge0_qbs_integral_morphism qbs_measurable_weight qbs_pweight_ge0 hb).
have mP : measurable_fun [set: mR] P.
  by apply: measurable_and; exact: measurable_fun_lte.
have md A : measurable A ->
    measurable_fun [set: mR] (fun r => qbs_density (pr r) A).
  move=> mA; pose w t : \bar R := (\1_A t)%:E * (maxr 0 (a t).2)%:E.
  have mw : measurable_fun [set: mR] w.
    apply: emeasurable_funM; first exact/measurable_EFinP/measurable_indic.
    apply/measurable_EFinP; apply: measurable_maxr => //.
    by have [] := ha.
  have w0 t : 0 <= w t.
    by rewrite mule_ge0 ?lee_fin ?indicE ?ler0n ?le_max ?lexx.
  have -> : (fun r => qbs_density (pr r) A) = (giry_int^~ w) \o g.
    apply/funext => r; rewrite /qbs_density integral_mkcond /giry_int /=.
    apply: eq_integral => t _; rewrite /w patchE indicE.
    by case: (t \in A); rewrite ?mul1e ?mul0e.
  exact: measurableT_comp (measurable_giry_int mw w0) mg.
right; right; exists P, (fun r => qbs_normalize_prob (b r)), (fun=> tt).
split => //; split; last first.
  split => // r.
  by rewrite /= /qbs_normalize_sum /qbs_normalize -/(P r); case: ifP.
(* By saturation, it suffices to normalise the representative [a, g r]. *)
apply: (@monadP_random_equiv _ _ (fun r => qbs_normalize_prob (pr r))).
  by move=> r; apply: qbs_normalize_prob_equiv; exact: qbs_prob_equiv_sym.
exists (fun t => (a t).1),
  (fun r => qbs_prob_mu (qbs_normalize_prob (pr r)) : giry mR R).
split => //.
- by have [] := ha.
- apply: measurable_giry_codensity => // B mB; rewrite /= /mnormalize.
  set c := fun x => (qbs_density (pr x) [set: mR] == 0) ||
    (qbs_density (pr x) [set: mR] == +oo).
  have -> : (fun x => (if c x then [eta giry_prob (g1 x)] else
        fun U : set mR => qbs_density (pr x) U *
          ((fine (qbs_density (pr x) [set: mR]))^-1)%:E) B) =
      (fun x => if c x then g x B else qbs_density (pr x) B *
          ((fine (qbs_density (pr x) [set: mR]))^-1)%:E).
    by apply/funext => x; case: ifP.
  apply: measurable_fun_ifT.
  + by apply: measurable_or; apply: measurable_fun_eqe => //; exact: md.
  + exact: measurableT_comp (measurable_giry_ev mB) mg.
  + apply: emeasurable_funM; first exact: md.
    apply/measurable_EFinP; apply: measurableT_comp measurable_invr _.
    exact: measurableT_comp (fine_measurable measurableT) (md _ measurableT).
- by move=> r; exact: probability_setT.
Qed.

Definition qbs_normalizeQ :
    qbsHomType (monadP (prodQ X (realQ R))) (coprodQ (monadP X) (unitQ R)) :=
  HB.pack qbs_normalize_sum
    (isQBSMorphism.Build R _ _ _ qbs_normalize_morphism).

End qbs_normalize.
