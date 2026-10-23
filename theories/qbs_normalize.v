(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot order functions algebra reals ereal topology
  classical_sets boolp numfun measure measurable_realfun lebesgue_measure
  lebesgue_integral lebesgue_stieltjes_measure probability giry.
From QBS Require Import measurable_aux quasi_borel coproduct_qbs probability_qbs
  qbs_monad.

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
(*  qbs_pdensity mu ha == the same for (alpha, mu), ha : qbs_Mx alpha         *)
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

Section density.
Variables (alpha : mR -> prodQ X (realQ R)) (mu : probability mR R).

Definition qbs_pdensity (ha : qbs_Mx alpha) (A : set mR) : \bar R :=
  \int[mu]_(r in A) qbs_pweight (alpha r).

Context (ha : qbs_Mx alpha).

Let pdensity0 : qbs_pdensity ha set0 = 0.
Proof. by rewrite /qbs_pdensity integral_set0. Qed.

Let pdensity_ge0 A : 0 <= qbs_pdensity ha A.
Proof. by apply: integral_ge0 => r _; exact: qbs_pweight_ge0. Qed.

Let pdensity_sigma : semi_sigma_additive (qbs_pdensity ha).
Proof.
apply: semi_sigma_additive_nng_induced;
  first exact: qbs_measurable_weight ha.
by move=> r; exact: qbs_pweight_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (qbs_pdensity ha)
  pdensity0 pdensity_ge0 pdensity_sigma.

End density.

Arguments qbs_pdensity {alpha} mu ha A.

Definition qbs_density p : set mR -> \bar R :=
  qbs_pdensity (qbs_prob_mu p) (qbs_prob_alpha_random p).

HB.instance Definition _ p := Measure.on (qbs_density p).

Lemma qbs_pdensityT (alpha : mR -> prodQ X (realQ R)) (mu : probability mR R)
    (ha : qbs_Mx alpha) :
  qbs_pdensity mu ha [set: mR] = \int[mu]_r qbs_pweight (alpha r).
Proof.
rewrite /qbs_pdensity integral_mkcond.
by apply: eq_integral => r _; rewrite patchE in_setT.
Qed.

Lemma qbs_prob_alpha_fst_random p :
  qbs_Mx (fun r => (qbs_prob_alpha p r).1).
Proof. by have [] := qbs_prob_alpha_random p. Qed.

Definition qbs_normalize_prob p : qbs_prob X :=
  mkQBSProb (fun r => (qbs_prob_alpha p r).1)
    (mnormalize (qbs_density p) (qbs_prob_mu p))
    (qbs_prob_alpha_fst_random p).

Definition qbs_normalize p : option (qbs_prob X) :=
  if 0 < qbs_evidence p < +oo
  then Some (qbs_normalize_prob p) else None.

Lemma qbs_densityT p : qbs_density p [set: mR] = qbs_evidence p.
Proof. exact: qbs_pdensityT. Qed.

Lemma qbs_evidence_ge0 p : 0 <= qbs_evidence p.
Proof. by rewrite -qbs_densityT; exact: measure_ge0. Qed.

Lemma qbs_evidence_degen p :
  ~~ (0 < qbs_evidence p < +oo) ->
  qbs_evidence p = 0 \/ qbs_evidence p = +oo.
Proof.
have := qbs_evidence_ge0 p; rewrite le_eqVlt => /orP[/eqP<-|ev0]; first by left.
by rewrite ev0 /= -leNgt leye_eq => /eqP; right.
Qed.

Lemma indic_maxr_ge0 (T : Type) (U : set T) (x : T) (w : R) :
  (0 <= (\1_U x : R) * maxr 0 w)%R.
Proof. by rewrite mulr_ge0 ?le_max ?lexx ?orbT// indicE ler0n. Qed.

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

Lemma qbs_pdensity_preimage (mu : probability mR R)
    (alpha : mR -> prodQ X (realQ R))
    (ha : qbs_Mx alpha) (U : set X) :
  qbs_pdensity mu ha ((fun r => (alpha r).1) @^-1` U) =
  \int[mu]_r ((\1_U (alpha r).1 : R) * maxr 0 (alpha r).2)%:E.
Proof.
rewrite /qbs_pdensity integral_mkcond; apply: eq_integral => r _.
rewrite patchE indicE.
have -> : (r \in (fun r0 : mR => (alpha r0).1) @^-1` U) =
    ((alpha r).1 \in U) by apply/idP/idP; rewrite !inE.
by case: (_ \in U); rewrite /qbs_pweight ?mul1r ?mul0r.
Qed.

(** The normalised probability of U is the weighted probability of U
    divided by the evidence. *)
Lemma qbs_normalize_event p (U : set X) : sigma_Mx U ->
  0 < qbs_evidence p < +oo ->
  qbs_prob_event X (qbs_normalize_prob p) U =
  qbs_integral _ p (fun xw => ((\1_U xw.1 : R) * maxr 0 xw.2)%:E) *
  (fine (qbs_evidence p))^-1%:E.
Proof.
move=> mU /andP[ev0 evoo].
rewrite /qbs_normalize_prob qbs_prob_event_mk //= /mnormalize.
case: ifPn => [/orP[] /eqP h|_].
- by move: ev0; rewrite -qbs_densityT h ltxx.
- by move: evoo; rewrite -qbs_densityT h ltxx.
by congr (_ * _); exact: qbs_pdensity_preimage.
Qed.

Lemma qbs_normalize_event_degen p (U : set X) : sigma_Mx U ->
  ~~ (0 < qbs_evidence p < +oo) ->
  qbs_prob_event X (qbs_normalize_prob p) U =
  qbs_prob_event _ p (fst @^-1` U).
Proof.
move=> mU /qbs_evidence_degen hev.
rewrite /qbs_normalize_prob qbs_prob_event_mk //= /mnormalize.
case: ifPn => // /norP[/eqP h0 /eqP hoo].
by exfalso; case: hev => hev; [apply: h0 | apply: hoo]; exact: hev.
Qed.

(** Events of the normalisation of a probability given by (alpha, mu). *)
Lemma qbs_normalize_prob_event_mk (alpha : mR -> prodQ X (realQ R))
    (mu : probability mR R) (ha : qbs_Mx alpha) (U : set X) : sigma_Mx U ->
  qbs_prob_event X (qbs_normalize_prob (mkQBSProb alpha mu ha)) U =
  mnormalize (qbs_pdensity mu ha) mu ((fun r => (alpha r).1) @^-1` U).
Proof.
move=> mU; set p := mkQBSProb alpha mu ha.
have evp : qbs_evidence p = qbs_pdensity mu ha [set: mR].
  rewrite qbs_pdensityT -[LHS]/(qbs_integral _ p qbs_pweight) /p.
  rewrite qbs_integral_mk; first exact: qbs_measurable_weight.
  by [].
rewrite /mnormalize; case: ifPn => [hc|/norP[/negbTE h0 /negbTE hoo]].
  have hev : ~~ (0 < qbs_evidence p < +oo).
    by rewrite evp; move: hc => /orP[] /eqP ->; rewrite ?ltxx ?ltNge ?leey.
  rewrite (qbs_normalize_event_degen mU hev) qbs_prob_event_mk //.
  exact: (sigma_Mx_preimage (qbs_fst X (realQ R)) mU).
have hev : 0 < qbs_evidence p < +oo.
  have {}h0 := negbT h0; have {}hoo := negbT hoo.
  by rewrite evp lt0e ltey h0 hoo /= measure_ge0.
rewrite (qbs_normalize_event mU hev) evp /p qbs_integral_mk;
  first exact: qbs_measurable_weighted_indic mU.
by rewrite -qbs_pdensity_preimage.
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
have ebr r : b r = pr r.
  by apply/qbs_prob_eqP => U mU; rewrite qbs_prob_event_mk//; exact: hbe.
pose d r := qbs_pdensity (giry_prob (g1 r)) ha.
have evr r : qbs_evidence (b r) = d r [set: mR].
  rewrite ebr /d qbs_pdensityT -[LHS]/(qbs_integral _ (pr r) qbs_pweight).
  by rewrite qbs_integral_mk //; exact: qbs_measurable_weight.
pose P r := 0 < qbs_evidence (b r) < +oo.
have mev : measurable_fun [set: mR] (fun r => qbs_evidence (b r)).
  exact: (ge0_qbs_integral_morphism qbs_measurable_weight qbs_pweight_ge0 hb).
have mP : measurable_fun [set: mR] P.
  apply: measurable_and.
    exact: measurable_fun_lte (measurable_cst 0) mev.
  exact: measurable_fun_lte mev (measurable_cst +oo).
have md A : measurable A -> measurable_fun [set: mR] (fun r => d r A).
  move=> mA; pose w t : \bar R := (\1_A t)%:E * (maxr 0 (a t).2)%:E.
  have mw : measurable_fun [set: mR] w.
    apply: emeasurable_funM; first exact/measurable_EFinP/measurable_indic.
    apply/measurable_EFinP; apply: measurable_maxr => //.
    by have [] := ha.
  have w0 t : 0 <= w t.
    by rewrite /w -EFinM lee_fin; exact: indic_maxr_ge0.
  have -> : (fun r => d r A) = (giry_int^~ w) \o g.
    apply/funext => r; rewrite /d /qbs_pdensity integral_mkcond /giry_int /=.
    apply: eq_integral => t _; rewrite /w patchE indicE.
    by case: (t \in A); rewrite /qbs_pweight ?mul1e ?mul0e.
  exact: measurableT_comp (measurable_giry_int mw w0) mg.
right; right; exists P, (fun r => qbs_normalize_prob (b r)), (fun=> tt).
split; first exact: mP.
split; last first.
  split=> // r.
  by rewrite /= /qbs_normalize_sum /qbs_normalize -/(P r); case: ifP.
exists (fun t => (a t).1),
  (fun r => mnormalize (d r) (giry_prob (g1 r))).
split=> //.
- by have [] := ha.
- apply: measurable_giry_codensity => // B mB; rewrite /= /mnormalize.
  set c := fun x => (d x [set: mR] == 0) || (d x [set: mR] == +oo).
  have -> : (fun x => (if c x then [eta giry_prob (g1 x)] else
        fun U : set mR => d x U * ((fine (d x [set: mR]))^-1)%:E) B) =
      (fun x => if c x then g x B else d x B *
          ((fine (d x [set: mR]))^-1)%:E).
    by apply/funext => x; case: ifP.
  apply: measurable_fun_ifT.
  + by apply: measurable_or; apply: measurable_fun_eqe => //; exact: md.
  + exact: measurableT_comp (measurable_giry_ev mB) mg.
  + apply: emeasurable_funM; first exact: md.
    apply/measurable_EFinP; apply: measurableT_comp measurable_invr _.
    exact: measurableT_comp (fine_measurable measurableT) (md _ measurableT).
- by move=> ?; exact: probability_setT.
- by move=> r U mU; rewrite ebr; exact: qbs_normalize_prob_event_mk.
Qed.

Definition qbs_normalizeQ :
    qbsHomType (monadP (prodQ X (realQ R))) (coprodQ (monadP X) (unitQ R)) :=
  HB.pack qbs_normalize_sum
    (isQBSMorphism.Build R _ _ _ qbs_normalize_morphism).

End qbs_normalize.
