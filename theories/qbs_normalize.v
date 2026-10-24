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
(*         pweight == (x, w) |-> max(0, w) as an extended real                *)
(*     evidence p == the integral of pweight against p                        *)
(*      density p == the measure A |-> \int_A pweight o alpha_p dmu_p         *)
(*  pdensity mu ha == the same for (alpha, mu), ha : qbs_Mx alpha             *)
(* normalize_prob p == the normalised probability on X                        *)
(*      normalize p == Some (normalize_prob p) if the evidence is             *)
(*                         positive and finite, None otherwise                *)
(*  normalize_sum p == the same, as an element of P(X) + 1                    *)
(*       normalizeQ == normalize_sum as a QBS morphism                        *)
(*                         P(X * R) -> P(X) + 1 (qbs_morphism_normalize)      *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section normalize.
Variable R : realType.
Local Abbreviation mR := (measurableTypeR R).
Variable X : qbsType R.
Implicit Types p : probQ (prodQ X (realQ R)).

Definition pweight (xw : X * R) : \bar R := (maxr 0 xw.2)%:E.

Lemma pweight_ge0 xw : 0 <= pweight xw.
Proof. by rewrite lee_fin le_max lexx. Qed.

Lemma qbs_measurable_weight :
  qbs_measurable (prodQ X (realQ R)) pweight.
Proof.
move=> b [_ hb2]; apply/measurable_EFinP.
by apply: measurable_maxr => //; exact: measurable_cst.
Qed.

(** The evidence: the integral of the weight. *)
Definition evidence p : \bar R := qbs_integral _ p pweight.

Section pdensity_measure.
Variables (alpha : mR -> prodQ X (realQ R)) (mu : probability mR R).

Definition pdensity (ha : qbs_Mx alpha) (A : set mR) : \bar R :=
  \int[mu]_(r in A) pweight (alpha r).

Context (ha : qbs_Mx alpha).

Let pdensity0 : pdensity ha set0 = 0.
Proof. by rewrite /pdensity integral_set0. Qed.

Let pdensity_ge0 A : 0 <= pdensity ha A.
Proof. by apply: integral_ge0 => r _; exact: pweight_ge0. Qed.

Let pdensity_sigma : semi_sigma_additive (pdensity ha).
Proof.
apply: semi_sigma_additive_nng_induced;
  first exact: qbs_measurable_weight ha.
by move=> r; exact: pweight_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (pdensity ha)
  pdensity0 pdensity_ge0 pdensity_sigma.

End pdensity_measure.

Arguments pdensity {alpha} mu ha A.

Definition density p : set mR -> \bar R :=
  pdensity (qbs_mu p) (qbs_alpha_random p).

HB.instance Definition _ p := Measure.on (density p).

Lemma pdensityT (alpha : mR -> prodQ X (realQ R)) (mu : probability mR R)
    (ha : qbs_Mx alpha) :
  pdensity mu ha [set: mR] = \int[mu]_r pweight (alpha r).
Proof.
rewrite /pdensity integral_mkcond.
by apply: eq_integral => r _; rewrite patchE in_setT.
Qed.

Lemma qbs_alpha_fst_random p :
  qbs_Mx (fun r => (qbs_alpha p r).1).
Proof. by have [] := qbs_alpha_random p. Qed.

Definition normalize_prob p : probQ X :=
  mkQBSProb (fun r => (qbs_alpha p r).1)
    (mnormalize (density p) (qbs_mu p))
    (qbs_alpha_fst_random p).

Definition normalize p : option (probQ X) :=
  if 0 < evidence p < +oo
  then Some (normalize_prob p) else None.

Lemma densityT p : density p [set: mR] = evidence p.
Proof. exact: pdensityT. Qed.

Lemma evidence_ge0 p : 0 <= evidence p.
Proof. by rewrite -densityT; exact: measure_ge0. Qed.

Lemma evidence_degen p :
  ~~ (0 < evidence p < +oo) ->
  evidence p = 0 \/ evidence p = +oo.
Proof.
have := evidence_ge0 p; rewrite le_eqVlt => /orP[/eqP<-|ev0]; first by left.
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

Lemma pdensity_preimage (mu : probability mR R)
    (alpha : mR -> prodQ X (realQ R))
    (ha : qbs_Mx alpha) (U : set X) :
  pdensity mu ha ((fun r => (alpha r).1) @^-1` U) =
  \int[mu]_r ((\1_U (alpha r).1 : R) * maxr 0 (alpha r).2)%:E.
Proof.
rewrite /pdensity integral_mkcond; apply: eq_integral => r _.
rewrite patchE indicE.
have -> : (r \in (fun r0 : mR => (alpha r0).1) @^-1` U) =
    ((alpha r).1 \in U) by apply/idP/idP; rewrite !inE.
by case: (_ \in U); rewrite /pweight ?mul1r ?mul0r.
Qed.

(** The normalised probability of U is the weighted probability of U
    divided by the evidence. *)
Lemma normalize_event p (U : set X) : sigma_Mx U ->
  0 < evidence p < +oo ->
  qbs_event X (normalize_prob p) U =
  qbs_integral _ p (fun xw => ((\1_U xw.1 : R) * maxr 0 xw.2)%:E) *
  (fine (evidence p))^-1%:E.
Proof.
move=> mU /andP[ev0 evoo].
rewrite /normalize_prob qbs_event_mk //= /mnormalize.
case: ifPn => [/orP[] /eqP h|_].
- by move: ev0; rewrite -densityT h ltxx.
- by move: evoo; rewrite -densityT h ltxx.
by congr (_ * _); exact: pdensity_preimage.
Qed.

Lemma normalize_event_degen p (U : set X) : sigma_Mx U ->
  ~~ (0 < evidence p < +oo) ->
  qbs_event X (normalize_prob p) U =
  qbs_event _ p (fst @^-1` U).
Proof.
move=> mU /evidence_degen hev.
rewrite /normalize_prob qbs_event_mk //= /mnormalize.
case: ifPn => // /norP[/eqP h0 /eqP hoo].
by exfalso; case: hev => hev; [apply: h0 | apply: hoo]; exact: hev.
Qed.

(** Events of the normalisation of a probability given by (alpha, mu). *)
Lemma normalize_prob_event_mk (alpha : mR -> prodQ X (realQ R))
    (mu : probability mR R) (ha : qbs_Mx alpha) (U : set X) : sigma_Mx U ->
  qbs_event X (normalize_prob (mkQBSProb alpha mu ha)) U =
  mnormalize (pdensity mu ha) mu ((fun r => (alpha r).1) @^-1` U).
Proof.
move=> mU; set p := mkQBSProb alpha mu ha.
have evp : evidence p = pdensity mu ha [set: mR].
  by rewrite pdensityT /evidence qbs_integral_mk//;
    exact: qbs_measurable_weight.
rewrite /mnormalize; case: ifPn => [hc|/norP[/negbTE h0 /negbTE hoo]].
  have hev : ~~ (0 < evidence p < +oo).
    by rewrite evp; move: hc => /orP[] /eqP ->; rewrite ?ltxx ?ltNge ?leey.
  rewrite (normalize_event_degen mU hev) qbs_event_mk //.
  exact: (sigma_Mx_preimage (qbs_fst X (realQ R)) mU).
have hev : 0 < evidence p < +oo.
  have {}h0 := negbT h0; have {}hoo := negbT hoo.
  by rewrite evp lt0e ltey h0 hoo /= measure_ge0.
rewrite (normalize_event mU hev) evp /p qbs_integral_mk;
  first exact: qbs_measurable_weighted_indic mU.
by rewrite -pdensity_preimage.
Qed.

(** Normalisation as a total map into P(X) + 1 (HKSY Sec. VI). *)
Definition normalize_sum p : coprodQ (probQ X) (unitQ R) :=
  if normalize p is Some q then inl q else inr tt.

Lemma normalize_sumE p : normalize_sum p =
  if normalize p is Some q then inl q else inr tt.
Proof. by []. Qed.

Lemma qbs_morphism_normalize :
  qbs_morphism (X := probQ (prodQ X (realQ R)))
    (Y := coprodQ (probQ X) (unitQ R)) normalize_sum.
Proof.
move=> b hb; have [a [g [ha mg g1 hbe]]] := hb.
pose pr r : probQ (prodQ X (realQ R)) := mkQBSProb a (giry_prob (g1 r)) ha.
have ebr r : b r = pr r.
  by apply/qbs_eqP => U mU; rewrite qbs_event_mk//; exact: hbe.
pose d r := pdensity (giry_prob (g1 r)) ha.
have evr r : evidence (b r) = d r [set: mR].
  rewrite ebr /d pdensityT /evidence qbs_integral_mk//.
  exact: qbs_measurable_weight.
pose P r := 0 < evidence (b r) < +oo.
have mev : measurable_fun [set: mR] (fun r => evidence (b r)).
  exact: (ge0_qbs_morphism_integral qbs_measurable_weight pweight_ge0 hb).
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
    apply/funext => r; rewrite /d /pdensity integral_mkcond /giry_int /=.
    apply: eq_integral => t _; rewrite /w patchE indicE.
    by case: (t \in A); rewrite /pweight ?mul1e ?mul0e.
  exact: measurableT_comp (measurable_giry_int mw w0) mg.
right; right; exists P, (fun r => normalize_prob (b r)), (fun=> tt).
split; first exact: mP.
split; last first.
  split=> // r.
  by rewrite /= /normalize_sum /normalize -/(P r); case: ifP.
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
- by move=> r U mU; rewrite ebr; exact: normalize_prob_event_mk.
Qed.

Definition normalizeQ :
    qbsHomType (probQ (prodQ X (realQ R))) (coprodQ (probQ X) (unitQ R)) :=
  HB.pack normalize_sum
    (isQBSMorphism.Build R _ _ _ qbs_morphism_normalize).

End normalize.
