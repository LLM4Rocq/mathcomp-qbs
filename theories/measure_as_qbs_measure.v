(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology
  classical_sets borel_hierarchy numfun measure lebesgue_integral_definition
  lebesgue_stieltjes_measure lebesgue_measure lebesgue_integral probability
  measurable_realfun derive ftc gauss_integral charge boolp.
From mathcomp Require giry.
From QBS Require Import quasi_borel probability_qbs qbs_monad.

(**md**************************************************************************)
(* # Embedding Classical Probability into QBS Probability                     *)
(*                                                                            *)
(* Standard distributions as QBS probabilities. The general embedding of a    *)
(* probability measure on a standard Borel space is giry_to_qbs (qbs_giry.v). *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_normal_distribution mu sigma == Normal(mu, sigma) as QBS probability *)
(*   qbs_bernoulli p == Bernoulli(p) as QBS probability on boolQ             *)
(*   qbs_uniform == Uniform[0,1] as QBS probability on realQ                 *)
(*   qbs_expect_normal == E[Normal(mu,sigma)] = mu (assumes centred moment 0) *)
(*                        (requires integrability hypotheses)                *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import boolp order.Order.POrderTheory.

Local Open Scope classical_set_scope.

Section measure_as_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

Implicit Types (p mu sigma : R).

(** Standard distributions as QBS probabilities. *)

(** Normal distribution as QBS probability. *)
Definition qbs_normal_distribution (mu sigma : R) : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (normal_prob mu sigma : probability mR R)
    (@measurable_id _ mR setT).

Arguments qbs_normal_distribution : clear implicits.

(** Bernoulli distribution as QBS probability on boolQ. *)
Definition qbs_bernoulli
  (p : R) (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) : qbs_prob (boolQ R) :=
  @mkQBSProb R (boolQ R) (fun r : mR => (r < p)%R)
    (uniform_prob ltr01 : probability mR R)
    (measurable_fun_ltr
      (@measurable_id _ mR setT)
      (@measurable_cst _ _ mR mR setT p)).

Arguments qbs_bernoulli : clear implicits.

(** Uniform[0,1] distribution as QBS probability. *)
Definition qbs_uniform : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (uniform_prob ltr01 : probability mR R)
    (@measurable_id _ mR setT).


Lemma qbs_normal_morphism (sigma : R) :
  @qbs_morphism R (realQ R) (monadP (realQ R))
    (fun mu => qbs_normal_distribution mu sigma).
Proof.
move=> a ha; exists idfun, (fun r => normal_prob (a r) sigma : giry.giry mR R).
split => //.
- exact: (@measurable_id _ mR setT).
- apply: giry.measurable_giry_codensity => // B mB.
  exact: measurableT_comp (measurable_normal_prob _ mB) ha.
- by move=> r; exact: probability_setT.
Qed.

(** mu |-> N(mu, sigma) as a bundled morphism R -> P(R). *)
Definition qbs_normalQ (sigma : R) : qbsHomType (realQ R) (monadP (realQ R)) :=
  HB.pack (fun mu : realQ R => qbs_normal_distribution mu sigma : monadP _)
    (isQBSMorphism.Build R _ _ _ (qbs_normal_morphism sigma)).

(** Distribution expectation lemmas. *)

Section distribution_expectations.
Local Open Scope ring_scope.

(** E[Bernoulli(p)] = p. *)
Lemma qbs_expect_bernoulli (p : R) (hp0 : 0 <= p) (hp1 : p <= 1) :
  qbs_expect (boolQ R) (qbs_bernoulli p hp0 hp1) (fun b : bool => b%:R) = p%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
rewrite integral_uniform//.
- apply: measurableT_comp => //=; apply: measurableT_comp => //=.
  exact: measurable_fun_ltr (@measurable_id _ mR setT)
    (@measurable_cst _ _ mR mR setT p).
- by move=> x; rewrite lee_fin.
rewrite subr0 invr1 mul1e.
rewrite (_ : (fun x : mR => _) =
  (fun x => (indic [set r : mR | r < p] x)%:E)).
  by apply: funext => x /=; rewrite indicE mem_setE.
rewrite integral_indic //=.
  have -> : [set r : mR | r < p] = [set` `]-oo, p[%R].
    by apply/seteqP; split => x /=; rewrite in_itv /=.
  exact: measurable_itv.
have -> : [set r : mR | r < p] `&` `[0, 1] = [set` `[0%R, p[%R].
  apply/seteqP; split => x /=.
  - rewrite in_itv /= => -[xp]; rewrite in_itv /= => /andP[x0 x1].
    by apply/andP; split.
  - rewrite in_itv /= => /andP[x0 xp]; split => //.
    rewrite in_itv /=; apply/andP; split => //.
    exact: (le_trans (ltW xp) hp1).
rewrite -/(lebesgue_measure _).
rewrite lebesgue_measure_itv /= oppr0 adde0.
case: (lerP p 0) => [p0|p0].
- have -> : p = 0 by apply: le_anti; rewrite hp0 p0.
  by rewrite ltxx.
- by rewrite ifT // lte_fin.
Qed.

(** E[Uniform(0,1)] = 1/2. *)
Lemma qbs_expect_uniform :
  qbs_expect (realQ R) qbs_uniform (fun x => x) = (2%:R^-1)%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
rewrite integralE /=.
rewrite (@integral_uniform _ 0 1 ltr01 [eta funepos.body (@EFin R)]);
  [exact: measurable_funepos|by move=> x; exact: funepos_ge0|].
rewrite (@integral_uniform _ 0 1 ltr01 [eta funeneg.body (@EFin R)]);
  [exact: measurable_funeneg|by move=> x; exact: funeneg_ge0|].
rewrite subr0 invr1 mul1e mul1e -integralE /=.
rewrite (@continuous_FTC2 _ idfun (fun x => x ^+ 2 / 2) 0 1 ltr01).
- by apply: (@continuous_subspaceT _ _ _ idfun) => x /=; exact: cvg_id.
- split.
  + move=> x hx.
    by apply: derivableM;
      [exact: exprn_derivable|exact: derivable_cst].
  + have := @continuous_horner R (2^-1 *: 'X^2); move/(_ 0) => /=.
    rewrite /continuous_at /= hornerZ hornerXn expr0n /= mul0r mulr0 => h.
    suff -> : (fun x : R => x ^+ 2 / 2) = horner (2^-1 *: 'X^2 : {poly R}).
      by move: h; exact: cvg_within_filter.
    by apply: funext => x; rewrite hornerZ hornerXn mulrC.
  + have := @continuous_horner R (2^-1 *: 'X^2); move/(_ 1) => /=.
    rewrite /continuous_at /= hornerZ hornerXn expr1n mulr1 => h.
    suff -> : (fun x : R => x ^+ 2 / 2) = horner (2^-1 *: 'X^2 : {poly R}).
      by rewrite div1r; move: h; exact: cvg_within_filter.
    by apply: funext => x; rewrite hornerZ hornerXn mulrC.
- move=> x hx /=.
  rewrite derive1E deriveM;
    [exact: exprn_derivable|exact: derivable_cst|].
  rewrite derive_cst GRing.scaler0 GRing.add0r.
  rewrite (@derive_val _ _ _ _ _ _ _
    (is_deriveX 2 (is_derive_id x 1))) /=.
  by rewrite expr1 /GRing.scale /= mulr1 mulrA mulVf ?mul1r // pnatr_eq0.
- by rewrite expr0n /= mul0r oppr0 adde0 expr1n mul1r.
Qed.

(** E[Normal(mu,sigma)] = mu, conditional on the hypothesis centred_moment0
    that the centred first moment \int (x - mu) * pdf(x) dx vanishes (true:
    (x - mu) * pdf is odd around mu), which is not proved here. *)
Lemma qbs_expect_normal (mu sigma : R) (hsigma : 0 < sigma)
  (id_int : (\int[normal_prob mu sigma]_x `|x%:E| < +oo)%E)
  (centred_int : lebesgue_measure.-integrable setT
    (fun x => ((x - mu) * normal_pdf mu sigma x)%:E))
  (centred_moment0 : (\int[lebesgue_measure]_x
    ((x - mu) * normal_pdf mu sigma x)%:E = 0 :> \bar R)%E) :
  qbs_expect (realQ R) (qbs_normal_distribution mu sigma)
    (fun x => x) = mu%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
rewrite integral_normal_prob//=; first by apply/integrableP; split.
under eq_integral do rewrite -EFinM.
(* Split x * pdf = mu * pdf + (x - mu) * pdf *)
rewrite (_ : (fun x => (x * normal_pdf mu sigma x)%:E) =
  (fun x => (mu * normal_pdf mu sigma x +
             (x - mu) * normal_pdf mu sigma x)%:E)).
  by apply: funext => x /=; rewrite -mulrDl addrC subrK.
under eq_integral do rewrite EFinD.
have hint1 : lebesgue_measure.-integrable setT
    (fun x => (mu * normal_pdf mu sigma x)%:E).
  rewrite (_ : (fun x => (mu * _)%:E) =
    (fun x => mu%:E * (normal_pdf mu sigma x)%:E)%E).
    by apply: funext => x; rewrite EFinM.
  exact: (integrableZl measurableT mu (integrable_normal_pdf mu sigma)).
rewrite (integralD measurableT hint1 centred_int).
rewrite (_ : (fun x => (mu * normal_pdf mu sigma x)%:E) =
  (fun x => mu%:E * (normal_pdf mu sigma x)%:E)%E).
  by apply: funext => x; rewrite EFinM.
rewrite integralZl//=; first exact: integrable_normal_pdf.
by rewrite integral_normal_pdf -EFinM mulr1 centred_moment0 adde0.
Qed.

End distribution_expectations.

End measure_as_qbs.

Arguments qbs_normal_distribution {R}.
