(* -------------------------------------------------------------------- *)
(* Bayesian Linear Regression Example (Section 13)                      *)
(*                                                                      *)
(* A complete Bayesian linear regression example demonstrating the      *)
(* QBS probability monad in action:                                     *)
(*   - Independent priors on slope and intercept (product of normals)   *)
(*   - Likelihood function                                              *)
(*   - Predictive distribution via pair integration                     *)
(*   - Posterior via conditioning                                       *)
(* -------------------------------------------------------------------- *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import all_analysis.
From QBS Require Import quasi_borel probability_qbs pair_qbs_measure.

Import Num.Def Num.Theory reals classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section BayesianRegression.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* 1. Prior distribution on model parameters                             *)
(*    The model is y = slope * x + intercept + noise.                   *)
(*    We place independent normal priors on slope and intercept.         *)
(*                                                                      *)
(*    The joint prior is represented as the PAIR (slope_prior,          *)
(*    intercept_prior) and integrated via qbs_pair_integral, which      *)
(*    uses the product measure mu_slope x mu_intercept on mR x mR.     *)
(*    This gives truly independent priors (no shared randomness).       *)
(* ===================================================================== *)

(* Prior on slope: Normal(0, 1)
   Uses standard normal as the underlying measure with identity
   random element, so the QBS triple represents Normal(0, 1). *)
Definition slope_prior : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (normal_prob (0 : R) (1 : R) : probability mR R)
    (@measurable_id _ mR setT).

(* Prior on intercept: Normal(0, 1)
   Same construction as slope_prior. *)
Definition intercept_prior : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (normal_prob (0 : R) (1 : R) : probability mR R)
    (@measurable_id _ mR setT).

(* ===================================================================== *)
(* 2. Likelihood function                                                *)
(*    Given parameters (slope, intercept) and an observation (x, y),    *)
(*    the likelihood is proportional to                                 *)
(*    exp(-(y - slope*x - intercept)^2 / (2*sigma^2)).                 *)
(*    We model this as a morphism from parameters to P(realQ).           *)
(* ===================================================================== *)

(* Observation noise standard deviation *)
Variable (noise_sigma : R).
Variable (noise_sigma_pos : (0 < noise_sigma)%R).

(* The likelihood for a single data point (obs_x, obs_y):
   Given parameters (slope, intercept), produce a distribution on
   observed y-values centered at slope * obs_x + intercept.
   This is Normal(slope * obs_x + intercept, noise_sigma). *)
Definition likelihood_single (obs_x : R) :
  prodQ (realQ R) (realQ R) -> qbs_prob (realQ R) :=
  fun params =>
    @mkQBSProb R (realQ R) idfun
      (normal_prob (fst params * obs_x + snd params)%R noise_sigma
        : probability mR R)
      (@measurable_id _ mR setT).

(* The likelihood is a QBS morphism: for any random element beta of
   the parameter space, the composition likelihood_single(obs_x) o beta
   produces random elements of monadP(realQ R). This holds because
   the alpha component (identity) is always measurable. *)
Lemma likelihood_single_morph (obs_x : R) :
  @qbs_morph R (prodQ (realQ R) (realQ R)) (monadP (realQ R))
    (likelihood_single obs_x).
Proof.
move=> alpha halpha r /=.
exact: (@measurable_id _ mR setT).
Qed.

(* The likelihood satisfies the strong morphism condition: the alpha
   component (identity) is shared across all parameters. *)
Lemma likelihood_single_strong (obs_x : R) :
  @qbs_morph_strong R (prodQ (realQ R) (realQ R)) (realQ R)
    (likelihood_single obs_x).
Proof.
move=> alpha halpha.
exists idfun.
exists (fun r => normal_prob (fst (alpha r) * obs_x + snd (alpha r))%R
                   noise_sigma : probability mR R).
split; first exact: (@measurable_id _ mR setT).
by split.
Qed.

(* ===================================================================== *)
(* 3. Predictive distribution via pair integration                       *)
(*    The predictive integrates the likelihood over the independent     *)
(*    prior on (slope, intercept) using qbs_pair_integral, which        *)
(*    computes the integral w.r.t. mu_slope x mu_intercept.             *)
(* ===================================================================== *)

(* Predictive integral: for an observation x, integrates a function h
   over y-values against the likelihood, marginalized over the
   independent prior on (slope, intercept). *)
Definition predictive_integral (obs_x : R) (h : realQ R -> \bar R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => qbs_integral _ (likelihood_single obs_x params) h).

(* Predictive event probability: the probability of event U under
   the predictive distribution for observation x. *)
Definition predictive_event (obs_x : R) (U : set (realQ R)) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => qbs_prob_event _ (likelihood_single obs_x params) U).

(* ===================================================================== *)
(* 4. Marginalization identity (Fubini)                                  *)
(*    The predictive integral satisfies the law of total probability:   *)
(*    predictive_integral(h) = \int\int h(y) dP(y|s,i) dpi(s) dpi(i)  *)
(*    This is a direct consequence of qbs_pair_integral_eq (Fubini).    *)
(* ===================================================================== *)

Lemma predictive_marginal (obs_x : R) (h : realQ R -> \bar R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params => qbs_integral _ (likelihood_single obs_x params) h))) :
  predictive_integral obs_x h =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      qbs_integral _ (likelihood_single obs_x (s, i)) h)).
Proof.
rewrite /predictive_integral.
exact: qbs_pair_integral_eq.
Qed.

(* ===================================================================== *)
(* 5. Predictive event marginalization                                   *)
(*    The probability of an event U under the predictive equals         *)
(*    the double integral of likelihoods over the independent prior.    *)
(* ===================================================================== *)

Lemma predictive_event_marginal (obs_x : R) (U : set (realQ R))
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params => qbs_prob_event _ (likelihood_single obs_x params) U))) :
  predictive_event obs_x U =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      qbs_prob_event _ (likelihood_single obs_x (s, i)) U)).
Proof.
rewrite /predictive_event.
exact: qbs_pair_integral_eq.
Qed.

(* ===================================================================== *)
(* 6. Posterior distribution via conditioning (stated abstractly)        *)
(*    Given observed data, the posterior on parameters is obtained by    *)
(*    conditioning the joint distribution. We represent the posterior    *)
(*    integral using qbs_pair_integral with a reweighting by the        *)
(*    likelihood.                                                       *)
(* ===================================================================== *)

(* The posterior integral for parameters given observation (obs_x, obs_y):
   Integrates a function g over the parameter space, weighted by the
   likelihood of the observed data point.
   posterior_integral(g) = \int\int g(s,i) * lik(obs_y|s,i) d pi(s) d pi(i)
   (unnormalized; normalization requires the evidence/marginal likelihood) *)
Definition posterior_integral (obs_x obs_y : R)
  (g : realQ R * realQ R -> \bar R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params =>
      g params * qbs_prob_event _ (likelihood_single obs_x params) [set obs_y]).

(* ===================================================================== *)
(* 7. Key properties                                                     *)
(* ===================================================================== *)

(* The posterior integral decomposes as iterated integration (Fubini). *)
Lemma posterior_integral_eq (obs_x obs_y : R)
  (g : realQ R * realQ R -> \bar R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params =>
        g params * qbs_prob_event _ (likelihood_single obs_x params) [set obs_y]))) :
  posterior_integral obs_x obs_y g =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      g (s, i) * qbs_prob_event _ (likelihood_single obs_x (s, i)) [set obs_y])).
Proof.
rewrite /posterior_integral.
exact: qbs_pair_integral_eq.
Qed.

(* The posterior expectation of the slope is given by the pair integral *)
Lemma posterior_slope_expectation (obs_x obs_y : R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params =>
        (fst params)%:E *
        qbs_prob_event _ (likelihood_single obs_x params) [set obs_y]))) :
  posterior_integral obs_x obs_y (fun params => (fst params)%:E) =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      s%:E * qbs_prob_event _ (likelihood_single obs_x (s, i)) [set obs_y])).
Proof.
rewrite /posterior_integral.
exact: qbs_pair_integral_eq.
Qed.

(* Integration over first component only: when the integrand depends
   only on the slope, the intercept integral marginalizes out. *)
Lemma predictive_slope_marginal (obs_x : R) (h : realQ R -> \bar R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params => h (fst params)))) :
  qbs_pair_integral slope_prior intercept_prior
    (fun params => h (fst params)) =
  qbs_integral _ slope_prior h.
Proof.
exact: qbs_pair_integral_fst.
Qed.

End BayesianRegression.
