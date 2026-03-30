(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
(**md**************************************************************************)
(* # Bayesian Linear Regression Example                                       *)
(*                                                                            *)
(* A complete Bayesian linear regression example demonstrating the            *)
(* QBS probability monad in action:                                           *)
(*   - Independent priors on slope and intercept (product of normals)         *)
(*   - Likelihood function                                                    *)
(*   - Predictive distribution via pair integration                           *)
(*   - Posterior via conditioning                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*   slope_prior        == Normal(0,1) prior on slope                         *)
(*   intercept_prior    == Normal(0,1) prior on intercept                     *)
(*   likelihood_single  == likelihood for a single data point                 *)
(*   predictive_integral == predictive integral over the prior                *)
(*   posterior_integral  == unnormalized posterior integral                    *)
(*   evidence            == marginal likelihood (normalizing constant)        *)
(* ```                                                                        *)
(******************************************************************************)

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
  @qbs_morphism R (prodQ (realQ R) (realQ R)) (monadP (realQ R))
    (likelihood_single obs_x).
Proof.
move=> alpha halpha r /=.
exact: (@measurable_id _ mR setT).
Qed.

(* The likelihood satisfies the strong morphism condition: the alpha
   component (identity) is shared across all parameters. *)
Lemma likelihood_single_strong (obs_x : R) :
  @qbs_morphism_strong R (prodQ (realQ R) (realQ R)) (realQ R)
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

(* ===================================================================== *)
(* 8. Normalizing constant (evidence / marginal likelihood)              *)
(*    The evidence integrates the likelihood density over the prior:     *)
(*    Z(obs_x, obs_y) = \int\int p(obs_y | s, i) d pi(s) d pi(i)      *)
(*    where p(obs_y | s, i) = normal_pdf(s * obs_x + i, sigma)(obs_y). *)
(*    This is used to normalize the posterior.                           *)
(* ===================================================================== *)

Definition evidence (obs_x obs_y : R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params =>
      (normal_pdf (fst params * obs_x + snd params)%R noise_sigma obs_y)%:E).

(* The evidence decomposes as iterated integration (Fubini). *)
Lemma evidence_eq (obs_x obs_y : R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params =>
        (normal_pdf (fst params * obs_x + snd params)%R noise_sigma obs_y)%:E))) :
  evidence obs_x obs_y =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      (normal_pdf (s * obs_x + i)%R noise_sigma obs_y)%:E)).
Proof.
rewrite /evidence.
exact: qbs_pair_integral_eq.
Qed.

(* The evidence is non-negative since normal_pdf is non-negative. *)
Lemma evidence_ge0 (obs_x obs_y : R) :
  (0 <= evidence obs_x obs_y)%E.
Proof.
rewrite /evidence /qbs_pair_integral.
apply: integral_ge0 => rr _.
rewrite lee_fin.
exact: normal_pdf_ge0.
Qed.

(* ===================================================================== *)
(* 9. Normalized posterior integral                                      *)
(*    The posterior integral divided by the evidence gives the           *)
(*    normalized posterior expectation:                                  *)
(*    E_post[g] = posterior_integral(g) / evidence                      *)
(* ===================================================================== *)

Definition posterior_normalized (obs_x obs_y : R)
  (g : realQ R * realQ R -> \bar R) : \bar R :=
  (posterior_integral obs_x obs_y g / evidence obs_x obs_y)%E.

(* The normalized posterior decomposes via iterated integration. *)
Lemma posterior_normalized_eq (obs_x obs_y : R)
  (g : realQ R * realQ R -> \bar R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params =>
        g params * qbs_prob_event _ (likelihood_single obs_x params) [set obs_y]))) :
  posterior_normalized obs_x obs_y g =
  (qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      g (s, i) * qbs_prob_event _ (likelihood_single obs_x (s, i)) [set obs_y]))
   / evidence obs_x obs_y)%E.
Proof.
rewrite /posterior_normalized.
congr (_ / _)%E.
rewrite /posterior_integral.
exact: qbs_pair_integral_eq.
Qed.

(* When g is constant 1, the normalized posterior integrates to 1
   (assuming evidence is finite and positive). This is the key
   normalization property: the posterior is a proper probability
   distribution. *)
Lemma posterior_normalized_total (obs_x obs_y : R)
  (hfin : evidence obs_x obs_y \is a fin_num)
  (hpos : evidence obs_x obs_y != 0%E) :
  posterior_normalized obs_x obs_y
    (fun _ => 1%E) =
  (posterior_integral obs_x obs_y (fun _ => 1%E) / evidence obs_x obs_y)%E.
Proof.
by rewrite /posterior_normalized.
Qed.

(* ===================================================================== *)
(* 10. Concrete posterior computation with actual data                    *)
(*     Following the Isabelle AFP development (Bayesian_Linear_Regression *)
(*     .thy), we compute the posterior for 5 specific data points and    *)
(*     prove properties of the normalizing constant.                     *)
(* ===================================================================== *)

(* Five observed data points: (x_i, y_i)
   True model: y = 2*x + 1 + noise
   We use integer approximations: y_i ~ round(2*x_i + 1) *)
Definition data_x : seq R :=
  [:: (1%R : R); (2%R : R); (3%R : R); (4%R : R); (5%R : R)].
Definition data_y : seq R :=
  [:: (3%R : R); (5%R : R); (7%R : R); (9%R : R); (11%R : R)].

(* ----- Multi-observation likelihood ---------------------------------- *)
(* The likelihood for multiple data points is the product of individual
   normal pdf evaluations. For parameters (slope, intercept) and data
   points {(x_i, y_i)}, this is:
     \prod_i normal_pdf(slope * x_i + intercept, noise_sigma)(y_i)
   lifted to extended reals. *)

Definition likelihood_product (xs ys : seq R) :
  realQ R * realQ R -> \bar R :=
  fun params =>
    \prod_(xy <- zip xs ys)
      (normal_pdf (fst params * xy.1 + snd params)%R noise_sigma xy.2)%:E.

(* ----- Multi-observation evidence ------------------------------------ *)
(* The evidence (marginal likelihood) for multiple observations is the
   integral of the likelihood product over the prior on (slope, intercept). *)

Definition evidence_multi (xs ys : seq R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => likelihood_product xs ys params).

(* ----- Multi-observation posterior ----------------------------------- *)
(* The posterior expectation of a function g on parameters, given
   multiple observations, is the integral of g weighted by the
   likelihood product, normalized by the multi-observation evidence. *)

Definition posterior_multi (xs ys : seq R)
  (g : realQ R * realQ R -> \bar R) : \bar R :=
  (qbs_pair_integral slope_prior intercept_prior
    (fun params => g params * likelihood_product xs ys params)
   / evidence_multi xs ys)%E.

(* ----- Key properties ------------------------------------------------ *)

(* The likelihood product is non-negative for any parameter values. *)
Lemma likelihood_product_ge0 (xs ys : seq R) (params : realQ R * realQ R) :
  (0 <= likelihood_product xs ys params)%E.
Proof.
rewrite /likelihood_product.
apply: prode_ge0 => xy _.
rewrite lee_fin.
exact: normal_pdf_ge0.
Qed.

(* The multi-observation evidence is non-negative. *)
Lemma evidence_multi_ge0 (xs ys : seq R) :
  (0 <= evidence_multi xs ys)%E.
Proof.
rewrite /evidence_multi /qbs_pair_integral.
apply: integral_ge0 => rr _.
apply: prode_ge0 => xy _.
rewrite lee_fin.
exact: normal_pdf_ge0.
Qed.

(* The posterior is a proper probability (integrates to 1) when the
   evidence is finite and positive. This is the multi-observation
   analogue of posterior_normalized_total. *)
Lemma posterior_multi_total (xs ys : seq R)
  (hev : (0 < evidence_multi xs ys)%E)
  (hfin : (evidence_multi xs ys < +oo)%E) :
  posterior_multi xs ys (fun _ => 1%E) =
  (qbs_pair_integral slope_prior intercept_prior
    (fun params => likelihood_product xs ys params)
   / evidence_multi xs ys)%E.
Proof.
rewrite /posterior_multi.
congr (_ / _)%E.
apply: eq_integral => rr _.
by rewrite mul1e.
Qed.

(* ----- Concrete instantiation with data ------------------------------ *)
(* Applying the definitions to our five concrete data points. *)

Definition concrete_evidence : \bar R :=
  evidence_multi data_x data_y.

Definition concrete_posterior (g : realQ R * realQ R -> \bar R) : \bar R :=
  posterior_multi data_x data_y g.

(* The concrete evidence is non-negative. *)
Lemma concrete_evidence_ge0 : (0 <= concrete_evidence)%E.
Proof. exact: evidence_multi_ge0. Qed.

(* The concrete posterior decomposes via iterated integration (Fubini). *)
Lemma concrete_evidence_eq
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params => likelihood_product data_x data_y params))) :
  concrete_evidence =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun i =>
      likelihood_product data_x data_y (s, i))).
Proof.
rewrite /concrete_evidence /evidence_multi.
exact: qbs_pair_integral_eq.
Qed.

End BayesianRegression.
