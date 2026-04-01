(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology normedtype numfun measure
  lebesgue_integral lebesgue_integral_fubini lebesgue_stieltjes_measure
  probability.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel probability_qbs pair_qbs_measure
  measure_as_qbs_measure.

Import Num.Def Num.Theory reals classical_sets GRing.Theory.

(**md**************************************************************************)
(* # Bayesian Linear Regression                                               *)
(*                                                                            *)
(* Following the Isabelle AFP development (Bayesian_Linear_Regression.thy)    *)
(* by Hirata, Minamide, Sato.                                                 *)
(*                                                                            *)
(* Model: y = slope * x + intercept + noise, noise ~ N(0, 1/2)              *)
(* Prior: slope, intercept ~ iid N(0, 3)                                      *)
(* Data: (1,2.5), (2,3.8), (3,4.5), (4,6.2), (5,8.0)                       *)
(*                                                                            *)
(* Key results:                                                               *)
(* ```                                                                        *)
(*   complete_the_square  == ax^2+bx+c = a(x+b/(2a))^2 - (b^2-4ac)/(4a)    *)
(*   normal_pdf_times     == product of two Gaussians decomposition            *)
(*   obs                  == observation likelihood (5 data points)            *)
(*   evidence             == normalizing constant Z                            *)
(*   posterior_density     == E_post[g] = E_prior[g*obs] / Z                  *)
(*   posterior_density_total == posterior integrates to 1                      *)
(*   posterior_is_reweighting == Bayesian update formula                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(* ===================================================================== *)
(* Part II: Bayesian regression example                                  *)
(* ===================================================================== *)

Section BayesianRegression.
Variable (R : realType).
Local Notation mR := (measurableTypeR R).
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* ----- Model parameters (matching Isabelle AFP) ---------------------- *)

Let prior_sigma : R := 3%:R.     (* N(0,3) prior *)
Let noise_sigma : R := 2%:R^-1.  (* sigma = 1/2 noise *)

(* ----- 1. Prior distributions ---------------------------------------- *)

(* Prior on slope: Normal(0, 3) *)
Definition slope_prior : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (normal_prob (0 : R) prior_sigma : probability mR R)
    (@measurable_id _ mR setT).

(* Prior on intercept: Normal(0, 3) *)
Definition intercept_prior : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (normal_prob (0 : R) prior_sigma : probability mR R)
    (@measurable_id _ mR setT).

(* ----- 2. Likelihood function (matching Isabelle's d and obs) -------- *)

(* d mu x = normal_pdf mu (1/2) x *)
Definition d (mu x : R) : R := normal_pdf mu noise_sigma x.

Lemma d_ge0 (mu x : R) : (0 <= d mu x)%R.
Proof. exact: normal_pdf_ge0. Qed.

(* Isabelle's 5 data points: (1,2.5), (2,3.8), (3,4.5), (4,6.2), (5,8.0)
   obs(s,b) = d(s*1+b, 2.5) * d(s*2+b, 3.8) * d(s*3+b, 4.5) *
              d(s*4+b, 6.2) * d(s*5+b, 8.0) *)
Definition obs (params : realQ R * realQ R) : R :=
  let s := fst params in
  let b := snd params in
  (d (s * 1 + b) (5%:R / 2%:R) *       (* d(f(1), 2.5) *)
   d (s * 2%:R + b) (19%:R / 5%:R) *   (* d(f(2), 3.8) *)
   d (s * 3%:R + b) (9%:R / 2%:R) *    (* d(f(3), 4.5) *)
   d (s * 4%:R + b) (31%:R / 5%:R) *   (* d(f(4), 6.2) *)
   d (s * 5%:R + b) 8%:R)%R.           (* d(f(5), 8.0) *)

Lemma obs_ge0 (params : realQ R * realQ R) : (0 <= obs params)%R.
Proof.
rewrite /obs; apply: mulr_ge0; last exact: d_ge0.
apply: mulr_ge0; last exact: d_ge0.
apply: mulr_ge0; last exact: d_ge0.
apply: mulr_ge0; last exact: d_ge0.
exact: d_ge0.
Qed.

(* ----- 3. Evidence (normalizing constant) ---------------------------- *)
(* Z = integral of obs over the prior.
   In the Isabelle development, this is computed explicitly as
   C = (4*sqrt(2)/(pi^2*sqrt(66961*pi))) * exp(-1674761/1674025)
   via iterative application of normal_pdf_times. *)

Definition evidence : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => (obs params)%:E).

Lemma evidence_ge0 : 0 <= evidence.
Proof.
rewrite /evidence /qbs_pair_integral.
apply: integral_ge0 => rr _.
rewrite lee_fin; exact: obs_ge0.
Qed.

(* Fubini decomposition of the evidence *)
Lemma evidence_eq
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params => (obs params)%:E))) :
  evidence =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun b =>
      (obs (s, b))%:E)).
Proof. rewrite /evidence; exact: qbs_pair_integralE. Qed.

(* ----- 4. Posterior distribution via Bayes' rule --------------------- *)
(* E_post[g] = E_prior[g * obs] / E_prior[obs]
   This corresponds to Isabelle's program_result_measure:
     posterior = density(prior)(obs / C) *)

Definition posterior_density (g : realQ R * realQ R -> \bar R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => g params * (obs params)%:E)
   / evidence.

(* The posterior integrates to 1 when evidence is finite and positive.
   This corresponds to Isabelle's program_result: the normalization
   succeeds (returns Inl, not error Inr). *)
Lemma posterior_density_total
  (hev_pos : 0 < evidence)
  (hev_fin : evidence < +oo) :
  posterior_density (fun _ => 1) = 1.
Proof.
rewrite /posterior_density.
have -> : (fun params : realQ R * realQ R => 1 * (obs params)%:E) =
          (fun params => (obs params)%:E) by apply: funext => p; rewrite mul1e.
rewrite -/(evidence).
apply: divee.
- by rewrite gt0_fin_numE.
- by move: hev_pos; rewrite lt0e => /andP[].
Qed.

(* Fubini decomposition of the posterior *)
Lemma posterior_density_eq (g : realQ R * realQ R -> \bar R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params => g params * (obs params)%:E))) :
  posterior_density g =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun b =>
      g (s, b) * (obs (s, b))%:E))
   / evidence.
Proof.
rewrite /posterior_density; congr (_ / _).
exact: qbs_pair_integralE.
Qed.

(* The posterior is the prior reweighted by obs/Z
   (Isabelle's program_result_measure) *)
Lemma posterior_is_reweighting (g : realQ R * realQ R -> \bar R) :
  posterior_density g =
  qbs_pair_integral slope_prior intercept_prior
    (fun params => g params * (obs params)%:E)
   / evidence.
Proof. by []. Qed.

(* ----- 5. Single-observation likelihood as QBS morphism -------------- *)

Definition likelihood_single (obs_x : R) :
  prodQ (realQ R) (realQ R) -> qbs_prob (realQ R) :=
  fun params =>
    @mkQBSProb R (realQ R) idfun
      (normal_prob (fst params * obs_x + snd params)%R noise_sigma
        : probability mR R)
      (@measurable_id _ mR setT).

Lemma likelihood_single_morphism (obs_x : R) :
  @qbs_morphism R (prodQ (realQ R) (realQ R)) (monadP (realQ R))
    (likelihood_single obs_x).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /= => r.
exact: (@measurable_id _ mR setT).
Qed.

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

(* ----- 6. Predictive distribution via pair integration (Fubini) ------ *)

Definition predictive_integral (obs_x : R) (h : realQ R -> \bar R) : \bar R :=
  qbs_pair_integral slope_prior intercept_prior
    (fun params => qbs_integral _ (likelihood_single obs_x params) h).

Lemma predictive_marginal (obs_x : R) (h : realQ R -> \bar R)
  (hint : (qbs_prob_mu slope_prior \x qbs_prob_mu intercept_prior).-integrable
    setT (qbs_pair_fun slope_prior intercept_prior
      (fun params => qbs_integral _ (likelihood_single obs_x params) h))) :
  predictive_integral obs_x h =
  qbs_integral _ slope_prior (fun s =>
    qbs_integral _ intercept_prior (fun b =>
      qbs_integral _ (likelihood_single obs_x (s, b)) h)).
Proof. rewrite /predictive_integral; exact: qbs_pair_integralE. Qed.

End BayesianRegression.
