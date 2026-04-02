(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology normedtype numfun measure
  lebesgue_integral lebesgue_integral_fubini lebesgue_stieltjes_measure
  lebesgue_measure probability charge.
From mathcomp.classical Require Import boolp.
From mathcomp.algebra_tactics Require Import ring.
From QBS Require Import quasi_borel probability_qbs pair_qbs_measure
  measure_as_qbs_measure normal_algebra.

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
(*   prior             == joint prior on (slope, intercept) as product QBS    *)
(*   prior_bind        == same prior via monadic bind/return                  *)
(*   norm_qbs          == normalizer: weighted QBS prob -> option density     *)
(*   program           == full Bayesian program: norm_qbs (fun _ => 1) obs   *)
(*   obs               == observation likelihood (5 data points)              *)
(*   evidence          == normalizing constant Z                              *)
(*   posterior_density  == E_post[g] = E_prior[g*obs] / Z                    *)
(*   posterior_density_total == posterior integrates to 1                      *)
(*   program_succeeds  == program returns Some when evidence is good          *)
(*   program_integrates_to_1 == program result integrates to 1                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(* ===================================================================== *)
(* Integration against normal_prob via Radon-Nikodym                     *)
(* ===================================================================== *)

Section IntegralNormalProb.
Variable (R : realType).
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* Convert integration against normal_prob to Lebesgue integration
   with the normal_pdf density. This is the normal-distribution
   analogue of integral_beta_prob from mathcomp-analysis. *)
Lemma integral_normal_prob (m sigma : R) (hsigma : (sigma != 0)%R)
    f (f_meas : measurable_fun setT f)
    (f_int : (\int[normal_prob m sigma]_x `|f x| < +oo)%E) :
  \int[normal_prob m sigma]_x f x =
  \int[mu]_x (f x * (normal_pdf m sigma x)%:E).
Proof.
rewrite -(Radon_Nikodym_change_of_variables
            (normal_prob_dominates m sigma) measurableT); last first.
  by apply/integrableP; split.
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //; apply: (measurable_int mu).
  apply: (integrableS _ _ (@subsetT _ _)) => //=.
  by apply: Radon_Nikodym_integrable; exact: normal_prob_dominates.
- apply: emeasurable_funM => //=; apply/measurableT_comp => //=.
  by apply/measurable_funTS; exact: measurable_normal_pdf.
- apply: ae_eqe_mul2l => /=.
  rewrite Radon_NikodymE//=; first exact: normal_prob_dominates.
  move=> ?.
  case: cid => /= h [h1 h2 h3].
  apply: integral_ae_eq => //=.
  + apply/measurable_EFinP; exact: measurable_normal_pdf.
  + by move=> E E01 mE; rewrite -h3.
Qed.

End IntegralNormalProb.

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

Lemma prior_sigma_gt0 : (0 < prior_sigma)%R.
Proof. by rewrite /prior_sigma ltr0n. Qed.

(* Prior on slope: Normal(0, 3) *)
Definition slope_prior : qbs_prob (realQ R) :=
  @qbs_normal_distribution R (0 : R) prior_sigma prior_sigma_gt0.

(* Prior on intercept: Normal(0, 3) *)
Definition intercept_prior : qbs_prob (realQ R) :=
  @qbs_normal_distribution R (0 : R) prior_sigma prior_sigma_gt0.

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
rewrite /obs.
do 4! (apply: mulr_ge0; last exact: d_ge0).
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

(* ----- 7. Monadic prior on the parameter space ----------------------- *)
(* Isabelle's prior: do { s <- nu; b <- nu; return (fun r => s*r+b) }

   In Isabelle, the prior is a probability on the function space
   expQ R (realQ R) (realQ R), built by sampling slope s and intercept b
   from the standard Gaussian (nu), then returning the function r |-> s*r+b.

   Constructing this directly on expQ requires packaging
   (fun r => s*r+b) as a qbsHomType, i.e., proving that for each (s,b),
   the map r |-> s*r+b is a QBS morphism. While this is straightforward
   (it is a measurable hence QBS-morphic function), the monadic bind on
   expQ also requires the strong morphism condition for the return map
   (s,b) |-> (fun r => s*r+b) : prodQ (realQ R) (realQ R) -> expQ ...

   Instead, we provide the equivalent pair-based formulation: the prior
   is a QBS probability on prodQ (realQ R) (realQ R) representing the
   joint distribution of (slope, intercept). This is isomorphic to the
   function-space version via the bijection (s,b) <-> (fun r => s*r+b).

   The pair formulation is standard in Bayesian computation and matches
   how the posterior is already defined above. *)

Definition prior : qbs_prob (prodQ (realQ R) (realQ R)) :=
  qbs_prob_pair slope_prior intercept_prior.

(* The monadic construction of the prior:
   prior_bind = bind(slope_prior, fun s =>
                  bind(intercept_prior, fun b =>
                    return (s, b)))

   We construct this using qbs_bind with explicit diagonal randomness
   proofs. The inner bind at fixed s produces a QBS probability on
   (realQ R * realQ R) with alpha r |-> (s, idfun r) = (s, r). *)

(* Diagonal randomness for the inner bind: r |-> (s, idfun r) *)
Lemma prior_inner_diag (s : realQ R) :
  @qbs_Mx R (prodQ (realQ R) (realQ R))
    (fun r => qbs_prob_alpha
      ((fun b => qbs_return (prodQ (realQ R) (realQ R)) (s, b)
                   (qbs_prob_mu intercept_prior))
       (qbs_prob_alpha intercept_prior r)) r).
Proof.
rewrite /= /qbs_Mx /=; split.
- exact: (@qbs_Mx_const R (realQ R) s).
- exact: (@measurable_id _ mR setT).
Qed.

Definition prior_inner (s : realQ R) : qbs_prob (prodQ (realQ R) (realQ R)) :=
  @qbs_bind R (realQ R) (prodQ (realQ R) (realQ R))
    intercept_prior
    (fun b => qbs_return (prodQ (realQ R) (realQ R)) (s, b)
                (qbs_prob_mu intercept_prior))
    (prior_inner_diag s).

(* Diagonal randomness for the outer bind *)
Lemma prior_bind_diag :
  @qbs_Mx R (prodQ (realQ R) (realQ R))
    (fun r => qbs_prob_alpha
      (prior_inner (qbs_prob_alpha slope_prior r)) r).
Proof.
rewrite /= /qbs_Mx /=; split.
- exact: (@measurable_id _ mR setT).
- exact: (@measurable_id _ mR setT).
Qed.

(* The full monadic prior:
   prior_bind = bind(slope_prior, fun s =>
                  bind(intercept_prior, fun b => return (s,b))) *)
Definition prior_bind : qbs_prob (prodQ (realQ R) (realQ R)) :=
  @qbs_bind R (realQ R) (prodQ (realQ R) (realQ R))
    slope_prior prior_inner prior_bind_diag.

(* ----- 8. Normalizer (norm_qbs) -------------------------------------- *)
(* Isabelle's norm_qbs_measure: given a weighted QBS probability, either
   return the normalized probability (when evidence is positive and finite)
   or signal an error. We model the error case with option.

   norm_qbs g obs_fn computes the evidence
     ev = integral of obs_fn over the joint prior
   and if 0 < ev < +oo, returns Some (fun p => g(p) * obs_fn(p) / ev),
   otherwise returns None (corresponding to Isabelle's Inr error). *)

Definition norm_qbs
    (g : realQ R * realQ R -> \bar R)
    (obs_fn : realQ R * realQ R -> R)
    : option (realQ R * realQ R -> \bar R) :=
  let ev := qbs_pair_integral slope_prior intercept_prior
              (fun p => (obs_fn p)%:E) in
  if (0 < ev) && (ev < +oo) then
    Some (fun p => g p * (obs_fn p)%:E / ev)
  else None.

(* The normalizer returns Some when evidence is positive and finite *)
Lemma norm_qbs_some (g : realQ R * realQ R -> \bar R)
  (obs_fn : realQ R * realQ R -> R)
  (hev_pos : 0 < qbs_pair_integral slope_prior intercept_prior
               (fun p => (obs_fn p)%:E))
  (hev_fin : qbs_pair_integral slope_prior intercept_prior
               (fun p => (obs_fn p)%:E) < +oo) :
  norm_qbs g obs_fn =
  Some (fun p => g p * (obs_fn p)%:E /
          qbs_pair_integral slope_prior intercept_prior
            (fun p => (obs_fn p)%:E)).
Proof.
rewrite /norm_qbs.
case: ifPn => // /negP.
move/negP; rewrite negb_and => /orP[/negP|/negP]; contradiction.
Qed.

(* The normalizer returns None when evidence is zero or infinite *)
Lemma norm_qbs_none (g : realQ R * realQ R -> \bar R)
  (obs_fn : realQ R * realQ R -> R)
  (hev : ~ ((0 < qbs_pair_integral slope_prior intercept_prior
                 (fun p => (obs_fn p)%:E)) /\
             (qbs_pair_integral slope_prior intercept_prior
                 (fun p => (obs_fn p)%:E) < +oo))) :
  norm_qbs g obs_fn = None.
Proof.
rewrite /norm_qbs.
case: ifPn => // /andP[h1 h2].
by exfalso; apply: hev.
Qed.

(* ----- 9. The Bayesian program --------------------------------------- *)
(* Isabelle's program:
     program = norm_qbs_measure (pushforward prior (fun f => (f, obs f)))
   In our pair formulation, the pushforward through (fun f => (f, obs f))
   is just the observation function obs applied to the prior parameters.
   So program = norm_qbs (fun _ => 1) obs. *)

Definition program : option (realQ R * realQ R -> \bar R) :=
  norm_qbs (fun _ => 1) obs.

(* When evidence is positive and finite, the program succeeds *)
Lemma program_succeeds
  (hev_pos : 0 < evidence)
  (hev_fin : evidence < +oo) :
  program = Some (fun p => 1 * (obs p)%:E / evidence).
Proof.
rewrite /program /norm_qbs -/(evidence).
case: ifPn => // /negP.
move/negP; rewrite negb_and => /orP[/negP|/negP]; contradiction.
Qed.

(* ----- 10. Program result -------------------------------------------- *)
(* When evidence is positive and finite, the program succeeds and the
   resulting density integrates to 1 (matching Isabelle's program_result).

   The connection: the density returned by norm_qbs (fun _ => 1) obs
   is precisely the function p |-> 1 * obs(p) / evidence = obs(p) / Z,
   which is the posterior density. Integrating this over the prior gives
   posterior_density (fun _ => 1) = 1 by posterior_density_total. *)

Theorem program_integrates_to_1
  (hev_pos : 0 < evidence)
  (hev_fin : evidence < +oo) :
  exists density,
    program = Some density /\
    posterior_density (fun _ => 1) = 1.
Proof.
exists (fun p => 1 * (obs p)%:E / evidence); split.
- rewrite /program /norm_qbs -/(evidence).
  case: ifPn => // /negP.
  move/negP; rewrite negb_and => /orP[/negP|/negP]; contradiction.
- exact: posterior_density_total.
Qed.

(* ===================================================================== *)
(* 11. Phase 1 integration: integrate out the intercept b                *)
(* ===================================================================== *)
(* The evidence integral decomposes via Fubini as:
     evidence = ∫[N(0,3)]_s ∫[N(0,3)]_b obs(s,b)

   Phase 1 evaluates the inner integral ∫[N(0,3)]_b obs(s,b) for
   fixed s.  The key steps are:

   (a) Convert to Lebesgue integral with density via integral_normal_prob:
         ∫[N(0,3)]_b obs(s,b) = ∫[leb]_b obs(s,b) * N(0,3,b)

   (b) Rewrite obs(s,b) * N(0,3,b) using the algebraic identities
       obs_rewrite + phase1_combine5 (from normal_algebra.v):
         N(0,3,b) * obs_factors(s,b) = scalar_of_s(s) * N(mu5(s), sigma5, b)

   (c) Factor out scalar_of_s(s) via ge0_integralZl_EFin:
         = scalar_of_s(s) * ∫[leb]_b N(mu5(s), sigma5, b)

   (d) Evaluate the remaining integral via integral_normal_pdf:
         ∫[leb]_b N(mu5(s), sigma5, b) = 1

   Result: ∫[N(0,3)]_b obs(s,b) = scalar_of_s(s).

   The scalar_of_s function is the product of 5 gaussian_prod_scalar
   factors, each of the form normal_peak(S_k) * normal_fun(mu_k, S_k, m'_k),
   arising from the iterative combination of the prior N(0,3) with each
   data-point factor via normal_pdf_times.                                 *)

(* The Phase 1 scalar: product of 5 gaussian_prod_scalar terms.
   Each factor is normal_peak(sqrt(sigma_k^2 + sigma'^2)) *
   normal_fun(mu_k, sqrt(sigma_k^2 + sigma'^2), m'_k).
   This matches the scalar part of phase1_combine5 from normal_algebra.v.
   The gaussian_prod_scalar definition is:
     gaussian_prod_scalar m m' s s' := normal_peak(sqrt(s^2+s'^2)) * normal_fun(m, sqrt(s^2+s'^2), m') *)
Definition scalar_of_s (s : R) : R :=
  (* Step 0->1: N(0,3) * N(5/2-s, 1/2) *)
  (normal_peak (sqrtr (3%:R ^+ 2 + (2%:R^-1 : R) ^+ 2)) *
   normal_fun 0 (sqrtr (3%:R ^+ 2 + (2%:R^-1 : R) ^+ 2)) (5%:R / 2%:R - s)) *
  (* Step 1->2: result * N(19/5-2s, 1/2) *)
  (normal_peak (sqrtr (sqrtr (9%:R / 37%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2)) *
   normal_fun ((90%:R - 36%:R * s) / 37%:R)
     (sqrtr (sqrtr (9%:R / 37%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2))
     (19%:R / 5%:R - 2%:R * s)) *
  (* Step 2->3: result * N(9/2-3s, 1/2) *)
  (normal_peak (sqrtr (sqrtr (9%:R / 73%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2)) *
   normal_fun ((1134%:R - 540%:R * s) / 365%:R)
     (sqrtr (sqrtr (9%:R / 73%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2))
     (9%:R / 2%:R - 3%:R * s)) *
  (* Step 3->4: result * N(31/5-4s, 1/2) *)
  (normal_peak (sqrtr (sqrtr (9%:R / 109%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2)) *
   normal_fun ((1944%:R - 1080%:R * s) / 545%:R)
     (sqrtr (sqrtr (9%:R / 109%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2))
     (31%:R / 5%:R - 4%:R * s)) *
  (* Step 4->5: result * N(8-5s, 1/2) *)
  (normal_peak (sqrtr (sqrtr (9%:R / 145%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2)) *
   normal_fun ((612%:R - 360%:R * s) / 145%:R)
     (sqrtr (sqrtr (9%:R / 145%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2))
     (8%:R - 5%:R * s)).

Lemma scalar_of_s_ge0 (s : R) : (0 <= scalar_of_s s)%R.
Proof.
rewrite /scalar_of_s.
apply: mulr_ge0; last by apply: mulr_ge0; [exact: normal_peak_ge0 | exact: normal_fun_ge0].
apply: mulr_ge0; last by apply: mulr_ge0; [exact: normal_peak_ge0 | exact: normal_fun_ge0].
apply: mulr_ge0; last by apply: mulr_ge0; [exact: normal_peak_ge0 | exact: normal_fun_ge0].
apply: mulr_ge0; last by apply: mulr_ge0; [exact: normal_peak_ge0 | exact: normal_fun_ge0].
by apply: mulr_ge0; [exact: normal_peak_ge0 | exact: normal_fun_ge0].
Qed.

(* Intermediate parameters after all 5 Phase 1 combination steps *)
Let phase1_mu5 (s : R) : R := (900%:R - 540%:R * s) / 181%:R.
Let phase1_sigma5 : R := sqrtr (9%:R / 181%:R).

(* Phase 1 integration: integrating obs(s,b) against the intercept
   prior N(0,3) yields the scalar_of_s(s). The algebraic identity
   (obs_rewrite + phase1_combine5) is imported from normal_algebra.v.

   Remaining hypotheses:
   - obs_meas: Measurability of obs as a function of b at fixed s.
   - obs_int: Integrability of |obs(s,b)| against N(0,3). *)
Lemma phase1_integration (s : R)
  (obs_meas : measurable_fun [set: mR]
    (fun b : mR => (obs (s, b))%:E :> \bar R))
  (obs_int : (\int[normal_prob 0 prior_sigma]_b
    `|(obs (s, b))%:E| < +oo)%E)
  :
  \int[normal_prob (0 : R) prior_sigma]_b (obs (s, b))%:E =
  (scalar_of_s s)%:E.
Proof.
have h3 : (prior_sigma != 0)%R by rewrite /prior_sigma pnatr_eq0.
rewrite (integral_normal_prob h3) //.
under eq_integral do rewrite -EFinM.
have step1 : forall x : R, (obs (s, x) * normal_pdf 0 prior_sigma x =
  scalar_of_s s * normal_pdf (phase1_mu5 s) phase1_sigma5 x)%R.
  move=> x; rewrite mulrC /obs /d /prior_sigma /noise_sigma.
  rewrite (obs_rewrite s x) !mulrA.
  exact: (phase1_combine5 s x).
under eq_integral do rewrite step1.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin //.
- rewrite integral_normal_pdf mule1 //.
- move=> x _; rewrite lee_fin; exact: normal_pdf_ge0.
- apply/measurableT_comp => //; exact: measurable_normal_pdf.
- exact: scalar_of_s_ge0.
Qed.

(* ===================================================================== *)
(* 12. Assembly chain: evidence computation                               *)
(* ===================================================================== *)
(* The full evidence computation chain:
   evidence = ∫∫ obs(s,b) = ∫ scalar_of_s(s) = C
   Phase 1 (this file): integrate out b using obs_rewrite + phase1_combine5.
   Phase 2 (normal_algebra.v): integrate out s similarly.
   Algebraic lemmas live in normal_algebra.v. *)

End BayesianRegression.
