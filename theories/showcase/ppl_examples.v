(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal classical_sets num_topology
  measurable_structure measurable_function lebesgue_stieltjes_measure
  measurable_realfun probability.
From mathcomp Require Import measure lebesgue_integral probability.
From mathcomp Require Import boolp.
From mathcomp Require Import ring.
From QBS Require Import quasi_borel probability_qbs pair_qbs_measure
  measure_as_qbs_measure.

(**md**************************************************************)
(* # Higher-Order Probabilistic Programs in QBS                    *)
(*                                                                  *)
(* This file showcases probabilistic programs whose denotational   *)
(* semantics require QBS function spaces -- distributions over     *)
(* functions -- which are impossible in the classical kernel-based *)
(* semantics of measurable spaces.                                  *)
(*                                                                  *)
(* Key constructions:                                               *)
(* ```                                                              *)
(*   random_constant    == distribution over constant functions    *)
(*                         lambda x. c with c ~ Normal(0,1)        *)
(*   random_linear      == distribution over linear functions      *)
(*                         lambda x. m*x+b with m,b ~ Normal(0,1)  *)
(*   random_sampler     == distribution over samplers              *)
(*                         lambda x. Normal(mu*x, 1) with mu ~ ... *)
(* ```                                                              *)
(*                                                                  *)
(* Why QBS? In ordinary measure-theoretic semantics, these programs *)
(* have no denotation: the function space R -> R cannot be given a *)
(* sigma-algebra that makes both evaluation and currying measurable.*)
(* QBS resolves this via the cartesian-closed category of           *)
(* quasi-Borel spaces, in which exponentials expQ X Y exist and     *)
(* currying/evaluation are QBS morphisms.                           *)
(******************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section higher_order_examples.
Variable R : realType.
Local Notation mR := (measurableTypeR R).
Local Open Scope ring_scope.

(** * Packaging QBS morphisms into [qbsHomType] *)

(** Small helper to promote a plain [qbs_morphism] proof to the
    bundled [qbsHomType R X Y] structure required by
    [qbs_morphism_curry]. *)
Definition pack_hom (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism R X Y f) : @qbsHomType R X Y :=
  HB.pack f (@isQBSMorphism.Build R X Y f
    (fun alpha ha => hf alpha ha)).

(** * Example 1: random constant functions *)

(** Inner function underlying the constant family: given a value
    [c : realQ] and an input [x : realQ], return [c] (ignoring
    [x]). As a morphism [prodQ realQ realQ -> realQ] it is just
    the first projection. *)
Definition const_body : prodQ (realQ R) (realQ R) -> realQ R :=
  fun p => p.1.

Lemma const_body_morphism :
  @qbs_morphism R (prodQ (realQ R) (realQ R)) (realQ R)
    const_body.
Proof. exact: qbs_morphism_fst. Qed.

(** Bundled version for [qbs_morphism_curry]. *)
Definition const_body_hom :
  @qbsHomType R (prodQ (realQ R) (realQ R)) (realQ R) :=
  pack_hom const_body_morphism.

(** Curried morphism [realQ -> expQ realQ realQ] sending [c] to
    the constant function [fun _ => c]. This is the key step that
    is impossible in kernel-based semantics: the codomain is the
    space of functions [realQ -> realQ]. *)
Lemma const_curried_morphism :
  @qbs_morphism R (realQ R) (expQ (realQ R) (realQ R))
    (fun c => HB.pack (fun _ : realQ R => (const_body_hom : _ -> _)
                       (c, (0 : realQ R)))
       (@isQBSMorphism.Build R (realQ R) (realQ R)
          (fun _ => (const_body_hom : _ -> _) (c, (0 : realQ R)))
          (fun alpha halpha =>
             @qbs_hom_proof R (prodQ (realQ R) (realQ R)) (realQ R)
               const_body_hom
               (fun r : mR => (c, alpha r))
               (prodQ_const_random c halpha)))).
Proof. exact: (@qbs_morphism_curry R (realQ R) (realQ R) (realQ R)
  const_body_hom). Qed.

(** The distribution over constant functions. We push the prior
    [Normal(0,1)] on [realQ] through the curried morphism using
    the functorial action [monadP_map] of the probability monad. *)
Definition random_constant :
  qbs_prob (expQ (realQ R) (realQ R)) :=
  monadP_map (realQ R) (expQ (realQ R) (realQ R))
    _ const_curried_morphism
    (@qbs_normal_distribution R (0 : R) (1 : R) (@ltr01 R)).

(** Well-formedness: the construction type-checks. *)
Definition random_constant_well_defined :
  qbs_prob (expQ (realQ R) (realQ R)) := random_constant.

(** * Example 2: random linear functions *)

(** The killer demo. Sample [m ~ Normal(0,1)] and [b ~ Normal(0,1)]
    independently, and return the function [fun x => m*x + b].
    The result is a probability measure on the function space
    [expQ realQ realQ] -- a first-class citizen in QBS. *)

(** Inner uncurried function: [((m,b), x) |-> m*x + b]. *)
Definition linear_body :
  prodQ (prodQ (realQ R) (realQ R)) (realQ R) -> realQ R :=
  fun p => p.1.1 * p.2 + p.1.2.

Lemma linear_body_morphism :
  @qbs_morphism R
    (prodQ (prodQ (realQ R) (realQ R)) (realQ R)) (realQ R)
    linear_body.
Proof.
(* linear_body = add o <mul o <fst o fst, snd>, snd o fst> *)
have hfst1 : @qbs_morphism R
  (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
  (prodQ (realQ R) (realQ R))
  fst := @qbs_morphism_fst R _ _.
have hsnd1 : @qbs_morphism R
  (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
  (realQ R)
  snd := @qbs_morphism_snd R _ _.
have hslope : @qbs_morphism R
  (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
  (realQ R)
  (fun p => p.1.1).
  exact: (qbs_morphism_comp hfst1 (@qbs_morphism_fst R _ _)).
have hintercept : @qbs_morphism R
  (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
  (realQ R)
  (fun p => p.1.2).
  exact: (qbs_morphism_comp hfst1 (@qbs_morphism_snd R _ _)).
have hmul_pair : @qbs_morphism R
  (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
  (prodQ (realQ R) (realQ R))
  (fun p => (p.1.1, p.2)).
  exact: (qbs_morphism_pair hslope hsnd1).
have hmul : @qbs_morphism R
  (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
  (realQ R)
  (fun p => p.1.1 * p.2)%R.
  exact: (qbs_morphism_comp hmul_pair (@qbs_morphism_mul R)).
have hadd_pair : @qbs_morphism R
  (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
  (prodQ (realQ R) (realQ R))
  (fun p => (p.1.1 * p.2, p.1.2)%R).
  exact: (qbs_morphism_pair hmul hintercept).
exact: (qbs_morphism_comp hadd_pair (@qbs_morphism_add R)).
Qed.

Definition linear_body_hom :
  @qbsHomType R
    (prodQ (prodQ (realQ R) (realQ R)) (realQ R))
    (realQ R) :=
  pack_hom linear_body_morphism.

(** Curried morphism [prodQ realQ realQ -> expQ realQ realQ]
    sending [(m,b)] to the function [fun x => m*x + b]. *)
Lemma linear_curried_morphism :
  @qbs_morphism R (prodQ (realQ R) (realQ R))
    (expQ (realQ R) (realQ R))
    (fun mb => HB.pack
       (fun x : realQ R => (linear_body_hom : _ -> _) (mb, x))
       (@isQBSMorphism.Build R (realQ R) (realQ R)
          (fun x => (linear_body_hom : _ -> _) (mb, x))
          (fun alpha halpha =>
             @qbs_hom_proof R _ _ linear_body_hom
               (fun r : mR => (mb, alpha r))
               (prodQ_const_random mb halpha)))).
Proof. exact: (@qbs_morphism_curry R
  (prodQ (realQ R) (realQ R)) (realQ R) (realQ R)
  linear_body_hom). Qed.

(** The joint prior [(m,b) ~ Normal(0,1) x Normal(0,1)] on
    [prodQ realQ realQ]. *)
Definition slope_intercept_prior :
  qbs_prob (prodQ (realQ R) (realQ R)) :=
  qbs_prob_pair
    (@qbs_normal_distribution R (0 : R) (1 : R) (@ltr01 R))
    (@qbs_normal_distribution R (0 : R) (1 : R) (@ltr01 R)).

(** The killer demo: a distribution over functions [R -> R]. *)
Definition random_linear :
  qbs_prob (expQ (realQ R) (realQ R)) :=
  monadP_map (prodQ (realQ R) (realQ R))
    (expQ (realQ R) (realQ R))
    _ linear_curried_morphism slope_intercept_prior.

(** Well-formedness: the construction type-checks. *)
Definition random_linear_well_defined :
  qbs_prob (expQ (realQ R) (realQ R)) := random_linear.

(** Evaluation of a random function at a fixed input is a QBS
    morphism [expQ realQ realQ -> realQ]. Combined with
    [monadP_map], this gives the pushforward distribution of
    [random_linear] at any fixed [x]. *)
Lemma random_linear_eval_morphism (x : realQ R) :
  @qbs_morphism R (expQ (realQ R) (realQ R)) (realQ R)
    (fun f : @qbsHomType R (realQ R) (realQ R) =>
       (f : realQ R -> realQ R) x).
Proof.
have hpair : @qbs_morphism R
  (expQ (realQ R) (realQ R))
  (prodQ (expQ (realQ R) (realQ R)) (realQ R))
  (fun f => (f, x)).
  apply: (@qbs_morphism_pair R
            (expQ (realQ R) (realQ R))
            (expQ (realQ R) (realQ R)) (realQ R)).
  - exact: (@qbs_morphism_id R _).
  - exact: (@qbs_morphism_const R _ _ x).
exact: (qbs_morphism_comp hpair
         (@qbs_morphism_eval R (realQ R) (realQ R))).
Qed.

(** The pushforward of [random_linear] under evaluation at a
    fixed [x]: this is the marginal distribution of
    [m*x + b] where [(m,b) ~ Normal(0,1) x Normal(0,1)]. *)
Definition random_linear_eval_at (x : realQ R) :
  qbs_prob (realQ R) :=
  monadP_map (expQ (realQ R) (realQ R)) (realQ R)
    _ (random_linear_eval_morphism x) random_linear.

(** * Example 3: random sampler (doubly higher-order) *)

(** Sample [mu ~ Normal(0,1)] and return the sampler
    [lambda x. Normal(mu*x, 1)]. The result type
    [qbs_prob (expQ realQ (monadP realQ))] is doubly higher-order:
    it is a distribution over functions that return
    distributions. *)

(** The map [(mu, x) |-> mu*x], as a QBS morphism. *)
Lemma sampler_mean_morphism :
  @qbs_morphism R (prodQ (realQ R) (realQ R)) (realQ R)
    (fun p => (p.1 * p.2)%R).
Proof. exact: (@qbs_morphism_mul R). Qed.

(** The map [(mu, x) |-> Normal(mu*x, 1)]. We use
    [qbs_normal_morphism] composed with [sampler_mean_morphism]. *)
Lemma sampler_body_morphism :
  @qbs_morphism R (prodQ (realQ R) (realQ R))
    (monadP (realQ R))
    (fun p =>
       @qbs_normal_distribution R
         (p.1 * p.2)%R (1 : R) (@ltr01 R)).
Proof.
exact: (qbs_morphism_comp sampler_mean_morphism
         (@qbs_normal_morphism R (1 : R) (@ltr01 R))).
Qed.

Definition sampler_body_hom :
  @qbsHomType R (prodQ (realQ R) (realQ R))
    (monadP (realQ R)) :=
  pack_hom sampler_body_morphism.

(** Curried: [mu |-> (lambda x. Normal(mu*x, 1))]. *)
Lemma sampler_curried_morphism :
  @qbs_morphism R (realQ R)
    (expQ (realQ R) (monadP (realQ R)))
    (fun mu => HB.pack
       (fun x : realQ R =>
          (sampler_body_hom : _ -> _) (mu, x))
       (@isQBSMorphism.Build R (realQ R) (monadP (realQ R))
          (fun x => (sampler_body_hom : _ -> _) (mu, x))
          (fun alpha halpha =>
             @qbs_hom_proof R _ _ sampler_body_hom
               (fun r : mR => (mu, alpha r))
               (prodQ_const_random mu halpha)))).
Proof. exact: (@qbs_morphism_curry R
  (realQ R) (realQ R) (monadP (realQ R))
  sampler_body_hom). Qed.

(** Distribution over samplers. A doubly higher-order construction
    that is impossible in classical kernel-based PPL semantics:
    the result type has the form [P(X -> P(Y))], requiring both a
    function space and a probability measure on it. *)
Definition random_sampler :
  qbs_prob (expQ (realQ R) (monadP (realQ R))) :=
  monadP_map (realQ R) (expQ (realQ R) (monadP (realQ R)))
    _ sampler_curried_morphism
    (@qbs_normal_distribution R (0 : R) (1 : R) (@ltr01 R)).

Definition random_sampler_well_defined :
  qbs_prob (expQ (realQ R) (monadP (realQ R))) := random_sampler.

(** * Example 4: Bayesian inference on random linear functions *)

(** We condition [random_linear] on observed data points to obtain
    a posterior distribution over functions. This is a higher-order
    Bayesian inference example: the posterior lives on the function
    space [expQ realQ realQ], which is impossible in the classical
    kernel-based semantics.

    Model:
    - Prior:      [f ~ random_linear] (i.e. [f = fun x => m*x + b]
                  with [m, b ~ Normal(0,1)]).
    - Likelihood: for each data point [(x_i, y_i)], the observation
                  density is [normal_pdf (f x_i) obs_sigma y_i].
    - Posterior:  [f | data], obtained by reweighting the prior by
                  the product of the observation densities. *)

(** Observation noise standard deviation. A constant [1] is used
    so that positivity is immediate. *)
Definition obs_sigma : R := 1.

Lemma obs_sigma_gt0 : (0 < obs_sigma)%R.
Proof. by rewrite /obs_sigma; exact: ltr01. Qed.

(** Measurable real functions are QBS morphisms between [realQ R]s.
    This is a convenient bridge lemma. *)
Lemma qbs_morphism_of_measurable (f : R -> R)
    (hf : measurable_fun [set: mR] f) :
  @qbs_morphism R (realQ R) (realQ R) f.
Proof.
move=> alpha halpha.
rewrite /qbs_Mx /=.
exact: (measurableT_comp hf halpha).
Qed.

(** Single-point observation density as a QBS morphism on the
    function space. Given fixed input [x] and observation [y],
    the map [f |-> normal_pdf (f x) obs_sigma y] is a QBS morphism
    [expQ realQ realQ -> realQ]. *)
Lemma obs_sigma_neq0 : (obs_sigma != 0 :> R)%R.
Proof. by rewrite /obs_sigma oner_neq0. Qed.

Lemma obs_at_point_morphism (x y : R) :
  @qbs_morphism R (expQ (realQ R) (realQ R)) (realQ R)
    (fun f : @qbsHomType R (realQ R) (realQ R) =>
       normal_pdf ((f : realQ R -> realQ R) x) obs_sigma y).
Proof.
have hpdf_meas : measurable_fun [set: mR]
  (fun u : R => normal_pdf u obs_sigma y).
  (* Via symmetry (y - u)^2 = (u - y)^2, we have
     normal_pdf u s y = normal_pdf y s u as a real function of u. *)
  have hsym : (fun u : R => normal_pdf u obs_sigma y) =
              (fun u : R => normal_pdf y obs_sigma u).
    apply: funext => u.
    rewrite (normal_pdfE u obs_sigma_neq0)
            (normal_pdfE y obs_sigma_neq0).
    congr (_ * _)%R.
    rewrite /normal_fun.
    suff -> : ((y - u) ^+ 2 = (u - y) ^+ 2)%R by [].
    by rewrite !expr2; ring.
  by rewrite hsym; exact: measurable_normal_pdf.
have hpdf_morph : @qbs_morphism R (realQ R) (realQ R)
  (fun u : R => normal_pdf u obs_sigma y).
  exact: qbs_morphism_of_measurable hpdf_meas.
exact: (qbs_morphism_comp
  (@random_linear_eval_morphism x) hpdf_morph).
Qed.

(** Real-valued observation density at a single point. *)
Definition obs_at_point (x y : R)
  (f : @qbsHomType R (realQ R) (realQ R)) : R :=
  normal_pdf ((f : realQ R -> realQ R) x) obs_sigma y.

Lemma obs_at_point_ge0 (x y : R) (f : @qbsHomType R (realQ R) (realQ R)) :
  (0 <= obs_at_point x y f)%R.
Proof. rewrite /obs_at_point; exact: normal_pdf_ge0. Qed.

(** The three observed data points: [(1, 2.5), (2, 3.8), (3, 4.5)].
    We use rationals expressed with [%:R] so the definitions stay
    independent of any float notation. *)
Definition data_x1 : R := 1.
Definition data_y1 : R := 5%:R / 2%:R.    (* 2.5 *)
Definition data_x2 : R := 2%:R.
Definition data_y2 : R := 19%:R / 5%:R.   (* 3.8 *)
Definition data_x3 : R := 3%:R.
Definition data_y3 : R := 9%:R / 2%:R.    (* 4.5 *)

(** Joint observation likelihood: product of per-point densities. *)
Definition obs_likelihood
    (f : @qbsHomType R (realQ R) (realQ R)) : R :=
  (obs_at_point data_x1 data_y1 f *
   obs_at_point data_x2 data_y2 f *
   obs_at_point data_x3 data_y3 f)%R.

Lemma obs_likelihood_ge0 (f : @qbsHomType R (realQ R) (realQ R)) :
  (0 <= obs_likelihood f)%R.
Proof.
rewrite /obs_likelihood.
apply: mulr_ge0; last exact: obs_at_point_ge0.
apply: mulr_ge0; exact: obs_at_point_ge0.
Qed.

(** The joint likelihood as a QBS morphism [expQ realQ realQ -> realQ].
    Built by pairing the single-point likelihoods and multiplying. *)
Lemma obs_likelihood_morphism :
  @qbs_morphism R (expQ (realQ R) (realQ R)) (realQ R)
    obs_likelihood.
Proof.
have h1 := obs_at_point_morphism data_x1 data_y1.
have h2 := obs_at_point_morphism data_x2 data_y2.
have h3 := obs_at_point_morphism data_x3 data_y3.
have h12pair : @qbs_morphism R (expQ (realQ R) (realQ R))
  (prodQ (realQ R) (realQ R))
  (fun f => (obs_at_point data_x1 data_y1 f,
             obs_at_point data_x2 data_y2 f)).
  exact: (qbs_morphism_pair h1 h2).
have h12 : @qbs_morphism R (expQ (realQ R) (realQ R)) (realQ R)
  (fun f => (obs_at_point data_x1 data_y1 f *
             obs_at_point data_x2 data_y2 f)%R).
  exact: (qbs_morphism_comp h12pair (@qbs_morphism_mul R)).
have h123pair : @qbs_morphism R (expQ (realQ R) (realQ R))
  (prodQ (realQ R) (realQ R))
  (fun f => ((obs_at_point data_x1 data_y1 f *
              obs_at_point data_x2 data_y2 f)%R,
             obs_at_point data_x3 data_y3 f)).
  exact: (qbs_morphism_pair h12 h3).
exact: (qbs_morphism_comp h123pair (@qbs_morphism_mul R)).
Qed.

(** The pairing morphism [f |-> (f, obs_likelihood f)].
    This packages each sampled function together with its likelihood
    weight, ready for normalization by [qbs_normalize]. *)
Lemma pair_with_likelihood_morphism :
  @qbs_morphism R (expQ (realQ R) (realQ R))
    (prodQ (expQ (realQ R) (realQ R)) (realQ R))
    (fun f => (f, obs_likelihood f)).
Proof.
apply: qbs_morphism_pair.
- exact: (@qbs_morphism_id R _).
- exact: obs_likelihood_morphism.
Qed.

(** The unnormalized weighted distribution: each sampled function
    from [random_linear] is paired with its likelihood weight. This
    is exactly the input expected by [qbs_normalize] on the function
    space. *)
Definition bayesian_random_linear_weighted :
  qbs_prob (prodQ (expQ (realQ R) (realQ R)) (realQ R)) :=
  monadP_map (expQ (realQ R) (realQ R))
    (prodQ (expQ (realQ R) (realQ R)) (realQ R))
    _ pair_with_likelihood_morphism random_linear.

(** Well-formedness: the construction type-checks as a QBS
    probability on the product of the function space and [R]. *)
Definition bayesian_random_linear_well_defined :
  qbs_prob (prodQ (expQ (realQ R) (realQ R)) (realQ R)) :=
  bayesian_random_linear_weighted.

(** The weight component is everywhere non-negative, as required
    by [qbs_normalize]. *)
Lemma bayesian_random_linear_weight_ge0 r :
  (0 <= snd (qbs_prob_alpha bayesian_random_linear_weighted r))%R.
Proof.
rewrite /bayesian_random_linear_weighted /monadP_map /=.
exact: obs_likelihood_ge0.
Qed.

(** The weight component is a measurable function of the underlying
    randomness, as required by [qbs_normalize]. *)
Local Open Scope ereal_scope.

Lemma bayesian_random_linear_weight_meas :
  measurable_fun [set: mR]
    (fun r : mR =>
      EFin (snd (qbs_prob_alpha
        bayesian_random_linear_weighted r))).
Proof.
have halpha := qbs_prob_alpha_random bayesian_random_linear_weighted.
have [_ h2] := halpha.
apply/measurable_EFinP; exact: h2.
Qed.

Local Close Scope ereal_scope.

(** The full Bayesian posterior via [qbs_normalize]. Returns
    [Some posterior] when the evidence is strictly positive and
    finite, and [None] otherwise. The option type reflects the
    fact that a generic weighted prior might not normalize. *)
Definition bayesian_random_linear :
  option (qbs_prob (expQ (realQ R) (realQ R))) :=
  @qbs_normalize R (expQ (realQ R) (realQ R))
    bayesian_random_linear_weighted
    bayesian_random_linear_weight_ge0
    bayesian_random_linear_weight_meas.

End higher_order_examples.
