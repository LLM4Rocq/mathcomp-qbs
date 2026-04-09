(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals.
From mathcomp Require Import classical_sets.
From mathcomp Require Import num_topology.
From mathcomp Require Import measurable_structure.
From mathcomp Require Import measurable_function.
From mathcomp Require Import lebesgue_stieltjes_measure.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import probability.
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

End higher_order_examples.
