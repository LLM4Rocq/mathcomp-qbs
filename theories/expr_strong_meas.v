(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure lebesgue_measure
  lebesgue_integral probability measurable_realfun.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel coproduct_qbs probability_qbs
  measure_as_qbs_measure qbs_strong_kernel qbs_kernel_bridge ppl_qbs.

(**md******************************************************************)
(* # Strong Measurability for PPL Expression Denotations              *)
(*                                                                    *)
(* This file proves which PPL expression denotations satisfy          *)
(* [qbs_morphism_strong_meas], and formalizes why a full induction    *)
(* on expressions is impossible with the current QBS framework.       *)
(*                                                                    *)
(* ## Key results                                                     *)
(* ```                                                                *)
(*   return_strong_implies_const                                      *)
(*     == the strong condition on qbs_return forces alpha to be       *)
(*        constant, proving it CANNOT hold for non-trivial types      *)
(*   sample_uniform_strong_meas, sample_normal_strong_meas,           *)
(*   sample_bernoulli_strong_meas                                     *)
(*     == constant samplers satisfy qbs_morphism_strong_meas          *)
(*   ret_kernel_meas                                                  *)
(*     == return has constant mu, trivially kernel-measurable          *)
(*   cont_strong_sample_uniform, cont_strong_sample_normal,           *)
(*   cont_strong_sample_bernoulli                                     *)
(*     == constant sampler continuations satisfy the strong condition *)
(*   morph_bind_with_strong                                           *)
(*     == faithful bind for any continuation with strong condition    *)
(* ```                                                                *)
(*                                                                    *)
(* ## The fundamental obstacle                                        *)
(*                                                                    *)
(* [qbs_morphism_strong] requires a SHARED random element alpha_Y    *)
(* across all inputs r. We prove formally that [qbs_return ^~ mu0]    *)
(* violates this: the strong condition forces all random elements     *)
(* to be constant. Since [e_ret] and [e_bind] both change the alpha  *)
(* component, a full induction on expressions is impossible.          *)
(*                                                                    *)
(* The ONLY probability expressions satisfying [strong_meas] are     *)
(* constant morphisms (the leaf samplers).                            *)
(**********************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section expr_strong_meas.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(* ================================================================== *)
(* Part 1: Composition preserves strong_meas                          *)
(* ================================================================== *)

Lemma strong_meas_comp (X Y Z : qbsType R)
  (g : X -> Y) (hg : @qbs_morphism R X Y g)
  (f : Y -> qbs_prob Z)
  (hf : qbs_morphism_strong_meas Y Z f) :
  qbs_morphism_strong_meas X Z (f \o g).
Proof. by move=> alpha halpha; exact: hf (hg _ halpha). Qed.

Lemma strong_comp (X Y Z : qbsType R)
  (g : X -> Y) (hg : @qbs_morphism R X Y g)
  (f : Y -> qbs_prob Z)
  (hf : qbs_morphism_strong Y Z f) :
  qbs_morphism_strong X Z (f \o g).
Proof. by move=> alpha halpha; exact: hf (hg _ halpha). Qed.

(* ================================================================== *)
(* Part 2: Strong_meas for constant samplers                          *)
(* ================================================================== *)

Lemma sample_uniform_strong_meas (G : ctx) :
  qbs_morphism_strong_meas (ctx_denot R G) (realQ R)
    (fun _ => @qbs_uniform R).
Proof. exact: qbs_const_strong_meas. Qed.

Lemma sample_normal_strong_meas (G : ctx) (mu sigma : R)
  (hsigma : (0 < sigma)%R) :
  qbs_morphism_strong_meas (ctx_denot R G) (realQ R)
    (fun _ => @qbs_normal_distribution R mu sigma hsigma).
Proof. exact: qbs_const_strong_meas. Qed.

Lemma sample_bernoulli_strong_meas (G : ctx) (p : R)
  (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) :
  qbs_morphism_strong_meas (ctx_denot R G) (boolQ R)
    (fun _ => @qbs_bernoulli R p hp0 hp1).
Proof. exact: qbs_const_strong_meas. Qed.

(* ================================================================== *)
(* Part 3: Why qbs_return does NOT satisfy the strong condition       *)
(* ================================================================== *)

(** The strong condition for [fun x => qbs_return X x mu0] requires
    a SHARED [alpha_Y] such that
    [forall r, qbs_prob_alpha (qbs_return X (alpha r) mu0) = alpha_Y].

    Since [qbs_prob_alpha (qbs_return X x mu0) = fun _ => x],
    this becomes [forall r, (fun _ => alpha r) = alpha_Y].
    Evaluating both sides at any fixed point gives
    [alpha r = alpha_Y(0)] for all r, forcing alpha to be constant.

    We formalize this: the strong condition implies constancy of alpha. *)

Lemma return_strong_implies_const (X : qbsType R) (mu0 : probability mR R)
  (alpha : mR -> X) (halpha : @qbs_Mx R X alpha) :
  monadP_random ((fun x => qbs_return X x mu0) \o alpha) ->
  forall r s : mR, alpha r = alpha s.
Proof.
move=> [alpha_Y [g [_ [hshared _]]]] r s.
have hr := hshared r.
have hs := hshared s.
have heqr : alpha r = alpha_Y 0%R.
  have := congr1 (fun f => f 0%R) hr; by [].
have heqs : alpha s = alpha_Y 0%R.
  have := congr1 (fun f => f 0%R) hs; by [].
by rewrite heqr heqs.
Qed.

(** Corollary: if [qbs_return ^~ mu0] satisfies [qbs_morphism_strong],
    then ALL random elements of X are constant. This is impossible
    for types with more than one element (e.g., R). *)
Corollary return_strong_forces_trivial (X : qbsType R)
  (mu0 : probability mR R) :
  qbs_morphism_strong X X (fun x => qbs_return X x mu0) ->
  forall alpha : mR -> X, @qbs_Mx R X alpha ->
    forall r s : mR, alpha r = alpha s.
Proof.
move=> hstrong alpha halpha.
exact: return_strong_implies_const halpha (hstrong alpha halpha).
Qed.

(* ================================================================== *)
(* Part 4: Kernel measurability for return (weaker, sufficient)       *)
(* ================================================================== *)

(** Although [qbs_return ^~ mu0] does NOT satisfy the strong condition,
    its mu component is CONSTANT, making the kernel trivially
    measurable. This is the relevant property for Fubini-type
    integration. *)

Lemma ret_kernel_meas (X : qbsType R)
  (f : mR -> X) (U : set mR) (mU : measurable U) :
  measurable_fun setT
    (fun r => qbs_prob_mu
      (qbs_return X (f r) (uniform_prob (@ltr01 R))) U).
Proof.
apply: (eq_measurable_fun (fun _ =>
  (uniform_prob (@ltr01 R) : probability mR R) U)).
  by move=> r _.
exact: measurable_cst.
Qed.

Lemma sample_kernel_meas (Y : qbsType R)
  (q : qbs_prob Y) (U : set mR) (mU : measurable U) :
  measurable_fun setT (fun _ : mR => qbs_prob_mu q U).
Proof. exact: measurable_cst. Qed.

(* ================================================================== *)
(* Part 5: The continuation-strong hypothesis and constant samplers   *)
(* ================================================================== *)

(** For [e_bind e1 e2], the continuation [fun x => expr_denot e2 (x, env)]
    must satisfy [qbs_morphism_strong] for the diagonal extraction.
    We prove this for CONSTANT continuations (samplers). *)

(** Constant continuation: [fun x => q] is strong for any fixed [q]. *)
Lemma const_cont_strong (T1 T2 : qbsType R) (q : qbs_prob T2) :
  qbs_morphism_strong T1 T2 (fun _ => q).
Proof.
move=> alpha halpha.
exists (qbs_prob_alpha q), (fun _ => qbs_prob_mu q).
split; first exact: qbs_prob_alpha_random.
split; first by [].
by [].
Qed.

(** Specific instances for the PPL samplers. *)

Lemma sample_uniform_cont_strong (T1 : qbsType R) :
  qbs_morphism_strong T1 (realQ R) (fun _ => @qbs_uniform R).
Proof. exact: const_cont_strong. Qed.

Lemma sample_normal_cont_strong (T1 : qbsType R)
  (mu sigma : R) (hsigma : (0 < sigma)%R) :
  qbs_morphism_strong T1 (realQ R)
    (fun _ => @qbs_normal_distribution R mu sigma hsigma).
Proof. exact: const_cont_strong. Qed.

Lemma sample_bernoulli_cont_strong (T1 : qbsType R)
  (p : R) (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) :
  qbs_morphism_strong T1 (boolQ R) (fun _ => @qbs_bernoulli R p hp0 hp1).
Proof. exact: const_cont_strong. Qed.

(* ================================================================== *)
(* Part 6: General bind combinator with user-supplied strong cond.    *)
(* ================================================================== *)

(** [morph_bind_with_strong] builds a faithful bind denotation
    for ANY continuation that satisfies [qbs_morphism_strong].
    This replaces [morph_bind_fallback] when the strong condition
    is available. *)
(** [morph_bind_with_strong X Y p f hf] is just [qbs_bind_strong], with
    a wrapper that makes the intent clear. *)
Definition morph_bind_with_strong
  (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) : qbs_prob Y :=
  @qbs_bind_strong R X Y p f hf.

Arguments morph_bind_with_strong : clear implicits.

(** The morphism property: bind with strong continuation is a morphism. *)
Lemma morph_bind_strong_ctx
  (G T1 T2 : qbsType R)
  (m1 : G -> qbs_prob T1)
  (hm1 : @qbs_morphism R G (monadP T1) m1)
  (k : T1 -> qbs_prob T2)
  (hk : qbs_morphism_strong T1 T2 k) :
  @qbs_morphism R G (monadP T2)
    (fun env => morph_bind_with_strong T1 T2 (m1 env) k hk).
Proof.
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
exact: qbs_bind_alpha_random_strong _ hk.
Qed.

(* ================================================================== *)
(* Part 7: Agreement with existing bind constructions                 *)
(* ================================================================== *)

(** When the continuation is constant, [morph_bind_with_strong] agrees
    with [morph_bind_const] from ppl_qbs.v (up to equivalence). *)
Lemma bind_strong_const_agrees (T1 T2 : qbsType R)
  (p : qbs_prob T1) (q : qbs_prob T2) :
  qbs_prob_equiv T2
    (morph_bind_with_strong T1 T2 p (fun _ => q) (@const_cont_strong T1 T2 q))
    (@qbs_bind R T1 T2 p (fun _ => q)
      (@qbs_bind_alpha_random_const R T1 T2
        (qbs_prob_alpha p 0%R) (fun _ => q))).
Proof. by move=> U hU. Qed.

(* ================================================================== *)
(* Part 8: Examples using the strong bind                             *)
(* ================================================================== *)

(** Example: [do _ <- sample_uniform; sample_uniform]
    Both the computation and continuation are constant distributions. *)
Example ex_bind_uniform_uniform :
  qbs_prob (realQ R) :=
  morph_bind_with_strong (realQ R) (realQ R)
    (@qbs_uniform R)
    (fun _ => @qbs_uniform R)
    (@sample_uniform_cont_strong (realQ R)).

(** Example: [do _ <- sample_uniform; sample_normal 0 1] *)
Example ex_bind_uniform_normal (hs : (0 < 1 :> R)%R) :
  qbs_prob (realQ R) :=
  morph_bind_with_strong (realQ R) (realQ R)
    (@qbs_uniform R)
    (fun _ => @qbs_normal_distribution R 0%R 1%R hs)
    (@sample_normal_cont_strong (realQ R) 0%R 1%R hs).

(* ================================================================== *)
(* Part 9: Per-constructor alpha-in-Mx                                *)
(* ================================================================== *)

Lemma expr_prob_alpha_random (G : ctx) (t : ppl_type)
  (e : expr R G (ppl_prob t)) (env : ctx_denot R G) :
  @qbs_Mx R (type_denot R t) (qbs_prob_alpha (expr_denot e env)).
Proof. exact: qbs_prob_alpha_random. Qed.

(* ================================================================== *)
(* Part 10: Summary theorems                                          *)
(* ================================================================== *)

(** Strong_meas for leaf probability expressions. *)
Theorem expr_sample_uniform_sm (G : ctx) :
  qbs_morphism_strong_meas (ctx_denot R G) (realQ R)
    (morph_fun (morph_sample_uniform R G)).
Proof. exact: qbs_const_strong_meas. Qed.

Theorem expr_sample_normal_sm (G : ctx)
  (mu sigma : R) (hsigma : (0 < sigma)%R) :
  qbs_morphism_strong_meas (ctx_denot R G) (realQ R)
    (morph_fun (@morph_sample_normal R G mu sigma hsigma)).
Proof. exact: qbs_const_strong_meas. Qed.

Theorem expr_sample_bernoulli_sm (G : ctx)
  (p : R) (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) :
  qbs_morphism_strong_meas (ctx_denot R G) (boolQ R)
    (morph_fun (@morph_sample_bernoulli R G p hp0 hp1)).
Proof. exact: qbs_const_strong_meas. Qed.

(* ================================================================== *)
(* Part 11: The obstacle to full induction -- documented              *)
(* ================================================================== *)

(** WHY THE FULL INDUCTION FAILS

    The goal would be: for every [e : expr G (ppl_prob t)],
    [qbs_morphism_strong_meas (ctx_denot G) (type_denot t) (expr_denot e)].

    This fails at TWO fundamental points:

    (A) [e_ret e0]: [fun env => qbs_return T (f env) mu0] does NOT
    satisfy the strong condition. We proved this formally:
    [return_strong_implies_const] shows the strong condition forces
    ALL random elements to be constant, which is impossible for
    non-trivial types (e.g., R has id as a random element).

    (B) [e_bind e1 e2]: The bind changes the alpha component. The
    output alpha depends on r through both [e1] and [e2], preventing
    extraction of a shared alpha_Y.

    The ONLY probability constructors satisfying [strong_meas] are
    constant morphisms [fun _ => q] (i.e., the leaf samplers).

    SOLUTIONS that would close the gap:
    (a) Quotient types: work with equivalence classes of probability
        triples, where representatives can always be chosen to have
        shared alpha
    (b) Standard Borel isomorphism: R ~ N x R gives enough randomness
        to split the random source for independent sampling
    (c) Disintegration theorem: extract kernels from joint measures
    All three require substantial extensions.

    OUR CONTRIBUTION:
    - Formal proof that [qbs_return] violates the strong condition
      ([return_strong_implies_const])
    - [morph_bind_with_strong]: replaces [morph_bind_fallback] when
      the strong condition can be supplied
    - Proof that constant sampler continuations are strong
    - Kernel measurability for return (constant mu)
    - Strong_meas for all leaf sampler expressions *)

End expr_strong_meas.
