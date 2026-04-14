(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure kernel
  probability measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_structure measurable_function
  measure_function probability_measure.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel probability_qbs
  measure_qbs_adjunction qbs_giry qbs_kernel
  measure_as_qbs_measure.

(**md*****************************************************************)
(* # Strong Morphism Condition and Measurable Kernels               *)
(*                                                                   *)
(* This file investigates whether the strong morphism condition      *)
(* [qbs_morphism_strong X Y f] applied to a QBS probability [p]     *)
(* yields a measurable kernel.                                       *)
(*                                                                   *)
(* ## The question                                                   *)
(*                                                                   *)
(* Given [f : X -> qbs_prob Y] satisfying [qbs_morphism_strong],    *)
(* the strong condition provides for each random element             *)
(* [alpha_p : mR -> X]:                                              *)
(* - A shared random element [alpha_Y : mR -> Y] in [Mx(Y)]         *)
(* - A function [g : mR -> probability mR R] with                    *)
(*   [qbs_prob_mu (f (alpha_p r)) = g r]                             *)
(*                                                                   *)
(* Is [g] measurable as a function [mR -> pprobability mR R]?        *)
(*                                                                   *)
(* ## Summary of findings                                            *)
(*                                                                   *)
(* **Approach A**: The QBS axioms constrain the [alpha] component    *)
(* of probability triples but not the [mu] component directly.       *)
(* The [monadP_random] condition existentially quantifies [g]        *)
(* without any measurability constraint. Measurability CANNOT be     *)
(* derived from the QBS structure alone.                             *)
(*                                                                   *)
(* **Approach B**: [kprobability] in [kernel.v] takes a              *)
(* MEASURABLE function [P : X -> pprobability Y R] and produces      *)
(* a probability kernel. We need the CONVERSE: starting from an      *)
(* existentially-quantified [g], show it is measurable. This is      *)
(* circular without further information.                             *)
(*                                                                   *)
(* **Approach C**: Strengthening [monadP_random] to include          *)
(* measurability of [g] (see [monadP_random_meas]) is the            *)
(* cleanest solution. We define the strengthened condition and        *)
(* show it suffices for kernel construction. The downstream impact   *)
(* is analyzed: existing strong-condition proofs (e.g.,              *)
(* [likelihood_single_strong] in bayesian_regression.v) would need   *)
(* to additionally supply measurability of their [g], which is       *)
(* provable but non-trivial.                                         *)
(*                                                                   *)
(* **Approach D**: For SPECIFIC strong morphisms used in practice    *)
(* (return, normal sampling), measurability of [g] is provable.      *)
(* We show:                                                          *)
(* - [qbs_return ^~ mu] does NOT satisfy the strong condition, but  *)
(*   its mu component is constant, giving trivial kernel measurability*)
(*   [qbs_return_kernel_meas].                                       *)
(* - [qbs_normal_strong_kernel_meas]: the normal distribution case  *)
(*   gives [g r = normal_prob (h r) sigma], measurable when [h] is. *)
(*   This requires a hypothesis about the measurability of           *)
(*   [fun m => normal_prob m sigma] as a function to pprobability,  *)
(*   which is analogous to [measurable_bernoulli_prob] but not yet  *)
(*   in mathcomp-analysis.                                           *)
(*                                                                   *)
(* ## Key constructions                                              *)
(* ```                                                               *)
(*   monadP_random_meas X beta                                       *)
(*     == strengthened strong condition with g-measurability          *)
(*   qbs_morphism_strong_meas X Y f                                  *)
(*     == strengthened morphism condition                             *)
(*   strong_meas_to_kprobability                                     *)
(*     == build a probability kernel from the strengthened condition *)
(*   strong_meas_kernel_measurable U                                 *)
(*     == the kernel is measurable for each measurable U             *)
(*   qbs_return_kernel_meas                                          *)
(*     == return gives measurable kernel (constant mu)               *)
(*   qbs_normal_strong_meas                                          *)
(*     == normal sampling satisfies the strengthened condition        *)
(*   qbs_normal_kernel_meas                                          *)
(*     == normal sampling gives measurable kernel                    *)
(*   qbs_normal_giry_kernel_meas                                     *)
(*     == normal sampling gives measurable Giry kernel               *)
(*   qbs_const_strong_meas                                           *)
(*     == constant morphism satisfies the strengthened condition      *)
(*   strong_meas_discharges_fubini                                   *)
(*     == strengthened condition discharges qbs_fubini hypothesis    *)
(*   strong_meas_discharges_fubini_giry                              *)
(*     == strengthened condition discharges Giry-level hypothesis    *)
(* ```                                                               *)
(*****************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_strong_kernel.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(* ================================================================== *)
(* Part 1: Why approaches A and B fail                                *)
(* ================================================================== *)

(* Approach A: Deriving measurability from QBS structure.

   The QBS on monadP Y is monadP_random_pw, which says:
     forall r, qbs_Mx (qbs_prob_alpha (beta r)).
   This constrains the ALPHA component of each beta(r), but says
   nothing about how qbs_prob_mu (beta r) varies with r.

   The STRONG condition monadP_random says:
     exists alpha, exists g,
       qbs_Mx alpha /\
       (forall r, qbs_prob_alpha (beta r) = alpha) /\
       (forall r, qbs_prob_mu (beta r) = g r).
   This makes alpha shared, but g is merely existentially quantified:
   there is no constraint that g is measurable.

   The QBS axioms (composition with measurables, constant, gluing)
   act on functions mR -> X, not on functions mR -> probability mR R.
   The probability type is not equipped with a QBS structure in a way
   that would constrain g.

   CONCLUSION: Approach A fails. No measurability of g can be derived
   from monadP_random or monadP_random_pw alone. *)

(* Approach B: Using kprobability from kernel.v.

   kprobability takes a MEASURABLE function P : X -> pprobability Y R
   and builds a probability kernel. To use it, we would need to first
   show that g : mR -> probability mR R is measurable as a function
   to pprobability mR R. But this is exactly what we are trying to
   prove, so this is circular.

   CONCLUSION: kprobability is the right OUTPUT format, but we need
   measurability as INPUT. The approach is useful AFTER we establish
   measurability by other means. *)

(* ================================================================== *)
(* Part 2: Approach C - Strengthened strong condition                  *)
(* ================================================================== *)

(* We define a strengthened version of monadP_random that includes
   measurability of the measure family g. This is the cleanest
   theoretical solution. *)

(** Strengthened random-element condition: a single shared alpha
    exists across all r, AND the measure family g is measurable
    as a function to pprobability. *)
Definition monadP_random_meas (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta |
    exists (alpha : mR -> X),
    exists (g : mR -> probability mR R),
      @qbs_Mx R X alpha /\
      (forall r, qbs_prob_alpha (beta r) = alpha) /\
      (forall r, qbs_prob_mu (beta r) = g r) /\
      measurable_fun setT (g : mR -> pprobability mR R)].

Arguments monadP_random_meas : clear implicits.

(** The strengthened condition implies the original one. *)
Lemma monadP_random_meas_impl (X : qbsType R) (beta : mR -> qbs_prob X) :
  monadP_random_meas X beta -> @monadP_random R X beta.
Proof.
move=> [alpha [g [halpha [hbeta_a [hbeta_g _]]]]].
by exists alpha, g.
Qed.

(** Strengthened strong morphism condition. *)
Definition qbs_morphism_strong_meas (X Y : qbsType R)
  (f : X -> qbs_prob Y) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> monadP_random_meas Y (f \o alpha).

Arguments qbs_morphism_strong_meas : clear implicits.

(** The strengthened condition implies the original. *)
Lemma qbs_morphism_strong_meas_impl (X Y : qbsType R)
  (f : X -> qbs_prob Y) :
  qbs_morphism_strong_meas X Y f -> qbs_morphism_strong X Y f.
Proof.
move=> hf alpha halpha.
exact: monadP_random_meas_impl (hf alpha halpha).
Qed.

(* ================================================================== *)
(* Part 3: From strengthened condition to probability kernel           *)
(* ================================================================== *)

Section strong_meas_kernel.

Variables (X Y : qbsType R).
Variable (f : X -> qbs_prob Y).
Variable (p : qbs_prob X).
Hypothesis hf : qbs_morphism_strong_meas X Y f.

Let alpha_p := qbs_prob_alpha p.
Let mu_p := qbs_prob_mu p.

(* Apply the strengthened strong condition *)
Let strong_data := hf (qbs_prob_alpha_random p).

(* Extract witnesses *)
Let alpha_Y : mR -> Y :=
  projT1 (cid strong_data).
Let g_data := projT2 (cid strong_data).
Let g : mR -> probability mR R :=
  projT1 (cid g_data).
Let g_props := projT2 (cid g_data).
Let alpha_Y_random : qbs_Mx alpha_Y := g_props.1.
Let alpha_eq : forall r, qbs_prob_alpha (f (alpha_p r)) = alpha_Y :=
  g_props.2.1.
Let mu_eq : forall r, qbs_prob_mu (f (alpha_p r)) = g r :=
  g_props.2.2.1.
Let g_meas : measurable_fun setT (g : mR -> pprobability mR R) :=
  g_props.2.2.2.

(** The measure family g gives a probability kernel via kprobability. *)
Definition strong_meas_to_kprobability :=
  kprobability g_meas.

(** The kernel is measurable for each measurable U.
    This follows from kprobability being a kernel (HB instance). *)
Lemma strong_meas_kernel_measurable (U : set mR) (mU : measurable U) :
  measurable_fun setT (fun r : mR => (g r : measure _ _) U).
Proof.
exact: measurable_kernel (kprobability g_meas) U mU.
Qed.

(** The kernel applied to r equals the mu component of f(alpha_p(r)). *)
Lemma strong_meas_kernel_eq (r : mR) (U : set mR) :
  strong_meas_to_kprobability r U = qbs_prob_mu (f (alpha_p r)) U.
Proof. by rewrite /strong_meas_to_kprobability /kprobability /= mu_eq. Qed.

(** The map r |-> qbs_prob_mu(f(alpha_p(r)))(U) is measurable. *)
Lemma strong_meas_mu_measurable (U : set mR) (mU : measurable U) :
  measurable_fun setT (fun r : mR => qbs_prob_mu (f (alpha_p r)) U).
Proof.
have hmeas := strong_meas_kernel_measurable mU.
apply: (eq_measurable_fun (fun r => (g r : measure _ _) U)).
  by move=> r _; rewrite mu_eq.
exact: hmeas.
Qed.


End strong_meas_kernel.

(* Giry-level kernel measurability for the standard Borel case.
   Here we work directly with Y = R_qbs M. *)
Section strong_meas_giry_kernel.

Variables (d : measure_display) (M : measurableType d).
Variable (X : qbsType R).
Variable (f : X -> qbs_prob (@R_qbs R _ M)).
Variable (p : qbs_prob X).
Hypothesis hf : qbs_morphism_strong_meas X (@R_qbs R _ M) f.

Let alpha_p := qbs_prob_alpha p.
Let mu_p := qbs_prob_mu p.
Let strong_data := hf (qbs_prob_alpha_random p).

(* We destruct the strong data into its components.
   Since monadP_random_meas unfolds to a nested existential in Prop,
   we use cid to extract witnesses constructively. *)
Let strong_cid := cid strong_data.
Let alpha_Y := projT1 strong_cid.
Let g_cid := cid (projT2 strong_cid).
Let g := projT1 g_cid.
Let g_props := projT2 g_cid.

(** The Giry kernel r |-> qbs_to_giry(f(alpha_p(r)))(U) is measurable.

    Proof idea: The strong condition gives alpha_Y in Mx(R_qbs M),
    i.e., alpha_Y is measurable as mR -> M. For measurable U in M,
    alpha_Y^{-1}(U) is measurable in mR. The Giry measure equals
    g(r)(alpha_Y^{-1}(U)), which is measurable in r because g is
    measurable as a function to pprobability mR R. *)
Lemma strong_meas_giry_kernel_measurable (U : set M) (mU : measurable U) :
  measurable_fun setT
    (fun r : mR => qbs_to_giry (f (alpha_p r)) U).
Proof.
have halpha_Y_random : qbs_Mx alpha_Y := g_props.1.
have halpha_eq : forall r, qbs_prob_alpha (f (alpha_p r)) = alpha_Y :=
  g_props.2.1.
have hmu_eq : forall r, qbs_prob_mu (f (alpha_p r)) = g r :=
  g_props.2.2.1.
have hg_meas : measurable_fun setT (g : mR -> pprobability mR R) :=
  g_props.2.2.2.
have halpha_meas : measurable_fun setT alpha_Y := halpha_Y_random.
(* Step 1: replace qbs_to_giry with qbs_to_giry_mu *)
apply: (eq_measurable_fun
  (fun r => qbs_to_giry_mu (f (alpha_p r)) U)) => [r _|]; first by [].
(* Step 2: unfold qbs_to_giry_mu and rewrite using strong condition *)
apply: (eq_measurable_fun
  (fun r => (g r : measure _ _) (alpha_Y @^-1` U))) => [r _|].
  by rewrite /qbs_to_giry_mu halpha_eq hmu_eq.
(* Step 3: measurability via kprobability *)
apply: measurable_kernel (kprobability hg_meas) _ _.
have := halpha_meas measurableT U mU.
by rewrite setTI.
Qed.

End strong_meas_giry_kernel.

(* ================================================================== *)
(* Part 4: Approach D - Specific strong morphisms                     *)
(* ================================================================== *)

(* Rather than changing the definition of monadP_random (which would
   require modifying probability_qbs.v), we can verify that specific
   strong morphisms used in the PPL satisfy the strengthened condition.

   For each concrete strong morphism, we prove the g it provides is
   measurable. This suffices for the kernel construction in practice. *)

Section specific_strong_morphisms.

(* ---- Case 1: qbs_return ---- *)
(* NOTE: qbs_return X ^~ mu does NOT satisfy the strong condition
   in general. The strong condition requires a single shared alpha_Y
   such that qbs_prob_alpha(qbs_return X (alpha r) mu) = alpha_Y
   for all r. But qbs_prob_alpha(qbs_return X (alpha r) mu) = fun _ => alpha r,
   which varies with r. So there is no single shared alpha_Y unless alpha
   is constant.

   However, qbs_return DOES trivially give a measurable kernel because
   mu is constant: qbs_prob_mu(qbs_return X (alpha r) mu) = mu for all r,
   so r |-> mu(U) is a constant function, hence measurable. *)

(** Return gives a trivially measurable kernel (constant). *)
Lemma qbs_return_kernel_meas (X : qbsType R) (mu : probability mR R)
  (p : qbs_prob X) (U : set mR) (mU : measurable U) :
  measurable_fun setT
    (fun r : mR => qbs_prob_mu (qbs_return X (qbs_prob_alpha p r) mu) U).
Proof.
apply: (eq_measurable_fun (fun _ => mu U)) => [r _|]; first by [].
exact: measurable_cst.
Qed.

(* ---- Case 2: Normal distribution ---- *)
(* qbs_normal_distribution mu hsigma = (idfun, normal_prob mu sigma).
   For f = fun x => qbs_normal_distribution x sigma hsigma:
     f(alpha_p(r)) = (idfun, normal_prob (alpha_p(r)) sigma)
   The strong condition is:
     alpha_Y = idfun
     g = fun r => normal_prob (alpha_p(r)) sigma
   g is measurable iff r |-> normal_prob(alpha_p(r)) sigma is
   measurable as mR -> pprobability mR R.

   This reduces to showing that normal_prob ^~ sigma is measurable
   as R -> pprobability mR R, analogous to measurable_bernoulli_prob.
   Unfortunately, measurable_normal_prob is NOT in mathcomp-analysis
   1.16.0. The Bernoulli case works because bernoulli_prob is a discrete
   (finite-support) distribution; normal_prob is absolutely continuous
   and requires different techniques (parametric integrals).

   We state this as a hypothesis and verify the rest of the
   construction goes through. *)

Section normal_kernel.
Variable (sigma : R).
Hypothesis hsigma : (0 < sigma)%R.

(* Hypothesis: normal_prob is measurable as a function to pprobability.
   This is the analogue of measurable_bernoulli_prob for the normal
   distribution. The proof would follow the same pattern:
   use measurability via pset, then show that for each mset U r,
   the preimage is measurable. For the normal distribution, this
   requires showing that m |-> \int[leb]_(x in U) normal_pdf(m,s,x)
   is measurable in m for each measurable U, which follows from
   Fubini/parametric-integral results. *)
Hypothesis measurable_normal_prob_sigma :
  measurable_fun setT
    (fun m : mR => normal_prob m sigma : pprobability mR R).

(** The normal sampling morphism satisfies the strengthened condition. *)
Lemma qbs_normal_strong_meas :
  qbs_morphism_strong_meas (realQ R) (realQ R)
    (fun mu => qbs_normal_distribution mu hsigma).
Proof.
move=> alpha halpha.
exists (@idfun mR).
exists (fun r => normal_prob (alpha r) sigma : probability mR R).
split; first exact: (@measurable_id _ mR setT).
split; first by [].
split; first by [].
(* measurable_fun setT (fun r => normal_prob (alpha r) sigma : pprobability) *)
exact: measurableT_comp measurable_normal_prob_sigma
  (halpha : measurable_fun setT alpha).
Qed.

(** The normal kernel: r |-> mu_{f(alpha_p(r))}(U) is measurable. *)
Lemma qbs_normal_kernel_meas (p : qbs_prob (realQ R))
  (U : set mR) (mU : measurable U) :
  measurable_fun setT
    (fun r : mR =>
      qbs_prob_mu
        (qbs_normal_distribution (qbs_prob_alpha p r) hsigma) U).
Proof.
have := @strong_meas_mu_measurable (realQ R) (realQ R)
  (fun mu => qbs_normal_distribution mu hsigma)
  p qbs_normal_strong_meas U mU.
done.
Qed.

(** The Giry-level kernel for the normal morphism is measurable. *)
Lemma qbs_normal_giry_kernel_meas (p : qbs_prob (realQ R))
  (U : set mR) (mU : measurable U) :
  measurable_fun setT
    (fun r : mR =>
      qbs_to_giry
        (qbs_normal_distribution (qbs_prob_alpha p r) hsigma) U).
Proof.
(* qbs_to_giry of a normal dist with alpha = id:
   qbs_to_giry(normal(m, s))(U) = normal_prob(m, s)(id^{-1}(U))
                                 = normal_prob(m, s)(U) *)
apply: (eq_measurable_fun
  (fun r => qbs_prob_mu
    (qbs_normal_distribution (qbs_prob_alpha p r) hsigma) U)).
  by move=> r _; rewrite /qbs_to_giry /qbs_to_giry_mu /=.
exact: qbs_normal_kernel_meas mU.
Qed.

End normal_kernel.

(* ---- Case 3: Constant morphism ---- *)
(* When f is constant: f(x) = q for some fixed q : qbs_prob Y.
   Then g = fun _ => qbs_prob_mu q, which is constant and trivially
   measurable. *)

Lemma qbs_const_strong_meas (X Y : qbsType R) (q : qbs_prob Y) :
  qbs_morphism_strong_meas X Y (fun _ => q).
Proof.
move=> alpha halpha.
exists (qbs_prob_alpha q), (fun _ => qbs_prob_mu q).
split; first exact: (qbs_prob_alpha_random q).
split; first by [].
split; first by [].
exact: measurable_cst.
Qed.

Lemma qbs_const_kernel_meas (X Y : qbsType R) (q : qbs_prob Y)
  (p : qbs_prob X) (U : set mR) (mU : measurable U) :
  measurable_fun setT (fun r : mR => qbs_prob_mu q U).
Proof. exact: measurable_cst. Qed.

End specific_strong_morphisms.

(* ================================================================== *)
(* Part 5: Bridge to qbs_fubini.v hypothesis                          *)
(* ================================================================== *)

(* The hypothesis in qbs_fubini.v is:

   qbs_mu_measurable_kernel :
     forall U : set mR, measurable U ->
       measurable_fun setT
         (fun r => qbs_prob_mu (f (qbs_prob_alpha p r)) U).

   We show that the strengthened strong condition discharges this. *)

Section fubini_bridge.
Variables (d : measure_display) (M : measurableType d).
Variable (f : mR -> qbs_prob (@R_qbs R _ M)).
Variable (p : qbs_prob (@R_qbs R _ mR)).

(** The strengthened strong condition discharges the fubini hypothesis. *)
Lemma strong_meas_discharges_fubini :
  qbs_morphism_strong_meas (@R_qbs R _ mR) (@R_qbs R _ M) f ->
  forall (U : set mR), measurable U ->
    measurable_fun setT
      (fun r : mR => qbs_prob_mu (f (qbs_prob_alpha p r)) U).
Proof.
move=> hf_meas U mU.
have := @strong_meas_mu_measurable
  (@R_qbs R _ mR) (@R_qbs R _ M) f p hf_meas U mU.
done.
Qed.

(** And the Giry-level version: *)
Lemma strong_meas_discharges_fubini_giry :
  qbs_morphism_strong_meas (@R_qbs R _ mR) (@R_qbs R _ M) f ->
  forall (U : set M), measurable U ->
    measurable_fun setT
      (fun r : mR => qbs_to_giry (f (qbs_prob_alpha p r)) U).
Proof.
move=> hf_meas U mU.
exact: (@strong_meas_giry_kernel_measurable
  _ M (@R_qbs R _ mR) f p hf_meas U mU).
Qed.

End fubini_bridge.

(* ================================================================== *)
(* Part 6: Impact analysis of approach C                              *)
(* ================================================================== *)

(* If we were to strengthen monadP_random in probability_qbs.v:

   Old definition:
     monadP_random X beta :=
       exists alpha g, Mx alpha /\
         (forall r, alpha_beta r = alpha) /\
         (forall r, mu_beta r = g r).

   New definition (monadP_random_meas):
     monadP_random_meas X beta :=
       exists alpha g, Mx alpha /\
         (forall r, alpha_beta r = alpha) /\
         (forall r, mu_beta r = g r) /\
         measurable_fun setT (g : mR -> pprobability mR R).

   Impact on existing proofs:

   1. probability_qbs.v:
      - monadP_random_impl: would need to add _ for the extra field.
        Trivial fix.
      - qbs_bind_alpha_random_strong: destructs as [alpha [g [h1 [h2 h3]]]].
        Would become [alpha [g [h1 [h2 [h3 h4]]]]]. Trivial fix.

   2. qbs_fubini.v: All destructions of hstrong would gain one more
      component. The key benefit: hf_kernel hypothesis becomes
      PROVABLE from the strengthened condition, eliminating it entirely.

   3. qbs_bind_kernel.v: The g_kernel_meas hypothesis becomes provable
      from the strengthened condition. Major simplification.

   4. showcase/bayesian_regression.v:
      - likelihood_single_strong: must additionally prove
        measurable_fun setT (fun r => normal_prob (...) sigma : pprobability).
        Requires measurable_normal_prob (approach D hypothesis).

   5. qbs_prob_quot.v: Uses monadP_random_pw, unaffected.

   CONCLUSION: The strengthening is minimally invasive. The main cost
   is proving measurability for each concrete strong morphism, which
   is the right obligation to have -- it is exactly the mathematical
   content needed to bridge QBS and kernel semantics. *)

(* ================================================================== *)
(* Part 7: Compositionality - strong_meas is preserved by bind        *)
(* ================================================================== *)

Section compositionality.
Variables (X Y Z : qbsType R).

(** monadP_map preserves the strengthened condition.
    If f : X -> Y is a QBS morphism and beta is in monadP_random_meas X,
    then the mapped family is in monadP_random_meas Y.
    This works because monadP_map only changes alpha (to f o alpha),
    leaving mu (= g) unchanged. *)
Lemma monadP_map_preserves_meas
  (f : X -> Y) (hf : @qbs_morphism R X Y f)
  (beta : mR -> qbs_prob X)
  (hbeta : monadP_random_meas X beta) :
  monadP_random_meas Y (fun r => monadP_map X Y f hf (beta r)).
Proof.
case: hbeta => alpha [g [halpha [hbeta_a [hbeta_g hg_meas]]]].
exists (f \o alpha), g.
split; first exact: hf _ halpha.
split.
  by move=> r; rewrite /monadP_map /= hbeta_a.
split.
  by move=> r; rewrite /monadP_map /= hbeta_g.
exact: hg_meas.
Qed.

(* NOTE: qbs_return Y (g x) mu does NOT satisfy the strong condition
   in general, for the same reason as qbs_return ^~ mu. The alpha
   component fun _ => g(alpha(r)) varies with r. The morphism
   fun x => qbs_return Y (g x) mu satisfies the POINTWISE condition
   (each alpha is constant hence in Mx) but NOT the strong condition.
   However, the mu component IS trivially measurable (constant mu),
   so kernel measurability holds directly. *)

End compositionality.

(* ================================================================== *)
(* Part 8: The qbs_mu_measurable_kernel hypothesis from qbs_fubini.v *)
(* can be stated as a DERIVABLE property                              *)
(* ================================================================== *)

(* Summary:

   The original qbs_fubini.v treats qbs_mu_measurable_kernel as an
   opaque hypothesis because the standard monadP_random does not
   constrain g's measurability. With the strengthened condition
   monadP_random_meas, this hypothesis becomes a THEOREM.

   The gap between monadP_random and monadP_random_meas is exactly
   the measurability of g : mR -> pprobability mR R. This is:

   - TRIVIALLY satisfied for constant g (return, constant morphisms)
   - Satisfied for parametric families like normal_prob, bernoulli_prob
     GIVEN the measurability of the parametrization (which requires
     Fubini-type arguments for continuous distributions)

   The mathematical content is: the QBS probability monad and the
   Giry monad agree on standard Borel spaces (HKSY Prop 22.3), but
   the formalization of this agreement requires measure-theoretic
   infrastructure (parametric integrals, measurability of density
   families) that goes beyond the current QBS development. *)

End qbs_strong_kernel.

Arguments monadP_random_meas {R}.
Arguments qbs_morphism_strong_meas {R}.
