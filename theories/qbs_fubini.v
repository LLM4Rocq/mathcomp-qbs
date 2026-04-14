(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure kernel
  probability measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel probability_qbs
  measure_qbs_adjunction qbs_giry.

(**md*************************************************************)
(* # Kernel Measurability for QBS Bind (Fubini Bridge)           *)
(*                                                                *)
(* Investigation of the key lemma for kernel-based bind on QBS:  *)
(* Given f : X -> monadP Y (a QBS morphism), is the map          *)
(*   r |-> qbs_prob_mu (f (qbs_prob_alpha p r))                  *)
(* a measurable kernel mR -> measure mR?                          *)
(*                                                                *)
(* Main findings:                                                 *)
(*                                                                *)
(* 1. The POINTWISE condition (monadP_random_pw) is insufficient *)
(*    to prove kernel measurability of the mu component.          *)
(*                                                                *)
(* 2. The STRONG condition (monadP_random / qbs_morphism_strong) *)
(*    makes the alpha component shared across all r, but still   *)
(*    does not constrain the measurability of the mu component.  *)
(*                                                                *)
(* 3. With an explicit kernel measurability hypothesis on the mu *)
(*    component, plus the strong condition, we can construct a   *)
(*    genuine measurable kernel on standard Borel spaces.         *)
(*                                                                *)
(* 4. The QBS bind uses a DIAGONAL construction that does NOT    *)
(*    correspond to kernel composition. The connection between   *)
(*    the two requires disintegration.                            *)
(*                                                                *)
(* Key results:                                                   *)
(* ```                                                            *)
(*   qbs_mu_measurable_kernel                                     *)
(*     == the minimal hypothesis bridging QBS and kernels         *)
(*   qbs_strong_measurable_kernel                                 *)
(*     == strong + kernel hyp gives measurable kernel on Borel   *)
(*   qbs_bind_giry_eq                                             *)
(*     == qbs_to_giry(bind) = mu_p(alpha_Y^{-1}(U))             *)
(*   qbs_iterated_integral_strong                                 *)
(*     == strong condition simplifies iterated integral           *)
(*   qbs_bind_integral_strong                                     *)
(*     == strong condition simplifies bind integral               *)
(* ```                                                            *)
(*****************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_fubini.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(* ================================================================== *)
(* Section 1: The kernel measurability hypothesis                      *)
(* ================================================================== *)

(* The QBS morphism condition (both pointwise and strong) constrains
   the ALPHA component of f(x) : qbs_prob Y, but says nothing about
   the measurability of the MU component as x varies. This is because
   the QBS axioms govern random elements (functions mR -> X), not
   measure-valued maps.

   To bridge QBS and kernel semantics, we need an additional hypothesis
   asserting that the measure component varies measurably. *)

(* The measurable kernel condition for the mu component:
   for a function f and a random element alpha, the map
   r |-> qbs_prob_mu(f(alpha(r)))(U) is measurable for each
   measurable U. *)
Definition qbs_mu_measurable_kernel (X : qbsType R) (Y : qbsType R)
  (f : X -> qbs_prob Y) (alpha : mR -> X) : Prop :=
  forall (U : set mR), measurable U ->
    measurable_fun setT (fun r : mR => qbs_prob_mu (f (alpha r)) U).

(* ================================================================== *)
(* Section 2: Strong morphism + kernel hypothesis on standard Borel   *)
(* ================================================================== *)

(* For the kernel construction to produce genuine probability measures,
   the codomain must be a measurableType (specifically R_qbs M for
   some M), so that qbs_to_giry produces probability measures on M.
   This is the natural setting for kernel composition. *)

Section strong_kernel.

Variables (d : measure_display) (M : measurableType d).

(* f : mR -> qbs_prob (R_qbs M), a QBS morphism from R_qbs mR
   into the probability monad on R_qbs M *)
Variable (f : mR -> qbs_prob (@R_qbs R _ M)).
Variable (p : qbs_prob (@R_qbs R _ mR)).

(* Strong morphism condition *)
Hypothesis hf_strong :
  @qbs_morphism_strong R (@R_qbs R _ mR) (@R_qbs R _ M) f.

(* Kernel measurability for the mu component *)
Hypothesis hf_kernel :
  forall (U : set mR), measurable U ->
    measurable_fun setT
      (fun r : mR => qbs_prob_mu (f (qbs_prob_alpha p r)) U).

(* KEY LEMMA: With the strong condition and kernel measurability
   hypothesis, the map r |-> qbs_to_giry(f(alpha_p(r)))(U) is
   measurable for each measurable U in M.

   Proof sketch:
   - The strong condition gives a shared alpha_Y : mR -> M with
     qbs_prob_alpha(f(alpha_p(r))) = alpha_Y for all r.
   - Since qbs_to_giry_mu(f(alpha_p(r)))(U) =
     qbs_prob_mu(f(alpha_p(r)))(alpha_Y^{-1}(U)), and
     alpha_Y^{-1}(U) is a fixed measurable set (alpha_Y is in
     qbs_Mx(R_qbs M) = measurable_fun setT), the map reduces
     to r |-> qbs_prob_mu(f(alpha_p(r)))(V) for a fixed
     measurable V, which is measurable by hypothesis. *)
Lemma qbs_strong_measurable_kernel (U : set M) (mU : measurable U) :
  measurable_fun setT
    (fun r : mR => qbs_to_giry (f (qbs_prob_alpha p r)) U).
Proof.
have hstrong :=
  @hf_strong (qbs_prob_alpha p) (qbs_prob_alpha_random p).
case: hstrong => alpha_Y [g [halpha_Y [hbeta_a hbeta_g]]].
(* alpha_Y : mR -> M is in qbs_Mx (R_qbs M) = measurable_fun setT *)
have halpha_meas : measurable_fun setT alpha_Y := halpha_Y.
rewrite /qbs_to_giry /qbs_to_giry_mu /=.
(* Rewrite using the shared alpha *)
have heq : (fun r => qbs_prob_mu (f (qbs_prob_alpha p r))
              (qbs_prob_alpha (f (qbs_prob_alpha p r)) @^-1` U)) =
           (fun r => qbs_prob_mu (f (qbs_prob_alpha p r))
              (alpha_Y @^-1` U)).
  apply: boolp.funext => r.
  by rewrite hbeta_a.
rewrite heq.
(* Now alpha_Y^{-1}(U) is a fixed measurable set *)
apply: hf_kernel.
(* Need: measurable (alpha_Y @^-1` U) *)
have := halpha_meas measurableT U mU.
by rewrite setTI.
Qed.

(* The kernel map has total mass 1 (it's a probability) *)
Lemma qbs_strong_kernel_prob (r : mR) :
  qbs_to_giry (f (qbs_prob_alpha p r)) setT = 1.
Proof. exact: probability_setT. Qed.

(* The kernel is s-finite *)
Lemma qbs_strong_kernel_sfinite (r : mR) :
  sfinite_measure (qbs_to_giry (f (qbs_prob_alpha p r))).
Proof.
apply: sfinite_measure_sigma_finite.
apply: fin_num_fun_sigma_finite.
  by rewrite measure0.
by move=> U mU; exact: fin_num_measure.
Qed.

(* ================================================================== *)
(* Section 3: Properties of qbs_to_giry of the QBS bind               *)
(* ================================================================== *)

Let bp := qbs_bind_strong (@R_qbs R _ mR) (@R_qbs R _ M) p f hf_strong.

(* qbs_to_giry(bind(p,f)) unfolds to mu_p applied to the
   preimage through the diagonal alpha *)
Lemma qbs_bind_giry_unfold (U : set M) (mU : measurable U) :
  qbs_to_giry bp U =
  qbs_prob_mu p
    ((fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r) @^-1` U).
Proof.
by rewrite /bp /qbs_bind_strong /qbs_to_giry /qbs_to_giry_mu /=.
Qed.

(* With the strong condition, the diagonal alpha simplifies to alpha_Y.
   So qbs_to_giry(bind(p,f))(U) = mu_p(alpha_Y^{-1}(U)). *)
Lemma qbs_bind_giry_eq (U : set M) (mU : measurable U) :
  exists alpha_Y : mR -> M,
    @qbs_Mx R (@R_qbs R _ M) alpha_Y /\
    qbs_to_giry bp U = qbs_prob_mu p (alpha_Y @^-1` U).
Proof.
have hstrong :=
  @hf_strong (qbs_prob_alpha p) (qbs_prob_alpha_random p).
case: hstrong => alpha_Y [g [halpha_Y [hbeta_a hbeta_g]]].
exists alpha_Y; split; first exact: halpha_Y.
rewrite /bp /qbs_bind_strong /qbs_to_giry /qbs_to_giry_mu /=.
congr (qbs_prob_mu p _).
apply: boolp.funext => r /=.
by rewrite hbeta_a.
Qed.

(* The Giry image of the QBS bind is a probability measure *)
Lemma qbs_bind_is_probability :
  qbs_to_giry bp setT = 1.
Proof. exact: probability_setT. Qed.

(* The Giry image of the QBS bind is s-finite *)
Lemma qbs_bind_sfinite :
  sfinite_measure (qbs_to_giry bp).
Proof.
apply: sfinite_measure_sigma_finite.
apply: fin_num_fun_sigma_finite.
  by rewrite measure0.
by move=> U mU; exact: fin_num_measure.
Qed.

(* ================================================================== *)
(* Section 4: Iterated integral with strong condition                  *)
(* ================================================================== *)

(* The iterated QBS integral: integrate the inner integral first *)
Definition qbs_iterated_integral (h : M -> \bar R) :=
  @qbs_integral R (@R_qbs R _ mR) p
    (fun x : mR =>
       @qbs_integral R (@R_qbs R _ M) (f x) h).

(* The bind integral *)
Definition qbs_bind_integral (h : M -> \bar R) :=
  @qbs_integral R (@R_qbs R _ M) bp h.

(* Unfolding the iterated integral *)
Lemma qbs_iterated_integral_unfold (h : M -> \bar R) :
  qbs_iterated_integral h =
  \int[qbs_prob_mu p]_r
    (\int[qbs_prob_mu (f (qbs_prob_alpha p r))]_r'
      h (qbs_prob_alpha (f (qbs_prob_alpha p r)) r')).
Proof. by []. Qed.

(* With the strong condition, the alpha part of the inner integral
   is shared: alpha_{f(alpha_p(r))} = alpha_Y for all r. *)
Lemma qbs_iterated_integral_strong (h : M -> \bar R) :
  exists alpha_Y : mR -> M,
    @qbs_Mx R (@R_qbs R _ M) alpha_Y /\
    qbs_iterated_integral h =
    \int[qbs_prob_mu p]_r
      (\int[qbs_prob_mu (f (qbs_prob_alpha p r))]_r'
        h (alpha_Y r')).
Proof.
have hstrong :=
  @hf_strong (qbs_prob_alpha p) (qbs_prob_alpha_random p).
case: hstrong => alpha_Y [g [halpha_Y [hbeta_a hbeta_g]]].
exists alpha_Y; split; first exact: halpha_Y.
rewrite /qbs_iterated_integral /qbs_integral /=.
congr (\int[_]_r _).
apply: boolp.funext => r.
by rewrite hbeta_a.
Qed.

(* The bind integral simplifies with the strong condition *)
Lemma qbs_bind_integral_strong (h : M -> \bar R) :
  exists alpha_Y : mR -> M,
    @qbs_Mx R (@R_qbs R _ M) alpha_Y /\
    qbs_bind_integral h =
    \int[qbs_prob_mu p]_r h (alpha_Y r).
Proof.
have hstrong :=
  @hf_strong (qbs_prob_alpha p) (qbs_prob_alpha_random p).
case: hstrong => alpha_Y [g [halpha_Y [hbeta_a hbeta_g]]].
exists alpha_Y; split; first exact: halpha_Y.
rewrite /qbs_bind_integral /qbs_integral /=.
congr (\int[_]_r _).
apply: boolp.funext => r.
by rewrite hbeta_a.
Qed.

(* ================================================================== *)
(* Section 5: The Giry-level Fubini via kernel composition             *)
(* ================================================================== *)

(* The connection between iterated integration and bind is through
   the KERNEL INTEGRAL identity. Using the Giry bridge:

   Iterated: \int[mu_p]_r (\int[kernel(r)]_y h(y))
           = \int[mu_p]_r (\int[g(r)]_r' h(alpha_Y(r')))

   Bind:     \int[mu_p]_r h(alpha_Y(r))

   These are equal iff for mu_p-a.e. r:
     \int[g(r)]_r' h(alpha_Y(r')) = h(alpha_Y(r))

   i.e., g(r) concentrates mass at r (g(r) = dirac(r)), which means
   the inner measure is a Dirac distribution. This holds when f is
   return-like, but NOT in general.

   The correct framework for relating these two integrals is via
   the product measure and the diagonal map, requiring either
   Tonelli's theorem or disintegration. This is beyond the scope
   of the current QBS formalization. *)

(* What IS provable: the iterated integral can be expressed via
   the kernel when h is measurable *)
Lemma qbs_iterated_as_kernel
  (h : M -> \bar R)
  (h_meas : measurable_fun setT h)
  (h_ge0 : forall y, 0 <= h y) :
  exists alpha_Y : mR -> M,
    @qbs_Mx R (@R_qbs R _ M) alpha_Y /\
    (measurable_fun setT alpha_Y ->
     qbs_iterated_integral h =
     \int[qbs_prob_mu p]_r
       (\int[qbs_to_giry (f (qbs_prob_alpha p r))]_y h y)).
(* Proof would require an integrability hypothesis for the inner integral.
   The QBS integral equals the Giry integral by qbs_integral_giry,
   but applying it pointwise requires pointwise integrability which
   we have not assumed. We state a cleaner version below with the
   explicit integrability hypothesis. *)
Abort.

(* Cleaner version: direct equality using qbs_integral_giry *)
Lemma qbs_iterated_giry_eq
  (h : M -> \bar R)
  (h_meas : measurable_fun setT h)
  (h_int : forall r,
    (qbs_prob_mu (f (qbs_prob_alpha p r))).-integrable setT
      (h \o qbs_prob_alpha (f (qbs_prob_alpha p r)))) :
  qbs_iterated_integral h =
  \int[qbs_prob_mu p]_r
    (\int[qbs_to_giry (f (qbs_prob_alpha p r))]_y h y).
Proof.
rewrite /qbs_iterated_integral /qbs_integral /=.
congr (\int[_]_r _).
apply: boolp.funext => r.
exact: (@qbs_integral_giry R _ M (f (qbs_prob_alpha p r)) h h_meas (h_int r)).
Qed.

End strong_kernel.

(* ================================================================== *)
(* Section 6: The mR -> mR special case (self-kernels)                *)
(* ================================================================== *)

(* The simplest interesting case: f : mR -> qbs_prob (R_qbs mR),
   where both source and target are mR. Here alpha_Y : mR -> mR
   is measurable, and qbs_to_giry maps to probability mR R. *)

Section self_kernel.

Variable (f : mR -> qbs_prob (@R_qbs R _ mR)).
Variable (p : qbs_prob (@R_qbs R _ mR)).

Hypothesis hf_strong :
  @qbs_morphism_strong R (@R_qbs R _ mR) (@R_qbs R _ mR) f.

Hypothesis hf_kernel :
  forall (U : set mR), measurable U ->
    measurable_fun setT
      (fun r : mR => qbs_prob_mu (f (qbs_prob_alpha p r)) U).

(* Measurable kernel for the self case *)
Lemma qbs_self_measurable_kernel (U : set mR) (mU : measurable U) :
  measurable_fun setT
    (fun r : mR => qbs_to_giry (f (qbs_prob_alpha p r)) U).
Proof.
exact: (@qbs_strong_measurable_kernel _
  _ _ _ hf_strong hf_kernel _ mU).
Qed.

(* The bind integral equals a pushforward integral *)
Lemma qbs_self_bind_eq (h : mR -> \bar R)
  (h_meas : measurable_fun setT h) :
  exists alpha_Y : mR -> mR,
    measurable_fun setT alpha_Y /\
    @qbs_integral R (@R_qbs R _ mR)
      (qbs_bind_strong (@R_qbs R _ mR) (@R_qbs R _ mR) p f hf_strong)
      h =
    \int[qbs_prob_mu p]_r h (alpha_Y r).
Proof.
have hstrong :=
  @hf_strong (qbs_prob_alpha p) (qbs_prob_alpha_random p).
case: hstrong => alpha_Y [g [halpha_Y [hbeta_a hbeta_g]]].
exists alpha_Y; split.
- exact: halpha_Y.
- rewrite /qbs_integral /=.
  congr (\int[_]_r _).
  apply: boolp.funext => r.
  by rewrite hbeta_a.
Qed.

End self_kernel.

(* ================================================================== *)
(* Section 7: Summary                                                  *)
(* ================================================================== *)

(* SUMMARY OF FINDINGS
   ====================

   THE KEY QUESTION was: Is r |-> qbs_prob_mu(f(alpha_p(r))) a
   measurable kernel?

   ANSWER: NOT automatically, but YES with an explicit hypothesis.

   DETAILED ANALYSIS:

   1. THE POINTWISE CONDITION IS INSUFFICIENT.
      monadP_random_pw says: for each r, alpha_{f(alpha_p(r))} is in Mx.
      This constrains the alpha (random element) component but says
      nothing about how the mu (measure) component varies with r.
      The mu components could be arbitrary unrelated probability
      measures.

   2. THE STRONG CONDITION HELPS BUT IS INSUFFICIENT.
      monadP_random (the strong condition) provides:
      - A shared alpha_Y : mR -> Y across all r
      - A function g : mR -> probability mR R with g(r) = mu_{f(alpha_p(r))}
      This makes the alpha component constant, so the kernel
      qbs_to_giry(f(alpha_p(r)))(U) = g(r)(alpha_Y^{-1}(U)).
      But there is no constraint that g is measurable.

   3. THE MINIMAL BRIDGING HYPOTHESIS is qbs_mu_measurable_kernel:
      for each measurable U, r |-> qbs_prob_mu(f(alpha_p(r)))(U) is
      measurable. With this PLUS the strong condition, we get a
      genuine measurable kernel on standard Borel spaces.

   4. QBS BIND != KERNEL COMPOSITION.
      The QBS bind uses a diagonal construction:
        bind(p,f).alpha(r) = alpha_{f(alpha_p(r))}(r) = alpha_Y(r)
        bind(p,f).mu = mu_p
      So qbs_to_giry(bind) = pushforward(mu_p, alpha_Y).

      Kernel composition gives:
        kcomp(qbs_to_giry(p), kernel)(U)
        = \int[qbs_to_giry(p)]_x kernel(x)(U)
        = \int[mu_p]_r qbs_to_giry(f(alpha_p(r)))(U)
        = \int[mu_p]_r g(r)(alpha_Y^{-1}(U))

      These differ: the bind gives mu_p(alpha_Y^{-1}(U)) while
      the kernel composition gives \int[mu_p] g(r)(alpha_Y^{-1}(U)).
      They are equal only when g(r) = dirac(r) a.e.

   5. THE CONNECTION REQUIRES DISINTEGRATION.
      To relate the QBS bind integral to the iterated integral
      (which is what kernel composition computes), one needs
      the disintegration theorem, which is not in the current
      development.

   WHAT IS PROVED (without Admitted):
   - qbs_strong_measurable_kernel: strong + kernel hyp => measurable kernel
   - qbs_bind_giry_eq: the Giry image of bind decomposes cleanly
   - qbs_iterated_integral_strong: strong condition simplifies iteration
   - qbs_bind_integral_strong: strong condition simplifies bind integral
   - qbs_iterated_giry_eq: iterated integral equals Giry integral
   - qbs_bind_is_probability, qbs_bind_sfinite: basic kernel properties *)

End qbs_fubini.

Arguments qbs_mu_measurable_kernel {R}.
