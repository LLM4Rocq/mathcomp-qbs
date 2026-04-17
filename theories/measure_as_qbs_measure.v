(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals ereal topology
  classical_sets borel_hierarchy numfun measure lebesgue_integral_definition
  lebesgue_stieltjes_measure lebesgue_measure lebesgue_integral probability
  measurable_realfun derive ftc gauss_integral charge boolp.
From QBS Require Import quasi_borel probability_qbs.

(**md**************************************************************************)
(* # Embedding Classical Probability into QBS Probability                     *)
(*                                                                            *)
(* Shows how standard probability measures on standard Borel spaces           *)
(* embed into QBS probability triples, and constructs standard                *)
(* distributions as QBS probabilities.                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*   as_qbs_prob d M f g hf hg hs P == embed probability P into R_qbs M      *)
(*   qbs_normal_distribution mu sigma == Normal(mu, sigma) as QBS probability *)
(*   qbs_bernoulli p == Bernoulli(p) as QBS probability on boolQ             *)
(*   qbs_uniform == Uniform[0,1] as QBS probability on realQ                 *)
(*   qbs_expect_normal == E[Normal(mu,sigma)] = mu                           *)
(*                        (requires integrability hypotheses)                *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import boolp order.Order.POrderTheory.

Local Open Scope classical_set_scope.

Section measure_as_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(** Embedding classical probability into QBS probability.
    For a standard Borel space M with measurable isomorphism to R,
    given a probability measure P on M, we construct a QBS triple.
    The key idea: if g : R -> M is a measurable section (with
    f : M -> R measurable and g o f = id), then (g, pushforward_f P)
    is a valid QBS probability triple on R_qbs(M). *)

(** Embed a probability on R into a QBS triple on realQ. *)
Definition as_qbs_prob_realQ
  (encode : mR -> mR)
  (decode : mR -> mR)
  (h_encode_meas : measurable_fun setT encode)
  (h_decode_meas : measurable_fun setT decode)
  (h_section : decode \o encode =1 idfun)
  (P : probability mR R) : qbs_prob (realQ R).
Proof.
apply: (@mkQBSProb R (realQ R) decode).
- exact: P.
- exact: h_decode_meas.
Qed.

(** Embed a probability on M into a QBS triple on R_qbs. *)
Definition as_qbs_prob d (M : measurableType d)
  (f : M -> mR) (g : mR -> M)
  (hf : measurable_fun setT f)
  (hg : measurable_fun setT g)
  (h_section : forall x, g (f x) = x)
  (P : probability mR R) : qbs_prob (R_qbs R M).
Proof.
apply: (@mkQBSProb R (R_qbs R M) g P).
exact: hg.
(* Must be Defined: as_qbs_prob_recover and as_qbs_prob_recover_full
   rely on transparency to reduce qbs_prob_mu/qbs_prob_event
   against the underlying pushforward. *)
Defined.

Arguments as_qbs_prob : clear implicits.

(** Standard distributions as QBS probabilities. *)

(** Normal distribution as QBS probability. *)
Definition qbs_normal_distribution
  (mu sigma : R) (hsigma : (0 < sigma)%R) : qbs_prob (realQ R) :=
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

Lemma as_qbs_prob_recover d (M : measurableType d)
  (f : M -> mR) (g : mR -> M)
  (hf : measurable_fun setT f)
  (hg : measurable_fun setT g)
  (h_section : forall x, g (f x) = x)
  (P : probability mR R)
  (U : set M) (hU : measurable U) :
  qbs_prob_mu (as_qbs_prob d M f g hf hg h_section P) (g @^-1` U) =
  P (g @^-1` U).
Proof. by []. Qed.

Lemma as_qbs_prob_recover_full d (M : measurableType d)
  (f : M -> mR) (g : mR -> M)
  (hf : measurable_fun setT f)
  (hg : measurable_fun setT g)
  (h_section : forall x, g (f x) = x)
  (h_retract : forall r, f (g r) = r)
  (P : probability mR R)
  (U : set M) (hU : measurable U) :
  qbs_prob_event (R_qbs R M) (as_qbs_prob d M f g hf hg h_section P) U =
  P (f @` U).
Proof.
rewrite /qbs_prob_event /=.
congr (P _).
rewrite eqEsubset; split => [r hUgr | r [x hUx hfx]].
- exists (g r) => //; exact: h_retract.
- rewrite /preimage /= -hfx h_section; exact: hUx.
Qed.

Lemma qbs_normal_morphism (sigma : R) (hsigma : (0 < sigma)%R) :
  @qbs_morphism R (realQ R) (monadP (realQ R))
    (fun mu => qbs_normal_distribution mu sigma hsigma).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /= => r.
exact: @measurable_id _ mR setT.
Qed.

Lemma qbs_uniform_random :
  qbs_Mx (fun _ : mR => qbs_uniform).
Proof.
rewrite /qbs_Mx /= => r.
exact: @measurable_id _ mR setT.
Qed.

(** Convert normal_prob integral to Lebesgue with density. *)
Lemma integral_normal_prob (m s : R) (hs : (s != 0)%R)
    f (f_meas : measurable_fun setT f)
    (f_int : (\int[normal_prob m s]_x `|f x| < +oo)%E) :
  (\int[normal_prob m s]_x f x =
  \int[lebesgue_measure]_x (f x * (normal_pdf m s x)%:E))%E.
Proof.
rewrite -(Radon_Nikodym_change_of_variables
            (normal_prob_dominates m s) measurableT); last first.
  by apply/integrableP; split.
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //; apply: (measurable_int lebesgue_measure).
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

(** Distribution expectation lemmas. *)

Section distribution_expectations.
Local Open Scope ring_scope.

(** E[Bernoulli(p)] = p. *)
Lemma qbs_expect_bernoulli (p : R) (hp0 : 0 <= p) (hp1 : p <= 1) :
  qbs_expect (boolQ R) (qbs_bernoulli p hp0 hp1) (fun b : bool => b%:R) = p%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
rewrite integral_uniform//; last first.
  apply: measurableT_comp => //=.
  apply: measurableT_comp => //=.
  exact: measurable_fun_ltr (@measurable_id _ mR setT)
    (@measurable_cst _ _ mR mR setT p).
rewrite subr0 invr1 mul1e.
rewrite (_ : (fun x : mR => _) =
  (fun x => (indic [set r : mR | r < p] x)%:E)); last first.
  by apply: funext => x /=; rewrite indicE mem_setE.
rewrite integral_indic //=; last first.
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
  [|exact: measurable_funepos|by move=> x; exact: funepos_ge0].
rewrite (@integral_uniform _ 0 1 ltr01 [eta funeneg.body (@EFin R)]);
  [|exact: measurable_funeneg|by move=> x; exact: funeneg_ge0].
rewrite subr0 invr1 mul1e mul1e -integralE /=.
rewrite (@ftc.continuous_FTC2 _ idfun (fun x => x ^+ 2 / 2) 0 1 ltr01).
- by rewrite expr0n /= mul0r oppr0 adde0 expr1n mul1r.
- by apply: (@continuous_subspaceT _ _ _ idfun) => x /=; exact: cvg_id.
- split.
  + move=> x hx.
    by apply: derive.derivableM;
      [exact: derive.exprn_derivable|exact: derive.derivable_cst].
  + have := @derive.continuous_horner R (2^-1 *: 'X^2); move/(_ 0) => /=.
    rewrite /continuous_at /= hornerZ hornerXn expr0n /= mul0r mulr0 => h.
    suff -> : (fun x : R => x ^+ 2 / 2) = horner (2^-1 *: 'X^2 : {poly R}).
      by move: h; exact: cvg_within_filter.
    by apply: funext => x; rewrite hornerZ hornerXn mulrC.
  + have := @derive.continuous_horner R (2^-1 *: 'X^2); move/(_ 1) => /=.
    rewrite /continuous_at /= hornerZ hornerXn expr1n mulr1 => h.
    suff -> : (fun x : R => x ^+ 2 / 2) = horner (2^-1 *: 'X^2 : {poly R}).
      by rewrite div1r; move: h; exact: cvg_within_filter.
    by apply: funext => x; rewrite hornerZ hornerXn mulrC.
- move=> x hx /=.
  rewrite derive1E derive.deriveM;
    [|exact: derive.exprn_derivable|exact: derive.derivable_cst].
  rewrite derive.derive_cst GRing.scaler0 GRing.add0r.
  rewrite (@derive.derive_val _ _ _ _ _ _ _
    (derive.is_deriveX 2 (derive.is_derive_id x 1))) /=.
  by rewrite expr1 /GRing.scale /= mulr1 mulrA mulVf ?mul1r // pnatr_eq0.
Qed.

(** E[Normal(mu,sigma)] = mu
    (requires integrability hypotheses). *)
Lemma qbs_expect_normal (mu sigma : R) (hsigma : 0 < sigma)
  (id_int : (\int[normal_prob mu sigma]_x `|x%:E| < +oo)%E)
  (odd_int : lebesgue_measure.-integrable setT
    (fun x => ((x - mu) * normal_pdf mu sigma x)%:E))
  (odd_zero : (\int[lebesgue_measure]_x
    ((x - mu) * normal_pdf mu sigma x)%:E = 0 :> \bar R)%E) :
  qbs_expect (realQ R) (qbs_normal_distribution mu sigma hsigma)
    (fun x => x) = mu%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
have hsigma0 : sigma != 0 by exact: lt0r_neq0.
rewrite (integral_normal_prob hsigma0)//=.
under eq_integral do rewrite -EFinM.
(* Split x * pdf = mu * pdf + (x - mu) * pdf *)
rewrite (_ : (fun x => (x * normal_pdf mu sigma x)%:E) =
  (fun x => (mu * normal_pdf mu sigma x +
             (x - mu) * normal_pdf mu sigma x)%:E)); last first.
  by apply: funext => x /=; rewrite -mulrDl addrC subrK.
under eq_integral do rewrite EFinD.
have hint1 : lebesgue_measure.-integrable setT
    (fun x => (mu * normal_pdf mu sigma x)%:E).
  rewrite (_ : (fun x => (mu * _)%:E) =
    (fun x => mu%:E * (normal_pdf mu sigma x)%:E)%E); last first.
    by apply: funext => x; rewrite EFinM.
  exact: (integrableZl measurableT mu (integrable_normal_pdf mu sigma)).
rewrite (integralD measurableT hint1 odd_int).
rewrite (_ : (fun x => (mu * normal_pdf mu sigma x)%:E) =
  (fun x => mu%:E * (normal_pdf mu sigma x)%:E)%E); last first.
  by apply: funext => x; rewrite EFinM.
rewrite integralZl//=; last exact: integrable_normal_pdf.
by rewrite integral_normal_pdf -EFinM mulr1 odd_zero adde0.
Qed.

End distribution_expectations.

End measure_as_qbs.
