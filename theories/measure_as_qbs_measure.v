(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure lebesgue_measure
  probability measurable_realfun derive ftc.
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
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(* General embedding: given a measurable encoding/decoding pair and
   a probability measure, produce a QBS probability triple on realQ. *)
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
(* Defined for computational transparency *)
Defined.

(* More general version: embedding into an arbitrary R_qbs *)
Definition as_qbs_prob (d : measure_display) (M : measurableType d)
  (f : M -> mR) (g : mR -> M)
  (hf : measurable_fun setT f)
  (hg : measurable_fun setT g)
  (h_section : forall x, g (f x) = x)
  (P : probability mR R) : qbs_prob (R_qbs R M).
Proof.
apply: (@mkQBSProb R (R_qbs R M) g P).
exact: hg.
(* Defined for computational transparency *)
Defined.

Arguments as_qbs_prob : clear implicits.

(** Standard distributions as QBS probabilities. *)

(* Normal distribution on realQ.
   Uses the math-comp analysis normal_prob as the underlying measure
   on R, with the identity function as the random element. The QBS
   triple (id, normal_prob mu sigma) represents the normal distribution
   since the pushforward id_*(normal_prob mu sigma) = normal_prob mu sigma. *)
Definition qbs_normal_distribution
  (mu sigma : R) (hsigma : (0 < sigma)%R) : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (normal_prob mu sigma : probability mR R)
    (@measurable_id _ mR setT).

Arguments qbs_normal_distribution : clear implicits.

(* Bernoulli distribution on boolQ.
   Assigns probability p to true and 1-p to false.
   Uses the uniform distribution on [0,1] with the threshold function
   alpha(r) = (r < p). The pushforward alpha_*(uniform[0,1]) satisfies
   P(true) = uniform[0,1]({r | r < p}) = p. *)
Definition qbs_bernoulli
  (p : R) (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) : qbs_prob (boolQ R) :=
  @mkQBSProb R (boolQ R) (fun r : mR => (r < p)%R)
    (uniform_prob ltr01 : probability mR R)
    (measurable_fun_ltr
      (@measurable_id _ mR setT)
      (@measurable_cst _ _ mR mR setT p)).

Arguments qbs_bernoulli : clear implicits.

(* Uniform distribution on realQ, supported on [0, 1].
   Uses the math-comp analysis uniform_prob as the underlying measure
   with the identity random element. *)
Definition qbs_uniform : qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (uniform_prob ltr01 : probability mR R)
    (@measurable_id _ mR setT).

(** Recovery theorem.
    The pushforward of the QBS measure along the alpha recovers the
    original probability measure (up to the encoding). *)

Lemma as_qbs_prob_recover (d : measure_display) (M : measurableType d)
  (f : M -> mR) (g : mR -> M)
  (hf : measurable_fun setT f)
  (hg : measurable_fun setT g)
  (h_section : forall x, g (f x) = x)
  (P : probability mR R)
  (U : set M) (hU : measurable U) :
  qbs_prob_mu (as_qbs_prob d M f g hf hg h_section P) (g @^-1` U) =
  P (g @^-1` U).
Proof.
by [].
Qed.

(* Stronger recovery: for sets in the sigma-algebra induced by f *)
Lemma as_qbs_prob_recover_full (d : measure_display) (M : measurableType d)
  (f : M -> mR) (g : mR -> M)
  (hf : measurable_fun setT f)
  (hg : measurable_fun setT g)
  (h_section : forall x, g (f x) = x)
  (h_retract : forall r, f (g r) = r)
  (P : probability mR R)
  (U : set M) (hU : measurable U) :
  @qbs_prob_event R (R_qbs R M) (as_qbs_prob d M f g hf hg h_section P) U =
  P (f @` U).
Proof.
rewrite /qbs_prob_event /=.
congr (P _).
rewrite eqEsubset; split => [r hUgr | r [x hUx hfx]].
- exists (g r) => //; exact: h_retract.
- rewrite /preimage /= -hfx h_section; exact: hUx.
Qed.

(** Parameterized distribution morphisms.
    Parameterized families of distributions are QBS morphisms from
    the parameter space to the probability monad.
    Key insight: since qbs_normal_distribution mu sigma has alpha =
    idfun for all mu, the monadP_random_pw condition reduces to showing
    qbs_Mx (realQ R) idfun, which is just measurable_id. *)

(* The normal distribution, viewed as a function of its mean parameter,
   is a QBS morphism from realQ to monadP(realQ). *)
Lemma qbs_normal_morphism (sigma : R) (hsigma : (0 < sigma)%R) :
  @qbs_morphism R (realQ R) (monadP (realQ R))
    (fun mu => qbs_normal_distribution mu sigma hsigma).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /= => r.
exact: @measurable_id _ mR setT.
Qed.

(* The uniform distribution is a constant element of monadP(realQ),
   i.e., the constant function mapping any r to qbs_uniform is a
   random element of the probability monad. *)
Lemma qbs_uniform_random :
  @qbs_Mx R (monadP (realQ R)) (fun _ : mR => qbs_uniform).
Proof.
rewrite /qbs_Mx /= => r.
exact: @measurable_id _ mR setT.
Qed.

(** Distribution expectation lemmas. *)

Section distribution_expectations.
Local Open Scope ring_scope.

Lemma qbs_expect_bernoulli (p : R) (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) :
  qbs_expect (boolQ R) (qbs_bernoulli p hp0 hp1) (fun b : bool => b%:R) = p%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
rewrite integral_uniform//; last first.
{ apply: measurableT_comp => //=.
  apply: measurableT_comp => //=.
  exact: measurable_fun_ltr (@measurable_id _ mR setT)
    (@measurable_cst _ _ mR mR setT p). }
rewrite subr0 invr1 mul1e.
rewrite (_ : (fun x : mR => _) =
  (fun x => (numfun.indic [set r : mR | (r < p)%R] x)%:E)); last first.
{ by apply: boolp.funext => x /=; rewrite numfun.indicE mem_setE. }
rewrite lebesgue_integral_definition.integral_indic //=; last first.
{ have -> : [set r : mR | (r < p)%R] = [set` `]-oo, p[%R].
  { by apply/seteqP; split => x /=; rewrite in_itv /=. }
  exact: measurable_itv. }
have -> : [set r : mR | (r < p)%R] `&` `[0, 1] = [set` `[0%R, p[%R].
{ apply/seteqP; split => x /=.
  - rewrite in_itv /= => -[xp]; rewrite in_itv /= => /andP[x0 x1].
    by apply/andP; split.
  - rewrite in_itv /= => /andP[x0 xp]; split => //.
    rewrite in_itv /=; apply/andP; split => //.
    exact: (order.Order.POrderTheory.le_trans
      (order.Order.POrderTheory.ltW xp) hp1). }
rewrite -/(lebesgue_measure.lebesgue_measure _).
rewrite lebesgue_measure.lebesgue_measure_itv /= oppr0 adde0.
case: (lerP p 0) => [p0|p0].
- have -> : p = 0 by apply: order.Order.POrderTheory.le_anti; rewrite hp0 p0.
  by rewrite order.Order.POrderTheory.ltxx.
- by rewrite ifT // lte_fin.
Qed.

Lemma qbs_expect_uniform :
  qbs_expect (realQ R) qbs_uniform (fun x => x) = (2%:R^-1)%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
rewrite lebesgue_integral_definition.integralE /=.
rewrite (@integral_uniform _ 0 1 ltr01 [eta numfun.funepos.body (@EFin R)]);
  [|exact: measurable_funepos|by move=> x; exact: numfun.funepos_ge0].
rewrite (@integral_uniform _ 0 1 ltr01 [eta numfun.funeneg.body (@EFin R)]);
  [|exact: measurable_funeneg|by move=> x; exact: numfun.funeneg_ge0].
rewrite subr0 invr1 mul1e mul1e -lebesgue_integral_definition.integralE /=.
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
    by apply: boolp.funext => x; rewrite hornerZ hornerXn mulrC.
  + have := @derive.continuous_horner R (2^-1 *: 'X^2); move/(_ 1) => /=.
    rewrite /continuous_at /= hornerZ hornerXn expr1n mulr1 => h.
    suff -> : (fun x : R => x ^+ 2 / 2) = horner (2^-1 *: 'X^2 : {poly R}).
      by move: h; exact: cvg_within_filter.
    by apply: boolp.funext => x; rewrite hornerZ hornerXn mulrC.
- move=> x hx /=.
  rewrite derive1E derive.deriveM;
    [|exact: derive.exprn_derivable|exact: derive.derivable_cst].
  rewrite derive.derive_cst mulr0 addr0.
  rewrite derive.deriveX //= derive.derive_id mulr1.
  by rewrite -mulr_natr mulrAC divff ?mulr1 // pnatr_eq0.
Qed.

End distribution_expectations.

End measure_as_qbs.
