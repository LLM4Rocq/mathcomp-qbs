(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology normedtype
  classical_sets borel_hierarchy numfun measure lebesgue_integral_definition
  lebesgue_stieltjes_measure lebesgue_measure lebesgue_integral probability
  measurable_realfun derive ftc gauss_integral charge boolp.
From mathcomp Require giry.
From mathcomp.algebra_tactics Require Import ring.
From QBS Require Import quasi_borel probability_qbs qbs_monad normal_centred.

(**md**************************************************************************)
(* # Embedding Classical Probability into QBS Probability                     *)
(*                                                                            *)
(* Standard distributions as QBS probabilities. The general embedding of a    *)
(* probability measure on a standard Borel space is giry_to_qbs (qbs_giry.v). *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_normal_distribution mu sigma == Normal(mu, sigma) as QBS probability *)
(*   qbs_bernoulli p == Bernoulli(p) as QBS probability on boolQ              *)
(*   qbs_interval_uniform ab == Uniform[a,b] as QBS probability on realQ, for *)
(*                           ab : a < b                                       *)
(*   qbs_uniform == Uniform[0,1] = qbs_interval_uniform ltr01                 *)
(*   intervalQ == QBS of pairs (a, b) with a < b (subspace of R * R)          *)
(*   qbs_uniformQ == (a, b) |-> Uniform[a,b] as a morphism                    *)
(*                   intervalQ -> P(R) (qbs_uniform_of_morphism)              *)
(*   qbs_bernoulli_event == the law of qbs_bernoulli is bernoulli_prob p      *)
(*   qbs_expect_interval_uniform == E[Uniform[a,b]] = (a + b) / 2             *)
(*   qbs_expect_normal == E[Normal(mu,sigma)] = mu                            *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import boolp order.Order.POrderTheory.

Local Open Scope classical_set_scope.

Section measure_as_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

Implicit Types (p mu sigma : R).

(** Standard distributions as QBS probabilities. *)

(** Normal distribution as QBS probability. *)
Definition qbs_normal_distribution (mu sigma : R) : qbs_prob (realQ R) :=
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

(** Uniform distribution on [a,b], for a < b, as QBS probability. *)
Definition qbs_interval_uniform (a b : R) (ab : (a < b)%R) :
    qbs_prob (realQ R) :=
  @mkQBSProb R (realQ R) idfun
    (uniform_prob ab : probability mR R)
    (@measurable_id _ mR setT).

Arguments qbs_interval_uniform {a b}.

(** Uniform[0,1] distribution as QBS probability. *)
Definition qbs_uniform : qbs_prob (realQ R) := qbs_interval_uniform ltr01.

(** The QBS of intervals (a, b) with a < b, and Uniform[a,b] as a morphism
    out of it (AFP qbs_interval_uniform_distribution_morphism). *)
Definition intervalQ : qbsType R :=
  @sub_qbs R (prodQ (realQ R) (realQ R)) (fun ab => (ab.1 < ab.2)%R).

Definition qbs_uniform_of (ab : intervalQ) : monadP (realQ R) :=
  qbs_interval_uniform (svalP ab).

Lemma qbs_uniform_of_morphism :
  qbs_morphism (X := intervalQ) (Y := monadP (realQ R)) qbs_uniform_of.
Proof.
move=> c [m1 m2].
exists idfun, (fun r => uniform_prob (svalP (c r)) : giry.giry mR R).
split => //; first exact: (@measurable_id _ mR setT).
- apply: giry.measurable_giry_codensity => // B mB.
  pose f (z : (mR * mR) * mR) : \bar R :=
    (\1_B z.2 * uniform_pdf z.1.1 z.1.2 z.2)%:E.
  have -> : (fun x => uniform_prob (svalP (c x)) B) =
      fubini_F lebesgue_measure f \o (fun x => sval (c x)).
    apply/funext => x; rewrite /uniform_prob /fubini_F /= integral_mkcond.
    apply: eq_integral => y _; rewrite /f /functions.patch indicE.
    by case: (y \in B); rewrite ?mul1r ?mul0r.
  have mf : measurable_fun [set: (mR * mR) * mR] f.
    apply/measurable_EFinP; apply: measurable_funM.
      exact: measurableT_comp (measurable_indic mB) measurable_snd.
    rewrite /uniform_pdf; apply: measurable_fun_ifT => //.
      apply: measurable_and; apply: measurable_fun_ler => //.
      - exact: measurableT_comp measurable_fst measurable_fst.
      - exact: measurableT_comp measurable_snd measurable_fst.
    apply: measurableT_comp (@measurable_invr R) _.
    by apply: measurable_funB; apply: measurableT_comp.
  have f0 z : (0 <= f z)%E.
    rewrite lee_fin mulr_ge0 ?indicE ?ler0n// /uniform_pdf.
    case: ifPn => // /andP[h1 h2].
    by rewrite invr_ge0 subr_ge0 (le_trans h1 h2).
  apply: measurableT_comp; first exact: measurable_fun_fubini_tonelli_F.
  by apply/measurable_fun_pairP; split.
- by move=> r; exact: probability_setT.
Qed.

Definition qbs_uniformQ : qbsHomType intervalQ (monadP (realQ R)) :=
  HB.pack qbs_uniform_of
    (isQBSMorphism.Build R _ _ _ qbs_uniform_of_morphism).


Lemma qbs_normal_morphism (sigma : R) :
  @qbs_morphism R (realQ R) (monadP (realQ R))
    (fun mu => qbs_normal_distribution mu sigma).
Proof.
move=> a ha; exists idfun, (fun r => normal_prob (a r) sigma : giry.giry mR R).
split => //.
- exact: (@measurable_id _ mR setT).
- apply: giry.measurable_giry_codensity => // B mB.
  exact: measurableT_comp (measurable_normal_prob _ mB) ha.
- by move=> r; exact: probability_setT.
Qed.

(** mu |-> N(mu, sigma) as a bundled morphism R -> P(R). *)
Definition qbs_normalQ (sigma : R) : qbsHomType (realQ R) (monadP (realQ R)) :=
  HB.pack (fun mu : realQ R => qbs_normal_distribution mu sigma : monadP _)
    (isQBSMorphism.Build R _ _ _ (qbs_normal_morphism sigma)).

(** Distribution expectation lemmas. *)

Section distribution_expectations.
Local Open Scope ring_scope.

(** The mass of [0,1]-uniform below p is p. *)
Lemma uniform_prob_lt (p : R) : 0 <= p <= 1 ->
  uniform_prob ltr01 [set r : mR | (r < p)%R] = p%:E.
Proof.
move=> /andP[hp0 hp1].
have mE : measurable [set r : mR | (r < p)%R].
  have -> : [set r : mR | r < p] = [set` `]-oo, p[%R].
    by apply/seteqP; split => x /=; rewrite in_itv /=.
  exact: measurable_itv.
rewrite -[X in uniform_prob _ X]setIT -integral_indic//.
rewrite integral_uniform//.
- exact/measurable_EFinP/measurable_indic.
- by move=> x; rewrite lee_fin.
rewrite subr0 invr1 mul1e integral_indic //=.
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

(** E[Bernoulli(p)] = p. *)
Lemma qbs_expect_bernoulli (p : R) (hp0 : 0 <= p) (hp1 : p <= 1) :
  qbs_expect (boolQ R) (qbs_bernoulli p hp0 hp1) (fun b : bool => b%:R) = p%:E.
Proof.
rewrite /qbs_expect /qbs_integral /=.
have -> : (fun x : mR => ((((x < p)%R : bool)%:R : R))%:E) =
    (fun x => (\1_[set r : mR | r < p] x)%:E).
  by apply: funext => x /=; rewrite indicE mem_setE.
rewrite integral_indic//= ?setIT ?uniform_prob_lt ?hp0//.
have -> : [set r : mR | r < p] = [set` `]-oo, p[%R].
  by apply/seteqP; split => x /=; rewrite in_itv /=.
exact: measurable_itv.
Qed.

(** The law of qbs_bernoulli is the Bernoulli probability of
    mathcomp-analysis. *)
Lemma qbs_bernoulli_event (p : R) (hp0 : 0 <= p) (hp1 : p <= 1)
    (A : set bool) :
  qbs_prob_event (boolQ R) (qbs_bernoulli p hp0 hp1) A = bernoulli_prob p A.
Proof.
have p01 : 0 <= p <= 1 by apply/andP.
pose f : {mfun mR >-> bool} := mfun_Sub (mem_set (measurable_fun_ltr
  (@measurable_id _ mR setT) (@measurable_cst _ _ mR mR setT p))).
pose P : probability bool R :=
  distribution (uniform_prob ltr01 : probability mR R) f.
suff: P =1 bernoulli_prob p by exact.
apply: eq_bernoulli => //.
rewrite /P /distribution /= /pushforward.
have -> : f @^-1` [set true] = [set r : mR | (r < p)%R].
  by apply/seteqP; split => r /=.
exact: uniform_prob_lt.
Qed.

Lemma qbs_bernoulli_law (p : R) (hp0 : 0 <= p) (hp1 : p <= 1)
    (A : set bool) :
  qbs_law (qbs_bernoulli p hp0 hp1) A = bernoulli_prob p A.
Proof. exact: qbs_bernoulli_event. Qed.

(** Integrals against Uniform(a,b) of nonnegative measurable functions. *)
Lemma ge0_qbs_integral_interval_uniform (a b : R) (ab : a < b)
    (h : mR -> \bar R) :
  measurable_fun setT h -> (forall x, 0 <= h x)%E ->
  qbs_integral (realQ R) (qbs_interval_uniform ab) h =
  ((b - a)^-1%:E * \int[lebesgue_measure]_(x in `[a, b]) h x)%E.
Proof. by move=> mh h0; exact: integral_uniform. Qed.

(** E[Uniform(a,b)] = (a+b)/2. *)
Lemma qbs_expect_interval_uniform (a b : R) (ab : a < b) :
  qbs_expect (realQ R) (qbs_interval_uniform ab) (fun x => x) =
  ((a + b) / 2)%:E.
Proof.
have iid : lebesgue_measure.-integrable `[a, b] (@EFin R).
  apply: (@continuous_compact_integrable R idfun); first exact: segment_compact.
  by apply: continuous_in_subspaceT => x _; exact: cvg_id.
rewrite /qbs_expect /qbs_integral /= integralE /=.
rewrite (@integral_uniform _ a b ab [eta funepos.body (@EFin R)]);
  [exact: measurable_funepos|by move=> x; exact: funepos_ge0|].
rewrite (@integral_uniform _ a b ab [eta funeneg.body (@EFin R)]);
  [exact: measurable_funeneg|by move=> x; exact: funeneg_ge0|].
have mab : measurable `[a, b] by exact: measurable_itv.
have fB : (\int[lebesgue_measure]_(x in `[a, b]) (@EFin R)^\- x)%E
    \is a fin_num := integrable_neg_fin_num mab iid.
rewrite -muleBr; [by []|by rewrite fin_num_adde_defl// fin_numN|].
rewrite -integralE /=.
have cF := @continuous_horner R (2^-1 *: 'X^2 : {poly R}).
have eF : horner (2^-1 *: 'X^2 : {poly R}) = (fun x : R => x ^+ 2 / 2).
  by apply: funext => x; rewrite hornerZ hornerXn mulrC.
rewrite eF in cF.
rewrite (@continuous_FTC2 _ idfun (fun x => x ^+ 2 / 2) a b ab).
- by apply: (@continuous_subspaceT _ _ _ idfun) => x /=; exact: cvg_id.
- split.
  + move=> x hx.
    by apply: derivableM;
      [exact: exprn_derivable|exact: derivable_cst].
  + by move: (cF a); rewrite /continuous_at; exact: cvg_within_filter.
  + by move: (cF b); rewrite /continuous_at; exact: cvg_within_filter.
- move=> x hx /=.
  rewrite derive1E deriveM;
    [exact: exprn_derivable|exact: derivable_cst|].
  rewrite derive_cst GRing.scaler0 GRing.add0r.
  rewrite (@derive_val _ _ _ _ _ _ _
    (is_deriveX 2 (is_derive_id x 1))) /=.
  by rewrite expr1 /GRing.scale /= mulr1 mulrA mulVf ?mul1r // pnatr_eq0.
have ba0 : b - a != 0 by rewrite gt_eqF// subr_gt0.
rewrite -EFinB -EFinM; congr (_%:E).
have -> : b ^+ 2 / 2 - a ^+ 2 / 2 = (b - a) * ((a + b) / 2) by ring.
by rewrite mulKf.
Qed.

(** E[Uniform(0,1)] = 1/2. *)
Lemma qbs_expect_uniform :
  qbs_expect (realQ R) qbs_uniform (fun x => x) = (2%:R^-1)%:E.
Proof. by rewrite qbs_expect_interval_uniform add0r div1r. Qed.

(** E[Normal(mu,sigma)] = mu. *)
Lemma qbs_expect_normal (mu sigma : R) : sigma != 0 ->
  qbs_expect (realQ R) (qbs_normal_distribution mu sigma)
    (fun x => x) = mu%:E.
Proof.
move=> s0; have id_int := normal_prob_abs_lty mu sigma s0.
have centred_int := integrable_normal_centred mu sigma s0.
have centred_moment0 := integral_normal_centred mu sigma s0.
rewrite /qbs_expect /qbs_integral /=.
rewrite integral_normal_prob//=; first by apply/integrableP; split.
under eq_integral do rewrite -EFinM.
(* Split x * pdf = mu * pdf + (x - mu) * pdf *)
rewrite (_ : (fun x => (x * normal_pdf mu sigma x)%:E) =
  (fun x => (mu * normal_pdf mu sigma x +
             (x - mu) * normal_pdf mu sigma x)%:E)).
  by apply: funext => x /=; rewrite -mulrDl addrC subrK.
under eq_integral do rewrite EFinD.
have hint1 : lebesgue_measure.-integrable setT
    (fun x => (mu * normal_pdf mu sigma x)%:E).
  rewrite (_ : (fun x => (mu * _)%:E) =
    (fun x => mu%:E * (normal_pdf mu sigma x)%:E)%E).
    by apply: funext => x; rewrite EFinM.
  exact: (integrableZl measurableT mu (integrable_normal_pdf mu sigma)).
rewrite (integralD measurableT hint1 centred_int).
rewrite (_ : (fun x => (mu * normal_pdf mu sigma x)%:E) =
  (fun x => mu%:E * (normal_pdf mu sigma x)%:E)%E).
  by apply: funext => x; rewrite EFinM.
rewrite integralZl//=; first exact: integrable_normal_pdf.
by rewrite integral_normal_pdf -EFinM mulr1 centred_moment0 adde0.
Qed.

End distribution_expectations.

End measure_as_qbs.

Arguments qbs_normal_distribution {R}.
