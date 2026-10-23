(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot order functions algebra reals ereal topology
  normedtype classical_sets numfun measure lebesgue_measure lebesgue_integral
  probability measurable_realfun derive ftc boolp.
From mathcomp Require Import giry.
From mathcomp.algebra_tactics Require Import ring.
From QBS Require Import measurable_aux quasi_borel probability_qbs qbs_monad
  normal_centred.

(**md**************************************************************************)
(* # Embedding Classical Probability into QBS Probability                     *)
(*                                                                            *)
(* Standard distributions as QBS probabilities. The general embedding of a    *)
(* probability measure on a standard Borel space is giry_to_qbs (qbs_giry.v). *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_normal_distribution m s == Normal(m, s) as QBS probability           *)
(*   qbs_normalQ s == m |-> Normal(m, s) as a morphism realQ -> P(R)          *)
(*   qbs_bernoulli p == Bernoulli(p) as QBS probability on boolQ              *)
(*   qbs_interval_uniform ab == Uniform[a,b] as QBS probability on realQ, for *)
(*                           ab : a < b                                       *)
(*   qbs_uniform == Uniform[0,1] = qbs_interval_uniform ltr01                 *)
(*   intervalQ == QBS of pairs (a, b) with a < b (subspace of R * R)          *)
(*   qbs_uniform_of == ab |-> Uniform[a,b] on intervalQ                       *)
(*   qbs_uniformQ == qbs_uniform_of as a morphism intervalQ -> P(R)           *)
(*   qbs_bernoulli_event == the law of qbs_bernoulli is bernoulli_prob p      *)
(*   qbs_expect_interval_uniform == E[Uniform[a,b]] = (a + b) / 2             *)
(*   qbs_expect_normal == E[Normal(m, s)] = m                                 *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section measure_as_qbs.
Variable R : realType.

Local Abbreviation mR := (measurableTypeR R).

Implicit Types (p m s : R).

(** Standard distributions as QBS probabilities. *)

(** A probability measure on R as a QBS probability (random element idfun). *)
Let qbs_of_prob (P : probability mR R) : qbs_prob (realQ R) :=
  mkQBSProb (X := realQ R) idfun P (@measurable_id _ mR setT).

(** Normal distribution as QBS probability. *)
Definition qbs_normal_distribution m s : qbs_prob (realQ R) :=
  qbs_of_prob (normal_prob m s).

Arguments qbs_normal_distribution : clear implicits.

Let measurable_ltr p : measurable_fun setT (fun r : mR => r < p).
Proof.
exact: measurable_fun_ltr (@measurable_id _ mR setT)
  (@measurable_cst _ _ mR mR setT p).
Qed.

(** Bernoulli distribution as QBS probability on boolQ. *)
Definition qbs_bernoulli p : qbs_prob (boolQ R) :=
  mkQBSProb (X := boolQ R) (fun r : mR => r < p)
    (uniform_prob ltr01 : probability mR R) (measurable_ltr p).

Arguments qbs_bernoulli : clear implicits.

(** Uniform distribution on [a,b], for a < b, as QBS probability. *)
Definition qbs_interval_uniform (a b : R) (ab : a < b) : qbs_prob (realQ R) :=
  qbs_of_prob (uniform_prob ab).

Arguments qbs_interval_uniform {a b}.

(** Uniform[0,1] distribution as QBS probability. *)
Definition qbs_uniform : qbs_prob (realQ R) := qbs_interval_uniform ltr01.

(** The QBS of intervals (a, b) with a < b, and Uniform[a,b] as a morphism
    out of it (AFP qbs_interval_uniform_distribution_morphism). *)
Definition intervalQ : qbsType R :=
  @subQ R (prodQ (realQ R) (realQ R)) (fun ab => (ab.1 < ab.2)).

Definition qbs_uniform_of (ab : intervalQ) : monadP (realQ R) :=
  qbs_interval_uniform (svalP ab).

Lemma qbs_uniform_of_morphism :
  qbs_morphism (X := intervalQ) (Y := monadP (realQ R)) qbs_uniform_of.
Proof.
move=> c [m1 m2].
exists idfun, (fun r => uniform_prob (svalP (c r)) : giry mR R).
apply: QbsProbRep; first exact: (@measurable_id _ mR setT); last first.
  by move=> r U mU; rewrite qbs_prob_event_mk.
  by move=> r; exact: probability_setT.
apply: measurable_giry_codensity => // B mB.
  pose f (z : (mR * mR) * mR) : \bar R :=
    (\1_B z.2 * uniform_pdf z.1.1 z.1.2 z.2)%:E.
  have -> : (fun x => uniform_prob (svalP (c x)) B) =
      fubini_F lebesgue_measure f \o (fun x => sval (c x)).
    apply/funext => x; rewrite /uniform_prob /fubini_F /= integral_mkcond.
    apply: eq_integral => y _; rewrite /f patchE indicE.
    by case: (y \in B); rewrite ?mul1r ?mul0r.
  have mf : measurable_fun [set: (mR * mR) * mR] f.
    apply/measurable_EFinP; apply: measurable_funM.
      exact: measurableT_comp.
    rewrite /uniform_pdf; apply: measurable_fun_ifT => //.
      apply: measurable_and; apply: measurable_fun_ler => //.
        exact: measurableT_comp measurable_fst measurable_fst.
      exact: measurableT_comp measurable_snd measurable_fst.
    apply: measurableT_comp measurable_invr _.
    by apply: measurable_funB; apply: measurableT_comp.
  have f0 z : (0 <= f z)%E.
    rewrite lee_fin mulr_ge0 ?indicE ?ler0n// /uniform_pdf.
    case: ifPn => // /andP[h1 h2].
    by rewrite invr_ge0 subr_ge0 (le_trans h1 h2).
  apply: measurableT_comp; first exact: measurable_fun_fubini_tonelli_F.
  by apply/measurable_fun_pairP; split.
Qed.

Definition qbs_uniformQ : qbsHomType intervalQ (monadP (realQ R)) :=
  HB.pack qbs_uniform_of
    (isQBSMorphism.Build R _ _ _ qbs_uniform_of_morphism).

Lemma qbs_normal_morphism s :
  qbs_morphism (X := realQ R) (Y := monadP (realQ R))
    (fun m => qbs_normal_distribution m s).
Proof.
move=> a ha; exists idfun, (fun r => normal_prob (a r) s : giry mR R).
apply: QbsProbRep; first exact: (@measurable_id _ mR setT); last first.
  by move=> r U mU; rewrite qbs_prob_event_mk.
  by move=> r; exact: probability_setT.
apply: measurable_giry_codensity => // B mB.
exact: measurableT_comp (measurable_normal_prob _ mB) ha.
Qed.

(** m |-> N(m, s) as a bundled morphism R -> P(R). *)
Definition qbs_normalQ s : qbsHomType (realQ R) (monadP (realQ R)) :=
  HB.pack (fun m : realQ R => qbs_normal_distribution m s : monadP _)
    (isQBSMorphism.Build R _ _ _ (qbs_normal_morphism s)).

(** Distribution expectation lemmas. *)

Section distribution_expectations.

Let lt_itv p : [set r : mR | r < p] = [set` `]-oo, p[%R].
Proof. by apply/seteqP; split=> x /=; rewrite in_itv/=. Qed.

Let measurable_lt p : measurable [set r : mR | r < p].
Proof. by rewrite lt_itv; exact: measurable_itv. Qed.

(** The mass of [0,1]-uniform below p is p. *)
Lemma uniform_prob_lt p : 0 <= p <= 1 ->
  uniform_prob ltr01 [set r : mR | r < p] = p%:E.
Proof.
move=> /andP[hp0 hp1]; have mE := measurable_lt p.
rewrite -[X in uniform_prob _ X]setIT -integral_indic//.
rewrite integral_uniform//.
- exact/measurable_EFinP/measurable_indic.
- by move=> x; rewrite lee_fin.
rewrite subr0 invr1 mul1e integral_indic //=.
have -> : [set r : mR | r < p] `&` `[0, 1] = [set` `[0%R, p[%R].
  apply/seteqP; split=> x /=.
    rewrite in_itv /= => -[xp]; rewrite in_itv /= => /andP[x0 x1].
    by apply/andP; split.
  rewrite in_itv /= => /andP[x0 xp]; split=> //.
  rewrite in_itv /=; apply/andP; split=> //.
  exact: (le_trans (ltW xp) hp1).
rewrite -/(lebesgue_measure _).
rewrite lebesgue_measure_itv /= oppr0 adde0.
have [->|p0] := eqVneq p 0; first by rewrite ltxx.
by rewrite ifT// lte_fin lt0r p0.
Qed.

Lemma qbs_integral_normal m s (h : R -> \bar R) :
  qbs_measurable (realQ R) h ->
  qbs_integral (realQ R) (qbs_normal_distribution m s) h =
  (\int[normal_prob m s]_x h x)%E.
Proof. exact: qbs_integral_mk. Qed.

(** E[Bernoulli(p)] = p. *)
Lemma qbs_expect_bernoulli p (hp0 : 0 <= p) (hp1 : p <= 1) :
  qbs_expect (boolQ R) (qbs_bernoulli p) (fun b : bool => b%:R) = p%:E.
Proof.
rewrite /qbs_expect qbs_integral_mk /=.
  move=> a ha.
  have ha' : measurable_fun setT a := ha.
  have mi : measurable_fun setT (fun r => if a r then 1%E else 0%E : \bar R).
    by apply: measurable_fun_ifT => //; exact: measurable_cst.
  by apply: (eq_measurable_fun _ _ mi) => r _; case: (a r).
have -> : (fun x : mR => ((((x < p)%R : bool)%:R : R))%:E) =
    (fun x => (\1_[set r : mR | r < p] x)%:E).
  by apply: funext => x /=; rewrite indicE mem_setE.
by rewrite integral_indic//= ?setIT ?uniform_prob_lt ?hp0//.
Qed.

(** The law of qbs_bernoulli is the Bernoulli probability of
    mathcomp-analysis. *)
Lemma qbs_bernoulli_event p (hp0 : 0 <= p) (hp1 : p <= 1)
    (A : set bool) :
  qbs_prob_event (boolQ R) (qbs_bernoulli p) A = bernoulli_prob p A.
Proof.
have p01 : 0 <= p <= 1 by apply/andP.
rewrite qbs_prob_event_mk.
  exact: (@sigma_Mx_measQ _ _ bool A).
pose f : {mfun mR >-> bool} := mfun_Sub (mem_set (measurable_ltr p)).
pose P : probability bool R :=
  distribution (uniform_prob ltr01 : probability mR R) f.
suff: P =1 bernoulli_prob p by exact.
apply: eq_bernoulli => //.
rewrite /P /distribution /= /pushforward.
have -> : f @^-1` [set true] = [set r : mR | r < p].
  by apply/seteqP; split=> r /=.
exact: uniform_prob_lt.
Qed.

(** Integrals against the uniform law, for f integrable on [a,b]. *)
Let integral_uniform_integrable (a b : R) (ab : a < b) (f : mR -> \bar R) :
  measurable_fun setT f -> lebesgue_measure.-integrable `[a, b] f ->
  (\int[uniform_prob ab]_x f x =
   (b - a)^-1%:E * \int[lebesgue_measure]_(x in `[a, b]) f x)%E.
Proof.
move=> mf if_; have mab : measurable `[a, b] by exact: measurable_itv.
rewrite integralE [in RHS]integralE.
rewrite (integral_uniform ab (measurable_funepos mf) (funepos_ge0 _)).
rewrite (integral_uniform ab (measurable_funeneg mf) (funeneg_ge0 _)).
have fB := integrable_neg_fin_num mab if_.
by rewrite -muleBr// fin_num_adde_defl// fin_numN.
Qed.

(** E[Uniform(a,b)] = (a+b)/2. *)
Lemma qbs_expect_interval_uniform (a b : R) (ab : a < b) :
  qbs_expect (realQ R) (qbs_interval_uniform ab) (fun x => x) =
  ((a + b) / 2)%:E.
Proof.
have iid : lebesgue_measure.-integrable `[a, b] (@EFin R).
  apply: (@continuous_compact_integrable R idfun); first exact: segment_compact.
  by apply: continuous_in_subspaceT => x _; exact: cvg_id.
rewrite /qbs_expect qbs_integral_mk /=.
  by apply: qbs_measurable_measQ; exact/measurable_EFinP/measurable_id.
rewrite integral_uniform_integrable//.
have dF (x : R) : is_derive x 1 (fun x : R => x ^+ 2 / 2) x.
  have h := is_deriveM (is_deriveX 2 (is_derive_id x 1))
    (is_derive_cst (2^-1 : R) x 1).
  have h' : is_derive x 1 (fun y : R => y ^+ 2 / 2) _ := h.
  apply: (is_derive_eq h').
  rewrite /= scaler0 add0r expr1 /GRing.scale/= mulr1 mulrA mulVf ?mul1r//.
  by rewrite pnatr_eq0.
have cF := @continuous_horner R (2^-1 *: 'X^2 : {poly R}).
have eF : horner (2^-1 *: 'X^2 : {poly R}) = (fun x : R => x ^+ 2 / 2).
  by apply: funext => x; rewrite hornerZ hornerXn mulrC.
rewrite eF in cF.
rewrite (@continuous_FTC2 _ idfun (fun x => x ^+ 2 / 2) a b ab).
- by apply: (@continuous_subspaceT _ _ _ idfun) => x /=; exact: cvg_id.
- split.
  + by move=> x _; case: (dF x).
  + by move: (cF a); rewrite /continuous_at; exact: cvg_within_filter.
  + by move: (cF b); rewrite /continuous_at; exact: cvg_within_filter.
- by move=> x _; rewrite derive1E; case: (dF x) => _ ->.
have ba0 : b - a != 0 by rewrite gt_eqF// subr_gt0.
rewrite -EFinB -EFinM; congr (_%:E).
have -> : b ^+ 2 / 2 - a ^+ 2 / 2 = (b - a) * ((a + b) / 2) by ring.
by rewrite mulKf.
Qed.

(** E[Uniform(0,1)] = 1/2. *)
Lemma qbs_expect_uniform :
  qbs_expect (realQ R) qbs_uniform (fun x => x) = (2%:R^-1)%:E.
Proof. by rewrite qbs_expect_interval_uniform add0r div1r. Qed.

(** E[Normal(m,s)] = m. *)
Lemma qbs_expect_normal m s : s != 0 ->
  qbs_expect (realQ R) (qbs_normal_distribution m s) (fun x => x) = m%:E.
Proof.
move=> s0; rewrite /qbs_expect qbs_integral_mk /=.
  by apply: qbs_measurable_measQ; exact/measurable_EFinP/measurable_id.
exact: integral_normal_mean.
Qed.

End distribution_expectations.

End measure_as_qbs.

Arguments qbs_normal_distribution {R}.
