(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra reals ereal topology
  classical_sets
  normedtype sequences numfun measure measurable_realfun lebesgue_measure
  lebesgue_integral probability exp trigo boolp.
From mathcomp.algebra_tactics Require Import ring.
From QBS Require Import quasi_borel probability_qbs qbs_monad qbs_normalize
  measure_as_qbs_measure.

(**md**************************************************************************)
(* # Bayesian linear regression (HKSY Sec. VI, Isabelle AFP example)          *)
(*                                                                            *)
(* Model: y = s * x + b + noise, noise ~ N(0, 1/2), s, b ~ N(0, 3).           *)
(* Data: (1, 2.5), (2, 3.8), (3, 4.5), (4, 6.2), (5, 8.0).                    *)
(* The prior is a probability on the function space R => R, the program is    *)
(* norm (P(id, obs) prior), and the posterior is computed in closed form.     *)
(*                                                                            *)
(* ```                                                                        *)
(*                nu == the normal distribution N(0,3) as a monadP RQ         *)
(*             prior2 == the parameter prior N(0,3) x N(0,3) on pairs (s, b)  *)
(*       lin_uncurried == ((s, b), r) |-> s * r + b, as a QBS morphism        *)
(*          lin (s,b) == the function r |-> s * r + b, as a morphism into     *)
(*                       R => R                                               *)
(*              prior == the prior on R => R, pushforward of prior2 by lin    *)
(*            obs_fun == likelihood of the data for a regression function     *)
(*                obs == obs_fun as a QBS morphism R => R -> R                *)
(*             wprior == the weighted prior P(id, obs) prior                  *)
(*            program == norm wprior : option (qbs_prob (R => R))             *)
(*     evidence_const == closed-form value of the evidence of wprior          *)
(*  post_s_mean, post_s_var == mean and variance of s in the posterior        *)
(*  post_b_mean s, post_b_var == mean (a function of s) and variance of b     *)
(*                       given s in the posterior                             *)
(*       post_b_meanQ == post_b_mean as a QBS morphism RQ -> RQ               *)
(*          posterior2 == explicit Gaussian posterior on pairs (s, b)         *)
(*          posterior == its pushforward by lin, the posterior on R => R      *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results: wprior_evidence (the evidence is the closed-form constant    *)
(* evidence_const) and program_posterior (program = Some posterior).          *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section regression.
Variable R : realType.
Local Abbreviation mR := (measurableTypeR R).
Local Abbreviation RQ := (realQ R).
Local Abbreviation W := (prodQ RQ RQ).
Local Abbreviation F := (expQ RQ RQ).

(** ** Model *)

Let half_neq0 : (2^-1 : R) != 0. Proof. by rewrite invr_eq0 pnatr_eq0. Qed.

Definition nu : monadP RQ := qbs_normal_distribution 0 3.

(** The parameter prior N(0,3) x N(0,3), as a monadic product. *)
Definition prior2 : monadP W := monadP_pair nu nu.

(** (s, b) |-> (r |-> s * r + b). *)
Definition lin_uncurried : qbsHomType (prodQ W RQ) RQ :=
  qbs_comp (qbs_pair
    (qbs_comp (qbs_pair (qbs_comp (qbs_fst W RQ) (qbs_fst RQ RQ))
      (qbs_snd W RQ)) (qbs_mul R))
    (qbs_comp (qbs_fst W RQ) (qbs_snd RQ RQ))) (qbs_add R).

Definition lin : qbsHomType W F := qbs_curry_morph lin_uncurried.

Lemma linE (s b r : R) : lin (s, b) r = s * r + b.
Proof. by []. Qed.

(** The prior on functions (HKSY eq. (5)). *)
Definition prior : monadP F := monadP_map lin prior2.

Let d (m x : R) : R := normal_pdf m (2^-1) x.

(** Likelihood of the data for a regression function f. *)
Definition obs_fun (f : F) : R :=
  d (f 1) (5 / 2) * d (f 2) (19 / 5) * d (f 3) (9 / 2) *
  d (f 4) (31 / 5) * d (f 5) 8.

Let measurable_d (y : R) :
    measurable_fun [set: mR] (fun m : mR => d m y).
Proof.
have -> : (fun m => d m y) = normal_pdf y (2^-1).
  by apply/funext => m; rewrite /d normal_pdf_sym.
exact: measurable_normal_pdf.
Qed.

Lemma obs_morphism : qbs_morphism (X := F) (Y := RQ) obs_fun.
Proof.
move=> a ha.
have mev (c : R) : measurable_fun [set: mR] (fun r => (a r : RQ -> RQ) c).
  apply: (ha (fun r => (r, c))); split; first exact: measurable_id.
  exact: measurable_cst.
by repeat apply: measurable_funM;
  apply: measurableT_comp (measurable_d _) (mev _).
Qed.

Definition obs : qbsHomType F RQ :=
  HB.pack obs_fun (isQBSMorphism.Build R F RQ _ obs_morphism).

(** The weighted prior P(id, obs)(prior) and the program. *)
Definition wprior : monadP (prodQ F RQ) :=
  monadP_map (qbs_pair (qbs_id F) obs) prior.

Definition program : option (qbs_prob F) := qbs_normalize wprior.

(** ** The posterior in closed form *)

Definition evidence_const : R :=
  4 * sqrtr 2 / (pi ^+ 2 * sqrtr (29 * 2309 * pi)) *
  expR (- (11 * 11 * (138 * 100 + 41) / (25 * 29 * 2309))).
Definition post_s_mean : R := 8 * 9 * 7 * 19 * 47 / (5 * 29 * 2309).
Definition post_s_var : R := 9 * 181 / (29 * 2309).
Definition post_b_mean (s : R) : R := (900 - 540 * s) / 181.
Definition post_b_var : R := 9 / 181.

Let post_s_var_gt0 : 0 < post_s_var.
Proof. by rewrite /post_s_var divr_gt0 // ?mulr_gt0 // ltr0n. Qed.

Let post_b_var_gt0 : 0 < post_b_var.
Proof. by rewrite /post_b_var divr_gt0 // ltr0n. Qed.

Let obs2 (s b : R) : R := obs_fun (lin (s, b)).

Let expoE s b :
  - (s - 0) ^+ 2 / (3 ^+ 2 *+ 2) + - (b - 0) ^+ 2 / (3 ^+ 2 *+ 2) +
  - (5 / 2 - (s * 1 + b)) ^+ 2 / (2^-1 ^+ 2 *+ 2) +
  - (19 / 5 - (s * 2 + b)) ^+ 2 / (2^-1 ^+ 2 *+ 2) +
  - (9 / 2 - (s * 3 + b)) ^+ 2 / (2^-1 ^+ 2 *+ 2) +
  - (31 / 5 - (s * 4 + b)) ^+ 2 / (2^-1 ^+ 2 *+ 2) +
  - (8 - (s * 5 + b)) ^+ 2 / (2^-1 ^+ 2 *+ 2) =
  - (11 * 11 * (138 * 100 + 41) / (25 * 29 * 2309)) +
  - (s - post_s_mean) ^+ 2 / (post_s_var *+ 2) +
  - (b - post_b_mean s) ^+ 2 / (post_b_var *+ 2) :> R.
Proof.
rewrite /post_s_mean /post_b_mean /post_s_var /post_b_var.
by field.
Qed.

Let peakE :
  normal_peak 3 ^+ 2 * normal_peak 2^-1 ^+ 5 =
  4 * sqrtr 2 / (pi ^+ 2 * sqrtr (29 * 2309 * pi)) *
  normal_peak (sqrtr post_s_var) * normal_peak (sqrtr post_b_var) :> R.
Proof.
have pi0 : 0 < pi :> R := pi_gt0.
have vs0 := post_s_var_gt0; have vb0 := post_b_var_gt0.
apply/eqP; rewrite -(eqrXn2 (n := 2)) //.
- by rewrite mulr_ge0 ?exprn_ge0 ?normal_peak_ge0.
- by rewrite !mulr_ge0 ?normal_peak_ge0 ?invr_ge0 ?mulr_ge0 ?sqrtr_ge0
    ?exprn_ge0 ?ltW.
have pk2 x : 0 <= x ^+ 2 * pi *+ 2 ->
    normal_peak x ^+ 2 = (x ^+ 2 * pi *+ 2)^-1.
  by move=> x0; rewrite /normal_peak exprVn sqr_sqrtr.
rewrite !exprMn !pk2 ?mulrn_wge0 ?mulr_ge0 ?sqr_ge0 ?ltW //.
all: try by rewrite ?sqrtr_gt0 ?invr_gt0.
rewrite !sqr_sqrtr ?ltW //.
rewrite (exprVn (pi ^+ 2 * _)) exprMn sqr_sqrtr ?mulr_ge0 ?ler0n ?ltW //.
rewrite /post_s_var /post_b_var.
move: pi0; move: (pi : R) => p p0.
by apply/eqP; field; rewrite lt0r_neq0.
Qed.

(** Completing the square: prior times likelihood is evidence_const times the
    posterior density. *)
Lemma obs_prior_factor s b :
  normal_pdf 0 3 s * normal_pdf 0 3 b * obs2 s b =
  evidence_const * normal_pdf post_s_mean (sqrtr post_s_var) s *
      normal_pdf (post_b_mean s) (sqrtr post_b_var) b.
Proof.
have h3 : (3 : R) != 0 by rewrite pnatr_eq0.
have vs0 := post_s_var_gt0; have vb0 := post_b_var_gt0.
have hvs : sqrtr post_s_var != 0 by rewrite sqrtr_eq0 -ltNge post_s_var_gt0.
have hvb : sqrtr post_b_var != 0 by rewrite sqrtr_eq0 -ltNge post_b_var_gt0.
rewrite /obs2 /obs_fun !linE /d /evidence_const !(normal_pdfE _ half_neq0)
  !(normal_pdfE _ h3)
  (normal_pdfE _ hvs) (normal_pdfE _ hvb) /normal_fun !sqr_sqrtr ?ltW //.
have HE := congr1 expR (expoE s b); rewrite !expRD in HE.
move: (peakE); move: (normal_peak _) => P3; move: (normal_peak 2^-1) => Ph.
move=> HP.
set e1 := expR (- (s - 0) ^+ 2 / _); set e2 := expR (- (b - 0) ^+ 2 / _).
set e3 := expR (- (5 / 2 - _) ^+ 2 / _).
set e4 := expR (- (19 / 5 - _) ^+ 2 / _).
set e5 := expR (- (9 / 2 - _) ^+ 2 / _).
set e6 := expR (- (31 / 5 - _) ^+ 2 / _).
set e7 := expR (- (8 - _) ^+ 2 / _).
transitivity ((P3 ^+ 2 * Ph ^+ 5) * (e1 * e2 * e3 * e4 * e5 * e6 * e7)).
  by ring.
by rewrite HP HE; ring.
Qed.

(** The posterior: s ~ N(post_s_mean, sqrt post_s_var), and given s,
    b ~ N(post_b_mean s, sqrt post_b_var); pushed to functions by lin. *)
Let post_b_mean_morphism : qbs_morphism (X := RQ) (Y := RQ) post_b_mean.
Proof.
move=> a ha; apply: measurable_funM => //; apply: measurable_funB => //.
exact: measurable_funM.
Qed.

Definition post_b_meanQ : qbsHomType RQ RQ :=
  HB.pack post_b_mean (isQBSMorphism.Build R RQ RQ _ post_b_mean_morphism).

Definition posterior2 : monadP W :=
  qbs_bind
    (qbs_normal_distribution post_s_mean (sqrtr post_s_var))
    (qbs_comp (qbs_pair (qbs_id RQ)
      (qbs_comp post_b_meanQ (qbs_normalQ (sqrtr post_b_var))))
      (qbs_strengthQ RQ RQ)).

Definition posterior : monadP F := monadP_map lin posterior2.

(** ** Integrals against the prior and the posterior *)

Local Open Scope ereal_scope.

Lemma prior2_integral (h : W -> \bar R) :
  qbs_measurable W h -> (forall x, 0 <= h x) ->
  qbs_integral W prior2 h =
  \int[normal_prob 0 3]_s \int[normal_prob 0 3]_b h (s, b).
Proof.
move=> mh h0; rewrite ge0_qbs_integral_bind// qbs_integral_normal.
  exact: ge0_qbs_measurable_integral.
apply: eq_integral => s _.
rewrite /= qbs_strength_integral// qbs_integral_normal//.
by move=> a ha; exact: mh _ (qbs_Mx_pair_cstl s ha).
Qed.

Lemma posterior2_integral (h : W -> \bar R) :
  qbs_measurable W h -> (forall x, 0 <= h x) ->
  qbs_integral W posterior2 h =
  \int[normal_prob post_s_mean (sqrtr post_s_var)]_s
    \int[normal_prob (post_b_mean s) (sqrtr post_b_var)]_b h (s, b).
Proof.
move=> mh h0; rewrite ge0_qbs_integral_bind// qbs_integral_normal.
  exact: ge0_qbs_measurable_integral.
apply: eq_integral => s _.
rewrite /= qbs_strength_integral// qbs_integral_normal//.
by move=> a ha; exact: mh _ (qbs_Mx_pair_cstl s ha).
Qed.

(** Helpers. *)

Let K : R := normal_peak 2^-1 ^+ 5.

Let obs2_ge0 s b : (0 <= obs2 s b)%R.
Proof. by rewrite /obs2 /obs_fun /d !mulr_ge0 ?normal_pdf_ge0. Qed.

Let obs2_ub s b : (obs2 s b <= K)%R.
Proof.
rewrite /obs2 /obs_fun /d /K !exprS expr0 mulr1.
have ub (x m : R) : (normal_pdf m 2^-1 x <= normal_peak 2^-1)%R.
  exact: normal_pdf_ub half_neq0.
have g0 (x m : R) : (0 <= normal_pdf m 2^-1 x)%R.
  exact: normal_pdf_ge0.
by rewrite -!mulrA; repeat apply: ler_pM;
  rewrite ?mulr_ge0 ?g0 ?ub ?normal_peak_ge0.
Qed.

Let obs2Q : qbsHomType W RQ := qbs_comp lin obs.

Let measurable_obs2 : qbs_measurable W (fun sb => (obs2 sb.1 sb.2)%:E).
Proof.
move=> a ha; apply/measurable_EFinP.
exact: (qbs_hom_proof (s := obs2Q) _ ha).
Qed.

Let qbs_Mx_pair_cst (s : R) : qbs_Mx (s := W) (fun b : mR => (s, b)).
Proof. by split; [exact: measurable_cst|exact: measurable_id]. Qed.

Let measurable_mul_obs2 (h : W -> \bar R) :
  qbs_measurable W h ->
  qbs_measurable W (fun sb => h sb * (obs2 sb.1 sb.2)%:E).
Proof.
by move=> mh a ha; apply: emeasurable_funM; [exact: mh|exact: measurable_obs2].
Qed.

Let mul_obs2_ge0 (h : W -> \bar R) :
  (forall x, 0 <= h x) -> forall sb, 0 <= h sb * (obs2 sb.1 sb.2)%:E.
Proof. by move=> h0 sb; rewrite mule_ge0 ?lee_fin ?obs2_ge0. Qed.

Let integral_normal_prob_cst1 (m s : R) :
  \int[normal_prob m s]_x (fun=> 1 : \bar R) x = 1.
Proof. by rewrite integral_cst //= probability_setT mule1. Qed.

Let ge0_of_le1 (T : Type) (h : T -> \bar R) :
  (forall x, 0 <= h x <= 1) -> forall x, 0 <= h x.
Proof. by move=> h01 x; case/andP: (h01 x). Qed.

Let integral_normal_prob_bnd (m s M : R) (f : mR -> \bar R) :
  measurable_fun [set: mR] f -> (forall x, 0 <= f x <= M%:E) ->
  0 <= \int[normal_prob m s]_x f x <= M%:E.
Proof.
move=> mf fM; apply/andP; split.
  by apply: integral_ge0 => x _; case/andP: (fM x).
rewrite (le_trans _ (y := \int[normal_prob m s]_x M%:E))//.
  by apply: ge0_le_integral => // x _; case/andP: (fM x).
by rewrite integral_cst //= probability_setT mule1.
Qed.

Let integral_normal_prob_bounded (m s : R) (f : mR -> \bar R) (M : R) :
  measurable_fun [set: mR] f -> (forall x, 0 <= f x <= M%:E) ->
  \int[normal_prob m s]_x f x =
  \int[lebesgue_measure]_x (f x * (normal_pdf m s x)%:E).
Proof.
move=> mf fM; apply: integral_normal_prob => //.
apply: emeasurable_bounded_integrable => //.
  by move=> x; have /andP[] := fM x.
by exists M => x; have /andP[] := fM x.
Qed.

(** s |-> \int[N(m s, sigma)]_b h (s, b) is measurable. *)
Let measurable_normal_prob_integral (m : qbsHomType RQ RQ) (sigma : R)
    (h : W -> \bar R) :
  qbs_measurable W h -> (forall x, 0 <= h x) ->
  measurable_fun [set: mR]
    (fun s : mR => \int[normal_prob (m s) sigma]_b h (s, b)).
Proof.
move=> mh h0.
pose g := qbs_comp (qbs_pair (qbs_id RQ) (qbs_comp m (qbs_normalQ sigma)))
  (qbs_strengthQ RQ RQ).
have := ge0_qbs_measurable_integral g mh h0 (@measurable_id _ mR setT).
apply: eq_measurable_fun => s _ /=.
rewrite qbs_strength_integral// qbs_integral_normal//.
by move=> a ha; exact: mh _ (qbs_Mx_pair_cstl (s : RQ) ha).
Qed.

Let evidence_const_gt0 : (0 < evidence_const)%R.
Proof.
rewrite /evidence_const mulr_gt0 ?expR_gt0//.
rewrite divr_gt0 ?mulr_gt0 ?sqrtr_gt0 ?exprn_gt0 ?pi_gt0 ?ltr0n //.
all: by rewrite ?mulr_gt0 ?ltr0n ?pi_gt0.
Qed.

Let evidence_const_ge0 : (0 <= evidence_const)%R.
Proof. exact: ltW evidence_const_gt0. Qed.

Let factor_inner (h : W -> \bar R) (s : R) :
  qbs_measurable W h -> (forall x, 0 <= h x <= 1) ->
  (\int[normal_prob 0 3]_b (h (s, b) * (obs2 s b)%:E)) * (normal_pdf 0 3 s)%:E =
  (evidence_const * normal_pdf post_s_mean (sqrtr post_s_var) s)%:E *
  \int[normal_prob (post_b_mean s) (sqrtr post_b_var)]_b h (s, b).
Proof.
move=> mh h01; have h0 := ge0_of_le1 h01.
have h1 x : h x <= 1 by case/andP: (h01 x).
have hs := qbs_Mx_pair_cst s.
have mhb : measurable_fun [set: mR] (fun b => h (s, b)) := mh _ hs.
have mob : measurable_fun [set: mR] (fun b => obs2 s b) :=
  qbs_hom_proof (s := obs2Q) _ hs.
have mho : measurable_fun [set: mR] (fun b => h (s, b) * (obs2 s b)%:E).
  by apply: emeasurable_funM => //; exact/measurable_EFinP.
have bho b : 0 <= h (s, b) * (obs2 s b)%:E <= K%:E.
  rewrite mule_ge0 ?lee_fin ?obs2_ge0//=.
  by rewrite -[K%:E]mul1e lee_pmul ?lee_fin ?obs2_ge0 ?obs2_ub.
rewrite (integral_normal_prob_bounded _ _ mho bho).
rewrite [X in _ = _ * X]
  (integral_normal_prob_bounded _ _ mhb (fun b => h01 (s, b))).
have mf1 : measurable_fun [set: mR]
    (fun x => h (s, x) * (obs2 s x)%:E * (normal_pdf 0 3 x)%:E).
  apply: emeasurable_funM.
    by apply: emeasurable_funM => //; exact/measurable_EFinP.
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
have mf2 : measurable_fun [set: mR] (fun x =>
    h (s, x) * (normal_pdf (post_b_mean s) (sqrtr post_b_var) x)%:E).
  apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
have nn1 x : [set: mR] x ->
    0 <= h (s, x) * (obs2 s x)%:E * (normal_pdf 0 3 x)%:E.
  by move=> _; rewrite !mule_ge0 ?lee_fin ?normal_pdf_ge0 ?obs2_ge0.
have nn2 x : [set: mR] x ->
    0 <= h (s, x) * (normal_pdf (post_b_mean s) (sqrtr post_b_var) x)%:E.
  by move=> _; rewrite !mule_ge0 ?lee_fin ?normal_pdf_ge0.
rewrite -(ge0_integralZr _ measurableT mf1 nn1);
  first by rewrite lee_fin normal_pdf_ge0.
rewrite -(ge0_integralZl _ measurableT mf2 nn2);
  first by rewrite lee_fin mulr_ge0 ?evidence_const_ge0 ?normal_pdf_ge0.
apply: eq_integral => b _; have e := obs_prior_factor s b.
rewrite -!muleA -!EFinM [RHS]muleCA -EFinM; congr (h (s, b) * _%:E).
by rewrite -e; ring.
Qed.

Lemma factor_integral (h : W -> \bar R) :
  qbs_measurable W h -> (forall x, 0 <= h x <= 1) ->
  \int[normal_prob 0 3]_s \int[normal_prob 0 3]_b (h (s, b) * (obs2 s b)%:E) =
  evidence_const%:E * \int[normal_prob post_s_mean (sqrtr post_s_var)]_s
    \int[normal_prob (post_b_mean s) (sqrtr post_b_var)]_b h (s, b).
Proof.
move=> mh h01; have h0 := ge0_of_le1 h01.
pose ho (sb : W) := h sb * (obs2 sb.1 sb.2)%:E.
have mho : qbs_measurable W ho := measurable_mul_obs2 mh.
have ho0 : forall x, 0 <= ho x := mul_obs2_ge0 h0.
have mG := measurable_normal_prob_integral (@qbs_const _ RQ RQ 0%R) 3 mho ho0.
have mJ :=
  measurable_normal_prob_integral post_b_meanQ (sqrtr post_b_var) mh h0.
have bG s : 0 <= \int[normal_prob 0 3]_b ho (s, b) <= K%:E.
  apply: integral_normal_prob_bnd => [|b].
    exact: mho _ (qbs_Mx_pair_cst s).
  by rewrite ho0 /ho -[K%:E]mul1e lee_pmul ?lee_fin ?obs2_ge0 ?obs2_ub//;
    case/andP: (h01 (s, b)).
have bJ s : 0 <= \int[normal_prob (post_b_mean s) (sqrtr post_b_var)]_b
    h (s, b) <= 1%:E.
  by apply: integral_normal_prob_bnd => //; exact: mh _ (qbs_Mx_pair_cst s).
rewrite -[LHS]/(\int[normal_prob 0 3]_s \int[normal_prob 0 3]_b ho (s, b)).
rewrite (integral_normal_prob_bounded _ _ mG bG)
  (integral_normal_prob_bounded _ _ mJ bJ).
rewrite -ge0_integralZl//.
- apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
- by move=> x _; rewrite mule_ge0 ?lee_fin ?normal_pdf_ge0//; case/andP: (bJ x).
- apply: eq_integral => s _.
  by rewrite (factor_inner s mh h01) muleCA -EFinM muleC.
Qed.

Lemma wprior_evidence : qbs_evidence wprior = evidence_const%:E.
Proof.
have mw0 := @qbs_measurable_weight R F.
have mw := qbs_measurable_comp (qbs_pair (qbs_id F) obs) mw0.
rewrite /qbs_evidence.
rewrite !monadP_map_integral//.
rewrite -[LHS]/(qbs_integral W prior2 (fun sb => (maxr 0 (obs2 sb.1 sb.2))%:E)).
have -> : (fun sb : W => (maxr 0 (obs2 sb.1 sb.2))%:E) =
    (fun sb => 1 * (obs2 sb.1 sb.2)%:E).
  by apply/funext => sb; rewrite mul1e max_r ?obs2_ge0.
rewrite prior2_integral.
- exact: (measurable_mul_obs2 (h := fun=> 1)) (fun _ _ => measurable_cst _).
- exact: (mul_obs2_ge0 (h := fun=> 1)) (fun _ => lee01).
rewrite (factor_integral (h := fun=> 1)).
- by move=> ? ?; exact: measurable_cst.
- by move=> _; rewrite lee01 lexx.
by under eq_integral do rewrite integral_normal_prob_cst1;
  rewrite integral_normal_prob_cst1 mule1.
Qed.

(** ** Main theorem: the program normalises to the closed-form posterior *)

Theorem program_posterior : program = Some posterior.
Proof.
have ev : 0 < qbs_evidence wprior < +oo.
  by rewrite wprior_evidence ltry lte_fin evidence_const_gt0.
rewrite /program /qbs_normalize ev; congr Some; apply/qbs_prob_eqP => U mU.
pose V := lin @^-1` U.
have mV : sigma_Mx V := sigma_Mx_preimage lin mU.
pose h (sb : W) : \bar R := (\1_V sb)%:E.
have mh : qbs_measurable W h.
  by move=> a ha; apply/measurable_EFinP/measurable_indic; exact: mV.
have h01 x : 0 <= h x <= 1.
  by rewrite /h indicE; case: (_ \in _); rewrite ?lee01 ?lexx.
have mw := qbs_measurable_weighted_indic mU.
have mw' := qbs_measurable_comp (qbs_pair (qbs_id F) obs) mw.
rewrite qbs_normalize_event// wprior_evidence monadP_map_event//.
rewrite qbs_prob_event_integral// !monadP_map_integral//.
have -> : (fun x : W => (x \in V)%:R%:E) = h.
  by apply/funext => x; rewrite /h indicE.
have -> : qbs_integral W prior2
    ((fun xw : prodQ F RQ => (\1_U xw.1 * maxr 0 xw.2)%:E) \o
      qbs_pair (qbs_id F) obs \o lin) =
    qbs_integral W prior2 (fun sb => h sb * (obs2 sb.1 sb.2)%:E).
  by apply: eq_integral => r _; rewrite /h /= max_r ?obs2_ge0// EFinM.
rewrite prior2_integral; first exact: measurable_mul_obs2 mh.
  exact: mul_obs2_ge0 (ge0_of_le1 h01).
rewrite factor_integral// posterior2_integral//; first exact: ge0_of_le1 h01.
by rewrite /= muleAC -EFinM divff ?gt_eqF ?evidence_const_gt0// mul1e.
Qed.

End regression.
