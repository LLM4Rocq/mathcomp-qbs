(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology boolp
  classical_sets borel_hierarchy numfun measure lebesgue_measure sequences
  lebesgue_integral hoelder probability lebesgue_stieltjes_measure charge.
From QBS Require Import quasi_borel.

(**md**************************************************************************)
(* # Probability Spaces on Quasi-Borel Spaces                                *)
(*                                                                            *)
(* Following "A Convenient Category for Higher-Order Probability Theory"      *)
(* Heunen, Kammar, Staton, Yang (LICS 2017), Section 4                       *)
(*                                                                            *)
(* Key constructions:                                                         *)
(* ```                                                                        *)
(*   qbs_prob X    == probability triples (alpha, mu) on a qbsType X         *)
(*   qbs_prob_equiv == equivalence of triples (same pushforward)              *)
(*   qbs_integral  == integration against a QBS probability                   *)
(*   qbs_law p     == the law of p, a probability on L X = qbs_meas X         *)
(* ```                                                                        *)
(* The probability monad itself is in qbs_monad.v.                            *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory
  order.Order.POrderTheory measurable_realfun
  charge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set SsrOldRewriteGoalsOrder.  (* TODO: port to the MathComp 2.6 goal order *)

Import MeasurableR.

Local Open Scope classical_set_scope.

Section probability_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

Implicit Types (X Y Z : qbsType R) (mu : probability mR R).

Section qbs_prob_basics.

(* 1. QBS Probability Triple
   A probability on a QBS X is a pair (alpha, mu) where
   alpha : R -> X is a random element (in Mx) and
   mu is a probability measure on R. *)

(** Probability triple on a QBS: a random element
    alpha and a base probability measure mu. *)
Record qbs_prob (X : qbsType R) := mkQBSProb {
  qbs_prob_alpha : mR -> X ;
  qbs_prob_mu : probability mR R ;
  qbs_prob_alpha_random : qbs_Mx (s := X) qbs_prob_alpha }.

(* 2. Equivalence of Probability Triples
   Two triples (alpha1, mu1) ~ (alpha2, mu2) iff they induce
   the same pushforward measure on X, i.e., for all measurable
   U in sigma_Mx(X),
   mu1(alpha1^{-1}(U)) = mu2(alpha2^{-1}(U)). *)

(** Equivalence of probability triples: same
    pushforward measure on sigma_Mx sets. *)
Definition qbs_prob_equiv (X : qbsType R) (p1 p2 : qbs_prob X) : Prop :=
  forall (U : set X),
    @sigma_Mx R X U ->
    qbs_prob_mu p1 (qbs_prob_alpha p1 @^-1` U) =
    qbs_prob_mu p2 (qbs_prob_alpha p2 @^-1` U).

Arguments qbs_prob_equiv : clear implicits.

Lemma qbs_prob_equivxx (X : qbsType R) (p : qbs_prob X) :
  qbs_prob_equiv X p p.
Proof. by []. Qed.

Lemma qbs_prob_equiv_sym (X : qbsType R) (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p1.
Proof. by move=> h U /h ->. Qed.

Lemma qbs_prob_equiv_trans (X : qbsType R) (p1 p2 p3 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p3 ->
  qbs_prob_equiv X p1 p3.
Proof. by move=> h12 h23 U hU; rewrite h12 // h23. Qed.

End qbs_prob_basics.

Arguments qbs_prob : clear implicits.
Arguments mkQBSProb {X}.
Arguments qbs_prob_equiv : clear implicits.

Section qbs_integration.

(* 7. Integration on QBS Probability Spaces *)

(** Integration of h : X -> \bar R against a QBS
    probability, via the base measure and alpha. *)
Definition qbs_integral (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x)))%E.

Arguments qbs_integral : clear implicits.

(* Sigma_Mx-measurability for functions h : X -> \bar R.
   h is sigma_Mx-measurable iff for every random element alpha
   in Mx(X), the composition h o alpha : R -> \bar R is Borel
   measurable. *)
Definition qbs_measurable (X : qbsType R) (h : X -> \bar R) : Prop :=
  forall alpha, qbs_Mx (s := X) alpha ->
    measurable_fun setT (fun r => h (alpha r)).

Arguments qbs_measurable : clear implicits.

(* If h is sigma_Mx-measurable, then preimages of
   measurable sets are in sigma_Mx. *)
Lemma qbs_measurable_sigma_Mx (X : qbsType R) (h : X -> \bar R)
  (hm : qbs_measurable X h) (V : set (\bar R)) :
  measurable V -> @sigma_Mx R X (h @^-1` V).
Proof.
move=> hV alpha halpha.
by have := hm alpha halpha measurableT V hV; rewrite setTI.
Qed.

(* When h is sigma_Mx-measurable, the pushforward measures
   through (h o alpha_i) agree on all measurable sets. *)
Lemma qbs_pushforward_agree (X : qbsType R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hequiv : qbs_prob_equiv X p1 p2) :
  forall (V : set (\bar R)), measurable V ->
    pushforward (qbs_prob_mu p1) (h \o qbs_prob_alpha p1) V =
    pushforward (qbs_prob_mu p2) (h \o qbs_prob_alpha p2) V.
Proof.
move=> V hV.
rewrite /pushforward /=.
have -> : (h \o qbs_prob_alpha p1) @^-1` V =
          qbs_prob_alpha p1 @^-1` (h @^-1` V) by [].
have -> : (h \o qbs_prob_alpha p2) @^-1` V =
          qbs_prob_alpha p2 @^-1` (h @^-1` V) by [].
apply: hequiv.
apply: (qbs_measurable_sigma_Mx hm).
exact: hV.
Qed.

(* Integration respects equivalence for sigma_Mx-measurable
   integrands. The proof factors through pushforward measures
   on \bar R and uses eq_measure_integral. *)
Lemma qbs_integral_equiv (X : qbsType R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint1 : (qbs_prob_mu p1).-integrable setT (h \o qbs_prob_alpha p1))
  (hint2 : (qbs_prob_mu p2).-integrable setT (h \o qbs_prob_alpha p2)) :
  qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof.
move=> hequiv.
rewrite /qbs_integral.
have hm1 := hm _ (qbs_prob_alpha_random p1).
have hm2 := hm _ (qbs_prob_alpha_random p2).
rewrite -(@integral_pushforward _ _ mR (\bar R : measurableType _) R
  (h \o qbs_prob_alpha p1) hm1
  (qbs_prob_mu p1) setT id
  (@measurable_id _ (\bar R) setT) hint1 measurableT).
rewrite -(@integral_pushforward _ _ mR (\bar R : measurableType _) R
  (h \o qbs_prob_alpha p2) hm2
  (qbs_prob_mu p2) setT id
  (@measurable_id _ (\bar R) setT) hint2 measurableT).
apply: (@eq_measure_integral _ _ _ setT
  (pushforward (qbs_prob_mu p2) (h \o qbs_prob_alpha p2))).
move=> A hA _.
apply: (qbs_pushforward_agree hm hequiv).
exact: hA.
Qed.

(* Simpler version: when both triples share the same random
   element and the base measures agree on all measurable sets. *)
Lemma qbs_integral_equiv_same_alpha (X : qbsType R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R) :
  qbs_prob_alpha p1 = qbs_prob_alpha p2 ->
  (forall A : set R, measurable A ->
    qbs_prob_mu p1 A = qbs_prob_mu p2 A) ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof.
move=> halpha hmu.
rewrite /qbs_integral halpha.
apply: (@eq_measure_integral _ _ _ setT (qbs_prob_mu p2)).
by move=> A hA _; apply: hmu.
Qed.

(* 7b. Pushforward integral infrastructure
   Since X is a QBS (not a measurableType), we compose with
   h : X -> \bar R to obtain pushforward mu (h o alpha). *)

(* The QBS integral equals the integral of id against the
   pushforward of mu through (h o alpha). *)
Lemma qbs_integral_as_pushforward (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint : (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p)) :
  qbs_integral X p h =
  (\int[pushforward (qbs_prob_mu p) (h \o qbs_prob_alpha p)]_y y)%E.
Proof.
rewrite /qbs_integral.
have hma := hm _ (qbs_prob_alpha_random p).
rewrite -(@integral_pushforward _ _ mR (\bar R : measurableType _) R
  (h \o qbs_prob_alpha p) hma
  (qbs_prob_mu p) setT id
  (@measurable_id _ (\bar R) setT) hint measurableT).
by [].
Qed.

(* Pushforward integrability: if h o alpha is mu-integrable,
   then id is integrable w.r.t. the pushforward measure. *)
Lemma qbs_pushforward_integrable (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint : (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p)) :
  (pushforward (qbs_prob_mu p) (h \o qbs_prob_alpha p)).-integrable setT id.
Proof.
have hma := hm _ (qbs_prob_alpha_random p).
exact: (integrable_pushforward hma
  (@measurable_id _ (\bar R) setT) hint measurableT).
Qed.


(** ** The law of a QBS probability on L X (HKSY l_X, eq. (3)) *)

Lemma qbs_measurableE (X : qbsType R) (h : X -> \bar R) :
  qbs_measurable X h <->
  measurable_fun [set: qbs_meas X] (h : qbs_meas X -> \bar R).
Proof. exact: (qbs_morphism_measurableP (M := \bar R)). Qed.

Definition qbs_prob_alpha_mfun (X : qbsType R) (p : qbs_prob X) :
    {mfun mR >-> qbs_meas X} :=
  mfun_Sub (mem_set (qbs_Mx_measurable (qbs_prob_alpha_random p))).

Definition qbs_law (X : qbsType R) (p : qbs_prob X) :
    probability (qbs_meas X) R :=
  distribution (qbs_prob_mu p) (qbs_prob_alpha_mfun p).

Lemma qbs_lawE (X : qbsType R) (p : qbs_prob X) (A : set X) :
  qbs_law p A = qbs_prob_mu p (qbs_prob_alpha p @^-1` A).
Proof. by []. Qed.

(** Equivalence of probabilities is equality of their laws. *)
Lemma qbs_prob_equivE (X : qbsType R) (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 <->
  (forall A : set (qbs_meas X), measurable A -> qbs_law p1 A = qbs_law p2 A).
Proof. by []. Qed.

Lemma ge0_qbs_integral_law (X : qbsType R) (p : qbs_prob X) (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, (0 <= h x)%E) ->
  qbs_integral X p h = (\int[qbs_law p]_x h x)%E.
Proof.
by move=> /qbs_measurableE mh h0; rewrite ge0_integral_distribution.
Qed.

Lemma qbs_integral_law (X : qbsType R) (p : qbs_prob X) (h : X -> \bar R) :
  qbs_measurable X h ->
  (qbs_prob_mu p).-integrable [set: mR] (h \o qbs_prob_alpha p) ->
  qbs_integral X p h = (\int[qbs_law p]_x h x)%E.
Proof. by move=> /qbs_measurableE mh ih; rewrite integral_distribution. Qed.

End qbs_integration.

Arguments qbs_integral : clear implicits.
Arguments qbs_measurable : clear implicits.

Section monad_operations.

(* 9. Expectation and probability of events *)

(** Expectation of a real-valued function h on a
    QBS probability, defined as qbs_integral of
    the extended-real embedding. *)
Definition qbs_expect (X : qbsType R) (p : qbs_prob X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Arguments qbs_expect : clear implicits.

Definition qbs_prob_event (X : qbsType R) (p : qbs_prob X)
  (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).

Arguments qbs_prob_event : clear implicits.

(* 10. Variance
   Defined via the mathcomp-analysis variance applied to
   f o alpha against the base measure mu. *)

(** Variance of f : X -> R under a QBS probability,
    via the base-measure variance of f o alpha. *)
Definition qbs_variance (X : qbsType R) (p : qbs_prob X)
  (f : X -> R) : \bar R :=
  variance (qbs_prob_mu p) (f \o qbs_prob_alpha p).

Arguments qbs_variance : clear implicits.

End monad_operations.

Arguments qbs_expect : clear implicits.
Arguments qbs_prob_event : clear implicits.
Arguments qbs_variance : clear implicits.

Section probability_inequalities.

Local Open Scope ereal_scope.

(* 15. QBS-level integrability predicate *)

(** Integrability of h : X -> \bar R under a QBS
    probability: h o alpha is mu-integrable. *)
Definition qbs_integrable (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :=
  (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p).

Arguments qbs_integrable : clear implicits.

(* 16. Integrability closure under arithmetic *)

Lemma qbs_integrableD (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integrable X p (f \+ g).
Proof. exact: integrableD. Qed.

Lemma qbs_integrableB (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integrable X p (f \- g).
Proof. exact: integrableB. Qed.

Lemma qbs_integrableN (X : qbsType R) (p : qbs_prob X)
    (f : X -> \bar R) :
  qbs_integrable X p f ->
  qbs_integrable X p (-%E \o f).
Proof. exact: integrableN. Qed.

Lemma qbs_integrableZl (X : qbsType R) (p : qbs_prob X)
    (k : R) (f : X -> \bar R) :
  qbs_integrable X p f ->
  qbs_integrable X p (fun x => k%:E * f x).
Proof. exact: integrableZl. Qed.

(* 17. Integral arithmetic *)

Lemma qbs_integralD (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integral X p (f \+ g) = qbs_integral X p f + qbs_integral X p g.
Proof. exact: integralD. Qed.

Lemma qbs_integralB (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integral X p (f \- g) = qbs_integral X p f - qbs_integral X p g.
Proof. exact: integralB. Qed.

Lemma qbs_integralZl (X : qbsType R) (p : qbs_prob X)
    (k : R) (f : X -> \bar R) :
  qbs_integrable X p f ->
  qbs_integral X p (fun x => k%:E * f x) =
  k%:E * qbs_integral X p f.
Proof. rewrite /qbs_integrable /qbs_integral => hf; exact: integralZl. Qed.

(* 18. Variance formulas *)

Lemma qbs_varianceE (X : qbsType R) (p : qbs_prob X) (h : X -> R) :
  h \o qbs_prob_alpha p \in Lfun (qbs_prob_mu p) 2 ->
  qbs_variance X p h =
  qbs_expect X p (fun x => h x ^+ 2)%R - (qbs_expect X p h) ^+ 2.
Proof.
move=> hL2; rewrite /qbs_variance /qbs_expect /qbs_integral.
by rewrite varianceE //; congr (_ - _); rewrite unlock.
Qed.

Lemma qbs_varianceZ (X : qbsType R) (p : qbs_prob X) (a : R)
    (h : X -> R) :
  h \o qbs_prob_alpha p \in Lfun (qbs_prob_mu p) 2 ->
  qbs_variance X p (a \o* h)%R =
  (a ^+ 2)%:E * qbs_variance X p h.
Proof.
move=> hL2; rewrite /qbs_variance.
have -> : ((a \o* h)%R \o qbs_prob_alpha p) =
          (a \o* (h \o qbs_prob_alpha p))%R.
  by apply: funext => r.
exact: varianceZ.
Qed.

(* 19. Markov inequality for QBS *)

(** Build a random variable from a measurable composition. *)
Definition qbs_rv (X : qbsType R) (p : qbs_prob X)
    (h : X -> R)
    (hm : measurable_fun setT (h \o qbs_prob_alpha p)) :
    {RV (qbs_prob_mu p) >-> R} :=
  HB.pack (h \o qbs_prob_alpha p)
    (@isMeasurableFun.phant_Build _ _ _ _
       (h \o qbs_prob_alpha p) hm).

(** Markov inequality lifted to QBS probabilities. *)
Lemma qbs_markov (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (f : R -> R) (eps : R)
    (hm : measurable_fun setT (h \o qbs_prob_alpha p))
    (heps : (0 < eps)%R)
    (hmf : measurable_fun [set: R] f)
    (hf0 : forall r, (0 <= r)%R -> (0 <= f r)%R)
    (hfnd : {in Num.nneg &, {homo f : x y / (x <= y)%R}}) :
  (f eps)%:E * qbs_prob_event X p [set x | eps%:E <= `|(h x)%:E|] <=
  qbs_integral X p (fun x => ((f \o normr \o h) x)%:E).
Proof.
rewrite /qbs_prob_event /qbs_integral /=.
pose rv : {RV (qbs_prob_mu p) >-> R} := qbs_rv hm.
have -> : qbs_prob_alpha p @^-1` [set x | eps%:E <= `|(h x)%:E|] =
          [set x | eps%:E <= `|(rv x)%:E|] by [].
have -> : (fun x => ((f \o normr \o h) (qbs_prob_alpha p x))%:E) =
          (fun x => ((f \o normr \o rv) x)%:E) by [].
have := @markov _ _ R (qbs_prob_mu p) rv f eps heps hmf hf0 hfnd.
suff -> : (\int[qbs_prob_mu p]_x (((f \o normr) \o rv) x)%:E)%E =
          'E_(qbs_prob_mu p)[((f \o [eta normr]) \o rv)] by [].
by rewrite unlock.
Qed.

(* 20. Chebyshev inequality for QBS *)

(** Chebyshev inequality lifted to QBS
    probabilities. *)
Lemma qbs_chebyshev (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (eps : R)
    (hm : measurable_fun setT (h \o qbs_prob_alpha p))
    (heps : (0 < eps)%R) :
  qbs_prob_mu p
    [set x | (eps <= `|h (qbs_prob_alpha p x) -
      fine (qbs_expect X p h)|)%R] <=
  (eps ^- 2)%:E * qbs_variance X p h.
Proof.
rewrite /qbs_variance /qbs_expect /qbs_integral.
pose rv : {RV (qbs_prob_mu p) >-> R} := qbs_rv hm.
have hE : (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x))%:E)%E =
          'E_(qbs_prob_mu p)[rv] by rewrite unlock.
rewrite hE.
have -> : (h \o qbs_prob_alpha p) = (rv : mR -> R) by [].
have -> : [set x | (eps <= `|h (qbs_prob_alpha p x) -
    fine 'E_(qbs_prob_mu p)[rv]|)%R] =
  [set x | (eps <= `|rv x - fine 'E_(qbs_prob_mu p)[rv]|)%R] by [].
exact: chebyshev.
Qed.

End probability_inequalities.

Arguments qbs_integrable : clear implicits.

(* Reopen ereal scope for the normalize_* sections below.
   The previous open was scoped to probability_inequalities and
   reset when that subsection closed. *)
Local Open Scope ereal_scope.

(* 21. General Normalizer: qbs_prob(X * R) -> option(qbs_prob(X))        *)
(*   normalize_mu p hw hw_m hpos hfin == reweighted probability measure  *)
(*   normalize_prob X p ...           == normalized qbs_prob on X        *)
(*   qbs_normalize X p hw hw_m        == option: Some if ev good, None   *)
(*   qbs_normalize_total              == normalized prob integrates to 1 *)
(*   qbs_normalize_integral           == E[g|norm] = E[g*w]/ev          *)

Section normalize_mu_build.
Variable X : qbsType R.
Variable p : qbs_prob (prodQ X (realQ R)).
Let w : mR -> R := fun r => snd (qbs_prob_alpha p r).
Hypothesis hw_ge0 : forall r, (0 <= w r)%R.
Hypothesis hw_meas : measurable_fun setT (fun r => (w r)%:E : \bar R).
Let ev : \bar R := (\int[qbs_prob_mu p]_r (w r)%:E)%E.
Hypothesis hev_pos : (0 < ev)%E.
Hypothesis hev_fin : (ev < +oo)%E.
Let ev_r : R := fine ev.
Let ev_r_gt0 : (0 < ev_r)%R.
Proof. by apply: fine_gt0; rewrite hev_pos hev_fin. Qed.
Let ev_r_neq0 : (ev_r != 0)%R.
Proof. exact: lt0r_neq0 ev_r_gt0. Qed.
Let wdiv (r : mR) : R := (w r / ev_r)%R.
Let wdiv_ge0 r : (0 <= wdiv r)%R.
Proof. by rewrite /wdiv divr_ge0 //= le0r ev_r_gt0 orbT. Qed.
Let wdiv_meas : measurable_fun setT (fun r => (wdiv r)%:E : \bar R).
Proof.
apply/measurable_EFinP; rewrite /wdiv; apply: measurable_funM.
  by move: hw_meas => /measurable_EFinP.
exact: measurable_cst.
Qed.
Let norm_mu (A : set mR) : \bar R :=
  (\int[qbs_prob_mu p]_(r in A) (wdiv r)%:E)%E.
Let norm_mu0 : norm_mu set0 = 0.
Proof. by rewrite /norm_mu integral_set0. Qed.
Let norm_mu_ge0 (A : set mR) : 0 <= norm_mu A.
Proof.
rewrite /norm_mu; apply: integral_ge0 => r _.
by rewrite lee_fin; exact: wdiv_ge0.
Qed.
Let norm_mu_sigma : semi_sigma_additive norm_mu.
Proof.
move=> F mF tF mUF; rewrite /norm_mu.
have hmfD : measurable_fun (\bigcup_n F n) (fun r => (wdiv r)%:E : \bar R).
  by apply/measurable_funTS; exact: wdiv_meas.
have hge0 : forall x, (\bigcup_n F n) x -> (0 <= (wdiv x)%:E)%E.
  by move=> x _; rewrite lee_fin; exact: wdiv_ge0.
rewrite (@ge0_integral_bigcup _ _ R (qbs_prob_mu p) F
  (fun r => (wdiv r)%:E) mF hmfD hge0 tF).
apply: is_cvg_ereal_nneg_natsum => n _.
apply: integral_ge0 => r _; rewrite lee_fin; exact: wdiv_ge0.
Qed.
HB.instance Definition _ := isMeasure.Build _ _ _
  norm_mu norm_mu0 norm_mu_ge0 norm_mu_sigma.
Let norm_mu_setT : norm_mu setT = 1.
Proof.
rewrite /norm_mu.
have -> : (fun r => (wdiv r)%:E) = (fun r => (ev_r^-1 * w r)%:E).
  by apply: funext => r; rewrite /wdiv mulrC.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin //=.
- have hfn : ev \is a fin_num by rewrite gt0_fin_numE.
  have -> : \int[qbs_prob_mu p]_x (w x)%:E = ev_r%:E by rewrite fineK.
  by rewrite -EFinM mulVf.
- by move=> r _; rewrite lee_fin.
- by rewrite invr_ge0 le0r ev_r_gt0 orbT.
Qed.
HB.instance Definition _ := Measure_isProbability.Build _ _ _
  norm_mu norm_mu_setT.
(** Reweighted probability measure: normalize the
    weight function w to integrate to 1. *)
Definition normalize_mu : probability mR R := norm_mu.
End normalize_mu_build.

Section qbs_normalize_def.
Variable X : qbsType R.

Lemma normalize_alpha_random (p : qbs_prob (prodQ X (realQ R))) :
  qbs_Mx (s := X) (fun r => fst (qbs_prob_alpha p r)).
Proof. by have /= [h1 _] := qbs_prob_alpha_random p. Qed.

(** Normalized QBS probability on X from a
    weighted triple on X * R. *)
Definition normalize_prob
    (p : qbs_prob (prodQ X (realQ R)))
    (hw_ge0 : forall r, (0 <= snd (qbs_prob_alpha p r))%R)
    (hw_meas : measurable_fun setT
      (fun r => (snd (qbs_prob_alpha p r))%:E : \bar R))
    (hev_pos : (0 < \int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E)%E)
    (hev_fin : (\int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E < +oo)%E) :
    qbs_prob X :=
  @mkQBSProb X
    (fun r => fst (qbs_prob_alpha p r))
    (normalize_mu hw_ge0 hw_meas hev_pos hev_fin)
    (normalize_alpha_random p).

(** Total normalizer: returns Some if the evidence
    is positive and finite, None otherwise. *)
Definition qbs_normalize
    (p : qbs_prob (prodQ X (realQ R)))
    (hw_ge0 : forall r, (0 <= snd (qbs_prob_alpha p r))%R)
    (hw_meas : measurable_fun setT
      (fun r => (snd (qbs_prob_alpha p r))%:E : \bar R)) :
    option (qbs_prob X) :=
  let ev := (\int[qbs_prob_mu p]_r
               (snd (qbs_prob_alpha p r))%:E)%E in
  match pselect (0 < ev)%E, pselect (ev < +oo)%E with
  | left hpos, left hfin =>
      Some (normalize_prob hw_ge0 hw_meas hpos hfin)
  | _, _ => None
  end.

Lemma qbs_normalize_alpha
    (p : qbs_prob (prodQ X (realQ R)))
    hw_ge0 hw_meas hev_pos hev_fin :
  qbs_prob_alpha (@normalize_prob p hw_ge0 hw_meas hev_pos hev_fin) =
  fun r => fst (qbs_prob_alpha p r).
Proof. by []. Qed.

Lemma qbs_normalize_total
    (p : qbs_prob (prodQ X (realQ R)))
    hw_ge0 hw_meas hev_pos hev_fin :
  qbs_integral X (@normalize_prob p hw_ge0 hw_meas hev_pos hev_fin)
    (fun _ => 1) = 1.
Proof.
rewrite /qbs_integral /=.
rewrite (_ : \int[_]__ 1 =
  1 * normalize_mu hw_ge0 hw_meas hev_pos hev_fin
    setT).
  by rewrite probability_setT mule1.
by rewrite -integral_cst.
Qed.

Lemma qbs_normalize_integral
    (p : qbs_prob (prodQ X (realQ R)))
    (hw_ge0 : forall r, (0 <= snd (qbs_prob_alpha p r))%R)
    (hw_meas : measurable_fun setT
      (fun r => (snd (qbs_prob_alpha p r))%:E : \bar R))
    (hev_pos : (0 < \int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E)%E)
    (hev_fin : (\int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E < +oo)%E)
    (g : X -> \bar R)
    (hg_ge0 : forall x, 0 <= g x)
    (hg_meas : qbs_measurable X g) :
  qbs_integral X (normalize_prob hw_ge0 hw_meas hev_pos hev_fin) g =
  (qbs_integral (prodQ X (realQ R)) p
    (fun xy => g (fst xy) * (snd xy)%:E) /
   \int[qbs_prob_mu p]_r (snd (qbs_prob_alpha p r))%:E)%E.
Proof.
rewrite /qbs_integral /=.
set ev := \int[qbs_prob_mu p]_r ((qbs_prob_alpha p r).2)%:E.
set mu := qbs_prob_mu p.
set alpha := qbs_prob_alpha p.
have hev_fin_num : ev \is a fin_num.
  by rewrite ge0_fin_numE; [exact: hev_fin | exact: ltW hev_pos].
have hwdiv_meas : measurable_fun setT
    (fun r : mR => (((alpha r).2 / fine ev)%:E : \bar R)).
  apply/measurable_EFinP; apply: measurable_funM.
  - by move: hw_meas => /measurable_EFinP.
  - exact: measurable_cst.
have hac :
  normalize_mu hw_ge0 hw_meas hev_pos hev_fin `<< mu.
  apply/null_content_dominatesP => A mA hA.
  rewrite /normalize_mu /=.
  by apply: null_set_integral => //;
     apply/measurable_funTS.
have hRN_wdiv : ae_eq mu setT
    (Radon_Nikodym_SigmaFinite.f
       (normalize_mu hw_ge0 hw_meas hev_pos hev_fin) mu)
    (fun r => (((alpha r).2 / fine ev)%:E : \bar R)).
  apply: integral_ae_eq.
  - exact: measurableT.
  - exact: Radon_Nikodym_SigmaFinite.f_integrable
      hac.
  - exact: hwdiv_meas.
  - move=> A _ mA.
    rewrite -(Radon_Nikodym_SigmaFinite.f_integral
      hac mA).
    by rewrite /normalize_mu /=.
have step1 :
  \int[normalize_mu hw_ge0 hw_meas hev_pos hev_fin]_r
    g ((alpha r).1) =
  \int[mu]_r
    (g ((alpha r).1) * (((alpha r).2 / fine ev)%:E)).
  rewrite -(Radon_Nikodym_SigmaFinite.change_of_variables
    hac _ measurableT
    (hg_meas _ (normalize_alpha_random p)));
    last by move=> x; exact: hg_ge0.
  apply: ge0_ae_eq_integral.
  - exact: measurableT.
  - apply: emeasurable_funM.
    + exact: hg_meas _ (normalize_alpha_random p).
    + have := Radon_Nikodym_SigmaFinite.f_integrable
        hac; by move=> /integrableP [? _].
  - apply: emeasurable_funM.
    + exact: hg_meas _ (normalize_alpha_random p).
    + exact: hwdiv_meas.
  - move=> r _; apply: mule_ge0; first exact: hg_ge0.
    exact: Radon_Nikodym_SigmaFinite.f_ge0.
  - move=> r _; apply: mule_ge0; first exact: hg_ge0.
    rewrite lee_fin; apply: divr_ge0; first exact: hw_ge0.
    by apply: fine_ge0; apply: integral_ge0 => x _;
       rewrite lee_fin; exact: hw_ge0.
  - by apply: filterS hRN_wdiv => r /= ->.
rewrite step1.
have hfine_ev_pos : (0 < fine ev)%R.
  by apply: fine_gt0; rewrite hev_pos hev_fin.
have hfine_ev_ne0 : fine ev != 0%R :=
  lt0r_neq0 hfine_ev_pos.
have hev_inv : ev^-1 = ((fine ev)^-1)%:E.
  by rewrite -{1}(fineK hev_fin_num) inver ifF //;
     exact: negbTE hfine_ev_ne0.
under eq_integral => r _ do rewrite EFinM muleA.
rewrite ge0_integralZr.
- by rewrite -hev_inv.
- exact: measurableT.
- exact: emeasurable_funM (hg_meas _ (normalize_alpha_random p)) hw_meas.
- move=> r _; apply: mule_ge0; first exact: hg_ge0.
  by rewrite lee_fin; exact: hw_ge0.
- rewrite lee_fin invr_ge0; exact: ltW hfine_ev_pos.
Qed.

End qbs_normalize_def.

Arguments qbs_normalize : clear implicits.
Arguments normalize_prob : clear implicits.

End probability_qbs.

Arguments qbs_prob {R}.
Arguments mkQBSProb {R X}.
Arguments qbs_prob_alpha {R X}.
Arguments qbs_prob_mu {R X}.
Arguments qbs_prob_alpha_random {R X}.
Arguments qbs_prob_equiv {R}.
Arguments qbs_integral {R}.
Arguments qbs_measurable {R}.
Arguments qbs_expect {R}.
Arguments qbs_prob_event {R}.
Arguments qbs_variance {R}.
Arguments qbs_integrable {R}.
Arguments qbs_normalize {R}.
Arguments normalize_prob {R}.
