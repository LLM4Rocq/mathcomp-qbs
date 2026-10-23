(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology boolp
  classical_sets borel_hierarchy numfun measure lebesgue_measure sequences
  lebesgue_integral hoelder probability lebesgue_stieltjes_measure charge.
From mathcomp.algebra_tactics Require Import ring.
From QBS Require Import quasi_borel.

(**md**************************************************************************)
(* # Probability Spaces on Quasi-Borel Spaces                                 *)
(*                                                                            *)
(* Following "A Convenient Category for Higher-Order Probability Theory"      *)
(* Heunen, Kammar, Staton, Yang (LICS 2017), Section 4                        *)
(*                                                                            *)
(* Key constructions:                                                         *)
(* ```                                                                        *)
(*   qbs_prob X    == probability triples (alpha, mu) on a qbsType X          *)
(*   qbs_prob_equiv == equivalence of triples (same pushforward)              *)
(*   qbs_integral  == integration against a QBS probability                   *)
(*   qbs_law p     == the law of p, a probability on L X = qbs_meas X         *)
(*   qbs_integrable X p h == h o alpha is mu-integrable                       *)
(*   qbs_integrableP      == for sigma_Mx-measurable h: integrable iff the    *)
(*                           integral of |h| is finite                        *)
(*   qbs_integrable_abseP, qbs_integrableMr, qbs_integrable_bounded,          *)
(*   qbs_integrable_sqrB  == integrability of |h|, of bounded factors, of     *)
(*                           bounded functions, of squared deviations         *)
(*   qbs_integral_cst, qbs_integral_le, ge0_qbs_integral_le == integral of a  *)
(*                           constant and monotonicity of the integral        *)
(*   qbs_integralE        == the integral is the difference of the integrals  *)
(*                           of the positive and negative parts               *)
(*   qbs_integrable_equiv, qbs_variance_equiv == equivalent probabilities     *)
(*                           agree on integrability and variance              *)
(*   qbs_variance_affine  == Var(a * h + b) = a^2 * Var(h)                    *)
(* ```                                                                        *)
(* The probability monad itself is in qbs_monad.v.                            *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory
  order.Order.POrderTheory measurable_realfun
  charge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import MeasurableR.

Local Open Scope classical_set_scope.

Section probability_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

Implicit Types (X Y Z : qbsType R) (mu : probability mR R).

(** Not (yet) in mathcomp-analysis. *)
Lemma measurable_invr : measurable_fun [set: mR] (@GRing.inv R).
Proof.
rewrite -(setUv [set (0 : mR)%R]); apply/measurable_funU => //.
  exact: measurableC.
split; first exact: measurable_fun_set1.
apply: open_continuous_measurable_fun.
  by apply/closed_openC/accessible_closed_set1; exact: hausdorff_accessible.
by move=> x /[!inE] /eqP x0; exact: normed_module.inv_continuous.
Qed.


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

Section ge0_integral_sigma_Mx.
Local Open Scope ereal_scope.

(** Integrals of nonnegative sigma_Mx-measurable functions only depend on
    the measures of the preimages of sigma_Mx sets. *)
Lemma ge0_integral_sigma_Mx X (a1 a2 : mR -> X)
    (m1 m2 : {measure set mR -> \bar R}%R) (k : X -> \bar R) :
  qbs_Mx a1 -> qbs_Mx a2 -> qbs_measurable X k -> (forall x, 0 <= k x) ->
  (forall U, sigma_Mx U -> m1 (a1 @^-1` U) = m2 (a2 @^-1` U)) ->
  \int[m1]_r k (a1 r) = \int[m2]_r k (a2 r).
Proof.
move=> ha1 ha2 mk k0 m12.
have mk1 := mk _ ha1; have mk2 := mk _ ha2.
have pre (a : mR -> X) : (k \o a) @^-1` `[0%E, +oo]%classic = [set: mR].
  by apply/seteqP; split => // r _; rewrite /= in_itv /= k0 leey.
have Pge0 : {in `[0%E, +oo]%classic, forall y : \bar R, 0 <= y}.
  by move=> y; rewrite inE /= in_itv /= => /andP[].
transitivity (\int[pushforward m1 (k \o a1)]_(y in `[0%E, +oo]%classic) y).
  by rewrite ge0_integral_pushforward ?pre//; exact: emeasurable_itv.
transitivity (\int[pushforward m2 (k \o a2)]_(y in `[0%E, +oo]%classic) y).
  apply: eq_measure_integral => V mV _; rewrite /pushforward.
  exact: m12 (qbs_measurable_sigma_Mx mk mV).
by rewrite ge0_integral_pushforward ?pre//; exact: emeasurable_itv.
Qed.

(** Positive and negative parts of a sigma_Mx-measurable function. *)
Lemma qbs_measurable_funepos X (h : X -> \bar R) :
  qbs_measurable X h -> qbs_measurable X h^\+.
Proof.
move=> mh a ha; move: (mh _ ha) => /measurable_funepos.
by apply: eq_measurable_fun => r _; rewrite !funeposE.
Qed.

Lemma qbs_measurable_funeneg X (h : X -> \bar R) :
  qbs_measurable X h -> qbs_measurable X h^\-.
Proof.
move=> mh a ha; move: (mh _ ha) => /measurable_funeneg.
by apply: eq_measurable_fun => r _; rewrite !funenegE.
Qed.

(** Integration respects equivalence for sigma_Mx-measurable integrands. *)
Lemma qbs_integral_equiv (X : qbsType R) (p1 p2 : qbs_prob X)
    (h : X -> \bar R) :
  qbs_measurable X h -> qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof.
move=> mh e; rewrite /qbs_integral integralE [RHS]integralE.
have mhp := qbs_measurable_funepos mh.
have mhn := qbs_measurable_funeneg mh.
have ep a r : (fun x0 : mR => h (a x0))^\+ r = h^\+ (a r) by rewrite !funeposE.
have en a r : (fun x0 : mR => h (a x0))^\- r = h^\- (a r) by rewrite !funenegE.
under eq_integral do rewrite ep.
under [X in _ - X]eq_integral do rewrite en.
under [in RHS]eq_integral do rewrite ep.
under [X in _ = _ - X]eq_integral do rewrite en.
congr (_ - _).
  apply: (ge0_integral_sigma_Mx (k := h^\+)) => //;
    exact: qbs_prob_alpha_random.
apply: (ge0_integral_sigma_Mx (k := h^\-)) => //; exact: qbs_prob_alpha_random.
Qed.

(** Splitting the integral into positive and negative parts. *)
Lemma qbs_integralE X (p : qbs_prob X) (h : X -> \bar R) :
  qbs_integral X p h = qbs_integral X p h^\+ - qbs_integral X p h^\-.
Proof.
rewrite /qbs_integral integralE.
congr (_ - _).
- by apply: eq_integral => r _; rewrite /= !funeposE.
- by apply: eq_integral => r _; rewrite /= !funenegE.
Qed.

End ge0_integral_sigma_Mx.

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
  qbs_measurable X h -> qbs_integral X p h = (\int[qbs_law p]_x h x)%E.
Proof.
move=> mh; rewrite /qbs_integral integralE [RHS]integralE.
have /qbs_measurableE mh' := mh.
congr (_ - _)%E.
- rewrite ge0_integral_distribution//; first exact: measurable_funepos mh'.
  by apply: eq_integral => r _; rewrite /= !funeposE.
- rewrite ge0_integral_distribution//; first exact: measurable_funeneg mh'.
  by apply: eq_integral => r _; rewrite /= !funenegE.
Qed.

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

(** QBS expectation is the expectation of a random variable on the law. *)
Lemma qbs_expectE (X : qbsType R) (p : qbs_prob X)
    (f : {mfun qbs_meas X >-> R}) :
  qbs_expect X p f = ('E_(qbs_law p)[f])%E.
Proof.
rewrite /qbs_expect qbs_integral_law ?unlock//.
apply/qbs_measurableE; exact/measurable_EFinP/measurable_funPT.
Qed.

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

(** Integrability of constants, and the integral of a constant. *)
Lemma qbs_integrable_cst (X : qbsType R) (p : qbs_prob X) (c : R) :
  qbs_integrable X p (fun=> c%:E).
Proof. exact: finite_measure_integrable_cst. Qed.

Lemma qbs_integral_cst (X : qbsType R) (p : qbs_prob X) (c : \bar R) :
  qbs_integral X p (fun=> c) = c.
Proof. by rewrite /qbs_integral integral_cst//= probability_setT mule1. Qed.

(** Integrability only depends on the equivalence class of the probability. *)
Lemma qbs_integrable_equiv (X : qbsType R) (p1 p2 : qbs_prob X)
    (h : X -> \bar R) :
  qbs_measurable X h -> qbs_prob_equiv X p1 p2 ->
  qbs_integrable X p1 h -> qbs_integrable X p2 h.
Proof.
move=> mh e /integrableP[_ fin]; apply/integrableP; split.
  exact: mh _ (qbs_prob_alpha_random p2).
have mabs : qbs_measurable X (abse \o h).
  by move=> a ha; exact: measurableT_comp (mh _ ha).
move: fin; rewrite -[X in X < _]/(qbs_integral X p1 (abse \o h)).
by rewrite (qbs_integral_equiv mabs e).
Qed.

(** A sigma_Mx-measurable function is integrable iff |h| has finite integral. *)
Lemma qbs_integrableP (X : qbsType R) (p : qbs_prob X) (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_integrable X p h <-> qbs_integral X p (fun x => `|h x|) < +oo.
Proof.
move=> mh; split=> [/integrableP[_ //]|fin]; apply/integrableP; split => //.
exact: mh _ (qbs_prob_alpha_random p).
Qed.

Lemma qbs_integrable_abseP (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_integrable X p (abse \o h) <-> qbs_integrable X p h.
Proof.
move=> mh; split=> [/integrableP[_ fin]|]; last exact: integrable_abse.
apply/integrableP; split; first exact: mh _ (qbs_prob_alpha_random p).
by move: fin; under eq_integral do rewrite /= abse_id.
Qed.

(** Multiplication by a bounded measurable factor preserves integrability. *)
Lemma qbs_integrableMr (X : qbsType R) (p : qbs_prob X) (k : X -> R)
    (h : X -> \bar R) :
  measurable_fun setT (k \o qbs_prob_alpha p) ->
  (exists M, forall x, `|k x| <= M)%R ->
  qbs_integrable X p h -> qbs_integrable X p (fun x => (k x)%:E * h x).
Proof.
move=> mk [M kM] hi; apply: (integrableMr measurableT mk _ hi).
exists M; split; first exact: num_real.
by move=> y My x _; exact/(le_trans (kM _))/ltW.
Qed.

(** The positive part of an integrable function has finite integral, and so
    has its negative part. *)
Lemma qbs_integral_funepos_lty (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :
  qbs_integrable X p h -> qbs_integral X p h^\+ < +oo.
Proof.
move=> hi; have := integral_funepos_lt_pinfty measurableT hi.
rewrite /qbs_integral; congr (_ < _) => //.
by apply: eq_integral => r _; rewrite /= !funeposE.
Qed.

Lemma qbs_integral_funeneg_fin_num (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :
  qbs_integrable X p h -> qbs_integral X p h^\- \is a fin_num.
Proof.
move=> hi; have := integrable_neg_fin_num measurableT hi.
rewrite /qbs_integral; congr (_ \is a fin_num).
by apply: eq_integral => r _; rewrite /= !funenegE.
Qed.

(** Bounded measurable real functions are integrable. *)
Lemma qbs_integrable_bounded (X : qbsType R) (p : qbs_prob X) (k : X -> R) :
  qbs_measurable X (fun x => (k x)%:E) -> (exists M, forall x, `|k x| <= M)%R ->
  qbs_integrable X p (fun x => (k x)%:E).
Proof.
move=> mk bd.
have /measurable_EFinP mka := mk _ (qbs_prob_alpha_random p).
have := qbs_integrableMr (h := fun=> 1%:E) mka bd (qbs_integrable_cst p 1%R).
by apply: eq_integrable => // r _ /=; rewrite mule1.
Qed.

Lemma qbs_integrable_sqrB (X : qbsType R) (p : qbs_prob X) (k : X -> R)
    (c : R) :
  k \o qbs_prob_alpha p \in Lfun (qbs_prob_mu p) 2%:E ->
  qbs_integrable X p (fun x => ((k x - c) ^+ 2)%:E).
Proof.
move=> kL2.
have k1 := Lfun_subset12 (fin_num_measure (qbs_prob_mu p) _ measurableT) kL2.
have /Lfun1_integrable ik := k1.
have isq := Lfun2_integrable_sqr kL2.
have := integrableD measurableT
  (integrableB measurableT isq (integrableZl measurableT (2 * c)%R ik))
  (finite_measure_integrable_cst (qbs_prob_mu p) (c ^+ 2)%R measurableT).
apply: eq_integrable => // r _ /=.
rewrite -!EFinD; congr (_%:E); ring.
Qed.

(** Monotonicity of the integral. *)
Lemma qbs_integral_le (X : qbsType R) (p : qbs_prob X) (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g -> (forall x, f x <= g x) ->
  qbs_integral X p f <= qbs_integral X p g.
Proof. by move=> hf hg fg; apply: le_integral => // r _; exact: fg. Qed.

Lemma ge0_qbs_integral_le (X : qbsType R) (p : qbs_prob X) (f g : X -> \bar R) :
  qbs_measurable X f -> qbs_measurable X g -> (forall x, 0 <= f x) ->
  (forall x, f x <= g x) -> qbs_integral X p f <= qbs_integral X p g.
Proof.
move=> mf mg f0 fg; apply: ge0_le_integral => //.
- exact: mf _ (qbs_prob_alpha_random p).
- exact: mg _ (qbs_prob_alpha_random p).
Qed.

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

(** The variance as the integral of the squared deviation from the mean. *)
Lemma qbs_varianceE_integral (X : qbsType R) (p : qbs_prob X) (h : X -> R) :
  qbs_variance X p h =
  qbs_integral X p (fun x => ((h x - fine (qbs_expect X p h)) *
                              (h x - fine (qbs_expect X p h)))%R%:E).
Proof.
rewrite /qbs_variance /variance /qbs_expect /qbs_integral !unlock/=.
by apply: eq_integral.
Qed.

(** The variance only depends on the equivalence class of the probability. *)
Lemma qbs_variance_equiv (X : qbsType R) (p1 p2 : qbs_prob X) (h : X -> R) :
  qbs_measurable X (fun x => (h x)%:E) -> qbs_prob_equiv X p1 p2 ->
  qbs_variance X p1 h = qbs_variance X p2 h.
Proof.
move=> mh e; rewrite !qbs_varianceE_integral.
have ee : qbs_expect X p1 h = qbs_expect X p2 h := qbs_integral_equiv mh e.
rewrite ee; apply: qbs_integral_equiv e => a ha.
have /measurable_EFinP mha := mh _ ha.
apply/measurable_EFinP/measurable_funM; apply: measurable_funB => //.
Qed.

(** Variance of an affine function, Var(a * h + b) = a^2 * Var(h). *)
Lemma qbs_variance_affine (X : qbsType R) (p : qbs_prob X) (a b : R)
    (h : X -> R) :
  h \o qbs_prob_alpha p \in Lfun (qbs_prob_mu p) 2%:E ->
  qbs_variance X p (fun x => a * h x + b)%R =
  (a ^+ 2)%:E * qbs_variance X p h.
Proof.
move=> hL2.
have haL2 : (a \o* h)%R \o qbs_prob_alpha p \in Lfun (qbs_prob_mu p) 2%:E.
  rewrite -[_ \o _]/(a \o* (h \o qbs_prob_alpha p))%R Lfun_scale//.
  exact: ler1n.
rewrite -(qbs_varianceZ a hL2).
have -> : (fun x => a * h x + b)%R = (fun x => (a \o* h)%R x + b)%R.
  by apply: funext => x /=; rewrite mulrC.
exact: (varianceD_cst_r (X := (a \o* h)%R \o qbs_prob_alpha p) b haL2).
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
