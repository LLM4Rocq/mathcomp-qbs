(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra reals ereal topology boolp
  classical_sets borel_hierarchy numfun measure lebesgue_measure sequences
  lebesgue_integral hoelder probability lebesgue_stieltjes_measure charge
  normedtype.
From mathcomp.algebra_tactics Require Import ring.
From QBS Require Import measurable_aux quasi_borel.

(**md**************************************************************************)
(* # Probability Spaces on Quasi-Borel Spaces                                 *)
(*                                                                            *)
(* Following "A Convenient Category for Higher-Order Probability Theory"      *)
(* Heunen, Kammar, Staton, Yang (LICS 2017), Section 4                        *)
(*                                                                            *)
(* A probability on X is represented by a pair (alpha, mu) of a random        *)
(* element alpha and a probability measure mu on R; two pairs represent the   *)
(* same probability when they agree on the sigma_Mx sets. As for the a.e.     *)
(* equality classes of hoelder.v, the probabilities are the quotient of the   *)
(* pairs by this equivalence (generic_quotient), so that the monad laws of    *)
(* qbs_monad.v are equalities.                                                *)
(*                                                                            *)
(* ```                                                                        *)
(*   preprob X        == pairs (alpha, mu) (representatives)                  *)
(*   probQ X           == probabilities on X: the quotient of the pairs       *)
(*   qbs_alpha p, qbs_mu p == the pair of a representative of p               *)
(*   mkQBSProb alpha mu ha == the probability represented by (alpha, mu)      *)
(*   qbs_event X p U == mu (alpha @^-1` U)                                    *)
(*   qbs_eqP         == probabilities are equal iff they agree on             *)
(*                           sigma_Mx sets                                    *)
(*   qbs_measurable X h   == h o alpha is Borel for every random alpha        *)
(*   integral_sigma_Mx    == integrals of sigma_Mx-measurable functions only  *)
(*                           depend on the measure of sigma_Mx sets           *)
(*   qbs_integral X p h   == integration against a QBS probability            *)
(*   qbs_event_mk, qbs_integral_mk, qbs_integrable_mk, qbs_variance_mk        *)
(*                        == computation on mkQBSProb                         *)
(*   qbs_law p            == the law of p, a probability on L X = qbs_meas X  *)
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
(*   qbs_variance_affine  == Var(a * h + b) = a^2 * Var(h)                    *)
(*   qbs_expect X p h     == expectation of a real function                   *)
(*   qbs_variance X p h   == variance of h o alpha under mu                   *)
(*   qbs_rv X p h hm      == random variable from a measurable h o alpha      *)
(* ```                                                                        *)
(* The probability monad itself is in qbs_monad.v.                            *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory Order.POrderTheory
  measurable_realfun MeasurableR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section probability_qbs.
Variable R : realType.

Local Abbreviation mR := (measurableTypeR R).

Implicit Types X : qbsType R.

(** Representatives of probabilities: a random element alpha : R -> X and a
    base probability measure mu on R. *)
Record preprob X := QBSPreProb {
  preprob_alpha : mR -> X ;
  preprob_mu : probability mR R ;
  preprob_alpha_random : qbs_Mx preprob_alpha }.

HB.instance Definition _ X := gen_eqMixin (preprob X).
HB.instance Definition _ X := gen_choiceMixin (preprob X).

(* Sigma_Mx-measurability for functions h : X -> \bar R.
   h is sigma_Mx-measurable iff for every random element alpha
   in Mx(X), the composition h o alpha : R -> \bar R is Borel
   measurable. *)
Definition qbs_measurable X (h : X -> \bar R) : Prop :=
  forall alpha, qbs_Mx alpha ->
    measurable_fun setT (fun r => h (alpha r)).

Arguments qbs_measurable : clear implicits.

(** Measurable functions out of measQ M are sigma_Mx-measurable. *)
Lemma qbs_measurable_measQ d (M : measurableType d) (h : M -> \bar R) :
  measurable_fun setT h -> qbs_measurable (measQ R M) h.
Proof. by move=> mh a ha; exact: measurableT_comp mh ha. Qed.

Lemma qbs_measurable_comp X Y (f : qbsHomType X Y) (h : Y -> \bar R) :
  qbs_measurable Y h -> qbs_measurable X (h \o f).
Proof. by move=> mh a ha; exact: mh _ (qbs_hom_proof _ ha). Qed.

(* If h is sigma_Mx-measurable, then preimages of
   measurable sets are in sigma_Mx. *)
Lemma qbs_measurable_sigma_Mx X (h : X -> \bar R)
  (hm : qbs_measurable X h) (V : set (\bar R)) :
  measurable V -> sigma_Mx (h @^-1` V).
Proof.
move=> hV alpha halpha.
by have := hm alpha halpha measurableT V hV; rewrite setTI.
Qed.

(** Positive and negative parts of a sigma_Mx-measurable function. *)
Lemma qbs_measurable_funepos X (h : X -> \bar R) :
  qbs_measurable X h -> qbs_measurable X h^\+%E.
Proof.
move=> mh a ha; move: (mh _ ha) => /measurable_funepos.
by apply: eq_measurable_fun => r _; rewrite !funeposE.
Qed.

Lemma qbs_measurable_funeneg X (h : X -> \bar R) :
  qbs_measurable X h -> qbs_measurable X h^\-%E.
Proof.
move=> mh a ha; move: (mh _ ha) => /measurable_funeneg.
by apply: eq_measurable_fun => r _; rewrite !funenegE.
Qed.

Section integral_sigma_Mx.
Local Open Scope ereal_scope.
Context X (a1 a2 : mR -> X) (m1 m2 : {measure set mR -> \bar R}%R).

(** Integrals of sigma_Mx-measurable functions only depend on the measures
    of the preimages of sigma_Mx sets. *)
Lemma ge0_integral_sigma_Mx (k : X -> \bar R) : qbs_Mx a1 -> qbs_Mx a2 ->
  (forall U, sigma_Mx U -> m1 (a1 @^-1` U) = m2 (a2 @^-1` U)) ->
  qbs_measurable X k -> (forall x, 0 <= k x) ->
  \int[m1]_r k (a1 r) = \int[m2]_r k (a2 r).
Proof.
move=> ha1 ha2 m12 mk k0; have mk1 := mk _ ha1; have mk2 := mk _ ha2.
have pre (a : mR -> X) : (k \o a) @^-1` `[0, +oo]%classic = [set: mR].
  by apply/seteqP; split=> // r _; rewrite /= in_itv /= k0 leey.
have Pge0 : {in `[0, +oo]%classic, forall y : \bar R, 0 <= y}.
  by move=> y; rewrite inE /= in_itv /= => /andP[].
transitivity (\int[pushforward m1 (k \o a1)]_(y in `[0, +oo]%classic) y).
  by rewrite ge0_integral_pushforward ?pre//; exact: emeasurable_itv.
transitivity (\int[pushforward m2 (k \o a2)]_(y in `[0, +oo]%classic) y).
  apply: eq_measure_integral => V mV _; rewrite /pushforward.
  exact: m12 (qbs_measurable_sigma_Mx mk mV).
by rewrite ge0_integral_pushforward ?pre//; exact: emeasurable_itv.
Qed.

Lemma integral_sigma_Mx (k : X -> \bar R) : qbs_Mx a1 -> qbs_Mx a2 ->
  (forall U, sigma_Mx U -> m1 (a1 @^-1` U) = m2 (a2 @^-1` U)) ->
  qbs_measurable X k -> \int[m1]_r k (a1 r) = \int[m2]_r k (a2 r).
Proof.
move=> ha1 ha2 m12 mk; rewrite integralE [RHS]integralE.
have mkp := qbs_measurable_funepos mk; have mkn := qbs_measurable_funeneg mk.
congr (_ - _).
  transitivity (\int[m1]_r k^\+ (a1 r)).
    by apply: eq_integral => r _; rewrite !funeposE.
  transitivity (\int[m2]_r k^\+ (a2 r)); first exact: ge0_integral_sigma_Mx.
  by apply: eq_integral => r _; rewrite !funeposE.
transitivity (\int[m1]_r k^\- (a1 r)).
  by apply: eq_integral => r _; rewrite !funenegE.
transitivity (\int[m2]_r k^\- (a2 r)); first exact: ge0_integral_sigma_Mx.
by apply: eq_integral => r _; rewrite !funenegE.
Qed.

End integral_sigma_Mx.

(** ** Probabilities: representatives up to equivalence *)

(** Two representatives are equivalent when they induce the same measure on
    sigma_Mx sets. *)
Definition preprob_equiv X (p1 p2 : preprob X) : Prop :=
  forall U, sigma_Mx U ->
    preprob_mu p1 (preprob_alpha p1 @^-1` U) =
    preprob_mu p2 (preprob_alpha p2 @^-1` U).

Section equiv_rel.
Variable X : qbsType R.

Definition preprob_eq_op : rel (preprob X) :=
  fun p1 p2 => `[< preprob_equiv p1 p2 >].

Let preprob_eq_op_refl : reflexive preprob_eq_op.
Proof. by move=> p; exact/asboolP. Qed.

Let preprob_eq_op_sym : symmetric preprob_eq_op.
Proof.
by move=> p q; apply/idP/idP=> /asboolP e; apply/asboolP=> U /e ->.
Qed.

Let preprob_eq_op_trans : transitive preprob_eq_op.
Proof.
move=> q p r /asboolP hpq /asboolP hqr; apply/asboolP=> U hU.
by rewrite hpq// hqr.
Qed.

Canonical preprob_equiv_rel :=
  EquivRel preprob_eq_op preprob_eq_op_refl preprob_eq_op_sym
    preprob_eq_op_trans.

End equiv_rel.

Local Open Scope quotient_scope.

(** The probabilities on X, P(X) of HKSY. *)
Definition probQ X : Type := {eq_quot (@preprob_equiv_rel X)}.

HB.instance Definition _ X := Choice.on (probQ X).
HB.instance Definition _ X := EqQuotient.on (probQ X).

Definition qbs_alpha X (p : probQ X) : mR -> X :=
  preprob_alpha (repr p).

Definition qbs_mu X (p : probQ X) : probability mR R :=
  preprob_mu (repr p).

Lemma qbs_alpha_random X (p : probQ X) : qbs_Mx (qbs_alpha p).
Proof. exact: preprob_alpha_random. Qed.

(** The probability represented by alpha and mu. *)
Definition mkQBSProb X (alpha : mR -> X) (mu : probability mR R)
    (halpha : qbs_Mx alpha) : probQ X :=
  \pi_(probQ X) (QBSPreProb mu halpha).

Definition qbs_event X (p : probQ X) (U : set X) : \bar R :=
  qbs_mu p (qbs_alpha p @^-1` U).

Arguments qbs_event : clear implicits.

Lemma qbs_event_mk X (alpha : mR -> X) (mu : probability mR R)
    (halpha : qbs_Mx alpha) (U : set X) : sigma_Mx U ->
  qbs_event X (mkQBSProb mu halpha) U = mu (alpha @^-1` U).
Proof.
set q := QBSPreProb mu halpha.
have /eqmodP/asboolP e : repr (\pi_(probQ X) q) = q %[mod probQ X].
  by rewrite reprK.
exact: e.
Qed.

(** Two probabilities are equal iff they agree on sigma_Mx sets. *)
Lemma qbs_eqP X (p1 p2 : probQ X) :
  p1 = p2 <->
  forall U, sigma_Mx U -> qbs_event X p1 U = qbs_event X p2 U.
Proof.
split=> [->//|e]; rewrite -[p1]reprK -[p2]reprK.
by apply/eqmodP/asboolP; exact: e.
Qed.

Lemma mkQBSProbK X (p : probQ X) :
  mkQBSProb (qbs_mu p) (qbs_alpha_random p) = p.
Proof. by apply/qbs_eqP => U mU; rewrite qbs_event_mk. Qed.

(** Integration of h : X -> \bar R against a QBS probability, via the base
    measure and alpha. *)
Definition qbs_integral X (p : probQ X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_mu p]_x (h (qbs_alpha p x)))%E.

Arguments qbs_integral : clear implicits.

(** Splitting the integral into positive and negative parts. *)
Lemma qbs_integralE X (p : probQ X) (h : X -> \bar R) :
  qbs_integral X p h = (qbs_integral X p h^\+ - qbs_integral X p h^\-)%E.
Proof.
rewrite /qbs_integral integralE; congr (_ - _)%E.
  by apply: eq_integral => r _; rewrite !funeposE.
by apply: eq_integral => r _; rewrite !funenegE.
Qed.

Lemma qbs_integral_mk X (alpha : mR -> X) (mu : probability mR R)
    (halpha : qbs_Mx alpha) (h : X -> \bar R) : qbs_measurable X h ->
  qbs_integral X (mkQBSProb mu halpha) h = (\int[mu]_r h (alpha r))%E.
Proof.
move=> mh; apply: integral_sigma_Mx => //; first exact: qbs_alpha_random.
by move=> U mU; exact: qbs_event_mk.
Qed.

(** ** The law of a QBS probability on L X (HKSY l_X, eq. (3)) *)

Lemma qbs_measurableP X (h : X -> \bar R) :
  qbs_measurable X h <->
  measurable_fun [set: qbs_meas X] h.
Proof. exact: (qbs_morphism_measurableP (M := \bar R)). Qed.

Definition qbs_alpha_mfun X (p : probQ X) :
    {mfun mR >-> qbs_meas X} :=
  mfun_Sub (mem_set (qbs_Mx_measurable (qbs_alpha_random p))).

Definition qbs_law X (p : probQ X) :
    probability (qbs_meas X) R :=
  distribution (qbs_mu p) (qbs_alpha_mfun p).

Lemma qbs_lawE X (p : probQ X) (A : set X) :
  qbs_law p A = qbs_event X p A.
Proof. by []. Qed.

(** Probabilities are determined by their laws. *)
Lemma qbs_eq_lawP X (p1 p2 : probQ X) :
  p1 = p2 <->
  (forall A : set (qbs_meas X), measurable A -> qbs_law p1 A = qbs_law p2 A).
Proof. exact: qbs_eqP. Qed.

Lemma ge0_qbs_integral_law X (p : probQ X) (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, (0 <= h x)%E) ->
  qbs_integral X p h = (\int[qbs_law p]_x h x)%E.
Proof.
by move=> /qbs_measurableP mh h0; rewrite ge0_integral_distribution.
Qed.

Lemma qbs_integral_law X (p : probQ X) (h : X -> \bar R) :
  qbs_measurable X h -> qbs_integral X p h = (\int[qbs_law p]_x h x)%E.
Proof.
move=> mh; rewrite qbs_integralE [RHS]integralE.
congr (_ - _)%E.
  apply: ge0_qbs_integral_law (fun x => funepos_ge0 _ _).
  exact: qbs_measurable_funepos.
apply: ge0_qbs_integral_law (fun x => funeneg_ge0 _ _).
exact: qbs_measurable_funeneg.
Qed.

(** Expectation of a real-valued function h on a QBS probability, defined as
    qbs_integral of the extended-real embedding. *)
Definition qbs_expect X (p : probQ X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Arguments qbs_expect : clear implicits.

(** QBS expectation is the expectation of a random variable on the law. *)
Lemma qbs_expectE X (p : probQ X)
    (f : {mfun qbs_meas X >-> R}) :
  qbs_expect X p f = ('E_(qbs_law p)[f])%E.
Proof.
rewrite /qbs_expect qbs_integral_law ?unlock//.
by apply/qbs_measurableP; exact/measurable_EFinP/measurable_funPT.
Qed.

(** Variance of f : X -> R under a QBS probability, via the base-measure
    variance of f o alpha. *)
Definition qbs_variance X (p : probQ X)
  (f : X -> R) : \bar R :=
  variance (qbs_mu p) (f \o qbs_alpha p).

Arguments qbs_variance : clear implicits.

Section probability_inequalities.

Local Open Scope ereal_scope.

(** Integrability of h : X -> \bar R under a QBS probability: h o alpha is
    mu-integrable. *)
Definition qbs_integrable X (p : probQ X)
    (h : X -> \bar R) :=
  (qbs_mu p).-integrable setT (h \o qbs_alpha p).

Arguments qbs_integrable : clear implicits.

(** Integrability of constants, and the integral of a constant. *)
Lemma qbs_integrable_cst X (p : probQ X) (c : R) :
  qbs_integrable X p (fun=> c%:E).
Proof. exact: finite_measure_integrable_cst. Qed.

Lemma qbs_integral_cst X (p : probQ X) (c : \bar R) :
  qbs_integral X p (fun=> c) = c.
Proof. by rewrite /qbs_integral integral_cst//= probability_setT mule1. Qed.

Lemma qbs_integrable_mk X (alpha : mR -> X) (mu : probability mR R)
    (halpha : qbs_Mx alpha) (h : X -> \bar R) : qbs_measurable X h ->
  qbs_integrable X (mkQBSProb mu halpha) h <-> mu.-integrable setT (h \o alpha).
Proof.
move=> mh; have mabs : qbs_measurable X (abse \o h).
  by move=> ? /mh; exact: measurableT_comp.
have e := qbs_integral_mk mu halpha mabs.
split=> /integrableP[_ fin]; apply/integrableP; split.
- exact: mh.
- by move: fin; rewrite -[X in X < _]/(qbs_integral X _ (abse \o h)) e.
- exact: mh _ (qbs_alpha_random _).
- by rewrite -[X in X < _]/(qbs_integral X _ (abse \o h)) e.
Qed.

(** A sigma_Mx-measurable function is integrable iff |h| has finite integral. *)
Lemma qbs_integrableP X (p : probQ X) (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_integrable X p h <-> qbs_integral X p (fun x => `|h x|) < +oo.
Proof.
move=> mh; split=> [/integrableP[_ //]|fin]; apply/integrableP; split=> //.
exact: mh _ (qbs_alpha_random p).
Qed.

Lemma qbs_integrable_abseP X (p : probQ X)
    (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_integrable X p (abse \o h) <-> qbs_integrable X p h.
Proof.
move=> mh; split=> [/integrableP[_ fin]|]; last exact: integrable_abse.
apply/integrableP; split; first exact: mh _ (qbs_alpha_random p).
by move: fin; under eq_integral do rewrite /= abse_id.
Qed.

(** Multiplication by a bounded measurable factor preserves integrability. *)
Lemma qbs_integrableMr X (p : probQ X) (k : X -> R)
    (h : X -> \bar R) :
  qbs_measurable X (fun x => (k x)%:E) ->
  (exists M, forall x, `|k x| <= M)%R ->
  qbs_integrable X p h -> qbs_integrable X p (fun x => (k x)%:E * h x).
Proof.
move=> mk [M kM] hi.
have /measurable_EFinP mka := mk _ (qbs_alpha_random p).
apply: (integrableMr measurableT mka _ hi).
exists M; split; first exact: num_real.
by move=> y My x _; exact/(le_trans (kM _))/ltW.
Qed.

(** The positive part of an integrable function has finite integral, and so
    has its negative part. *)
Lemma qbs_integral_funepos_lty X (p : probQ X)
    (h : X -> \bar R) :
  qbs_integrable X p h -> qbs_integral X p h^\+ < +oo.
Proof.
move=> hi; have := integral_funepos_lt_pinfty measurableT hi.
rewrite /qbs_integral; congr (_ < _) => //.
by apply: eq_integral => r _; rewrite !funeposE.
Qed.

Lemma qbs_integral_funeneg_fin_num X (p : probQ X)
    (h : X -> \bar R) :
  qbs_integrable X p h -> qbs_integral X p h^\- \is a fin_num.
Proof.
move=> hi; have := integrable_neg_fin_num measurableT hi.
rewrite /qbs_integral; congr (_ \is a fin_num).
by apply: eq_integral => r _; rewrite !funenegE.
Qed.

Lemma qbs_integral_funeneg_lty X (p : probQ X)
    (h : X -> \bar R) :
  qbs_integrable X p h -> qbs_integral X p h^\- < +oo.
Proof.
by move=> /qbs_integral_funeneg_fin_num; rewrite fin_numElt => /andP[_].
Qed.

(** Bounded measurable real functions are integrable. *)
Lemma qbs_integrable_bounded X (p : probQ X) (k : X -> R) :
  qbs_measurable X (fun x => (k x)%:E) -> (exists M, forall x, `|k x| <= M)%R ->
  qbs_integrable X p (fun x => (k x)%:E).
Proof.
move=> mk bd.
have := qbs_integrableMr (h := fun=> 1%:E) mk bd (qbs_integrable_cst p 1%R).
by apply: eq_integrable => // r _ /=; rewrite mule1.
Qed.

Lemma qbs_integrable_sqrB X (p : probQ X) (k : X -> R)
    (c : R) :
  k \o qbs_alpha p \in Lfun (qbs_mu p) 2%:E ->
  qbs_integrable X p (fun x => ((k x - c) ^+ 2)%:E).
Proof.
move=> kL2.
have k1 := Lfun_subset12 (fin_num_measure (qbs_mu p) _ measurableT) kL2.
have /Lfun1_integrable ik := k1.
have isq := Lfun2_integrable_sqr kL2.
have := integrableD measurableT
  (integrableB measurableT isq (integrableZl measurableT (2 * c)%R ik))
  (finite_measure_integrable_cst (qbs_mu p) (c ^+ 2)%R measurableT).
apply: eq_integrable => // r _ /=.
by rewrite -!EFinD; congr (_%:E); ring.
Qed.

(** Monotonicity of the integral. *)
Lemma qbs_integral_le X (p : probQ X) (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g -> (forall x, f x <= g x) ->
  qbs_integral X p f <= qbs_integral X p g.
Proof. by move=> hf hg fg; apply: le_integral => // r _; exact: fg. Qed.

Lemma ge0_qbs_integral_le X (p : probQ X) (f g : X -> \bar R) :
  qbs_measurable X f -> qbs_measurable X g -> (forall x, 0 <= f x) ->
  (forall x, f x <= g x) -> qbs_integral X p f <= qbs_integral X p g.
Proof.
move=> mf mg f0 fg; apply: ge0_le_integral => //.
  exact: mf _ (qbs_alpha_random p).
exact: mg _ (qbs_alpha_random p).
Qed.

Lemma qbs_varianceE X (p : probQ X) (h : X -> R) :
  h \o qbs_alpha p \in Lfun (qbs_mu p) 2%:E ->
  qbs_variance X p h =
  qbs_expect X p (fun x => h x ^+ 2)%R - (qbs_expect X p h) ^+ 2.
Proof.
move=> hL2; rewrite /qbs_variance /qbs_expect /qbs_integral.
by rewrite varianceE //; congr (_ - _); rewrite unlock.
Qed.

Lemma qbs_varianceZ X (p : probQ X) (a : R)
    (h : X -> R) :
  h \o qbs_alpha p \in Lfun (qbs_mu p) 2%:E ->
  qbs_variance X p (a \o* h)%R =
  (a ^+ 2)%:E * qbs_variance X p h.
Proof.
move=> hL2; exact: varianceZ.
Qed.

(** The variance as the integral of the squared deviation from the mean. *)
Lemma qbs_varianceE_integral X (p : probQ X) (h : X -> R) :
  qbs_variance X p h =
  qbs_integral X p (fun x => ((h x - fine (qbs_expect X p h)) *
                              (h x - fine (qbs_expect X p h)))%R%:E).
Proof.
rewrite /qbs_variance /variance /qbs_expect /qbs_integral !unlock/=.
by apply: eq_integral.
Qed.

Lemma qbs_variance_mk X (alpha : mR -> X) (mu : probability mR R)
    (halpha : qbs_Mx alpha) (h : X -> R) :
  qbs_measurable X (fun x => (h x)%:E) ->
  qbs_variance X (mkQBSProb mu halpha) h = variance mu (h \o alpha).
Proof.
move=> mh; rewrite qbs_varianceE_integral /qbs_expect !qbs_integral_mk//.
  move=> a ha; have /measurable_EFinP mha := mh _ ha.
  by apply/measurable_EFinP/measurable_funM; apply: measurable_funB.
by rewrite /variance !unlock.
Qed.

(** Variance of an affine function, Var(a * h + b) = a^2 * Var(h). *)
Lemma qbs_variance_affine X (p : probQ X) (a b : R)
    (h : X -> R) :
  h \o qbs_alpha p \in Lfun (qbs_mu p) 2%:E ->
  qbs_variance X p (fun x => a * h x + b)%R =
  (a ^+ 2)%:E * qbs_variance X p h.
Proof.
move=> hL2.
have haL2 : (a \o* h)%R \o qbs_alpha p \in Lfun (qbs_mu p) 2%:E.
  rewrite -[_ \o _]/(a \o* (h \o qbs_alpha p))%R Lfun_scale//.
  exact: ler1n.
rewrite -(qbs_varianceZ a hL2).
have -> : (fun x => a * h x + b)%R = (fun x => (a \o* h)%R x + b)%R.
  by apply: funext => x /=; rewrite mulrC.
exact: (varianceD_cst_r (X := (a \o* h)%R \o qbs_alpha p) b haL2).
Qed.

(** Build a random variable from a measurable composition. *)
Definition qbs_rv X (p : probQ X)
    (h : X -> R)
    (hm : measurable_fun setT (h \o qbs_alpha p)) :
    {RV (qbs_mu p) >-> R} :=
  mfun_Sub (mem_set hm).

(** Markov inequality lifted to QBS probabilities. *)
Lemma qbs_markov X (p : probQ X)
    (h : X -> R) (f : R -> R) (eps : R)
    (hm : qbs_measurable X (fun x => (h x)%:E))
    (heps : (0 < eps)%R)
    (hmf : measurable_fun [set: R] f)
    (hf0 : forall r, (0 <= r)%R -> (0 <= f r)%R)
    (hfnd : {in Num.nneg &, {homo f : x y / (x <= y)%R}}) :
  (f eps)%:E * qbs_event X p [set x | (eps <= `|h x|)%R] <=
  qbs_integral X p (fun x => (f `|h x|)%:E).
Proof.
have /measurable_EFinP mha := hm _ (qbs_alpha_random p).
pose rv : {RV (qbs_mu p) >-> R} := qbs_rv mha.
have := @markov _ _ R _ rv f eps heps hmf hf0 hfnd.
rewrite unlock /qbs_event /qbs_integral /=.
under eq_set => x do rewrite -abse_EFin lee_fin.
exact.
Qed.

(** Chebyshev inequality lifted to QBS probabilities. *)
Lemma qbs_chebyshev X (p : probQ X)
    (h : X -> R) (eps : R)
    (hm : qbs_measurable X (fun x => (h x)%:E))
    (heps : (0 < eps)%R) :
  qbs_event X p [set x | (eps <= `|h x - fine (qbs_expect X p h)|)%R] <=
  (eps ^- 2)%:E * qbs_variance X p h.
Proof.
have /measurable_EFinP mha := hm _ (qbs_alpha_random p).
pose rv : {RV (qbs_mu p) >-> R} := qbs_rv mha.
have hE : qbs_expect X p h = 'E_(qbs_mu p)[rv] by rewrite unlock.
rewrite hE.
exact: chebyshev rv eps heps.
Qed.

End probability_inequalities.

End probability_qbs.

Arguments probQ {R}.
Arguments mkQBSProb {R X}.
Arguments qbs_alpha {R X}.
Arguments qbs_mu {R X}.
Arguments qbs_alpha_random {R X}.
Arguments qbs_eqP {R X p1 p2}.
Arguments qbs_integral {R}.
Arguments qbs_measurable {R}.
Arguments qbs_expect {R}.
Arguments qbs_event {R}.
Arguments qbs_variance {R}.
Arguments qbs_integrable {R}.
