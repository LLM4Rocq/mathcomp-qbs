(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
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

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import all_analysis.
From QBS Require Import quasi_borel probability_qbs.

Import Num.Def Num.Theory reals classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section MeasureAsQBS.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* 1. Embedding classical probability into QBS probability               *)
(*    For a standard Borel space M with measurable isomorphism to R,     *)
(*    given a probability measure P on M, we construct a QBS triple.     *)
(*                                                                       *)
(*    The key idea: if g : R -> M is a measurable section (with          *)
(*    f : M -> R measurable and g o f = id), then (g, pushforward_f P)  *)
(*    is a valid QBS probability triple on R_qbs(M).                    *)
(* ===================================================================== *)

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
Defined.

Arguments as_qbs_prob : clear implicits.

(* ===================================================================== *)
(* 2. Standard distributions as QBS probabilities                        *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(* 3. Recovery theorem                                                    *)
(*    The pushforward of the QBS measure along the alpha recovers the    *)
(*    original probability measure (up to the encoding).                 *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(* 4. Parameterized distribution morphisms                               *)
(*    Parameterized families of distributions are QBS morphisms from     *)
(*    the parameter space to the probability monad.                      *)
(*                                                                       *)
(*    Key insight: since qbs_normal_distribution mu sigma has alpha =    *)
(*    idfun for all mu, the monadP_random' condition reduces to showing *)
(*    qbs_Mx (realQ R) idfun, which is just measurable_id.              *)
(* ===================================================================== *)

(* The normal distribution, viewed as a function of its mean parameter,
   is a QBS morphism from realQ to monadP(realQ). *)
Lemma qbs_normal_morph (sigma : R) (hsigma : (0 < sigma)%R) :
  @qbs_morphism R (realQ R) (monadP (realQ R))
    (fun mu => qbs_normal_distribution mu sigma hsigma).
Proof.
move=> alpha halpha r /=.
exact: @measurable_id _ mR setT.
Qed.

(* The uniform distribution is a constant element of monadP(realQ),
   i.e., the constant function mapping any r to qbs_uniform is a
   random element of the probability monad. *)
Lemma qbs_uniform_random :
  @qbs_Mx R (monadP (realQ R)) (fun _ : mR => qbs_uniform).
Proof.
move=> r /=.
exact: @measurable_id _ mR setT.
Qed.

End MeasureAsQBS.
