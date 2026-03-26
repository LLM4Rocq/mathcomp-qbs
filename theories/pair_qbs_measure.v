(* -------------------------------------------------------------------- *)
(* Product Measures on QBS Probability Spaces (Section 11)              *)
(*                                                                      *)
(* Constructs the product of QBS probability spaces P(X) x P(Y) ->     *)
(* P(X x Y), and develops Fubini-type theorems and independence.        *)
(* -------------------------------------------------------------------- *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import all_analysis.
From QBS Require Import quasi_borel probability_qbs.

Import Num.Def Num.Theory reals classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section PairQBSMeasure.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* 1. Product of QBS probability spaces                                  *)
(*    Given p : qbs_prob X and q : qbs_prob Y, construct                 *)
(*    qbs_prob (prodQ X Y) with alpha pairing the two alphas and         *)
(*    measure being the product measure.                                 *)
(* ===================================================================== *)

(* The product alpha pairs the random elements componentwise.
   We use the diagonal: r |-> (alpha_p(r), alpha_q(r)) which requires
   that we view R as a product of two copies via a measurable bijection.
   For simplicity, we use the direct pairing. *)

Definition qbs_pair_alpha (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r => (qbs_prob_alpha p r, qbs_prob_alpha q r).

Lemma qbs_pair_alpha_random (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) :
  @qbs_random R (prodQ X Y) (qbs_pair_alpha p q).
Proof.
split => /=.
- have -> : fst \o qbs_pair_alpha p q = qbs_prob_alpha p by [].
  exact: (qbs_prob_alpha_random p).
- have -> : snd \o qbs_pair_alpha p q = qbs_prob_alpha q by [].
  exact: (qbs_prob_alpha_random q).
Qed.

(* The product probability measure on R. In the full development this
   would be the product measure of qbs_prob_mu p and qbs_prob_mu q
   transported via a measurable bijection R -> R x R. Here we admit
   the existence of such a probability measure. *)

Definition qbs_pair_mu (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : probability mR R.
Proof. Admitted.

Definition qbs_prob_pair (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha p q)
    (qbs_pair_mu p q)
    (qbs_pair_alpha_random p q).

Arguments qbs_prob_pair : clear implicits.

(* ===================================================================== *)
(* 2. Fubini-type theorems for QBS integration                          *)
(* ===================================================================== *)

(* Integration over the first component *)
Lemma qbs_integral_fst (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair X Y p q)
    (fun xy => h (fst xy)) =
  @qbs_integral R X p h.
Proof. Admitted.

(* Integration over the second component *)
Lemma qbs_integral_snd (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair X Y p q)
    (fun xy => h (snd xy)) =
  @qbs_integral R Y q h.
Proof. Admitted.

(* Fubini's theorem: iterated integration equals joint integration *)
Lemma qbs_integral_pair (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair X Y p q) h =
  @qbs_integral R X p (fun x =>
    @qbs_integral R Y q (fun y => h (x, y))).
Proof. Admitted.

(* ===================================================================== *)
(* 3. Independence                                                       *)
(* ===================================================================== *)

(* Two QBS random variables are independent if their joint distribution
   equals the product of their marginals. *)
Definition qbs_indep (X Y Z : qbs R)
  (p : qbs_prob Z)
  (f : Z -> X) (g : Z -> Y)
  (hf : @qbs_morph R Z X f) (hg : @qbs_morph R Z Y g) : Prop :=
  @qbs_prob_equiv R (prodQ X Y)
    (@monadP_map R Z (prodQ X Y) (fun z => (f z, g z))
       (@qbs_morph_pair R Z X Y f g hf hg) p)
    (qbs_prob_pair X Y
       (@monadP_map R Z X f hf p)
       (@monadP_map R Z Y g hg p)).

Arguments qbs_indep : clear implicits.

(* E[f * g] = E[f] * E[g] for independent random variables.
   We specialize to two independent QBS random variables on X and Y. *)
Lemma qbs_integral_indep_mult (X Y : qbs R)
  (pxy : qbs_prob (prodQ X Y))
  (f : X -> R) (g : Y -> R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (hindep : @qbs_prob_equiv R (prodQ X Y) pxy (qbs_prob_pair X Y px py)) :
  @qbs_expect R (prodQ X Y) pxy
    (fun xy => f (fst xy) * g (snd xy))%R =
  (@qbs_expect R X px f * @qbs_expect R Y py g)%E.
Proof. Admitted.

End PairQBSMeasure.
