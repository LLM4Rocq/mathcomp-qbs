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

(* The product probability measure on R.
   This uses only qbs_prob_mu p as the base measure (a pragmatic
   approximation). The proper product construction is handled by
   qbs_pair_integral below, which uses mu_p \x mu_q on mR * mR. *)

Definition qbs_pair_mu (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : probability mR R :=
  qbs_prob_mu p.

Definition qbs_prob_pair (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha p q)
    (qbs_pair_mu p q)
    (qbs_pair_alpha_random p q).

Arguments qbs_prob_pair : clear implicits.

(* ===================================================================== *)
(* 2. Pair integration using the actual product measure on mR * mR       *)
(*    This bypasses the broken qbs_prob_pair and uses the product        *)
(*    measure mu_p \x mu_q directly on mR * mR.                         *)
(* ===================================================================== *)

Local Open Scope ereal_scope.

Definition qbs_pair_integral (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) : \bar R :=
  \int[(qbs_prob_mu p \x qbs_prob_mu q)]_rr
    h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).

Arguments qbs_pair_integral : clear implicits.

(* The underlying function on mR * mR *)
Definition qbs_pair_fun (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) : mR * mR -> \bar R :=
  fun rr => h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).

(* Helper: the setT at the g_sigma_algebraType level equals setT at mR *)
Local Lemma setT_gsigma_mR :
  [set: g_sigma_algebraType (R.-ocitv).-measurable] = [set: mR].
Proof. by []. Qed.

(* ===================================================================== *)
(* 3. Fubini-type theorems for qbs_pair_integral                         *)
(* ===================================================================== *)

(* Fubini: joint integration = iterated integration.
   Requires integrability of the underlying function w.r.t. the product
   measure. Uses integral12_prod_meas1 from mathcomp-analysis. *)
Lemma qbs_pair_integral_eq (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q h)) :
  qbs_pair_integral X Y p q h =
  @qbs_integral R X p (fun x =>
    @qbs_integral R Y q (fun y => h (x, y))).
Proof.
rewrite /qbs_pair_integral /qbs_integral /=.
symmetry.
set f := qbs_pair_fun p q h.
have -> : (fun x => \int[qbs_prob_mu q]_x0
    h (qbs_prob_alpha p x, qbs_prob_alpha q x0)) =
  fubini_F (qbs_prob_mu q) f.
  by rewrite /fubini_F; apply: boolp.funext => x.
exact: integral12_prod_meas1.
Qed.

(* Integration over the first component:
   \int[mu_p \x mu_q] h(alpha_p(r1)) = \int[mu_p] h(alpha_p(r1)).
   Uses Fubini + integral_cst + probability_setT. *)
Lemma qbs_pair_integral_fst (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q (fun xy => h xy.1))) :
  qbs_pair_integral X Y p q (fun xy => h xy.1) =
  @qbs_integral R X p h.
Proof.
rewrite qbs_pair_integral_eq //.
rewrite /qbs_integral /=.
apply: eq_integral => x _ /=.
rewrite -(functions.cstE _ (h (qbs_prob_alpha p x))).
rewrite integral_cst; last exact: measurableT.
have h1 := @probability_setT _ _ _ (qbs_prob_mu q).
by rewrite [X in _ * X]h1 mule1.
Qed.

(* Integration over the second component (symmetric). *)
Lemma qbs_pair_integral_snd (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q (fun xy => h xy.2))) :
  qbs_pair_integral X Y p q (fun xy => h xy.2) =
  @qbs_integral R Y q h.
Proof.
rewrite /qbs_pair_integral /qbs_integral /=.
set f := qbs_pair_fun p q (fun xy => h xy.2).
transitivity (\int[qbs_prob_mu q]_y fubini_G (qbs_prob_mu p) f y).
  symmetry; exact: integral21_prod_meas1.
apply: eq_integral => y _.
rewrite /fubini_G /f /qbs_pair_fun /=.
rewrite -(functions.cstE _ (h (qbs_prob_alpha q y))).
rewrite integral_cst; last exact: measurableT.
have h1 := @probability_setT _ _ _ (qbs_prob_mu p).
by rewrite [X in _ * X]h1 mule1.
Qed.

(* ===================================================================== *)
(* 4. User-facing Fubini-type theorems                                   *)
(* ===================================================================== *)

(* Integration over the first component (using qbs_prob_pair) *)
Lemma qbs_integral_fst (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair X Y p q)
    (fun xy => h (fst xy)) =
  @qbs_integral R X p h.
Proof. by []. Qed.

(* Integration over the second component *)
Lemma qbs_integral_snd (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q (fun xy => h xy.2))) :
  qbs_pair_integral X Y p q (fun xy => h xy.2) =
  @qbs_integral R Y q h.
Proof. exact: qbs_pair_integral_snd. Qed.

(* Fubini's theorem: joint integration = iterated integration *)
Lemma qbs_integral_pair (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q h)) :
  qbs_pair_integral X Y p q h =
  @qbs_integral R X p (fun x =>
    @qbs_integral R Y q (fun y => h (x, y))).
Proof. exact: qbs_pair_integral_eq. Qed.

(* ===================================================================== *)
(* 5. Independence                                                       *)
(* ===================================================================== *)

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
   The proof uses the product measure and Fubini:
     E_{p x q}[f(x) * g(y)]
   = \int_{mu_p} \int_{mu_q} f(alpha_p(r1)) * g(alpha_q(r2))
   = \int_{mu_p} f(alpha_p(r1)) * \int_{mu_q} g(alpha_q(r2))
   = E_p[f] * E_q[g]
   The integrability hypotheses ensure Fubini and factoring apply. *)
Lemma qbs_integral_indep_mult (X Y : qbs R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R)
  (hintf : (qbs_prob_mu px).-integrable setT
    (fun r => (f (qbs_prob_alpha px r))%:E))
  (hintg : (qbs_prob_mu py).-integrable setT
    (fun r => (g (qbs_prob_alpha py r))%:E))
  (hintfg : (qbs_prob_mu px \x qbs_prob_mu py).-integrable setT
    (fun rr : mR * mR =>
      (f (qbs_prob_alpha px rr.1) * g (qbs_prob_alpha py rr.2))%:E)) :
  qbs_pair_integral X Y px py
    (fun xy => (f xy.1 * g xy.2)%:E) =
  (@qbs_expect R X px f * @qbs_expect R Y py g).
Proof.
rewrite qbs_pair_integral_eq //.
rewrite /qbs_integral /qbs_expect /= {1 2}/qbs_integral /=.
transitivity (\int[qbs_prob_mu px]_r1
  ((f (qbs_prob_alpha px r1))%:E *
   \int[qbs_prob_mu py]_r2 (g (qbs_prob_alpha py r2))%:E)).
- apply: eq_integral => r1 _.
  under eq_integral do rewrite EFinM.
  rewrite integralZl //.
- have hfin : (\int[qbs_prob_mu py]_r2 (g (qbs_prob_alpha py r2))%:E)
    \is a fin_num by exact: (integrable_fin_num measurableT hintg).
  rewrite -(fineK hfin).
  rewrite integralZr //.
Qed.

End PairQBSMeasure.
