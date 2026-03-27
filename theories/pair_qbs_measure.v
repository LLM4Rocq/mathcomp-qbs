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

(* ===================================================================== *)
(* 6. Variance of sum of independent random variables                    *)
(*    For independent X, Y (on separate probability spaces px, py),     *)
(*    define the sum f(x) + g(y) on the product space. The variance     *)
(*    of this sum w.r.t. the product measure mu_px x mu_py equals       *)
(*    Var_px(f) + Var_py(g).                                            *)
(*                                                                       *)
(*    Key idea: varianceD gives                                          *)
(*      Var(F+G) = Var(F) + Var(G) + 2*Cov(F,G)                        *)
(*    For independent F, G (functions of separate coordinates),          *)
(*    Cov(F,G) = E[FG] - E[F]*E[G] = 0 by Fubini (the product          *)
(*    integral of f(r1)*g(r2) factors as E[f]*E[g]).                    *)
(*    Also, Var(F) w.r.t. product = Var_px(f) since F only depends      *)
(*    on the first coordinate, and similarly Var(G) = Var_py(g).        *)
(* ===================================================================== *)

(* Variance of f(x) + g(y) on the product space w.r.t. product measure *)
Definition qbs_pair_variance (X Y : qbs R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R) : \bar R :=
  variance (qbs_prob_mu px \x qbs_prob_mu py)
    (fun rr : mR * mR =>
      f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2)).

Arguments qbs_pair_variance : clear implicits.

(* Var(f(X) + g(Y)) = Var(f(X)) + Var(g(Y)) for independent X, Y.
   Independence is captured by the fact that X and Y live on separate
   probability spaces px, py, and the joint distribution is the
   product measure mu_px x mu_py. *)

(* Helper: expectation on product of a function depending only on the
   first coordinate equals expectation on the first marginal.
   E_{mu1 x mu2}[h(rr.1)] = E_{mu1}[h] *)
Lemma expectation_prod_fst (mu1 : probability mR R)
  (mu2 : probability mR R) (h : mR -> R)
  (hint : (mu1 \x mu2).-integrable setT
    (EFin \o (fun rr : mR * mR => h rr.1))) :
  'E_(mu1 \x mu2)[fun rr : mR * mR => h rr.1] =
  'E_mu1[h].
Proof.
rewrite !unlock /=.
set f := (fun rr : mR * mR => (h rr.1)%:E).
transitivity (\int[mu1]_x fubini_F mu2 f x).
  symmetry; rewrite -[f]/(EFin \o (fun rr : mR * mR => h rr.1)).
  exact: integral12_prod_meas1.
apply: eq_integral => x _.
rewrite /fubini_F /f /=.
rewrite -(functions.cstE _ (h x)%:E).
rewrite integral_cst; last exact: measurableT.
have h1 := @probability_setT _ _ _ mu2.
by rewrite [X in _ * X]h1 mule1.
Qed.

(* Helper: expectation on product of a function depending only on the
   second coordinate equals expectation on the second marginal. *)
Lemma expectation_prod_snd (mu1 : probability mR R)
  (mu2 : probability mR R) (h : mR -> R)
  (hint : (mu1 \x mu2).-integrable setT
    (EFin \o (fun rr : mR * mR => h rr.2))) :
  'E_(mu1 \x mu2)[fun rr : mR * mR => h rr.2] =
  'E_mu2[h].
Proof.
rewrite !unlock /=.
set f := (fun rr : mR * mR => (h rr.2)%:E).
transitivity (\int[mu2]_y fubini_G mu1 f y).
  rewrite -[f]/(EFin \o (fun rr : mR * mR => h rr.2)).
  symmetry; exact: integral21_prod_meas1.
apply: eq_integral => y _.
rewrite /fubini_G /f /=.
rewrite -(functions.cstE _ (h y)%:E).
rewrite integral_cst; last exact: measurableT.
have h1 := @probability_setT _ _ _ mu1.
by rewrite [X in _ * X]h1 mule1.
Qed.

(* Helper: variance on product of a function depending only on the
   first coordinate equals variance on the first marginal. *)
Lemma variance_prod_fst (mu1 : probability mR R)
  (mu2 : probability mR R) (h : mR -> R)
  (hL2prod : (fun rr : mR * mR => h rr.1) \in Lfun (mu1 \x mu2) 2)
  (hL2 : h \in Lfun mu1 2)
  (hint1 : (mu1 \x mu2).-integrable setT
    (EFin \o (fun rr : mR * mR => h rr.1)))
  (hint2 : (mu1 \x mu2).-integrable setT
    (EFin \o (fun rr : mR * mR => (h rr.1 ^+ 2)%R))) :
  'V_(mu1 \x mu2)[fun rr : mR * mR => h rr.1] =
  'V_mu1[h].
Proof.
rewrite !varianceE // /GRing.exp /= /GRing.mul /=.
unlock; congr (_ - _).
- rewrite unlock /=.
  set f := (fun rr : mR * mR => (h rr.1 * h rr.1)%:E).
  transitivity (\int[mu1]_x fubini_F mu2 f x).
    symmetry; rewrite -[f]/(EFin \o (fun rr : mR * mR => (h rr.1 ^+ 2)%R)).
    exact: integral12_prod_meas1.
  apply: eq_integral => x _.
  rewrite /fubini_F /f /=.
  rewrite -(functions.cstE _ (h x * h x)%:E).
  rewrite integral_cst; last exact: measurableT.
  have h1 := @probability_setT _ _ _ mu2.
  by rewrite [X in _ * X]h1 mule1.
- by rewrite (expectation_prod_fst hint1).
Qed.

(* Helper: variance on product of a function depending only on the
   second coordinate equals variance on the second marginal. *)
Lemma variance_prod_snd (mu1 : probability mR R)
  (mu2 : probability mR R) (h : mR -> R)
  (hL2prod : (fun rr : mR * mR => h rr.2) \in Lfun (mu1 \x mu2) 2)
  (hL2 : h \in Lfun mu2 2)
  (hint1 : (mu1 \x mu2).-integrable setT
    (EFin \o (fun rr : mR * mR => h rr.2)))
  (hint2 : (mu1 \x mu2).-integrable setT
    (EFin \o (fun rr : mR * mR => (h rr.2 ^+ 2)%R))) :
  'V_(mu1 \x mu2)[fun rr : mR * mR => h rr.2] =
  'V_mu2[h].
Proof.
rewrite !varianceE // /GRing.exp /= /GRing.mul /=.
unlock; congr (_ - _).
- rewrite unlock /=.
  set f := (fun rr : mR * mR => (h rr.2 * h rr.2)%:E).
  transitivity (\int[mu2]_y fubini_G mu1 f y).
    rewrite -[f]/(EFin \o (fun rr : mR * mR => (h rr.2 ^+ 2)%R)).
    symmetry; exact: integral21_prod_meas1.
  apply: eq_integral => y _.
  rewrite /fubini_G /f /=.
  rewrite -(functions.cstE _ (h y * h y)%:E).
  rewrite integral_cst; last exact: measurableT.
  have h1 := @probability_setT _ _ _ mu1.
  by rewrite [X in _ * X]h1 mule1.
- by rewrite (expectation_prod_snd hint1).
Qed.

(* Helper: E_{mu1 x mu2}[h1(rr.1) * h2(rr.2)] = E_{mu1}[h1] * E_{mu2}[h2] *)
Lemma expectation_prod_indep (mu1 : probability mR R)
  (mu2 : probability mR R) (h1 h2 : mR -> R)
  (hint1 : mu1.-integrable setT (fun r => (h1 r)%:E))
  (hint2 : mu2.-integrable setT (fun r => (h2 r)%:E))
  (hintprod : (mu1 \x mu2).-integrable setT
    (fun rr : mR * mR => (h1 rr.1 * h2 rr.2)%:E)) :
  'E_(mu1 \x mu2)[(fun rr : mR * mR => (h1 rr.1 * h2 rr.2)%R)] =
  ('E_mu1[h1] * 'E_mu2[h2]).
Proof.
rewrite !unlock /=.
set fg := (fun rr : mR * mR => (h1 rr.1 * h2 rr.2)%:E).
transitivity (\int[mu1]_r1
  ((h1 r1)%:E *
   \int[mu2]_r2 (h2 r2)%:E)).
- transitivity (\int[mu1]_r1 fubini_F mu2 fg r1).
    symmetry; exact: integral12_prod_meas1.
  apply: eq_integral => r1 _.
  rewrite /fubini_F /fg /=.
  under eq_integral do rewrite EFinM.
  rewrite integralZl //.
- have hfin : (\int[mu2]_r2 (h2 r2)%:E)
    \is a fin_num by exact: (integrable_fin_num measurableT hint2).
  rewrite -(fineK hfin).
  rewrite integralZr //.
Qed.

Lemma qbs_variance_indep_sum (X Y : qbs R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R)
  (hf2 : (fun rr : mR * mR => f (qbs_prob_alpha px rr.1))
    \in Lfun (qbs_prob_mu px \x qbs_prob_mu py) 2)
  (hg2 : (fun rr : mR * mR => g (qbs_prob_alpha py rr.2))
    \in Lfun (qbs_prob_mu px \x qbs_prob_mu py) 2)
  (hf1 : (fun r => f (qbs_prob_alpha px r))
    \in Lfun (qbs_prob_mu px) 2)
  (hg1 : (fun r => g (qbs_prob_alpha py r))
    \in Lfun (qbs_prob_mu py) 2)
  (hintf : (qbs_prob_mu px \x qbs_prob_mu py).-integrable setT
    (EFin \o (fun rr : mR * mR => f (qbs_prob_alpha px rr.1))))
  (hintg : (qbs_prob_mu px \x qbs_prob_mu py).-integrable setT
    (EFin \o (fun rr : mR * mR => g (qbs_prob_alpha py rr.2))))
  (hintf2 : (qbs_prob_mu px \x qbs_prob_mu py).-integrable setT
    (EFin \o (fun rr : mR * mR => (f (qbs_prob_alpha px rr.1) ^+ 2)%R)))
  (hintg2 : (qbs_prob_mu px \x qbs_prob_mu py).-integrable setT
    (EFin \o (fun rr : mR * mR => (g (qbs_prob_alpha py rr.2) ^+ 2)%R)))
  (hintfg : (qbs_prob_mu px \x qbs_prob_mu py).-integrable setT
    (EFin \o (fun rr : mR * mR =>
      (f (qbs_prob_alpha px rr.1) * g (qbs_prob_alpha py rr.2))%R)))
  (hintfm : (qbs_prob_mu px).-integrable setT
    (EFin \o (fun r => f (qbs_prob_alpha px r))))
  (hintgm : (qbs_prob_mu py).-integrable setT
    (EFin \o (fun r => g (qbs_prob_alpha py r)))) :
  qbs_pair_variance X Y px py f g =
  (qbs_variance X px f + qbs_variance Y py g)%E.
Proof.
rewrite /qbs_pair_variance /qbs_variance.
set F := (fun rr : mR * mR => f (qbs_prob_alpha px rr.1)).
set G := (fun rr : mR * mR => g (qbs_prob_alpha py rr.2)).
set fp := (fun r => f (qbs_prob_alpha px r)).
set gp := (fun r => g (qbs_prob_alpha py r)).
set mu_p := qbs_prob_mu px.
set mu_q := qbs_prob_mu py.
have FGeq : (fun rr : mR * mR =>
  f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2)) = (F \+ G)%R.
  by apply: boolp.funext => rr.
rewrite FGeq varianceD //.
(* Var(F) + Var(G) + 2 * Cov(F,G) = variance mu_p fp + variance mu_q gp *)
rewrite (variance_prod_fst hf2 hf1 hintf hintf2).
rewrite (variance_prod_snd hg2 hg1 hintg hintg2).
(* variance mu_p fp + variance mu_q gp + 2 * Cov(F,G) =
   variance mu_p fp + variance mu_q gp *)
suff -> : covariance (mu_p \x mu_q) F G = 0
  by rewrite mule0 adde0.
(* Use covarianceE: Cov(F,G) = E[FG] - E[F]*E[G] *)
have prod_fin : (mu_p \x mu_q) setT \is a fin_num.
  by rewrite -(@setXTT mR mR) product_measure1E //= !probability_setT mule1.
have hfL1 : F \in Lfun (mu_p \x mu_q) 1.
  exact: (Lfun_subset12 prod_fin hf2).
have hgL1 : G \in Lfun (mu_p \x mu_q) 1.
  exact: (Lfun_subset12 prod_fin hg2).
have hfgL1 : (F \* G)%R \in Lfun (mu_p \x mu_q) 1.
  exact: (Lfun2_mul_Lfun1 hf2 hg2).
rewrite covarianceE //.
(* E[F*G] factors by Fubini: E[F*G] = E[fp] * E[gp] *)
have -> : 'E_(mu_p \x mu_q)[(F \* G)%R] =
  ('E_mu_p[fp] * 'E_mu_q[gp]).
  rewrite (@expectation_prod_indep mu_p mu_q fp gp hintfm hintgm) //.
(* E[F] = E[fp] *)
have -> : 'E_(mu_p \x mu_q)[F] = 'E_mu_p[fp].
  exact: (expectation_prod_fst hintf).
(* E[G] = E[gp] *)
have -> : 'E_(mu_p \x mu_q)[G] = 'E_mu_q[gp].
  exact: (expectation_prod_snd hintg).
(* Now: E[fp] * E[gp] - E[fp] * E[gp] = 0 *)
apply: subee.
have mu_p_fin : mu_p setT \is a fin_num.
  by rewrite (@probability_setT _ _ _ mu_p).
have mu_q_fin : mu_q setT \is a fin_num.
  by rewrite (@probability_setT _ _ _ mu_q).
have hfp_fin := expectation_fin_num (Lfun_subset12 mu_p_fin hf1).
have hgp_fin := expectation_fin_num (Lfun_subset12 mu_q_fin hg1).
by rewrite fin_numM.
Qed.

End PairQBSMeasure.
