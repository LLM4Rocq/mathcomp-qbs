(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals ereal topology boolp
  classical_sets normedtype numfun measure lebesgue_integral
  lebesgue_integral_fubini lebesgue_stieltjes_measure probability
  hoelder functions.
From QBS Require Import quasi_borel probability_qbs standard_borel.

(**md**************************************************************************)
(* # Product Measures on QBS Probability Spaces                               *)
(*                                                                            *)
(* Constructs the product of QBS probability spaces P(X) x P(Y) ->           *)
(* P(X x Y), and develops Fubini-type theorems and independence.              *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_prob_pair X Y p q == product QBS probability on prodQ X Y            *)
(*   qbs_pair_integral X Y p q h == integral of h w.r.t. product measure      *)
(*   qbs_indep X Y Z p f g == independence of f and g under p                 *)
(*   qbs_pair_variance X Y px py f g == variance of f(x) + g(y) on product   *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import boolp.

Local Open Scope classical_set_scope.

Section pair_qbs_measure.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(** Product of QBS probability spaces.
    Given p : qbs_prob X and q : qbs_prob Y, construct
    qbs_prob (prodQ X Y) with alpha pairing the two alphas and
    measure being the product measure. *)

(* The product probability measure on R.
   Uses R ≅ R×R (from standard_borel.v): push mu_p × mu_q through
   encode_RR to obtain a probability measure on mR. *)

Section pair_mu_build.
Variables (X Y : qbsType R).
Variables (p : qbs_prob X) (q : qbs_prob Y).

Let mu_p := qbs_prob_mu p.
Let mu_q := qbs_prob_mu q.

Let pf_mu (A : set mR) : \bar R :=
  (mu_p \x mu_q) (@encode_RR_mR R @^-1` A).

Local Open Scope ereal_scope.

Let pf_mu0 : pf_mu set0 = 0.
Proof. by rewrite /pf_mu preimage_set0 measure0. Qed.

Let pf_mu_ge0 (A : set mR) : 0 <= pf_mu A.
Proof. by rewrite /pf_mu; exact: measure_ge0. Qed.

Let pf_mu_sigma : semi_sigma_additive pf_mu.
Proof.
move=> F mF tF mUF; rewrite /pf_mu preimage_bigcup.
apply: measure_semi_sigma_additive.
- move=> n; rewrite -[X in measurable X]setTI.
  exact: (measurable_RR_to_R measurableT (mF n)).
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- rewrite -preimage_bigcup -[X in measurable X]setTI.
  exact: (measurable_RR_to_R measurableT mUF).
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  pf_mu pf_mu0 pf_mu_ge0 pf_mu_sigma.

Let pf_mu_setT : pf_mu setT = 1%:E.
Proof. by rewrite /pf_mu preimage_setT probability_setT. Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _
  pf_mu pf_mu_setT.

Definition qbs_pair_mu_build : probability mR R :=
  [the probability mR R of pf_mu].

End pair_mu_build.

Definition qbs_pair_alpha (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r =>
    let uv := @decode_RR_mR R r in
    (qbs_prob_alpha p uv.1, qbs_prob_alpha q uv.2).

(** Product measure on mR for the QBS product. *)
Definition qbs_pair_mu (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : probability mR R :=
  qbs_pair_mu_build p q.

Lemma qbs_pair_alpha_random (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) :
  @qbs_Mx R (prodQ X Y) (qbs_pair_alpha p q).
Proof.
rewrite /qbs_Mx /=; split.
- have -> : (fun r => (qbs_pair_alpha p q r).1) =
    qbs_prob_alpha p \o (fst \o @decode_RR_mR R) by [].
  apply: qbs_Mx_compT; first exact: (qbs_prob_alpha_random p).
  apply: measurableT_comp; first exact: measurable_fst.
  exact: measurable_R_to_RR.
- have -> : (fun r => (qbs_pair_alpha p q r).2) =
    qbs_prob_alpha q \o (snd \o @decode_RR_mR R) by [].
  apply: qbs_Mx_compT; first exact: (qbs_prob_alpha_random q).
  apply: measurableT_comp; first exact: measurable_snd.
  exact: measurable_R_to_RR.
Qed.

Definition qbs_prob_pair (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha p q)
    (qbs_pair_mu p q)
    (qbs_pair_alpha_random p q).

Arguments qbs_prob_pair : clear implicits.

(** Pair integration using the product measure on mR * mR.
    Works directly with mu_p \x mu_q on mR * mR for Fubini etc. *)

Local Open Scope ereal_scope.

Definition qbs_pair_integral (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) : \bar R :=
  \int[(qbs_prob_mu p \x qbs_prob_mu q)]_rr
    h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).

Arguments qbs_pair_integral : clear implicits.

(* The underlying function on mR * mR *)
Definition qbs_pair_fun (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) : mR * mR -> \bar R :=
  fun rr => h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).

(** Fubini-type theorems for qbs_pair_integral. *)

(* Fubini: joint integration = iterated integration.
   Requires integrability of the underlying function w.r.t. the product
   measure. Uses integral12_prod_meas1 from mathcomp-analysis. *)
(** Iterated integration on a fixed QBS product measure:
    the joint integral on [mu_p \x mu_q] equals the iterated
    integral in one fixed order. Not a full Fubini statement. *)
Lemma qbs_pair_integral_iterated (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q h)) :
  qbs_pair_integral X Y p q h =
  qbs_integral X p (fun x =>
    qbs_integral Y q (fun y => h (x, y))).
Proof.
rewrite /qbs_pair_integral /qbs_integral /=.
symmetry.
set f := qbs_pair_fun p q h.
have -> : (fun x => \int[qbs_prob_mu q]_x0
    h (qbs_prob_alpha p x, qbs_prob_alpha q x0)) =
  fubini_F (qbs_prob_mu q) f.
  by rewrite /fubini_F; apply: funext => x.
exact: integral12_prod_meas1.
Qed.

(* Integration over the first component:
   \int[mu_p \x mu_q] h(alpha_p(r1)) = \int[mu_p] h(alpha_p(r1)).
   Uses Fubini + integral_cst + probability_setT. *)
Lemma qbs_pair_integral_fst (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q (fun xy => h xy.1))) :
  qbs_pair_integral X Y p q (fun xy => h xy.1) =
  qbs_integral X p h.
Proof.
rewrite qbs_pair_integral_iterated //.
rewrite /qbs_integral /=.
apply: eq_integral => x _ /=.
rewrite -(cstE _ (h (qbs_prob_alpha p x))).
rewrite integral_cst; last exact: measurableT.
have h1 := @probability_setT _ _ _ (qbs_prob_mu q).
by rewrite [X in _ * X]h1 mule1.
Qed.

(* Integration over the second component (symmetric). *)
Lemma qbs_pair_integral_snd (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q (fun xy => h xy.2))) :
  qbs_pair_integral X Y p q (fun xy => h xy.2) =
  qbs_integral Y q h.
Proof.
rewrite /qbs_pair_integral /qbs_integral /=.
set f := qbs_pair_fun p q (fun xy => h xy.2).
transitivity (\int[qbs_prob_mu q]_y fubini_G (qbs_prob_mu p) f y).
  symmetry; exact: integral21_prod_meas1.
apply: eq_integral => y _.
rewrite /fubini_G /f /qbs_pair_fun /=.
rewrite -(cstE _ (h (qbs_prob_alpha q y))).
rewrite integral_cst; last exact: measurableT.
have h1 := @probability_setT _ _ _ (qbs_prob_mu p).
by rewrite [X in _ * X]h1 mule1.
Qed.

(** Independence. *)

Definition qbs_indep (X Y Z : qbsType R)
  (p : qbs_prob Z)
  (f : Z -> X) (g : Z -> Y)
  (hf : qbs_morphism f) (hg : qbs_morphism g) : Prop :=
  qbs_prob_equiv (prodQ X Y)
    (monadP_map Z (prodQ X Y) (fun z => (f z, g z))
       (fun alpha halpha => conj (hf _ halpha) (hg _ halpha)) p)
    (qbs_prob_pair X Y
       (monadP_map Z X f hf p)
       (monadP_map Z Y g hg p)).

Arguments qbs_indep : clear implicits.

(* E[f * g] = E[f] * E[g] for independent random variables.
   The proof uses the product measure and Fubini:
     E_{p x q}[f(x) * g(y)]
   = \int_{mu_p} \int_{mu_q} f(alpha_p(r1)) * g(alpha_q(r2))
   = \int_{mu_p} f(alpha_p(r1)) * \int_{mu_q} g(alpha_q(r2))
   = E_p[f] * E_q[g]
   The integrability hypotheses ensure Fubini and factoring apply. *)
(** Factorization of integration on a product measure (Fubini for
    products): the integral of [f xy.1 * g xy.2] on [px \x py] equals
    [qbs_expect px f * qbs_expect py g]. Note: this is pure product-
    measure factorization and has no independence hypothesis; the
    [qbs_indep] predicate is not involved. *)
Lemma qbs_pair_integral_factorization (X Y : qbsType R)
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
  (qbs_expect X px f * qbs_expect Y py g).
Proof.
rewrite qbs_pair_integral_iterated //.
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

(** Variance of sum of independent random variables.
    For independent X, Y (on separate probability spaces px, py),
    define the sum f(x) + g(y) on the product space. The variance
    of this sum w.r.t. the product measure mu_px x mu_py equals
    Var_px(f) + Var_py(g).
    Key idea: varianceD gives
      Var(F+G) = Var(F) + Var(G) + 2*Cov(F,G)
    For independent F, G (functions of separate coordinates),
    Cov(F,G) = E[FG] - E[F]*E[G] = 0 by Fubini (the product
    integral of f(r1)*g(r2) factors as E[f]*E[g]).
    Also, Var(F) w.r.t. product = Var_px(f) since F only depends
    on the first coordinate, and similarly Var(G) = Var_py(g). *)

(* Variance of f(x) + g(y) on the product space w.r.t. product measure *)
Definition qbs_pair_variance (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (f : X -> R) (g : Y -> R) : \bar R :=
  variance (qbs_prob_mu px \x qbs_prob_mu py)
    (fun rr : mR * mR =>
      (f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2))%R).

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
rewrite -(cstE _ (h x)%:E).
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
rewrite -(cstE _ (h y)%:E).
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
  rewrite -(cstE _ (h x * h x)%:E).
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
  rewrite -(cstE _ (h y * h y)%:E).
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

Lemma qbs_variance_indep_sum (X Y : qbsType R)
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
  (f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2))%R) = (F \+ G)%R.
  by apply: funext => rr.
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

(** Commutativity of the probability monad (Proposition 22).
    The two ways of combining P(X) x P(Y) -> P(X x Y) agree:
    integrating h w.r.t. the product mu_p x mu_q with alphas
    (alpha_p, alpha_q) equals integrating h(swap) w.r.t. mu_q x mu_p
    with alphas (alpha_q, alpha_p). Follows from Fubini's theorem. *)

Lemma qbs_pair_integral_comm (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
    setT (qbs_pair_fun p q h))
  (hint' : (qbs_prob_mu q \x qbs_prob_mu p).-integrable
    setT (qbs_pair_fun q p (fun yx => h (yx.2, yx.1)))) :
  qbs_pair_integral X Y p q h =
  qbs_pair_integral Y X q p (fun yx => h (yx.2, yx.1)).
Proof.
rewrite /qbs_pair_integral.
set f := (fun rr : mR * mR =>
  h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2)).
transitivity (\int[qbs_prob_mu p]_r1 \int[qbs_prob_mu q]_r2 f (r1, r2)).
  symmetry; exact: integral12_prod_meas1.
transitivity (\int[qbs_prob_mu q]_r2 \int[qbs_prob_mu p]_r1 f (r1, r2)).
  exact: Fubini.
set g := (fun rr : mR * mR =>
  h (qbs_prob_alpha p rr.2, qbs_prob_alpha q rr.1)).
have fg : forall r2 r1, f (r1, r2) = g (r2, r1) by [].
under eq_integral do under eq_integral do rewrite fg.
have hint'' : (qbs_prob_mu q \x qbs_prob_mu p).-integrable setT g.
  rewrite /g /qbs_pair_fun in hint' |- *.
  exact: hint'.
rewrite -(@integral12_prod_meas1 _ _ _ _ _
  (qbs_prob_mu q) (qbs_prob_mu p) g hint'').
by apply: eq_integral => r1 _; apply: eq_integral => r2 _.
Qed.

(** Product measure integral equals iterated QBS integral.
    The integral of h against qbs_prob_pair p q (the explicit product
    measure on prodQ X Y) equals the iterated QBS integral
    ∫_p (fun x => ∫_q (fun y => h(x,y))).
    This is the sense in which the product measure construction
    agrees with the monadic bind: integration against the product
    equals iterated integration (Fubini). *)

(** Product measure = iterated integral (bind). *)
Lemma qbs_prob_pair_measure_eq_bind (X Y : qbsType R)
    (p : qbs_prob X) (q : qbs_prob Y)
    (h : X * Y -> \bar R)
    (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
      setT (qbs_pair_fun p q h))
    (hint_g : (qbs_pair_mu_build p q).-integrable setT
      (fun r : mR => h (qbs_pair_alpha p q r))) :
  qbs_integral (prodQ X Y) (qbs_prob_pair X Y p q) h =
  qbs_integral X p (fun x =>
    qbs_integral Y q (fun y => h (x, y))).
Proof.
rewrite /qbs_integral /=.
(* Go through the qbs_pair_integral (integration over the product measure) *)
transitivity (qbs_pair_integral X Y p q h);
  last exact: (qbs_pair_integral_iterated hint).
rewrite /qbs_pair_integral.
set mu_pq := qbs_prob_mu p \x qbs_prob_mu q.
have hint' := hint.
move/integrableP : hint' => [hm_pqf _].
(* Rewrite RHS integrand using encode_RRK *)
have fg_eq : forall rr : mR * mR,
  h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2) =
  h (qbs_pair_alpha p q (@encode_RR_mR R rr)).
  by move=> rr; rewrite /qbs_pair_alpha encode_RR_mRK.
under [RHS]eq_integral do rewrite fg_eq.
(* Now both sides have integrand h(pair_alpha(_)) *)
set g := (fun x : mR => h (qbs_pair_alpha p q x)).
(* Use integral_pushforward to convert the pushforward integral *)
have hm_enc : measurable_fun
  [set: Datatypes_prod__canonical__measurable_structure_Measurable mR mR]
  (@encode_RR_mR R).
  exact: measurable_RR_to_R.
rewrite -[RHS](@integral_pushforward _ _ _ mR R
  (@encode_RR_mR R) hm_enc mu_pq setT g _ _ measurableT).
- (* Measures are extensionally equal *)
  by [].
- (* Measurability of g *)
  by move/integrableP : hint_g => [].
- (* Integrability of g o encode_RR *)
  rewrite preimage_setT.
  suff -> : g \o @encode_RR_mR R = qbs_pair_fun p q h by exact: hint.
  apply: funext => rr.
  rewrite /g /qbs_pair_alpha /qbs_pair_fun /=.
  by congr (h (_, _));
    [congr (qbs_prob_alpha p) | congr (qbs_prob_alpha q)];
    exact: (congr1 fst (encode_RR_mRK rr))
        || exact: (congr1 snd (encode_RR_mRK rr)).
Qed.

End pair_qbs_measure.

Arguments qbs_prob_pair {R X Y}.
Arguments qbs_pair_integral {R X Y}.
Arguments qbs_pair_fun {R X Y}.
Arguments qbs_indep {R X Y Z}.
Arguments qbs_pair_variance {R X Y}.
