(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal boolp classical_sets
  numfun measure lebesgue_integral lebesgue_stieltjes_measure probability
  hoelder functions.
From QBS Require Import quasi_borel probability_qbs qbs_monad standard_borel.

(**md**************************************************************************)
(* # Product Measures on QBS Probability Spaces                               *)
(*                                                                            *)
(* A concrete representation of the product of QBS probabilities, through     *)
(* which integrals reduce to integrals on the product measure mu_p \x mu_q,   *)
(* so that Fubini and the variance of mathcomp-analysis apply.                *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_prob_pair p q == product QBS probability on prodQ X Y, the           *)
(*                            pushforward of mu_p \x mu_q along R * R -> R;   *)
(*                            it is equal to monadP_pair                      *)
(*                            (qbs_prob_pairE)                                *)
(*      qbs_pair_alpha p q == the pairing map mR -> X * Y of the two alphas   *)
(*   qbs_pair_mu_build p q == the probability measure on mR obtained by       *)
(*                            pushing mu_p \x mu_q through encode_RR          *)
(*     qbs_pair_fun p q h == h composed with the two alphas, on mR * mR       *)
(*   integral_prod_{fst,snd,mul} == integrals of h rr.1, h rr.2, h1 rr.1 *    *)
(*                            h2 rr.2 against a product of probabilities      *)
(*   qbs_indep p f g == independence of f and g under p                       *)
(*   qbs_pair_variance px py f g == variance of f(x) + g(y) on product        *)
(* ```                                                                        *)
(******************************************************************************)

Import Num.Theory measurable_realfun.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section product_measure.
Variable R : realType.

Local Abbreviation mR := (measurableTypeR R).

Implicit Types (X Y : qbsType R).

(** Product of QBS probability spaces.
    Given p : qbs_prob X and q : qbs_prob Y, construct
    qbs_prob (prodQ X Y) with alpha pairing the two alphas and
    measure being the product measure. The measure lives on R: using
    R ~ R x R (standard_borel.v), mu_p \x mu_q is pushed through
    encode_RR to obtain a probability measure on mR. *)

Section pair_mu_build.
Variables (X Y : qbsType R).
Variables (p : qbs_prob X) (q : qbs_prob Y).

Let mu_p := qbs_prob_mu p.
Let mu_q := qbs_prob_mu q.

Definition pf_mu (A : set mR) : \bar R :=
  (mu_p \x mu_q) (encode_RR_mR @^-1` A).

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

(** Product measure on mR for the QBS product. *)
Definition qbs_pair_mu_build : probability mR R := pf_mu.

End pair_mu_build.

Definition qbs_pair_alpha (X Y : qbsType R)
    (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r =>
    let uv := decode_RR_mR r in
    (qbs_prob_alpha p uv.1, qbs_prob_alpha q uv.2).

Lemma qbs_pair_alpha_random (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) :
  qbs_Mx (s := prodQ X Y) (qbs_pair_alpha p q).
Proof.
rewrite /qbs_Mx /=; split.
  have -> : (fun r => (qbs_pair_alpha p q r).1) =
      qbs_prob_alpha p \o (fst \o decode_RR_mR) by [].
  apply: qbs_Mx_compT; first exact: (qbs_prob_alpha_random p).
  apply: measurableT_comp; first exact: measurable_fst.
  exact: measurable_R_to_RR.
have -> : (fun r => (qbs_pair_alpha p q r).2) =
    qbs_prob_alpha q \o (snd \o decode_RR_mR) by [].
apply: qbs_Mx_compT; first exact: (qbs_prob_alpha_random q).
apply: measurableT_comp; first exact: measurable_snd.
exact: measurable_R_to_RR.
Qed.

Definition qbs_prob_pair (X Y : qbsType R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha p q)
    (qbs_pair_mu_build p q)
    (qbs_pair_alpha_random p q).

Local Open Scope ereal_scope.

(** Computation rule for [qbs_prob_pair]. *)
Lemma qbs_prob_pair_event (X Y : qbsType R) (p : qbs_prob X)
    (q : qbs_prob Y) (U : set (prodQ X Y)) : sigma_Mx U ->
  qbs_prob_event _ (qbs_prob_pair p q) U =
  (qbs_prob_mu p \x qbs_prob_mu q)
    [set rr | U (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2)].
Proof.
move=> mU; rewrite /qbs_prob_pair qbs_prob_event_mk //= /qbs_pair_mu_build.
rewrite /pf_mu; congr (_ _); apply/seteqP; split=> rr /=;
  by rewrite /qbs_pair_alpha encode_RR_mRK.
Qed.

(** The encoded product agrees with the monadic product
    p >>= (fun x => strength (x, q)) of qbs_monad.v. *)
Lemma qbs_prob_pairE (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y) :
  monadP_pair p q = qbs_prob_pair p q.
Proof.
apply/qbs_prob_eqP => U mU; rewrite monadP_pair_event// qbs_prob_pair_event//.
rewrite /product_measure1 /=; apply: eq_integral => r _; congr (_ _).
by apply/seteqP; split=> t /=; rewrite /xsection /= inE.
Qed.

Local Open Scope ereal_scope.

(** ** Integrals on a product of probabilities on mR *)

Section prod_meas.
Variables (mu1 mu2 : probability mR R).

Lemma integral_prod_fst (h : mR -> \bar R) :
  (mu1 \x mu2).-integrable setT (fun rr : mR * mR => h rr.1) ->
  \int[mu1 \x mu2]_rr h rr.1 = \int[mu1]_x h x.
Proof.
move=> hi; rewrite -(integral12_prod_meas1 hi); apply: eq_integral => x _.
rewrite /fubini_F -(cstE _ (h x)) integral_cst//.
by rewrite [X in _ * X](probability_setT mu2) mule1.
Qed.

Lemma integral_prod_snd (h : mR -> \bar R) :
  (mu1 \x mu2).-integrable setT (fun rr : mR * mR => h rr.2) ->
  \int[mu1 \x mu2]_rr h rr.2 = \int[mu2]_y h y.
Proof.
move=> hi; rewrite -(integral21_prod_meas1 hi); apply: eq_integral => y _.
rewrite /fubini_G -(cstE _ (h y)) integral_cst//.
by rewrite [X in _ * X](probability_setT mu1) mule1.
Qed.

Lemma integral_prod_mul (h1 h2 : mR -> R) :
  mu1.-integrable setT (EFin \o h1) -> mu2.-integrable setT (EFin \o h2) ->
  (mu1 \x mu2).-integrable setT (fun rr : mR * mR => (h1 rr.1 * h2 rr.2)%:E) ->
  \int[mu1 \x mu2]_rr (h1 rr.1 * h2 rr.2)%:E =
  \int[mu1]_x (h1 x)%:E * \int[mu2]_y (h2 y)%:E.
Proof.
move=> i1 i2 i12; rewrite -(integral12_prod_meas1 i12).
transitivity (\int[mu1]_x ((h1 x)%:E * \int[mu2]_y (h2 y)%:E)).
  apply: eq_integral => x _; rewrite /fubini_F /=.
  by under eq_integral do rewrite EFinM; rewrite integralZl.
by rewrite -(fineK (integrable_fin_num measurableT i2)) integralZr.
Qed.

End prod_meas.

(** ** Integrals against the encoded product *)

Definition qbs_pair_fun (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y)
    (h : X * Y -> \bar R) (rr : mR * mR) : \bar R :=
  h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).

Lemma qbs_prob_pair_integral (X Y : qbsType R) (p : qbs_prob X)
    (q : qbs_prob Y) (h : X * Y -> \bar R) :
  qbs_measurable (prodQ X Y) h ->
  (qbs_prob_mu p \x qbs_prob_mu q).-integrable setT (qbs_pair_fun p q h) ->
  qbs_integral (prodQ X Y) (qbs_prob_pair p q) h =
  \int[qbs_prob_mu p \x qbs_prob_mu q]_rr qbs_pair_fun p q h rr.
Proof.
move=> mh0 hint; have /integrableP[mh _] := hint.
have hg : (fun r => h (qbs_pair_alpha p q r)) =
    qbs_pair_fun p q h \o decode_RR_mR by [].
have mg : measurable_fun [set: mR] (fun r => h (qbs_pair_alpha p q r)).
  by rewrite hg; exact: measurableT_comp mh measurable_R_to_RR.
have fg rr :
    qbs_pair_fun p q h rr = h (qbs_pair_alpha p q (encode_RR_mR rr)).
  by rewrite /qbs_pair_alpha encode_RR_mRK.
rewrite /qbs_prob_pair qbs_integral_mk //= /qbs_pair_mu_build.
under [RHS]eq_integral do rewrite fg.
rewrite -[RHS](integral_pushforward measurable_RR_to_R mg _ measurableT)//.
rewrite preimage_setT (_ : _ \o _ = qbs_pair_fun p q h)//.
by apply/funext => rr; rewrite /= -fg.
Qed.

(** Fubini: integrating against the product is iterated integration. *)
Lemma qbs_prob_pair_iterated (X Y : qbsType R) (p : qbs_prob X)
    (q : qbs_prob Y) (h : X * Y -> \bar R) :
  qbs_measurable (prodQ X Y) h ->
  (qbs_prob_mu p \x qbs_prob_mu q).-integrable setT (qbs_pair_fun p q h) ->
  qbs_integral (prodQ X Y) (qbs_prob_pair p q) h =
  qbs_integral X p (fun x => qbs_integral Y q (fun y => h (x, y))).
Proof.
move=> mh hint; rewrite qbs_prob_pair_integral// -(integral12_prod_meas1 hint).
by apply: eq_integral => x _; rewrite /fubini_F /qbs_pair_fun.
Qed.

(** E[f(x) g(y)] = E[f] E[g] on the product. *)
Lemma qbs_prob_pair_mul (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y)
    (f : X -> R) (g : Y -> R) :
  qbs_measurable (prodQ X Y) (fun xy => (f xy.1 * g xy.2)%:E) ->
  (qbs_prob_mu p).-integrable setT (EFin \o (f \o qbs_prob_alpha p)) ->
  (qbs_prob_mu q).-integrable setT (EFin \o (g \o qbs_prob_alpha q)) ->
  (qbs_prob_mu p \x qbs_prob_mu q).-integrable setT
    (qbs_pair_fun p q (fun xy => (f xy.1 * g xy.2)%:E)) ->
  qbs_integral (prodQ X Y) (qbs_prob_pair p q)
    (fun xy => (f xy.1 * g xy.2)%:E) = qbs_expect X p f * qbs_expect Y q g.
Proof.
move=> mfg hf hg hfg; rewrite qbs_prob_pair_integral//.
exact: (integral_prod_mul hf hg hfg).
Qed.

(** ** Independence *)

Definition qbs_indep (X Y Z : qbsType R) (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y) : Prop :=
  monadP_map (qbs_pair f g) p = qbs_prob_pair (monadP_map f p) (monadP_map g p).

(** For real-valued variables, qbs_indep gives the classical product rule
    on Borel rectangles. *)
Lemma qbs_indep_rect (Z : qbsType R) (p : qbs_prob Z)
    (f g : qbsHomType Z (realQ R)) (A B : set mR) :
  measurable A -> measurable B -> qbs_indep p f g ->
  qbs_prob_event Z p [set z | A (f z) /\ B (g z)] =
  qbs_prob_event Z p (f @^-1` A) * qbs_prob_event Z p (g @^-1` B).
Proof.
move=> mA mB hind.
have sA : sigma_Mx (X := realQ R) A.
  by move=> b hb; have := hb measurableT A mA; rewrite setTI.
have sB : sigma_Mx (X := realQ R) B.
  by move=> b hb; have := hb measurableT B mB; rewrite setTI.
have mU : sigma_Mx (X := prodQ (realQ R) (realQ R)) (A `*` B).
  move=> b [hb1 hb2].
  have -> : b @^-1` (A `*` B) =
      (fun r => (b r).1) @^-1` A `&` (fun r => (b r).2) @^-1` B by [].
  apply: measurableI.
    by have := hb1 measurableT A mA; rewrite setTI.
  by have := hb2 measurableT B mB; rewrite setTI.
transitivity (qbs_prob_event _ (monadP_map (qbs_pair f g) p) (A `*` B)).
  by rewrite (monadP_map_event (qbs_pair f g) p mU).
rewrite hind qbs_prob_pair_event//.
set p1 := monadP_map f p; set p2 := monadP_map g p.
have mA1 : measurable (qbs_prob_alpha p1 @^-1` A).
  have := qbs_prob_alpha_random p1 measurableT A mA.
  by rewrite setTI.
have mB2 : measurable (qbs_prob_alpha p2 @^-1` B).
  have := qbs_prob_alpha_random p2 measurableT B mB.
  by rewrite setTI.
rewrite (_ : [set rr | _] = qbs_prob_alpha p1 @^-1` A `*`
    qbs_prob_alpha p2 @^-1` B)// product_measure1E//.
congr (_ * _).
  exact: (monadP_map_event f p sA).
exact: (monadP_map_event g p sB).
Qed.

(** Independence factorization: E[phi(f) psi(g)] = E[phi(f)] E[psi(g)]. *)
Lemma qbs_integral_indepM (X Y Z : qbsType R) (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y) (phi : X -> R) (psi : Y -> R) :
  qbs_indep p f g ->
  qbs_measurable (prodQ X Y) (fun xy => (phi xy.1 * psi xy.2)%:E) ->
  (qbs_prob_mu (monadP_map f p)).-integrable setT
    (EFin \o (phi \o qbs_prob_alpha (monadP_map f p))) ->
  (qbs_prob_mu (monadP_map g p)).-integrable setT
    (EFin \o (psi \o qbs_prob_alpha (monadP_map g p))) ->
  (qbs_prob_mu (monadP_map f p) \x qbs_prob_mu (monadP_map g p)).-integrable
    setT (qbs_pair_fun (monadP_map f p) (monadP_map g p)
      (fun xy => (phi xy.1 * psi xy.2)%:E)) ->
  qbs_integral Z p (fun z => (phi (f z) * psi (g z))%:E) =
  qbs_expect X (monadP_map f p) phi * qbs_expect Y (monadP_map g p) psi.
Proof.
move=> hind hmeas hphi hpsi hprod.
rewrite -[LHS](monadP_map_integral (qbs_pair f g) p hmeas) hind.
exact: qbs_prob_pair_mul.
Qed.

(** ** Variance of independent sums *)

Definition qbs_pair_variance (X Y : qbsType R)
  (px : qbs_prob X) (py : qbs_prob Y) (f : X -> R) (g : Y -> R) : \bar R :=
  variance (qbs_prob_mu px \x qbs_prob_mu py)
    (fun rr : mR * mR =>
      (f (qbs_prob_alpha px rr.1) + g (qbs_prob_alpha py rr.2))%R).

Let L2_integrable d (T : measurableType d)
    (m : {measure set T -> \bar R}%R) (h : T -> R) :
  m setT \is a fin_num -> h \in Lfun m 2 -> m.-integrable setT (EFin \o h).
Proof. by move=> fm /(Lfun_subset12 fm) /Lfun1_integrable. Qed.

Lemma qbs_pair_varianceD (X Y : qbsType R)
    (px : qbs_prob X) (py : qbs_prob Y) (f : X -> R) (g : Y -> R) :
  let mu := (qbs_prob_mu px \x qbs_prob_mu py) in
  (fun rr : mR * mR => f (qbs_prob_alpha px rr.1)) \in Lfun mu 2 ->
  (fun rr : mR * mR => g (qbs_prob_alpha py rr.2)) \in Lfun mu 2 ->
  f \o qbs_prob_alpha px \in Lfun (qbs_prob_mu px) 2 ->
  g \o qbs_prob_alpha py \in Lfun (qbs_prob_mu py) 2 ->
  qbs_pair_variance px py f g = qbs_variance X px f + qbs_variance Y py g.
Proof.
move=> mu hF2 hG2 hf2 hg2.
set F := fun rr : mR * mR => f (qbs_prob_alpha px rr.1).
set G := fun rr : mR * mR => g (qbs_prob_alpha py rr.2).
have mu_fin : mu setT \is a fin_num.
  by rewrite /mu -(@setXTT mR mR) product_measure1E //= !probability_setT mule1.
have fin1 (m : probability mR R) : m setT \is a fin_num.
  by rewrite probability_setT.
have EF : 'E_mu[F] = 'E_(qbs_prob_mu px)[(f \o qbs_prob_alpha px)].
  by rewrite !unlock; exact: (integral_prod_fst
    (h := fun x => (f (qbs_prob_alpha px x))%:E) (L2_integrable mu_fin hF2)).
have EG : 'E_mu[G] = 'E_(qbs_prob_mu py)[(g \o qbs_prob_alpha py)].
  by rewrite !unlock; exact: (integral_prod_snd
    (h := fun y => (g (qbs_prob_alpha py y))%:E) (L2_integrable mu_fin hG2)).
rewrite /qbs_pair_variance -[fun rr => _]/(F \+ G)%R varianceD//.
rewrite covarianceE ?(Lfun2_mul_Lfun1 hF2 hG2) ?(Lfun_subset12 mu_fin)//.
have -> : 'E_mu[(F \* G)%R] = 'E_mu[F] * 'E_mu[G].
  rewrite EF EG !unlock.
  apply: (integral_prod_mul (h1 := f \o qbs_prob_alpha px)
    (h2 := g \o qbs_prob_alpha py));
    [exact: L2_integrable (fin1 (qbs_prob_mu px)) hf2
    |exact: L2_integrable (fin1 (qbs_prob_mu py)) hg2|].
  by apply/Lfun1_integrable; exact: Lfun2_mul_Lfun1.
have EFG : 'E_mu[F] * 'E_mu[G] \is a fin_num.
  by rewrite fin_numM ?expectation_fin_num ?(Lfun_subset12 mu_fin).
rewrite subee// mule0 adde0.
rewrite /qbs_variance !varianceE ?(Lfun_subset12 (fin1 _))//.
rewrite -/mu EF EG; congr (_ - _ + (_ - _)); rewrite !unlock.
  exact: (integral_prod_fst (Lfun2_integrable_sqr hF2)
    (h := fun x => ((f (qbs_prob_alpha px x)) ^+ 2)%:E)).
exact: (integral_prod_snd (Lfun2_integrable_sqr hG2)
  (h := fun y => ((g (qbs_prob_alpha py y)) ^+ 2)%:E)).
Qed.

End product_measure.

