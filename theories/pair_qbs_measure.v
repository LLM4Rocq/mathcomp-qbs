(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal boolp classical_sets
  numfun measure lebesgue_integral lebesgue_stieltjes_measure probability
  hoelder functions.
From QBS Require Import quasi_borel probability_qbs qbs_monad standard_borel.

(**md**************************************************************************)
(* # Product Measures on QBS Probability Spaces                               *)
(*                                                                            *)
(* The monadic product monadP_pair p q of qbs_monad.v is represented by the   *)
(* product measure mu_p \x mu_q pushed to R along R * R -> R                  *)
(* (qbs_prob_pairE), so that its integrals are integrals against mu_p \x mu_q *)
(* and Fubini and the variance of mathcomp-analysis apply.                    *)
(*                                                                            *)
(* ```                                                                        *)
(*      qbs_prob_pair p q == the encoded product, equal to monadP_pair p q    *)
(*                            (qbs_prob_pairE)                                *)
(*      qbs_pair_alpha p q == the pairing map mR -> X * Y of the two alphas   *)
(*   qbs_pair_mu_build p q == the probability measure on mR obtained by       *)
(*                            pushing mu_p \x mu_q through encode_RR          *)
(*     qbs_pair_fun p q h == h composed with the two alphas, on mR * mR       *)
(*   integral_prod_{fst,snd,mul} == integrals of h rr.1, h rr.2, h1 rr.1 *    *)
(*                            h2 rr.2 against a product of probabilities      *)
(*   monadP_pair_integrable, monadP_pair_integral, monadP_pair_iterated,      *)
(*   monadP_pair_mul == integrability and integrals against monadP_pair p q:  *)
(*                            product measure, Fubini, E[f g] = E[f] E[g]     *)
(*   qbs_indep p f g == independence of f and g under p                       *)
(*   qbs_indep_rect, qbs_integral_indepM == product rule on rectangles and    *)
(*                            E[phi(f) psi(g)] = E[phi(f)] E[psi(g)]          *)
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

(** ** Integrals against the product *)

Definition qbs_pair_fun (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y)
    (h : X * Y -> \bar R) (rr : mR * mR) : \bar R :=
  h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).

Section monadP_pair_integral.
Context (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y).
Context (h : X * Y -> \bar R) (mh : qbs_measurable (prodQ X Y) h).

Let mg : measurable_fun [set: mR] (h \o qbs_pair_alpha p q).
Proof. exact: mh _ (qbs_pair_alpha_random p q). Qed.

Let pair_funE : qbs_pair_fun p q h = (h \o qbs_pair_alpha p q) \o encode_RR_mR.
Proof. by apply/funext => rr; rewrite /= /qbs_pair_alpha encode_RR_mRK. Qed.

Lemma monadP_pair_integrable :
  qbs_integrable (prodQ X Y) (monadP_pair p q) h <->
  (qbs_prob_mu p \x qbs_prob_mu q).-integrable setT (qbs_pair_fun p q h).
Proof.
rewrite qbs_prob_pairE qbs_integrable_mk// pair_funE.
have mabs : measurable_fun [set: mR] (abse \o (h \o qbs_pair_alpha p q)).
  exact: measurableT_comp.
split=> /integrableP[_ fin]; apply/integrableP; split.
- exact: measurableT_comp mg measurable_RR_to_R.
- move: fin; rewrite -[X in X < _ -> _]/(\int[pushforward _ encode_RR_mR]_x _).
  rewrite ge0_integral_pushforward//.
    exact: measurable_RR_to_R.
  by move=> ? _; exact: abse_ge0.
- exact: mg.
- rewrite -[X in X < _]/(\int[pushforward _ encode_RR_mR]_x _).
  rewrite ge0_integral_pushforward//.
    exact: measurable_RR_to_R.
  by move=> ? _; exact: abse_ge0.
Qed.

Lemma monadP_pair_integral :
  (qbs_prob_mu p \x qbs_prob_mu q).-integrable setT (qbs_pair_fun p q h) ->
  qbs_integral (prodQ X Y) (monadP_pair p q) h =
  \int[qbs_prob_mu p \x qbs_prob_mu q]_rr qbs_pair_fun p q h rr.
Proof.
move=> hint; rewrite qbs_prob_pairE qbs_integral_mk// pair_funE.
rewrite -[LHS]/(\int[pushforward _ encode_RR_mR]_x _).
rewrite (integral_pushforward measurable_RR_to_R mg _ measurableT)//.
by rewrite preimage_setT -pair_funE.
Qed.

(** Fubini: integrating against the product is iterated integration. *)
Lemma monadP_pair_iterated :
  qbs_integrable (prodQ X Y) (monadP_pair p q) h ->
  qbs_integral (prodQ X Y) (monadP_pair p q) h =
  qbs_integral X p (fun x => qbs_integral Y q (fun y => h (x, y))).
Proof.
move=> /monadP_pair_integrable hint.
rewrite monadP_pair_integral// -(integral12_prod_meas1 hint).
by apply: eq_integral => x _; rewrite /fubini_F /qbs_pair_fun.
Qed.

End monadP_pair_integral.

(** E[f(x) g(y)] = E[f] E[g] on the product. *)
Lemma monadP_pair_mul (X Y : qbsType R) (p : qbs_prob X) (q : qbs_prob Y)
    (f : X -> R) (g : Y -> R) :
  qbs_measurable (prodQ X Y) (fun xy => (f xy.1 * g xy.2)%:E) ->
  qbs_integrable X p (EFin \o f) -> qbs_integrable Y q (EFin \o g) ->
  qbs_integrable (prodQ X Y) (monadP_pair p q)
    (fun xy => (f xy.1 * g xy.2)%:E) ->
  qbs_integral (prodQ X Y) (monadP_pair p q)
    (fun xy => (f xy.1 * g xy.2)%:E) = qbs_expect X p f * qbs_expect Y q g.
Proof.
move=> mfg hf hg /(monadP_pair_integrable _ _ mfg) hfg.
by rewrite monadP_pair_integral//; exact: (integral_prod_mul hf hg hfg).
Qed.

(** ** Independence *)

Definition qbs_indep (X Y Z : qbsType R) (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y) : Prop :=
  monadP_map (qbs_pair f g) p = monadP_pair (monadP_map f p) (monadP_map g p).

(** For real-valued variables, qbs_indep gives the classical product rule
    on Borel rectangles. *)
Lemma qbs_indep_rect (Z : qbsType R) (p : qbs_prob Z)
    (f g : qbsHomType Z (realQ R)) (A B : set mR) :
  measurable A -> measurable B -> qbs_indep p f g ->
  qbs_prob_event Z p [set z | A (f z) /\ B (g z)] =
  qbs_prob_event Z p (f @^-1` A) * qbs_prob_event Z p (g @^-1` B).
Proof.
move=> mA mB hind.
have sA : sigma_Mx (X := realQ R) A := sigma_Mx_measQ mA.
have sB : sigma_Mx (X := realQ R) B := sigma_Mx_measQ mB.
have mU : sigma_Mx (X := prodQ (realQ R) (realQ R)) (A `*` B).
  move=> b [hb1 hb2].
  have -> : b @^-1` (A `*` B) =
      (fun r => (b r).1) @^-1` A `&` (fun r => (b r).2) @^-1` B by [].
  by apply: measurableI; [exact: sA _ hb1|exact: sB _ hb2].
transitivity (qbs_prob_event _ (monadP_map (qbs_pair f g) p) (A `*` B)).
  by rewrite (monadP_map_event (qbs_pair f g) p mU).
rewrite hind qbs_prob_pairE qbs_prob_pair_event//.
set p1 := monadP_map f p; set p2 := monadP_map g p.
have mA1 : measurable (qbs_prob_alpha p1 @^-1` A).
  by have := sA _ (qbs_prob_alpha_random p1).
have mB2 : measurable (qbs_prob_alpha p2 @^-1` B).
  by have := sB _ (qbs_prob_alpha_random p2).
rewrite (_ : [set rr | _] = qbs_prob_alpha p1 @^-1` A `*`
    qbs_prob_alpha p2 @^-1` B)// product_measure1E//.
by congr (_ * _); exact: monadP_map_event.
Qed.

(** Independence factorization: E[phi(f) psi(g)] = E[phi(f)] E[psi(g)]. *)
Lemma qbs_integral_indepM (X Y Z : qbsType R) (p : qbs_prob Z)
    (f : qbsHomType Z X) (g : qbsHomType Z Y) (phi : X -> R) (psi : Y -> R) :
  qbs_indep p f g ->
  qbs_measurable X (EFin \o phi) -> qbs_measurable Y (EFin \o psi) ->
  qbs_integrable Z p (EFin \o (phi \o f)) ->
  qbs_integrable Z p (EFin \o (psi \o g)) ->
  qbs_integrable Z p (fun z => (phi (f z) * psi (g z))%:E) ->
  qbs_expect Z p (fun z => phi (f z) * psi (g z))%R =
  qbs_expect Z p (phi \o f) * qbs_expect Z p (psi \o g).
Proof.
move=> hind mphi mpsi hphi hpsi hprod.
have mfg : qbs_measurable (prodQ X Y) (fun xy => (phi xy.1 * psi xy.2)%:E).
  move=> a [ha1 ha2]; rewrite (_ : (fun r => _) =
    (fun r => (phi (a r).1)%:E * (psi (a r).2)%:E)).
    by apply/funext => r; rewrite EFinM.
  by apply: emeasurable_funM; [exact: mphi _ ha1|exact: mpsi _ ha2].
have -> : qbs_expect Z p (fun z => phi (f z) * psi (g z))%R =
    qbs_integral _ (monadP_map (qbs_pair f g) p)
      (fun xy => (phi xy.1 * psi xy.2)%:E).
  by rewrite monadP_map_integral.
rewrite hind monadP_pair_mul//.
- exact/(monadP_map_integrable _ _ mphi).
- exact/(monadP_map_integrable _ _ mpsi).
- by rewrite -hind; exact/(monadP_map_integrable _ _ mfg).
- by rewrite /qbs_expect !monadP_map_integral.
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

