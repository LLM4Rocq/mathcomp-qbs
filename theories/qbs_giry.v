(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals classical_sets boolp
  ereal measurable_structure measurable_function measure measure_function
  probability_measure borel_hierarchy lebesgue_stieltjes_measure
  lebesgue_integral lebesgue_measure.
From QBS Require Import quasi_borel measure_qbs_adjunction probability_qbs.

(**md**************************************************************************)
(* # Connection between QBS Probability Monad and Giry Monad                  *)
(*                                                                            *)
(* The L functor extends to probability: L(P_QBS(R(M))) -> Giry(M).          *)
(* For standard Borel spaces, this is an isomorphism.                         *)
(*                                                                            *)
(* Following Heunen-Kammar-Staton-Yang (2017), Proposition 22.3:              *)
(* the functor L extends faithfully from Kleisli(P_QBS) to Kleisli(Giry).    *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_to_giry_mu p == pushforward measure on M from qbs_prob(R(M))        *)
(*   qbs_to_giry p    == packaged as probability M R                          *)
(*   giry_to_qbs P    == inverse map using standard Borel encode/decode       *)
(*   qbs_to_giryK == qbs_to_giry (giry_to_qbs P) = P                  *)
(*   giry_to_qbsK == giry_to_qbs (qbs_to_giry p) ~ p (equiv)         *)
(*   qbs_integral_giry   == qbs_integral p f = \int[qbs_to_giry p] f        *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_giry.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(** Forward map: qbs_prob(R(M)) -> probability M R.
    Given a QBS probability triple (alpha, mu) on R(M), the
    pushforward mu o alpha^{-1} is a probability on M. *)

Section qbs_to_giry.
Context d (M : measurableType d).
Variable (p : qbs_prob (R_qbs R M)).

Let alpha := qbs_prob_alpha p.
Let mu : probability mR R := qbs_prob_mu p.

Let alpha_meas : measurable_fun setT alpha.
Proof. exact: (qbs_prob_alpha_random p). Qed.

Definition qbs_to_giry_mu (A : set M) : \bar R :=
  mu (alpha @^-1` A).

Lemma qbs_to_giry_mu0 : qbs_to_giry_mu set0 = 0.
Proof. by rewrite /qbs_to_giry_mu preimage_set0 measure0. Qed.

Lemma qbs_to_giry_mu_ge0 A : 0 <= qbs_to_giry_mu A.
Proof.
by apply: measure_ge0; rewrite -[X in measurable X]setTI; exact: alpha_meas.
Qed.

Lemma qbs_to_giry_mu_semi_sigma_additive :
  semi_sigma_additive qbs_to_giry_mu.
Proof.
move=> F mF tF mUF; rewrite /qbs_to_giry_mu preimage_bigcup.
apply: measure_semi_sigma_additive.
- by move=> n; rewrite -[X in measurable X]setTI; exact: alpha_meas.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: alpha_meas.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  qbs_to_giry_mu qbs_to_giry_mu0 qbs_to_giry_mu_ge0
  qbs_to_giry_mu_semi_sigma_additive.

Lemma qbs_to_giry_mu_setT : qbs_to_giry_mu setT = 1%:E.
Proof.
by rewrite /qbs_to_giry_mu preimage_setT probability_setT.
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _
  qbs_to_giry_mu qbs_to_giry_mu_setT.

End qbs_to_giry.

(** Forward: QBS probability to Giry probability. *)
Definition qbs_to_giry d (M : measurableType d)
    (p : qbs_prob (R_qbs R M)) : probability M R :=
  [the probability M R of qbs_to_giry_mu p].

(** Backward map: probability M R -> qbs_prob(R(M)).
    Requires standard Borel witnesses: encode : M -> R, decode : R -> M
    with decode o encode = id.
    Given P : probability M R, the triple (decode, P o encode^{-1})
    is a QBS probability on R(M). *)

Section giry_to_qbs.
Context d (M : measurableType d).
Variables (encode : M -> mR) (decode : mR -> M).
Hypothesis encode_meas : measurable_fun setT encode.
Hypothesis decode_meas : measurable_fun setT decode.
Variable (P : probability M R).

Let pf_mu (A : set mR) : \bar R := P (encode @^-1` A).

Let pf_mu0 : pf_mu set0 = 0.
Proof. by rewrite /pf_mu preimage_set0 measure0. Qed.

Let pf_mu_ge0 A : 0 <= pf_mu A.
Proof.
by apply: measure_ge0; rewrite -[X in measurable X]setTI; exact: encode_meas.
Qed.

Let pf_mu_sigma_additive : semi_sigma_additive pf_mu.
Proof.
move=> F mF tF mUF; rewrite /pf_mu preimage_bigcup.
apply: measure_semi_sigma_additive.
- by move=> n; rewrite -[X in measurable X]setTI; exact: encode_meas.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: encode_meas.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  pf_mu pf_mu0 pf_mu_ge0 pf_mu_sigma_additive.

Let pf_mu_setT : pf_mu setT = 1%:E.
Proof. by rewrite /pf_mu preimage_setT probability_setT. Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _
  pf_mu pf_mu_setT.

(** Backward: Giry probability to QBS probability. *)
Definition giry_to_qbs : qbs_prob (R_qbs R M) :=
  mkQBSProb decode
    [the probability mR R of pf_mu] decode_meas.

End giry_to_qbs.

(** Round-trip: qbs_to_giry o giry_to_qbs = id. *)
Lemma qbs_to_giryK
    d (M : measurableType d)
    (encode : M -> mR) (decode : mR -> M)
    (encode_meas : measurable_fun setT encode)
    (decode_meas : measurable_fun setT decode)
    (decode_encode : forall x : M, decode (encode x) = x)
    (P : probability M R) (A : set M) :
  measurable A ->
  qbs_to_giry_mu (giry_to_qbs encode_meas decode_meas P) A = P A.
Proof.
move=> mA; rewrite /qbs_to_giry_mu /giry_to_qbs /=.
congr (P _).
by apply/seteqP; split => x /=; rewrite decode_encode.
Qed.

(** Round-trip: giry_to_qbs o qbs_to_giry ~ id. *)
Lemma giry_to_qbsK
    d (M : measurableType d)
    (encode : M -> mR) (decode : mR -> M)
    (encode_meas : measurable_fun setT encode)
    (decode_meas : measurable_fun setT decode)
    (decode_encode : forall x : M, decode (encode x) = x)
    (p : qbs_prob (R_qbs R M)) :
  qbs_prob_equiv (R_qbs R M)
    (giry_to_qbs encode_meas decode_meas (qbs_to_giry p))
    p.
Proof.
move=> U hU.
rewrite /giry_to_qbs /qbs_to_giry_mu /=.
congr (qbs_prob_mu p _).
by apply/seteqP; split => r /=; rewrite decode_encode.
Qed.

(** QBS integral = Lebesgue integral against qbs_to_giry. *)
Lemma qbs_integral_giry
    d (M : measurableType d)
    (p : qbs_prob (R_qbs R M))
    (f : M -> \bar R)
    (f_meas : measurable_fun setT f)
    (f_int : (qbs_prob_mu p).-integrable setT (f \o qbs_prob_alpha p)) :
  qbs_integral (R_qbs R M) p f = \int[qbs_to_giry p]_y f y.
Proof.
rewrite /qbs_integral.
rewrite -(@integral_pushforward _ _ _ M R (qbs_prob_alpha p)
  (qbs_prob_alpha_random p) (qbs_prob_mu p) setT f f_meas f_int measurableT).
by congr (integral _ setT f).
Qed.

End qbs_giry.
