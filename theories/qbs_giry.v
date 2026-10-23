(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals classical_sets boolp
  ereal measurable_structure measurable_function measure measure_function
  probability_measure lebesgue_stieltjes_measure lebesgue_integral
  lebesgue_measure measurable_realfun probability.
From QBS Require Import quasi_borel measure_qbs_adjunction probability_qbs
  qbs_monad.

(**md**************************************************************************)
(* # QBS probabilities on measurable spaces and probability measures          *)
(*                                                                            *)
(* A probability on R(M) induces a probability measure on M (its             *)
(* distribution). Conversely, given a measurable encode : M -> R with a       *)
(* measurable left inverse decode, a probability measure on M induces a       *)
(* probability on R(M).                                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*      qbs_to_giry p == distribution of p : qbs_prob (R_qbs R M) on M        *)
(* giry_to_qbs me md P == the probability (decode, P o encode^-1) on R(M)     *)
(* ```                                                                        *)
(******************************************************************************)

Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_giry.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

Section qbs_to_giry.
Context d (M : measurableType d).

Definition qbs_prob_alpha_mfun (p : qbs_prob (R_qbs R M)) : {mfun mR >-> M} :=
  mfun_Sub (mem_set (qbs_prob_alpha_random p)).

Definition qbs_to_giry (p : qbs_prob (R_qbs R M)) : probability M R :=
  distribution (qbs_prob_mu p) (qbs_prob_alpha_mfun p).

Lemma qbs_to_giryE (p : qbs_prob (R_qbs R M)) (A : set M) :
  qbs_to_giry p A = qbs_prob_event (R_qbs R M) p A.
Proof. by []. Qed.

Lemma qbs_integral_giry (p : qbs_prob (R_qbs R M)) (f : M -> \bar R) :
  measurable_fun [set: M] f ->
  (qbs_prob_mu p).-integrable [set: mR] (f \o qbs_prob_alpha p) ->
  qbs_integral (R_qbs R M) p f = \int[qbs_to_giry p]_y f y.
Proof. by move=> mf intf; rewrite integral_distribution. Qed.

Lemma qbs_prob_equiv_giry (p1 p2 : qbs_prob (R_qbs R M)) (A : set M) :
  qbs_prob_equiv (R_qbs R M) p1 p2 -> measurable A ->
  qbs_to_giry p1 A = qbs_to_giry p2 A.
Proof. by move=> e mA; exact: (e _ (sigma_Mx_measurable mA)). Qed.

Lemma qbs_to_giry_return (x : M) (A : set M) :
  qbs_to_giry (qbs_return (x : R_qbs R M)) A = (\d_x)%R A.
Proof.
by rewrite qbs_to_giryE qbs_return_event diracE; congr ((_ : bool)%:R%:E).
Qed.

End qbs_to_giry.

Lemma qbs_to_giry_map d1 d2 (M1 : measurableType d1) (M2 : measurableType d2)
    (f : qbsHomType (R_qbs R M1) (R_qbs R M2))
    (p : qbs_prob (R_qbs R M1)) (A : set M2) :
  qbs_to_giry (monadP_map f p : qbs_prob _) A =
  qbs_to_giry p (f @^-1` A).
Proof. by []. Qed.

Section giry_to_qbs.
Context d (M : measurableType d).
Variables (encode : {mfun M >-> mR}) (decode : mR -> M).
Hypothesis decode_meas : measurable_fun [set: mR] decode.
Hypothesis decode_encode : cancel encode decode.

Definition giry_to_qbs (P : probability M R) : qbs_prob (R_qbs R M) :=
  @mkQBSProb R (R_qbs R M) decode (distribution P encode) decode_meas.

Lemma qbs_to_giryK (P : probability M R) (A : set M) :
  qbs_to_giry (giry_to_qbs P) A = P A.
Proof.
rewrite qbs_to_giryE /qbs_prob_event /= /distribution /pushforward.
by congr (P _); apply/seteqP; split => x /=; rewrite decode_encode.
Qed.

Lemma giry_to_qbsK (p : qbs_prob (R_qbs R M)) :
  qbs_prob_equiv (R_qbs R M) (giry_to_qbs (qbs_to_giry p)) p.
Proof.
move=> U _; rewrite /= /distribution /pushforward.
by congr (qbs_prob_mu p _); apply/seteqP; split => r /=; rewrite decode_encode.
Qed.

End giry_to_qbs.

End qbs_giry.
