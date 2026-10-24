(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals classical_sets boolp ereal
  measure lebesgue_stieltjes_measure lebesgue_integral measurable_realfun
  probability.
From QBS Require Import quasi_borel measure_qbs_adjunction probability_qbs
  qbs_monad.

(**md**************************************************************************)
(* # QBS probabilities on measurable spaces and probability measures          *)
(*                                                                            *)
(* A probability on R(M) induces a probability measure on M (its              *)
(* distribution). Conversely, given a measurable encode : M -> R with a       *)
(* measurable left inverse decode, a probability measure on M induces a       *)
(* probability on R(M).                                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*      qbs_to_giry p == distribution of p : qbs_prob (measQ R M) on M        *)
(* giry_to_qbs encode decode P == the probability (decode, P o encode^-1)     *)
(*                  on R(M); it returns a qbs_prob, not an element of the     *)
(*                  Giry monad                                                *)
(* ```                                                                        *)
(******************************************************************************)

Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section giry_comparison.
Variable R : realType.
Local Abbreviation mR := (measurableTypeR R).

Section qbs_to_giry.
Context d (M : measurableType d).

Definition qbs_prob_alpha_mfunR (p : qbs_prob (measQ R M)) : {mfun mR >-> M} :=
  mfun_Sub (mem_set (qbs_prob_alpha_random p)).

Definition qbs_to_giry (p : qbs_prob (measQ R M)) : probability M R :=
  distribution (qbs_prob_mu p) (qbs_prob_alpha_mfunR p).

Lemma qbs_to_giryE (p : qbs_prob (measQ R M)) (A : set M) :
  qbs_to_giry p A = qbs_prob_event (measQ R M) p A.
Proof. by []. Qed.

Lemma qbs_integral_giry (p : qbs_prob (measQ R M)) (f : M -> \bar R) :
  measurable_fun [set: M] f ->
  (qbs_prob_mu p).-integrable [set: mR] (f \o qbs_prob_alpha p) ->
  qbs_integral (measQ R M) p f = \int[qbs_to_giry p]_y f y.
Proof. by move=> *; rewrite integral_distribution. Qed.

Lemma qbs_to_giry_return (x : M) (A : set M) : measurable A ->
  qbs_to_giry (qbs_return (x : measQ R M)) A = (\d_x)%R A.
Proof.
move=> mA; rewrite qbs_to_giryE qbs_return_event ?diracE//.
  exact: sigma_Mx_measQ.
Qed.

End qbs_to_giry.

Lemma qbs_to_giry_map d1 d2 (M1 : measurableType d1) (M2 : measurableType d2)
    (f : qbsHomType (measQ R M1) (measQ R M2))
    (p : qbs_prob (measQ R M1)) (A : set M2) : measurable A ->
  qbs_to_giry (monadP_map f p : qbs_prob _) A =
  qbs_to_giry p (f @^-1` A).
Proof.
move=> mA; rewrite qbs_to_giryE monadP_map_event//.
exact: sigma_Mx_measQ.
Qed.

(** ** Comparison with the Giry monad on standard Borel spaces
    (HKSY Prop. 22(3) and 23) *)

Section standard_borel_giry.
Context d (M : measurableType d) (sb : standard_borel_wit R M).

(** On a standard Borel space, a QBS probability is determined by its
    distribution. *)
Lemma qbs_to_giry_inj (p1 p2 : qbs_prob (measQ R M)) :
  (forall A, measurable A -> qbs_to_giry p1 A = qbs_to_giry p2 A) ->
  p1 = p2.
Proof.
by move=> e; apply/qbs_prob_eqP => U /(sigma_Mx_standard_borelP sb U)/e.
Qed.

(** L preserves bind: the distribution of p >>= f is the Giry bind of the
    distribution of p with the distributions of f. *)
Lemma qbs_to_giry_bind d' (M' : measurableType d') (p : qbs_prob (measQ R M))
    (f : qbsHomType (measQ R M) (qbs_prob (measQ R M'))) (A : set M') :
  measurable A ->
  qbs_to_giry (qbs_bind p f : qbs_prob _) A =
  \int[qbs_to_giry p]_x qbs_to_giry (f x : qbs_prob _) A.
Proof.
move=> mA; rewrite qbs_to_giryE (qbs_bind_event _ _ (sigma_Mx_measQ mA)).
have mh : measurable_fun [set: M] (fun x => qbs_to_giry (f x : qbs_prob _) A).
  apply: (measQ_full sb (M2 := \bar R)) => a ha.
  apply: monadP_random_event (sigma_Mx_measQ mA).
  exact: qbs_hom_proof.
by rewrite ge0_integral_distribution.
Qed.

End standard_borel_giry.

Section giry_to_qbs.
Context d (M : measurableType d).
Variables (encode : {mfun M >-> mR}) (decode : {mfun mR >-> M}).
Hypothesis decode_encode : cancel encode decode.

Definition giry_to_qbs (P : probability M R) : qbs_prob (measQ R M) :=
  mkQBSProb decode (distribution P encode)
    (measurable_funP decode).

Lemma qbs_to_giryK (P : probability M R) (A : set M) : measurable A ->
  qbs_to_giry (giry_to_qbs P) A = P A.
Proof.
move=> mA; rewrite qbs_to_giryE qbs_prob_event_mk//=.
  exact: sigma_Mx_measQ.
by congr (P _); apply/seteqP; split=> x /=; rewrite decode_encode.
Qed.

Lemma giry_to_qbsK (p : qbs_prob (measQ R M)) :
  giry_to_qbs (qbs_to_giry p) = p.
Proof.
apply/qbs_prob_eqP => U mU; rewrite qbs_prob_event_mk//=.
by congr (qbs_prob_mu p _); apply/seteqP; split=> r /=; rewrite decode_encode.
Qed.

End giry_to_qbs.

End giry_comparison.
