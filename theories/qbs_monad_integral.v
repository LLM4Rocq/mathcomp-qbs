(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology classical_sets
  boolp numfun measure measurable_realfun lebesgue_measure lebesgue_integral
  lebesgue_stieltjes_measure probability.
From QBS Require Import quasi_borel probability_qbs qbs_monad.

(**md**************************************************************************)
(* # Integrals through the probability monad                                  *)
(*                                                                            *)
(* Signed and integrable versions of the integration lemmas of qbs_monad.v,   *)
(* following the end of Monad_QuasiBorel.thy in the Isabelle/HOL development  *)
(* of quasi-Borel spaces (Hirata, Minamide, Sato).                            *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_integrable_returnP == h is integrable for the Dirac probability at x *)
(*                             iff h x is finite                              *)
(*   qbs_integrable_return  == real-valued functions are integrable for       *)
(*                             qbs_return x                                   *)
(*   qbs_integral_bind     == the integral of an integrable function against  *)
(*                             p >>= f is the integral of the inner integrals *)
(*   qbs_integral_bind_bounded == same for bounded measurable real functions  *)
(*   monadP_random_integral, qbs_integral_morphism == signed versions         *)
(*                             of the integral being measurable in a random   *)
(*                             probability, and of p |-> qbs_integral p h     *)
(*                             being a morphism P(X) -> \bar R                *)
(*   qbs_integral_param == x |-> integral of h(x, .) against L x is a         *)
(*                             morphism, for L : X -> P(Y)                    *)
(*   qbs_integral_param_snd == y |-> integral of h(., y) against p is a       *)
(*                             morphism                                       *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_monad_integral.
Variable R : realType.
Local Abbreviation mR := (measurableTypeR R).
Implicit Types (X Y : qbsType R).

(** ** Return *)

Lemma qbs_integrable_returnP X (x : X) (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_integrable X (qbs_return x) h <-> h x \is a fin_num.
Proof.
move=> mh; split=> [hi|hx].
  have := integrable_fin_num measurableT hi.
  by rewrite -[A in A \is a fin_num]/(qbs_integral X (qbs_return x) h)
    qbs_return_integral.
rewrite /qbs_return (qbs_integrable_mk _ _ mh).
rewrite (_ : h \o _ = fun=> (fine (h x))%:E).
  by apply/funext => r /=; rewrite fineK.
exact: finite_measure_integrable_cst _ _ measurableT.
Qed.

Lemma qbs_integrable_return X (x : X) (f : X -> R) :
  qbs_measurable X (fun y => (f y)%:E) ->
  qbs_integrable X (qbs_return x) (fun y => (f y)%:E).
Proof. by move=> mf; apply/qbs_integrable_returnP. Qed.

(** ** Bind *)

Section bind.
Context X Y (p : qbs_prob X) (f : qbsHomType X (monadP Y)).

Let hf : monadP_random Y (f \o qbs_prob_alpha p) :=
  qbs_hom_proof _ (qbs_prob_alpha_random p).

(** Signed version of ge0_qbs_integral_bind. *)
Lemma qbs_integral_bind (h : Y -> \bar R) :
  qbs_measurable Y h -> qbs_integrable Y (qbs_bind p f) h ->
  qbs_integral Y (qbs_bind p f) h =
  qbs_integral X p (fun x => qbs_integral Y (f x) h).
Proof.
move=> mh hi.
have mhp := qbs_measurable_funepos mh; have mhn := qbs_measurable_funeneg mh.
pose A r := qbs_integral Y (f (qbs_prob_alpha p r)) h^\+.
pose B r := qbs_integral Y (f (qbs_prob_alpha p r)) h^\-.
have A0 r : 0 <= A r by apply: integral_ge0 => ? _; exact: funepos_ge0.
have B0 r : 0 <= B r by apply: integral_ge0 => ? _; exact: funeneg_ge0.
have mA : measurable_fun setT A.
  exact: ge0_monadP_random_integral hf mhp (funepos_ge0 h).
have mB : measurable_fun setT B.
  exact: ge0_monadP_random_integral hf mhn (funeneg_ge0 h).
have eA : qbs_integral Y (qbs_bind p f) h^\+ = \int[qbs_prob_mu p]_r A r.
  exact: ge0_qbs_integral_bind mhp (funepos_ge0 h).
have eB : qbs_integral Y (qbs_bind p f) h^\- = \int[qbs_prob_mu p]_r B r.
  exact: ge0_qbs_integral_bind mhn (funeneg_ge0 h).
have iA : (qbs_prob_mu p).-integrable setT A.
  apply/integrableP; split=> //.
  under eq_integral do rewrite gee0_abs//.
  by rewrite -eA; exact: qbs_integral_funepos_lty hi.
have iB : (qbs_prob_mu p).-integrable setT B.
  apply/integrableP; split=> //.
  under eq_integral do rewrite gee0_abs//.
  by rewrite -eB; exact: qbs_integral_funeneg_lty hi.
rewrite qbs_integralE eA eB -(integralB measurableT iA iB).
by apply: eq_integral => r _; rewrite qbs_integralE.
Qed.

End bind.

(** Bounded measurable real functions: AFP qbs_prob_integral_bind. *)
Lemma qbs_integral_bind_bounded X Y (p : qbs_prob X)
    (f : qbsHomType X (monadP Y)) (k : Y -> R) :
  qbs_measurable Y (fun y => (k y)%:E) -> (exists M, forall y, `|k y| <= M)%R ->
  qbs_integral Y (qbs_bind p f) (fun y => (k y)%:E) =
  qbs_integral X p (fun x => qbs_integral Y (f x) (fun y => (k y)%:E)).
Proof.
move=> mk bd; apply: qbs_integral_bind => //.
exact: qbs_integrable_bounded.
Qed.

(** ** Integration is a morphism, signed version of ge0_qbs_integral_morphism *)

Lemma monadP_random_integral X (b : mR -> qbs_prob X) (h : X -> \bar R) :
  monadP_random X b -> qbs_measurable X h ->
  measurable_fun [set: mR] (fun r => qbs_integral X (b r) h).
Proof.
move=> hb mh; under eq_fun do rewrite qbs_integralE.
apply: emeasurable_funB.
  exact: ge0_monadP_random_integral hb (qbs_measurable_funepos mh)
    (funepos_ge0 h).
exact: ge0_monadP_random_integral hb (qbs_measurable_funeneg mh)
  (funeneg_ge0 h).
Qed.

Lemma qbs_integral_morphism X (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_morphism (X := monadP X) (Y := measQ R (\bar R))
    (fun p => qbs_integral X p h).
Proof. by move=> mh b hb; exact: monadP_random_integral. Qed.

(** ** Parametric integrals (AFP qbs_prob_integral_morphism) *)

Lemma qbs_integral_param X Y (L : qbsHomType X (monadP Y))
    (h : prodQ X Y -> \bar R) :
  qbs_measurable (prodQ X Y) h ->
  qbs_morphism (X := X) (Y := measQ R (\bar R))
    (fun x => qbs_integral Y (L x) (fun y => h (x, y))).
Proof.
move=> mh a ha.
pose g := qbs_comp (qbs_pair (qbs_id X) L) (qbs_strengthQ X Y).
have hs : monadP_random (prodQ X Y) (g \o a) := qbs_hom_proof _ ha.
have := monadP_random_integral hs mh.
by under [X in measurable_fun _ X -> _]eq_fun do
  rewrite /g /= qbs_strength_integral//.
Qed.

Lemma qbs_integral_param_snd X Y (p : monadP X) (h : prodQ X Y -> \bar R) :
  qbs_measurable (prodQ X Y) h ->
  qbs_morphism (X := Y) (Y := measQ R (\bar R))
    (fun y => qbs_integral X p (fun x => h (x, y))).
Proof.
move=> mh; apply: (qbs_integral_param (qbs_const Y p)
  (h := fun yx => h (yx.2, yx.1))).
move=> a ha.
have hs : qbs_Mx (s := prodQ X Y) (qbs_swap Y X \o a) := qbs_hom_proof _ ha.
exact: mh _ hs.
Qed.

End qbs_monad_integral.
