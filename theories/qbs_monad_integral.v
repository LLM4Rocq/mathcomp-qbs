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
(*   qbs_integral_bind_return, qbs_integrable_bind_return,                    *)
(*   qbs_variance_bind_return == bind against return . g computes with        *)
(*                             the pushforward, for integrals, integrability  *)
(*                             and variance                                   *)
(*   qbs_integral_bind     == the integral of an integrable function against  *)
(*                             p >>= f is the integral of the inner integrals *)
(*   qbs_integral_bind_bounded == same for bounded measurable real functions  *)
(*   qbs_integral_morphism_sgn == P(X) -> \bar R, p |-> qbs_integral p h is a *)
(*                             morphism for any sigma_Mx-measurable h         *)
(*   qbs_integral_param == x |-> integral of h(x, .) against L x is a         *)
(*                             morphism, for L : X -> P(Y)                    *)
(*   qbs_integral_snd == y |-> integral of h(., y) against p is a morphism    *)
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
Local Notation mR := (measurableTypeR R).
Implicit Types (W X Y Z : qbsType R).

(** ** Return *)

Lemma qbs_integrable_returnP X (x : X) (h : X -> \bar R) :
  qbs_integrable X (qbs_return x) h <-> h x \is a fin_num.
Proof.
split=> [hi|hx].
  have := integrable_fin_num measurableT hi.
  by rewrite -[X in X \is a fin_num]/(qbs_integral X (qbs_return x) h)
    qbs_return_integral.
rewrite /qbs_integrable (_ : h \o _ = fun=> (fine (h x))%:E).
  by apply/funext => r /=; rewrite fineK.
exact: finite_measure_integrable_cst.
Qed.

Lemma qbs_integrable_return X (x : X) (f : X -> R) :
  qbs_integrable X (qbs_return x) (fun y => (f y)%:E).
Proof. exact/qbs_integrable_returnP. Qed.

(** ** Bind against a return *)

Section bind_return.
Context X Y (p : monadP X) (g : qbsHomType X Y).

Local Notation q := (qbs_bind p (qbs_comp g (qbs_returnQ Y))).

Lemma qbs_integral_bind_return (h : Y -> \bar R) :
  qbs_measurable Y h -> qbs_integral Y q h = qbs_integral X p (h \o g).
Proof.
move=> mh.
by rewrite (qbs_integral_equiv mh (qbs_prob_equiv_sym (monadP_map_bind g p))).
Qed.

Lemma qbs_integrable_bind_return (h : Y -> \bar R) :
  qbs_measurable Y h -> qbs_integrable Y q h <-> qbs_integrable X p (h \o g).
Proof.
move=> mh; split.
- exact/(qbs_integrable_equiv mh (qbs_prob_equiv_sym (monadP_map_bind g p))).
- exact/(qbs_integrable_equiv mh (monadP_map_bind g p)).
Qed.

Lemma qbs_variance_bind_return (f : Y -> R) :
  qbs_measurable Y (fun y => (f y)%:E) ->
  qbs_variance Y q f = qbs_variance X p (f \o g).
Proof.
move=> mf.
by rewrite (qbs_variance_equiv mf (qbs_prob_equiv_sym (monadP_map_bind g p))).
Qed.

End bind_return.

(** ** Bind *)

Section bind.
Context X Y (p : qbs_prob X) (f : qbsHomType X (monadP Y)).

Let hf : monadP_random Y (f \o qbs_prob_alpha p) :=
  qbs_hom_proof _ (qbs_prob_alpha_random p).

(** Signed version of qbs_bind_integral. *)
Lemma qbs_integral_bind (h : Y -> \bar R) :
  qbs_measurable Y h -> qbs_integrable Y (qbs_bind p f) h ->
  qbs_integral Y (qbs_bind p f) h =
  \int[qbs_prob_mu p]_r qbs_integral Y (f (qbs_prob_alpha p r)) h.
Proof.
move=> mh hi.
have mhp := qbs_measurable_funepos mh; have mhn := qbs_measurable_funeneg mh.
pose A r := qbs_integral Y (f (qbs_prob_alpha p r)) h^\+.
pose B r := qbs_integral Y (f (qbs_prob_alpha p r)) h^\-.
have A0 r : 0 <= A r by apply: integral_ge0 => x _; exact: funepos_ge0.
have B0 r : 0 <= B r by apply: integral_ge0 => x _; exact: funeneg_ge0.
have mA : measurable_fun setT A.
  exact: monadP_random_integral hf mhp (fun y => funepos_ge0 h y).
have mB : measurable_fun setT B.
  exact: monadP_random_integral hf mhn (fun y => funeneg_ge0 h y).
have eA : qbs_integral Y (qbs_bind p f) h^\+ = \int[qbs_prob_mu p]_r A r.
  exact: qbs_bind_integral mhp (fun y => funepos_ge0 h y).
have eB : qbs_integral Y (qbs_bind p f) h^\- = \int[qbs_prob_mu p]_r B r.
  exact: qbs_bind_integral mhn (fun y => funeneg_ge0 h y).
have iA : (qbs_prob_mu p).-integrable setT A.
  apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  by rewrite -eA; exact: qbs_integral_funepos_lty hi.
have iB : (qbs_prob_mu p).-integrable setT B.
  apply/integrableP; split => //.
  under eq_integral do rewrite gee0_abs//.
  rewrite -ge0_fin_numE; first by apply: integral_ge0 => r _; exact: B0.
  by rewrite -eB; exact: qbs_integral_funeneg_fin_num hi.
rewrite qbs_integralE eA eB -(integralB measurableT iA iB).
by apply: eq_integral => r _; rewrite qbs_integralE.
Qed.

End bind.

(** Bounded measurable real functions: AFP qbs_prob_integral_bind. *)
Lemma qbs_integral_bind_bounded X Y (p : qbs_prob X)
    (f : qbsHomType X (monadP Y)) (k : Y -> R) :
  qbs_measurable Y (fun y => (k y)%:E) -> (exists M, forall y, `|k y| <= M)%R ->
  qbs_integral Y (qbs_bind p f) (fun y => (k y)%:E) =
  \int[qbs_prob_mu p]_r qbs_integral Y (f (qbs_prob_alpha p r))
    (fun y => (k y)%:E).
Proof.
move=> mk bd; apply: qbs_integral_bind => //.
exact: qbs_integrable_bounded.
Qed.

(** ** Integration is a morphism, signed version of qbs_integral_morphism *)

Lemma monadP_random_integral_sgn X (b : mR -> qbs_prob X) (h : X -> \bar R) :
  monadP_random X b -> qbs_measurable X h ->
  measurable_fun [set: mR] (fun r => qbs_integral X (b r) h).
Proof.
move=> hb mh.
rewrite (_ : (fun r => _) = (fun r => qbs_integral X (b r) h^\+ -
  qbs_integral X (b r) h^\-)).
  by apply/funext => r; exact: qbs_integralE.
apply: emeasurable_funB.
- exact: monadP_random_integral hb (qbs_measurable_funepos mh)
    (fun y => funepos_ge0 h y).
- exact: monadP_random_integral hb (qbs_measurable_funeneg mh)
    (fun y => funeneg_ge0 h y).
Qed.

Lemma qbs_integral_morphism_sgn X (h : X -> \bar R) :
  qbs_measurable X h ->
  qbs_morphism (X := monadP X) (Y := R_qbs R (\bar R))
    (fun p => qbs_integral X p h).
Proof. by move=> mh b hb; exact: monadP_random_integral_sgn. Qed.

(** ** Parametric integrals (AFP qbs_prob_integral_morphism) *)

Lemma qbs_integral_param X Y (L : qbsHomType X (monadP Y))
    (h : prodQ X Y -> \bar R) :
  qbs_measurable (prodQ X Y) h ->
  qbs_morphism (X := X) (Y := R_qbs R (\bar R))
    (fun x => qbs_integral Y (L x) (fun y => h (x, y))).
Proof.
move=> mh a ha.
pose g := qbs_comp (qbs_pair (qbs_id X) L) (qbs_strengthQ X Y).
have hs : monadP_random (prodQ X Y) (g \o a) := qbs_hom_proof _ ha.
exact: monadP_random_integral_sgn hs mh.
Qed.

Lemma qbs_integral_snd X Y (p : monadP X) (h : prodQ X Y -> \bar R) :
  qbs_measurable (prodQ X Y) h ->
  qbs_morphism (X := Y) (Y := R_qbs R (\bar R))
    (fun y => qbs_integral X p (fun x => h (x, y))).
Proof.
move=> mh; apply: (qbs_integral_param (qbs_const Y p)
  (h := fun yx => h (yx.2, yx.1))).
move=> a ha.
have hs : qbs_Mx (s := prodQ X Y) (qbs_swap Y X \o a) := qbs_hom_proof _ ha.
exact: mh _ hs.
Qed.

End qbs_monad_integral.
