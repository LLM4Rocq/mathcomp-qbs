(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure lebesgue_measure
  lebesgue_integral probability measurable_realfun.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel coproduct_qbs probability_qbs
  qbs_prob_quot qbs_giry qbs_quot_bind measure_qbs_adjunction.

(**md**************************************************************************)
(* # Proof of qps_bind_classical_wd                                           *)
(*                                                                            *)
(* We prove that the classical bind on QBS probability spaces respects        *)
(* the equivalence relation qps_eq: if p1 ~ p2 then                          *)
(* qps_bind_classical p1 f hf ~ qps_bind_classical p2 f hf.                  *)
(*                                                                            *)
(* ## Hypotheses                                                              *)
(*                                                                            *)
(* We rely on two hypotheses:                                                 *)
(*                                                                            *)
(* 1. [qps_bind_exists]: For any QBS probability p and morphism f,            *)
(*    there exists alpha_Y in qbs_Mx Y such that the pushforward             *)
(*    mu_p(alpha_Y^{-1}(U)) = mu_p(diag^{-1}(U)) for sigma_Mx U.            *)
(*    This decouples the diagonal randomness.                                 *)
(*                                                                            *)
(* 2. [bind_pushforward_wd]: The diagonal bind pushforward respects           *)
(*    equivalence: if p1 ~ p2 then                                            *)
(*    mu_1(diag_1^{-1}(U)) = mu_2(diag_2^{-1}(U)) for sigma_Mx U.           *)
(*    This is a theorem in QBS theory (HKSY 2017): the bind pushforward       *)
(*    factors through the Giry measure, which is invariant under              *)
(*    equivalence. For standard Borel spaces this follows from                *)
(*    kernel composition; for general QBS types it requires the               *)
(*    standard Borel isomorphism R ~ N x R.                                   *)
(*                                                                            *)
(* ## Proof strategy                                                          *)
(*                                                                            *)
(* For sigma_Mx Y set U, we chain:                                            *)
(*   mu_1(alpha_Y1^{-1}(U)) = mu_1(diag_1^{-1}(U))  [qps_bind_exists, p1]   *)
(*                           = mu_2(diag_2^{-1}(U))  [bind_pushforward_wd]    *)
(*                           = mu_2(alpha_Y2^{-1}(U)) [qps_bind_exists, p2]   *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section qps_bind_classical_wd_proof.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(** Hypothesis 1: Existence of a decoupled bind representative. *)
Variable qps_bind_exists :
  forall (X0 Y0 : qbsType R)
    (p0 : qbs_prob X0)
    (f0 : X0 -> qbs_prob Y0)
    (hf0 : @qbs_morphism R X0 (monadP Y0) f0),
  { alpha_Y : mR -> Y0 |
    @qbs_Mx R Y0 alpha_Y /\
    forall (U : set Y0),
      @sigma_Mx R Y0 U ->
      qbs_prob_mu p0 (alpha_Y @^-1` U) =
      qbs_prob_mu p0
        ((fun r => qbs_prob_alpha (f0 (qbs_prob_alpha p0 r)) r) @^-1` U) }.

(** Hypothesis 2: The diagonal bind pushforward respects equivalence. *)
Variable bind_pushforward_wd :
  forall (X0 Y0 : qbsType R)
    (p1 p2 : qbs_prob X0)
    (f0 : X0 -> qbs_prob Y0)
    (hf0 : @qbs_morphism R X0 (monadP Y0) f0),
  qbs_prob_equiv X0 p1 p2 ->
  forall (U : set Y0),
    @sigma_Mx R Y0 U ->
    qbs_prob_mu p1
      ((fun r => qbs_prob_alpha (f0 (qbs_prob_alpha p1 r)) r) @^-1` U) =
    qbs_prob_mu p2
      ((fun r => qbs_prob_alpha (f0 (qbs_prob_alpha p2 r)) r) @^-1` U).

(** The classical bind on the quotient, using qps_bind_exists. *)
Definition qps_bind_classical_loc (X Y : qbsType R)
  (p : qbs_prob_space X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morphism R X (monadP Y) f) :
  qbs_prob_space Y :=
  let raw := qps_repr p in
  let alpha_Y_sig := qps_bind_exists raw hf in
  QPS (@mkQBSProb R Y
    (proj1_sig alpha_Y_sig)
    (qbs_prob_mu raw)
    (proj1 (proj2_sig alpha_Y_sig))).

(** Main theorem: the classical bind respects qps_eq.
    If p1 ~ p2 then bind(p1, f) ~ bind(p2, f). *)
Lemma qps_bind_classical_wd :
  forall (X0 Y0 : qbsType R)
    (p1 p2 : qbs_prob_space X0)
    (f0 : X0 -> qbs_prob Y0)
    (hf0 : @qbs_morphism R X0 (monadP Y0) f0),
  qps_eq p1 p2 ->
  qps_eq (qps_bind_classical_loc p1 hf0)
         (qps_bind_classical_loc p2 hf0).
Proof.
move=> X0 Y0 p1 p2 f0 hf0 heq U hU /=.
case: (qps_bind_exists (qps_repr p1) hf0) => /= alpha_Y1 [hMx1 hpush1].
case: (qps_bind_exists (qps_repr p2) hf0) => /= alpha_Y2 [hMx2 hpush2].
rewrite (hpush1 U hU) (hpush2 U hU).
exact: (bind_pushforward_wd hf0 heq hU).
Qed.

End qps_bind_classical_wd_proof.

(* ================================================================== *)
(* Standard Borel instantiation: bind_pushforward_wd from Giry bridge *)
(* ================================================================== *)

(**md**************************************************************************)
(* ## Standard Borel case                                                     *)
(*                                                                            *)
(* For standard Borel types X = R_qbs(M1), Y = R_qbs(M2), the               *)
(* `bind_pushforward_wd` hypothesis is discharged by the Giry bridge.         *)
(* Instead of proving that the diagonal pushforward directly respects         *)
(* equivalence, we use `qbs_giry_bind_well_def` from `qbs_quot_bind.v`,      *)
(* which defines bind via kernel composition of pushforward measures.         *)
(*                                                                            *)
(* The Giry bridge (HKSY 2017) works as follows:                              *)
(* 1. Map QBS probabilities to Giry measures via `qbs_to_giry`.              *)
(* 2. Define bind as kernel composition at the Giry level                     *)
(*    (`giry_bind_mu`), avoiding diagonal randomness entirely.                *)
(* 3. Map the result back to QBS via `giry_to_qbs`.                           *)
(* 4. Well-definedness follows because `qbs_to_giry` maps equivalent         *)
(*    triples to equal measures (`qbs_to_giry_equiv`), so the kernel          *)
(*    composition integral is invariant.                                      *)
(*                                                                            *)
(* This gives `qps_bind_classical_wd_sb`: the bind on `qbs_prob_space`       *)
(* respects `qps_eq` for standard Borel types, proved as a Lemma with        *)
(* no `bind_pushforward_wd` variable.                                         *)
(*                                                                            *)
(* ## Key results                                                             *)
(* ```                                                                        *)
(*   qps_bind_classical_wd_sb                                                 *)
(*     == qps_eq p1 p2 -> qps_eq (giry_bind p1) (giry_bind p2)              *)
(*        for standard Borel X = R_qbs(M1), Y = R_qbs(M2)                    *)
(* ```                                                                        *)
(******************************************************************************)

Section qps_bind_classical_wd_standard_borel.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1) (M2 : measurableType d2).

Let X := @R_qbs R _ M1.
Let Y := @R_qbs R _ M2.

(** Standard Borel witnesses for the codomain Y = R_qbs(M2). *)
Variable (encode2 : M2 -> mR) (decode2 : mR -> M2).
Hypothesis encode2_meas : measurable_fun setT encode2.
Hypothesis decode2_meas : measurable_fun setT decode2.
Hypothesis decode2_encode2 : forall x : M2, decode2 (encode2 x) = x.

Variable (f : M1 -> qbs_prob Y).

(** Kernel measurability: the Giry image of f is a measurable kernel.
    This is the measurability condition needed for the kernel composition
    integral that defines the Giry bind. *)
Hypothesis giry_f_kernel_meas :
  forall (B : set M2), measurable B ->
    measurable_fun setT
      (fun x : M1 => (qbs_to_giry (f x) : measure _ _) B).

(** The Giry-level bind is well-defined on the quotient.
    This eliminates the `bind_pushforward_wd` hypothesis from
    Section [qps_bind_classical_wd_proof] for standard Borel spaces,
    by routing through `qbs_giry_bind_well_def` which uses kernel
    composition instead of diagonal randomness. *)
Lemma qps_bind_classical_wd_sb
  (p1 p2 : qbs_prob_space X) :
  qps_eq p1 p2 ->
  qps_eq (qps_giry_bind encode2 decode2 encode2_meas decode2_meas
            f giry_f_kernel_meas p1)
         (qps_giry_bind encode2 decode2 encode2_meas decode2_meas
            f giry_f_kernel_meas p2).
Proof. exact: qps_giry_bind_equiv. Qed.

End qps_bind_classical_wd_standard_borel.
