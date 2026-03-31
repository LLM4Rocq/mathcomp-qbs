(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.classical Require Import classical_sets.
From mathcomp.analysis Require Import topology_theory.num_topology.
From mathcomp.analysis Require Import normedtype_theory.normedtype sequences.
From mathcomp.analysis Require Import measure_theory.measurable_structure.
From mathcomp.analysis Require Import measure_theory.measurable_function.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measurable_realfun trigo exp.

(**md**************************************************************************)
(* # Standard Borel Spaces                                                     *)
(* Measurable bijection R ≅ R × R for standard Borel space closure.           *)
(*                                                                            *)
(* This file constructs a measurable bijection between R and the open         *)
(* interval (0,1) using the arctangent function, as the first step towards    *)
(* the R ≅ R × R construction.                                               *)
(*                                                                            *)
(* ```                                                                        *)
(*   phi x == atan(x)/pi + 1/2, a measurable bijection R -> (0,1)            *)
(*   psi y == tan(pi*(y - 1/2)), its inverse (0,1) -> R                      *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                               *)
(*   phi_gt0 == phi x > 0 for all x                                           *)
(*   phi_lt1 == phi x < 1 for all x                                           *)
(*   psiK    == cancel phi psi (psi is left inverse of phi)                   *)
(*   phiK    == cancel psi phi on (0,1)                                       *)
(*   measurable_phi == phi is measurable on R                                 *)
(*   measurable_psi == psi is measurable on (0,1)                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory reals classical_sets.
Import GRing.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section phi_psi.
Variable R : realType.
Implicit Types x y : R.

(** phi : R -> (0,1) via atan *)
Definition phi (x : R) : R := atan x / pi + 1 / 2.

(** psi : (0,1) -> R via tan *)
Definition psi (y : R) : R := tan (pi * (y - 1 / 2)).

(** phi lands in (0,1) *)
Lemma phi_gt0 x : 0 < phi x.
Proof.
rewrite /phi.
have hpi : (0 : R) < pi := pi_gt0 R.
have hatangt : - (pi / 2) < atan x := atan_gtNpi2 x.
have h1 : - (1 / 2) < atan x / (pi : R).
  rewrite ltr_pdivlMr //.
  by rewrite mulNr mul1r mulrC.
rewrite -subr_gt0 subr0; move: h1; rewrite -subr_gt0 opprK; exact.
Qed.

Lemma phi_lt1 x : phi x < 1.
Proof.
rewrite /phi.
have hpi : (0 : R) < pi := pi_gt0 R.
have hatanlt : atan x < pi / 2 := atan_ltpi2 x.
have h1 : atan x / (pi : R) < 1 / 2.
  rewrite ltr_pdivrMr //.
  by rewrite mul1r mulrC.
have h2 : (1/2 : R) <= 1/2 by done.
have h3 := ltr_leD h1 h2.
by rewrite -splitr in h3.
Qed.

(** psi is the inverse of phi *)
Lemma psiK : cancel phi psi.
Proof.
rewrite /cancel => x; rewrite /psi /phi.
rewrite addrK mulrCA divff ?mulr1; first exact: atanK.
exact: lt0r_neq0 (pi_gt0 R).
Qed.

Lemma phiK : {in `](0:R), 1[, cancel psi phi}.
Proof.
move=> y hy; rewrite /phi /psi.
have hpi : (0 : R) < pi := pi_gt0 R.
have hpi0 : (pi : R) != 0 := lt0r_neq0 hpi.
rewrite in_itv /= in hy.
have /andP [hy0 hy1] := hy.
have hrange : pi * (y - 1 / 2) \in `](- (pi / 2)), pi / 2[.
  rewrite in_itv /=; apply/andP; split.
    have -> : - ((pi : R) / 2) = pi * (- (1 / 2)) by rewrite mulrN mul1r.
    by rewrite ltr_pM2l // ltrDr.
  have -> : (pi : R) / 2 = pi * (1 / 2) by rewrite mul1r.
  rewrite ltr_pM2l // ltrBlDr -splitr; exact: hy1.
by rewrite (tanK hrange) mulrC mulKf // subrK.
Qed.

(** Both are measurable *)
Lemma measurable_phi : measurable_fun setT phi.
Proof.
rewrite /phi.
apply: measurable_funD.
  apply: measurable_funM.
    apply: continuous_measurable_fun; exact: continuous_atan.
  exact: measurable_cst.
exact: measurable_cst.
Qed.

Lemma measurable_psi : measurable_fun (`](0:R), 1[) psi.
Proof.
apply: open_continuous_measurable_fun; first exact: interval_open.
move=> y hy.
have hy01 : 0 < y < 1.
  by move: hy; rewrite inE /= => /andP []; rewrite !bnd_simp => ? ?;
     apply/andP.
have /andP [hy0 hy1] := hy01.
have hcos : cos (pi * (y - 1 / 2)) != 0.
  rewrite lt0r_neq0 //; apply: cos_gt0_pihalf.
  apply/andP; split.
    have -> : - ((pi : R) / 2) = pi * (- (1 / 2)) by rewrite mulrN mul1r.
    by rewrite ltr_pM2l ?pi_gt0 // ltrDr.
  have -> : (pi : R) / 2 = pi * (1 / 2) by rewrite mul1r.
  rewrite ltr_pM2l ?pi_gt0 // ltrBlDr -splitr; exact: hy1.
rewrite /psi.
apply: (@topology_structure.continuous_comp _ _ _
          (fun y0 : R => pi * (y0 - 1/2)) tan).
  apply: continuousM; first exact: topology_structure.cvg_cst.
  apply: continuousB; first exact: filter.cvg_id.
  exact: topology_structure.cvg_cst.
exact: continuous_tan.
Qed.

End phi_psi.
