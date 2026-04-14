(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets functions
  borel_hierarchy measure lebesgue_stieltjes_measure lebesgue_measure
  lebesgue_integral lebesgue_integral_fubini probability
  measurable_realfun kernel measurable_structure measurable_function
  probability_measure numfun sequences.
From mathcomp.classical Require Import boolp.
From QBS Require Import measurable_prob.

(**md**************************************************************************)
(* # Measurability of the Normal Probability Kernel                           *)
(*                                                                            *)
(* The main result:                                                           *)
(* ```                                                                        *)
(*   measurable_normal_prob_sigma sigma hs ==                                 *)
(*     m |-> normal_prob m sigma is measurable                                *)
(*     as a function mR -> pprobability mR R                                  *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Local Open Scope ring_scope.

Section measurable_normal_prob.
Variable R : realType.
Local Notation mR := (measurableTypeR R).
Local Notation mu := (@lebesgue_measure R).

Variable sigma : R.
Hypothesis hs : (0 < sigma)%R.

Let sigma_neq0 : sigma != 0.
Proof. exact: lt0r_neq0 hs. Qed.

(* Step 1: Joint measurability of (m, x) |-> normal_fun m sigma x *)

Lemma measurable_normal_fun_joint :
  measurable_fun [set: mR * mR]
    (fun p : mR * mR => normal_fun p.1 sigma p.2).
Proof.
have h1 : measurable_fun [set: mR * mR] (fun p : mR * mR => p.2 - p.1).
  exact: measurable_funB measurable_snd measurable_fst.
have h2 : measurable_fun [set: mR * mR] (fun p : mR * mR => (p.2 - p.1)^+2).
  exact: measurable_funX h1.
have h3 : measurable_fun [set: mR * mR] (fun p : mR * mR => -((p.2 - p.1)^+2)).
  exact: measurable_funN h2.
have h4 : measurable_fun [set: mR * mR]
  (fun p : mR * mR => -((p.2 - p.1)^+2) / (sigma ^+ 2 *+ 2)).
  apply: measurable_funM h3 _.
  exact: measurable_cst.
suff -> : (fun p : mR * mR => normal_fun p.1 sigma p.2) =
          expR \o (fun p : mR * mR => -((p.2 - p.1)^+2) / (sigma ^+ 2 *+ 2)).
  exact: measurableT_comp h4.
by apply: boolp.funext => p; rewrite /normal_fun /=.
Qed.

(* Step 2: Joint measurability of (m, x) |-> normal_pdf m sigma x *)

Lemma measurable_normal_pdf_joint :
  measurable_fun [set: mR * mR]
    (fun p : mR * mR => normal_pdf p.1 sigma p.2).
Proof.
rewrite (_ : (fun p => _) =
  (fun p => normal_peak sigma * normal_fun p.1 sigma p.2)).
  apply: measurable_funM => //=.
  exact: measurable_normal_fun_joint.
apply: boolp.funext => p.
by rewrite /normal_pdf (negbTE sigma_neq0).
Qed.

(* Step 3: Auxiliary lemma - restrict/indicator equivalence *)

Let restrict_indic_EFin (m0 : mR) (U : set mR) :
  restrict U (fun x : mR => (normal_pdf m0 sigma x)%:E) =
  (fun y : mR => (normal_pdf m0 sigma y * numfun.indic U y)%:E).
Proof.
apply: boolp.funext => y; rewrite /restrict /patch /numfun.indic.
by case: (y \in U); rewrite ?mulr1 ?mulr0.
Qed.

(* Step 4: For each measurable U, the parametric integral
   m |-> normal_prob m sigma U is measurable *)

Lemma measurable_normal_prob_U (U : set mR) (mU : measurable U) :
  measurable_fun setT
    (fun m : mR => (normal_prob m sigma : measure _ _) U).
Proof.
pose g : mR * mR -> R :=
  fun p => (normal_pdf p.1 sigma p.2) * (numfun.indic U p.2).
have mg : measurable_fun setT g.
  rewrite /g.
  apply: measurable_funM.
  - exact: measurable_normal_pdf_joint.
  - exact: (measurableT_comp (measurable_indic mU) measurable_snd).
pose k : mR * mR -> \bar R := EFin \o g.
have mk : measurable_fun setT k by exact/measurable_EFinP.
have k0 : forall p, (0 <= k p)%E.
  move=> p; rewrite /k /= /g lee_fin.
  apply: mulr_ge0.
  - exact: normal_pdf_ge0.
  - by rewrite indicE ler0n.
have hfub : measurable_fun setT (fubini_F mu k).
  exact: (@measurable_fun_fubini_tonelli_F _ _ mR mR R mu k mk k0).
(* Show our function equals fubini_F mu k *)
(* The function equals fubini_F mu k because: *)
(* normal_prob m0 sigma U = ∫_(x in U) (normal_pdf m0 sigma x)%:E *)
(*   [by integral_mkcond + epatch_indic + EFinM] *)
(* = ∫_x (normal_pdf m0 sigma x * 1_U x)%:E = fubini_F mu k m0 *)
suff Heq : (fun m0 => (normal_prob m0 sigma : measure _ _) U) =
           fubini_F mu k by rewrite Heq.
apply: boolp.funext => m0.
rewrite /fubini_F /k /g /comp /normal_prob.
transitivity (integral mu setT
  ((fun x : mR => (normal_pdf m0 sigma x)%:E) \_ U)).
  by rewrite -integral_mkcond.
congr (integral _ _ _).
apply/funext => y.
rewrite patchE indicE.
by case: ifPn => /= yU; rewrite ?mulr1 ?mulr0.
Qed.

(* Main Theorem *)

Lemma measurable_normal_prob_sigma :
  measurable_fun setT
    (fun m : mR => normal_prob m sigma : pprobability mR R).
Proof.
apply: pointwise_to_pprobability_meas.
move=> U mU.
exact: measurable_normal_prob_U.
Qed.

End measurable_normal_prob.
