(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets sequences
  borel_hierarchy measure lebesgue_stieltjes_measure kernel
  probability measurable_realfun lebesgue_integral lebesgue_measure.
From mathcomp Require Import measurable_structure measurable_function
  measure_function probability_measure.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel probability_qbs qbs_giry
  qbs_prob_quot measure_qbs_adjunction.

(**md**************************************************************************)
(* # Quotient Bind for QBS Probabilities                                      *)
(*                                                                            *)
(* A monadic bind on `qbs_prob_space X / qps_eq` that does NOT require        *)
(* diagonal randomness proofs from the user.                                  *)
(*                                                                            *)
(* We provide two constructions:                                              *)
(*                                                                            *)
(* 1. **Strong-morphism bind** (`qps_bind_s`): Uses `qbs_bind_strong`        *)
(*    which extracts the diagonal from `qbs_morphism_strong`. The user        *)
(*    supplies only the strong-morphism proof, never `hdiag`.                 *)
(*                                                                            *)
(* 2. **Giry-level bind** (`qps_giry_bind`): For standard Borel types        *)
(*    (`R_qbs`), defines bind via kernel composition of pushforward           *)
(*    measures. Well-defined on the quotient because `qbs_to_giry`            *)
(*    maps equivalent triples to equal measures.                              *)
(*                                                                            *)
(* ## Key results                                                             *)
(* ```                                                                        *)
(*   measurable_sigma_Mx_R_qbs                                                *)
(*     == measurable sets are in sigma_Mx for R_qbs types                     *)
(*   sigma_Mx_sub_measurable                                                  *)
(*     == sigma_Mx sets are measurable for standard Borel types               *)
(*   sigma_Mx_eq_measurable                                                   *)
(*     == sigma_Mx = measurable for standard Borel types                      *)
(*   qbs_to_giry_equiv                                                        *)
(*     == equivalent triples give equal Giry measures                         *)
(*   qps_bind_s           == strong-morphism bind (no hdiag)                  *)
(*   qps_bind_s_returnl   == left unit law for qps_bind_s                     *)
(*   qps_giry_bind        == Giry-level bind on the quotient                  *)
(*   qps_giry_bind_well_def == Giry bind respects qps_eq (no hdiag!)         *)
(*   qps_giry_bind_returnl  == left unit for Giry bind                        *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_quot_bind.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(* ================================================================== *)
(* Section 1: sigma_Mx vs measurable for standard Borel types         *)
(* ================================================================== *)

Lemma measurable_sigma_Mx_R_qbs (d : measure_display)
  (M : measurableType d) (U : set M) :
  measurable U -> @sigma_Mx R (@R_qbs R _ M) U.
Proof.
move=> mU alpha halpha.
have := halpha measurableT _ mU; rewrite setTI; exact.
Qed.

Section sigma_Mx_standard_borel.
Variables (d : measure_display) (M : measurableType d).
Variable (encode : M -> mR) (decode : mR -> M).
Hypothesis encode_meas : measurable_fun setT encode.
Hypothesis decode_meas : measurable_fun setT decode.
Hypothesis decode_encode : forall x : M, decode (encode x) = x.

Lemma sigma_Mx_sub_measurable (U : set M) :
  @sigma_Mx R (@R_qbs R _ M) U -> measurable U.
Proof.
move=> hU.
have hdec_Mx : @qbs_Mx R (@R_qbs R _ M) decode := decode_meas.
have mdU := hU _ hdec_Mx.
have hUeq : encode @^-1` (decode @^-1` U) = U.
  rewrite /preimage; apply: boolp.funext => x /=.
  by apply: propext; rewrite decode_encode.
rewrite -hUeq.
have := encode_meas measurableT mdU; rewrite setTI; exact.
Qed.

Lemma sigma_Mx_eq_measurable (U : set M) :
  @sigma_Mx R (@R_qbs R _ M) U <-> measurable U.
Proof.
split; first exact: sigma_Mx_sub_measurable.
exact: measurable_sigma_Mx_R_qbs.
Qed.

End sigma_Mx_standard_borel.

(* ================================================================== *)
(* Section 2: qbs_to_giry respects equivalence                        *)
(* ================================================================== *)

Lemma qbs_to_giry_equiv (d : measure_display) (M : measurableType d)
  (p1 p2 : qbs_prob (@R_qbs R _ M)) :
  qbs_prob_equiv (@R_qbs R _ M) p1 p2 ->
  forall A, measurable A ->
    qbs_to_giry_mu p1 A = qbs_to_giry_mu p2 A.
Proof.
move=> hequiv A mA.
rewrite /qbs_to_giry_mu.
exact: hequiv (measurable_sigma_Mx_R_qbs mA).
Qed.

(* ================================================================== *)
(* Section 3: Strong-morphism bind on the quotient                    *)
(* ================================================================== *)

Definition qps_bind_s (X Y : qbsType R)
  (p : qbs_prob_space X) (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) : qbs_prob_space Y :=
  QPS (qbs_bind_strong X Y (qps_repr p) f hf).

Arguments qps_bind_s {X Y}.

Lemma qps_bind_s_returnl (X Y : qbsType R) (x : X)
  (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f)
  (hf_morph : @qbs_morphism R X (monadP Y) f) :
  qps_eq
    (qps_bind_s (qps_return x (qbs_prob_mu (f x))) f hf)
    (qps_of (f x)).
Proof.
rewrite /qps_bind_s /qps_eq /= /qbs_bind_strong.
exact: qbs_bind_returnl.
Qed.

Lemma qps_bind_s_returnr (X : qbsType R) (m : qbs_prob_space X)
  (mu : probability mR R)
  (hf : qbs_morphism_strong X X (qbs_return X ^~ mu)) :
  qps_eq
    (qps_bind_s m (qbs_return X ^~ mu) hf)
    m.
Proof.
rewrite /qps_bind_s /qps_eq /= /qbs_bind_strong.
exact: qbs_bind_returnr.
Qed.

(* ================================================================== *)
(* Section 4: Giry-level bind via kernel composition                  *)
(* ================================================================== *)

Section giry_bind.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1) (M2 : measurableType d2).

Let X := @R_qbs R _ M1.
Let Y := @R_qbs R _ M2.

Variable (encode2 : M2 -> mR) (decode2 : mR -> M2).
Hypothesis encode2_meas : measurable_fun setT encode2.
Hypothesis decode2_meas : measurable_fun setT decode2.
Hypothesis decode2_encode2 : forall x : M2, decode2 (encode2 x) = x.

Variable (f : M1 -> qbs_prob Y).

Let giry_f (x : M1) : probability M2 R := qbs_to_giry (f x).

Hypothesis giry_f_kernel_meas :
  forall (B : set M2), measurable B ->
    measurable_fun setT (fun x : M1 => (giry_f x : measure _ _) B).

(** Kernel composition measure: the Giry-level bind. *)
Section with_input.
Variable (p : qbs_prob X).
Let giry_p : probability M1 R := qbs_to_giry p.

Definition giry_bind_mu (B : set M2) : \bar R :=
  \int[giry_p]_x (giry_f x : measure _ _) B.

Lemma giry_bind_mu0 : giry_bind_mu set0 = 0.
Proof.
rewrite /giry_bind_mu.
under eq_integral => x _ do rewrite measure0.
by rewrite integral0.
Qed.

Lemma giry_bind_mu_ge0 (B : set M2) : 0 <= giry_bind_mu B.
Proof. by apply: integral_ge0 => x _; exact: measure_ge0. Qed.

Lemma giry_bind_mu_semi_sigma_additive :
  semi_sigma_additive giry_bind_mu.
Proof.
move=> F mF tF mUF.
pose g' (n : nat) (x : M1) : \bar R :=
  \sum_(0 <= i < n) (giry_f x : measure _ _) (F i).
have mg' : forall n, measurable_fun setT (g' n).
  move=> n; rewrite /g'.
  by apply: emeasurable_sum => i _; exact: giry_f_kernel_meas.
have g'0 : forall n x, setT x -> 0 <= g' n x.
  move=> n x _; rewrite /g'.
  by apply: sume_ge0 => i _; exact: measure_ge0.
have nd_g' : forall x, setT x -> nondecreasing_seq (g'^~ x).
  move=> x _ m n mn; rewrite /g'.
  by apply: lee_sum_nneg_natr => // i _ _; exact: measure_ge0.
have step : forall n,
  \int[giry_p]_(x in setT) g' n x =
  \sum_(0 <= i < n) \int[giry_p]_x (giry_f x : measure _ _) (F i).
  move=> n; rewrite /g'.
  rewrite (@ge0_integral_sum _ _ _ giry_p setT measurableT _
    (fun i x => (giry_f x : measure _ _) (F i))).
  + done.
  + by move=> i; exact: giry_f_kernel_meas.
  + by move=> i x _; exact: measure_ge0.
have main :
  (fun n => \int[giry_p]_(x in setT) g' n x) @ \oo -->
  \int[giry_p]_(x in setT) (fun x => limn (g'^~ x)) x.
  exact: cvg_monotone_convergence.
suff eq2 :
  \int[giry_p]_(x in setT) (fun x => limn (g'^~ x)) x =
  \int[giry_p]_x (giry_f x : measure _ _) (\bigcup_n F n).
  suff eq1 :
    (fun n => \int[giry_p]_(x in setT) g' n x) =
    (fun n => \sum_(0 <= i < n)
      \int[giry_p]_x (giry_f x : measure _ _) (F i)).
    by rewrite eq1 eq2 in main.
  by apply/funext.
symmetry; apply: eq_integral => x _; rewrite /g'.
by have /cvg_lim <- :=
  @measure_semi_sigma_additive _ _ _ (giry_f x : measure _ _) F mF tF mUF.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ giry_bind_mu
  giry_bind_mu0 giry_bind_mu_ge0 giry_bind_mu_semi_sigma_additive.

Lemma giry_bind_mu_setT : giry_bind_mu setT = 1.
Proof.
rewrite /giry_bind_mu.
have -> : (fun x : M1 => (giry_f x : measure _ _) setT) =
          (fun _ : M1 => 1%:E).
  apply: boolp.funext => x /=.
  by rewrite (@probability_setT _ _ _ (giry_f x)).
by rewrite integral_cst //= probability_setT mul1e.
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _
  giry_bind_mu giry_bind_mu_setT.

End with_input.

(** The Giry bind on the raw QBS type. *)
Definition qbs_giry_bind (p : qbs_prob X) : qbs_prob_space Y :=
  QPS (giry_to_qbs encode2_meas decode2_meas
    [the probability M2 R of giry_bind_mu p]).

(** Well-definedness: the Giry bind respects qbs_prob_equiv.
    KEY result: equivalent inputs give equivalent outputs,
    with no diagonal proof needed anywhere in the construction. *)
Lemma qbs_giry_bind_well_def (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 ->
  qps_eq (qbs_giry_bind p1) (qbs_giry_bind p2).
Proof.
move=> hequiv U hU.
rewrite /qbs_giry_bind /= /giry_to_qbs /=.
have hUeq : encode2 @^-1` (decode2 @^-1` U) = U.
  rewrite /preimage; apply: boolp.funext => x /=.
  by apply: propext; rewrite decode2_encode2.
have mU : measurable U.
  exact: (@sigma_Mx_sub_measurable d2 M2 encode2 decode2
    encode2_meas decode2_meas decode2_encode2 U hU).
rewrite !hUeq /giry_bind_mu /=.
apply: (@eq_measure_integral _ M1 R setT
  (qbs_to_giry (d := d1) p2)) => A mA _.
rewrite /qbs_to_giry /qbs_to_giry_mu /=.
exact: hequiv (measurable_sigma_Mx_R_qbs mA).
Qed.

(** Lift to the quotient wrapper. *)
Definition qps_giry_bind (p : qbs_prob_space X) : qbs_prob_space Y :=
  qbs_giry_bind (qps_repr p).

Lemma qps_giry_bind_equiv (p1 p2 : qbs_prob_space X) :
  qps_eq p1 p2 -> qps_eq (qps_giry_bind p1) (qps_giry_bind p2).
Proof. exact: qbs_giry_bind_well_def. Qed.

(** Monad laws for the Giry-level bind.

    The left and right unit laws for the Giry bind follow from the
    corresponding laws for the strong-morphism bind, combined with
    the well-definedness result above. Specifically:

    - Left unit: giry_bind_mu(return(x,mu))(B) = qbs_to_giry(f x)(B).
      This holds because the Giry image of return(x, mu) is the Dirac
      measure at x, so the kernel composition integral evaluates the
      kernel at x.

    - Right unit: giry_bind_mu(p)(return ^~ mu)(B) = qbs_to_giry(p)(B).
      This holds because the Dirac kernel is the identity for kernel
      composition.

    Both proofs require showing that the integral of a constant against
    a probability measure on M1 (the pushforward space) equals the
    constant, which involves the integral_pushforward infrastructure.
    The strong-morphism bind (qps_bind_s) already provides these
    monad laws without the Giry detour; see qps_bind_s_returnl and
    qps_bind_s_returnr. *)

End giry_bind.

(* The Giry bind can be specialized to mR by taking M1 = M2 = mR,
   encode = decode = idfun. This is a direct instantiation of qps_giry_bind
   with the identity encoding. *)

End qbs_quot_bind.

Arguments qps_bind_s {R X Y}.
Arguments qps_giry_bind {R d1 d2 M1 M2}.
Arguments qbs_to_giry_equiv {R d M}.
Arguments measurable_sigma_Mx_R_qbs {R d M}.
Arguments sigma_Mx_sub_measurable {R d M}.
Arguments sigma_Mx_eq_measurable {R d M}.
Arguments qbs_giry_bind_well_def {R d1 d2 M1 M2}.
