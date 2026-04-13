(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals ereal topology
  classical_sets borel_hierarchy measure kernel probability
  measurable_structure measurable_function measure_function
  lebesgue_integral lebesgue_measure probability_measure
  lebesgue_stieltjes_measure.
From QBS Require Import quasi_borel measure_qbs_adjunction
  probability_qbs qbs_giry.

(**md*************************************************************)
(* # Bridge: QBS Probability and S-Finite Kernels               *)
(*                                                               *)
(* Following Heunen-Kammar-Staton-Yang (2017), we connect the   *)
(* QBS probability monad to the s-finite kernel formalism of    *)
(* mathcomp-analysis 1.16.0.                                    *)
(*                                                               *)
(* Key results:                                                  *)
(* ```                                                           *)
(*   probability_fin_num_fun   == probability measures have      *)
(*                                finite values                  *)
(*   prob_sfinite_measure      == probability => s-finite        *)
(*   qbs_prob_sfinite          == QBS probs are s-finite via     *)
(*                                qbs_to_giry                    *)
(*   qbs_morph_kdirac          == QBS morph on std Borel gives   *)
(*                                a Dirac probability kernel     *)
(*   qbs_to_giry_map           == qbs_to_giry commutes with     *)
(*                                pushforward (monadP_map)       *)
(*   kdirac_comp_noparam       == composition of Dirac kernels   *)
(*                                is the Dirac of composition    *)
(*   kernel_round_trip         == qbs_to_giry o giry_to_qbs = id*)
(*   qbs_prob_equiv_giry       == equiv QBS probs => same Giry   *)
(*   kernel_integration        == QBS integral = Lebesgue vs     *)
(*                                qbs_to_giry                    *)
(* ```                                                           *)
(*****************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_kernel.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(** ** Probability measures are s-finite *)

(** A probability measure is [fin_num_fun]: every
    measurable set receives a finite value. *)
Lemma probability_fin_num_fun
    (d : measure_display) (T : measurableType d)
    (P : probability T R) :
  fin_num_fun P.
Proof. by move=> U mU; exact: fin_num_measure. Qed.

(** A probability measure satisfies [sfinite_measure].
    Probabilities are finite, hence sigma-finite,
    hence s-finite. *)
Lemma prob_sfinite_measure
    (d : measure_display) (T : measurableType d)
    (P : probability T R) :
  sfinite_measure P.
Proof.
apply: sfinite_measure_sigma_finite.
apply: fin_num_fun_sigma_finite.
  by rewrite measure0.
exact: probability_fin_num_fun.
Qed.

(** The Giry image of a QBS probability is s-finite. *)
Lemma qbs_prob_sfinite
    (d : measure_display) (M : measurableType d)
    (p : qbs_prob (@R_qbs R _ M)) :
  sfinite_measure (qbs_to_giry p).
Proof. exact: prob_sfinite_measure. Qed.

(** ** Pushforward preserves probability *)

Section pushforward_prob.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1).
Variables (M2 : measurableType d2).

(** The pushforward of a probability through a
    measurable function has total mass 1. *)
Lemma pushforward_probability
    (P : probability M1 R)
    (f : M1 -> M2) (hf : measurable_fun setT f) :
  pushforward P f setT = 1.
Proof.
by rewrite /pushforward /= preimage_setT
           probability_setT.
Qed.

End pushforward_prob.

(** ** Dirac kernel: kdirac unfolds to dirac *)

Section kdirac_unfold.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1).
Variables (M2 : measurableType d2).

(** [kdirac hf x U = dirac (f x) U]. *)
Lemma kdiracE
    (f : M1 -> M2) (hf : measurable_fun setT f)
    (x : M1) (U : set M2) :
  kdirac hf x U = @dirac _ M2 (f x) R U.
Proof. by []. Qed.

End kdirac_unfold.

(** ** QBS return and Dirac kernel *)

Section qbs_return_dirac.
Variables (d : measure_display) (M : measurableType d).
Variables (encode : M -> mR) (decode : mR -> M).
Hypothesis encode_meas : measurable_fun setT encode.
Hypothesis decode_meas : measurable_fun setT decode.
Hypothesis decode_encode :
  forall y : M, decode (encode y) = y.

(** For standard Borel M (with encode/decode),
    qbs_to_giry of the Dirac probability at x,
    passed through giry_to_qbs, recovers dirac(x). *)
Lemma qbs_return_to_dirac
    (x : M) (U : set M) (mU : measurable U) :
  qbs_to_giry
    (giry_to_qbs encode_meas decode_meas
      [the probability M R of @dirac _ M x R]) U =
  @dirac _ M x R U.
Proof.
exact: (@qbs_to_giryK R _ M encode decode
  encode_meas decode_meas decode_encode
  [the probability M R of @dirac _ M x R] U mU).
Qed.

End qbs_return_dirac.

(** ** QBS morphisms to kernels via standard Borel *)

Section qbs_morph_kernel.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1).
Variables (M2 : measurableType d2).
Hypothesis sb1 : is_standard_borel R M1.
Hypothesis sb2 : is_standard_borel R M2.

(** A measurable function f : M1 -> M2 yields a
    Dirac kernel, which is automatically a
    probability kernel. *)
Definition measfun_kernel
    (f : M1 -> M2) (hf : measurable_fun setT f) :
  M1 -> measure M2 R :=
  @kdirac _ _ _ _ R f hf.

(** The Dirac kernel has total mass 1. *)
Lemma measfun_kernel_prob
    (f : M1 -> M2) (hf : measurable_fun setT f)
    (x : M1) :
  measfun_kernel hf x setT = 1.
Proof.
by rewrite /measfun_kernel /kdirac /= diracT.
Qed.

(** A QBS morphism between standard Borel spaces is
    measurable (by full faithfulness of R). *)
Lemma qbs_morph_is_measurable
    (f : M1 -> M2)
    (hf : @qbs_morphism R
      (@R_qbs R _ M1) (@R_qbs R _ M2) f) :
  measurable_fun setT f.
Proof.
exact: (R_full_faithful_standard_borel sb1 sb2 hf).
Qed.

(** From a QBS morphism, extract a Dirac kernel.
    This is the key bridge: QBS morphisms lift to
    probability kernels on standard Borel spaces. *)
Definition qbs_morph_kdirac
    (f : M1 -> M2)
    (hf : @qbs_morphism R
      (@R_qbs R _ M1) (@R_qbs R _ M2) f) :
  M1 -> measure M2 R :=
  @kdirac _ _ _ _ R f
    (R_full_faithful_standard_borel sb1 sb2 hf).

Lemma qbs_morph_kdirac_prob
    (f : M1 -> M2)
    (hf : @qbs_morphism R
      (@R_qbs R _ M1) (@R_qbs R _ M2) f)
    (x : M1) :
  qbs_morph_kdirac hf x setT = 1.
Proof.
by rewrite /qbs_morph_kdirac /kdirac /= diracT.
Qed.

End qbs_morph_kernel.

(** ** Kernel measurability of the Dirac kernel *)

Section kdirac_measurability.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1).
Variables (M2 : measurableType d2).

(** For each measurable U, x |-> kdirac(f)(x)(U) is
    a measurable function (the kernel condition). *)
Lemma kdirac_measurable_kernel
    (f : M1 -> M2) (hf : measurable_fun setT f)
    (U : set M2) (mU : measurable U) :
  measurable_fun setT
    (fun x : M1 => @kdirac _ _ _ _ R f hf x U).
Proof. exact: measurable_kernel. Qed.

End kdirac_measurability.

(** ** Constant kernel from a QBS probability *)

Section const_kernel.
Variables (d : measure_display) (M : measurableType d).

(** A single QBS probability gives a constant kernel:
    every input maps to the same probability on M. *)
Definition const_kernel_of_qbs
    (p : qbs_prob (@R_qbs R _ M)) :
  mR -> measure M R :=
  fun _ => qbs_to_giry p.

Lemma const_kernel_of_qbs_measurable
    (p : qbs_prob (@R_qbs R _ M))
    (U : set M) (mU : measurable U) :
  measurable_fun setT
    (fun x : mR => const_kernel_of_qbs p x U).
Proof. by rewrite /const_kernel_of_qbs /=;
  exact: measurable_cst. Qed.

End const_kernel.

(** ** Equivalence preservation *)

Section equiv_kernel.
Variables (d : measure_display) (M : measurableType d).

(** Equivalent QBS probabilities yield the same
    probability measure via qbs_to_giry. *)
Lemma qbs_prob_equiv_giry
    (p1 p2 : qbs_prob (@R_qbs R _ M))
    (hequiv :
      qbs_prob_equiv (@R_qbs R _ M) p1 p2) :
  forall U : set M, measurable U ->
    qbs_to_giry p1 U = qbs_to_giry p2 U.
Proof.
move=> U mU.
rewrite /qbs_to_giry /qbs_to_giry_mu /=.
apply: hequiv.
exact: (@adjunction_counit R _ M U mU).
Qed.

End equiv_kernel.

(** ** Pushforward commutes with qbs_to_giry *)

Section giry_pushforward.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1).
Variables (M2 : measurableType d2).

(** qbs_to_giry(monadP_map(f,p)) = pushforward of
    qbs_to_giry(p) through f. *)
Lemma qbs_to_giry_map
    (f : M1 -> M2)
    (hf : measurable_fun setT f)
    (p : qbs_prob (@R_qbs R _ M1))
    (U : set M2) (mU : measurable U) :
  qbs_to_giry
    (monadP_map (@R_qbs R _ M1)
      (@R_qbs R _ M2) f (R_qbs_morph hf) p) U =
  pushforward (qbs_to_giry p) f U.
Proof.
by rewrite /pushforward /qbs_to_giry
           /qbs_to_giry_mu /monadP_map.
Qed.

(** Pushforward of qbs_to_giry through f also
    equals the qbs_to_giry_mu of the mapped triple. *)
Lemma qbs_giry_pushforward
    (f : M1 -> M2)
    (hf : measurable_fun setT f)
    (p : qbs_prob (@R_qbs R _ M1))
    (U : set M2) (mU : measurable U) :
  pushforward (qbs_to_giry p) f U =
  @qbs_to_giry_mu R _ M2
    (monadP_map (@R_qbs R _ M1)
      (@R_qbs R _ M2) f (R_qbs_morph hf) p) U.
Proof.
by rewrite /pushforward /qbs_to_giry_mu
           /monadP_map /=.
Qed.

End giry_pushforward.

(** ** Composition of Dirac kernels *)

Section dirac_comp.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1).
Variables (M2 : measurableType d2).

(** kdirac(g o f)(x) = kdirac(g)(f(x)), i.e.,
    the Dirac kernel of a composition is the
    pointwise composition. *)
Lemma kdirac_comp
    (d3 : measure_display)
    (M3 : measurableType d3)
    (f : M1 -> M2) (hf : measurable_fun setT f)
    (g : M2 -> M3) (hg : measurable_fun setT g)
    (x : M1) (U : set M3) (mU : measurable U) :
  @kdirac _ _ _ _ R _
    (measurableT_comp hg hf) x U =
  @kdirac _ _ _ _ R _ hg (f x) U.
Proof. by rewrite /kdirac /=. Qed.

(** kcomp_noparam of two Dirac kernels is the
    Dirac of the composed function: the
    functoriality of deterministic kernels. *)
Lemma kdirac_comp_noparam
    (d3 : measure_display)
    (M3 : measurableType d3)
    (f : M1 -> M2) (hf : measurable_fun setT f)
    (g : M2 -> M3) (hg : measurable_fun setT g)
    (x : M1) (U : set M3) (mU : measurable U) :
  kcomp_noparam (kdirac hf) (kdirac hg) x U =
  @dirac _ M3 (g (f x)) R U.
Proof.
rewrite /kcomp_noparam /=.
have hm : measurable_fun setT
    (fun y : M2 => @dirac _ M3 (g y) R U).
  exact: measurableT_comp (measurable_fun_dirac mU) hg.
rewrite (@integral_dirac _ M2 (f x) R setT
  measurableT _ hm).
by rewrite diracT mul1e.
Qed.

End dirac_comp.

(** ** Bind of qbs_return via a measurable function *)

Section bind_return.
Variables (d1 d2 : measure_display).
Variables (M1 : measurableType d1).
Variables (M2 : measurableType d2).

(** Binding qbs_return(x) with (y |-> return(f y))
    is equivalent to qbs_return(f x).
    This is the QBS counterpart of the kernel identity
    kdirac(f)(x) = dirac(f x). *)
Lemma qbs_bind_return_map
    (f : M1 -> M2)
    (hf : measurable_fun setT f)
    (x : @R_qbs R _ M1)
    (mu : probability mR R) :
  @qbs_prob_equiv R (@R_qbs R _ M2)
    (qbs_bind (@R_qbs R _ M1) (@R_qbs R _ M2)
      (qbs_return (@R_qbs R _ M1) x mu)
      (fun y : @R_qbs R _ M1 =>
        qbs_return (@R_qbs R _ M2) (f y) mu)
      (qbs_bind_alpha_random_const x
        (fun y : @R_qbs R _ M1 =>
          qbs_return (@R_qbs R _ M2)
            (f y) mu)))
    (qbs_return (@R_qbs R _ M2) (f x) mu).
Proof. by move=> U hU. Qed.

End bind_return.

(** ** Integration correspondence *)

Section integration.
Variables (d : measure_display) (M : measurableType d).

(** Integration against qbs_to_giry equals the
    QBS integral (restates qbs_integral_giry). *)
Lemma kernel_integration
    (p : qbs_prob (@R_qbs R _ M))
    (f : M -> \bar R)
    (f_meas : measurable_fun setT f)
    (f_int : (qbs_prob_mu p).-integrable setT
      (f \o qbs_prob_alpha p)) :
  @qbs_integral R (@R_qbs R _ M) p f =
  \int[qbs_to_giry p]_y f y.
Proof.
exact: (@qbs_integral_giry R _ M p f f_meas f_int).
Qed.

End integration.

(** ** Standard Borel round-trip *)

Section round_trip.
Variables (d : measure_display) (M : measurableType d).
Variables (encode : M -> mR) (decode : mR -> M).
Hypothesis encode_meas : measurable_fun setT encode.
Hypothesis decode_meas : measurable_fun setT decode.
Hypothesis decode_encode :
  forall x : M, decode (encode x) = x.

(** kdirac(decode)(encode(x)) = dirac(x). *)
Lemma kdirac_round_trip
    (x : M) (U : set M) :
  measurable U ->
  kdirac decode_meas (encode x) U =
  @dirac _ M x R U.
Proof. by move=> mU; rewrite /kdirac /= decode_encode. Qed.

(** qbs_to_giry(giry_to_qbs(P))(U) = P(U). *)
Lemma kernel_round_trip
    (P : probability M R)
    (U : set M) (mU : measurable U) :
  qbs_to_giry_mu
    (giry_to_qbs encode_meas decode_meas P) U =
  P U.
Proof.
exact: (@qbs_to_giryK R _ M encode decode
  encode_meas decode_meas decode_encode P U mU).
Qed.

(** Composing encode and decode Dirac kernels via
    kcomp_noparam gives the identity kernel. *)
Lemma encode_decode_kcomp_noparam
    (x : M) (U : set M) (mU : measurable U) :
  kcomp_noparam (kdirac encode_meas)
    (kdirac decode_meas) x U =
  @dirac _ M x R U.
Proof.
rewrite kdirac_comp_noparam //.
by rewrite decode_encode.
Qed.

End round_trip.

End qbs_kernel.
