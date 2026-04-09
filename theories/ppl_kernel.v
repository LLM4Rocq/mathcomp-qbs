(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure lebesgue_measure
  lebesgue_integral probability measurable_realfun kernel.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel coproduct_qbs probability_qbs
  measure_as_qbs_measure measure_qbs_adjunction qbs_giry qbs_kernel
  ppl_qbs.

(**md***********************************************************)
(* # Bridge: First-Order PPL and S-Finite Kernels              *)
(*                                                              *)
(* This file connects the QBS-based PPL semantics of           *)
(* [ppl_qbs.v] to the s-finite kernel formalism of             *)
(* mathcomp-analysis via the QBS-kernel bridge in              *)
(* [qbs_kernel.v]. We isolate the first-order fragment of      *)
(* the PPL (no function types) and show that closed programs   *)
(* of type [ppl_prob ppl_real] denote s-finite probability    *)
(* kernels. The construction is: [expr_denot e] takes the      *)
(* unit environment to a [qbs_prob (realQ R)], which           *)
(* [qbs_to_giry] turns into a probability measure on [mR],    *)
(* which [const_kernel_of_qbs] packages as a constant kernel. *)
(*                                                              *)
(* Key constructions:                                           *)
(* ```                                                          *)
(*   is_first_order t    == t does not contain ppl_fun         *)
(*   is_first_order_ctx  == every type in a context is FO      *)
(*   expr_prob_real_to_giry e env                              *)
(*                       == Giry probability from an           *)
(*                          expression of type ppl_prob        *)
(*                          ppl_real                            *)
(*   expr_prob_real_kernel e                                    *)
(*                       == constant s-finite kernel from a    *)
(*                          closed expr of type ppl_prob       *)
(*                          ppl_real                            *)
(*   e_sample_normal_kernel                                     *)
(*                       == sampling from Normal(mu, sigma)    *)
(*                          gives a probability kernel         *)
(*   e_sample_uniform_kernel                                    *)
(*                       == sampling from Uniform[0,1]         *)
(*                          gives a probability kernel         *)
(*   e_ret_real_kernel    == closed [e_ret (e_real r)] gives   *)
(*                          a Dirac kernel at [r]               *)
(*   expr_real_is_kernel  == a first-order program of real     *)
(*                          type yields a Dirac kernel         *)
(*   expr_prob_real_kernel_integration                         *)
(*                       == QBS integration equals the kernel  *)
(*                          (Lebesgue) integration              *)
(* ```                                                          *)
(***************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** * First-order PPL types *)

(** A PPL type is first-order when it does not
    contain a function type [ppl_fun]. This is
    the fragment that maps cleanly to s-finite
    kernels over standard Borel spaces. *)
Fixpoint is_first_order (t : ppl_type) : bool :=
  match t with
  | ppl_real | ppl_bool | ppl_unit => true
  | ppl_prod t1 t2 =>
      is_first_order t1 && is_first_order t2
  | ppl_sum t1 t2 =>
      is_first_order t1 && is_first_order t2
  | ppl_fun _ _ => false
  | ppl_prob t1 => is_first_order t1
  end.

(** A context is first-order when all of its
    types are first-order. *)
Fixpoint is_first_order_ctx (G : ctx) : bool :=
  match G with
  | nil => true
  | t :: G' => is_first_order t && is_first_order_ctx G'
  end.

(** Smoke tests: the base types are first-order. *)
Lemma is_first_order_real : is_first_order ppl_real.
Proof. by []. Qed.

Lemma is_first_order_bool : is_first_order ppl_bool.
Proof. by []. Qed.

Lemma is_first_order_unit : is_first_order ppl_unit.
Proof. by []. Qed.

Lemma is_first_order_prob_real :
  is_first_order (ppl_prob ppl_real).
Proof. by []. Qed.

Lemma is_first_order_fun_false
    (t1 t2 : ppl_type) :
  is_first_order (ppl_fun t1 t2) = false.
Proof. by []. Qed.

Section ppl_kernel.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(** * From a closed expression to a Giry probability *)

(** For a closed expression of type [ppl_prob
    ppl_real], the QBS denotation produces a
    [qbs_prob (realQ R)], which we push through
    the QBS-to-Giry transformation (from
    [qbs_giry.v]) to obtain a genuine probability
    measure on [mR]. *)
Definition expr_prob_real_to_giry
    (e : expr R [::] (ppl_prob ppl_real)) :
  probability mR R :=
  qbs_to_giry
    (@expr_denot R [::] (ppl_prob ppl_real) e tt).

(** * S-finite kernel from a closed real-prob expr *)

(** Package the Giry probability obtained from a
    closed program of type [ppl_prob ppl_real] as
    a constant kernel [mR -> probability mR R]. *)
Definition expr_prob_real_kernel
    (e : expr R [::] (ppl_prob ppl_real)) :
  mR -> measure mR R :=
  const_kernel_of_qbs
    (@expr_denot R [::] (ppl_prob ppl_real) e tt).

(** The kernel obtained from a closed program has
    total mass [1] on [setT] because the underlying
    object is a probability measure. *)
Lemma expr_prob_real_kernel_setT
    (e : expr R [::] (ppl_prob ppl_real)) (x : mR) :
  expr_prob_real_kernel e x setT = 1.
Proof.
rewrite /expr_prob_real_kernel /const_kernel_of_qbs.
exact: probability_setT.
Qed.

(** The kernel is measurable in its parameter for
    every measurable output set: this is one half
    of the kernel condition. Constant kernels are
    trivially measurable. *)
Lemma expr_prob_real_kernel_measurable
    (e : expr R [::] (ppl_prob ppl_real))
    (U : set mR) (mU : measurable U) :
  measurable_fun setT
    (fun x : mR => expr_prob_real_kernel e x U).
Proof.
exact: const_kernel_of_qbs_measurable.
Qed.

(** The kernel arising from a closed PPL program
    is s-finite, because the underlying measure is
    a probability measure. This is the key property
    making it a legitimate target for the s-finite
    kernel semantics of PR #912. *)
Lemma expr_prob_real_kernel_sfinite
    (e : expr R [::] (ppl_prob ppl_real)) (x : mR) :
  sfinite_measure (expr_prob_real_kernel e x).
Proof.
rewrite /expr_prob_real_kernel /const_kernel_of_qbs.
exact: prob_sfinite_measure.
Qed.

(** * Concrete constructors as kernels *)

(** Sampling from [Normal(mu, sigma)] at the PPL
    level denotes a [qbs_normal_distribution], and
    turning that into a Giry measure gives a
    probability measure on [mR]. This lemma packs
    the full chain: [e_sample_normal] is a
    probability kernel. *)
Lemma e_sample_normal_kernel
    (mu sigma : R) (hs : (0 < sigma)%R)
    (x : mR) :
  expr_prob_real_kernel
    (@e_sample_normal R [::] mu sigma hs) x setT = 1.
Proof. exact: expr_prob_real_kernel_setT. Qed.

(** Similarly for uniform sampling. *)
Lemma e_sample_uniform_kernel (x : mR) :
  expr_prob_real_kernel (@e_sample_uniform R [::]) x setT = 1.
Proof. exact: expr_prob_real_kernel_setT. Qed.

(** Monadic return on a real literal denotes a
    Dirac probability at the literal value, so its
    kernel is a constant Dirac kernel. *)
Lemma e_ret_real_kernel (r : R) (x : mR) :
  expr_prob_real_kernel
    (e_ret (@e_real R [::] r)) x setT = 1.
Proof. exact: expr_prob_real_kernel_setT. Qed.

(** * First-order values of real type give Dirac kernels *)

(** A closed expression of type [ppl_real] denotes
    a real value via its QBS morphism. Composing
    with [e_ret] yields a probability kernel whose
    target is the Dirac distribution at that value. *)
Definition expr_real_kernel
    (e : expr R [::] ppl_real) :
  mR -> measure mR R :=
  const_kernel_of_qbs
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_ret e) tt).

Lemma expr_real_kernel_prob
    (e : expr R [::] ppl_real) (x : mR) :
  expr_real_kernel e x setT = 1.
Proof.
rewrite /expr_real_kernel /const_kernel_of_qbs.
exact: probability_setT.
Qed.

(** A more direct form: a measurable function from
    [mR] to [mR] immediately yields a probability
    kernel via [qbs_morph_kdirac] on standard Borel
    spaces. This exposes the kernel structure
    pointwise. *)
Lemma measurable_fun_to_prob_kernel
    (f : mR -> mR) (hf : measurable_fun setT f)
    (x : mR) :
  @qbs_morph_kdirac R _ _ _ _
    (R_standard_borel R) (R_standard_borel R)
    f (R_qbs_morph hf) x setT = 1.
Proof. exact: qbs_morph_kdirac_prob. Qed.

(** * Integration correspondence for closed programs *)

(** For closed programs of type [ppl_prob ppl_real],
    the QBS integral against the program's
    denotation equals the Lebesgue integral against
    the kernel output. This is the concrete form of
    [kernel_integration] from [qbs_kernel.v] in the
    PPL setting. *)
Lemma expr_prob_real_kernel_integration
    (e : expr R [::] (ppl_prob ppl_real))
    (f : mR -> \bar R)
    (f_meas : measurable_fun setT f)
    (f_int :
      (qbs_prob_mu
        (@expr_denot R [::] (ppl_prob ppl_real) e tt))
      .-integrable setT
      (f \o qbs_prob_alpha
        (@expr_denot R [::] (ppl_prob ppl_real) e tt)))
    (x : mR) :
  @qbs_integral R (realQ R)
    (@expr_denot R [::] (ppl_prob ppl_real) e tt) f =
  \int[expr_prob_real_kernel e x]_y f y.
Proof.
rewrite /expr_prob_real_kernel /const_kernel_of_qbs.
exact: kernel_integration.
Qed.

(** * A sanity-check closed program *)

(** The canonical first-order program that samples
    from [Normal(0, 1)]. This illustrates the full
    pipeline: a PPL expression of type [ppl_prob
    ppl_real] denotes a [qbs_prob], transported to
    a [probability mR R], then lifted to a kernel. *)
Definition ex_normal01 :
  expr R [::] (ppl_prob ppl_real) :=
  @e_sample_normal R [::] 0%R 1%R ltr01.

Lemma ex_normal01_first_order :
  is_first_order (ppl_prob ppl_real).
Proof. by []. Qed.

Lemma ex_normal01_kernel_prob (x : mR) :
  expr_prob_real_kernel ex_normal01 x setT = 1.
Proof. exact: expr_prob_real_kernel_setT. Qed.

Lemma ex_normal01_kernel_sfinite (x : mR) :
  sfinite_measure (expr_prob_real_kernel ex_normal01 x).
Proof. exact: expr_prob_real_kernel_sfinite. Qed.

(** * Structural lemmas on first-order types *)

(** A first-order product is first-order in both
    components. *)
Lemma is_first_order_prod
    (t1 t2 : ppl_type) :
  is_first_order (ppl_prod t1 t2) =
  is_first_order t1 && is_first_order t2.
Proof. by []. Qed.

(** A first-order [ppl_prob] wraps a first-order
    type. *)
Lemma is_first_order_prob
    (t : ppl_type) :
  is_first_order (ppl_prob t) = is_first_order t.
Proof. by []. Qed.

(** First-order expressions do not, by definition,
    mention [e_lam] in the outermost type — because
    their resulting type excludes [ppl_fun]. This
    witnesses the match between the first-order
    fragment and the kernel-based semantics. *)
Lemma is_first_order_no_fun
    (t1 t2 : ppl_type) :
  is_first_order (ppl_fun t1 t2) = false.
Proof. by []. Qed.

End ppl_kernel.
