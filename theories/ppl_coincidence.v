(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure lebesgue_measure
  lebesgue_integral probability measurable_realfun kernel.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel coproduct_qbs probability_qbs
  measure_as_qbs_measure measure_qbs_adjunction qbs_giry qbs_kernel
  ppl_qbs ppl_kernel.

(**md****************************************************************)
(* # Coincidence: QBS Denotation and Kernel Semantics               *)
(*                                                                   *)
(* For first-order PPL programs (no function types), we establish    *)
(* that the QBS denotation via [expr_denot] produces the same       *)
(* probability measure as kernel composition (kcomp_noparam) would.  *)
(*                                                                   *)
(* ## Architecture                                                   *)
(*                                                                   *)
(* The [morph_ret], [morph_sample_uniform], [morph_sample_normal]   *)
(* definitions in [ppl_qbs.v] are now transparent ([Defined]),      *)
(* allowing the simple denotation equations to be proved by         *)
(* [reflexivity]: [expr_denot_ret_real],                            *)
(* [expr_denot_sample_uniform], [expr_denot_sample_normal].         *)
(*                                                                   *)
(* The [morph_bind_ret] definition is also [Defined], but its       *)
(* proof term uses ssreflect's [have] tactic which creates an      *)
(* opaque [ssr_have_upoly] wrapper. This blocks computation for     *)
(* the bind-related equations, which remain as hypotheses.          *)
(*                                                                   *)
(* The [integral_dirac_indicator] bridge lemma is now proved        *)
(* using [integral_indic] from mathcomp-analysis.                   *)
(*                                                                   *)
(* 1. **Proved** denotation equations: [expr_denot_ret_real],       *)
(*    [expr_denot_sample_uniform], [expr_denot_sample_normal],      *)
(*    and [integral_dirac_indicator].                                *)
(*                                                                   *)
(* 2. **Hypothesized** bind equations (blocked by                   *)
(*    [ssr_have_upoly]): would be provable if [morph_bind_ret]     *)
(*    avoided ssreflect's [have] tactic.                            *)
(*                                                                   *)
(* 3. Derive the **coincidence theorems** from those equations,     *)
(*    connecting the QBS denotation to kernel composition.           *)
(*                                                                   *)
(* 4. Prove the **integration bridge** connecting QBS integrals     *)
(*    to Lebesgue integrals via [kernel_integration].               *)
(*                                                                   *)
(* Key results:                                                      *)
(* ```                                                               *)
(*   ret_real_coincidence      == e_ret(e_real c) gives dirac(c)    *)
(*   sample_uniform_coincidence== e_sample_uniform gives uniform     *)
(*   sample_normal_coincidence == e_sample_normal gives normal_prob  *)
(*   bind_sample_ret_coincidence                                     *)
(*                             == e_bind(sample)(e_ret e0)           *)
(*                                gives kcomp_noparam                *)
(*   integral_dirac_indicator  == bridge: int of dirac = preimage   *)
(*   closed_program_integration                                      *)
(*                             == QBS integral = Lebesgue integral  *)
(* ```                                                               *)
(*                                                                   *)
(* ## Obstacles for the general case                                 *)
(*                                                                   *)
(* The general coincidence for [e_bind e1 e2] where [e1] is not a   *)
(* sample requires:                                                  *)
(* (a) **Measure extraction measurability**: the map                *)
(*     [x |-> qbs_to_giry(f x)(U)] must be measurable when [f]     *)
(*     is a QBS morphism into [monadP]. This holds for standard     *)
(*     Borel spaces (HKSY 2017, Prop 22.3) but is not formalized.  *)
(* (b) **Strong morphism condition**: general [qbs_bind] needs      *)
(*     [qbs_morphism_strong], which cannot be derived from the      *)
(*     pointwise condition without quotient types or the standard   *)
(*     Borel isomorphism [R ~ N x R].                               *)
(* (c) **ssr_have_upoly in morph_bind_ret**: [morph_bind_ret] is    *)
(*     now [Defined] but uses ssreflect's [have] which creates an  *)
(*     opaque [ssr_have_upoly] wrapper in the proof term. This     *)
(*     blocks computation. Fix: rewrite [morph_bind_ret] to use    *)
(*     [refine] or term-mode instead of [have].                    *)
(*****************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section ppl_coincidence.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(* ================================================================ *)
(* Part 1: Denotation equations                                     *)
(*                                                                   *)
(* The simple equations (ret_real, sample_uniform, sample_normal)   *)
(* are now proved by [by []] since [morph_ret], [morph_sample_*]    *)
(* are [Defined] and their proofs use only [exists] and [exact:].   *)
(*                                                                   *)
(* The bind-related equations remain as hypotheses: [morph_bind_ret]*)
(* is [Defined] but its proof uses ssreflect's [have] which wraps  *)
(* the term in opaque [ssr_have_upoly], blocking computation.       *)
(*                                                                   *)
(* The internal structure is:                                        *)
(*   morph_ret s    : fun env => qbs_return T (s env) uniform_prob  *)
(*   morph_sample_uniform G : fun _ => qbs_uniform                  *)
(*   morph_sample_normal G mu sigma hs                              *)
(*                  : fun _ => qbs_normal_distribution mu sigma hs  *)
(*   morph_bind_ret m1 m2                                           *)
(*                  : fun env => qbs_bind ... (m1 env)              *)
(*                       (fun x => qbs_return T (m2(x,env)) mu0)   *)
(* ================================================================ *)

(** Equation: expr_denot of e_ret (e_real c) is
    qbs_return (realQ R) c (uniform_prob ltr01). *)
Lemma expr_denot_ret_real :
  forall (c : R),
  expr_denot (e_ret (@e_real R [::] c)) tt =
  qbs_return (realQ R) c (uniform_prob (@ltr01 R)).
Proof. by []. Qed.

(** Equation: expr_denot of e_sample_uniform is qbs_uniform. *)
Lemma expr_denot_sample_uniform :
  expr_denot (@e_sample_uniform R [::]) tt =
  @qbs_uniform R.
Proof. by []. Qed.

(** Equation: expr_denot of e_sample_normal is
    qbs_normal_distribution. *)
Lemma expr_denot_sample_normal :
  forall (mu sigma : R) (hs : (0 < sigma)%R),
  expr_denot (@e_sample_normal R [::] mu sigma hs) tt =
  @qbs_normal_distribution R mu sigma hs.
Proof. by []. Qed.

(** Equation: the bind/return denotation for
    [do x <- sample_uniform; return (f x)] is a
    qbs_bind of qbs_uniform with a return continuation.

    The key structural fact: the alpha of the result is
    [fun r => expr_denot e0 (id r, tt)]
    and the mu is [uniform_prob ltr01].
    This means qbs_to_giry_mu = uniform_prob o (alpha^{-1}). *)
(* Cannot be discharged: morph_bind_ret internally uses ssreflect's
   [have] tactic which creates an opaque [ssr_have_upoly] wrapper,
   blocking computation even though morph_bind_ret is Defined.
   Fix: rewrite morph_bind_ret in ppl_qbs.v to avoid [have]. *)
Hypothesis expr_denot_bind_sample_uniform_ret :
  forall (e0 : expr R (ppl_real :: [::]) ppl_real),
  qbs_prob_alpha
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind (@e_sample_uniform R [::]) (e_ret e0)) tt) =
  fun r => @expr_denot R (ppl_real :: [::]) ppl_real e0 (r, tt).

Hypothesis expr_denot_bind_sample_uniform_ret_mu :
  forall (e0 : expr R (ppl_real :: [::]) ppl_real),
  qbs_prob_mu
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind (@e_sample_uniform R [::]) (e_ret e0)) tt) =
  uniform_prob (@ltr01 R).

(** Analogous equations for normal source.
    Cannot be discharged: same ssr_have_upoly blocker as above. *)
Hypothesis expr_denot_bind_sample_normal_ret :
  forall (mu sigma : R) (hs : (0 < sigma)%R)
    (e0 : expr R (ppl_real :: [::]) ppl_real),
  qbs_prob_alpha
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind (@e_sample_normal R [::] mu sigma hs)
        (e_ret e0)) tt) =
  fun r => @expr_denot R (ppl_real :: [::]) ppl_real e0 (r, tt).

Hypothesis expr_denot_bind_sample_normal_ret_mu :
  forall (mu sigma : R) (hs : (0 < sigma)%R)
    (e0 : expr R (ppl_real :: [::]) ppl_real),
  qbs_prob_mu
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind (@e_sample_normal R [::] mu sigma hs)
        (e_ret e0)) tt) =
  normal_prob mu sigma.

(** Equation: bind/return identity
    [do x <- e1; return x] has the same alpha and mu as e1.
    Cannot be discharged: same ssr_have_upoly blocker as above. *)
Hypothesis expr_denot_bind_ret_id_alpha :
  forall (e1 : expr R [::] (ppl_prob ppl_real)),
  qbs_prob_alpha
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind e1
        (e_ret (@e_var R _ _ (@var_here [::] ppl_real)))) tt) =
  qbs_prob_alpha (@expr_denot R [::] (ppl_prob ppl_real) e1 tt).

Hypothesis expr_denot_bind_ret_id_mu :
  forall (e1 : expr R [::] (ppl_prob ppl_real)),
  qbs_prob_mu
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind e1
        (e_ret (@e_var R _ _ (@var_here [::] ppl_real)))) tt) =
  qbs_prob_mu (@expr_denot R [::] (ppl_prob ppl_real) e1 tt).

(* ================================================================ *)
(* Part 2: Coincidence for concrete constructors                    *)
(*                                                                   *)
(* Using the denotation equations, we show that the QBS-to-Giry     *)
(* transformation of each constructor's denotation equals the       *)
(* expected probability measure.                                    *)
(* ================================================================ *)

(** ** e_ret (e_real c) denotes dirac(c) *)

Theorem ret_real_coincidence (c : R) (U : set mR) :
  measurable U ->
  qbs_to_giry_mu
    (expr_denot (e_ret (@e_real R [::] c)) tt) U =
  @dirac _ mR c R U.
Proof.
move=> mU.
rewrite expr_denot_ret_real.
rewrite /qbs_to_giry_mu /=.
(* alpha = fun _ => c, mu = uniform_prob ltr01 *)
(* preimage of (fun _ => c) at U *)
case: (asboolP (U c)) => hc.
- have -> : (fun _ : mR => c) @^-1` U = setT.
    by apply/seteqP; split => // r _; rewrite /preimage.
  rewrite probability_setT.
  by rewrite /dirac /= numfun.indicE mem_set.
- have -> : (fun _ : mR => c) @^-1` U = set0.
    by apply/seteqP; split => // r; rewrite /preimage.
  rewrite measure0.
  by rewrite /dirac /= numfun.indicE memNset.
Qed.

(** ** e_sample_uniform denotes uniform_prob *)

Theorem sample_uniform_coincidence (U : set mR) :
  measurable U ->
  qbs_to_giry_mu
    (expr_denot (@e_sample_uniform R [::]) tt) U =
  uniform_prob (@ltr01 R) U.
Proof.
move=> mU.
rewrite expr_denot_sample_uniform.
rewrite /qbs_to_giry_mu /=.
by rewrite preimage_id.
Qed.

(** ** e_sample_normal denotes normal_prob *)

Theorem sample_normal_coincidence
    (mu sigma : R) (hs : (0 < sigma)%R) (U : set mR) :
  measurable U ->
  qbs_to_giry_mu
    (expr_denot (@e_sample_normal R [::] mu sigma hs) tt) U =
  normal_prob mu sigma U.
Proof.
move=> mU.
rewrite expr_denot_sample_normal.
rewrite /qbs_to_giry_mu /=.
by rewrite preimage_id.
Qed.

(* ================================================================ *)
(* Part 3: Integration bridge                                       *)
(*                                                                   *)
(* The key lemma connecting measures to kernels: integrating         *)
(* [dirac(f(y))(U)] against a measure [mu] equals [mu(f^{-1}(U))]. *)
(* This is the change-of-variables formula in the Dirac case.       *)
(* ================================================================ *)

(** Integrating dirac(f(y))(U) against a measure mu equals
    mu(f^{-1}(U)). This is the change-of-variables formula for
    Dirac measures: dirac(f(y))(U) = indic(f^{-1}(U))(y), so
    the integral reduces to mu(f^{-1}(U)) by integral_indic. *)
Lemma integral_dirac_indicator :
  forall (d : measure_display) (T : measurableType d)
    (mu : measure T R) (f : T -> mR)
    (hf : measurable_fun setT f) (U : set mR)
    (mU : measurable U),
  \int[mu]_y @dirac _ mR (f y) R U = mu (f @^-1` U).
Proof.
move=> d T mu f hf U mU.
have mfU : d.-measurable (f @^-1` U).
  have := hf measurableT U mU.
  by rewrite setTI.
transitivity (mu (f @^-1` U `&` setT)).
  rewrite -(@integral_indic _ _ _ mu setT measurableT _ mfU).
  apply: eq_integral => y _.
  by rewrite diracE numfun.indicE /preimage.
by rewrite setIT.
Qed.

(** The existing integration correspondence from ppl_kernel.v:
    QBS integration equals Lebesgue integration against the
    kernel. *)
Lemma closed_program_integration
    (e : expr R [::] (ppl_prob ppl_real))
    (f : mR -> \bar R)
    (f_meas : measurable_fun setT f)
    (f_int :
      (qbs_prob_mu (expr_denot e tt)).-integrable setT
      (f \o qbs_prob_alpha (expr_denot e tt))) :
  @qbs_integral R (realQ R) (expr_denot e tt) f =
  \int[expr_prob_real_kernel e (0%R : mR)]_y f y.
Proof. exact: expr_prob_real_kernel_integration. Qed.

(* ================================================================ *)
(* Part 4: Bind/return coincidence with kcomp_noparam               *)
(*                                                                   *)
(* The main results: for programs of the form                       *)
(* [e_bind (e_sample) (e_ret e0)], the QBS denotation produces     *)
(* the same measure as kcomp_noparam of the component kernels.      *)
(* ================================================================ *)

(** ** Bind/sample_uniform/return coincidence *)

(** For [do x <- sample_uniform; return (e0 x)], the QBS
    denotation's Giry measure equals kcomp_noparam of uniform_prob
    and (fun y => dirac(e0(y,tt))).

    This is the central coincidence: the QBS bind/return computes
    the same measure as kernel composition via integration. *)
Theorem bind_sample_ret_coincidence
    (e0 : expr R (ppl_real :: [::]) ppl_real)
    (he0 : measurable_fun setT
      (fun y : mR => @expr_denot R _ _ e0 (y, tt))) (U : set mR) :
  measurable U ->
  qbs_to_giry_mu
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind (@e_sample_uniform R [::]) (e_ret e0)) tt) U =
  kcomp_noparam
    (fun _ : mR => uniform_prob (@ltr01 R) : measure mR R)
    (fun y : mR =>
      @dirac _ mR (@expr_denot R _ _ e0 (y, tt)) R : measure mR R)
    (0%R : mR) U.
Proof.
move=> mU.
(* LHS: pushforward of mu through alpha
   = mu (alpha @^-1` U)
   = uniform_prob ((fun r => e0(r,tt)) @^-1` U) *)
rewrite /qbs_to_giry_mu.
rewrite expr_denot_bind_sample_uniform_ret.
rewrite expr_denot_bind_sample_uniform_ret_mu.
(* RHS: kcomp_noparam gives integral *)
rewrite /kcomp_noparam /=.
(* \int[uniform_prob]_y dirac(e0(y,tt)) U
   = uniform_prob ((fun y => e0(y,tt)) @^-1` U)
   by integral_dirac_indicator *)
by rewrite integral_dirac_indicator.
Qed.

(** ** Bind/sample_normal/return coincidence *)

Theorem bind_normal_ret_coincidence
    (mu sigma : R) (hs : (0 < sigma)%R)
    (e0 : expr R (ppl_real :: [::]) ppl_real)
    (he0 : measurable_fun setT
      (fun y : mR => @expr_denot R _ _ e0 (y, tt))) (U : set mR) :
  measurable U ->
  qbs_to_giry_mu
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind (@e_sample_normal R [::] mu sigma hs)
        (e_ret e0)) tt) U =
  kcomp_noparam
    (fun _ : mR => normal_prob mu sigma : measure mR R)
    (fun y : mR =>
      @dirac _ mR (@expr_denot R _ _ e0 (y, tt)) R : measure mR R)
    (0%R : mR) U.
Proof.
move=> mU.
rewrite /qbs_to_giry_mu.
rewrite (expr_denot_bind_sample_normal_ret mu hs).
rewrite (expr_denot_bind_sample_normal_ret_mu mu hs).
rewrite /kcomp_noparam /=.
by rewrite integral_dirac_indicator.
Qed.

(** ** Monadic right-unit: bind/return identity *)

Theorem bind_ret_id_coincidence
    (e1 : expr R [::] (ppl_prob ppl_real)) (U : set mR) :
  measurable U ->
  qbs_to_giry_mu
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind e1
        (e_ret (@e_var R _ _ (@var_here [::] ppl_real)))) tt) U =
  qbs_to_giry_mu (@expr_denot R [::] (ppl_prob ppl_real) e1 tt) U.
Proof.
move=> mU.
rewrite /qbs_to_giry_mu.
by rewrite expr_denot_bind_ret_id_alpha
           expr_denot_bind_ret_id_mu.
Qed.

(* ================================================================ *)
(* Part 5: Coincidence in kernel form                               *)
(*                                                                   *)
(* The same results expressed through expr_prob_real_kernel          *)
(* (the constant kernel from ppl_kernel.v) and the existing         *)
(* kernel properties.                                                *)
(* ================================================================ *)

(** ** Total mass: all closed programs give probability kernels *)

(** Every closed program of type ppl_prob ppl_real produces a
    probability kernel (total mass 1). This is already proven
    in ppl_kernel.v as expr_prob_real_kernel_setT; we re-export
    it here for completeness. *)
Lemma kernel_is_probability
    (e : expr R [::] (ppl_prob ppl_real)) (x : mR) :
  expr_prob_real_kernel e x setT = 1.
Proof. exact: expr_prob_real_kernel_setT. Qed.

(** ** S-finiteness: kernels from closed programs are s-finite *)

Lemma kernel_sfinite
    (e : expr R [::] (ppl_prob ppl_real)) (x : mR) :
  sfinite_measure (expr_prob_real_kernel e x).
Proof. exact: expr_prob_real_kernel_sfinite. Qed.

(** ** The kernel is constant: it does not depend on the input *)

Lemma kernel_constant
    (e : expr R [::] (ppl_prob ppl_real)) (x y : mR)
    (U : set mR) :
  expr_prob_real_kernel e x U = expr_prob_real_kernel e y U.
Proof. by rewrite /expr_prob_real_kernel /const_kernel_of_qbs. Qed.

(* ================================================================ *)
(* Part 6: The general coincidence theorem (statement)              *)
(*                                                                   *)
(* For a closed first-order program [e : expr R [::] (ppl_prob      *)
(* ppl_real)], we want:                                             *)
(*                                                                   *)
(*   qbs_to_giry_mu (expr_denot e tt) U                             *)
(*   = kernel_semantics(e)(U)                                       *)
(*                                                                   *)
(* where kernel_semantics interprets each constructor as:           *)
(*   e_ret(e_real c)         ~> dirac(c)                            *)
(*   e_sample_uniform        ~> uniform_prob                        *)
(*   e_sample_normal mu s hs ~> normal_prob mu s                    *)
(*   e_bind e1 (e_ret e0)    ~> kcomp_noparam K1 K2                *)
(*     where K1 = kernel_semantics(e1)                              *)
(*           K2(y) = dirac(expr_denot e0 (y, env))                  *)
(*                                                                   *)
(* We have proved the coincidence for:                              *)
(*   - All three primitive distributions (Part 2)                   *)
(*   - bind/return with sample source (Part 4)                      *)
(*   - The monadic right-unit law (Part 4)                          *)
(*                                                                   *)
(* The remaining obstacles for the GENERAL e_bind case:             *)
(*                                                                   *)
(* 1. OPACITY: morph_ret, morph_bind_ret, morph_sample_* are        *)
(*    opaque. The denotation equations in Part 1 would hold by      *)
(*    reflexivity if those were transparent (Defined).               *)
(*                                                                   *)
(* 2. NON-SAMPLE SOURCES: when e1 is not a sample, the QBS triple  *)
(*    has a non-identity alpha and a non-canonical mu. The          *)
(*    coincidence requires the change-of-variables formula:         *)
(*      qbs_to_giry_mu p U = pushforward (qbs_prob_mu p)           *)
(*                              (qbs_prob_alpha p) U                *)
(*    which is definitionally true, but to relate it to             *)
(*    kcomp_noparam one needs:                                      *)
(*      \int[pushforward mu alpha]_y g(y)                           *)
(*      = \int[mu]_r g(alpha(r))                                    *)
(*    This is integral_pushforward from mathcomp-analysis.          *)
(*                                                                   *)
(* 3. MEASURE EXTRACTION: for the general bind, one needs           *)
(*      x |-> qbs_to_giry_mu (f x) U                               *)
(*    to be measurable when f is a QBS morphism into monadP.        *)
(*    This holds for standard Borel spaces (HKSY 2017) but is       *)
(*    not formalized in the codebase.                                *)
(*                                                                   *)
(* 4. STRONG MORPHISM: the current qbs_bind requires a diagonal     *)
(*    randomness proof constructed ad-hoc. The general case needs   *)
(*    qbs_morphism_strong, unavailable without quotient types.      *)
(* ================================================================ *)

(** Statement of the general coincidence (cannot be proved
    without resolving the obstacles above). We phrase it as a
    hypothesis-guarded theorem.

    With measure extraction and transparent definitions, the
    proof structure would be:
    - By induction on the first-order expression
    - Sample cases: alpha = id, coincidence immediate
    - Bind/return: use integral_dirac_indicator +
      integral_pushforward
    - Bind/sample: use integral_dirac_indicator directly *)

Hypothesis measure_extraction_measurable :
  forall (f : mR -> qbs_prob (realQ R))
    (hf : @qbs_morphism R (realQ R) (monadP (realQ R)) f)
    (U : set mR),
    measurable U ->
    measurable_fun setT (fun x => qbs_to_giry_mu (f x) U).

(** Hypothesis: denotation equations for the general bind case.
    The alpha of bind(e1, ret(e0)) applied at tt is
    [fun r => expr_denot e0 (qbs_prob_alpha(e1_denot tt) r, tt)]
    and the mu is [qbs_prob_mu(e1_denot tt)]. *)
(* Cannot be discharged: same ssr_have_upoly blocker as above. *)
Hypothesis expr_denot_bind_ret_alpha :
  forall (e1 : expr R [::] (ppl_prob ppl_real))
    (e0 : expr R (ppl_real :: [::]) ppl_real),
  qbs_prob_alpha
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind e1 (e_ret e0)) tt) =
  fun r => @expr_denot R _ _ e0
    (qbs_prob_alpha (@expr_denot R [::] (ppl_prob ppl_real) e1 tt) r, tt).

Hypothesis expr_denot_bind_ret_mu :
  forall (e1 : expr R [::] (ppl_prob ppl_real))
    (e0 : expr R (ppl_real :: [::]) ppl_real),
  qbs_prob_mu
    (@expr_denot R [::] (ppl_prob ppl_real)
      (e_bind e1 (e_ret e0)) tt) =
  qbs_prob_mu (@expr_denot R [::] (ppl_prob ppl_real) e1 tt).

(** The general bind/return coincidence for arbitrary e1. *)
Theorem bind_ret_coincidence_general
    (e1 : expr R [::] (ppl_prob ppl_real))
    (e0 : expr R (ppl_real :: [::]) ppl_real)
    (he0 : measurable_fun setT
      (fun y : mR => @expr_denot R _ _ e0 (y, tt)))
    (U : set mR) :
  measurable U ->
  qbs_to_giry_mu
    (expr_denot (e_bind e1 (e_ret e0)) tt) U =
  kcomp_noparam
    (fun _ : mR =>
      qbs_to_giry (expr_denot e1 tt) : measure mR R)
    (fun y : mR =>
      @dirac _ mR (expr_denot e0 (y, tt)) R : measure mR R)
    (0%R : mR) U.
Proof.
move=> mU.
(* LHS *)
rewrite /qbs_to_giry_mu.
rewrite expr_denot_bind_ret_alpha expr_denot_bind_ret_mu.
(* LHS is now:
   qbs_prob_mu(e1_denot tt)
     ((fun r => e0_denot(alpha_e1(r), tt)) @^-1` U) *)
(* RHS *)
rewrite /kcomp_noparam /=.
(* RHS is:
   \int[qbs_to_giry(e1_denot tt)]_y dirac(e0_denot(y,tt)) U *)
(* By integral_dirac_indicator:
   = qbs_to_giry(e1_denot tt) ((fun y => e0_denot(y,tt)) @^-1` U) *)
by rewrite integral_dirac_indicator.
Qed.

(* ================================================================ *)
(* Part 7: Summary                                                   *)
(*                                                                   *)
(* PROVED (modulo denotation equations stated as hypotheses):        *)
(*                                                                   *)
(* - ret_real_coincidence:                                           *)
(*     qbs_to_giry_mu(e_ret(e_real c)) = dirac(c)                  *)
(*                                                                   *)
(* - sample_uniform_coincidence:                                     *)
(*     qbs_to_giry_mu(e_sample_uniform) = uniform_prob              *)
(*                                                                   *)
(* - sample_normal_coincidence:                                      *)
(*     qbs_to_giry_mu(e_sample_normal) = normal_prob                *)
(*                                                                   *)
(* - bind_sample_ret_coincidence:                                    *)
(*     qbs_to_giry_mu(bind(sample_uniform, ret(e0)))                *)
(*     = kcomp_noparam(uniform, dirac o e0)                         *)
(*                                                                   *)
(* - bind_normal_ret_coincidence:                                    *)
(*     qbs_to_giry_mu(bind(sample_normal, ret(e0)))                 *)
(*     = kcomp_noparam(normal, dirac o e0)                          *)
(*                                                                   *)
(* - bind_ret_id_coincidence:                                        *)
(*     qbs_to_giry_mu(bind(e1, ret(var))) = qbs_to_giry_mu(e1)     *)
(*                                                                   *)
(* - bind_ret_coincidence_general:                                   *)
(*     qbs_to_giry_mu(bind(e1, ret(e0)))                            *)
(*     = kcomp_noparam(qbs_to_giry(e1), dirac o e0)                *)
(*                                                                   *)
(* - integral_dirac_indicator:                                       *)
(*     \int[mu]_y dirac(f(y))(U) = mu(f^{-1}(U))                  *)
(*                                                                   *)
(* DISCHARGED (4 of 13 hypotheses now proved):                       *)
(*                                                                   *)
(* A. expr_denot_ret_real: by []. (morph_ret is Defined, no have)   *)
(* B. expr_denot_sample_uniform: by []. (morph_sample_uniform idem) *)
(* C. expr_denot_sample_normal: by []. (morph_sample_normal idem)   *)
(* D. integral_dirac_indicator: proved via integral_indic/diracE    *)
(*                                                                   *)
(* REMAINING HYPOTHESES (9):                                         *)
(*                                                                   *)
(* A. Bind equations (expr_denot_bind_...): blocked by opaque       *)
(*    [ssr_have_upoly] in [morph_bind_ret]'s proof term.            *)
(*    Fix: rewrite [morph_bind_ret] to avoid ssreflect [have].     *)
(*                                                                   *)
(* B. measure_extraction_measurable: would follow from HKSY 2017    *)
(*    Prop 22.3 (full faithfulness of R for standard Borel spaces). *)
(*    Used only in bind_ret_coincidence_general.                    *)
(*                                                                   *)
(* The key conceptual insight: for first-order programs, the QBS    *)
(* bind/return reduces to pushforward composition, which is         *)
(* exactly kcomp_noparam in the kernel world. The bridge is         *)
(* integral_dirac_indicator, which relates integration of Dirac     *)
(* measures to preimage computation.                                *)
(* ================================================================ *)

End ppl_coincidence.
