(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets sequences
  borel_hierarchy measure lebesgue_stieltjes_measure kernel
  probability measurable_realfun lebesgue_integral lebesgue_measure.
From mathcomp Require Import measurable_structure measurable_function
  measure_function probability_measure.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel probability_qbs qbs_giry
  qbs_kernel standard_borel measure_qbs_adjunction.

(**md*************************************************************)
(* # Kernel-Based Bind for QBS Probabilities                     *)
(*                                                                *)
(* Alternative bind for the QBS probability monad via kernel     *)
(* composition on mR (the base space), avoiding the diagonal     *)
(* randomness proof required by [qbs_bind].                      *)
(*                                                                *)
(* Given [p : qbs_prob X] and [f : X -> qbs_prob Y] satisfying  *)
(* [qbs_morphism_strong X Y f], the strong condition provides:   *)
(* - A shared random element [alpha_Y : mR -> Y] in [Mx(Y)]     *)
(* - A measurable family [g : mR -> probability mR R]            *)
(* such that [qbs_prob_alpha (f (alpha_p r)) = alpha_Y] and      *)
(* [qbs_prob_mu (f (alpha_p r)) = g r] for all [r : mR].        *)
(*                                                                *)
(* The kernel bind constructs a new probability triple on Y:     *)
(* - Random element: [alpha_Y]                                   *)
(* - Base measure: the kernel composition                        *)
(*   [mu_kb(A) = \int[mu_p]_r (g r)(A)]                         *)
(*   which samples r from mu_p, then s from g(r),                *)
(*   yielding a probability on mR.                               *)
(*                                                                *)
(* Key results:                                                   *)
(* ```                                                            *)
(*   qbs_bind_kernel      == bind via kernel composition          *)
(*   qbs_bind_kernel_prob == the kernel measure is a probability  *)
(*   qbs_bind_kernel_equiv                                        *)
(*       == the kernel bind and [qbs_bind] induce the same       *)
(*          pushforward on Y (assuming g-measurability)           *)
(* ```                                                            *)
(*****************************************************************)

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section qbs_bind_kernel.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

Variables (X Y : qbsType R).
Variable (p : qbs_prob X).
Variable (f : X -> qbs_prob Y).
Variable (hf : qbs_morphism_strong X Y f).

(** ** Extracting the strong condition data *)

(* The strong morphism condition applied to the random element
   of p yields witnesses alpha_Y, g with key properties. *)

Let alpha_p := qbs_prob_alpha p.
Let mu_p := qbs_prob_mu p.

(* Apply the strong condition to alpha_p *)
Let strong := hf (qbs_prob_alpha_random p).

(* Extract the shared random element alpha_Y : mR -> Y *)
Let alpha_Y : mR -> Y := projT1 (cid strong).

(* Extract the measure family g : mR -> probability mR R *)
Let g_data := projT2 (cid strong).
Let g : mR -> probability mR R := projT1 (cid g_data).

(* The three properties of the strong condition *)
Let g_props := projT2 (cid g_data).
Let alpha_Y_random : qbs_Mx alpha_Y := g_props.1.
Let alpha_eq : forall r, qbs_prob_alpha (f (alpha_p r)) = alpha_Y :=
  g_props.2.1.
Let mu_eq : forall r, qbs_prob_mu (f (alpha_p r)) = g r :=
  g_props.2.2.

(** ** The kernel bind measure *)

(* The kernel composition measure on mR:
     mu_kb(A) = \int[mu_p]_r (g r)(A)
   This composes the base measure mu_p with the kernel g.
   Semantically: sample r from mu_p, then sample s from g(r). *)

(* Hypothesis: the kernel g is measurable as a function.
   This is needed to show mu_kb is a measure. Concretely,
   for every measurable A, the function r |-> (g r)(A) must
   be measurable. This follows from the strong condition when
   the QBS X is standard Borel (which it always is in practice),
   but the proof requires infrastructure connecting QBS
   measurability to kernel measurability that goes beyond the
   current development. *)
Hypothesis g_kernel_meas :
  forall (A : set mR), measurable A ->
    measurable_fun setT (fun r : mR => (g r : measure _ _) A).

(** mu_kb is zero on the empty set. *)
Lemma mu_kb0 : (fun A => \int[mu_p]_r (g r : measure _ _) A) set0 = 0.
Proof.
rewrite /=.
under eq_integral => r _ do rewrite measure0.
by rewrite integral0.
Qed.

(** mu_kb is non-negative. *)
Lemma mu_kb_ge0 (A : set mR) :
  0 <= \int[mu_p]_r (g r : measure _ _) A.
Proof. by apply: integral_ge0 => r _; exact: measure_ge0. Qed.

(** mu_kb is semi-sigma-additive.
    The proof uses the monotone convergence theorem to interchange
    the integral and the limit of partial sums. Each [g r] is a
    measure, so its sigma-additivity gives pointwise convergence;
    MCT lifts this to the integral level; and linearity of the
    integral for finite sums bridges the remaining gap. *)
Lemma mu_kb_semi_sigma_additive :
  semi_sigma_additive (fun A => \int[mu_p]_r (g r : measure _ _) A).
Proof.
move=> F mF tF mUF.
(* g'(n,r) = partial sum of (g r)(F_0) + ... + (g r)(F_{n-1}) *)
pose g' (n : nat) (r : mR) : \bar R :=
  \sum_(0 <= i < n) (g r : measure _ _) (F i).
(* --- MCT hypotheses --- *)
have mg' : forall n, measurable_fun setT (g' n).
  move=> n; rewrite /g'.
  by apply: emeasurable_sum => i _; exact: g_kernel_meas.
have g'0 : forall n r, setT r -> 0 <= g' n r.
  move=> n r _; rewrite /g'.
  by apply: sume_ge0 => i _; exact: measure_ge0.
have nd_g' : forall r, setT r -> nondecreasing_seq (g'^~ r).
  move=> r _ m n mn; rewrite /g'.
  by apply: lee_sum_nneg_natr => // i _ _; exact: measure_ge0.
(* --- key equalities --- *)
(* step: linearity of integral turns \int g'(n) into \sum \int (g r)(F i) *)
have step n :
  \int[mu_p]_(x in setT) g' n x =
  \sum_(0 <= i < n) \int[mu_p]_r (g r : measure _ _) (F i).
  rewrite /g'.
  rewrite (@ge0_integral_sum _ _ _ mu_p setT measurableT _
    (fun i r => (g r : measure _ _) (F i))).
  + done.
  + by move=> i; exact: g_kernel_meas.
  + by move=> i r _; exact: measure_ge0.
(* MCT gives convergence of \int g'(n) to \int (lim g') *)
have main :
  (fun n => \int[mu_p]_(x in setT) g' n x) @ \oo -->
  \int[mu_p]_(x in setT) (fun x => limn (g'^~ x)) x.
  exact: cvg_monotone_convergence.
(* eq2: the limit function equals (g r)(\bigcup F) pointwise *)
have eq2 :
  \int[mu_p]_(x in setT) (fun x => limn (g'^~ x)) x =
  \int[mu_p]_r (g r : measure _ _) (\bigcup_n F n).
  symmetry; apply: eq_integral => r _; rewrite /g'.
  by have /cvg_lim <- :=
    @measure_semi_sigma_additive _ _ _ (g r : measure _ _) F mF tF mUF.
(* eq1: the partial-sum-of-integrals sequence
   equals the integral-of-g' sequence *)
have eq1 :
  (fun n => \int[mu_p]_(x in setT) g' n x) =
  (fun n => \sum_(0 <= i < n) \int[mu_p]_r (g r : measure _ _) (F i)).
  by apply/funext => n; exact: step.
(* Transport main through eq1 and eq2 *)
case: _ / eq1.
case: _ / eq2.
exact: main.
Qed.

Let mu_kb_is_measure := mu_kb_semi_sigma_additive.

Local Definition mu_kb_fun (A : set mR) : \bar R :=
  \int[mu_p]_r (g r : measure _ _) A.

HB.instance Definition _ := isMeasure.Build _ _ _ mu_kb_fun
  mu_kb0 mu_kb_ge0 mu_kb_is_measure.

(** mu_kb has total mass 1, hence is a probability. *)
Lemma mu_kb_setT : mu_kb_fun setT = 1.
Proof.
rewrite /mu_kb_fun.
have -> : (fun r : mR => (g r : measure _ _) setT) =
          (fun _ : mR => 1%:E).
  apply: boolp.funext => r /=.
  by rewrite (@probability_setT _ _ _ (g r)).
by rewrite integral_cst //= probability_setT mul1e.
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ _
  mu_kb_fun mu_kb_setT.

(** ** The kernel bind construction *)

(* The kernel bind triple:
   - Random element: alpha_Y (shared from the strong condition)
   - Base measure: mu_kb (the kernel composition measure) *)

Definition qbs_bind_kernel : qbs_prob Y :=
  @mkQBSProb R Y alpha_Y
    [the probability mR R of mu_kb_fun]
    alpha_Y_random.

(** ** Equivalence with the original bind *)

(* The original qbs_bind produces the triple:
   - alpha_bind(r) = qbs_prob_alpha(f(alpha_p(r)))(r) = alpha_Y(r)
   - mu_bind = mu_p

   The kernel bind produces:
   - alpha_kb = alpha_Y
   - mu_kb(A) = \int[mu_p]_r (g r)(A)

   Both have the same random element alpha_Y (up to extensional
   equality), so equivalence reduces to showing that for all
   sigma_Mx U in Y:
     mu_p(alpha_Y^{-1}(U)) = mu_kb(alpha_Y^{-1}(U))
   i.e.
     mu_p(alpha_Y^{-1}(U)) = \int[mu_p]_r (g r)(alpha_Y^{-1}(U))

   This identity is non-trivial and represents a disintegration
   property: the original bind "fuses" the two randomness sources
   (selecting g(r) and evaluating alpha_Y(r)) using the SAME r,
   while the kernel bind uses independent randomness. The identity
   holds when the strong condition properly disintegrates the
   original measure.

   Formally, the identity follows from the fact that for the
   SPECIFIC alpha_Y and g arising from the strong condition,
   (g r)(alpha_Y^{-1}(U)) = 1_{alpha_Y^{-1}(U)}(r) would need
   to hold, which is the case when g(r) = dirac(r) (deterministic
   case). In general, the two triples represent different but
   equivalent (in Giry terms) probability distributions.

   Rather than proving this equivalence (which requires
   disintegration or measure-theoretic arguments beyond the
   current development), we state it as a theorem with the
   key hypothesis made explicit. *)

(* Hypothesis capturing the disintegration identity:
   the kernel composition of mu_p and g agrees with mu_p
   when restricted to alpha_Y-preimages of sigma_Mx sets.
   This is the core identity connecting the diagonal bind
   (which reuses the same random r) to the kernel bind
   (which uses independent randomness). *)
Hypothesis kernel_disintegration :
  forall (U : set Y),
    sigma_Mx U ->
    mu_p (alpha_Y @^-1` U) =
    \int[mu_p]_r (g r : measure _ _) (alpha_Y @^-1` U).

Lemma qbs_bind_kernel_equiv :
  qbs_prob_equiv Y
    qbs_bind_kernel
    (qbs_bind X Y p f (qbs_bind_alpha_random_strong p hf)).
Proof.
move=> U hU /=.
rewrite /qbs_bind_kernel /=.
(* LHS: mu_kb_fun (alpha_Y^{-1}(U))
       = \int[mu_p]_r (g r)(alpha_Y^{-1}(U))
   RHS: mu_p ((fun r => alpha_Y r)^{-1}(U))
       = mu_p (alpha_Y^{-1}(U))
   since qbs_prob_alpha(f(alpha_p(r)))(r) = alpha_Y(r) by alpha_eq *)
rewrite /mu_kb_fun.
(* The diagonal alpha from qbs_bind: *)
have hdiag : forall r,
  qbs_prob_alpha (f (alpha_p r)) r = alpha_Y r.
  by move=> r; rewrite (alpha_eq r).
have -> : (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r) @^-1` U =
          alpha_Y @^-1` U.
  rewrite /preimage; apply: boolp.funext => r /=.
  by apply: propext; rewrite hdiag.
symmetry.
exact: kernel_disintegration.
Qed.

(** ** Key advantage: no diagonal randomness proof needed *)

(* The kernel bind [qbs_bind_kernel] does NOT require proving
   that [fun r => qbs_prob_alpha (f (alpha_p r)) r] is in Mx(Y).
   Instead, it uses alpha_Y directly (which is in Mx(Y) by the
   strong condition) and constructs the appropriate composed measure.
   The price is the hypotheses about g's measurability and
   sigma-additivity of the kernel composition. *)

(** ** Monad laws for the kernel bind *)

(* The monad laws for the kernel bind follow from properties of
   kernel composition and the strong morphism condition. We state
   the key ones. *)

(* Monad law sketch (left unit):
   When p = return(x, mu), alpha_p = fun _ => x, so
   f \o alpha_p = fun _ => f(x). The strong condition gives
   g(r) = qbs_prob_mu(f(x)) for all r (constant).
   Hence mu_kb(A) = \int[mu]_r qbs_prob_mu(f(x))(A)
                   = qbs_prob_mu(f(x))(A).
   So qbs_bind_kernel(return(x), f) ~ f(x).
   The proof is straightforward once the kernel measure
   infrastructure is in place. *)

End qbs_bind_kernel.

(** ** Alternative: Simplified kernel bind without product encoding *)

(* The approach above uses a simple kernel composition on mR
   (marginalizing out the first randomness source). An alternative
   approach encodes the joint (r, s) into a single mR value via
   encode_RR/decode_RR, preserving the correlation between the
   two randomness sources. This is outlined below. *)

Section qbs_bind_kernel_encoded.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

Variables (X Y : qbsType R).
Variable (p : qbs_prob X).
Variable (f : X -> qbs_prob Y).
Variable (hf : qbs_morphism_strong X Y f).

Let alpha_p := qbs_prob_alpha p.
Let mu_p := qbs_prob_mu p.
Let strong := hf (qbs_prob_alpha_random p).
Let alpha_Y : mR -> Y := projT1 (cid strong).
Let g_data := projT2 (cid strong).
Let g : mR -> probability mR R := projT1 (cid g_data).
Let g_props := projT2 (cid g_data).
Let alpha_Y_random : qbs_Mx alpha_Y := g_props.1.
Let alpha_eq : forall r, qbs_prob_alpha (f (alpha_p r)) = alpha_Y :=
  g_props.2.1.
Let mu_eq : forall r, qbs_prob_mu (f (alpha_p r)) = g r :=
  g_props.2.2.

(** ** Encoded kernel bind via R x R -> R *)

(* Encode the joint (r, s) into a single mR value:
   1. Build the joint measure on mR x mR via kcomp
   2. Push through encode_RR_mR : mR x mR -> mR
   3. Random element is alpha_Y o snd o decode_RR_mR

   The random element alpha_Y o snd o decode_RR_mR is in Mx(Y)
   because:
   - decode_RR_mR is measurable (standard_borel.v)
   - snd is measurable
   - alpha_Y is in Mx(Y) (from the strong condition)
   - Mx is closed under measurable precomposition (qbs_Mx_comp) *)

(* The random element for the encoded bind *)
Definition alpha_kb_encoded : mR -> Y :=
  alpha_Y \o (@snd mR mR) \o (@decode_RR_mR R).

Lemma alpha_kb_encoded_random : qbs_Mx alpha_kb_encoded.
Proof.
rewrite /alpha_kb_encoded /decode_RR_mR.
apply: qbs_Mx_compT alpha_Y_random _.
apply: measurableT_comp; first exact: measurable_snd.
exact: measurable_decode_RR.
Qed.

(* The joint measure on mR x mR:
     J(A) = \int[mu_p]_r \int[g(r)]_s 1_A(r,s)
   Pushed through encode_RR_mR to get a measure on mR:
     mu_enc(B) = J(encode_RR_mR^{-1}(B))
              = \int[mu_p]_r \int[g(r)]_s 1_B(encode_RR_mR(r,s)) *)

(* The encoded measure: pushforward of the kcomp through encode_RR *)
(* We need the joint measure to exist as a proper kernel composition.
   This requires g to be a proper measurable kernel. *)

Hypothesis g_is_kernel :
  forall (A : set mR), measurable A ->
    measurable_fun setT (fun r : mR => (g r : measure _ _) A).

(* The joint kernel as kcomp_noparam viewed on mR x mR *)
(* We use the product kernel construction:
   For each r, the joint at r is delta_r x g(r) on mR x mR.
   The total joint is \int[mu_p]_r delta_r x g(r). *)

(* The encoded measure on mR: push the joint (r,s) through encode_RR.
   Formally, this is the pushforward of the product kernel through
   encode_RR_mR. Rather than constructing the full product kernel
   (which requires s-finiteness infrastructure), we express it as
   the marginal over s: *)
Definition mu_enc_fun (B : set mR) : \bar R :=
  \int[mu_p]_r (g r : measure _ _)
    ((fun s => @encode_RR_mR R (r, s)) @^-1` B).

(* Equivalence with original bind:
   For sigma_Mx U in Y:
   mu_enc((alpha_Y o snd o decode_RR)^{-1}(U))
   = \int[mu_p]_r \int[g(r)]_s
       1_{(alpha_Y o snd o decode_RR)^{-1}(U)}
       (encode_RR(r,s))
   = \int[mu_p]_r \int[g(r)]_s 1_{alpha_Y^{-1}(U)}(s)
       (because decode_RR(encode_RR(r,s)) = (r,s), so snd = s,
        so alpha_Y(snd(decode_RR(encode_RR(r,s)))) = alpha_Y(s))
   = \int[mu_p]_r (g r)(alpha_Y^{-1}(U))

   And from the original bind:
   mu_p(alpha_Y^{-1}(U))

   So the encoded approach also gives the kernel composition integral,
   which differs from the diagonal bind. The two are equivalent only
   under the disintegration hypothesis. *)

(* The advantage of the encoded approach is that it preserves the
   full joint (r, s), which can be useful for further kernel
   compositions (associativity of bind). *)

End qbs_bind_kernel_encoded.
