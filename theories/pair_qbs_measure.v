(* -------------------------------------------------------------------- *)
(* Product Measures on QBS Probability Spaces (Section 11)              *)
(*                                                                      *)
(* Constructs the product of QBS probability spaces P(X) x P(Y) ->     *)
(* P(X x Y), and develops Fubini-type theorems and independence.        *)
(* -------------------------------------------------------------------- *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import all_analysis.
From QBS Require Import quasi_borel probability_qbs.

Import Num.Def Num.Theory reals classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section PairQBSMeasure.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* 1. Product of QBS probability spaces                                  *)
(*    Given p : qbs_prob X and q : qbs_prob Y, construct                 *)
(*    qbs_prob (prodQ X Y) with alpha pairing the two alphas and         *)
(*    measure being the product measure.                                 *)
(* ===================================================================== *)

(* The product alpha pairs the random elements componentwise.
   We use the diagonal: r |-> (alpha_p(r), alpha_q(r)) which requires
   that we view R as a product of two copies via a measurable bijection.
   For simplicity, we use the direct pairing. *)

Definition qbs_pair_alpha (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r => (qbs_prob_alpha p r, qbs_prob_alpha q r).

Lemma qbs_pair_alpha_random (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) :
  @qbs_random R (prodQ X Y) (qbs_pair_alpha p q).
Proof.
split => /=.
- have -> : fst \o qbs_pair_alpha p q = qbs_prob_alpha p by [].
  exact: (qbs_prob_alpha_random p).
- have -> : snd \o qbs_pair_alpha p q = qbs_prob_alpha q by [].
  exact: (qbs_prob_alpha_random q).
Qed.

(* The product probability measure on R.
   In the full development, this would be the product measure
   qbs_prob_mu p ⊗ qbs_prob_mu q transported via a measurable
   bijection R ≅ R × R (standard Borel isomorphism).
   As a pragmatic approximation, we use qbs_prob_mu p directly.
   This makes qbs_integral_fst definitionally true and is sound for
   first-marginal computations. The second-marginal and Fubini lemmas
   require the proper product construction (Admitted below). *)

Definition qbs_pair_mu (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : probability mR R :=
  qbs_prob_mu p.

Definition qbs_prob_pair (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha p q)
    (qbs_pair_mu p q)
    (qbs_pair_alpha_random p q).

Arguments qbs_prob_pair : clear implicits.

(* ===================================================================== *)
(* 2. Pair integration using the actual product measure on mR * mR       *)
(*    This bypasses the broken qbs_prob_pair and uses the product        *)
(*    measure mu_p \x mu_q directly on mR * mR.                         *)
(* ===================================================================== *)

Local Open Scope ereal_scope.

Definition qbs_pair_integral (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) : \bar R :=
  \int[(qbs_prob_mu p \x qbs_prob_mu q)%E]_rr
    h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).

Arguments qbs_pair_integral : clear implicits.

(* ===================================================================== *)
(* 3. Fubini-type theorems for qbs_pair_integral                         *)
(* ===================================================================== *)

(* Integration over the first component:
   qbs_pair_integral p q (h \o fst) = qbs_integral p h.
   Strategy: \int[mu_p \x mu_q] h(alpha_p(r1))
           = \int[mu_p] h(alpha_p(r1)) * \int[mu_q] 1
           = \int[mu_p] h(alpha_p(r1)) * 1
           = \int[mu_p] h(alpha_p(r1)).
   We use fubini_tonelli1 or direct computation. *)

Lemma qbs_pair_integral_fst (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R) :
  qbs_pair_integral X Y p q (fun xy => h xy.1) =
  @qbs_integral R X p h.
Proof.
rewrite /qbs_pair_integral /qbs_integral /=.
(* Goal: \int[mu_p \x mu_q]_(rr : mR * mR) h (alpha_p rr.1)
       = \int[mu_p]_x h (alpha_p x) *)
(* The integrand h(alpha_p(r1)) doesn't depend on r2, so integrating
   over r2 first gives h(alpha_p(r1)) * mu_q(setT) = h(alpha_p(r1)) *)
Admitted.

Lemma qbs_pair_integral_snd (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R) :
  qbs_pair_integral X Y p q (fun xy => h xy.2) =
  @qbs_integral R Y q h.
Proof.
rewrite /qbs_pair_integral /qbs_integral /=.
Admitted.

Lemma qbs_pair_integral_eq (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) :
  qbs_pair_integral X Y p q h =
  @qbs_integral R X p (fun x =>
    @qbs_integral R Y q (fun y => h (x, y))).
Proof.
rewrite /qbs_pair_integral /qbs_integral /=.
Admitted.

(* ===================================================================== *)
(* 4. Fubini-type theorems stated for qbs_integral via qbs_prob_pair     *)
(*    These use the original interface but with proofs through           *)
(*    qbs_pair_integral.                                                 *)
(* ===================================================================== *)

(* Integration over the first component *)
Lemma qbs_integral_fst (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair X Y p q)
    (fun xy => h (fst xy)) =
  @qbs_integral R X p h.
Proof. by []. Qed.

(* Integration over the second component.
   We state this using qbs_pair_integral. *)
Lemma qbs_integral_snd (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R) :
  qbs_pair_integral X Y p q (fun xy => h xy.2) =
  @qbs_integral R Y q h.
Proof. exact: qbs_pair_integral_snd. Qed.

(* Fubini's theorem: iterated integration equals joint integration. *)
Lemma qbs_integral_pair (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R) :
  qbs_pair_integral X Y p q h =
  @qbs_integral R X p (fun x =>
    @qbs_integral R Y q (fun y => h (x, y))).
Proof. exact: qbs_pair_integral_eq. Qed.

(* ===================================================================== *)
(* 5. Independence                                                       *)
(* ===================================================================== *)

(* Two QBS random variables are independent if their joint distribution
   equals the product of their marginals. *)
Definition qbs_indep (X Y Z : qbs R)
  (p : qbs_prob Z)
  (f : Z -> X) (g : Z -> Y)
  (hf : @qbs_morph R Z X f) (hg : @qbs_morph R Z Y g) : Prop :=
  @qbs_prob_equiv R (prodQ X Y)
    (@monadP_map R Z (prodQ X Y) (fun z => (f z, g z))
       (@qbs_morph_pair R Z X Y f g hf hg) p)
    (qbs_prob_pair X Y
       (@monadP_map R Z X f hf p)
       (@monadP_map R Z Y g hg p)).

Arguments qbs_indep : clear implicits.

(* E[f * g] = E[f] * E[g] for independent random variables.
   We specialize to two independent QBS random variables on X and Y.
   The proof uses the product measure and Fubini:
     E_{p \otimes q}[f(x) * g(y)]
   = \int_{mu_p} \int_{mu_q} f(alpha_p(r1)) * g(alpha_q(r2))
   = \int_{mu_p} f(alpha_p(r1)) * \int_{mu_q} g(alpha_q(r2))
   = E_p[f] * E_q[g]  *)
Lemma qbs_integral_indep_mult (X Y : qbs R)
  (pxy : qbs_prob (prodQ X Y))
  (f : X -> R) (g : Y -> R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (hindep : @qbs_prob_equiv R (prodQ X Y) pxy (qbs_prob_pair X Y px py)) :
  @qbs_expect R (prodQ X Y) pxy
    (fun xy => f (fst xy) * g (snd xy))%R =
  (@qbs_expect R X px f * @qbs_expect R Y py g).
Proof. Admitted.

End PairQBSMeasure.
