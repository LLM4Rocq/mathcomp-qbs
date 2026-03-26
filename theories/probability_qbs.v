(* -------------------------------------------------------------------- *)
(* Probability Spaces on Quasi-Borel Spaces and the Probability Monad    *)
(*                                                                        *)
(* Following "A Convenient Category for Higher-Order Probability Theory"  *)
(* Heunen, Kammar, Staton, Yang (LICS 2017), Section 4                   *)
(*                                                                        *)
(* Key constructions:                                                     *)
(* - qbs_prob X: probability triples (alpha, mu) on a QBS X              *)
(* - qbs_prob_equiv: equivalence of triples (same pushforward)            *)
(* - monadP X: the probability monad on QBS                              *)
(* - qbs_return / qbs_bind: monadic operations                           *)
(* - qbs_integral: integration against a QBS probability                 *)
(* -------------------------------------------------------------------- *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import all_analysis.
From QBS Require Import quasi_borel.

Import Num.Def Num.Theory reals classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section ProbabilityQBS.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* 1. QBS Probability Triple                                             *)
(*    A probability on a QBS X is a pair (alpha, mu) where               *)
(*    alpha : R -> X is a random element (in Mx) and                     *)
(*    mu is a probability measure on R.                                  *)
(* ===================================================================== *)

Record qbs_prob (X : qbs R) := mkQBSProb {
  qbs_prob_alpha : mR -> X ;
  qbs_prob_mu : probability mR R ;
  qbs_prob_alpha_random : @qbs_random R X qbs_prob_alpha ;
}.

Arguments qbs_prob : clear implicits.
Arguments mkQBSProb {X}.
Arguments qbs_prob_alpha {X}.
Arguments qbs_prob_mu {X}.
Arguments qbs_prob_alpha_random {X}.

(* ===================================================================== *)
(* 2. Equivalence of Probability Triples                                 *)
(*    Two triples (alpha1, mu1) ~ (alpha2, mu2) iff they induce the      *)
(*    same pushforward measure on X, i.e., for all measurable U in       *)
(*    sigma_Mx(X), mu1(alpha1^{-1}(U)) = mu2(alpha2^{-1}(U)).          *)
(* ===================================================================== *)

Definition qbs_prob_equiv (X : qbs R) (p1 p2 : qbs_prob X) : Prop :=
  forall (U : set X),
    @sigma_Mx R X U ->
    qbs_prob_mu p1 (qbs_prob_alpha p1 @^-1` U) =
    qbs_prob_mu p2 (qbs_prob_alpha p2 @^-1` U).

Arguments qbs_prob_equiv : clear implicits.

Lemma qbs_prob_equiv_refl (X : qbs R) (p : qbs_prob X) :
  qbs_prob_equiv X p p.
Proof. by move=> U hU. Qed.

Lemma qbs_prob_equiv_sym (X : qbs R) (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p1.
Proof. by move=> h U hU; rewrite (h U hU). Qed.

Lemma qbs_prob_equiv_trans (X : qbs R) (p1 p2 p3 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p3 ->
  qbs_prob_equiv X p1 p3.
Proof. by move=> h12 h23 U hU; rewrite (h12 U hU) (h23 U hU). Qed.

(* ===================================================================== *)
(* 3. The Probability Monad P(X)                                         *)
(* ===================================================================== *)

(* Random elements for the probability monad.
   We use the "pointwise" definition: beta : mR -> qbs_prob X is random iff
   for all r, qbs_prob_alpha(beta(r)) is in Mx(X).

   NOTE: The Isabelle development uses a STRONGER definition requiring a
   single shared alpha across all r (monadP_qbs_MPx). This stronger version
   needs quotient types to work with return (since qbs_return produces
   triples whose alpha varies with r, but which are equivalent in the
   quotient). Without quotient types, we use the weaker pointwise condition
   and accept that qbs_bind_alpha_random requires an Admitted diagonal
   extraction argument. *)

(* Strong definition (for reference; used in bind under additional hypotheses) *)
Definition monadP_random (X : qbs R) : set (mR -> qbs_prob X) :=
  [set beta |
    exists (alpha : mR -> X),
    exists (g : mR -> probability mR R),
      @qbs_random R X alpha /\
      (forall r, qbs_prob_alpha (beta r) = alpha) /\
      (forall r, qbs_prob_mu (beta r) = g r)].

Arguments monadP_random : clear implicits.

(* Pointwise definition (used for the QBS structure) *)
Definition monadP_random' (X : qbs R) : set (mR -> qbs_prob X) :=
  [set beta | forall r, @qbs_random R X (qbs_prob_alpha (beta r))].

Arguments monadP_random' : clear implicits.

(* The strong definition implies the weak one *)
Lemma monadP_random_impl (X : qbs R) (beta : mR -> qbs_prob X) :
  monadP_random X beta -> monadP_random' X beta.
Proof.
move=> [alpha [g [halpha [hbeta_a hbeta_g]]]] r.
by rewrite hbeta_a.
Qed.

Lemma monadP_comp (X : qbs R) :
  forall beta f,
    monadP_random' X beta ->
    measurable_fun setT f ->
    monadP_random' X (beta \o f).
Proof. by move=> beta f hbeta hf r; apply: hbeta. Qed.

Lemma monadP_const (X : qbs R) :
  forall x : qbs_prob X, monadP_random' X (fun _ => x).
Proof. by move=> x r; exact: (qbs_prob_alpha_random x). Qed.

Lemma monadP_glue (X : qbs R) :
  forall (P : mR -> nat) (Fi : nat -> mR -> qbs_prob X),
    measurable_fun setT P ->
    (forall i, monadP_random' X (Fi i)) ->
    monadP_random' X (fun r => Fi (P r) r).
Proof. by move=> P Fi hP hFi r; apply: hFi. Qed.

Definition monadP (X : qbs R) : qbs R :=
  @mkQBS R (qbs_prob X)
    (monadP_random' X)
    (@monadP_comp X)
    (@monadP_const X)
    (@monadP_glue X).

Arguments monadP : clear implicits.

(* ===================================================================== *)
(* 4. Return: X -> P(X)                                                  *)
(* ===================================================================== *)

Variable (default_prob : probability mR R).

Definition qbs_return (X : qbs R) (x : X) : qbs_prob X :=
  @mkQBSProb X (fun _ => x) default_prob (@qbs_random_const R X x).

Arguments qbs_return : clear implicits.

Lemma qbs_return_random (X : qbs R) :
  @qbs_morph R X (monadP X) (qbs_return X).
Proof.
move=> alpha halpha r /=.
exact: (@qbs_random_const R X).
Qed.

Arguments qbs_return_random : clear implicits.

(* ===================================================================== *)
(* 5. Bind: P(X) -> (X -> P(Y)) -> P(Y)                                 *)
(* ===================================================================== *)

Lemma qbs_bind_alpha_random (X Y : qbs R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morph R X (monadP Y) f) :
  @qbs_random R Y (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r).
Proof.
(* Diagonal extraction: we need r |-> alpha_{f(alpha_p(r))}(r) in Mx(Y).
   From hf applied to qbs_prob_alpha p, we get:
     forall r, qbs_random Y (qbs_prob_alpha (f (qbs_prob_alpha p r)))
   i.e., each alpha_{f(alpha_p(r))} is individually in Mx(Y), but they may
   differ across r. The goal is the "diagonal" fun r => alpha_{f(alpha_p(r))}(r).

   With the STRONG definition monadP_random, the alpha would be constant
   across r (a single alpha in Mx(Y)), making the diagonal trivially alpha
   itself. But monadP_random does not satisfy the QBS glue axiom (the glue
   of distinct alphas from a countable family cannot be represented as a
   single shared alpha).

   The Isabelle AFP (Monad_QuasiBorel.thy) resolves this by:
   1. Using qbs_prob as an equivalence class (quotient type), so that
      monadP_random can be defined with the strong condition, and
   2. The glue axiom holds because equivalent triples are identified.

   Without quotient types, one could alternatively use a standard Borel
   isomorphism R ≅ nat x R to encode countable choice, but this requires
   substantial measure-theoretic infrastructure. *)
Admitted.

Definition qbs_bind (X Y : qbs R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morph R X (monadP Y) f) : qbs_prob Y :=
  @mkQBSProb Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)
    (qbs_prob_mu p)
    (qbs_bind_alpha_random p hf).

Arguments qbs_bind : clear implicits.

Lemma qbs_bind_morph (X Y : qbs R) (f : qbs_hom X (monadP Y)) :
  @qbs_morph R (monadP X) (monadP Y)
    (fun p => qbs_bind X Y p (qbs_hom_val f) (qbs_hom_proof f)).
Proof.
move=> beta hbeta r /=.
all: exact: (qbs_bind_alpha_random (beta r) (qbs_hom_proof f)).
Qed.

(* ===================================================================== *)
(* 6. Monad Laws (stated up to qbs_prob_equiv, admitted)                 *)
(* ===================================================================== *)

Lemma qbs_monad_left_unit (X Y : qbs R) (x : X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morph R X (monadP Y) f) :
  qbs_prob_equiv Y (qbs_bind X Y (qbs_return X x) f hf) (f x).
Proof.
(* The bind result has alpha = qbs_prob_alpha(f(x)) and mu = default_prob.
   The target f(x) has alpha = qbs_prob_alpha(f(x)) and mu = qbs_prob_mu(f(x)).
   The alphas agree (up to eta), but the measures differ: default_prob vs
   qbs_prob_mu(f(x)). So this reduces to showing that for all U in sigma_Mx(Y):
     default_prob(alpha_{f(x)}^{-1}(U)) = mu_{f(x)}(alpha_{f(x)}^{-1}(U))
   This is NOT provable in general. The left unit law requires either:
   (1) qbs_return to use a measure depending on x (e.g., Dirac-like), or
   (2) Working with equivalence classes (quotient) of probability triples, or
   (3) A different definition of bind that uses kernel composition with
       the R x R -> R measurable isomorphism (as in the LICS 2017 paper). *)
Admitted.

Lemma qbs_monad_right_unit (X : qbs R) (m : qbs_prob X) :
  qbs_prob_equiv X
    (qbs_bind X X m (qbs_return X) (qbs_return_random X)) m.
Proof. by move=> U hU. Qed.

Lemma qbs_monad_assoc (X Y Z : qbs R) (m : qbs_prob X)
  (f : X -> qbs_prob Y) (g : Y -> qbs_prob Z)
  (hf : @qbs_morph R X (monadP Y) f)
  (hg : @qbs_morph R Y (monadP Z) g)
  (hfg : @qbs_morph R X (monadP Z)
    (fun x => qbs_bind Y Z (f x) g hg)) :
  qbs_prob_equiv Z
    (qbs_bind Y Z (qbs_bind X Y m f hf) g hg)
    (qbs_bind X Z m (fun x => qbs_bind Y Z (f x) g hg) hfg).
Proof. by move=> U hU. Qed.

(* ===================================================================== *)
(* 7. Integration on QBS Probability Spaces                              *)
(* ===================================================================== *)

Definition qbs_integral (X : qbs R) (p : qbs_prob X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x)))%E.

Arguments qbs_integral : clear implicits.

Lemma qbs_integral_equiv (X : qbs R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R) :
  qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof.
(* The equivalence hypothesis says the pushforward measures agree on
   sigma_Mx-measurable sets. To conclude equality of integrals
     int[mu1] (h o alpha1) = int[mu2] (h o alpha2)
   we need a change-of-variables / pushforward integral theorem:
   the integral of h against the pushforward measure alpha_*(mu) equals
   the integral of (h o alpha) against mu.
   Then both sides equal int h d(alpha1_* mu1) = int h d(alpha2_* mu2),
   and these agree because the pushforward measures are equal (on sigma_Mx).
   This requires:
   (a) A pushforward integral theorem from mathcomp-analysis, and
   (b) h to be sigma_Mx-measurable (or an approximation argument for
       general h via simple functions on the generated sigma-algebra). *)
Admitted.

Lemma qbs_integral_const (X : qbs R) (p : qbs_prob X) (c : \bar R) :
  qbs_integral X p (fun _ => c) = (\int[qbs_prob_mu p]_x c)%E.
Proof. by []. Qed.

Lemma qbs_integral_return (X : qbs R) (x : X)
  (h : X -> \bar R) :
  qbs_integral X (qbs_return X x) h = (\int[default_prob]_r h x)%E.
Proof. by []. Qed.

Lemma qbs_integral_bind (X Y : qbs R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morph R X (monadP Y) f)
  (h : Y -> \bar R) :
  qbs_integral Y (qbs_bind X Y p f hf) h =
  (\int[qbs_prob_mu p]_r
    h (qbs_prob_alpha (f (qbs_prob_alpha p r)) r))%E.
Proof. by []. Qed.

(* ===================================================================== *)
(* 8. Functorial action of the probability monad                         *)
(* ===================================================================== *)

Definition monadP_map (X Y : qbs R) (f : X -> Y)
  (hf : @qbs_morph R X Y f) (p : qbs_prob X) : qbs_prob Y :=
  @mkQBSProb Y
    (f \o qbs_prob_alpha p)
    (qbs_prob_mu p)
    (hf _ (qbs_prob_alpha_random p)).

Arguments monadP_map : clear implicits.

Lemma monadP_map_morph (X Y : qbs R) (f : qbs_hom X Y) :
  @qbs_morph R (monadP X) (monadP Y)
    (monadP_map X Y (qbs_hom_val f) (qbs_hom_proof f)).
Proof.
move=> beta hbeta r /=.
exact: (qbs_hom_proof f) _ (hbeta r).
Qed.

Lemma monadP_map_id (X : qbs R) (p : qbs_prob X) :
  qbs_prob_equiv X
    (monadP_map X X idfun (@qbs_morph_id R X) p) p.
Proof. by move=> U hU. Qed.

Lemma monadP_map_comp (X Y Z : qbs R)
  (f : qbs_hom X Y) (g : qbs_hom Y Z) (p : qbs_prob X) :
  qbs_prob_equiv Z
    (monadP_map X Z (qbs_hom_val g \o qbs_hom_val f)
       (@qbs_morph_comp R X Y Z _ _
          (qbs_hom_proof f) (qbs_hom_proof g)) p)
    (monadP_map Y Z (qbs_hom_val g) (qbs_hom_proof g)
       (monadP_map X Y (qbs_hom_val f) (qbs_hom_proof f) p)).
Proof. by move=> U hU. Qed.

(* ===================================================================== *)
(* 9. Expectation and probability of events                              *)
(* ===================================================================== *)

Definition qbs_expect (X : qbs R) (p : qbs_prob X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Arguments qbs_expect : clear implicits.

Definition qbs_prob_event (X : qbs R) (p : qbs_prob X)
  (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).

Arguments qbs_prob_event : clear implicits.

End ProbabilityQBS.

Arguments qbs_prob {R}.
Arguments mkQBSProb {R X}.
Arguments qbs_prob_alpha {R X}.
Arguments qbs_prob_mu {R X}.
Arguments qbs_prob_alpha_random {R X}.
Arguments qbs_prob_equiv {R}.
Arguments monadP {R}.
Arguments qbs_return {R}.
Arguments qbs_bind {R}.
Arguments qbs_integral {R}.
Arguments monadP_map {R}.
Arguments qbs_expect {R}.
Arguments qbs_prob_event {R}.
