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
(* NOT PROVABLE with the current definitions. Here is the detailed analysis.

   Unfolding, the bind result is:
     alpha_bind = fun r => qbs_prob_alpha (f ((fun _ => x) r)) r
                = fun r => qbs_prob_alpha (f x) r
                = qbs_prob_alpha (f x)
     mu_bind    = qbs_prob_mu (qbs_return X x) = default_prob

   And f(x) is:
     alpha_fx   = qbs_prob_alpha (f x)
     mu_fx      = qbs_prob_mu (f x)

   The alphas agree: alpha_bind = alpha_fx (both are qbs_prob_alpha (f x)).
   But the measures differ: mu_bind = default_prob vs mu_fx = qbs_prob_mu (f x).

   The equivalence qbs_prob_equiv Y asks: for all U in sigma_Mx(Y),
     default_prob (alpha_{f(x)}^{-1}(U)) = mu_{f(x)} (alpha_{f(x)}^{-1}(U))

   This requires two DIFFERENT probability measures (default_prob and
   mu_{f(x)}) to agree on all sets of the form alpha^{-1}(U). There is
   no reason for this to hold: default_prob is an arbitrary fixed probability
   measure on R, while mu_{f(x)} depends on x and f.

   COUNTEREXAMPLE: Take X = Y = R_qbs, f = id (viewing elements of R_qbs
   as trivial probability triples). Then alpha_{f(x)} = id and the condition
   becomes default_prob(U) = mu_{f(x)}(U) for all measurable U, i.e.,
   default_prob = mu_{f(x)} as measures. This fails whenever
   mu_{f(x)} /= default_prob.

   ROOT CAUSE: qbs_return fixes the measure to default_prob, while bind
   preserves the measure from the input triple. So bind(return(x), f) gets
   default_prob as its base measure instead of mu_{f(x)}.

   RESOLUTION APPROACHES (any one suffices):
   (1) Quotient types: Define P(X) as equivalence classes of (alpha, mu)
       under qbs_prob_equiv, so that the monad operates on classes. Then
       return(x) = [(fun _ => x, mu)] for ANY mu (all choices are
       equivalent since the pushforward of any mu through (fun _ => x)
       is the Dirac measure at x). The Isabelle AFP takes this approach.
   (2) Kernel composition: Define bind using the s-finite kernel
       composition on R, via a measurable isomorphism R -> R x R
       (a standard Borel space fact). This gives bind a different
       structure where the left unit law holds by properties of kernel
       composition. See LICS 2017 Section 4, Definition 19.
   (3) Dependent measure in return: Make qbs_return carry a measure
       parameter, so return(x, mu) = (fun _ => x, mu). Then
       bind(return(x, mu_{f(x)}), f) has mu = mu_{f(x)}, matching f(x).
       But this changes the type signature and complicates the API. *)
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

(* Sigma_Mx-measurability for functions h : X -> \bar R.                 *)
(* h is sigma_Mx-measurable iff for every random element alpha in Mx(X), *)
(* the composition h o alpha : R -> \bar R is Borel measurable.          *)
Definition qbs_measurable (X : qbs R) (h : X -> \bar R) : Prop :=
  forall alpha, @qbs_random R X alpha ->
    measurable_fun setT (h \o alpha).

Arguments qbs_measurable : clear implicits.

(* If h is sigma_Mx-measurable, then preimages of measurable sets are    *)
(* in sigma_Mx.                                                          *)
Lemma qbs_measurable_sigma_Mx (X : qbs R) (h : X -> \bar R)
  (hm : qbs_measurable X h) (V : set (\bar R)) :
  measurable V -> @sigma_Mx R X (h @^-1` V).
Proof.
move=> hV alpha halpha.
have hma := hm alpha halpha.
have := hma measurableT V hV.
rewrite setTI.
have -> : (h \o alpha) @^-1` V = alpha @^-1` (h @^-1` V) by [].
done.
Qed.

(* When h is sigma_Mx-measurable, the pushforward measures through       *)
(* (h o alpha_i) agree on all measurable sets of \bar R.                 *)
Lemma qbs_pushforward_agree (X : qbs R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hequiv : qbs_prob_equiv X p1 p2) :
  forall (V : set (\bar R)), measurable V ->
    pushforward (qbs_prob_mu p1) (h \o qbs_prob_alpha p1) V =
    pushforward (qbs_prob_mu p2) (h \o qbs_prob_alpha p2) V.
Proof.
move=> V hV.
rewrite /pushforward /=.
have -> : (h \o qbs_prob_alpha p1) @^-1` V =
          qbs_prob_alpha p1 @^-1` (h @^-1` V) by [].
have -> : (h \o qbs_prob_alpha p2) @^-1` V =
          qbs_prob_alpha p2 @^-1` (h @^-1` V) by [].
apply: hequiv.
apply: (qbs_measurable_sigma_Mx hm).
exact: hV.
Qed.

(* Integration respects equivalence for sigma_Mx-measurable integrands.  *)
(* The proof factors through pushforward measures on \bar R:             *)
(*   int[mu_i] (h o alpha_i) = int[pushforward mu_i (h o alpha_i)] id   *)
(* by the pushforward integral theorem (integral_pushforward). Since     *)
(* the pushforward measures agree (qbs_pushforward_agree), the integrals *)
(* against them agree by eq_measure_integral.                            *)
Lemma qbs_integral_equiv (X : qbs R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint1 : (qbs_prob_mu p1).-integrable setT (h \o qbs_prob_alpha p1))
  (hint2 : (qbs_prob_mu p2).-integrable setT (h \o qbs_prob_alpha p2)) :
  qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof.
move=> hequiv.
rewrite /qbs_integral.
have hm1 := hm _ (qbs_prob_alpha_random p1).
have hm2 := hm _ (qbs_prob_alpha_random p2).
rewrite -(@integral_pushforward _ _ mR (\bar R : measurableType _) R
  (h \o qbs_prob_alpha p1) hm1
  (qbs_prob_mu p1) setT id
  (@measurable_id _ (\bar R) setT) hint1 measurableT).
rewrite -(@integral_pushforward _ _ mR (\bar R : measurableType _) R
  (h \o qbs_prob_alpha p2) hm2
  (qbs_prob_mu p2) setT id
  (@measurable_id _ (\bar R) setT) hint2 measurableT).
apply: (@eq_measure_integral _ _ _ setT
  (pushforward (qbs_prob_mu p2) (h \o qbs_prob_alpha p2))).
move=> A hA _.
apply: (qbs_pushforward_agree hm hequiv).
exact: hA.
Qed.

(* Simpler version: when both triples share the same random element and  *)
(* the base measures agree on all measurable sets.                       *)
Lemma qbs_integral_equiv_same_alpha (X : qbs R) (p1 p2 : qbs_prob X)
  (h : X -> \bar R) :
  qbs_prob_alpha p1 = qbs_prob_alpha p2 ->
  (forall A : set R, measurable A ->
    qbs_prob_mu p1 A = qbs_prob_mu p2 A) ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof.
move=> halpha hmu.
rewrite /qbs_integral halpha.
apply: (@eq_measure_integral _ _ _ setT (qbs_prob_mu p2)).
by move=> A hA _; apply: hmu.
Qed.

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
Arguments qbs_measurable {R}.
Arguments monadP_map {R}.
Arguments qbs_expect {R}.
Arguments qbs_prob_event {R}.
