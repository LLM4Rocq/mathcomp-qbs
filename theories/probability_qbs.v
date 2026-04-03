(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals ereal topology
  classical_sets borel_hierarchy numfun measure lebesgue_measure
  lebesgue_integral probability lebesgue_stieltjes_measure.
From QBS Require Import quasi_borel.

(**md**************************************************************************)
(* # Probability Spaces on Quasi-Borel Spaces and the Probability Monad      *)
(*                                                                            *)
(* Following "A Convenient Category for Higher-Order Probability Theory"      *)
(* Heunen, Kammar, Staton, Yang (LICS 2017), Section 4                       *)
(*                                                                            *)
(* Key constructions:                                                         *)
(* ```                                                                        *)
(*   qbs_prob X    == probability triples (alpha, mu) on a qbsType X         *)
(*   qbs_prob_equiv == equivalence of triples (same pushforward)              *)
(*   monadP X      == the probability monad on QBS                            *)
(*   qbs_return / qbs_bind == monadic operations                              *)
(*   qbs_integral  == integration against a QBS probability                   *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section probability_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(* 1. QBS Probability Triple
   A probability on a QBS X is a pair (alpha, mu) where
   alpha : R -> X is a random element (in Mx) and
   mu is a probability measure on R. *)

Record qbs_prob (X : qbsType R) := mkQBSProb {
  qbs_prob_alpha : mR -> X ;
  qbs_prob_mu : probability mR R ;
  qbs_prob_alpha_random : @qbs_Mx R X qbs_prob_alpha }.

Arguments qbs_prob : clear implicits.
Arguments mkQBSProb {X}.
Arguments qbs_prob_alpha {X}.
Arguments qbs_prob_mu {X}.
Arguments qbs_prob_alpha_random {X}.

(* 2. Equivalence of Probability Triples
   Two triples (alpha1, mu1) ~ (alpha2, mu2) iff they induce
   the same pushforward measure on X, i.e., for all measurable
   U in sigma_Mx(X),
   mu1(alpha1^{-1}(U)) = mu2(alpha2^{-1}(U)). *)

Definition qbs_prob_equiv (X : qbsType R) (p1 p2 : qbs_prob X) : Prop :=
  forall (U : set X),
    @sigma_Mx R X U ->
    qbs_prob_mu p1 (qbs_prob_alpha p1 @^-1` U) =
    qbs_prob_mu p2 (qbs_prob_alpha p2 @^-1` U).

Arguments qbs_prob_equiv : clear implicits.

Lemma qbs_prob_equivxx (X : qbsType R) (p : qbs_prob X) :
  qbs_prob_equiv X p p.
Proof. by move=> U hU. Qed.

Lemma qbs_prob_equivC (X : qbsType R) (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p1.
Proof. by move=> h U hU; rewrite (h U hU). Qed.

Lemma qbs_prob_equiv_trans (X : qbsType R) (p1 p2 p3 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv X p2 p3 ->
  qbs_prob_equiv X p1 p3.
Proof. by move=> h12 h23 U hU; rewrite (h12 U hU) (h23 U hU). Qed.

(* 3. The Probability Monad P(X)

   Random elements for the probability monad.
   We use the "pointwise" definition: beta : mR -> qbs_prob X
   is random iff for all r, qbs_prob_alpha(beta(r)) is in Mx(X).

   NB: The Isabelle development uses a STRONGER definition
   requiring a single shared alpha across all r. This stronger
   version needs quotient types to work with return. Without
   quotient types, we use the weaker pointwise condition. The
   current development avoids quotient types by factoring
   qbs_bind to take an explicit diagonal randomness proof,
   with helper lemmas for the strong morphism and
   constant-alpha cases. See Section 5. *)

(* Strong definition (for reference; used in bind
   under additional hypotheses) *)
Definition monadP_random (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta |
    exists (alpha : mR -> X),
    exists (g : mR -> probability mR R),
      @qbs_Mx R X alpha /\
      (forall r, qbs_prob_alpha (beta r) = alpha) /\
      (forall r, qbs_prob_mu (beta r) = g r)].

Arguments monadP_random : clear implicits.

(* Pointwise definition (used for the QBS structure) *)
Definition monadP_random_pw (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta | forall r, @qbs_Mx R X (qbs_prob_alpha (beta r))].

Arguments monadP_random_pw : clear implicits.

(* The strong definition implies the weak one *)
Lemma monadP_random_impl (X : qbsType R) (beta : mR -> qbs_prob X) :
  monadP_random X beta -> monadP_random_pw X beta.
Proof.
move=> [alpha [g [halpha [hbeta_a hbeta_g]]]] r.
by rewrite hbeta_a.
Qed.

Lemma monadP_comp (X : qbsType R) :
  forall beta f,
    monadP_random_pw X beta ->
    measurable_fun setT f ->
    monadP_random_pw X (beta \o f).
Proof. by move=> beta f hbeta hf r; apply: hbeta. Qed.

Lemma monadP_const (X : qbsType R) :
  forall x : qbs_prob X, monadP_random_pw X (fun _ => x).
Proof. by move=> x r; exact: (qbs_prob_alpha_random x). Qed.

Lemma monadP_glue (X : qbsType R) :
  forall (P : mR -> nat) (Fi : nat -> mR -> qbs_prob X),
    measurable_fun setT P ->
    (forall i, monadP_random_pw X (Fi i)) ->
    monadP_random_pw X (fun r => Fi (P r) r).
Proof. by move=> P Fi hP hFi r; apply: hFi. Qed.

(* NB: manual HB.pack because monadP creates a
   non-canonical QBS on qbs_prob X *)
Definition monadP (X : qbsType R) : qbsType R :=
  HB.pack (qbs_prob X)
    (@isQBS.Build R (qbs_prob X)
      (monadP_random_pw X)
      (@monadP_comp X)
      (@monadP_const X)
      (@monadP_glue X)).

Arguments monadP : clear implicits.

(* 4. Return: X -> P(X)
   The return operation takes a measure parameter mu, so that
   qbs_return X x mu = (fun _ => x, mu). This is crucial for
   the left unit law: all triples (fun _ => x, mu) are
   equivalent for any mu, since pushforward mu (fun _ => x) =
   Dirac(x) regardless of mu. The monad law uses
   qbs_return X x (qbs_prob_mu (f x)) so that
   bind(return(x), f) has the same mu as f(x). *)

Definition qbs_return (X : qbsType R) (x : X) (mu : probability mR R) :
  qbs_prob X :=
  @mkQBSProb X (fun _ => x) mu (@qbs_Mx_const R X x).

Arguments qbs_return : clear implicits.

(* All returns with the same point are equivalent, regardless of mu *)
Lemma qbs_return_equiv (X : qbsType R) (x : X)
  (mu1 mu2 : probability mR R) :
  qbs_prob_equiv X (qbs_return X x mu1) (qbs_return X x mu2).
Proof.
move=> U hU /=.
have [hx|hx] := boolp.pselect (U x).
  have heq : (fun=> x) @^-1` U = @setT mR.
    rewrite /preimage; apply: boolp.funext => r /=.
    by apply: boolp.propext; split => // _; exact: hx.
  by rewrite heq !probability_setT.
have heq : (fun=> x) @^-1` U = @set0 mR.
  rewrite /preimage; apply: boolp.funext => r /=.
  by apply: boolp.propext; split => // hUx; exfalso; exact: hx hUx.
by rewrite heq !measure0.
Qed.

Lemma qbs_return_random (X : qbsType R) (mu : probability mR R) :
  @qbs_morphism R X (monadP X) (qbs_return X ^~ mu).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /= => r.
exact: (@qbs_Mx_const R X).
Qed.

Arguments qbs_return_random : clear implicits.

(* 5. Bind: P(X) -> (X -> P(Y)) -> P(Y)

   The bind operation constructs the triple:
     alpha_bind(r) = alpha_{f(alpha_p(r))}(r)
     mu_bind       = mu_p

   The diagonal extraction requires showing that
     r |-> alpha_{f(alpha_p(r))}(r)
   is in Mx(Y). This is the "bind_alpha_random" obligation.

   With the STRONG monadP_random condition (requiring a single
   shared alpha across all r), the diagonal is trivially that
   shared alpha. The weak pointwise condition is insufficient.

   We factor qbs_bind to take an explicit proof of the diagonal
   randomness. Helper lemmas provide this proof in two cases:
   (1) Strong morphism (qbs_bind_alpha_random_strong)
   (2) Constant alpha in p (qbs_bind_alpha_random_const)

   The general case requires quotient types or a standard
   Borel isomorphism R ~ nat x R; see Section 10. *)

(* Strong morphism condition: f composed with any random alpha in X
   yields a family in monadP_random (strong) for Y. *)
Definition qbs_morphism_strong (X Y : qbsType R) (f : X -> qbs_prob Y) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> monadP_random Y (f \o alpha).

Arguments qbs_morphism_strong : clear implicits.

(* Diagonal randomness from the strong morphism condition *)
Lemma qbs_bind_alpha_random_strong (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf_strong : qbs_morphism_strong X Y f) :
  @qbs_Mx R Y (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r).
Proof.
have [alpha_Y [g [halpha [hbeta_a hbeta_g]]]] :=
  hf_strong _ (qbs_prob_alpha_random p).
have -> : (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r) = alpha_Y.
  by apply: boolp.funext => r; rewrite /= hbeta_a.
exact: halpha.
Qed.

(* Diagonal randomness when alpha_p is constant (i.e., p comes from return).
   Then f(alpha_p(r)) = f(x) for all r, so the diagonal is just
   qbs_prob_alpha(f(x)), which is random by construction. *)
Lemma qbs_bind_alpha_random_const (X Y : qbsType R) (x : X)
  (f : X -> qbs_prob Y) :
  @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f ((fun _ : mR => x) r)) r).
Proof. exact: (qbs_prob_alpha_random (f x)). Qed.

(* Diagonal randomness for bind with return on the right:
   f = qbs_return X ^~ mu, so qbs_prob_alpha(f(alpha_p(r)))(r) =
   (fun _ => alpha_p(r))(r) = alpha_p(r). *)
Lemma qbs_bind_alpha_random_return (X : qbsType R) (p : qbs_prob X)
  (mu : probability mR R) :
  @qbs_Mx R X
    (fun r => qbs_prob_alpha (qbs_return X (qbs_prob_alpha p r) mu) r).
Proof. exact: (qbs_prob_alpha_random p). Qed.

(* General bind: takes an explicit proof of diagonal randomness *)
Definition qbs_bind (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)) : qbs_prob Y :=
  @mkQBSProb Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)
    (qbs_prob_mu p)
    hdiag.

Arguments qbs_bind : clear implicits.

(* Bind specialized for strong morphisms *)
Definition qbs_bind_strong (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) : qbs_prob Y :=
  qbs_bind X Y p f (qbs_bind_alpha_random_strong p hf).

Arguments qbs_bind_strong : clear implicits.

(* Bind morphism for the monad structure.
   We need the strong condition for f to extract the diagonal. *)
Lemma qbs_bind_morph (X Y : qbsType R) (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) :
  @qbs_morphism R (monadP X) (monadP Y)
    (fun p => qbs_bind_strong X Y p f hf).
Proof.
move=> beta hbeta; rewrite /qbs_Mx /= => r.
exact: (qbs_bind_alpha_random_strong (beta r) hf).
Qed.

(* 6. Monad Laws (up to qbs_prob_equiv)
   Left unit and right unit are fully proved. Associativity
   is proved assuming the strong morphism condition. *)

Lemma qbs_bind_returnl (X Y : qbsType R) (x : X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morphism R X (monadP Y) f) :
  qbs_prob_equiv Y
    (qbs_bind X Y (qbs_return X x (qbs_prob_mu (f x))) f
      (qbs_bind_alpha_random_const x f))
    (f x).
Proof.
move=> U hU /=.
by [].
Qed.

Lemma qbs_bind_returnr (X : qbsType R) (m : qbs_prob X)
  (mu : probability mR R) :
  qbs_prob_equiv X
    (qbs_bind X X m (qbs_return X ^~ mu)
      (qbs_bind_alpha_random_return m mu)) m.
Proof. by move=> U hU. Qed.

Lemma qbs_bindA (X Y Z : qbsType R) (m : qbs_prob X)
  (f : X -> qbs_prob Y) (g : Y -> qbs_prob Z)
  (hf_diag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha m r)) r))
  (hg_bind : forall (p : qbs_prob Y),
    @qbs_Mx R Z
      (fun r => qbs_prob_alpha (g (qbs_prob_alpha p r)) r))
  (hfg_diag : @qbs_Mx R Z
    (fun r => qbs_prob_alpha
      (g (qbs_prob_alpha (f (qbs_prob_alpha m r)) r)) r)) :
  qbs_prob_equiv Z
    (qbs_bind Y Z (qbs_bind X Y m f hf_diag) g (hg_bind _))
    (mkQBSProb
      (fun r => qbs_prob_alpha
        (g (qbs_prob_alpha (f (qbs_prob_alpha m r)) r)) r)
      (qbs_prob_mu m)
      hfg_diag).
Proof. by move=> U hU. Qed.

(* 7. Integration on QBS Probability Spaces *)

Definition qbs_integral (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x)))%E.

Arguments qbs_integral : clear implicits.

(* Sigma_Mx-measurability for functions h : X -> \bar R.
   h is sigma_Mx-measurable iff for every random element alpha
   in Mx(X), the composition h o alpha : R -> \bar R is Borel
   measurable. *)
Definition qbs_measurable (X : qbsType R) (h : X -> \bar R) : Prop :=
  forall alpha, @qbs_Mx R X alpha ->
    measurable_fun setT (h \o alpha).

Arguments qbs_measurable : clear implicits.

(* If h is sigma_Mx-measurable, then preimages of
   measurable sets are in sigma_Mx. *)
Lemma qbs_measurable_sigma_Mx (X : qbsType R) (h : X -> \bar R)
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

(* When h is sigma_Mx-measurable, the pushforward measures
   through (h o alpha_i) agree on all measurable sets. *)
Lemma qbs_pushforward_agree (X : qbsType R) (p1 p2 : qbs_prob X)
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

(* Integration respects equivalence for sigma_Mx-measurable
   integrands. The proof factors through pushforward measures
   on \bar R and uses eq_measure_integral. *)
Lemma qbs_integral_equiv (X : qbsType R) (p1 p2 : qbs_prob X)
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

(* Simpler version: when both triples share the same random
   element and the base measures agree on all measurable sets. *)
Lemma qbs_integral_equiv_same_alpha (X : qbsType R) (p1 p2 : qbs_prob X)
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

Lemma qbs_integral_const (X : qbsType R) (p : qbs_prob X) (c : \bar R) :
  qbs_integral X p (fun _ => c) = (\int[qbs_prob_mu p]_x c)%E.
Proof. by []. Qed.

Lemma qbs_integral_return (X : qbsType R) (x : X)
  (mu : probability mR R) (h : X -> \bar R) :
  qbs_integral X (qbs_return X x mu) h = (\int[mu]_r h x)%E.
Proof. by []. Qed.

Lemma qbs_integral_bind (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r))
  (h : Y -> \bar R) :
  qbs_integral Y (qbs_bind X Y p f hdiag) h =
  (\int[qbs_prob_mu p]_r
    h (qbs_prob_alpha (f (qbs_prob_alpha p r)) r))%E.
Proof. by []. Qed.

(* 7b. Pushforward integral infrastructure
   Since X is a QBS (not a measurableType), we compose with
   h : X -> \bar R to obtain pushforward mu (h o alpha). *)

(* The QBS integral equals the integral of id against the
   pushforward of mu through (h o alpha). *)
Lemma qbs_integral_as_pushforward (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint : (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p)) :
  qbs_integral X p h =
  (\int[pushforward (qbs_prob_mu p) (h \o qbs_prob_alpha p)]_y y)%E.
Proof.
rewrite /qbs_integral.
have hma := hm _ (qbs_prob_alpha_random p).
rewrite -(@integral_pushforward _ _ mR (\bar R : measurableType _) R
  (h \o qbs_prob_alpha p) hma
  (qbs_prob_mu p) setT id
  (@measurable_id _ (\bar R) setT) hint measurableT).
by [].
Qed.

(* Pushforward integrability: if h o alpha is mu-integrable,
   then id is integrable w.r.t. the pushforward measure. *)
Lemma qbs_pushforward_integrable (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint : (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p)) :
  (pushforward (qbs_prob_mu p) (h \o qbs_prob_alpha p)).-integrable setT id.
Proof.
have hma := hm _ (qbs_prob_alpha_random p).
exact: (integrable_pushforward hma
  (@measurable_id _ (\bar R) setT) hint measurableT).
Qed.

(* 8. Functorial action of the probability monad *)

Definition monadP_map (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism R X Y f) (p : qbs_prob X) : qbs_prob Y :=
  @mkQBSProb Y
    (f \o qbs_prob_alpha p)
    (qbs_prob_mu p)
    (hf _ (qbs_prob_alpha_random p)).

Arguments monadP_map : clear implicits.

Lemma monadP_map_morph (X Y : qbsType R) (f : @qbsHomType R X Y) :
  @qbs_morphism R (monadP X) (monadP Y)
    (monadP_map X Y f (@qbs_hom_proof R X Y f)).
Proof.
move=> beta hbeta; rewrite /qbs_Mx /= => r.
exact: (@qbs_hom_proof R X Y f) _ (hbeta r).
Qed.

Lemma monadP_map_id (X : qbsType R) (p : qbs_prob X) :
  qbs_prob_equiv X
    (monadP_map X X idfun (@qbs_morphism_id R X) p) p.
Proof. by move=> U hU. Qed.

Lemma monadP_map_comp (X Y Z : qbsType R)
  (f : @qbsHomType R X Y) (g : @qbsHomType R Y Z) (p : qbs_prob X) :
  qbs_prob_equiv Z
    (monadP_map X Z ((g : Y -> Z) \o (f : X -> Y))
       (@qbs_morphism_comp R X Y Z _ _
          (@qbs_hom_proof R X Y f) (@qbs_hom_proof R Y Z g)) p)
    (monadP_map Y Z g (@qbs_hom_proof R Y Z g)
       (monadP_map X Y f (@qbs_hom_proof R X Y f) p)).
Proof. by move=> U hU. Qed.

(* 9. Expectation and probability of events *)

Definition qbs_expect (X : qbsType R) (p : qbs_prob X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

Arguments qbs_expect : clear implicits.

Definition qbs_prob_event (X : qbsType R) (p : qbs_prob X)
  (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).

Arguments qbs_prob_event : clear implicits.

(* 10. Variance
   Defined via the mathcomp-analysis variance applied to
   f o alpha against the base measure mu. *)

Definition qbs_variance (X : qbsType R) (p : qbs_prob X)
  (f : X -> R) : \bar R :=
  variance (qbs_prob_mu p) (f \o qbs_prob_alpha p).

Arguments qbs_variance : clear implicits.

(* 11. Monad Join: P(P(X)) -> P(X)
   Flattens a probability over probabilities into a single
   probability, defined via bind with the identity function. *)

Definition qbs_join (X : qbsType R)
  (p : qbs_prob (monadP X))
  (hdiag : @qbs_Mx R X
    (fun r => qbs_prob_alpha (id (qbs_prob_alpha p r)) r)) :
  qbs_prob X :=
  qbs_bind (monadP X) X p id hdiag.

Arguments qbs_join : clear implicits.

(* 12. Monad Strength: W x P(X) -> P(W x X)
   Given a constant w : W and a probability p on X, produce a
   probability on W x X where W is held constant. *)

Definition qbs_strength (W X : qbsType R)
  (w : W) (p : qbs_prob X) : qbs_prob (prodQ W X) :=
  @mkQBSProb (prodQ W X)
    (fun r => (w, qbs_prob_alpha p r))
    (qbs_prob_mu p)
    (prodQ_const_random w (qbs_prob_alpha_random p)).

Arguments qbs_strength : clear implicits.

(* 13. Bind respects equivalence
   The key result: bind respects equivalence on the first
   argument. The proof requires the diagonal extraction to
   factor through a QBS morphism g : X -> Y.

   The general case requires the disintegration theorem,
   which is beyond the current development. *)

(* Bind respects equivalence on the first argument when the diagonal
   factors through a QBS morphism g : X -> Y.

   Under this condition, the bind's alpha for p is (g o alpha_p).
   The preimage (g o alpha_p)^{-1}(U) = alpha_p^{-1}(g^{-1}(U)),
   and g^{-1}(U) is in sigma_Mx(X) since g is a morphism and U is
   in sigma_Mx(Y). The equivalence p1 ~ p2 then gives the result
   directly. *)
Lemma qbs_bind_equiv_l (X Y : qbsType R)
  (p1 p2 : qbs_prob X)
  (f : X -> qbs_prob Y)
  (g : X -> Y) (hg : @qbs_morphism R X Y g)
  (hdiag1 : forall r,
    qbs_prob_alpha (f (qbs_prob_alpha p1 r)) r = g (qbs_prob_alpha p1 r))
  (hdiag2 : forall r,
    qbs_prob_alpha (f (qbs_prob_alpha p2 r)) r = g (qbs_prob_alpha p2 r))
  (hrand1 : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p1 r)) r))
  (hrand2 : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p2 r)) r))
  (hequiv : qbs_prob_equiv X p1 p2) :
  qbs_prob_equiv Y
    (qbs_bind X Y p1 f hrand1)
    (qbs_bind X Y p2 f hrand2).
Proof.
move=> U hU /=.
have heq1 : (fun r => qbs_prob_alpha (f (qbs_prob_alpha p1 r)) r) @^-1` U =
            qbs_prob_alpha p1 @^-1` (g @^-1` U).
  rewrite /preimage; apply: boolp.funext => r /=.
  by apply: boolp.propext; split => h; rewrite ?hdiag1 // -hdiag1.
have heq2 : (fun r => qbs_prob_alpha (f (qbs_prob_alpha p2 r)) r) @^-1` U =
            qbs_prob_alpha p2 @^-1` (g @^-1` U).
  rewrite /preimage; apply: boolp.funext => r /=.
  by apply: boolp.propext; split => h; rewrite ?hdiag2 // -hdiag2.
rewrite heq1 heq2.
apply: hequiv.
move=> alpha halpha.
apply: (hU (g \o alpha)).
exact: hg _ halpha.
Qed.

(* Specialization for the strong morphism case when the diagonal
   factors through a morphism g. This combines the strong morphism
   condition (for diagonal randomness) with the factoring condition
   (for the equivalence proof). *)
Lemma qbs_bind_strong_equiv_l (X Y : qbsType R)
  (p1 p2 : qbs_prob X)
  (f : X -> qbs_prob Y)
  (g : X -> Y) (hg : @qbs_morphism R X Y g)
  (hf : qbs_morphism_strong X Y f)
  (hfact1 : forall r,
    qbs_prob_alpha (f (qbs_prob_alpha p1 r)) r = g (qbs_prob_alpha p1 r))
  (hfact2 : forall r,
    qbs_prob_alpha (f (qbs_prob_alpha p2 r)) r = g (qbs_prob_alpha p2 r))
  (hequiv : qbs_prob_equiv X p1 p2) :
  qbs_prob_equiv Y
    (qbs_bind_strong X Y p1 f hf)
    (qbs_bind_strong X Y p2 f hf).
Proof.
move=> U hU.
have hrand1 := qbs_bind_alpha_random_strong p1 hf.
have hrand2 := qbs_bind_alpha_random_strong p2 hf.
exact: (@qbs_bind_equiv_l X Y p1 p2 f g hg hfact1 hfact2
          hrand1 hrand2 hequiv U hU).
Qed.

(* Bind respects equivalence for "return-like" f.
   When f(x) = (fun _ => g(x), mu_x) for a morphism g, the diagonal
   simplifies to g o alpha_p. This covers important cases like
   f(x) = qbs_return Y (g x) (mu x). *)
Lemma qbs_bind_equiv_l_return (X Y : qbsType R)
  (p1 p2 : qbs_prob X)
  (g : X -> Y) (hg : @qbs_morphism R X Y g)
  (mu_f : X -> probability mR R)
  (hequiv : qbs_prob_equiv X p1 p2) :
  let f := fun x => qbs_return Y (g x) (mu_f x) in
  qbs_prob_equiv Y
    (qbs_bind X Y p1 f (hg _ (qbs_prob_alpha_random p1)))
    (qbs_bind X Y p2 f (hg _ (qbs_prob_alpha_random p2))).
Proof.
move=> f U hU /=.
have -> : (fun r : mR => g (qbs_prob_alpha p1 r)) @^-1` U =
          qbs_prob_alpha p1 @^-1` (g @^-1` U) by [].
have -> : (fun r : mR => g (qbs_prob_alpha p2 r)) @^-1` U =
          qbs_prob_alpha p2 @^-1` (g @^-1` U) by [].
apply: hequiv.
move=> alpha halpha.
apply: (hU (g \o alpha)).
exact: hg _ halpha.
Qed.

(* 14. Strength Naturality and Coherence Laws
   The monad strength commutes with morphisms and satisfies
   the standard coherence conditions for a strong monad. *)

(* Naturality: strength commutes with morphisms f : W -> W', g : X -> X' *)
Lemma qbs_strength_natural (W W' X X' : qbsType R)
  (f : W -> W') (g : X -> X')
  (hf : @qbs_morphism R W W' f) (hg : @qbs_morphism R X X' g)
  (w : W) (p : qbs_prob X) :
  qbs_prob_equiv (prodQ W' X')
    (monadP_map (prodQ W X) (prodQ W' X')
      (fun wx => (f wx.1, g wx.2))
      (@qbs_morphism_pair R (prodQ W X) W' X'
        (f \o fst) (g \o snd)
        (qbs_morphism_comp (@qbs_morphism_fst R W X) hf)
        (qbs_morphism_comp (@qbs_morphism_snd R W X) hg))
      (qbs_strength W X w p))
    (qbs_strength W' X' (f w) (monadP_map X X' g hg p)).
Proof. by move=> U hU. Qed.

(* Unit law: projecting away the unit component recovers p *)
Lemma qbs_strength_unit (X : qbsType R) (p : qbs_prob X) :
  qbs_prob_equiv X
    (monadP_map (prodQ (unitQ R) X) X snd
      (@qbs_morphism_snd R (unitQ R) X)
      (qbs_strength (unitQ R) X tt p))
    p.
Proof. by move=> U hU. Qed.

(* Associativity: strength with (u,v) then reassociate = strength u then
   strength v *)
Lemma qbs_strength_assoc (U V X : qbsType R) (u : U) (v : V)
  (p : qbs_prob X) :
  qbs_prob_equiv (prodQ U (prodQ V X))
    (monadP_map (prodQ (prodQ U V) X) (prodQ U (prodQ V X))
      (fun t => (t.1.1, (t.1.2, t.2)))
      (@qbs_morphism_pair R (prodQ (prodQ U V) X) U (prodQ V X)
        (fst \o fst) (fun t => (t.1.2, t.2))
        (qbs_morphism_comp (@qbs_morphism_fst R (prodQ U V) X)
          (@qbs_morphism_fst R U V))
        (@qbs_morphism_pair R (prodQ (prodQ U V) X) V X
          (snd \o fst) snd
          (qbs_morphism_comp (@qbs_morphism_fst R (prodQ U V) X)
            (@qbs_morphism_snd R U V))
          (@qbs_morphism_snd R (prodQ U V) X)))
      (qbs_strength (prodQ U V) X (u, v) p))
    (qbs_strength U (prodQ V X) u (qbs_strength V X v p)).
Proof. by move=> S hS. Qed.

(* Strength + return: strength of a return is a return of the pair *)
Lemma qbs_strength_return (W X : qbsType R) (w : W) (x : X)
  (mu : probability mR R) :
  qbs_prob_equiv (prodQ W X)
    (qbs_strength W X w (qbs_return X x mu))
    (qbs_return (prodQ W X) (w, x) mu).
Proof. by move=> U hU. Qed.

(* Join morphism: join (= bind with id) is a QBS morphism
   P(P(X)) -> P(X) when id satisfies the strong morphism condition.
   The strong condition ensures diagonal randomness can be extracted.
   The general case requires quotient types or a standard Borel
   isomorphism R ~ nat x R; see Section 10 above. *)
Lemma qbs_join_morphism (X : qbsType R)
  (hid : qbs_morphism_strong (monadP X) X id) :
  @qbs_morphism R (monadP (monadP X)) (monadP X)
    (fun p => qbs_bind_strong (monadP X) X p id hid).
Proof. exact: qbs_bind_morph. Qed.

(* Strength morphism: the monad strength W x P(X) -> P(W x X)
   is a QBS morphism. The proof uses that for each r, the pair
   (constant w, random element alpha_p) is a random element
   of the product QBS. *)
Lemma qbs_strength_morphism (W X : qbsType R) :
  @qbs_morphism R (prodQ W (monadP X)) (monadP (prodQ W X))
    (fun wp => qbs_strength W X wp.1 wp.2).
Proof.
move=> alpha [h1 h2] /=.
rewrite /qbs_Mx /= => r.
split => /=.
- exact: qbs_Mx_const.
- exact: (h2 r).
Qed.

(* Bind decomposition: bind(p, f) = join(map(f, p)).
   The bind alpha is r |-> alpha_{f(alpha_p(r))}(r),
   and map(f, p) has alpha = f o alpha_p, so
   join(map(f, p)) has the same alpha and mu.
   The equivalence is thus definitional. *)
Lemma qbs_bind_decomp (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morphism R X (monadP Y) f)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)) :
  let p' := monadP_map X (monadP Y) f hf p in
  qbs_prob_equiv Y (qbs_bind X Y p f hdiag)
    (qbs_join Y p' hdiag).
Proof. by move=> U hU. Qed.

Local Open Scope ereal_scope.

(* 15. QBS-level integrability predicate *)

Definition qbs_integrable (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :=
  (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p).

Arguments qbs_integrable : clear implicits.

(* 16. Integrability closure under arithmetic *)

Lemma qbs_integrableD (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integrable X p (f \+ g).
Proof. exact: integrableD. Qed.

Lemma qbs_integrableB (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integrable X p (f \- g).
Proof. exact: integrableB. Qed.

Lemma qbs_integrableN (X : qbsType R) (p : qbs_prob X)
    (f : X -> \bar R) :
  qbs_integrable X p f ->
  qbs_integrable X p (-%E \o f).
Proof. exact: integrableN. Qed.

Lemma qbs_integrableZl (X : qbsType R) (p : qbs_prob X)
    (k : R) (f : X -> \bar R) :
  qbs_integrable X p f ->
  qbs_integrable X p (fun x => k%:E * f x).
Proof. exact: integrableZl. Qed.

(* 17. Integral arithmetic *)

Lemma qbs_integralD (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integral X p (f \+ g) = qbs_integral X p f + qbs_integral X p g.
Proof. exact: integralD. Qed.

Lemma qbs_integralB (X : qbsType R) (p : qbs_prob X)
    (f g : X -> \bar R) :
  qbs_integrable X p f -> qbs_integrable X p g ->
  qbs_integral X p (f \- g) = qbs_integral X p f - qbs_integral X p g.
Proof. exact: integralB. Qed.

Lemma qbs_integralZl (X : qbsType R) (p : qbs_prob X)
    (k : R) (f : X -> \bar R) :
  qbs_integrable X p f ->
  qbs_integral X p (fun x => k%:E * f x) =
  k%:E * qbs_integral X p f.
Proof. rewrite /qbs_integrable /qbs_integral => hf; exact: integralZl. Qed.

(* 18. Variance formulas *)

Lemma qbs_varianceE (X : qbsType R) (p : qbs_prob X) (h : X -> R) :
  h \o qbs_prob_alpha p \in hoelder.Lfun (qbs_prob_mu p) 2 ->
  qbs_variance X p h =
  qbs_expect X p (fun x => h x ^+ 2)%R - (qbs_expect X p h) ^+ 2.
Proof.
move=> hL2; rewrite /qbs_variance /qbs_expect /qbs_integral.
by rewrite varianceE //; congr (_ - _); rewrite unlock.
Qed.

Lemma qbs_varianceZ (X : qbsType R) (p : qbs_prob X) (a : R)
    (h : X -> R) :
  h \o qbs_prob_alpha p \in hoelder.Lfun (qbs_prob_mu p) 2 ->
  qbs_variance X p (a \o* h)%R =
  (a ^+ 2)%:E * qbs_variance X p h.
Proof.
move=> hL2; rewrite /qbs_variance.
have -> : ((a \o* h)%R \o qbs_prob_alpha p) =
          (a \o* (h \o qbs_prob_alpha p))%R.
  by apply: boolp.funext => r.
exact: varianceZ.
Qed.

(* 19. Markov inequality for QBS *)

Lemma qbs_markov (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (f : R -> R) (eps : R)
    (hm : measurable_fun setT (h \o qbs_prob_alpha p))
    (heps : (0 < eps)%R)
    (hmf : measurable_fun [set: R] f)
    (hf0 : forall r, (0 <= r)%R -> (0 <= f r)%R)
    (hfnd : {in Num.nneg &, {homo f : x y / (x <= y)%R}}) :
  (f eps)%:E * qbs_prob_event X p [set x | eps%:E <= `|(h x)%:E|] <=
  qbs_integral X p (fun x => ((f \o normr \o h) x)%:E).
Proof.
rewrite /qbs_prob_event /qbs_integral /=.
set X0 := @isMeasurableFun.phant_Build _ _ _ _ (h \o qbs_prob_alpha p) hm.
pose rv : {RV (qbs_prob_mu p) >-> R} :=
  HB.pack (h \o qbs_prob_alpha p) X0.
have -> : qbs_prob_alpha p @^-1` [set x | eps%:E <= `|(h x)%:E|] =
          [set x | eps%:E <= `|(rv x)%:E|] by [].
have -> : (fun x => ((f \o normr \o h) (qbs_prob_alpha p x))%:E) =
          (fun x => ((f \o normr \o rv) x)%:E) by [].
have := @markov _ _ R (qbs_prob_mu p) rv f eps heps hmf hf0 hfnd.
suff -> : (\int[qbs_prob_mu p]_x (((f \o normr) \o rv) x)%:E)%E =
          'E_(qbs_prob_mu p)[((f \o [eta normr]) \o rv)] by [].
by rewrite unlock.
Qed.

(* 20. Chebyshev inequality for QBS *)

Lemma qbs_chebyshev (X : qbsType R) (p : qbs_prob X)
    (h : X -> R) (eps : R)
    (hm : measurable_fun setT (h \o qbs_prob_alpha p))
    (heps : (0 < eps)%R) :
  qbs_prob_mu p
    [set x | (eps <= `|h (qbs_prob_alpha p x) -
      fine (qbs_expect X p h)|)%R] <=
  (eps ^- 2)%:E * qbs_variance X p h.
Proof.
rewrite /qbs_variance /qbs_expect /qbs_integral.
set X0 := @isMeasurableFun.phant_Build _ _ _ _ (h \o qbs_prob_alpha p) hm.
pose rv : {RV (qbs_prob_mu p) >-> R} :=
  HB.pack (h \o qbs_prob_alpha p) X0.
have hE : (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x))%:E)%E =
          'E_(qbs_prob_mu p)[rv] by rewrite unlock.
rewrite hE.
have -> : (h \o qbs_prob_alpha p) = (rv : mR -> R) by [].
have -> : [set x | (eps <= `|h (qbs_prob_alpha p x) -
    fine 'E_(qbs_prob_mu p)[rv]|)%R] =
  [set x | (eps <= `|rv x - fine 'E_(qbs_prob_mu p)[rv]|)%R] by [].
exact: chebyshev.
Qed.

End probability_qbs.

Arguments qbs_prob {R}.
Arguments mkQBSProb {R X}.
Arguments qbs_prob_alpha {R X}.
Arguments qbs_prob_mu {R X}.
Arguments qbs_prob_alpha_random {R X}.
Arguments qbs_prob_equiv {R}.
Arguments monadP {R}.
Arguments qbs_return {R}.
Arguments qbs_bind {R}.
Arguments qbs_bind_strong {R}.
Arguments qbs_morphism_strong {R}.
Arguments qbs_integral {R}.
Arguments qbs_measurable {R}.
Arguments monadP_map {R}.
Arguments qbs_expect {R}.
Arguments qbs_prob_event {R}.
Arguments qbs_variance {R}.
Arguments qbs_join {R}.
Arguments qbs_strength {R}.
Arguments qbs_integrable {R}.
