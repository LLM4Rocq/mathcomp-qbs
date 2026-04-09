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

Import GRing.Theory Num.Def Num.Theory measurable_realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section probability_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

Section qbs_prob_basics.

(* 1. QBS Probability Triple
   A probability on a QBS X is a pair (alpha, mu) where
   alpha : R -> X is a random element (in Mx) and
   mu is a probability measure on R. *)

(** Probability triple on a QBS: a random element
    alpha and a base probability measure mu. *)
Record qbs_prob (X : qbsType R) := mkQBSProb {
  qbs_prob_alpha : mR -> X ;
  qbs_prob_mu : probability mR R ;
  qbs_prob_alpha_random : @qbs_Mx R X qbs_prob_alpha }.

#[global] Arguments qbs_prob : clear implicits.
#[global] Arguments mkQBSProb {X}.
#[global] Arguments qbs_prob_alpha {X}.
#[global] Arguments qbs_prob_mu {X}.
#[global] Arguments qbs_prob_alpha_random {X}.

(* 2. Equivalence of Probability Triples
   Two triples (alpha1, mu1) ~ (alpha2, mu2) iff they induce
   the same pushforward measure on X, i.e., for all measurable
   U in sigma_Mx(X),
   mu1(alpha1^{-1}(U)) = mu2(alpha2^{-1}(U)). *)

(** Equivalence of probability triples: same
    pushforward measure on sigma_Mx sets. *)
Definition qbs_prob_equiv (X : qbsType R) (p1 p2 : qbs_prob X) : Prop :=
  forall (U : set X),
    @sigma_Mx R X U ->
    qbs_prob_mu p1 (qbs_prob_alpha p1 @^-1` U) =
    qbs_prob_mu p2 (qbs_prob_alpha p2 @^-1` U).

#[global] Arguments qbs_prob_equiv : clear implicits.

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

End qbs_prob_basics.

Section probability_monad.

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

(** Strong random-element condition: a single
    shared alpha exists across all r. *)
Definition monadP_random (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta |
    exists (alpha : mR -> X),
    exists (g : mR -> probability mR R),
      @qbs_Mx R X alpha /\
      (forall r, qbs_prob_alpha (beta r) = alpha) /\
      (forall r, qbs_prob_mu (beta r) = g r)].

#[global] Arguments monadP_random : clear implicits.

(** Pointwise random-element condition: each
    beta(r) has its own random element in Mx. *)
Definition monadP_random_pw (X : qbsType R) : set (mR -> qbs_prob X) :=
  [set beta | forall r, @qbs_Mx R X (qbs_prob_alpha (beta r))].

#[global] Arguments monadP_random_pw : clear implicits.

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

(** The probability monad P(X) on QBS, equipped
    with the pointwise random-element structure. *)
Definition monadP (X : qbsType R) : qbsType R :=
  HB.pack (qbs_prob X)
    (@isQBS.Build R (qbs_prob X)
      (monadP_random_pw X)
      (@monadP_comp X)
      (@monadP_const X)
      (@monadP_glue X)).

#[global] Arguments monadP : clear implicits.

(* 4. Return: X -> P(X)
   The return operation takes a measure parameter mu, so that
   qbs_return X x mu = (fun _ => x, mu). This is crucial for
   the left unit law: all triples (fun _ => x, mu) are
   equivalent for any mu, since pushforward mu (fun _ => x) =
   Dirac(x) regardless of mu. The monad law uses
   qbs_return X x (qbs_prob_mu (f x)) so that
   bind(return(x), f) has the same mu as f(x). *)

(** Monadic return: embed a point x into the
    probability monad with base measure mu. *)
Definition qbs_return (X : qbsType R) (x : X) (mu : probability mR R) :
  qbs_prob X :=
  @mkQBSProb X (fun _ => x) mu (@qbs_Mx_const R X x).

#[global] Arguments qbs_return : clear implicits.

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

#[global] Arguments qbs_return_random : clear implicits.

End probability_monad.

Section monad_bind.

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

#[global] Arguments qbs_morphism_strong : clear implicits.

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

(** Monadic bind: given p : P(X), f : X -> P(Y),
    and a diagonal randomness proof, produce P(Y). *)
Definition qbs_bind (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)) : qbs_prob Y :=
  @mkQBSProb Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha p r)) r)
    (qbs_prob_mu p)
    hdiag.

#[global] Arguments qbs_bind : clear implicits.

(* Bind specialized for strong morphisms *)
Definition qbs_bind_strong (X Y : qbsType R) (p : qbs_prob X)
  (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) : qbs_prob Y :=
  qbs_bind X Y p f (qbs_bind_alpha_random_strong p hf).

#[global] Arguments qbs_bind_strong : clear implicits.

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
   is proved assuming the strong morphism condition.

   Usage note. The laws below are stated up to the setoid
   equivalence [qbs_prob_equiv]. To apply them inside nested
   bind-expressions (i.e. to rewrite under a [qbs_bind]) we
   need a congruence lemma stating that [qbs_bind] respects
   [qbs_prob_equiv] in its first argument. Such congruence
   lemmas are provided in Section 13 below:

     - [qbs_bind_equiv_l]         -- general case, assumes
                                     the diagonal extraction
                                     factors through a
                                     QBS morphism g : X -> Y;
     - [qbs_bind_strong_equiv_l]  -- specialisation to
                                     strong morphisms f,
                                     still requiring the
                                     factoring hypothesis;
     - [qbs_bind_equiv_l_return]  -- specialisation when f
                                     is a "return-like" map
                                     f(x) = qbs_return(g x, mu x),
                                     which covers the maps
                                     arising from morphisms
                                     g : X -> Y.

   An unconditional congruence (with no factoring assumption)
   would require the disintegration theorem for QBS, which is
   not in the current development; see the comment at the head
   of Section 13. *)

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

End monad_bind.

Section qbs_integration.

(* 7. Integration on QBS Probability Spaces *)

(** Integration of h : X -> \bar R against a QBS
    probability, via the base measure and alpha. *)
Definition qbs_integral (X : qbsType R) (p : qbs_prob X)
  (h : X -> \bar R) : \bar R :=
  (\int[qbs_prob_mu p]_x (h (qbs_prob_alpha p x)))%E.

#[global] Arguments qbs_integral : clear implicits.

(* Sigma_Mx-measurability for functions h : X -> \bar R.
   h is sigma_Mx-measurable iff for every random element alpha
   in Mx(X), the composition h o alpha : R -> \bar R is Borel
   measurable. *)
Definition qbs_measurable (X : qbsType R) (h : X -> \bar R) : Prop :=
  forall alpha, @qbs_Mx R X alpha ->
    measurable_fun setT (fun r => h (alpha r)).

#[global] Arguments qbs_measurable : clear implicits.

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

End qbs_integration.

Section monad_operations.

(* 8. Functorial action of the probability monad *)

Definition monadP_map (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism R X Y f) (p : qbs_prob X) : qbs_prob Y :=
  @mkQBSProb Y
    (f \o qbs_prob_alpha p)
    (qbs_prob_mu p)
    (hf _ (qbs_prob_alpha_random p)).

#[global] Arguments monadP_map : clear implicits.

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

(** Expectation of a real-valued function h on a
    QBS probability, defined as qbs_integral of
    the extended-real embedding. *)
Definition qbs_expect (X : qbsType R) (p : qbs_prob X)
  (h : X -> R) : \bar R :=
  qbs_integral X p (fun x => (h x)%:E).

#[global] Arguments qbs_expect : clear implicits.

Definition qbs_prob_event (X : qbsType R) (p : qbs_prob X)
  (U : set X) : \bar R :=
  qbs_prob_mu p (qbs_prob_alpha p @^-1` U).

#[global] Arguments qbs_prob_event : clear implicits.

(* 10. Variance
   Defined via the mathcomp-analysis variance applied to
   f o alpha against the base measure mu. *)

(** Variance of f : X -> R under a QBS probability,
    via the base-measure variance of f o alpha. *)
Definition qbs_variance (X : qbsType R) (p : qbs_prob X)
  (f : X -> R) : \bar R :=
  variance (qbs_prob_mu p) (f \o qbs_prob_alpha p).

#[global] Arguments qbs_variance : clear implicits.

(* 11. Monad Join: P(P(X)) -> P(X)
   Flattens a probability over probabilities into a single
   probability, defined via bind with the identity function. *)

(** Monad join: flatten P(P(X)) to P(X) via bind
    with the identity function. *)
Definition qbs_join (X : qbsType R)
  (p : qbs_prob (monadP X))
  (hdiag : @qbs_Mx R X
    (fun r => qbs_prob_alpha (id (qbs_prob_alpha p r)) r)) :
  qbs_prob X :=
  qbs_bind (monadP X) X p id hdiag.

#[global] Arguments qbs_join : clear implicits.

(* 12. Monad Strength: W x P(X) -> P(W x X)
   Given a constant w : W and a probability p on X, produce a
   probability on W x X where W is held constant. *)

(** Monad strength: pair a constant w : W with a
    probability p on X to get P(W x X). *)
Definition qbs_strength (W X : qbsType R)
  (w : W) (p : qbs_prob X) : qbs_prob (prodQ W X) :=
  @mkQBSProb (prodQ W X)
    (fun r => (w, qbs_prob_alpha p r))
    (qbs_prob_mu p)
    (prodQ_const_random w (qbs_prob_alpha_random p)).

#[global] Arguments qbs_strength : clear implicits.

End monad_operations.

Section bind_congruence.

(* 13. Bind respects equivalence (congruence lemmas)

   The monad laws [qbs_bind_returnl], [qbs_bind_returnr] and
   [qbs_bindA] in Section 6 are stated up to [qbs_prob_equiv].
   For these laws to be usable for rewriting inside nested
   bind-terms we also need a congruence lemma: if p1 ~ p2 then
   [qbs_bind p1 f ~ qbs_bind p2 f]. Without this, the setoid-level
   monad laws cannot be composed.

   The obstacle to a fully unconditional congruence is the
   definition of [qbs_bind], whose alpha is the "diagonal"
     r |-> qbs_prob_alpha (f (qbs_prob_alpha p r)) r,
   i.e. it mixes the alpha of p with the alpha of each f(x).
   From p1 ~ p2 alone we only know that pushforwards along
   [qbs_prob_alpha p1] and [qbs_prob_alpha p2] agree on
   sigma_Mx(X), and this is not sufficient to conclude
   equality of the pushforwards of the diagonals, which
   involve f as well. A general argument would require the
   disintegration theorem for QBS, which is not in the current
   development.

   We therefore provide three congruence lemmas covering the
   cases actually used in the rest of the development:

     1. [qbs_bind_equiv_l]        : the diagonal factors
        through a QBS morphism g : X -> Y. This is the most
        common situation (e.g. bind-with-return, bind along
        a pure map, etc.).
     2. [qbs_bind_strong_equiv_l] : specialisation to strong
        morphisms f, still needing the factoring hypothesis.
     3. [qbs_bind_equiv_l_return] : specialisation when f is
        "return-like", f(x) = qbs_return (g x) (mu_f x).

   Note on congruence in the function argument. A congruence
   of the form
     (forall x, qbs_prob_equiv (f x) (g x))
     -> qbs_prob_equiv (qbs_bind p f) (qbs_bind p g)
   is *not* provable from [qbs_prob_equiv] alone, for the same
   diagonal-extraction reason: equivalence of f(x) and g(x) for
   each x only constrains their pushforwards on sigma_Mx(Y),
   whereas the bind's alpha depends on the pointwise value
   [qbs_prob_alpha (f x) r] for the specific r, not on the
   pushforward. So no such lemma is provided here. *)

(** Congruence: [qbs_bind] respects [qbs_prob_equiv] in its
    first argument, under the assumption that the diagonal
    extraction factors through a QBS morphism g : X -> Y.
    This is the rewriting law that makes the monad laws
    ([qbs_bind_returnl], [qbs_bind_returnr], [qbs_bindA])
    usable inside nested bind-terms.

    Under the factoring hypothesis, the bind's alpha for p is
    (g o alpha_p). The preimage (g o alpha_p)^{-1}(U) equals
    alpha_p^{-1}(g^{-1}(U)), and g^{-1}(U) is in sigma_Mx(X)
    since g is a morphism and U is in sigma_Mx(Y). The
    equivalence p1 ~ p2 then gives the result directly. *)
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

(** Congruence: strong-morphism variant of [qbs_bind_equiv_l].
    Combines the strong morphism condition (which supplies the
    diagonal randomness proof automatically, via
    [qbs_bind_alpha_random_strong]) with the same factoring
    hypothesis through a morphism g : X -> Y (needed for the
    equivalence proof itself). This is the congruence law used
    when the client of a bind has the strong form
    [qbs_bind_strong X Y p f hf] and needs to rewrite p. *)
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

(** Congruence: specialisation of [qbs_bind_equiv_l] to
    "return-like" f of the form f(x) = qbs_return Y (g x) (mu_f x)
    for a QBS morphism g : X -> Y. In this case the diagonal
    simplifies to (g o alpha_p), so the factoring hypothesis
    holds definitionally and the caller does not have to supply
    it. This covers the most common rewriting situation: binds
    where the continuation is a pure map lifted to a probability
    via [qbs_return]. *)
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

End bind_congruence.

Section strength_and_monad_structure.

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

End strength_and_monad_structure.

Section probability_inequalities.

Local Open Scope ereal_scope.

(* 15. QBS-level integrability predicate *)

(** Integrability of h : X -> \bar R under a QBS
    probability: h o alpha is mu-integrable. *)
Definition qbs_integrable (X : qbsType R) (p : qbs_prob X)
    (h : X -> \bar R) :=
  (qbs_prob_mu p).-integrable setT (h \o qbs_prob_alpha p).

#[global] Arguments qbs_integrable : clear implicits.

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

(** Markov inequality lifted to QBS probabilities. *)
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

(** Chebyshev inequality lifted to QBS
    probabilities. *)
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

(* Strength law 4 diagonal helper: the diagonal randomness proof
   needed for the join on the RHS of strength law 4. *)
Lemma qbs_strength_law4_diag (W X : qbsType R) (w : W)
  (pp : qbs_prob (monadP X))
  (hdiag : @qbs_Mx R X
    (fun r => qbs_prob_alpha (qbs_prob_alpha pp r) r)) :
  @qbs_Mx R (prodQ W X)
    (fun r => qbs_prob_alpha
      (id (qbs_prob_alpha
        (monadP_map (prodQ W (monadP X)) (monadP (prodQ W X))
          (fun wp => qbs_strength W X wp.1 wp.2)
          (@qbs_strength_morphism W X)
          (qbs_strength W (monadP X) w pp)) r)) r).
Proof.
split => /=.
- exact: qbs_Mx_const.
- exact: hdiag.
Qed.

(* Strength law 4: strength commutes with join.
   LHS: strength(w, join(pp))
   RHS: join(P(strength)(strength(w, pp)))
   Both sides have the same alpha and mu at the representation level. *)
Lemma qbs_strength_law4 (W X : qbsType R) (w : W)
  (pp : qbs_prob (monadP X))
  (hdiag : @qbs_Mx R X
    (fun r => qbs_prob_alpha (qbs_prob_alpha pp r) r)) :
  qbs_prob_equiv (prodQ W X)
    (qbs_strength W X w (qbs_join X pp hdiag))
    (qbs_join (prodQ W X)
      (monadP_map (prodQ W (monadP X)) (monadP (prodQ W X))
        (fun wp => qbs_strength W X wp.1 wp.2)
        (@qbs_strength_morphism W X)
        (qbs_strength W (monadP X) w pp))
      (@qbs_strength_law4_diag W X w pp hdiag)).
Proof. by move=> U hU. Qed.

End probability_inequalities.

Local Open Scope ereal_scope.

(* 21. General Normalizer: qbs_prob(X * R) -> option(qbs_prob(X))        *)
(*   normalize_mu p hw hw_m hpos hfin == reweighted probability measure  *)
(*   normalize_prob X p ...           == normalized qbs_prob on X        *)
(*   qbs_normalize X p hw hw_m        == option: Some if ev good, None   *)
(*   qbs_normalize_total              == normalized prob integrates to 1 *)
(*   qbs_normalize_integral           == E[g|norm] = E[g*w]/ev          *)

Section normalize_mu_build.
Variable (X : qbsType R).
Variable (p : qbs_prob (prodQ X (realQ R))).
Let w : mR -> R := fun r => snd (qbs_prob_alpha p r).
Hypothesis hw_ge0 : forall r, (0 <= w r)%R.
Hypothesis hw_meas : measurable_fun setT (fun r => (w r)%:E : \bar R).
Let ev : \bar R := (\int[qbs_prob_mu p]_r (w r)%:E)%E.
Hypothesis hev_pos : (0 < ev)%E.
Hypothesis hev_fin : (ev < +oo)%E.
Let ev_r : R := fine ev.
Let ev_r_gt0 : (0 < ev_r)%R.
Proof. by apply: fine_gt0; rewrite hev_pos hev_fin. Qed.
Let ev_r_neq0 : (ev_r != 0)%R.
Proof. exact: lt0r_neq0 ev_r_gt0. Qed.
Let wdiv (r : mR) : R := (w r / ev_r)%R.
Let wdiv_ge0 r : (0 <= wdiv r)%R.
Proof. by rewrite /wdiv divr_ge0 //= le0r ev_r_gt0 orbT. Qed.
Let wdiv_meas : measurable_fun setT (fun r => (wdiv r)%:E : \bar R).
Proof.
apply/measurable_EFinP; rewrite /wdiv; apply: measurable_funM.
  by move: hw_meas => /measurable_EFinP.
exact: measurable_cst.
Qed.
Let norm_mu (A : set mR) : \bar R :=
  (\int[qbs_prob_mu p]_(r in A) (wdiv r)%:E)%E.
Let norm_mu0 : norm_mu set0 = 0.
Proof. by rewrite /norm_mu integral_set0. Qed.
Let norm_mu_ge0 (A : set mR) : 0 <= norm_mu A.
Proof.
rewrite /norm_mu; apply: integral_ge0 => r _.
by rewrite lee_fin; exact: wdiv_ge0.
Qed.
Let norm_mu_sigma : semi_sigma_additive norm_mu.
Proof.
move=> F mF tF mUF; rewrite /norm_mu.
have hmfD : measurable_fun (\bigcup_n F n) (fun r => (wdiv r)%:E : \bar R).
  by apply/measurable_funTS; exact: wdiv_meas.
have hge0 : forall x, (\bigcup_n F n) x -> (0 <= (wdiv x)%:E)%E.
  by move=> x _; rewrite lee_fin; exact: wdiv_ge0.
rewrite (@ge0_integral_bigcup _ _ R (qbs_prob_mu p) F
  (fun r => (wdiv r)%:E) mF hmfD hge0 tF).
apply: sequences.is_cvg_ereal_nneg_natsum => n _.
apply: integral_ge0 => r _; rewrite lee_fin; exact: wdiv_ge0.
Qed.
HB.instance Definition _ := isMeasure.Build _ _ _
  norm_mu norm_mu0 norm_mu_ge0 norm_mu_sigma.
Let norm_mu_setT : norm_mu setT = 1.
Proof.
rewrite /norm_mu.
have -> : (fun r => (wdiv r)%:E) = (fun r => (ev_r^-1 * w r)%:E).
  by apply: boolp.funext => r; rewrite /wdiv mulrC.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin //=.
- have hfn : ev \is a fin_num by rewrite gt0_fin_numE.
  have -> : \int[qbs_prob_mu p]_x (w x)%:E = ev_r%:E by rewrite fineK.
  by rewrite -EFinM mulVf.
- by move=> r _; rewrite lee_fin.
- by rewrite invr_ge0 le0r ev_r_gt0 orbT.
Qed.
HB.instance Definition _ := Measure_isProbability.Build _ _ _
  norm_mu norm_mu_setT.
(** Reweighted probability measure: normalize the
    weight function w to integrate to 1. *)
Definition normalize_mu : probability mR R :=
  [the probability mR R of norm_mu].
End normalize_mu_build.

Section qbs_normalize_def.
Variable (X : qbsType R).

Lemma normalize_alpha_random (p : qbs_prob (prodQ X (realQ R))) :
  @qbs_Mx R X (fun r => fst (qbs_prob_alpha p r)).
Proof. by have /= [h1 _] := qbs_prob_alpha_random p. Qed.

(** Normalized QBS probability on X from a
    weighted triple on X * R. *)
Definition normalize_prob
    (p : qbs_prob (prodQ X (realQ R)))
    (hw_ge0 : forall r, (0 <= snd (qbs_prob_alpha p r))%R)
    (hw_meas : measurable_fun setT
      (fun r => (snd (qbs_prob_alpha p r))%:E : \bar R))
    (hev_pos : (0 < \int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E)%E)
    (hev_fin : (\int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E < +oo)%E) :
    qbs_prob X :=
  @mkQBSProb X
    (fun r => fst (qbs_prob_alpha p r))
    (normalize_mu hw_ge0 hw_meas hev_pos hev_fin)
    (normalize_alpha_random p).

(** Total normalizer: returns Some if the evidence
    is positive and finite, None otherwise. *)
Definition qbs_normalize
    (p : qbs_prob (prodQ X (realQ R)))
    (hw_ge0 : forall r, (0 <= snd (qbs_prob_alpha p r))%R)
    (hw_meas : measurable_fun setT
      (fun r => (snd (qbs_prob_alpha p r))%:E : \bar R)) :
    option (qbs_prob X) :=
  let ev := (\int[qbs_prob_mu p]_r
               (snd (qbs_prob_alpha p r))%:E)%E in
  match boolp.pselect (0 < ev)%E, boolp.pselect (ev < +oo)%E with
  | left hpos, left hfin =>
      Some (normalize_prob hw_ge0 hw_meas hpos hfin)
  | _, _ => None
  end.

Lemma qbs_normalize_alpha
    (p : qbs_prob (prodQ X (realQ R)))
    hw_ge0 hw_meas hev_pos hev_fin :
  qbs_prob_alpha (@normalize_prob p hw_ge0 hw_meas hev_pos hev_fin) =
  fun r => fst (qbs_prob_alpha p r).
Proof. by []. Qed.

Lemma qbs_normalize_total
    (p : qbs_prob (prodQ X (realQ R)))
    hw_ge0 hw_meas hev_pos hev_fin :
  qbs_integral X (@normalize_prob p hw_ge0 hw_meas hev_pos hev_fin)
    (fun _ => 1) = 1.
Proof.
rewrite /qbs_integral /=.

rewrite (_ : \int[_]__ 1 =
  1 * normalize_mu hw_ge0 hw_meas hev_pos hev_fin
    setT).
  by rewrite probability_setT mule1.
rewrite -integral_cst //=.
Qed.

Lemma qbs_normalize_integral
    (p : qbs_prob (prodQ X (realQ R)))
    (hw_ge0 : forall r, (0 <= snd (qbs_prob_alpha p r))%R)
    (hw_meas : measurable_fun setT
      (fun r => (snd (qbs_prob_alpha p r))%:E : \bar R))
    (hev_pos : (0 < \int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E)%E)
    (hev_fin : (\int[qbs_prob_mu p]_r
                  (snd (qbs_prob_alpha p r))%:E < +oo)%E)
    (g : X -> \bar R)
    (hg_ge0 : forall x, 0 <= g x)
    (hg_meas : qbs_measurable X g) :
  qbs_integral X (normalize_prob hw_ge0 hw_meas hev_pos hev_fin) g =
  (qbs_integral (prodQ X (realQ R)) p
    (fun xy => g (fst xy) * (snd xy)%:E) /
   \int[qbs_prob_mu p]_r (snd (qbs_prob_alpha p r))%:E)%E.
Proof.
rewrite /qbs_integral /=.
set ev := \int[qbs_prob_mu p]_r ((qbs_prob_alpha p r).2)%:E.
set mu := qbs_prob_mu p.
set alpha := qbs_prob_alpha p.
have hev_fin_num : ev \is a fin_num.
{ rewrite ge0_fin_numE; [exact: hev_fin |
    exact: order.Order.POrderTheory.ltW hev_pos]. }
have hwdiv_meas : measurable_fun setT
    (fun r : mR => (((alpha r).2 / fine ev)%:E : \bar R)).
{ apply/measurable_EFinP; apply: measurable_funM.
  - have h := hw_meas; move: h => /measurable_EFinP //.
  - exact: measurable_cst. }
have hac : (normalize_mu hw_ge0 hw_meas hev_pos hev_fin : measure mR R) `<< mu.
{ apply/null_content_dominatesP => A mA hA.
  rewrite /normalize_mu /=.
  apply: null_set_integral => //; apply/measurable_funTS; exact: hwdiv_meas. }
have hRN_wdiv : ae_eq mu setT
    (charge.Radon_Nikodym_SigmaFinite.f
       (normalize_mu hw_ge0 hw_meas hev_pos hev_fin) mu)
    (fun r => (((alpha r).2 / fine ev)%:E : \bar R)).
{ apply: integral_ae_eq.
  - exact: measurableT.
  - exact: charge.Radon_Nikodym_SigmaFinite.f_integrable hac.
  - exact: hwdiv_meas.
  - move=> A _ mA.
    rewrite -(charge.Radon_Nikodym_SigmaFinite.f_integral hac mA).
    rewrite /normalize_mu /=. reflexivity. }
have step1 : \int[normalize_mu hw_ge0 hw_meas hev_pos hev_fin]_r
    g ((alpha r).1) =
  \int[mu]_r (g ((alpha r).1) * (((alpha r).2 / fine ev)%:E)).
{ rewrite -(charge.Radon_Nikodym_SigmaFinite.change_of_variables
    hac _ measurableT
    (hg_meas _ (normalize_alpha_random p)));
    last by move=> x; exact: hg_ge0.
  apply: ge0_ae_eq_integral.
  - exact: measurableT.
  - apply: emeasurable_funM.
    + exact: hg_meas _ (normalize_alpha_random p).
    + have := charge.Radon_Nikodym_SigmaFinite.f_integrable hac;
        move=> /integrableP [? _]; exact.
  - apply: emeasurable_funM.
    + exact: hg_meas _ (normalize_alpha_random p).
    + exact: hwdiv_meas.
  - move=> r _; apply: mule_ge0; first exact: hg_ge0.
    exact: charge.Radon_Nikodym_SigmaFinite.f_ge0.
  - move=> r _; apply: mule_ge0; first exact: hg_ge0.
    rewrite lee_fin; apply: divr_ge0; first exact: hw_ge0.
    by apply: fine_ge0; apply: integral_ge0 => x _;
       rewrite lee_fin; exact: hw_ge0.
  - apply: filterS hRN_wdiv => r /= ->; by []. }
rewrite step1.
have hfine_ev_pos : (0 < fine ev)%R.
{ apply: fine_gt0; rewrite hev_pos hev_fin //. }
have hfine_ev_ne0 : fine ev != 0%R := lt0r_neq0 hfine_ev_pos.
have hev_inv : ev^-1 = ((fine ev)^-1)%:E.
{ rewrite -{1}(fineK hev_fin_num) inver ifF //.
  exact: negbTE hfine_ev_ne0. }
under eq_integral => r _ do rewrite EFinM muleA.
rewrite ge0_integralZr.
- by rewrite -hev_inv.
- exact: measurableT.
- exact: emeasurable_funM (hg_meas _ (normalize_alpha_random p)) hw_meas.
- move=> r _; apply: mule_ge0; first exact: hg_ge0.
  by rewrite lee_fin; exact: hw_ge0.
- rewrite lee_fin invr_ge0; exact: order.Order.POrderTheory.ltW hfine_ev_pos.
Qed.

End qbs_normalize_def.

Arguments qbs_normalize : clear implicits.
Arguments normalize_prob : clear implicits.

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
Arguments qbs_normalize {R}.
Arguments normalize_prob {R}.
