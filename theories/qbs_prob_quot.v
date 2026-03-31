(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.classical Require Import classical_sets boolp.
From mathcomp Require Import ereal.
From mathcomp.analysis Require Import measure_theory.measurable_structure.
From mathcomp.analysis Require Import measure_theory.measurable_function.
From mathcomp.analysis Require Import measure_theory.probability_measure.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import lebesgue_integral.
From QBS Require Import quasi_borel probability_qbs.

Import Num.Def Num.Theory reals classical_sets.

(**md**************************************************************************)
(* # Quotient Type for QBS Probability Spaces                                 *)
(*                                                                            *)
(* We define a setoid-style quotient over qbs_prob, where equality is         *)
(* qbs_prob_equiv (same pushforward measure). We lift the monadic             *)
(* operations (return, bind) and integration to this quotient type, and       *)
(* prove the monad laws hold as equalities under qps_eq.                      *)
(*                                                                            *)
(* ```                                                                        *)
(*   qbs_prob_space X == setoid-quotient wrapping a qbs_prob X representative *)
(*   qps_eq p1 p2     == equality via qbs_prob_equiv on representatives       *)
(*   qps_return x mu   == return lifted to the quotient                       *)
(*   qps_bind p f hdiag == bind lifted to the quotient                        *)
(*   qps_integral p h  == integration lifted to the quotient                  *)
(*   qps_map f hf p    == functorial map lifted to the quotient               *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section QBSProbQuot.
Variable (R : realType).
Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* 1. The Quotient Type (setoid-style)                                    *)
(*    A qbs_prob_space X wraps a qbs_prob X representative.              *)
(*    Equality is qbs_prob_equiv: two wrapped triples are equal iff      *)
(*    they induce the same pushforward measure.                          *)
(* ===================================================================== *)

Record qbs_prob_space (X : qbsType R) := QPS {
  qps_repr : qbs_prob X ;
}.

Arguments QPS {X}.
Arguments qps_repr {X}.

Definition qps_eq (X : qbsType R) (p1 p2 : qbs_prob_space X) : Prop :=
  qbs_prob_equiv X (qps_repr p1) (qps_repr p2).

Arguments qps_eq {X}.

(* qps_eq is an equivalence relation *)
Lemma qps_eqxx (X : qbsType R) (p : qbs_prob_space X) :
  qps_eq p p.
Proof. exact: qbs_prob_equivxx. Qed.

Lemma qps_eqC (X : qbsType R) (p1 p2 : qbs_prob_space X) :
  qps_eq p1 p2 -> qps_eq p2 p1.
Proof. exact: qbs_prob_equivC. Qed.

Lemma qps_eq_trans (X : qbsType R) (p1 p2 p3 : qbs_prob_space X) :
  qps_eq p1 p2 -> qps_eq p2 p3 -> qps_eq p1 p3.
Proof. exact: qbs_prob_equiv_trans. Qed.

(* Embedding: wrap a qbs_prob into the quotient *)
Definition qps_of (X : qbsType R) (p : qbs_prob X) : qbs_prob_space X :=
  QPS p.

Arguments qps_of {X}.

(* ===================================================================== *)
(* 2. Lifted Operations                                                   *)
(*    Return, bind, and integral lifted to qbs_prob_space.               *)
(* ===================================================================== *)

(* Return: X -> qbs_prob_space X *)
Definition qps_return (X : qbsType R) (x : X) (mu : probability mR R) :
  qbs_prob_space X :=
  qps_of (qbs_return X x mu).

Arguments qps_return {X}.

(* Bind: qbs_prob_space X -> (X -> qbs_prob Y) -> qbs_prob_space Y
   Requires the diagonal randomness proof, just like qbs_bind. *)
Definition qps_bind (X Y : qbsType R) (p : qbs_prob_space X)
  (f : X -> qbs_prob Y)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha (qps_repr p) r)) r)) :
  qbs_prob_space Y :=
  qps_of (qbs_bind X Y (qps_repr p) f hdiag).

Arguments qps_bind {X Y}.

(* Bind specialized for strong morphisms *)
Definition qps_bind_strong (X Y : qbsType R) (p : qbs_prob_space X)
  (f : X -> qbs_prob Y)
  (hf : qbs_morphism_strong X Y f) : qbs_prob_space Y :=
  qps_of (qbs_bind_strong X Y (qps_repr p) f hf).

Arguments qps_bind_strong {X Y}.

(* Integration: qbs_prob_space X -> (X -> \bar R) -> \bar R *)
Definition qps_integral (X : qbsType R) (p : qbs_prob_space X)
  (h : X -> \bar R) : \bar R :=
  qbs_integral X (qps_repr p) h.

Arguments qps_integral {X}.

(* Functorial map *)
Definition qps_map (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism R X Y f) (p : qbs_prob_space X) :
  qbs_prob_space Y :=
  qps_of (monadP_map X Y f hf (qps_repr p)).

Arguments qps_map {X Y}.

(* ===================================================================== *)
(* 3. Well-definedness: operations respect qps_eq                         *)
(* ===================================================================== *)

(* Return is well-defined: all returns at the same point are equivalent *)
Lemma qps_return_equiv (X : qbsType R) (x : X)
  (mu1 mu2 : probability mR R) :
  qps_eq (qps_return x mu1) (qps_return x mu2).
Proof. exact: qbs_return_equiv. Qed.

(* Integration respects qps_eq for sigma_Mx-measurable integrands *)
Lemma qps_integral_equiv (X : qbsType R) (p1 p2 : qbs_prob_space X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint1 : (qbs_prob_mu (qps_repr p1)).-integrable setT
    (h \o qbs_prob_alpha (qps_repr p1)))
  (hint2 : (qbs_prob_mu (qps_repr p2)).-integrable setT
    (h \o qbs_prob_alpha (qps_repr p2))) :
  qps_eq p1 p2 ->
  qps_integral p1 h = qps_integral p2 h.
Proof.
move=> heq.
exact: (qbs_integral_equiv hm hint1 hint2 heq).
Qed.

(* Map respects qps_eq *)
Lemma qps_map_equiv (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism R X Y f)
  (p1 p2 : qbs_prob_space X) :
  qps_eq p1 p2 -> qps_eq (qps_map f hf p1) (qps_map f hf p2).
Proof.
move=> heq U hU /=.
rewrite /qps_eq /= /qbs_prob_equiv /=.
have hpreimg : forall (p : qbs_prob X),
  (f \o qbs_prob_alpha p) @^-1` U = qbs_prob_alpha p @^-1` (f @^-1` U).
  by move=> p.
by rewrite !hpreimg; apply: heq; move=> alpha halpha; apply: hU; apply: hf.
Qed.

(* ===================================================================== *)
(* 4. Monad Laws on the quotient (as qps_eq equalities)                  *)
(* ===================================================================== *)

(* Left unit: bind (return x) f ~ f x *)
Lemma qps_bind_returnl (X Y : qbsType R) (x : X)
  (f : X -> qbs_prob Y)
  (hf : @qbs_morphism R X (monadP Y) f) :
  qps_eq
    (qps_bind (qps_return x (qbs_prob_mu (f x))) f
      (qbs_bind_alpha_random_const x f))
    (qps_of (f x)).
Proof. exact: qbs_bind_returnl. Qed.

(* Right unit: bind m (return ^~ mu) ~ m *)
Lemma qps_bind_returnr (X : qbsType R) (m : qbs_prob_space X)
  (mu : probability mR R) :
  qps_eq
    (qps_bind m (qbs_return X ^~ mu)
      (qbs_bind_alpha_random_return (qps_repr m) mu))
    m.
Proof. exact: qbs_bind_returnr. Qed.

(* Associativity *)
Lemma qps_bindA (X Y Z : qbsType R) (m : qbs_prob_space X)
  (f : X -> qbs_prob Y) (g : Y -> qbs_prob Z)
  (hf_diag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha (qps_repr m) r)) r))
  (hg_bind : forall (p : qbs_prob Y),
    @qbs_Mx R Z
      (fun r => qbs_prob_alpha (g (qbs_prob_alpha p r)) r))
  (hfg_diag : @qbs_Mx R Z
    (fun r => qbs_prob_alpha
      (g (qbs_prob_alpha (f (qbs_prob_alpha (qps_repr m) r)) r)) r)) :
  qps_eq
    (qps_bind (qps_bind m f hf_diag) g (hg_bind _))
    (qps_of (mkQBSProb
      (fun r => qbs_prob_alpha (g (qbs_prob_alpha (f (qbs_prob_alpha (qps_repr m) r)) r)) r)
      (qbs_prob_mu (qps_repr m))
      hfg_diag)).
Proof. exact: qbs_bindA. Qed.

(* ===================================================================== *)
(* 5. Expectation and probability of events on the quotient              *)
(* ===================================================================== *)

Definition qps_expect (X : qbsType R) (p : qbs_prob_space X)
  (h : X -> R) : \bar R :=
  qbs_expect X (qps_repr p) h.

Arguments qps_expect {X}.

Definition qps_prob_event (X : qbsType R) (p : qbs_prob_space X)
  (U : set X) : \bar R :=
  qbs_prob_event X (qps_repr p) U.

Arguments qps_prob_event {X}.

(* Probability of events respects qps_eq for sigma_Mx sets *)
Lemma qps_prob_event_equiv (X : qbsType R) (p1 p2 : qbs_prob_space X)
  (U : set X) :
  @sigma_Mx R X U ->
  qps_eq p1 p2 ->
  qps_prob_event p1 U = qps_prob_event p2 U.
Proof.
move=> hU heq.
rewrite /qps_prob_event /qbs_prob_event.
exact: heq.
Qed.

(* ===================================================================== *)
(* 6. The quotient forms a QBS via monadP                                *)
(*    Since qbs_prob_space X is isomorphic to qbs_prob X as a type,     *)
(*    and monadP X already equips qbs_prob X with a QBS structure,      *)
(*    we transfer the QBS structure to qbs_prob_space X.                *)
(* ===================================================================== *)

Definition qps_Mx (X : qbsType R) : set (mR -> qbs_prob_space X) :=
  [set beta | @monadP_random' R X (fun r => qps_repr (beta r))].

Arguments qps_Mx {X}.

Lemma qps_Mx_comp (X : qbsType R) :
  forall beta f,
    @qps_Mx X beta ->
    measurable_fun setT f ->
    @qps_Mx X (beta \o f).
Proof.
move=> beta f hbeta hf r /=.
exact: hbeta.
Qed.

Lemma qps_Mx_const (X : qbsType R) :
  forall x : qbs_prob_space X, @qps_Mx X (fun _ => x).
Proof.
move=> x r /=.
exact: (qbs_prob_alpha_random (qps_repr x)).
Qed.

Lemma qps_Mx_glue (X : qbsType R) :
  forall (P : mR -> nat) (Fi : nat -> mR -> qbs_prob_space X),
    measurable_fun setT P ->
    (forall i, @qps_Mx X (Fi i)) ->
    @qps_Mx X (fun r => Fi (P r) r).
Proof.
move=> P Fi hP hFi r /=.
exact: hFi.
Qed.

Definition qbs_prob_space_qbs (X : qbsType R) : qbsType R :=
  (* NB: manual HB.pack to equip the quotient wrapper with a QBS structure *)
  HB.pack (qbs_prob_space X)
    (@isQBS.Build R (qbs_prob_space X)
      (@qps_Mx X)
      (@qps_Mx_comp X)
      (@qps_Mx_const X)
      (@qps_Mx_glue X)).

(* ===================================================================== *)
(* 7. Integration on the quotient: linearity properties                  *)
(* ===================================================================== *)

Lemma qps_integral_const (X : qbsType R) (p : qbs_prob_space X) (c : \bar R) :
  qps_integral p (fun _ => c) = (\int[qbs_prob_mu (qps_repr p)]_x c)%E.
Proof. by []. Qed.

Lemma qps_integral_return (X : qbsType R) (x : X)
  (mu : probability mR R) (h : X -> \bar R) :
  qps_integral (qps_return x mu) h = (\int[mu]_r h x)%E.
Proof. by []. Qed.

Lemma qps_integral_bind (X Y : qbsType R) (p : qbs_prob_space X)
  (f : X -> qbs_prob Y)
  (hdiag : @qbs_Mx R Y
    (fun r => qbs_prob_alpha (f (qbs_prob_alpha (qps_repr p) r)) r))
  (h : Y -> \bar R) :
  qps_integral (qps_bind p f hdiag) h =
  (\int[qbs_prob_mu (qps_repr p)]_r
    h (qbs_prob_alpha (f (qbs_prob_alpha (qps_repr p) r)) r))%E.
Proof. by []. Qed.

(* ===================================================================== *)
(* 8. Canonical representative via classical choice                       *)
(*    Given a qbs_prob, we can pick a canonical representative from its  *)
(*    equivalence class using constructive_indefinite_description.        *)
(*    This does NOT give a well-defined function (different inputs in     *)
(*    the same class may get different representatives), but it provides  *)
(*    a representative that IS equivalent to the original.               *)
(* ===================================================================== *)

Definition qps_pick_repr (X : qbsType R) (p : qbs_prob_space X) :
  qbs_prob_space X :=
  QPS (proj1_sig (boolp.constructive_indefinite_description
    (ex_intro (fun q => qbs_prob_equiv X (qps_repr p) q)
      (qps_repr p) (qbs_prob_equivxx (qps_repr p))))).

Lemma qps_pick_repr_equiv (X : qbsType R) (p : qbs_prob_space X) :
  qps_eq p (qps_pick_repr p).
Proof.
rewrite /qps_pick_repr /qps_eq /=.
exact: (proj2_sig (boolp.constructive_indefinite_description _ )).
Qed.

End QBSProbQuot.

Arguments qbs_prob_space {R}.
Arguments QPS {R X}.
Arguments qps_repr {R X}.
Arguments qps_eq {R X}.
Arguments qps_of {R X}.
Arguments qps_return {R X}.
Arguments qps_bind {R X Y}.
Arguments qps_bind_strong {R X Y}.
Arguments qps_integral {R X}.
Arguments qps_map {R X Y}.
Arguments qps_expect {R X}.
Arguments qps_prob_event {R X}.
Arguments qbs_prob_space_qbs {R}.
Arguments qps_pick_repr {R X}.
