(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals classical_sets boolp
  ereal measurable_structure measurable_function probability_measure
  lebesgue_stieltjes_measure lebesgue_integral.
From QBS Require Import quasi_borel probability_qbs qbs_monad.

(**md**************************************************************************)
(* # Quotient of QBS probabilities by equivalence                             *)
(*                                                                            *)
(* qbs_prob X is quotiented by qbs_prob_equiv (same measure on every          *)
(* sigma_Mx set) with mathcomp's generic_quotient, following the a.e.         *)
(* equality quotient of hoelder.v. On the quotient the monad laws hold as     *)
(* equalities.                                                                *)
(*                                                                            *)
(* ```                                                                        *)
(*      qbs_equiv_op X == boolean version of qbs_prob_equiv X                 *)
(*         qbs_quot X == {eq_quot qbs_equiv_op}, the quotient type            *)
(*      quot_return x == \pi (qbs_return x)                                   *)
(*      quot_bind q f == \pi (qbs_bind (repr q) f)                            *)
(*       quot_map f q == \pi (monadP_map f (repr q))                          *)
(* quot_integral q h == qbs_integral X (repr q) h                             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope quotient_scope.

Section qbs_quotient.
Variable R : realType.
Implicit Types (X Y Z : qbsType R).

Section equiv_instances.
Variable X : qbsType R.

Definition qbs_equiv_op : rel (qbs_prob X) :=
  fun p1 p2 => `[< qbs_prob_equiv X p1 p2 >].

Let qbs_equiv_op_refl : reflexive qbs_equiv_op.
Proof. by move=> p; exact/asboolP/qbs_prob_equivxx. Qed.

Let qbs_equiv_op_sym : symmetric qbs_equiv_op.
Proof.
by move=> p q; apply/idP/idP => /asboolP h; exact/asboolP/qbs_prob_equivC.
Qed.

Let qbs_equiv_op_trans : transitive qbs_equiv_op.
Proof.
move=> q p r /asboolP hpq /asboolP hqr.
exact/asboolP/(qbs_prob_equiv_trans hpq hqr).
Qed.

Canonical qbs_prob_equiv_canonical :=
  EquivRel qbs_equiv_op qbs_equiv_op_refl qbs_equiv_op_sym qbs_equiv_op_trans.

HB.instance Definition _ := gen_eqMixin (qbs_prob X).
HB.instance Definition _ := gen_choiceMixin (qbs_prob X).

Definition qbs_quot : Type := {eq_quot qbs_prob_equiv_canonical}.

HB.instance Definition _ := Choice.on qbs_quot.
HB.instance Definition _ := EqQuotient.on qbs_quot.

Lemma qbs_prob_equivP (p1 p2 : qbs_prob X) :
  reflect (qbs_prob_equiv X p1 p2) (p1 == p2 %[mod qbs_quot]).
Proof. by rewrite eqquotE; exact: asboolP. Qed.

Lemma qbs_quot_eqP (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 -> \pi_qbs_quot p1 = \pi_qbs_quot p2.
Proof.
by move=> e; apply/eqmodP; exact/asboolP.
Qed.

Lemma qbs_prob_equiv_repr (p : qbs_prob X) :
  qbs_prob_equiv X (repr (\pi_qbs_quot p)) p.
Proof. by apply/qbs_prob_equivP; rewrite reprK. Qed.

End equiv_instances.

Arguments qbs_quot : clear implicits.

Section lifted_ops.
Variables (X Y : qbsType R).

Definition quot_return (x : X) : qbs_quot X := \pi_(qbs_quot X) (qbs_return x : qbs_prob X).

Definition quot_bind (q : qbs_quot X) (f : qbsHomType X (monadP Y)) :
  qbs_quot Y := \pi_(qbs_quot Y) (qbs_bind (repr q) f : qbs_prob Y).

Definition quot_map (f : qbsHomType X Y) (q : qbs_quot X) : qbs_quot Y :=
  \pi_(qbs_quot Y) (monadP_map f (repr q) : qbs_prob Y).

Definition quot_integral (q : qbs_quot X) (h : X -> \bar R) : \bar R :=
  qbs_integral X (repr q) h.

Lemma quot_bindE (p : qbs_prob X) (f : qbsHomType X (monadP Y)) :
  quot_bind (\pi_(qbs_quot X) p) f = \pi_(qbs_quot Y) (qbs_bind p f : qbs_prob Y).
Proof. exact/qbs_quot_eqP/qbs_bind_equiv_l/qbs_prob_equiv_repr. Qed.

Lemma quot_mapE (f : qbsHomType X Y) (p : qbs_prob X) :
  quot_map f (\pi_(qbs_quot X) p) = \pi_(qbs_quot Y) (monadP_map f p : qbs_prob Y).
Proof. exact/qbs_quot_eqP/monadP_map_equiv/qbs_prob_equiv_repr. Qed.

Lemma ge0_quot_integralE (p : qbs_prob X) (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, (0 <= h x)%E) ->
  quot_integral (\pi_(qbs_quot X) p) h = qbs_integral X p h.
Proof.
move=> mh h0; apply: ge0_qbs_integral_equiv => //.
exact: qbs_prob_equiv_repr.
Qed.

End lifted_ops.

Section monad_laws.

Lemma quot_bind_returnl X Y (x : X) (f : qbsHomType X (monadP Y)) :
  quot_bind (quot_return x) f = \pi_(qbs_quot Y) (f x : qbs_prob Y).
Proof.
by rewrite /quot_return quot_bindE; exact/qbs_quot_eqP/qbs_bind_returnl.
Qed.

Lemma quot_bind_returnr X (q : qbs_quot X) : quot_bind q (qbs_returnQ X) = q.
Proof.
by rewrite -[RHS]reprK /quot_bind; exact/qbs_quot_eqP/qbs_bind_returnr.
Qed.

Lemma quot_bindA X Y Z (q : qbs_quot X) (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) :
  quot_bind (quot_bind q f) g = quot_bind q (qbs_bindQ f g).
Proof.
rewrite [quot_bind q f]/quot_bind quot_bindE /quot_bind.
exact/qbs_quot_eqP/qbs_bindA.
Qed.

Lemma quot_map_id X (q : qbs_quot X) : quot_map (qbs_id X) q = q.
Proof. by rewrite /quot_map monadP_map_id reprK. Qed.

Lemma quot_map_comp X Y Z (f : qbsHomType X Y) (g : qbsHomType Y Z)
    (q : qbs_quot X) :
  quot_map (qbs_comp f g) q = quot_map g (quot_map f q).
Proof.
by rewrite [quot_map f q]/quot_map quot_mapE /quot_map monadP_map_comp.
Qed.

End monad_laws.

End qbs_quotient.
