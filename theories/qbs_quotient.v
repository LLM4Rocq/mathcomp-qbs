(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals classical_sets boolp
  ereal measurable_structure measurable_function probability_measure
  lebesgue_stieltjes_measure lebesgue_integral.
From QBS Require Import quasi_borel probability_qbs.

(**md**************************************************************************)
(* # Mathcomp Quotient for QBS Probability Spaces                            *)
(*                                                                           *)
(* This file builds a proper quotient type for qbs_prob X using mathcomp's   *)
(* generic_quotient infrastructure (Cyril Cohen, ITP 2013). The quotient     *)
(* identifies probability triples that induce the same pushforward measure   *)
(* (i.e., are related by qbs_prob_equiv).                                    *)
(*                                                                           *)
(* The key ingredient is boolp.asbool, which classically turns the           *)
(* Prop-valued qbs_prob_equiv into a boolean relation suitable for           *)
(* generic_quotient's {eq_quot} construction. The base type qbs_prob X       *)
(* is given eqType and choiceType instances via gen_eqMixin/gen_choiceMixin  *)
(* from mathcomp's classical library.                                        *)
(*                                                                           *)
(* This follows the same pattern as hoelder.v's aeEqMfun quotient of        *)
(* measurable functions by a.e. equality.                                    *)
(*                                                                           *)
(* ```                                                                       *)
(*   qbs_equiv_op X == boolean relation: asbool (qbs_prob_equiv X p1 p2)    *)
(*   qbs_prob_equivRel X == canonical equiv_rel packaging qbs_equiv_op       *)
(*   qbs_quot X      == the quotient type {eq_quot qbs_prob_equivRel X}      *)
(*   \pi             == canonical surjection qbs_prob X -> qbs_quot X        *)
(*   repr            == representative selection qbs_quot X -> qbs_prob X    *)
(*   reprK           == cancel repr \pi                                      *)
(*   qbs_equivP      == reflect (qbs_prob_equiv X p1 p2)                     *)
(*                              (\pi p1 == \pi p2 :> qbs_quot X)            *)
(*   quot_return     == return lifted to the quotient                        *)
(*   quot_bind_strong == bind lifted (strong morphism, no diagonal proof)    *)
(*   quot_integral   == integration on the quotient                          *)
(*   quot_map        == functorial map on the quotient                       *)
(* ```                                                                       *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section qbs_quotient.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

(** * 1. Boolean equivalence relation and choiceType instance                *)

Section equiv_instances.
Variable X : qbsType R.

(** Boolean version of qbs_prob_equiv via classical decidability. *)
Definition qbs_equiv_op : rel (qbs_prob X) :=
  fun p1 p2 => `[< qbs_prob_equiv X p1 p2 >].

Let qbs_equiv_op_refl : reflexive qbs_equiv_op.
Proof. by move=> p; apply/asboolP/qbs_prob_equivxx. Qed.

Let qbs_equiv_op_sym : symmetric qbs_equiv_op.
Proof.
move=> p q; apply/idP/idP => /asboolP h; apply/asboolP/qbs_prob_equivC => //.
Qed.

Let qbs_equiv_op_trans : transitive qbs_equiv_op.
Proof.
move=> q p r /asboolP hpq /asboolP hqr.
by apply/asboolP; exact: (qbs_prob_equiv_trans hpq hqr).
Qed.

(** Canonical equiv_rel structure for generic_quotient. *)
Canonical qbs_prob_equivRel :=
  EquivRel qbs_equiv_op qbs_equiv_op_refl qbs_equiv_op_sym qbs_equiv_op_trans.

(** Classical eqType and choiceType instances on qbs_prob X.
    These are required by generic_quotient's {eq_quot} construction. *)
HB.instance Definition _ := gen_eqMixin (qbs_prob X).
HB.instance Definition _ := gen_choiceMixin (qbs_prob X).

End equiv_instances.

(** * 2. The quotient type                                                   *)

Local Open Scope quotient_scope.

Section quotient_def.
Variable X : qbsType R.

(** The quotient type: qbs_prob X quotiented by pushforward-measure
    equality. Elements of qbs_quot X are equivalence classes of
    probability triples. Equality in qbs_quot X is decidable
    (classically) and corresponds exactly to qbs_prob_equiv. *)
Definition qbs_quot : Type := {eq_quot @qbs_prob_equivRel X}.

(** Recover standard HB instances on the quotient type. *)
HB.instance Definition _ := Choice.on qbs_quot.
HB.instance Definition _ := EqQuotient.on qbs_quot.

(** Reflection between Prop-valued qbs_prob_equiv and equality in the
    quotient. This is the fundamental bridge: two probability triples
    are equivalent iff their images under \pi are equal. *)
Lemma qbs_equivP (p1 p2 : qbs_prob X) :
  reflect (qbs_prob_equiv X p1 p2)
    (@pi_subdef _ qbs_quot p1 == @pi_subdef _ qbs_quot p2).
Proof.
suff -> : (@pi_subdef _ qbs_quot p1 == @pi_subdef _ qbs_quot p2) =
  `[< qbs_prob_equiv X p1 p2 >] by exact: asboolP.
have -> : pi_subdef qbs_quot = (\pi : _ -> qbs_quot)
  by rewrite /pi_subdef unlock.
by rewrite eqquotE.
Qed.

(** Equivalent: iff version for rewriting. *)
Lemma qbs_equivE (p1 p2 : qbs_prob X) :
  (@pi_subdef _ qbs_quot p1 == @pi_subdef _ qbs_quot p2) =
  `[< qbs_prob_equiv X p1 p2 >].
Proof.
have -> : pi_subdef qbs_quot = (\pi : _ -> qbs_quot)
  by rewrite /pi_subdef unlock.
by rewrite eqquotE.
Qed.

(** repr always picks a representative in the same equivalence class. *)
Lemma repr_equiv (q : qbs_quot) :
  qbs_prob_equiv X (repr q) (repr q).
Proof. exact: qbs_prob_equivxx. Qed.

(** \pi composed with repr is the identity (from generic_quotient). *)
Lemma quot_reprK : cancel (repr : qbs_quot -> qbs_prob X)
  (\pi : qbs_prob X -> qbs_quot).
Proof. exact: reprK. Qed.

End quotient_def.

(** * 3. Lifted operations                                                   *)

Section lifted_ops.
Variables (X Y : qbsType R).

(** Local notation for the canonical surjection. *)
Local Notation piX := (@pi_subdef (qbs_prob X) (qbs_quot X)).
Local Notation piY := (@pi_subdef (qbs_prob Y) (qbs_quot Y)).

(** Return lifted to the quotient. *)
Definition quot_return (x : X) (mu : probability mR R) : qbs_quot X :=
  piX (qbs_return X x mu).

(** Integration on the quotient, defined via representative. *)
Definition quot_integral (q : qbs_quot X) (h : X -> \bar R) : \bar R :=
  qbs_integral X (repr q) h.

(** Map lifted to the quotient: given a morphism f : X -> Y, push
    forward the probability. This uses repr on the input and \pi
    on the output. *)
Definition quot_map (f : X -> Y) (hf : qbs_morphism f)
  (q : qbs_quot X) : qbs_quot Y :=
  piY (monadP_map X Y f hf (repr q)).

(** Bind lifted to the quotient (strong morphism version).
    The strong morphism condition ensures diagonal randomness
    without an explicit proof. On the quotient, this is the key
    improvement: we operate on repr and project back via \pi. *)
Definition quot_bind_strong
  (f : X -> qbs_prob Y) (hf : qbs_morphism_strong X Y f)
  (q : qbs_quot X) : qbs_quot Y :=
  piY (qbs_bind_strong X Y (repr q) f hf).

End lifted_ops.

(** * 4. Well-definedness: lifted operations respect the quotient           *)

Section well_defined.
Variables (X Y : qbsType R).

Local Notation piX := (@pi_subdef (qbs_prob X) (qbs_quot X)).
Local Notation piY := (@pi_subdef (qbs_prob Y) (qbs_quot Y)).

(** Return: all returns at the same point are identified in the quotient. *)
Lemma quot_return_equiv (x : X) (mu1 mu2 : probability mR R) :
  quot_return x mu1 = quot_return x mu2 :> qbs_quot X.
Proof.
apply/eqP/qbs_equivP.
exact: qbs_return_equiv.
Qed.

(** Map respects the quotient. *)
Lemma quot_map_proper (f : X -> Y) (hf : qbs_morphism f)
  (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 ->
  piY (monadP_map X Y f hf p1) = piY (monadP_map X Y f hf p2) :> qbs_quot Y.
Proof.
move=> hequiv; apply/eqP/qbs_equivP => U hU /=.
have hpreimg : forall (p : qbs_prob X),
  (f \o qbs_prob_alpha p) @^-1` U = qbs_prob_alpha p @^-1` (f @^-1` U).
  by move=> p.
by rewrite !hpreimg; apply: hequiv; move=> alpha halpha; apply: hU; apply: hf.
Qed.

(** Bind (strong) respects the quotient in its probability argument,
    given a factoring morphism. This is the quotient-level version
    of qbs_bind_strong_equiv_l. *)
Lemma quot_bind_strong_proper
  (f : X -> qbs_prob Y)
  (g : X -> Y) (hg : qbs_morphism g)
  (hf : qbs_morphism_strong X Y f)
  (hfact : forall (p : qbs_prob X) r,
    qbs_prob_alpha (f (qbs_prob_alpha p r)) r = g (qbs_prob_alpha p r))
  (p1 p2 : qbs_prob X)
  (hequiv : qbs_prob_equiv X p1 p2) :
  piY (qbs_bind_strong X Y p1 f hf) =
  piY (qbs_bind_strong X Y p2 f hf) :> qbs_quot Y.
Proof.
apply/eqP/qbs_equivP.
exact: (qbs_bind_strong_equiv_l hg hf (hfact p1) (hfact p2) hequiv).
Qed.

(** Integration respects the quotient for qbs-measurable integrands. *)
Lemma quot_integral_proper (p1 p2 : qbs_prob X)
  (h : X -> \bar R)
  (hm : qbs_measurable X h)
  (hint1 : (qbs_prob_mu p1).-integrable setT
    (h \o qbs_prob_alpha p1))
  (hint2 : (qbs_prob_mu p2).-integrable setT
    (h \o qbs_prob_alpha p2)) :
  qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof. exact: qbs_integral_equiv. Qed.

End well_defined.

(** * 5. Monad laws as equalities in the quotient                           *)

Section monad_laws_quot.
Variables (X Y Z : qbsType R).

Local Notation piX := (@pi_subdef (qbs_prob X) (qbs_quot X)).
Local Notation piY := (@pi_subdef (qbs_prob Y) (qbs_quot Y)).

(** Left unit: bind (return x) f ~ f x, as an equality in the quotient.
    We state this at the level of piY applied to qbs_bind_strong, not
    through quot_bind_strong (which goes via repr, losing the definitional
    structure of the return). *)
Lemma quot_bind_returnl (x : X)
  (f : X -> qbs_prob Y)
  (hf_morph : qbs_morphism f)
  (hf_strong : qbs_morphism_strong X Y f) :
  piY (qbs_bind_strong X Y (qbs_return X x (qbs_prob_mu (f x))) f hf_strong) =
  piY (f x) :> qbs_quot Y.
Proof.
apply/eqP/qbs_equivP.
exact: qbs_bind_returnl.
Qed.

(** Right unit: bind m return ~ m, as an equality in the quotient. *)
Lemma quot_bind_returnr (m : qbs_prob X) (mu : probability mR R) :
  @pi_subdef _ (qbs_quot X)
    (qbs_bind X X m (qbs_return X ^~ mu)
      (qbs_bind_alpha_random_return m mu)) =
  @pi_subdef _ (qbs_quot X) m.
Proof.
apply/eqP/qbs_equivP.
exact: qbs_bind_returnr.
Qed.

End monad_laws_quot.

(** * 6. Comparison with the setoid-style quotient in qbs_prob_quot.v       *)
(*                                                                           *)
(* The existing qbs_prob_quot.v defines qbs_prob_space X as a record         *)
(* wrapping qbs_prob X, with qps_eq as a Prop-valued equivalence.           *)
(* The present file uses mathcomp's generic_quotient.v instead, yielding:    *)
(*                                                                           *)
(* - Decidable equality: qbs_quot X has eqType and choiceType instances.     *)
(*   Equivalence classes can be compared with ==.                            *)
(* - reprK: the canonical surjection and representative selection satisfy    *)
(*   cancel repr \pi, which is a stronger property than what                 *)
(*   qps_pick_repr provides.                                                 *)
(* - Integration with mathcomp: the quotient type plugs into the broader    *)
(*   mathcomp infrastructure (sets, topology, etc.) because it is a          *)
(*   proper eqType/choiceType.                                               *)
(*                                                                           *)
(* The cost is that gen_eqMixin/gen_choiceMixin use classical axioms         *)
(* (excluded middle) to define equality. This is consistent with the         *)
(* classical setting of mathcomp-analysis.                                   *)
(*                                                                           *)
(* Note: both approaches still require the strong morphism condition (or     *)
(* a factoring hypothesis through a morphism g) for bind congruence.         *)
(* The quotient does NOT eliminate this requirement. It eliminates the        *)
(* need for the diagonal randomness proof in qbs_bind: on the quotient,     *)
(* we always have a concrete representative via repr, so                     *)
(* qbs_bind_alpha_random_strong provides the diagonal automatically.         *)

End qbs_quotient.

Arguments qbs_equiv_op {R X}.
Arguments qbs_prob_equivRel {R}.
Arguments qbs_quot {R}.
Arguments qbs_equivP {R X}.
Arguments qbs_equivE {R X}.
Arguments quot_return {R X}.
Arguments quot_integral {R X}.
Arguments quot_map {R X Y}.
Arguments quot_bind_strong {R X Y}.
Arguments quot_return_equiv {R X}.
Arguments quot_bind_returnl {R X Y}.
