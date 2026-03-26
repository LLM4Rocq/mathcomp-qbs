(* -------------------------------------------------------------------- *)
(* Adjunction between Measurable Spaces and Quasi-Borel Spaces          *)
(*                                                                        *)
(* The R functor: Meas -> QBS sends a measurable space to its QBS of     *)
(* measurable functions. The L functor: QBS -> sigma-algebra sends a QBS *)
(* to the sigma-algebra sigma_Mx of sets whose preimages under random    *)
(* elements are measurable. These form an adjunction L -| R.             *)
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

Section MQA.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* Section 1: R functor properties                                       *)
(* R_qbs is defined in quasi_borel.v. Here we show it is functorial.     *)
(* ===================================================================== *)

(* If f is measurable, then f is a QBS morphism between R_qbs spaces *)
Lemma R_qbs_morph (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2)
    (f : M1 -> M2) :
  measurable_fun setT f ->
  @qbs_morph R (@R_qbs R _ M1) (@R_qbs R _ M2) f.
Proof.
move=> hf alpha /= halpha.
exact: measurableT_comp hf halpha.
Qed.

(* R_qbs preserves identity *)
Lemma R_qbs_id (d : measure_display) (M : measurableType d) :
  @qbs_morph R (@R_qbs R _ M) (@R_qbs R _ M) idfun.
Proof. exact: (@qbs_morph_id R). Qed.

(* R_qbs preserves composition *)
Lemma R_qbs_comp (d1 d2 d3 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2)
    (M3 : measurableType d3)
    (f : M1 -> M2) (g : M2 -> M3) :
  measurable_fun setT f ->
  measurable_fun setT g ->
  @qbs_morph R (@R_qbs R _ M1) (@R_qbs R _ M3) (g \o f).
Proof.
move=> hf hg.
apply: (@qbs_morph_comp R (@R_qbs R _ M1) (@R_qbs R _ M2) (@R_qbs R _ M3)).
- exact: R_qbs_morph.
- exact: R_qbs_morph.
Qed.

(* ===================================================================== *)
(* Section 2: L functor (sigma-algebra level)                            *)
(* L sends a QBS to its induced sigma-algebra sigma_Mx.                  *)
(* ===================================================================== *)

(* sigma_Mx is already defined in quasi_borel.v as:
   sigma_Mx X = { U | forall alpha in Mx, alpha^{-1}(U) is measurable } *)

(* sigma_Mx contains the empty set *)
Lemma L_sigma_set0 (X : @qbs R) : @sigma_Mx R X set0.
Proof.
by move=> alpha _; rewrite preimage_set0; exact: measurable0.
Qed.

(* L_sigma collects the sigma-algebra properties *)
Definition L_sigma (X : @qbs R) : set (set (@qbs_car R X)) := @sigma_Mx R X.
Arguments L_sigma : clear implicits.

Lemma L_sigma_measurableT (X : @qbs R) : L_sigma X setT.
Proof. exact: (@sigma_Mx_setT R X). Qed.

Lemma L_sigma_measurableC (X : @qbs R) (U : set (@qbs_car R X)) :
  L_sigma X U -> L_sigma X (~` U).
Proof. exact: (@sigma_Mx_setC R X). Qed.

Lemma L_sigma_measurable_bigcup (X : @qbs R) (F : nat -> set (@qbs_car R X)) :
  (forall i, L_sigma X (F i)) -> L_sigma X (\bigcup_i F i).
Proof. exact: (@sigma_Mx_bigcup R X). Qed.

(* L is functorial: QBS morphisms map to measurable functions *)
Lemma L_qbs_morph (X Y : @qbs R) (f : @qbs_car R X -> @qbs_car R Y) :
  @qbs_morph R X Y f ->
  forall U, L_sigma Y U -> L_sigma X (f @^-1` U).
Proof.
move=> hf U hU alpha halpha.
have hfa : @qbs_random R Y (f \o alpha) by exact: hf.
exact: hU.
Qed.

(* L preserves identity *)
Lemma L_qbs_id (X : @qbs R) (U : set (@qbs_car R X)) :
  L_sigma X U -> L_sigma X (idfun @^-1` U).
Proof. by []. Qed.

(* L preserves composition *)
Lemma L_qbs_comp (X Y Z : @qbs R) (f : @qbs_car R X -> @qbs_car R Y)
    (g : @qbs_car R Y -> @qbs_car R Z) :
  @qbs_morph R X Y f ->
  @qbs_morph R Y Z g ->
  forall U, L_sigma Z U -> L_sigma X ((g \o f) @^-1` U).
Proof.
move=> hf hg U hU alpha halpha.
have hfa : @qbs_random R Y (f \o alpha) by exact: hf.
have hgfa : @qbs_random R Z (g \o (f \o alpha)) by exact: hg.
exact: hU.
Qed.

(* ===================================================================== *)
(* Section 3: Adjunction L -| R                                          *)
(* For a QBS X and measurable space Y:                                   *)
(*   Hom_QBS(X, R(Y)) ~ Hom_Meas(L(X), Y)                             *)
(* ===================================================================== *)

(* Left-to-right: a QBS morphism X -> R(Y) gives a "measurable" map
   w.r.t. L_sigma(X) and sigma(Y) *)
Lemma lr_adj_l2r (X : @qbs R) (d : measure_display)
    (Y : measurableType d) (f : @qbs_car R X -> Y) :
  @qbs_morph R X (@R_qbs R _ Y) f ->
  forall U, measurable U -> L_sigma X (f @^-1` U).
Proof. Admitted.

(* Right-to-left: a "measurable" map w.r.t. L_sigma(X) and sigma(Y)
   gives a QBS morphism X -> R(Y) *)
Lemma lr_adj_r2l (X : @qbs R) (d : measure_display)
    (Y : measurableType d) (f : @qbs_car R X -> Y) :
  (forall U, measurable U -> L_sigma X (f @^-1` U)) ->
  @qbs_morph R X (@R_qbs R _ Y) f.
Proof. Admitted.

(* The two directions are inverse to each other (naturality) *)
Lemma lr_adj_natural (X : @qbs R) (d : measure_display)
    (Y : measurableType d) (f : @qbs_car R X -> Y) :
  (@qbs_morph R X (@R_qbs R _ Y) f) <->
  (forall U, measurable U -> L_sigma X (f @^-1` U)).
Proof.
split.
- exact: lr_adj_l2r.
- exact: lr_adj_r2l.
Qed.

(* ===================================================================== *)
(* Section 4: R preserves products                                       *)
(* R(M1 x M2) has the same random elements as prodQ(R(M1), R(M2))       *)
(* ===================================================================== *)

(* The random elements of R_qbs applied to a product measurable type
   coincide with those of the QBS product of R_qbs spaces *)
Lemma R_preserves_prod (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2)
    (alpha : mR -> M1 * M2) :
  @qbs_random R (@R_qbs R _ [the measurableType _ of (M1 * M2)%type]) alpha <->
  @qbs_random R (@prodQ R (@R_qbs R _ M1) (@R_qbs R _ M2)) alpha.
Proof. Admitted.

(* ===================================================================== *)
(* Section 5: Standard Borel spaces                                      *)
(* A measurable space is standard Borel if it is measurably isomorphic   *)
(* to a measurable subset of R.                                          *)
(* ===================================================================== *)

(* Definition of standard Borel: there exist measurable maps
   witnessing an isomorphism with a measurable subset of R *)
Definition is_standard_borel (d : measure_display) (M : measurableType d) :=
  exists (f : M -> mR) (g : mR -> M),
    measurable_fun setT f /\
    measurable_fun setT g /\
    (forall x, g (f x) = x).

(* R itself is standard Borel (via the identity) *)
Lemma R_standard_borel : is_standard_borel mR.
Proof.
exists idfun, idfun; split; first exact: measurable_id.
split; first exact: measurable_id.
by [].
Qed.

(* On standard Borel spaces, the R functor is fully faithful:
   every QBS morphism R(M1) -> R(M2) arises from a measurable function *)
Lemma R_full_faithful_standard_borel
    (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2) :
  is_standard_borel M1 ->
  is_standard_borel M2 ->
  forall (f : M1 -> M2),
    @qbs_morph R (@R_qbs R _ M1) (@R_qbs R _ M2) f ->
    measurable_fun setT f.
Proof. Admitted.

(* The unit of the adjunction: X -> R(L(X)) at the level of
   the identity function being a QBS morphism into
   the R_qbs of the L_sigma-measurable structure *)
Lemma adjunction_unit (X : @qbs R) (alpha : mR -> @qbs_car R X) :
  @qbs_random R X alpha ->
  forall U, L_sigma X U -> measurable (alpha @^-1` U).
Proof. by move=> halpha U hU; exact: hU. Qed.

(* The counit: L(R(M)) refines sigma(M), i.e., every measurable set
   is in the induced sigma-algebra *)
Lemma adjunction_counit (d : measure_display) (M : measurableType d)
    (U : set M) :
  measurable U -> L_sigma (@R_qbs R _ M) U.
Proof. Admitted.

End MQA.
