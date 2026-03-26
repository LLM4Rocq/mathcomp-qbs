(* -------------------------------------------------------------------- *)
(* Quasi-Borel Spaces                                                    *)
(*                                                                        *)
(* Formalization following:                                               *)
(* - "A Convenient Category for Higher-Order Probability Theory"          *)
(*   Heunen, Kammar, Staton, Yang (LICS 2017)                           *)
(* - Isabelle AFP: Quasi_Borel_Spaces by Hirata, Minamide, Sato          *)
(*                                                                        *)
(* Built on math-comp analysis (measurable types, measures, kernels)      *)
(* -------------------------------------------------------------------- *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import all_analysis.

Import Num.Def Num.Theory reals classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(* ===================================================================== *)
(* Core Definitions                                                       *)
(* A quasi-Borel space on a type T is a set Mx of "random elements"      *)
(* (functions R -> T) satisfying three closure axioms.                    *)
(* ===================================================================== *)

Section QBS.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ----- 1. Core Record ----- *)

Record qbs := mkQBS {
  qbs_car :> Type ;
  qbs_random : set (mR -> qbs_car) ;
  qbs_random_comp : forall alpha f,
    qbs_random alpha ->
    measurable_fun setT f ->
    qbs_random (alpha \o f) ;
  qbs_random_const : forall x, qbs_random (fun _ => x) ;
  qbs_random_glue : forall (P : mR -> nat) (Fi : nat -> mR -> qbs_car),
    measurable_fun setT P ->
    (forall i, qbs_random (Fi i)) ->
    qbs_random (fun r => Fi (P r) r) ;
}.

Arguments qbs_random : clear implicits.
Arguments qbs_car : clear implicits.

(* ----- 2. Morphisms ----- *)

Definition qbs_morph (X Y : qbs) (f : qbs_car X -> qbs_car Y) : Prop :=
  forall alpha, qbs_random X alpha -> qbs_random Y (f \o alpha).

Arguments qbs_morph : clear implicits.

Lemma qbs_morph_id (X : qbs) : qbs_morph X X idfun.
Proof. by move=> alpha hα. Qed.

Lemma qbs_morph_comp (X Y Z : qbs) (f : X -> Y) (g : Y -> Z) :
  qbs_morph X Y f -> qbs_morph Y Z g -> qbs_morph X Z (g \o f).
Proof. by move=> hf hg alpha hα; apply: hg; apply: hf. Qed.

Lemma qbs_morph_const (X Y : qbs) (y : Y) :
  qbs_morph X Y (fun _ => y).
Proof. by move=> alpha _; apply: qbs_random_const. Qed.

(* ----- 3. Bundled Morphism ----- *)

Record qbs_hom (X Y : qbs) := QBSHom {
  qbs_hom_val :> X -> Y ;
  qbs_hom_proof : qbs_morph X Y qbs_hom_val ;
}.

Arguments qbs_hom_val {X Y}.
Arguments qbs_hom_proof {X Y}.

(* ----- 4. The R functor: measurableType -> qbs ----- *)

Lemma measurable_glue (d : measure_display) (M : measurableType d)
  (P : mR -> nat) (Fi : nat -> mR -> M) :
  measurable_fun setT P ->
  (forall i, measurable_fun setT (Fi i)) ->
  measurable_fun setT (fun r => Fi (P r) r).
Proof.
move=> hP hFi _ U mU; rewrite setTI.
have -> : (fun r => Fi (P r) r) @^-1` U =
          \bigcup_i (P @^-1` [set i] `&` (Fi i) @^-1` U).
  rewrite eqEsubset; split => [r hUr | r [i _ [hPi hFir]]].
  - exists (P r) => //; split => //.
  - rewrite /preimage /=; rewrite /preimage /= in hPi; rewrite hPi; exact: hFir.
apply: bigcupT_measurable => i; apply: measurableI.
- have := hP measurableT [set i] I; rewrite setTI; exact.
- have := hFi i measurableT U mU; rewrite setTI; exact.
Qed.

Definition R_qbs (d : measure_display) (M : measurableType d) : qbs :=
  @mkQBS M
    [set f : mR -> M | measurable_fun setT f]
    (fun alpha f (ha : measurable_fun setT alpha) hf =>
       measurableT_comp ha hf)
    (fun x => @measurable_cst _ _ mR M setT x)
    (fun P Fi hP hFi => @measurable_glue d M P Fi hP hFi).

Definition realQ : qbs := R_qbs mR.
Definition natQ : qbs := R_qbs nat.
Definition boolQ : qbs := R_qbs bool.

(* ----- 5. Binary Product ----- *)

Lemma prodQ_closed1 (X Y : qbs) :
  forall alpha f,
    (qbs_random X (fst \o alpha) /\ qbs_random Y (snd \o alpha)) ->
    measurable_fun setT f ->
    (qbs_random X (fst \o (alpha \o f)) /\ qbs_random Y (snd \o (alpha \o f))).
Proof.
move=> alpha f [h1 h2] hf; split.
- have -> : fst \o (alpha \o f) = (fst \o alpha) \o f by [].
  exact: qbs_random_comp h1 hf.
- have -> : snd \o (alpha \o f) = (snd \o alpha) \o f by [].
  exact: qbs_random_comp h2 hf.
Qed.

Lemma prodQ_closed2 (X Y : qbs) :
  forall xy : X * Y,
    qbs_random X (fst \o (fun _ : mR => xy)) /\
    qbs_random Y (snd \o (fun _ : mR => xy)).
Proof.
move=> [x y]; split.
- have -> : fst \o (fun _ : mR => (x, y)) = (fun _ => x) by [].
  exact: qbs_random_const.
- have -> : snd \o (fun _ : mR => (x, y)) = (fun _ => y) by [].
  exact: qbs_random_const.
Qed.

Lemma prodQ_closed3 (X Y : qbs) :
  forall (P : mR -> nat)
         (Fi : nat -> mR -> X * Y),
    measurable_fun setT P ->
    (forall i, qbs_random X (fst \o Fi i) /\ qbs_random Y (snd \o Fi i)) ->
    qbs_random X (fst \o (fun r => Fi (P r) r)) /\
    qbs_random Y (snd \o (fun r => Fi (P r) r)).
Proof.
move=> P Fi hP hFi; split.
- have -> : fst \o (fun r => Fi (P r) r) =
            (fun r => (fun i => fst \o Fi i) (P r) r) by [].
  apply: (@qbs_random_glue X P (fun i => fst \o Fi i)) => // i.
  by have [] := hFi i.
- have -> : snd \o (fun r => Fi (P r) r) =
            (fun r => (fun i => snd \o Fi i) (P r) r) by [].
  apply: (@qbs_random_glue Y P (fun i => snd \o Fi i)) => // i.
  by have [] := hFi i.
Qed.

Definition prodQ (X Y : qbs) : qbs :=
  @mkQBS (X * Y)
    [set f | qbs_random X (fst \o f) /\ qbs_random Y (snd \o f)]
    (@prodQ_closed1 X Y)
    (@prodQ_closed2 X Y)
    (@prodQ_closed3 X Y).

Arguments prodQ : clear implicits.

Lemma qbs_morph_fst (X Y : qbs) : qbs_morph (prodQ X Y) X fst.
Proof. by move=> alpha [h1 h2]. Qed.

Lemma qbs_morph_snd (X Y : qbs) : qbs_morph (prodQ X Y) Y snd.
Proof. by move=> alpha [h1 h2]. Qed.

Lemma qbs_morph_pair (W X Y : qbs) (f : W -> X) (g : W -> Y) :
  qbs_morph W X f -> qbs_morph W Y g ->
  qbs_morph W (prodQ X Y) (fun w => (f w, g w)).
Proof.
by move=> hf hg alpha hα; split; [apply: hf | apply: hg].
Qed.

(* ----- 6. Exponential (Function Space) ----- *)

(* The carrier of expQ X Y is qbs_hom X Y (bundled morphisms).
   The random elements are those g : mR -> qbs_hom X Y such that
   the uncurried map (r, x) |-> g(r)(x) is a morphism prodQ realQ X -> Y. *)

Lemma expQ_closed1 (X Y : qbs) :
  forall alpha f,
    (qbs_morph (prodQ realQ X) Y
       (fun p : realQ * X => qbs_hom_val (alpha p.1) p.2)) ->
    measurable_fun setT f ->
    qbs_morph (prodQ realQ X) Y
      (fun p : realQ * X => qbs_hom_val ((alpha \o f) p.1) p.2).
Proof.
move=> alpha f halpha hf beta [hb1 hb2].
have -> : (fun p : realQ * X => (alpha \o f) p.1 p.2) \o beta =
          (fun p : realQ * X => alpha p.1 p.2) \o
            (fun r => (f (fst (beta r)), snd (beta r))) by [].
apply: halpha; split => /=.
- have -> : fst \o (fun r : mR => (f (beta r).1, (beta r).2)) =
            f \o (fst \o beta) by [].
  exact: measurableT_comp hf hb1.
- have -> : snd \o (fun r : mR => (f (beta r).1, (beta r).2)) =
            snd \o beta by [].
  exact: hb2.
Qed.

Lemma expQ_closed2 (X Y : qbs) :
  forall g : qbs_hom X Y,
    qbs_morph (prodQ realQ X) Y
      (fun p : realQ * X => qbs_hom_val ((fun _ : mR => g) p.1) p.2).
Proof.
move=> g beta [hb1 hb2].
have -> : (fun p : realQ * X => qbs_hom_val g p.2) \o beta =
          qbs_hom_val g \o (snd \o beta) by [].
exact: (qbs_hom_proof g) _ hb2.
Qed.

Lemma expQ_closed3 (X Y : qbs) :
  forall (P : mR -> nat) (Fi : nat -> mR -> qbs_hom X Y),
    measurable_fun setT P ->
    (forall i, qbs_morph (prodQ realQ X) Y
       (fun p : realQ * X => qbs_hom_val (Fi i p.1) p.2)) ->
    qbs_morph (prodQ realQ X) Y
      (fun p : realQ * X => qbs_hom_val ((fun r => Fi (P r) r) p.1) p.2).
Proof.
move=> P Fi hP hFi beta [hb1 hb2].
set Q := (fun r => P (fst (beta r))).
have hQ : measurable_fun setT Q.
  rewrite /Q; apply: measurableT_comp hP _; exact: hb1.
have -> : (fun p : realQ * X => Fi (P p.1) p.1 p.2) \o beta =
          (fun r => (fun i => (fun p : realQ * X => Fi i p.1 p.2) \o beta)
            (Q r) r) by [].
apply: (@qbs_random_glue Y Q
  (fun i => (fun p : realQ * X => Fi i p.1 p.2) \o beta) hQ).
move=> i; exact: hFi i _ (conj hb1 hb2).
Qed.

Definition expQ (X Y : qbs) : qbs :=
  @mkQBS (qbs_hom X Y)
    [set g : mR -> qbs_hom X Y |
      qbs_morph (prodQ realQ X) Y
        (fun p : realQ * X => qbs_hom_val (g p.1) p.2)]
    (@expQ_closed1 X Y)
    (@expQ_closed2 X Y)
    (@expQ_closed3 X Y).

Arguments expQ : clear implicits.

(* ----- 7. Key Theorems: Cartesian Closure ----- *)

(* Evaluation morphism: (expQ X Y) x X -> Y *)
Lemma qbs_eval_morph (X Y : qbs) :
  qbs_morph (prodQ (expQ X Y) X) Y (fun p => qbs_hom_val p.1 p.2).
Proof.
move=> beta [hb1 hb2].
have hmorph : qbs_morph (prodQ realQ X) Y
    (fun p : realQ * X => qbs_hom_val ((fst \o beta) p.1) p.2).
  exact: hb1.
set gamma := (fun r : mR => (r, snd (beta r))) : mR -> realQ * X.
have hgamma : qbs_random (prodQ realQ X) gamma.
  split => /=.
  - have -> : fst \o gamma = idfun by [].
    exact: measurable_id.
  - have -> : snd \o gamma = snd \o beta by [].
    exact: hb2.
have := hmorph gamma hgamma.
have -> : (fun p : realQ * X => (fst \o beta) p.1 p.2) \o gamma =
          (fun r => (fst (beta r)) (snd (beta r))) by [].
by [].
Qed.

(* Helper: constant paired with random element is random in product *)
Lemma prodQ_const_random (X Y : qbs) (x : X) (alpha : mR -> Y) :
  qbs_random Y alpha -> qbs_random (prodQ X Y) (fun r => (x, alpha r)).
Proof.
move=> hα; split => /=.
- have -> : fst \o (fun r : mR => (x, alpha r)) = (fun _ => x) by [].
  exact: qbs_random_const.
- have -> : snd \o (fun r : mR => (x, alpha r)) = alpha by [].
  exact: hα.
Qed.

(* Curry morphism: if f : prodQ X Y -> Z is morph, then curry(f) : X -> expQ Y Z *)
Lemma qbs_curry_morph (X Y Z : qbs)
  (f : qbs_hom (prodQ X Y) Z) :
  qbs_morph X (expQ Y Z)
    (fun x => @QBSHom Y Z (fun y => f (x, y))
       (fun alpha hα => qbs_hom_proof f _
          (prodQ_const_random x hα))).
Proof.
move=> beta hbeta /= gamma [hg1 hg2].
apply: (qbs_hom_proof f); split => /=.
- have -> : fst \o (fun x : mR => (beta (gamma x).1, (gamma x).2)) =
            beta \o (fst \o gamma) by [].
  exact: qbs_random_comp hbeta hg1.
- have -> : snd \o (fun x : mR => (beta (gamma x).1, (gamma x).2)) =
            snd \o gamma by [].
  exact: hg2.
Qed.

(* ----- 8. Unit QBS ----- *)

Definition unitQ : qbs :=
  @mkQBS unit
    [set _ : mR -> unit | True]
    (fun _ _ _ _ => I)
    (fun _ => I)
    (fun _ _ _ _ => I).

(* Unit is terminal: unique morphism to unit *)
Lemma qbs_morph_unit (X : qbs) :
  qbs_morph X unitQ (fun _ => tt).
Proof. by move=> alpha _. Qed.

(* ----- 9. sigma_Mx: the induced sigma-algebra ----- *)

Definition sigma_Mx (X : qbs) : set (set X) :=
  [set U | forall alpha, qbs_random X alpha ->
    measurable (alpha @^-1` U)].

Arguments sigma_Mx : clear implicits.

Lemma sigma_Mx_setT (X : qbs) : sigma_Mx X setT.
Proof. by move=> alpha _; exact: measurableT. Qed.

Lemma sigma_Mx_setC (X : qbs) (U : set X) :
  sigma_Mx X U -> sigma_Mx X (~` U).
Proof.
move=> hU alpha halpha.
rewrite preimage_setC.
exact: measurableC (hU _ halpha).
Qed.

Lemma sigma_Mx_bigcup (X : qbs) (F : nat -> set X) :
  (forall i, sigma_Mx X (F i)) ->
  sigma_Mx X (\bigcup_i F i).
Proof.
move=> hF alpha halpha.
rewrite preimage_bigcup.
exact: bigcup_measurable (fun i _ => hF i _ halpha).
Qed.

(* ----- 10. Comparison Morphisms ----- *)
(* Standard operations on R, nat, bool that are measurable are automatically
   QBS morphisms, since R_qbs sends measurable functions to morphisms. *)

(* Addition is a QBS morphism prodQ realQ realQ -> realQ *)
Lemma qbs_morph_add :
  qbs_morph (prodQ realQ realQ) realQ (fun p => (p.1 + p.2)%R).
Proof.
move=> alpha [h1 h2] /=; exact: measurable_funD h1 h2.
Qed.

(* Multiplication is a QBS morphism prodQ realQ realQ -> realQ *)
Lemma qbs_morph_mul :
  qbs_morph (prodQ realQ realQ) realQ (fun p => (p.1 * p.2)%R).
Proof.
move=> alpha [h1 h2] /=; exact: measurable_funM h1 h2.
Qed.

(* Less-than comparison: realQ x realQ -> boolQ *)
Lemma qbs_morph_ltr :
  qbs_morph (prodQ realQ realQ) boolQ (fun p => (p.1 < p.2)%R).
Proof.
move=> alpha [h1 h2] /=; exact: measurable_fun_ltr h1 h2.
Qed.

(* Negation on bool *)
Lemma qbs_morph_negb :
  qbs_morph boolQ boolQ negb.
Proof.
move=> alpha ha /=; exact: measurable_neg ha.
Qed.

End QBS.
