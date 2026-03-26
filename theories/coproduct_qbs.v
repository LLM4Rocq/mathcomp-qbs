(* -------------------------------------------------------------------- *)
(* Coproducts for Quasi-Borel Spaces                                     *)
(*                                                                        *)
(* Binary coproducts (sum types) and general coproducts (sigma types)     *)
(* following the Isabelle AFP development by Hirata, Minamide, Sato.      *)
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

Section CoProductQBS.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ===================================================================== *)
(* 1. Binary Coproduct                                                    *)
(*                                                                        *)
(* For QBS X and Y, the coproduct X + Y has carrier (X + Y) (Coq sum).   *)
(* A function f : mR -> X + Y is a random element iff it factors through  *)
(* inl, through inr, or is a measurable gluing of an inl-part and an     *)
(* inr-part via a measurable boolean predicate.                           *)
(* ===================================================================== *)

Definition coprodQ_random (X Y : @qbs R) : set (mR -> @qbs_car R X + @qbs_car R Y) :=
  [set f |
    (exists a : mR -> @qbs_car R X,
      @qbs_random R X a /\ forall r, f r = inl (a r))
    \/
    (exists b : mR -> @qbs_car R Y,
      @qbs_random R Y b /\ forall r, f r = inr (b r))
    \/
    (exists (P : mR -> bool) (a : mR -> @qbs_car R X) (b : mR -> @qbs_car R Y),
      measurable_fun setT P /\
      @qbs_random R X a /\
      @qbs_random R Y b /\
      forall r, f r = if P r then inl (a r) else inr (b r))].

Arguments coprodQ_random : clear implicits.

Lemma coprodQ_closed1 (X Y : @qbs R) :
  forall (h : mR -> @qbs_car R X + @qbs_car R Y) (f : mR -> mR),
    coprodQ_random X Y h ->
    measurable_fun setT f ->
    coprodQ_random X Y (h \o f).
Proof.
move=> h f Hh hf.
case: Hh => [[a [ha hdef]] | [[b' [hb hdef]] | [P [a [b' [hP [ha [hb hdef]]]]]]]].
- left; exists (a \o f); split.
  + exact: qbs_random_comp ha hf.
  + by move=> r; rewrite /= hdef.
- right; left; exists (b' \o f); split.
  + exact: qbs_random_comp hb hf.
  + by move=> r; rewrite /= hdef.
- right; right; exists (P \o f), (a \o f), (b' \o f); split; [|split; [|split]].
  + exact: measurableT_comp hP hf.
  + exact: qbs_random_comp ha hf.
  + exact: qbs_random_comp hb hf.
  + by move=> r; rewrite /= hdef.
Qed.

Lemma coprodQ_closed2 (X Y : @qbs R) :
  forall x : @qbs_car R X + @qbs_car R Y,
    coprodQ_random X Y (fun _ => x).
Proof.
case=> [xl | yr].
- left; exists (fun _ => xl); split.
  + exact: qbs_random_const.
  + by [].
- right; left; exists (fun _ => yr); split.
  + exact: qbs_random_const.
  + by [].
Qed.

Lemma coprodQ_closed3 (X Y : @qbs R) :
  forall (Q : mR -> nat) (Fi : nat -> mR -> @qbs_car R X + @qbs_car R Y),
    measurable_fun setT Q ->
    (forall i, coprodQ_random X Y (Fi i)) ->
    coprodQ_random X Y (fun r => Fi (Q r) r).
Proof. Admitted.

Definition coprodQ (X Y : @qbs R) : @qbs R :=
  @mkQBS R (@qbs_car R X + @qbs_car R Y)
    (coprodQ_random X Y)
    (coprodQ_closed1 (X:=X) (Y:=Y))
    (coprodQ_closed2 (X:=X) (Y:=Y))
    (coprodQ_closed3 (X:=X) (Y:=Y)).

Arguments coprodQ : clear implicits.

(* ===================================================================== *)
(* 2. Injection Morphisms                                                 *)
(* ===================================================================== *)

Lemma qbs_morph_inl (X Y : @qbs R) :
  @qbs_morph R X (coprodQ X Y) (@inl (@qbs_car R X) (@qbs_car R Y)).
Proof.
move=> h ha /=.
left; exists h; split => //.
Qed.

Lemma qbs_morph_inr (X Y : @qbs R) :
  @qbs_morph R Y (coprodQ X Y) (@inr (@qbs_car R X) (@qbs_car R Y)).
Proof.
move=> h hb /=.
right; left; exists h; split => //.
Qed.

(* ===================================================================== *)
(* 3. Case Analysis Morphism                                              *)
(*                                                                        *)
(* If f : X -> Z and g : Y -> Z are morphisms, then                      *)
(* case analysis : coprodQ X Y -> Z is a morphism.                       *)
(* ===================================================================== *)

Lemma qbs_morph_case (X Y Z : @qbs R)
  (f : @qbs_car R X -> @qbs_car R Z) (g : @qbs_car R Y -> @qbs_car R Z) :
  @qbs_morph R X Z f ->
  @qbs_morph R Y Z g ->
  @qbs_morph R (coprodQ X Y) Z
    (fun s => match s with inl x => f x | inr y => g y end).
Proof.
move=> hf hg gamma.
case=> [[a [ha hdef]] | [[b' [hb hdef]] | [P [a [b' [hP [ha [hb hdef]]]]]]]].
- (* gamma factors through inl *)
  have heq : (fun s => match s with inl x => f x | inr y => g y end) \o gamma =
              f \o a.
  { rewrite boolp.funeqE => r; rewrite /= hdef //. }
  by rewrite heq; exact: hf _ ha.
- (* gamma factors through inr *)
  have heq : (fun s => match s with inl x => f x | inr y => g y end) \o gamma =
              g \o b'.
  { rewrite boolp.funeqE => r; rewrite /= hdef //. }
  by rewrite heq; exact: hg _ hb.
- (* gamma is a measurable gluing: use qbs_random_glue *)
  have heq : (fun s => match s with inl x => f x | inr y => g y end) \o gamma =
              fun r => if P r then f (a r) else g (b' r).
  { rewrite boolp.funeqE => r; rewrite /= hdef; by case: (P r). }
  rewrite heq.
  set Pn : mR -> nat := fun r => if P r then 0 else 1.
  set Gi : nat -> mR -> @qbs_car R Z :=
    fun i => if i == 0 then f \o a else g \o b'.
  have heq2 : (fun r => if P r then f (a r) else g (b' r)) =
               (fun r => Gi (Pn r) r).
  { rewrite boolp.funeqE => r; rewrite /Gi /Pn.
    by case: (P r). }
  rewrite heq2.
  apply: (@qbs_random_glue R Z Pn Gi).
    rewrite /Pn; apply: measurable_fun_ifT => //; exact: measurable_cst.
  move=> i; rewrite /Gi.
  by case: (i == 0); [exact: hf _ ha | exact: hg _ hb].
Qed.

(* ===================================================================== *)
(* 4. General Coproduct (Sigma Type)                                      *)
(*                                                                        *)
(* For a family X : I -> qbs R, the general coproduct has carrier         *)
(* {i : I & qbs_car (X i)} (dependent sum / sigma type).                 *)
(* A random element f selects an index via P : mR -> I and then a        *)
(* random element in the corresponding fiber.                             *)
(* ===================================================================== *)

Definition gen_coprodQ_random (I : Type) (X : I -> @qbs R) :
  set (mR -> {i : I & @qbs_car R (X i)}) :=
  [set f | exists (P : mR -> I) (Fi : forall i, mR -> @qbs_car R (X i)),
    (forall i, @qbs_random R (X i) (Fi i)) /\
    (forall r, f r = existT _ (P r) (Fi (P r) r))].

Arguments gen_coprodQ_random : clear implicits.

Lemma gen_coprodQ_closed1 (I : Type) (X : I -> @qbs R) :
  forall (h : mR -> {i : I & @qbs_car R (X i)}) (f : mR -> mR),
    gen_coprodQ_random I X h ->
    measurable_fun setT f ->
    gen_coprodQ_random I X (h \o f).
Proof. Admitted.

Lemma gen_coprodQ_closed2 (I : Type) (X : I -> @qbs R) :
  forall x : {i : I & @qbs_car R (X i)},
    gen_coprodQ_random I X (fun _ => x).
Proof. Admitted.

Lemma gen_coprodQ_closed3 (I : Type) (X : I -> @qbs R) :
  forall (Q : mR -> nat) (Fi : nat -> mR -> {i : I & @qbs_car R (X i)}),
    measurable_fun setT Q ->
    (forall i, gen_coprodQ_random I X (Fi i)) ->
    gen_coprodQ_random I X (fun r => Fi (Q r) r).
Proof. Admitted.

Definition gen_coprodQ (I : Type) (X : I -> @qbs R) : @qbs R :=
  @mkQBS R {i : I & @qbs_car R (X i)}
    (gen_coprodQ_random I X)
    (gen_coprodQ_closed1 (X:=X))
    (gen_coprodQ_closed2 (X:=X))
    (gen_coprodQ_closed3 (X:=X)).

Arguments gen_coprodQ : clear implicits.

(* Injection into general coproduct *)
Lemma qbs_morph_gen_inj (I : Type) (X : I -> @qbs R) (i : I) :
  @qbs_morph R (X i) (gen_coprodQ I X) (fun x => existT _ i x).
Proof. Admitted.

End CoProductQBS.
