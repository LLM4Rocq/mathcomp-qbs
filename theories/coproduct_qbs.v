(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals classical_sets boolp
  measurable_structure measurable_function borel_hierarchy
  lebesgue_stieltjes_measure measurable_realfun.
From QBS Require Import quasi_borel.

(**md**************************************************************************)
(* # Coproducts for Quasi-Borel Spaces                                        *)
(*                                                                            *)
(* Binary coproducts (sum types) and general coproducts (sigma types)         *)
(* following the Isabelle AFP development by Hirata, Minamide, Sato.          *)
(*                                                                            *)
(* ```                                                                        *)
(*   coprodQ X Y == binary coproduct QBS on X + Y                             *)
(*   gen_coprodQ d I X inh == general coproduct (sigma type) QBS              *)
(*   piQ I X == dependent product (Pi type) QBS                               *)
(*   listQ X x0 == list QBS on seq X                                          *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import boolp.

Local Open Scope classical_set_scope.

Section coproduct_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(** Binary coproduct.
    For QBS X and Y, the coproduct X + Y has carrier (X + Y) (Coq sum).
    A function f : mR -> X + Y is a random element iff it factors through
    inl, through inr, or is a measurable gluing of an inl-part and an
    inr-part via a measurable boolean predicate. *)

Definition coprodQ_random (X Y : qbsType R) : set (mR -> X + Y) :=
  [set f |
    (exists a : mR -> X,
      @qbs_Mx R X a /\ forall r, f r = inl (a r))
    \/
    (exists b : mR -> Y,
      @qbs_Mx R Y b /\ forall r, f r = inr (b r))
    \/
    (exists (P : mR -> bool) (a : mR -> X) (b : mR -> Y),
      measurable_fun setT P /\
      @qbs_Mx R X a /\
      @qbs_Mx R Y b /\
      forall r, f r = if P r then inl (a r) else inr (b r))].

Arguments coprodQ_random : clear implicits.

Lemma coprodQ_Mx_comp (X Y : qbsType R) :
  forall (h : mR -> X + Y) (f : {mfun mR >-> mR}),
    coprodQ_random X Y h ->
    coprodQ_random X Y (h \o f).
Proof.
move=> h f Hh.
case: Hh => [[a [ha hdef]] |
  [[b' [hb hdef]] | [P [a [b' [hP [ha [hb hdef]]]]]]]].
- left; exists (a \o f); split.
  + exact: qbs_Mx_comp ha.
  + by move=> r; rewrite /= hdef.
- right; left; exists (b' \o f); split.
  + exact: qbs_Mx_comp hb.
  + by move=> r; rewrite /= hdef.
- right; right; exists (P \o f), (a \o f), (b' \o f); split; [|split; [|split]].
  + exact: measurableT_comp hP (measurable_funPT f).
  + exact: qbs_Mx_comp ha.
  + exact: qbs_Mx_comp hb.
  + by move=> r; rewrite /= hdef.
Qed.

Lemma coprodQ_Mx_const (X Y : qbsType R) :
  forall x : X + Y,
    coprodQ_random X Y (fun _ => x).
Proof.
case=> [xl | yr].
- left; exists (fun _ => xl); split.
  + exact: qbs_Mx_const.
  + by [].
- right; left; exists (fun _ => yr); split.
  + exact: qbs_Mx_const.
  + by [].
Qed.

Lemma coprodQ_Mx_glue (X Y : qbsType R) :
  forall (Q : {mfun mR >-> nat}) (Fi : nat -> mR -> X + Y),
    (forall i, coprodQ_random X Y (Fi i)) ->
    coprodQ_random X Y (fun r => Fi (Q r) r).
Proof.
move=> Q Fi hFi.
have hQ : measurable_fun setT Q := measurable_funPT Q.
(* We handle the cases based on whether X and Y are inhabited *)
have [Xempty | x0] := pselectT X.
- (* X is empty: cases 1 and 3 of coprodQ_random are impossible *)
  (* So all Fi i must factor through inr *)
  have hFi2 : forall i, exists b : mR -> Y,
    @qbs_Mx R Y b /\ forall r, Fi i r = inr (b r).
    move=> i; case: (hFi i).
    + move=> [a [_ hdef]].
      exfalso; exact: Xempty (a (0%R : mR)).
    + case=> [[b' [hb hdef]] | [P [a _]]].
      * by exists b'.
      * exfalso; exact: Xempty (a (0%R : mR)).
  have [getB hgetB] := choice hFi2.
  right; left; exists (fun r => getB (Q r) r); split.
  + exact: (@qbs_Mx_glueT R Y Q getB hQ
      (fun i => (hgetB i).1)).
  + move=> r; exact: (hgetB (Q r)).2.
- have [Yempty | y0] := pselectT Y.
  + (* Y is empty: all Fi i must factor through inl *)
    have hFi1 : forall i, exists a : mR -> X,
      @qbs_Mx R X a /\ forall r, Fi i r = inl (a r).
      move=> i; case: (hFi i).
      * move=> [a [ha hdef]]; by exists a.
      * case=> [[b' [_ hdef]] | [_ [_ [b' _]]]].
        -- exfalso; exact: Yempty (b' (0%R : mR)).
        -- exfalso; exact: Yempty (b' (0%R : mR)).
    have [getA hgetA] := choice hFi1.
    left; exists (fun r => getA (Q r) r); split.
    * exact: (@qbs_Mx_glueT R X Q getA hQ
        (fun i => (hgetA i).1)).
    * move=> r; exact: (hgetA (Q r)).2.
  + (* Both X and Y are inhabited *)
    (* Normalize each Fi i to case 3 form *)
    have hFi3 : forall i,
      exists triple : (mR -> bool) * (mR -> X) * (mR -> Y),
      measurable_fun setT triple.1.1 /\
      @qbs_Mx R X triple.1.2 /\
      @qbs_Mx R Y triple.2 /\
      forall r, Fi i r =
        if triple.1.1 r then inl (triple.1.2 r)
        else inr (triple.2 r).
      move=> i; case: (hFi i).
      * move=> [a [ha hdef]].
        (* case 1: pure inl *)
        exists ((fun _ => true), a, (fun _ => y0)).
        split; [|split; [|split]] => /=.
        -- exact: measurable_cst.
        -- exact: ha.
        -- exact: qbs_Mx_const.
        -- by move=> r; rewrite hdef.
      * case=> [[b' [hb hdef]] |
          [P [a [b' [hP [ha [hb hdef]]]]]]].
        (* case 2: pure inr *)
        -- exists ((fun _ => false), (fun _ => x0), b').
           split; [|split; [|split]] => /=.
           ++ exact: measurable_cst.
           ++ exact: qbs_Mx_const.
           ++ exact: hb.
           ++ by move=> r; rewrite hdef.
        (* case 3: already gluing *)
        -- exists (P, a, b').
           split; [|split; [|split]] => //.
    have [getTriple hgetTriple] := choice hFi3.
    (* Extract the components *)
    set Pi := fun i => (getTriple i).1.1.
    set ai := fun i => (getTriple i).1.2.
    set bi := fun i => (getTriple i).2.
    have hPi_meas :
      forall i, measurable_fun setT (Pi i).
      move=> i; exact: (hgetTriple i).1.
    have hai : forall i, @qbs_Mx R X (ai i).
      move=> i; exact: (hgetTriple i).2.1.
    have hbi : forall i, @qbs_Mx R Y (bi i).
      move=> i; exact: (hgetTriple i).2.2.1.
    have hFi_eq : forall i r,
      Fi i r = if Pi i r then inl (ai i r)
               else inr (bi i r).
      move=> i; exact: (hgetTriple i).2.2.2.
    (* Now construct the result in case 3 *)
    right; right.
    (* The combined P: P'(r) = Pi(Q(r))(r) *)
    set P' : mR -> bool := fun r => Pi (Q r) r.
    (* The combined a: a'(r) = ai(Q(r))(r) *)
    set a' : mR -> X := fun r => ai (Q r) r.
    (* The combined b: b'(r) = bi(Q(r))(r) *)
    set b'' : mR -> Y := fun r => bi (Q r) r.
    exists P', a', b''; split; [|split; [|split]].
    * (* P' is measurable *)
      rewrite /P'.
      exact: (@measurable_glue R _ _ Q
        (fun i => Pi i) hQ hPi_meas).
    * (* a' is in Mx(X) *)
      rewrite /a'.
      exact: (@qbs_Mx_glueT R X Q
        (fun i => ai i) hQ hai).
    * (* b'' is in Mx(Y) *)
      rewrite /b''.
      exact: (@qbs_Mx_glueT R Y Q
        (fun i => bi i) hQ hbi).
    * (* extensional equality *)
      move=> r; rewrite /P' /a' /b'' hFi_eq //.
Qed.

(** Binary coproduct QBS on (X + Y). *)
Section coprodQ_instance.
Variables (X Y : qbsType R).
Let Mx := coprodQ_random X Y.
Let ax1 := coprodQ_Mx_comp (X:=X) (Y:=Y).
Let ax2 := coprodQ_Mx_const (X:=X) (Y:=Y).
Let ax3 := coprodQ_Mx_glue (X:=X) (Y:=Y).
HB.instance Definition _ := @isQBS.Build R (X + Y)%type Mx ax1 ax2 ax3.
Definition coprodQ : qbsType R := (X + Y)%type.
End coprodQ_instance.

Arguments coprodQ : clear implicits.

(** Injection morphisms. *)

Lemma qbs_morphism_inl (X Y : qbsType R) :
  @qbs_morphism R X (coprodQ X Y) (@inl X Y).
Proof.
move=> h ha; rewrite /qbs_Mx /=.
left; exists h; split => //.
Qed.

Lemma qbs_morphism_inr (X Y : qbsType R) :
  @qbs_morphism R Y (coprodQ X Y) (@inr X Y).
Proof.
move=> h hb; rewrite /qbs_Mx /=.
right; left; exists h; split => //.
Qed.

(** Case analysis morphism.
    If f : X -> Z and g : Y -> Z are morphisms, then
    case analysis : coprodQ X Y -> Z is a morphism. *)

Lemma qbs_morphism_case (X Y Z : qbsType R)
  (f : X -> Z) (g : Y -> Z) :
  @qbs_morphism R X Z f ->
  @qbs_morphism R Y Z g ->
  @qbs_morphism R (coprodQ X Y) Z
    (fun s => match s with inl x => f x | inr y => g y end).
Proof.
move=> hf hg gamma.
case=> [[a [ha hdef]] | [[b' [hb hdef]] | [P [a [b' [hP [ha [hb hdef]]]]]]]].
- (* gamma factors through inl *)
  have heq : (fun s => match s with inl x => f x | inr y => g y end) \o gamma =
              f \o a.
  { apply: funext => r; rewrite /= hdef //. }
  by rewrite heq; exact: hf _ ha.
- (* gamma factors through inr *)
  have heq : (fun s => match s with inl x => f x | inr y => g y end) \o gamma =
              g \o b'.
  { apply: funext => r; rewrite /= hdef //. }
  by rewrite heq; exact: hg _ hb.
- (* gamma is a measurable gluing: use qbs_Mx_glue *)
  have heq : (fun s => match s with inl x => f x | inr y => g y end) \o gamma =
              fun r => if P r then f (a r) else g (b' r).
  { apply: funext => r; rewrite /= hdef; by case: (P r). }
  rewrite heq.
  set Pn : mR -> nat := fun r => if P r then 0 else 1.
  set Gi : nat -> mR -> Z :=
    fun i => if i == 0 then f \o a else g \o b'.
  have heq2 : (fun r => if P r then f (a r) else g (b' r)) =
               (fun r => Gi (Pn r) r).
  { apply: funext => r; rewrite /Gi /Pn.
    by case: (P r). }
  rewrite heq2.
  apply: (@qbs_Mx_glueT R Z Pn Gi).
    rewrite /Pn; apply: measurable_fun_ifT => //; exact: measurable_cst.
  move=> i; rewrite /Gi.
  by case: (i == 0); [exact: hf _ ha | exact: hg _ hb].
Qed.

(** ## Universal property of coproducts                              *)
(** The following lemmas express that [coprodQ X Y] is the coproduct *)
(** of [X] and [Y] in QBS: any morphism out of [coprodQ X Y] is      *)
(** uniquely determined by its restrictions along [inl] and [inr].   *)

(** Beta rule for coproducts (left injection): case analysis on an
    [inl]-value reduces to the left branch. *)
Lemma qbs_morphism_case_inl (X Y Z : qbsType R)
  (f : X -> Z) (g : Y -> Z) (x : X) :
  (fun s : X + Y => match s with inl x0 => f x0 | inr y0 => g y0 end) (inl x)
    = f x.
Proof. by []. Qed.

(** Beta rule for coproducts (right injection): case analysis on an
    [inr]-value reduces to the right branch. *)
Lemma qbs_morphism_case_inr (X Y Z : qbsType R)
  (f : X -> Z) (g : Y -> Z) (y : Y) :
  (fun s : X + Y => match s with inl x0 => f x0 | inr y0 => g y0 end) (inr y)
    = g y.
Proof. by []. Qed.

(** Eta rule / universal property: any function out of [coprodQ X Y]
    factors through [inl]/[inr] via case analysis. This is a
    tautology at the level of underlying functions, but makes
    explicit the uniqueness part of the coproduct universal property:
    a morphism [h : coprodQ X Y -> Z] is completely determined by
    [h \o inl] and [h \o inr]. *)
Lemma qbs_coprod_eta (X Y Z : qbsType R)
  (h : coprodQ X Y -> Z) (xy : coprodQ X Y) :
  h xy = match xy with
         | inl x => h (inl x)
         | inr y => h (inr y)
         end.
Proof. by case: xy. Qed.

(** General coproduct (Sigma type).
    For a family X : I -> qbsType R, the general coproduct has carrier
    {i : I & X i} (dependent sum / sigma type).
    A random element f selects an index via P : mR -> I and then a
    random element in the corresponding fiber. *)

Definition gen_coprodQ_random (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) :
  set (mR -> {i : I & X i}) :=
  [set f | exists (P : mR -> I) (Fi : forall i, mR -> X i),
    measurable_fun setT P /\
    (forall i, @qbs_Mx R (X i) (Fi i)) /\
    (forall r, f r = existT _ (P r) (Fi (P r) r))].

Arguments gen_coprodQ_random : clear implicits.

Lemma gen_coprodQ_Mx_comp (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) :
  forall (h : mR -> {i : I & X i}) (f : {mfun mR >-> mR}),
    gen_coprodQ_random d I X h ->
    gen_coprodQ_random d I X (h \o f).
Proof.
move=> h f [P [Fi [hP [hFi hdef]]]].
exists (P \o f), (fun i => Fi i \o f); split; [|split].
- exact: measurableT_comp hP (measurable_funPT f).
- move=> i; exact: qbs_Mx_comp (hFi i).
- move=> r; rewrite /= hdef //.
Qed.

Lemma gen_coprodQ_Mx_const (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R)
  (inh : forall i, X i) :
  forall x : {i : I & X i},
    gen_coprodQ_random d I X (fun _ => x).
Proof.
move=> [i0 v0].
exists (fun _ => i0).
(* For Fi, we need forall j, mR -> X j. At j = i0, return v0;
   at j <> i0, use the inhabitedness witness inh j.
   We use pselect to decide j = i0 and eq_rect to transport v0. *)
exists (fun j => match pselect (j = i0) with
  | left H => fun _ => eq_rect _ (fun k => X k) v0 _ (esym H)
  | right _ => fun _ => inh j
  end).
split; [|split].
- exact: measurable_cst.
- move=> j.
  case: (pselect (j = i0)) => [H | _].
  + subst j; exact: qbs_Mx_const.
  + exact: qbs_Mx_const.
- move=> r /=.
  case: (pselect (i0 = i0)) => [H | abs].
  + congr (existT _ i0 _).
    have -> : H = erefl by exact: Prop_irrelevance.
    by [].
  + exfalso; exact: abs erefl.
Qed.

Lemma gen_coprodQ_Mx_glue (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) :
  forall (Q : {mfun mR >-> nat}) (Fi : nat -> mR -> {i : I & X i}),
    (forall i, gen_coprodQ_random d I X (Fi i)) ->
    gen_coprodQ_random d I X (fun r => Fi (Q r) r).
Proof.
move=> Q Fi hFi.
have hQ : measurable_fun setT Q := measurable_funPT Q.
(* Each Fi n is in gen_coprodQ_random, so extract witnesses uniformly *)
have hFi' : forall n, exists triple :
  (mR -> I) * (forall i, mR -> X i) * Prop,
  measurable_fun setT triple.1.1 /\
  (forall i, @qbs_Mx R (X i) (triple.1.2 i)) /\
  (forall r, Fi n r = existT _ (triple.1.1 r) (triple.1.2 (triple.1.1 r) r)).
  move=> n; case: (hFi n) => [Pn [Gin [hPn [hGin hdef]]]].
  by exists (Pn, Gin, True).
have [getTriple hgetTriple] := choice hFi'.
set Pn := fun n => (getTriple n).1.1.
set Gin := fun n => (getTriple n).1.2.
have hPn_meas : forall n, measurable_fun setT (Pn n).
  move=> n; exact: (hgetTriple n).1.
have hGin :
  forall n i, @qbs_Mx R (X i) (Gin n i).
  move=> n i; exact: (hgetTriple n).2.1 i.
have hFi_eq : forall n r,
  Fi n r = existT _ (Pn n r) (Gin n (Pn n r) r).
  move=> n; exact: (hgetTriple n).2.2.
(* Construct the result *)
exists (fun r => Pn (Q r) r),
  (fun i => fun r => Gin (Q r) i r); split; [|split].
- exact: (@measurable_glue R _ _ Q (fun n => Pn n) hQ hPn_meas).
- move=> i.
  exact: (@qbs_Mx_glueT R (X i) Q (fun n => Gin n i) hQ (fun n => hGin n i)).
- move=> r; rewrite hFi_eq //.
Qed.

(** General coproduct (sigma type) QBS. *)
Section gen_coprodQ_instance.
Variables (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R) (inh : forall i, X i).
Let Mx := gen_coprodQ_random d I X.
Let ax1 := gen_coprodQ_Mx_comp (I:=I) (X:=X).
Let ax2 := gen_coprodQ_Mx_const (I:=I) inh.
Let ax3 := gen_coprodQ_Mx_glue (I:=I) (X:=X).
HB.instance Definition _ := @isQBS.Build R {i : I & X i} Mx ax1 ax2 ax3.
Definition gen_coprodQ : qbsType R := {i : I & X i}.
End gen_coprodQ_instance.

Arguments gen_coprodQ : clear implicits.

(* Injection into general coproduct *)
Lemma qbs_morphism_gen_inj (d : measure_display) (I : measurableType d)
  (X : I -> qbsType R)
  (inh : forall i, X i) (i : I) :
  @qbs_morphism R (X i) (gen_coprodQ d I X inh) (fun x => existT _ i x).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /=.
exists (fun _ => i), (fun j => match pselect (j = i) with
  | left H => fun r => eq_rect _ (fun k => X k) (alpha r) _ (esym H)
  | right _ => fun _ => inh j
  end).
split; [|split].
- exact: measurable_cst.
- move=> j.
  case: (pselect (j = i)) => [H | _].
  + subst j; exact: halpha.
  + exact: qbs_Mx_const.
- move=> r /=.
  case: (pselect (i = i)) => [H | abs].
  + congr (existT _ i _).
    have -> : H = erefl by exact: Prop_irrelevance.
    by [].
  + exfalso; exact: abs erefl.
Qed.

(** Dependent product (Pi type).
    For a family X : I -> qbsType R, the dependent product (Pi type) has
    carrier forall i, X i (dependent function type).
    A function alpha : mR -> (forall i, X i) is a random element
    iff for each i, (fun r => alpha r i) is in qbs_Mx (X i). *)

Definition piQ_random (I : Type) (X : I -> qbsType R) :
  set (mR -> forall i : I, X i) :=
  [set alpha | forall i, @qbs_Mx R (X i) (fun r => alpha r i)].

Arguments piQ_random : clear implicits.

Lemma piQ_Mx_comp (I : Type) (X : I -> qbsType R) :
  forall (h : mR -> forall i, X i) (f : {mfun mR >-> mR}),
    piQ_random I X h ->
    piQ_random I X (h \o f).
Proof.
move=> h f Hh i.
have -> : (fun r => (h \o f) r i) = (fun r => h r i) \o f by [].
exact: qbs_Mx_comp (Hh i).
Qed.

Lemma piQ_Mx_const (I : Type) (X : I -> qbsType R) :
  forall x : (forall i : I, X i),
    piQ_random I X (fun _ => x).
Proof.
move=> x i.
exact: qbs_Mx_const.
Qed.

Lemma piQ_Mx_glue (I : Type) (X : I -> qbsType R) :
  forall (Q : {mfun mR >-> nat})
    (Fi : nat -> mR -> forall i, X i),
    (forall n, piQ_random I X (Fi n)) ->
    piQ_random I X (fun r => Fi (Q r) r).
Proof.
move=> Q Fi hFi i.
exact: (@qbs_Mx_glue _ (X i) Q (fun n r => Fi n r i) (fun n => hFi n i)).
Qed.

(** Dependent product (Pi type) QBS. *)
Section piQ_instance.
Variables (I : Type) (X : I -> qbsType R).
Let Mx := piQ_random I X.
Let ax1 := piQ_Mx_comp (X:=X).
Let ax2 := piQ_Mx_const (X:=X).
Let ax3 := piQ_Mx_glue (X:=X).
HB.instance Definition _ := @isQBS.Build R (forall i : I, X i) Mx ax1 ax2 ax3.
Definition piQ : qbsType R := (forall i : I, X i).
End piQ_instance.

Arguments piQ : clear implicits.

(* Projection morphism *)
Lemma qbs_morphism_proj (I : Type) (X : I -> qbsType R) (i : I) :
  @qbs_morphism R (piQ I X) (X i) (fun f => f i).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /=.
exact: (halpha i).
Qed.

(* Tupling morphism *)
Lemma qbs_morphism_tuple (I : Type) (X : I -> qbsType R) (W : qbsType R)
  (fi : forall i, W -> X i)
  (hfi : forall i, @qbs_morphism R W (X i) (fi i)) :
  @qbs_morphism R W (piQ I X) (fun w i => fi i w).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /= => i.
have -> : (fun r => fi i (alpha r)) = (fi i) \o alpha by [].
exact: (hfi i) _ halpha.
Qed.

(** Binary coproduct ~ general coproduct isomorphism.
    The binary coproduct X + Y is isomorphic to the general coproduct
    over bool, where true |-> X and false |-> Y. *)

Lemma qbs_morphism_coprod_to_gen (X Y : qbsType R)
  (inhX : X) (inhY : Y) :
  @qbs_morphism R (coprodQ X Y) (gen_coprodQ default_measure_display bool
    (fun b => if b then X else Y)
    (fun b => if b as b0 return (if b0 then X else Y) then inhX else inhY))
    (fun s => match s with
     | inl x => existT _ true x
     | inr y => existT _ false y
     end).
Proof.
move=> alpha.
case=> [[a [ha hdef]] | [[b' [hb hdef]] | [P [a [b' [hP [ha [hb hdef]]]]]]]].
- (* alpha factors through inl: alpha r = inl (a r) *)
  exists (fun _ => true), (fun (i : bool) =>
    if i as i0 return (mR -> (if i0 then X else Y))
    then a
    else (fun _ => inhY)).
  split; [|split].
  + exact: measurable_cst.
  + move=> [|] /=; [exact: ha | exact: qbs_Mx_const].
  + move=> r /=; rewrite hdef //.
- (* alpha factors through inr: alpha r = inr (b' r) *)
  exists (fun _ => false), (fun (i : bool) =>
    if i as i0 return (mR -> (if i0 then X else Y))
    then (fun _ => inhX)
    else b').
  split; [|split].
  + exact: measurable_cst.
  + move=> [|] /=; [exact: qbs_Mx_const | exact: hb].
  + move=> r /=; rewrite hdef //.
- (* alpha is a measurable gluing *)
  (* P : mR -> bool with measurable_fun setT P *)
  (* We need an index function mR -> bool for the gen coproduct *)
  exists P, (fun (i : bool) =>
    if i as i0 return (mR -> (if i0 then X else Y))
    then a
    else b').
  split; [|split].
  + exact: hP.
  + move=> [|] /=; [exact: ha | exact: hb].
  + move=> r /=; rewrite hdef; by case: (P r).
Qed.

Lemma qbs_morphism_gen_to_coprod (X Y : qbsType R)
  (inhX : X) (inhY : Y) :
  @qbs_morphism R (gen_coprodQ default_measure_display bool
    (fun b => if b then X else Y)
    (fun b => if b as b0 return (if b0 then X else Y) then inhX else inhY))
    (coprodQ X Y)
    (fun s => match projT1 s as b return
      ((if b then X else Y) -> X + Y)
      with true => inl | false => inr end (projT2 s)).
Proof.
move=> alpha [P [Fi [hP [hFi hdef]]]].
(* P : mR -> bool, Fi : forall i : bool, mR -> (if i then X else Y) *)
(* After rewriting with hdef, the composition becomes:
   fun r => if P r then inl (Fi true r) else inr (Fi false r)
   which is a coprodQ_random element. P is measurable by gen_coprodQ_random. *)
right; right.
exists P, (Fi true), (Fi false); split; [|split; [|split]].
- exact: hP.
- exact: (hFi true).
- exact: (hFi false).
- move=> r; rewrite /= hdef /=; by case: (P r).
Qed.

(** List type as coproduct of products.
    Following Isabelle's Product_QuasiBorel.thy, the list type list(X) is
    a QBS defined as a countable coproduct of finite products:
    list(X) = coprod_{n : nat} X^n.
    The carrier is seq X. A function alpha : mR -> seq X is a
    random element iff there exist a measurable length function
    len : mR -> nat and for each position i a random element Fi i in Mx(X)
    such that alpha(r) = mkseq (fun i => Fi i r) (len r). *)

Definition listQ_random (X : qbsType R) :
  set (mR -> seq X) :=
  [set alpha | exists (len : mR -> nat) (Fi : nat -> mR -> X),
    measurable_fun setT len /\
    (forall i, @qbs_Mx R X (Fi i)) /\
    (forall r, alpha r = mkseq (fun i => Fi i r) (len r))].

Arguments listQ_random : clear implicits.

Lemma listQ_Mx_comp (X : qbsType R) :
  forall (h : mR -> seq X) (f : {mfun mR >-> mR}),
    listQ_random X h ->
    listQ_random X (h \o f).
Proof.
move=> h f [len [Fi [hlen [hFi hdef]]]].
exists (len \o f), (fun i => Fi i \o f); split; [|split].
- exact: measurableT_comp hlen (measurable_funPT f).
- move=> i; exact: qbs_Mx_comp (hFi i).
- move=> r; rewrite /= hdef //.
Qed.

Lemma listQ_Mx_const (X : qbsType R) (x0 : X) :
  forall x : seq X,
    listQ_random X (fun _ => x).
Proof.
move=> x.
exists (fun _ => size x), (fun i _ => nth x0 x i).
split; [|split].
- exact: measurable_cst.
- move=> i; exact: qbs_Mx_const.
- move=> r; symmetry; exact: mkseq_nth.
Qed.

Lemma listQ_Mx_glue (X : qbsType R) :
  forall (Q : {mfun mR >-> nat}) (Gi : nat -> mR -> seq X),
    (forall i, listQ_random X (Gi i)) ->
    listQ_random X (fun r => Gi (Q r) r).
Proof.
move=> Q Gi hGi.
have hQ : measurable_fun setT Q := measurable_funPT Q.
have hGi' : forall n, exists pair : (mR -> nat) * (nat -> mR -> X),
  measurable_fun setT pair.1 /\
  (forall i, @qbs_Mx R X (pair.2 i)) /\
  (forall r, Gi n r = mkseq (fun i => pair.2 i r) (pair.1 r)).
  move=> n; case: (hGi n) => [len [Fi [hlen [hFi hdef]]]].
  by exists (len, Fi).
have [getPair hgetPair] := choice hGi'.
set lenN := fun n => (getPair n).1.
set FiN := fun n => (getPair n).2.
have hlenN : forall n, measurable_fun setT (lenN n).
  move=> n; exact: (hgetPair n).1.
have hFiN : forall n i, @qbs_Mx R X (FiN n i).
  move=> n i; exact: (hgetPair n).2.1 i.
have hGi_eq : forall n r,
  Gi n r = mkseq (fun i => FiN n i r) (lenN n r).
  move=> n; exact: (hgetPair n).2.2.
exists (fun r => lenN (Q r) r), (fun i r => FiN (Q r) i r); split; [|split].
- exact: (@measurable_glue _ _ _ Q (fun n => lenN n) hQ hlenN).
- move=> i.
  exact: (@qbs_Mx_glueT R X Q (fun n => FiN n i) hQ (fun n => hFiN n i)).
- move=> r; rewrite hGi_eq //.
Qed.

(* The list QBS. Requires an inhabitedness witness x0 for the constant
   axiom (needed to extract nth elements from constant lists). *)
(** List QBS: countable coproduct of finite products. *)
Section listQ_instance.
Variables (X : qbsType R) (x0 : X).
Let Mx := listQ_random X.
Let ax1 := listQ_Mx_comp (X:=X).
Let ax2 := listQ_Mx_const x0.
Let ax3 := listQ_Mx_glue (X:=X).
HB.instance Definition _ := @isQBS.Build R (seq X) Mx ax1 ax2 ax3.
Definition listQ : qbsType R := (seq X).
End listQ_instance.

(* Length is a QBS morphism from listQ to natQ *)
Lemma qbs_morphism_length (X : qbsType R) (x0 : X) :
  @qbs_morphism R (listQ x0) (natQ R) (@size X).
Proof.
move=> alpha [len [Fi [hlen [hFi hdef]]]]; rewrite /qbs_Mx /=.
have heq : size \o alpha = len.
  apply: funext => r; rewrite /= hdef size_mkseq //.
by rewrite heq.
Qed.

(* nth projection: for any index i, the i-th element extraction
   preserves randomness. When i < len(r), the result is Fi i r;
   when i >= len(r), the result is the default x0. *)
Lemma listQ_nth_random (X : qbsType R) (x0 : X) (i : nat) :
  forall alpha, @qbs_Mx R (listQ x0) alpha ->
    @qbs_Mx R X (fun r => nth x0 (alpha r) i).
Proof.
move=> alpha [len [Fi [hlen [hFi hdef]]]].
have heq : (fun r => nth x0 (alpha r) i) =
          (fun r => if i < len r then Fi i r else x0).
  apply: funext => r; rewrite hdef.
  case hlt : (i < len r).
  - by rewrite nth_mkseq.
  - rewrite nth_default //; rewrite size_mkseq.
    by rewrite leqNgt hlt.
rewrite heq.
set P := fun r : mR => if (i < len r)%N then 0%N else 1%N.
set Gi := fun (n : nat) => if n == 0 then Fi i else (fun _ => x0).
have hP : measurable_fun setT P.
  rewrite /P.
  apply: (@measurable_fun_ifT _ _ mR nat
    (fun _ => 0%N) (fun _ => 1%N) (fun r => i < len r)).
  - exact: (measurable_fun_ltn (@measurable_cst _ _ mR _ setT i) hlen).
  - exact: measurable_cst.
  - exact: measurable_cst.
have heq2 : (fun r => if i < len r then Fi i r else x0) =
          (fun r => Gi (P r) r).
  apply: funext => r; rewrite /Gi /P.
  by case: (i < len r).
rewrite heq2.
apply: (@qbs_Mx_glueT R X P Gi hP).
move=> n; rewrite /Gi.
by case: (n == 0); [exact: hFi | exact: qbs_Mx_const].
Qed.

End coproduct_qbs.
