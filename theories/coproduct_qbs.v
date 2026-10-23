(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals classical_sets boolp
  measurable_structure measurable_function borel_hierarchy
  lebesgue_stieltjes_measure measurable_realfun.
From QBS Require Import quasi_borel.

(**md**************************************************************************)
(* # Coproducts for Quasi-Borel Spaces                                        *)
(*                                                                            *)
(* Binary coproducts, countable coproducts (HKSY Prop. 17), dependent        *)
(* products, and lists as the countable coproduct of finite powers.           *)
(*                                                                            *)
(* ```                                                                        *)
(*   coprodQ X Y == binary coproduct QBS on X + Y                             *)
(*   sigmaQ X == countable coproduct {n & X n} of X : nat -> qbsType R        *)
(*   sigma_case f == copairing of a family of morphisms out of the fibres     *)
(*   piQ I X == dependent product (Pi type) QBS                               *)
(*   listQ X == lists, sigmaQ (fun n => X ^ 'I_n)                              *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set SsrOldRewriteGoalsOrder.  (* TODO: port to the MathComp 2.6 goal order *)
Import boolp.

Local Open Scope classical_set_scope.

Section coproduct_qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

Implicit Types (X Y : qbsType R).

(** Binary coproduct.
    For QBS X and Y, the coproduct X + Y has carrier (X + Y) (Coq sum).
    A function f : mR -> X + Y is a random element iff it factors through
    inl, through inr, or is a measurable gluing of an inl-part and an
    inr-part via a measurable boolean predicate. *)

Definition coprodQ_random (X Y : qbsType R) : set (mR -> X + Y) :=
  [set f |
    (exists a : mR -> X,
      qbs_Mx a /\ forall r, f r = inl (a r))
    \/
    (exists b : mR -> Y,
      qbs_Mx b /\ forall r, f r = inr (b r))
    \/
    (exists (P : mR -> bool) (a : mR -> X) (b : mR -> Y),
      measurable_fun setT P /\
      qbs_Mx a /\
      qbs_Mx b /\
      forall r, f r = if P r then inl (a r) else inr (b r))].

Arguments coprodQ_random : clear implicits.

Lemma coprodQ_Mx_comp (X Y : qbsType R) :
  forall (h : mR -> X + Y) (f : {mfun mR >-> mR}),
    coprodQ_random X Y h ->
    coprodQ_random X Y (h \o f).
Proof.
move=> h f [[a [ha hdef]] |
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
    qbs_Mx b /\ forall r, Fi i r = inr (b r).
    move=> i; case: (hFi i).
    + move=> [a [_ _]].
      by case: (Xempty (a 0%R)).
    + case=> [[b' [hb hdef]] | [P [a _]]].
      * by exists b'.
      * by case: (Xempty (a 0%R)).
  have [getB hgetB] := choice hFi2.
  right; left; exists (fun r => getB (Q r) r); split.
  + exact: (@qbs_Mx_glueT R Y Q getB hQ
      (fun i => (hgetB i).1)).
  + move=> r; exact: (hgetB (Q r)).2.
- have [Yempty | y0] := pselectT Y.
  + (* Y is empty: all Fi i must factor through inl *)
    have hFi1 : forall i, exists a : mR -> X,
      qbs_Mx a /\ forall r, Fi i r = inl (a r).
      move=> i; case: (hFi i).
      * move=> [a [ha hdef]]; by exists a.
      * case=> [[b' [_ _]] | [_ [_ [b' _]]]].
        -- by case: (Yempty (b' 0%R)).
        -- by case: (Yempty (b' 0%R)).
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
      qbs_Mx triple.1.2 /\
      qbs_Mx triple.2 /\
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
    have hai : forall i, qbs_Mx (ai i).
      move=> i; exact: (hgetTriple i).2.1.
    have hbi : forall i, qbs_Mx (bi i).
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
  qbs_morphism (X := X) (Y := coprodQ X Y) (@inl X Y).
Proof.
move=> h ha; rewrite /qbs_Mx /=.
left; exists h; split => //.
Qed.

Lemma qbs_morphism_inr (X Y : qbsType R) :
  qbs_morphism (X := Y) (Y := coprodQ X Y) (@inr X Y).
Proof.
move=> h hb; rewrite /qbs_Mx /=.
right; left; exists h; split => //.
Qed.

(** Case analysis morphism.
    If f : X -> Z and g : Y -> Z are morphisms, then
    case analysis : coprodQ X Y -> Z is a morphism. *)

Lemma qbs_morphism_case (X Y Z : qbsType R)
  (f : X -> Z) (g : Y -> Z) :
  qbs_morphism (X := X) (Y := Z) f ->
  qbs_morphism (X := Y) (Y := Z) g ->
  qbs_morphism (X := coprodQ X Y) (Y := Z)
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

(** Countable coproduct (HKSY Prop. 17).
    For a family X : nat -> qbsType R, a map f : mR -> {n & X n} is a
    random element iff its index is measurable and, for every index i that
    occurs, f agrees on the corresponding part with (i, a_i) for a random
    element a_i of X i. Fibres that do not occur impose nothing, so empty
    fibres are allowed. *)

Definition sigmaQ_random (X : nat -> qbsType R) : set (mR -> {n & X n}) :=
  [set f | measurable_fun [set: mR] (fun r => projT1 (f r)) /\
    forall i, (exists r, projT1 (f r) = i) ->
      exists2 a : mR -> X i, qbs_Mx a &
        forall r, projT1 (f r) = i -> f r = existT X i (a r)].

Arguments sigmaQ_random : clear implicits.

Section sigmaQ_instance.
Variable X : nat -> qbsType R.

Let sigma_comp f (g : {mfun mR >-> mR}) :
  sigmaQ_random X f -> sigmaQ_random X (f \o g).
Proof.
move=> [mi hf]; split; first exact: measurableT_comp mi (measurable_funPT g).
move=> i [r ri]; have [a ha af] := hf i (ex_intro _ (g r) ri).
by exists (a \o g); [exact: qbs_Mx_comp|move=> t ti; exact: af].
Qed.

Let sigma_const (x : {n & X n}) : sigmaQ_random X (fun=> x).
Proof.
split; first exact: measurable_cst.
case: x => j y i [_ /= <-]; exists (fun=> y); first exact: qbs_Mx_const.
by [].
Qed.

Let sigma_glue (P : {mfun mR >-> nat}) (F : nat -> mR -> {n & X n}) :
  (forall n, sigmaQ_random X (F n)) ->
  sigmaQ_random X (fun r => F (P r) r).
Proof.
move=> hF; split.
  apply: (measurable_glue (Fi := fun n r => projT1 (F n r))).
    exact: measurable_funPT.
  by move=> n; have [] := hF n.
move=> i [r0 ri0].
have x0 : X i by rewrite -ri0; exact: projT2 (F (P r0) r0).
have /choice[a ha] : forall n, exists a : mR -> X i, qbs_Mx a /\
    forall r, projT1 (F n r) = i -> F n r = existT X i (a r).
  move=> n; have [ex|nex] := pselect (exists r, projT1 (F n r) = i).
    by have [a ? ?] := (hF n).2 i ex; exists a.
  exists (fun=> x0); split; first exact: qbs_Mx_const.
  by move=> r ri; exfalso; apply: nex; exists r.
exists (fun r => a (P r) r).
  by apply: qbs_Mx_glue => n; exact: (ha n).1.
by move=> r ri; exact: (ha (P r)).2.
Qed.

HB.instance Definition _ :=
  @isQBS.Build R {n & X n} (sigmaQ_random X) sigma_comp sigma_const sigma_glue.
Definition sigmaQ : qbsType R := {n & X n}.
End sigmaQ_instance.

Arguments sigmaQ : clear implicits.

Section sigmaQ_universal.
Variable X : nat -> qbsType R.

(** Injections. *)
Lemma qbs_morphism_sigma_inj (i : nat) :
  qbs_morphism (X := X i) (Y := sigmaQ X) (existT X i).
Proof.
move=> a ha; split; first exact: measurable_cst.
by move=> j [_ /= <-]; exists a.
Qed.

(** Copairing: a family of morphisms out of the fibres induces a morphism
    out of the coproduct. *)
Definition sigma_case Z (f : forall i, X i -> Z) (x : sigmaQ X) : Z :=
  f (projT1 x) (projT2 x).

Lemma qbs_morphism_sigma_case Z (f : forall i, qbsHomType (X i) Z) :
  qbs_morphism (X := sigmaQ X) (Y := Z) (sigma_case f).
Proof.
move=> b [mi hb].
have z0 : Z := sigma_case f (b 0%R).
have /choice[a ha] : forall i, exists a : mR -> Z, qbs_Mx a /\
    forall r, projT1 (b r) = i -> sigma_case f (b r) = a r.
  move=> i; have [ex|nex] := pselect (exists r, projT1 (b r) = i).
    have [a ra hab] := hb i ex; exists (f i \o a); split.
      exact: qbs_hom_proof.
    by move=> r ri; rewrite /sigma_case (hab r ri).
  exists (fun=> z0); split; first exact: qbs_Mx_const.
  by move=> r ri; exfalso; apply: nex; exists r.
have -> : sigma_case f \o b = fun r => a (projT1 (b r)) r.
  by apply/funext => r /=; rewrite ((ha (projT1 (b r))).2 r erefl).
by apply: qbs_Mx_glueT mi _ => n; exact: (ha n).1.
Qed.

Lemma sigma_caseE Z (f : forall i, X i -> Z) i (x : X i) :
  sigma_case f (existT X i x) = f i x.
Proof. by []. Qed.

(** Uniqueness: a map out of the coproduct is determined by its
    restrictions along the injections. *)
Lemma sigma_case_uniq Z (h : sigmaQ X -> Z) :
  h = sigma_case (fun i x => h (existT X i x)).
Proof. by apply/funext => -[i x]. Qed.

End sigmaQ_universal.

(** Dependent product (Pi type).
    For a family X : I -> qbsType R, the dependent product (Pi type) has
    carrier forall i, X i (dependent function type).
    A function alpha : mR -> (forall i, X i) is a random element
    iff for each i, (fun r => alpha r i) is in qbs_Mx (X i). *)

Definition piQ_random (I : Type) (X : I -> qbsType R) :
  set (mR -> forall i : I, X i) :=
  [set alpha | forall i, qbs_Mx (s := X i) (fun r => alpha r i)].

Arguments piQ_random : clear implicits.

Lemma piQ_Mx_comp (I : Type) (X : I -> qbsType R) :
  forall (h : mR -> forall i, X i) (f : {mfun mR >-> mR}),
    piQ_random I X h ->
    piQ_random I X (h \o f).
Proof.
move=> h f hh i.
have -> : (fun r => (h \o f) r i) = (fun r => h r i) \o f by [].
exact: qbs_Mx_comp (hh i).
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
  qbs_morphism (X := piQ I X) (Y := X i) (fun f => f i).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /=.
exact: (halpha i).
Qed.

(* Tupling morphism *)
Lemma qbs_morphism_tuple (I : Type) (X : I -> qbsType R) (W : qbsType R)
  (fi : forall i, W -> X i)
  (hfi : forall i, qbs_morphism (X := W) (Y := X i) (fi i)) :
  qbs_morphism (X := W) (Y := piQ I X) (fun w i => fi i w).
Proof.
move=> alpha halpha; rewrite /qbs_Mx /= => i.
have -> : (fun r => fi i (alpha r)) = (fi i) \o alpha by [].
exact: (hfi i) _ halpha.
Qed.

(** Lists as the countable coproduct of finite powers (HKSY Sec. IV). *)
Definition listQ (X : qbsType R) : qbsType R :=
  sigmaQ (fun n => piQ 'I_n (fun=> X)).

(** The length of a list is a measurable function of a random list. *)
Lemma qbs_morphism_size (X : qbsType R) :
  qbs_morphism (X := listQ X) (Y := natQ R) (fun l => projT1 l).
Proof. by move=> b [mi _]. Qed.

End coproduct_qbs.
