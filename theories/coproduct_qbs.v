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
(*   listQ X == lists, sigmaQ (fun n => X ^ 'I_n)                             *)
(*   list_mk a == the list given by a finite family a : 'I_n -> X             *)
(*   seq_of_list l, list_of_seq s == bijection listQ X <-> seq X              *)
(*                    (list_of_seqK, seq_of_listK)                            *)
(*   qbs_nil X, qbs_cons == nil, and cons : X * listQ X -> listQ X            *)
(*   list_rec b f l == recursion, f : X -> listQ X -> Y -> Y                  *)
(*                    (list_rec_nil, list_rec_cons)                           *)
(*   qbs_morphism_list_rec_ext == list_rec is a morphism listQ X -> Y         *)
(*   list_rec_hom == Y => (X => listQ X => Y => Y) => listQ X => Y            *)
(*   qbs_negb, qbs_andb, qbs_orb, qbs_implb == boolean operations             *)
(*   qbs_ltr, qbs_ltn == < on realQ and on natQ, into boolQ                   *)
(*   qbs_arg_swap == (X => Y => Z) -> (Y => X => Z)                           *)
(*   qbs_exp_compose == (X => Y) * (Y => Z) -> (X => Z)                       *)
(*   qbs_case f g == copairing of f : X -> Z and g : Y -> Z                   *)
(*   qbs_case_exp == (X => Z) * (Y => Z) -> (X + Y => Z)                      *)
(*   qbs_hom_of f hf == f bundled with a proof hf that it is a morphism       *)
(* ```                                                                        *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
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


(** ## Concrete morphisms
    Boolean and order operations, and internal morphisms on exponentials
    and coproducts (AFP Exponent_QuasiBorel.thy). *)

(** Bundle a function together with a proof that it is a morphism. *)
Definition qbs_hom_of (X Y : qbsType R) (f : X -> Y) (hf : qbs_morphism f) :
    qbsHomType X Y :=
  @QBSHom.Pack R X Y f (QBSHom.Class (@isQBSMorphism.Build R X Y f hf)).

Definition qbs_negb : qbsHomType (boolQ R) (boolQ R) :=
  qbs_hom_of (f := negb : boolQ R -> boolQ R) (fun a ha => measurable_neg ha).

Definition qbs_andb : qbsHomType (prodQ (boolQ R) (boolQ R)) (boolQ R) :=
  qbs_hom_of (f := fun p : prodQ (boolQ R) (boolQ R) => (p.1 && p.2 : boolQ R))
    (fun a ha => measurable_and ha.1 ha.2).

Definition qbs_orb : qbsHomType (prodQ (boolQ R) (boolQ R)) (boolQ R) :=
  qbs_hom_of (f := fun p : prodQ (boolQ R) (boolQ R) => (p.1 || p.2 : boolQ R))
    (fun a ha => measurable_or ha.1 ha.2).

Lemma qbs_morphism_implb :
  qbs_morphism (X := prodQ (boolQ R) (boolQ R)) (Y := boolQ R)
    (fun p => p.1 ==> p.2).
Proof.
move=> a ha; have -> : (fun p : bool * bool => p.1 ==> p.2) \o a =
    fun r => ~~ (a r).1 || (a r).2 by apply/funext => r; rewrite /= implybE.
exact: measurable_or (measurable_neg ha.1) ha.2.
Qed.

Definition qbs_implb : qbsHomType (prodQ (boolQ R) (boolQ R)) (boolQ R) :=
  qbs_hom_of qbs_morphism_implb.

Definition qbs_ltr : qbsHomType (prodQ (realQ R) (realQ R)) (boolQ R) :=
  qbs_hom_of
    (f := fun p : prodQ (realQ R) (realQ R) => ((p.1 < p.2)%R : boolQ R))
    (fun a ha => measurable_fun_ltr ha.1 ha.2).

Definition qbs_ltn : qbsHomType (prodQ (natQ R) (natQ R)) (boolQ R) :=
  qbs_hom_of (f := fun p : prodQ (natQ R) (natQ R) => ((p.1 < p.2)%N : boolQ R))
    (fun a ha => measurable_fun_ltn ha.1 ha.2).

(** Gluing two random elements along a measurable boolean test. *)
Lemma qbs_Mx_if (A : qbsType R) (P : mR -> bool) (u v : mR -> A) :
  measurable_fun setT P -> qbs_Mx u -> qbs_Mx v ->
  qbs_Mx (fun r => if P r then u r else v r).
Proof.
move=> hP hu hv.
pose Pn (r : mR) : nat := if P r then 0 else 1.
pose G (i : nat) : mR -> A := if i == 0 then u else v.
have -> : (fun r => if P r then u r else v r) = fun r => G (Pn r) r.
  by apply/funext => r; rewrite /G /Pn; case: (P r).
apply: (@qbs_Mx_glueT R A Pn G).
  by apply: measurable_fun_ifT => //; exact: measurable_cst.
by move=> i; rewrite /G; case: ifP.
Qed.

(** Pointwise application of a random function to a random argument. *)
Lemma qbs_Mx_app (A B : qbsType R) (h : mR -> expQ A B) (a : mR -> A) :
  qbs_Mx h -> qbs_Mx a -> qbs_Mx (fun r => (h r : qbsHomType A B) (a r)).
Proof.
move=> hh ha.
have hh' : qbs_morphism (X := prodQ (realQ R) A) (Y := B)
    (fun p => (h p.1 : qbsHomType A B) p.2) := hh.
have hra : qbs_Mx (s := prodQ (realQ R) A) (fun r => (r, a r)).
  by split => //=; exact: measurable_id.
exact: hh' _ hra.
Qed.

(** Argument swap [(X => Y => Z) -> (Y => X => Z)]. *)
Section qbs_arg_swap.
Variables (X Y Z : qbsType R).

Let swap1 (f : qbsHomType X (expQ Y Z)) (y : Y) : qbsHomType X Z :=
  qbs_hom_of (f := fun x => (f x : qbsHomType Y Z) y)
    (fun a ha => qbs_Mx_app (qbs_hom_proof _ ha) (qbs_Mx_const y)).

Let swap2 (f : qbsHomType X (expQ Y Z)) : qbsHomType Y (expQ X Z) :=
  qbs_hom_of (f := swap1 f) (fun b hb a ha =>
    qbs_Mx_app (h := fun r => (f (a r).2 : qbsHomType Y Z))
      (qbs_hom_proof _ ha.2) (qbs_Mx_compT hb ha.1)).

Definition qbs_arg_swap :
    qbsHomType (expQ X (expQ Y Z)) (expQ Y (expQ X Z)) :=
  qbs_hom_of (f := fun f => swap2 f) (fun phi hphi b hb a ha =>
    qbs_Mx_app (h := fun r => (phi (b (a r).1).1 : qbsHomType X (expQ Y Z))
        (a r).2)
      (hphi (fun r => ((b (a r).1).1, (a r).2))
        (conj (measurableT_comp hb.1 ha.1) ha.2))
      (qbs_Mx_compT hb.2 ha.1)).

Lemma qbs_arg_swapE f y x : qbs_arg_swap f y x = f x y.
Proof. by []. Qed.

End qbs_arg_swap.

(** Internal composition [(X => Y) * (Y => Z) -> (X => Z)]. *)
Section qbs_exp_compose.
Variables (X Y Z : qbsType R).

Definition qbs_exp_compose :
    qbsHomType (prodQ (expQ X Y) (expQ Y Z)) (expQ X Z) :=
  qbs_hom_of (f := fun p => qbs_comp (p.1 : qbsHomType X Y)
      (p.2 : qbsHomType Y Z))
    (fun a ha b hb =>
      qbs_Mx_app (h := fun r => (a (b r).1).2 : qbsHomType Y Z)
        (qbs_Mx_compT (X := expQ Y Z) ha.2 hb.1)
        (qbs_Mx_app (h := fun r => (a (b r).1).1 : qbsHomType X Y)
          (qbs_Mx_compT (X := expQ X Y) ha.1 hb.1) hb.2)).

Lemma qbs_exp_composeE f g x :
  qbs_exp_compose (f, g) x = (g : qbsHomType Y Z) ((f : qbsHomType X Y) x).
Proof. by []. Qed.

End qbs_exp_compose.

(** Case analysis as an internal morphism
    [(X => Z) * (Y => Z) -> (X + Y => Z)]. *)
Section qbs_case_exp.
Variables (X Y Z : qbsType R).

Definition qbs_case (f : qbsHomType X Z) (g : qbsHomType Y Z) :
    qbsHomType (coprodQ X Y) Z :=
  qbs_hom_of (qbs_morphism_case (fun a ha => qbs_hom_proof (s := f) a ha)
    (fun a ha => qbs_hom_proof (s := g) a ha)).

Lemma qbs_case_inl f g x : qbs_case f g (inl x) = f x.
Proof. by []. Qed.

Lemma qbs_case_inr f g y : qbs_case f g (inr y) = g y.
Proof. by []. Qed.

Lemma qbs_case_exp_morphism :
  qbs_morphism (X := prodQ (expQ X Z) (expQ Y Z)) (Y := expQ (coprodQ X Y) Z)
    (fun p => qbs_case (p.1 : qbsHomType X Z) (p.2 : qbsHomType Y Z)).
Proof.
move=> a [ha1 ha2] b [hb1 hb2].
have h1 : qbs_Mx (s := expQ X Z) (fun r => (a (b r).1).1) :=
  qbs_Mx_compT ha1 hb1.
have h2 : qbs_Mx (s := expQ Y Z) (fun r => (a (b r).1).2) :=
  qbs_Mx_compT ha2 hb1.
change (qbs_Mx (s := Z)
  (fun r => qbs_case (a (b r).1).1 (a (b r).1).2 (b r).2)).
case: hb2 => [[c [hc e]] | [[d [hd e]] | [P [c [d [hP [hc [hd e]]]]]]]].
- have -> : (fun r => qbs_case (a (b r).1).1 (a (b r).1).2 (b r).2) =
      fun r => (a (b r).1).1 (c r) by apply/funext => r; rewrite /= e.
  exact: qbs_Mx_app h1 hc.
- have -> : (fun r => qbs_case (a (b r).1).1 (a (b r).1).2 (b r).2) =
      fun r => (a (b r).1).2 (d r) by apply/funext => r; rewrite /= e.
  exact: qbs_Mx_app h2 hd.
have -> : (fun r => qbs_case (a (b r).1).1 (a (b r).1).2 (b r).2) =
    fun r => if P r then (a (b r).1).1 (c r) else (a (b r).1).2 (d r).
  by apply/funext => r; rewrite /= e; case: (P r).
exact: qbs_Mx_if hP (qbs_Mx_app h1 hc) (qbs_Mx_app h2 hd).
Qed.

Definition qbs_case_exp : qbsHomType (prodQ (expQ X Z) (expQ Y Z))
    (expQ (coprodQ X Y) Z) :=
  qbs_hom_of qbs_case_exp_morphism.

Lemma qbs_case_expE f g s :
  qbs_case_exp (f, g) s = qbs_case f g s.
Proof. by []. Qed.

End qbs_case_exp.

(** Copairing with a parameter: a family of morphisms
    [W * X i -> Z] induces a morphism [W * sigmaQ X -> Z]. *)
Lemma qbs_morphism_sigma_case_prod (W Z : qbsType R) (X : nat -> qbsType R)
  (f : forall i, qbsHomType (prodQ W (X i)) Z) :
  qbs_morphism (X := prodQ W (sigmaQ X)) (Y := Z)
    (fun p => f (projT1 p.2) (p.1, projT2 p.2)).
Proof.
move=> a [hw hl].
pose g i (x : X i) : qbsHomType W Z := qbs_hom_of (f := fun w => f i (w, x))
  (fun c hc => qbs_hom_proof (s := f i) (fun r => (c r, x))
    (conj hc (qbs_Mx_const x))).
have hg i : qbs_morphism (X := X i) (Y := expQ W Z) (g i).
  move=> b hb c hc; exact: (qbs_hom_proof (s := f i)
    (fun r => ((c r).2, b (c r).1)) (conj hc.2 (qbs_Mx_compT hb hc.1))).
have hs := qbs_morphism_sigma_case (fun i => qbs_hom_of (hg i)) hl.
exact: (qbs_Mx_app (h := fun r => sigma_case (fun i => qbs_hom_of (hg i))
  (a r).2) hs hw).
Qed.

(** ## Lists
    [listQ X] has carrier [{n & 'I_n -> X}]; it is in bijection with
    [seq X], and [qbs_nil], [qbs_cons] and the recursor [list_rec] are
    morphisms. *)

Section qbs_list.
Variable X : qbsType R.

Definition list_mk n (a : 'I_n -> X) : listQ X :=
  existT (fun n => piQ 'I_n (fun=> X)) n a.

Definition seq_of_list (l : listQ X) : seq X :=
  [seq projT2 l i | i <- enum 'I_(projT1 l)].

Definition list_of_seq (s : seq X) : listQ X :=
  list_mk (fun i : 'I_(size s) => tnth (in_tuple s) i).

Lemma list_of_seqK : cancel list_of_seq seq_of_list.
Proof.
by move=> s; rewrite /seq_of_list /=; exact: map_tnth_enum (in_tuple s).
Qed.

Lemma list_mk_cast m n (e : m = n) (b : 'I_m -> X) (a : 'I_n -> X) :
  (forall i, b i = a (cast_ord e i)) -> list_mk b = list_mk a.
Proof.
case: n / e in a * => hb; congr list_mk; apply/funext => i.
by rewrite hb cast_ord_id.
Qed.

Lemma seq_of_listK : cancel seq_of_list list_of_seq.
Proof.
case=> n a; have hs : size (seq_of_list (list_mk a)) = n.
  by rewrite size_map size_enum_ord.
change (list_of_seq (seq_of_list (list_mk a)) = list_mk a).
rewrite /list_of_seq.
apply: (list_mk_cast (e := hs)) => i.
rewrite (tnth_nth (a (cast_ord hs i))) /seq_of_list /=.
have hi : i < n := ltn_ord (cast_ord hs i).
rewrite (nth_map (cast_ord hs i)) ?size_enum_ord //.
by congr (a _); apply: val_inj; exact: nth_enum_ord.
Qed.

Lemma nil_ord_proof (i : 'I_0) : False.
Proof. by case: i => m; rewrite ltn0. Qed.

Definition qbs_nil : listQ X := list_mk (fun i : 'I_0 => nosimpl
  (False_rect X (nil_ord_proof i))).

Definition ord_cons n (x : X) (a : 'I_n -> X) : 'I_n.+1 -> X :=
  fun i => oapp a x (unlift ord0 i).

Lemma ord_cons0 n x (a : 'I_n -> X) : ord_cons x a ord0 = x.
Proof. by rewrite /ord_cons unlift_none. Qed.

Lemma ord_consS n x (a : 'I_n -> X) i : ord_cons x a (lift ord0 i) = a i.
Proof. by rewrite /ord_cons liftK. Qed.

Definition list_cons (p : X * listQ X) : listQ X :=
  list_mk (ord_cons p.1 (projT2 p.2)).

Lemma qbs_morphism_cons :
  qbs_morphism (X := prodQ X (listQ X)) (Y := listQ X) list_cons.
Proof.
move=> a [hx [mi hl]]; split.
  exact: measurable_fun_addn (measurable_cst 1%N) mi.
move=> i [r0 hr0]; rewrite /= in hr0; subst i.
have [c hc e] := hl _ (ex_intro _ r0 erefl).
exists (fun r => ord_cons (a r).1 (c r)).
  move=> j; rewrite /ord_cons; case: (unlift ord0 j) => [k|] /=.
    exact: hc.
  exact: hx.
move=> r hr; have hn : projT1 (a r).2 = projT1 (a r0).2 := succn_inj hr.
by rewrite /list_cons /= (e r hn).
Qed.

Definition qbs_cons : qbsHomType (prodQ X (listQ X)) (listQ X) :=
  qbs_hom_of qbs_morphism_cons.

Lemma seq_of_list_nil : seq_of_list qbs_nil = [::].
Proof. by rewrite /seq_of_list /= enum_ord0. Qed.

Lemma seq_of_list_cons x l :
  seq_of_list (qbs_cons (x, l)) = x :: seq_of_list l.
Proof.
case: l => n a; rewrite /seq_of_list /= enum_ordSl /= ord_cons0.
by congr (_ :: _); rewrite -map_comp; apply: eq_map => i; exact: ord_consS.
Qed.

End qbs_list.

Arguments qbs_cons {X}.

(** Structural recursion on lists:
    [list_rec b f nil = b] and
    [list_rec b f (x :: l) = f x l (list_rec b f l)]. *)
Section qbs_list_rec.
Variables (X Y : qbsType R).

Fixpoint list_rec_ord (b : Y) (f : X -> listQ X -> Y -> Y) n :
    ('I_n -> X) -> Y :=
  match n with
  | 0 => fun _ => b
  | n.+1 => fun a => f (a ord0) (list_mk (a \o lift ord0))
      (list_rec_ord b f (a \o lift ord0))
  end.

Definition list_rec (b : Y) (f : X -> listQ X -> Y -> Y) (l : listQ X) : Y :=
  list_rec_ord b f (projT2 l).

Lemma list_rec_nil b f : list_rec b f (qbs_nil X) = b.
Proof. by []. Qed.

Lemma list_rec_cons b f x l :
  list_rec b f (qbs_cons (x, l)) = f x l (list_rec b f l).
Proof.
case: l => n a; rewrite /list_rec /= ord_cons0.
have -> : ord_cons x a \o lift ord0 = a by apply/funext => i; exact: ord_consS.
by [].
Qed.

(** Recursion is a morphism, uniformly in a parameter [w : W]. *)
Lemma qbs_morphism_list_rec_ord (W : qbsType R) (b : qbsHomType W Y)
  (F : qbsHomType (prodQ W (prodQ X (prodQ (listQ X) Y))) Y) n :
  qbs_morphism (X := prodQ W (piQ 'I_n (fun=> X))) (Y := Y)
    (fun p => list_rec_ord (b p.1) (fun x l y => F (p.1, (x, (l, y)))) p.2).
Proof.
elim: n => [|n IH] a [hw ha] /=.
  exact: (qbs_hom_proof (s := b) (fun r => (a r).1) hw).
have hl : qbs_Mx (s := piQ 'I_n (fun=> X)) (fun r => (a r).2 \o lift ord0).
  by move=> j; exact: (ha (lift ord0 j)).
apply: (qbs_hom_proof (s := F)
  (fun r => ((a r).1, ((a r).2 ord0, (list_mk ((a r).2 \o lift ord0),
    list_rec_ord (b (a r).1) (fun x l y => F ((a r).1, (x, (l, y))))
      ((a r).2 \o lift ord0)))))).
split => //; split; first exact: (ha ord0).
split; first exact: (qbs_morphism_sigma_inj
  (X := fun n => piQ 'I_n (fun=> X)) (i := n) hl).
exact: (IH (fun r => ((a r).1, (a r).2 \o lift ord0)) (conj hw hl)).
Qed.

Lemma qbs_morphism_list_rec (W : qbsType R) (b : qbsHomType W Y)
  (F : qbsHomType (prodQ W (prodQ X (prodQ (listQ X) Y))) Y) :
  qbs_morphism (X := prodQ W (listQ X)) (Y := Y)
    (fun p => list_rec (b p.1) (fun x l y => F (p.1, (x, (l, y)))) p.2).
Proof.
have h := qbs_morphism_sigma_case_prod
  (X := fun n => piQ 'I_n (fun=> X)) (fun n => qbs_hom_of
    (qbs_morphism_list_rec_ord b F (n := n))).
exact: h.
Qed.

(** External form: a base case and a morphism for the cons step. *)
Lemma qbs_morphism_list_rec_ext (b : Y)
  (f : qbsHomType (prodQ X (prodQ (listQ X) Y)) Y) :
  qbs_morphism (X := listQ X) (Y := Y)
    (list_rec b (fun x l y => f (x, (l, y)))).
Proof.
move=> a ha.
have hr : qbs_Mx (s := prodQ (unitQ R) (listQ X)) (fun r => (tt, a r)) :=
  conj I ha.
exact: (qbs_morphism_list_rec (W := unitQ R) (qbs_const _ b)
  (qbs_comp (qbs_snd _ _) f) hr).
Qed.

End qbs_list_rec.

(** Internal form (AFP [rec_list_morphism]): [list_rec_hom] is a morphism
    [Y => (X => listQ X => Y => Y) => listQ X => Y]. *)
Section qbs_list_rec_hom.
Variables (X Y : qbsType R).

Let step_ty := expQ X (expQ (listQ X) (expQ Y Y)).

Let list_step_proof : qbs_morphism
    (X := prodQ (prodQ Y step_ty) (prodQ X (prodQ (listQ X) Y))) (Y := Y)
    (fun p => (((p.1.2 : qbsHomType X (expQ (listQ X) (expQ Y Y))) p.2.1
      : qbsHomType (listQ X) (expQ Y Y)) p.2.2.1 : qbsHomType Y Y) p.2.2.2).
Proof.
move=> a [[hy he] [hx [hl hy']]].
have h1 := qbs_Mx_app (A := X) (B := expQ (listQ X) (expQ Y Y)) he hx.
have h2 := qbs_Mx_app (A := listQ X) (B := expQ Y Y) h1 hl.
exact: (qbs_Mx_app (A := Y) (B := Y) h2 hy').
Qed.

Let list_step : qbsHomType
    (prodQ (prodQ Y step_ty) (prodQ X (prodQ (listQ X) Y))) Y :=
  qbs_hom_of list_step_proof.

Let list_rec_uncurried : qbsHomType (prodQ (prodQ Y step_ty) (listQ X)) Y :=
  qbs_hom_of (qbs_morphism_list_rec (qbs_fst _ _) list_step).

Definition list_rec_hom :
    qbsHomType Y (expQ step_ty (expQ (listQ X) Y)) :=
  qbs_curry_morph (qbs_curry_morph list_rec_uncurried).

Lemma list_rec_homE b (f : step_ty) l :
  list_rec_hom b f l = list_rec b (fun x l' y => f x l' y) l.
Proof. by []. Qed.

End qbs_list_rec_hom.
End coproduct_qbs.
