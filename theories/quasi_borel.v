(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.classical Require Import classical_sets.
From mathcomp.analysis Require Import topology_theory.num_topology.
From mathcomp.analysis Require Import measure_theory.measurable_structure.
From mathcomp.analysis Require Import measure_theory.measurable_function.
From mathcomp.analysis Require Import borel_hierarchy.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measurable_realfun.

Import Num.Def Num.Theory reals classical_sets.
Import numFieldTopology.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(**md**************************************************************************)
(* # Quasi-Borel Spaces                                                       *)
(*                                                                            *)
(* Formalization following:                                                    *)
(* - "A Convenient Category for Higher-Order Probability Theory"              *)
(*   Heunen, Kammar, Staton, Yang (LICS 2017)                                *)
(* - Isabelle AFP: Quasi_Borel_Spaces by Hirata, Minamide, Sato              *)
(*                                                                            *)
(* Built on math-comp analysis (measurable types, measures, kernels)          *)
(*                                                                            *)
(* ```                                                                        *)
(*         qbsType R == type of quasi-Borel spaces over reals R               *)
(*   qbs_Mx alpha == alpha is a random element (in Mx)                        *)
(*   qbs_morphism X Y f == f is a QBS morphism from X to Y                    *)
(*   qbs_hom X Y == bundled QBS morphisms from X to Y                         *)
(*   R_qbs d M == QBS induced on measurableType M by measurable functions     *)
(*   realQ, natQ, boolQ == QBS on R, nat, bool via R_qbs                      *)
(*   prodQ X Y == binary product QBS on (X * Y)                               *)
(*   expQ X Y == exponential (function space) QBS on qbs_hom X Y              *)
(*   unitQ == terminal QBS on unit                                             *)
(*   sub_qbs X P == subspace QBS on {x : X | P x}                             *)
(*   generating_qbs G == smallest QBS containing generators G                  *)
(*   generating_Mx G == inductive closure of G under the QBS axioms            *)
(*   map_qbs f hf == image QBS on Y via morphism f : X -> Y                   *)
(*   sigma_Mx X == the sigma-algebra induced by the random elements of X      *)
(*   qbs_leT MxX MxY == order on QBS: set inclusion on random elements        *)
(*   qbs_supT MxX MxY == join (sup) of two QBS on the same carrier            *)
(*   qbs_morphism_eval == evaluation morphism (expQ X Y) x X -> Y             *)
(*   qbs_morphism_curry == currying morphism X -> expQ Y Z                     *)
(* ```                                                                        *)
(******************************************************************************)

HB.mixin Record isQBS (R : realType) (T : Type) := {
  qbs_Mx : set (measurableTypeR R -> T) ;
  qbs_Mx_comp : forall alpha f,
    qbs_Mx alpha -> measurable_fun setT f -> qbs_Mx (alpha \o f) ;
  qbs_Mx_const : forall x : T, qbs_Mx (fun _ => x) ;
  qbs_Mx_glue : forall (P : measurableTypeR R -> nat)
    (Fi : nat -> measurableTypeR R -> T),
    measurable_fun setT P ->
    (forall i, qbs_Mx (Fi i)) ->
    qbs_Mx (fun r => Fi (P r) r) ;
}.

#[short(type="qbsType")]
HB.structure Definition QBSpace (R : realType) := { T of isQBS R T }.

Section QBS.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* ----- 1. Morphisms ----- *)

Definition qbs_morphism (X Y : qbsType R) (f : X -> Y) : Prop :=
  forall alpha, @qbs_Mx R X alpha -> @qbs_Mx R Y (f \o alpha).

Record qbs_hom (X Y : qbsType R) := QBSHom {
  qbs_hom_val :> X -> Y ;
  qbs_hom_proof : forall alpha, @qbs_Mx R X alpha ->
    @qbs_Mx R Y (qbs_hom_val \o alpha) ;
}.

Arguments qbs_hom_val {X Y}.
Arguments qbs_hom_proof {X Y}.

Lemma qbs_morphism_id (X : qbsType R) : @qbs_morphism X X idfun.
Proof. by move=> alpha hα. Qed.

Lemma qbs_morphism_comp (X Y Z : qbsType R) (f : X -> Y) (g : Y -> Z) :
  @qbs_morphism X Y f -> @qbs_morphism Y Z g -> @qbs_morphism X Z (g \o f).
Proof. by move=> hf hg alpha hα; apply: hg; apply: hf. Qed.

Lemma qbs_morphism_const (X Y : qbsType R) (y : Y) :
  @qbs_morphism X Y (fun _ => y).
Proof. by move=> alpha _; apply: qbs_Mx_const. Qed.

(* ----- 2. The R functor: measurableType -> qbsType ----- *)

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

(* NB: manual QBSpace.Pack because R_qbs builds a non-canonical QBS on an
   existing measurableType *)
Definition R_qbs (d : measure_display) (M : measurableType d) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R M
      [set f : mR -> M | measurable_fun setT f]
      (fun alpha f (ha : measurable_fun setT alpha) hf =>
         measurableT_comp ha hf)
      (fun x => @measurable_cst _ _ mR M setT x)
      (fun P Fi hP hFi => @measurable_glue d M P Fi hP hFi))).

Definition realQ : qbsType R := R_qbs mR.
Definition natQ : qbsType R := R_qbs nat.
Definition boolQ : qbsType R := R_qbs bool.

(* ----- 3. Binary Product ----- *)

Lemma prodQ_Mx_comp (X Y : qbsType R) :
  forall alpha f,
    (@qbs_Mx R X (fst \o alpha) /\ @qbs_Mx R Y (snd \o alpha)) ->
    measurable_fun setT f ->
    (@qbs_Mx R X (fst \o (alpha \o f)) /\ @qbs_Mx R Y (snd \o (alpha \o f))).
Proof.
move=> alpha f [h1 h2] hf; split.
- have -> : fst \o (alpha \o f) = (fst \o alpha) \o f by [].
  exact: qbs_Mx_comp h1 hf.
- have -> : snd \o (alpha \o f) = (snd \o alpha) \o f by [].
  exact: qbs_Mx_comp h2 hf.
Qed.

Lemma prodQ_Mx_const (X Y : qbsType R) :
  forall xy : X * Y,
    @qbs_Mx R X (fst \o (fun _ : mR => xy)) /\
    @qbs_Mx R Y (snd \o (fun _ : mR => xy)).
Proof.
move=> [x y]; split.
- have -> : fst \o (fun _ : mR => (x, y)) = (fun _ => x) by [].
  exact: qbs_Mx_const.
- have -> : snd \o (fun _ : mR => (x, y)) = (fun _ => y) by [].
  exact: qbs_Mx_const.
Qed.

Lemma prodQ_Mx_glue (X Y : qbsType R) :
  forall (P : mR -> nat)
         (Fi : nat -> mR -> X * Y),
    measurable_fun setT P ->
    (forall i, @qbs_Mx R X (fst \o Fi i) /\ @qbs_Mx R Y (snd \o Fi i)) ->
    @qbs_Mx R X (fst \o (fun r => Fi (P r) r)) /\
    @qbs_Mx R Y (snd \o (fun r => Fi (P r) r)).
Proof.
move=> P Fi hP hFi; split.
- have -> : fst \o (fun r => Fi (P r) r) =
            (fun r => (fun i => fst \o Fi i) (P r) r) by [].
  apply: (@qbs_Mx_glue _ X P (fun i => fst \o Fi i)) => // i.
  by have [] := hFi i.
- have -> : snd \o (fun r => Fi (P r) r) =
            (fun r => (fun i => snd \o Fi i) (P r) r) by [].
  apply: (@qbs_Mx_glue _ Y P (fun i => snd \o Fi i)) => // i.
  by have [] := hFi i.
Qed.

(* NB: manual QBSpace.Pack because this is a non-canonical QBS on (X * Y)%type *)
Definition prodQ (X Y : qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (X * Y)%type
      [set f | @qbs_Mx R X (fst \o f) /\ @qbs_Mx R Y (snd \o f)]
      (@prodQ_Mx_comp X Y)
      (@prodQ_Mx_const X Y)
      (@prodQ_Mx_glue X Y))).

Arguments prodQ : clear implicits.

Lemma qbs_morphism_fst (X Y : qbsType R) : @qbs_morphism (prodQ X Y) X fst.
Proof. by move=> alpha [h1 h2]. Qed.

Lemma qbs_morphism_snd (X Y : qbsType R) : @qbs_morphism (prodQ X Y) Y snd.
Proof. by move=> alpha [h1 h2]. Qed.

Lemma qbs_morphism_pair (W X Y : qbsType R) (f : W -> X) (g : W -> Y) :
  @qbs_morphism W X f -> @qbs_morphism W Y g ->
  @qbs_morphism W (prodQ X Y) (fun w => (f w, g w)).
Proof.
by move=> hf hg alpha hα; split; [apply: hf | apply: hg].
Qed.

(* ----- 4. Exponential (Function Space) ----- *)

(* The carrier of expQ X Y is qbs_hom X Y (bundled morphisms).
   The random elements are those g : mR -> qbs_hom X Y such that
   the uncurried map (r, x) |-> g(r)(x) is a morphism prodQ realQ X -> Y. *)

Lemma expQ_Mx_comp (X Y : qbsType R) :
  forall alpha f,
    (@qbs_morphism (prodQ realQ X) Y
       (fun p : realQ * X => qbs_hom_val (alpha p.1) p.2)) ->
    measurable_fun setT f ->
    @qbs_morphism (prodQ realQ X) Y
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

Lemma expQ_Mx_const (X Y : qbsType R) :
  forall g : qbs_hom X Y,
    @qbs_morphism (prodQ realQ X) Y
      (fun p : realQ * X => qbs_hom_val ((fun _ : mR => g) p.1) p.2).
Proof.
move=> g beta [hb1 hb2].
have -> : (fun p : realQ * X => qbs_hom_val g p.2) \o beta =
          qbs_hom_val g \o (snd \o beta) by [].
exact: (qbs_hom_proof g) _ hb2.
Qed.

Lemma expQ_Mx_glue (X Y : qbsType R) :
  forall (P : mR -> nat) (Fi : nat -> mR -> qbs_hom X Y),
    measurable_fun setT P ->
    (forall i, @qbs_morphism (prodQ realQ X) Y
       (fun p : realQ * X => qbs_hom_val (Fi i p.1) p.2)) ->
    @qbs_morphism (prodQ realQ X) Y
      (fun p : realQ * X => qbs_hom_val ((fun r => Fi (P r) r) p.1) p.2).
Proof.
move=> P Fi hP hFi beta [hb1 hb2].
set Q := (fun r => P (fst (beta r))).
have hQ : measurable_fun setT Q.
  rewrite /Q; apply: measurableT_comp hP _; exact: hb1.
have -> : (fun p : realQ * X => Fi (P p.1) p.1 p.2) \o beta =
          (fun r => (fun i => (fun p : realQ * X => Fi i p.1 p.2) \o beta)
            (Q r) r) by [].
apply: (@qbs_Mx_glue _ Y Q
  (fun i => (fun p : realQ * X => Fi i p.1 p.2) \o beta) hQ).
move=> i; exact: hFi i _ (conj hb1 hb2).
Qed.

(* NB: manual QBSpace.Pack because this is a non-canonical QBS on (qbs_hom X Y) *)
Definition expQ (X Y : qbsType R) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R (qbs_hom X Y)
      [set g : mR -> qbs_hom X Y |
        @qbs_morphism (prodQ realQ X) Y
          (fun p : realQ * X => qbs_hom_val (g p.1) p.2)]
      (@expQ_Mx_comp X Y)
      (@expQ_Mx_const X Y)
      (@expQ_Mx_glue X Y))).

Arguments expQ : clear implicits.

(* ----- 5. Key Theorems: Cartesian Closure ----- *)

(* Evaluation morphism: (expQ X Y) x X -> Y *)
Lemma qbs_morphism_eval (X Y : qbsType R) :
  @qbs_morphism (prodQ (expQ X Y) X) Y (fun p => qbs_hom_val p.1 p.2).
Proof.
move=> beta [hb1 hb2].
have hmorph : @qbs_morphism (prodQ realQ X) Y
    (fun p : realQ * X => qbs_hom_val ((fst \o beta) p.1) p.2).
  exact: hb1.
set gamma := (fun r : mR => (r, snd (beta r))) : mR -> realQ * X.
have hgamma : @qbs_Mx R (prodQ realQ X) gamma.
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
Lemma prodQ_const_random (X Y : qbsType R) (x : X) (alpha : mR -> Y) :
  @qbs_Mx R Y alpha -> @qbs_Mx R (prodQ X Y) (fun r => (x, alpha r)).
Proof.
move=> hα; split => /=.
- have -> : fst \o (fun r : mR => (x, alpha r)) = (fun _ => x) by [].
  exact: qbs_Mx_const.
- have -> : snd \o (fun r : mR => (x, alpha r)) = alpha by [].
  exact: hα.
Qed.

(* Curry morphism: if f : prodQ X Y -> Z is morph, then curry(f) : X -> expQ Y Z *)
Lemma qbs_morphism_curry (X Y Z : qbsType R)
  (f : qbs_hom (prodQ X Y) Z) :
  @qbs_morphism X (expQ Y Z)
    (fun x => @QBSHom Y Z (fun y => f (x, y))
       (fun alpha hα => qbs_hom_proof f _
          (prodQ_const_random x hα))).
Proof.
move=> beta hbeta /= gamma [hg1 hg2].
apply: (qbs_hom_proof f); split => /=.
- have -> : fst \o (fun x : mR => (beta (gamma x).1, (gamma x).2)) =
            beta \o (fst \o gamma) by [].
  exact: qbs_Mx_comp hbeta hg1.
- have -> : snd \o (fun x : mR => (beta (gamma x).1, (gamma x).2)) =
            snd \o gamma by [].
  exact: hg2.
Qed.

(* ----- 6. Unit QBS ----- *)

(* NB: manual QBSpace.Pack because this is a non-canonical QBS on unit *)
Definition unitQ : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R unit
      [set _ : mR -> unit | True]
      (fun _ _ _ _ => I)
      (fun _ => I)
      (fun _ _ _ _ => I))).

(* Unit is terminal: unique morphism to unit *)
Lemma qbs_morphism_unit (X : qbsType R) :
  @qbs_morphism X unitQ (fun _ => tt).
Proof. by move=> alpha _. Qed.

(* ----- 7. sigma_Mx: the induced sigma-algebra ----- *)

Definition sigma_Mx (X : qbsType R) : set (set X) :=
  [set U | forall alpha, @qbs_Mx R X alpha ->
    measurable (alpha @^-1` U)].

Lemma sigma_Mx_setT (X : qbsType R) : @sigma_Mx X setT.
Proof. by move=> alpha _; exact: measurableT. Qed.

Lemma sigma_Mx_setC (X : qbsType R) (U : set X) :
  @sigma_Mx X U -> @sigma_Mx X (~` U).
Proof.
move=> hU alpha halpha.
rewrite preimage_setC.
exact: measurableC (hU _ halpha).
Qed.

Lemma sigma_Mx_bigcup (X : qbsType R) (F : nat -> set X) :
  (forall i, @sigma_Mx X (F i)) ->
  @sigma_Mx X (\bigcup_i F i).
Proof.
move=> hF alpha halpha.
rewrite preimage_bigcup.
exact: bigcup_measurable (fun i _ => hF i _ halpha).
Qed.

(* ----- 8. Comparison Morphisms ----- *)
(* Standard operations on R, nat, bool that are measurable are automatically
   QBS morphisms, since R_qbs sends measurable functions to morphisms. *)

(* Addition is a QBS morphism prodQ realQ realQ -> realQ *)
Lemma qbs_morphism_add :
  @qbs_morphism (prodQ realQ realQ) realQ (fun p => (p.1 + p.2)%R).
Proof.
move=> alpha [h1 h2] /=; exact: measurable_funD h1 h2.
Qed.

(* Multiplication is a QBS morphism prodQ realQ realQ -> realQ *)
Lemma qbs_morphism_mul :
  @qbs_morphism (prodQ realQ realQ) realQ (fun p => (p.1 * p.2)%R).
Proof.
move=> alpha [h1 h2] /=; exact: measurable_funM h1 h2.
Qed.

(* Less-than comparison: realQ x realQ -> boolQ *)
Lemma qbs_morphism_ltr :
  @qbs_morphism (prodQ realQ realQ) boolQ (fun p => (p.1 < p.2)%R).
Proof.
move=> alpha [h1 h2] /=; exact: measurable_fun_ltr h1 h2.
Qed.

(* Negation on bool *)
Lemma qbs_morphism_negb :
  @qbs_morphism boolQ boolQ negb.
Proof.
move=> alpha ha /=; exact: measurable_neg ha.
Qed.

(* ===================================================================== *)
(* Extensions: Subspaces, Generating sets, Structural morphisms          *)
(* ===================================================================== *)

(* ----- 9. Subspace QBS ----- *)
(* Given a QBS X and a predicate P on X, the subspace sub_qbs X P has
   carrier {x : X | P x} and random elements alpha such that
   proj1_sig \o alpha is random in X. *)

Section sub_qbs_def.
Variable (X : qbsType R) (P : set X).

Let sub_car := {x : X | P x}.
Let sub_proj : sub_car -> X := @proj1_sig _ P.

Let sub_Mx : set (mR -> sub_car) :=
  [set alpha | @qbs_Mx R X (sub_proj \o alpha)].

Lemma sub_qbs_closed1 : forall alpha f,
  sub_Mx alpha -> measurable_fun setT f -> sub_Mx (alpha \o f).
Proof.
move=> alpha f halpha hf; rewrite /sub_Mx /=.
have -> : sub_proj \o (alpha \o f) = (sub_proj \o alpha) \o f by [].
exact: qbs_Mx_comp halpha hf.
Qed.

Lemma sub_qbs_closed2 : forall x : sub_car,
  sub_Mx (fun _ => x).
Proof.
move=> x; rewrite /sub_Mx /=.
have -> : sub_proj \o (fun _ : mR => x) = (fun _ => sub_proj x) by [].
exact: qbs_Mx_const.
Qed.

Lemma sub_qbs_closed3 : forall (Q : mR -> nat) (Fi : nat -> mR -> sub_car),
  measurable_fun setT Q ->
  (forall i, sub_Mx (Fi i)) ->
  sub_Mx (fun r => Fi (Q r) r).
Proof.
move=> Q Fi hQ hFi; rewrite /sub_Mx /=.
have -> : sub_proj \o (fun r => Fi (Q r) r) =
          (fun r => (fun i r => sub_proj (Fi i r)) (Q r) r) by [].
exact: (@qbs_Mx_glue _ X Q (fun i r => sub_proj (Fi i r)) hQ (fun i => hFi i)).
Qed.

(* NB: manual QBSpace.Pack because this is a non-canonical QBS on {x : X | P x} *)
Definition sub_qbs : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R sub_car sub_Mx
      sub_qbs_closed1 sub_qbs_closed2 sub_qbs_closed3)).

End sub_qbs_def.

(* ----- 10. Generating QBS ----- *)
(* Given a set G of functions R -> X, generate the smallest QBS
   containing G by closing under the three QBS axioms. *)

Inductive generating_Mx (T : Type) (G : set (mR -> T))
  : (mR -> T) -> Prop :=
  | gen_base : forall alpha, G alpha -> generating_Mx G alpha
  | gen_comp : forall alpha f,
      generating_Mx G alpha ->
      measurable_fun setT f ->
      generating_Mx G (alpha \o f)
  | gen_const : forall x : T, generating_Mx G (fun _ => x)
  | gen_glue : forall (P : mR -> nat) (Fi : nat -> mR -> T),
      measurable_fun setT P ->
      (forall i, generating_Mx G (Fi i)) ->
      generating_Mx G (fun r => Fi (P r) r).

(* NB: manual QBSpace.Pack because this is a non-canonical QBS on T *)
Definition generating_qbs (T : Type) (G : set (mR -> T)) : qbsType R :=
  QBSpace.Pack (QBSpace.Class
    (@isQBS.Build R T (generating_Mx G)
      (fun alpha f ha hf => gen_comp ha hf)
      (fun x => gen_const G x)
      (fun P Fi hP hFi => gen_glue hP hFi))).

Lemma generating_qbs_incl (T : Type) (G : set (mR -> T)) :
  G `<=` @qbs_Mx R (generating_qbs G).
Proof. by move=> alpha hα; exact: gen_base. Qed.

(* ----- 11. Product swap and associators ----- *)

Lemma qbs_morphism_swap (X Y : qbsType R) :
  @qbs_morphism (prodQ X Y) (prodQ Y X) (fun p => (p.2, p.1)).
Proof.
move=> alpha [h1 h2]; split => /=.
- have -> : fst \o (fun r : mR => ((alpha r).2, (alpha r).1)) =
            snd \o alpha by [].
  exact: h2.
- have -> : snd \o (fun r : mR => ((alpha r).2, (alpha r).1)) =
            fst \o alpha by [].
  exact: h1.
Qed.

Lemma qbs_morphism_assoc_lr (X Y Z : qbsType R) :
  @qbs_morphism (prodQ (prodQ X Y) Z) (prodQ X (prodQ Y Z))
    (fun p => (p.1.1, (p.1.2, p.2))).
Proof.
move=> alpha [h12 h3].
have h12' : @qbs_Mx R (prodQ X Y) (fst \o alpha) by exact: h12.
have [h1 h2] := h12'.
split => /=.
- have -> : fst \o (fun r : mR => ((fst (alpha r)).1, ((fst (alpha r)).2, (alpha r).2))) =
            fst \o (fst \o alpha) by [].
  exact: h1.
- split => /=.
  + have -> : fst \o (snd \o (fun r : mR => ((fst (alpha r)).1, ((fst (alpha r)).2, (alpha r).2)))) =
              snd \o (fst \o alpha) by [].
    exact: h2.
  + have -> : snd \o (snd \o (fun r : mR => ((fst (alpha r)).1, ((fst (alpha r)).2, (alpha r).2)))) =
              snd \o alpha by [].
    exact: h3.
Qed.

Lemma qbs_morphism_assoc_rl (X Y Z : qbsType R) :
  @qbs_morphism (prodQ X (prodQ Y Z)) (prodQ (prodQ X Y) Z)
    (fun p => ((p.1, p.2.1), p.2.2)).
Proof.
move=> alpha [h1 h23].
have h23' : @qbs_Mx R (prodQ Y Z) (snd \o alpha) by exact: h23.
have [h2 h3] := h23'.
split => /=.
- split => /=.
  + have -> : fst \o (fst \o (fun r : mR => (((alpha r).1, (snd (alpha r)).1), (snd (alpha r)).2))) =
              fst \o alpha by [].
    exact: h1.
  + have -> : snd \o (fst \o (fun r : mR => (((alpha r).1, (snd (alpha r)).1), (snd (alpha r)).2))) =
              fst \o (snd \o alpha) by [].
    exact: h2.
- have -> : snd \o (fun r : mR => (((alpha r).1, (snd (alpha r)).1), (snd (alpha r)).2)) =
            snd \o (snd \o alpha) by [].
  exact: h3.
Qed.

(* ----- 12. Exponential morphisms ----- *)

(* Helper: random element paired with constant is random in product *)
Lemma prodQ_random_const (X Y : qbsType R) (alpha : mR -> X) (y : Y) :
  @qbs_Mx R X alpha -> @qbs_Mx R (prodQ X Y) (fun r => (alpha r, y)).
Proof.
move=> hα; split => /=.
- have -> : fst \o (fun r : mR => (alpha r, y)) = alpha by [].
  exact: hα.
- have -> : snd \o (fun r : mR => (alpha r, y)) = (fun _ => y) by [].
  exact: qbs_Mx_const.
Qed.

(* Application/evaluation composed with pairing: given f : W -> expQ X Y
   and g : W -> X, the map w |-> f(w)(g(w)) is a morphism W -> Y *)
Lemma qbs_morphism_exp_comp (W X Y : qbsType R)
  (f : qbs_hom W (expQ X Y)) (g : qbs_hom W X) :
  @qbs_morphism W Y (fun w => qbs_hom_val (f w) (g w)).
Proof.
move=> alpha halpha.
have hf_alpha : @qbs_Mx R (expQ X Y) (f \o alpha).
  exact: (qbs_hom_proof f) _ halpha.
have hg_alpha : @qbs_Mx R X (g \o alpha).
  exact: (qbs_hom_proof g) _ halpha.
set beta := (fun r : mR => (r, g (alpha r))) : mR -> realQ * X.
have hbeta : @qbs_Mx R (prodQ realQ X) beta.
  split => /=.
  - have -> : fst \o beta = idfun by [].
    exact: measurable_id.
  - have -> : snd \o beta = g \o alpha by [].
    exact: hg_alpha.
have := hf_alpha beta hbeta.
have -> : (fun p : realQ * X => qbs_hom_val ((f \o alpha) p.1) p.2) \o beta =
          (fun r => qbs_hom_val (f (alpha r)) (g (alpha r))) by [].
by [].
Qed.

(* Argument swap: given f : X -> expQ Y Z, construct the morphism
   Y -> expQ X Z sending y to (x |-> f(x)(y)). *)
Lemma qbs_morphism_arg_swap (X Y Z : qbsType R) (f : qbs_hom X (expQ Y Z)) :
  @qbs_morphism Y (expQ X Z)
    (fun y => @QBSHom X Z (fun x => qbs_hom_val (f x) y)
       (fun alpha halpha =>
          ((qbs_hom_proof f alpha halpha) :
             @qbs_morphism (prodQ realQ Y) Z
               (fun p : realQ * Y => qbs_hom_val ((f \o alpha) p.1) p.2))
          (fun r : mR => (r, y))
          (conj (@measurable_id _ mR setT) (qbs_Mx_const y))
       )).
Proof.
move=> beta hbeta /= gamma [hg1 hg2].
have hf_sg : @qbs_Mx R (expQ Y Z) (f \o (snd \o gamma)).
  exact: (qbs_hom_proof f) _ hg2.
have hbfg : @qbs_Mx R Y (beta \o (fst \o gamma)).
  exact: qbs_Mx_comp hbeta hg1.
set delta := (fun r : mR => (r, beta ((fst \o gamma) r))) : mR -> realQ * Y.
have hdelta : @qbs_Mx R (prodQ realQ Y) delta.
  split => /=.
  - have -> : fst \o delta = idfun by [].
    exact: measurable_id.
  - have -> : snd \o delta = beta \o (fst \o gamma) by [].
    exact: hbfg.
have := hf_sg delta hdelta.
have -> : (fun p : realQ * Y => qbs_hom_val ((f \o (snd \o gamma)) p.1) p.2) \o delta =
          (fun r : mR => qbs_hom_val (f (snd (gamma r))) (beta ((fst \o gamma) r))) by [].
have -> : (fun p : realQ * X => (fun x : X => qbs_hom_val (f x) (beta p.1)) p.2) \o gamma =
          (fun r : mR => qbs_hom_val (f (snd (gamma r))) (beta ((fst \o gamma) r))) by [].
by [].
Qed.

(* ----- 13. Image QBS (map_qbs) ----- *)
(* Given a QBS morphism f : X -> Y, the image QBS map_qbs f X has
   carrier Y and random elements generated by {f \o alpha | alpha in Mx(X)}.
   This uses generating_qbs to close under the three QBS axioms,
   ensuring all constant functions are included even if f is not surjective. *)

Definition map_qbs (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism X Y f) : qbsType R :=
  generating_qbs [set beta : mR -> Y |
    exists alpha, @qbs_Mx R X alpha /\ beta = f \o alpha].

Lemma map_qbs_random (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism X Y f) (alpha : mR -> X) :
  @qbs_Mx R X alpha -> @qbs_Mx R (map_qbs hf) (f \o alpha).
Proof.
move=> halpha; apply: gen_base; exists alpha; split => //.
Qed.

(* map_qbs is coarser than Y: every random element of map_qbs f X
   is also a random element of Y. *)
Lemma map_qbs_sub (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism X Y f) :
  forall beta, @qbs_Mx R (map_qbs hf) beta -> @qbs_Mx R Y beta.
Proof.
move=> beta; elim => {beta}.
- move=> beta [alpha [halpha ->]]; exact: hf _ halpha.
- move=> alpha g _ hIH hg; exact: qbs_Mx_comp hIH hg.
- move=> x; exact: qbs_Mx_const.
- move=> P Fi hP hFi IH; exact: qbs_Mx_glue hP IH.
Qed.

(* map_qbs is functorial: identity *)
Lemma map_qbs_morph_id (X Y Z : qbsType R) (f : X -> Y) (g : Y -> Z)
  (hf : @qbs_morphism X Y f) (hg : @qbs_morphism Y Z g) :
  @qbs_morphism (map_qbs hf) Z g.
Proof.
move=> beta hbeta.
have hbY := map_qbs_sub hbeta.
exact: hg _ hbY.
Qed.

(* The defining map f is a morphism from X to map_qbs f X *)
Lemma map_qbs_morph_from (X Y : qbsType R) (f : X -> Y)
  (hf : @qbs_morphism X Y f) :
  @qbs_morphism X (map_qbs hf) f.
Proof.
move=> alpha halpha; exact: map_qbs_random halpha.
Qed.

(* ----- 14. Order Structure on QBS ----- *)
(* Following Isabelle's order on QBS spaces:
   X <= Y iff Mx(X) <= Mx(Y) (for QBS with the same carrier type).
   More random elements = less restrictive structure = higher in the order.

   In our type-theoretic setting, the order is most naturally expressed
   between QBS with the same carrier type T. We define qbs_leT as
   set inclusion on random elements. *)

Section qbs_order.
Variable (T : Type).

(* X <= Y iff Mx(X) <= Mx(Y) *)
Definition qbs_leT (MxX MxY : set (mR -> T)) : Prop :=
  MxX `<=` MxY.

Lemma qbs_leT_refl (Mx : set (mR -> T)) :
  qbs_leT Mx Mx.
Proof. by move=> alpha. Qed.

Lemma qbs_leT_trans (Mx1 Mx2 Mx3 : set (mR -> T)) :
  qbs_leT Mx1 Mx2 -> qbs_leT Mx2 Mx3 -> qbs_leT Mx1 Mx3.
Proof. by move=> h12 h23 alpha /h12 /h23. Qed.

Lemma qbs_leT_antisym (Mx1 Mx2 : set (mR -> T)) :
  qbs_leT Mx1 Mx2 -> qbs_leT Mx2 Mx1 -> Mx1 = Mx2.
Proof.
move=> h12 h21; rewrite eqEsubset; split => alpha h.
- exact: h12.
- exact: h21.
Qed.

End qbs_order.

(* Generating QBS is the smallest QBS containing a set of generators *)
Lemma generating_qbs_least (T : Type) (G : set (mR -> T)) (Mx : set (mR -> T))
  (c1 : forall alpha f, Mx alpha -> measurable_fun setT f -> Mx (alpha \o f))
  (c2 : forall x : T, Mx (fun _ => x))
  (c3 : forall (P : mR -> nat) (Fi : nat -> mR -> T),
    measurable_fun setT P -> (forall i, Mx (Fi i)) -> Mx (fun r => Fi (P r) r)) :
  G `<=` Mx -> generating_Mx G `<=` Mx.
Proof.
move=> hG beta hbeta; elim: hbeta.
- move=> alpha hGa; exact: hG _ hGa.
- move=> alpha f _ hIH hf; exact: c1 hIH hf.
- move=> x; exact: c2.
- move=> P Fi hP hFi IH; exact: c3 hP IH.
Qed.

(* Sup (join) of two sets of random elements on the same type:
   Mx(sup) is the generating closure of their union. *)
Definition qbs_supT (T : Type) (MxX MxY : set (mR -> T)) : qbsType R :=
  generating_qbs [set alpha : mR -> T | MxX alpha \/ MxY alpha].

(* Left inclusion: MxX <= Mx(sup) *)
Lemma qbs_supT_ub_l (T : Type) (MxX MxY : set (mR -> T)) :
  qbs_leT MxX (@qbs_Mx R (qbs_supT MxX MxY)).
Proof.
move=> alpha halpha; apply: gen_base; left; exact: halpha.
Qed.

(* Right inclusion: MxY <= Mx(sup) *)
Lemma qbs_supT_ub_r (T : Type) (MxX MxY : set (mR -> T)) :
  qbs_leT MxY (@qbs_Mx R (qbs_supT MxX MxY)).
Proof.
move=> alpha halpha; apply: gen_base; right; exact: halpha.
Qed.

(* The sup is the least upper bound among QBS-closed sets *)
Lemma qbs_supT_least (T : Type) (MxX MxY MxZ : set (mR -> T))
  (c1 : forall alpha f, MxZ alpha -> measurable_fun setT f -> MxZ (alpha \o f))
  (c2 : forall x : T, MxZ (fun _ => x))
  (c3 : forall (P : mR -> nat) (Fi : nat -> mR -> T),
    measurable_fun setT P -> (forall i, MxZ (Fi i)) -> MxZ (fun r => Fi (P r) r)) :
  qbs_leT MxX MxZ ->
  qbs_leT MxY MxZ ->
  qbs_leT (@qbs_Mx R (qbs_supT MxX MxY)) MxZ.
Proof.
move=> hX hY.
apply: generating_qbs_least c1 c2 c3 _.
by move=> alpha /= -[/hX | /hY].
Qed.

End QBS.

Arguments QBSHom {R X Y}.
Arguments qbs_hom_val {R X Y}.
Arguments qbs_hom_proof {R X Y}.
