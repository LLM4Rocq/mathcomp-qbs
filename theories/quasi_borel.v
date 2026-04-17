(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals classical_sets
  num_topology measurable_structure measurable_function
  lebesgue_stieltjes_measure measurable_realfun.

(**md**************************************************************************)
(* # Quasi-Borel Spaces                                                       *)
(*                                                                            *)
(* Formalization following:                                                   *)
(* - "A Convenient Category for Higher-Order Probability Theory"              *)
(*   Heunen, Kammar, Staton, Yang (LICS 2017)                                 *)
(* - Isabelle AFP: Quasi_Borel_Spaces by Hirata, Minamide, Sato               *)
(*                                                                            *)
(* Built on math-comp analysis (measurable types, measures, kernels)          *)
(*                                                                            *)
(* ```                                                                        *)
(*         qbsType R == type of quasi-Borel spaces over reals R               *)
(*   qbs_Mx alpha == alpha is a random element (in Mx)                        *)
(*   qbs_morphism X Y f == f is a QBS morphism from X to Y                    *)
(*   qbsHomType R X Y == bundled QBS morphisms from X to Y (HB structure)     *)
(*   R_qbs d M == QBS induced on measurableType M by measurable functions     *)
(*   realQ, natQ, boolQ == QBS on R, nat, bool via R_qbs                      *)
(*   prodQ X Y == binary product QBS on (X * Y)                               *)
(*   expQ X Y == exponential (function space) QBS on qbsHomType R X Y         *)
(*   unitQ == terminal QBS on unit                                            *)
(*   sub_qbs X P == subspace QBS on {x : X | P x}                             *)
(*   generating_qbs G == smallest QBS containing generators G                 *)
(*   generating_Mx G == inductive closure of G under the QBS axioms           *)
(*   map_qbs f hf == image QBS on Y via morphism f : X -> Y                   *)
(*   sigma_Mx X == the sigma-algebra induced by the random elements of X      *)
(*   qbs_leT MxX MxY == order on QBS: set inclusion on random elements        *)
(*   qbs_supT MxX MxY == join (sup) of two QBS on the same carrier            *)
(*   qbs_id X == bundled identity morphism X -> X                             *)
(*   qbs_comp f g == bundled composition of morphisms g \o f                  *)
(*   qbs_const X y == bundled constant morphism X -> Y                        *)
(*   qbs_fst X Y == bundled first projection prodQ X Y -> X                   *)
(*   qbs_snd X Y == bundled second projection prodQ X Y -> Y                  *)
(*   qbs_pair f g == bundled pairing W -> prodQ X Y                           *)
(*   qbs_eval X Y == bundled evaluation prodQ (expQ X Y) X -> Y               *)
(*   qbs_unit X == bundled terminal morphism X -> unitQ                       *)
(*   qbs_add == bundled addition prodQ realQ realQ -> realQ                   *)
(*   qbs_mul == bundled multiplication prodQ realQ realQ -> realQ             *)
(*   qbs_curry f == bundled curried morphism Y -> Z from f : prodQ X Y -> Z   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Mixin: a QBS is a type with a set of random elements. *)
HB.mixin Record isQBS (R : realType) (T : Type) := {
  qbs_Mx : set (measurableTypeR R -> T) ;
  qbs_Mx_comp : forall alpha
    (f : {mfun measurableTypeR R >-> measurableTypeR R}),
    qbs_Mx alpha -> qbs_Mx (alpha \o f) ;
  qbs_Mx_const : forall x : T, qbs_Mx (fun _ => x) ;
  qbs_Mx_glue : forall (P : {mfun measurableTypeR R >-> nat})
    (Fi : nat -> measurableTypeR R -> T),
    (forall i, qbs_Mx (Fi i)) ->
    qbs_Mx (fun r => Fi (P r) r) }.

(** Structure: a quasi-Borel space over reals R. *)
#[short(type="qbsType")]
HB.structure Definition QBSpace (R : realType) := { T of isQBS R T }.

HB.mixin Record isQBSMorphism (R : realType) (X Y : qbsType R)
    (f : X -> Y) := {
  qbs_hom_proof : forall alpha, @qbs_Mx R X alpha ->
    @qbs_Mx R Y (f \o alpha)
}.

#[short(type="qbsHomType")]
HB.structure Definition QBSHom (R : realType) (X Y : qbsType R) :=
  {f of @isQBSMorphism R X Y f}.

Section qbs.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(* 1. Morphisms *)

(** QBS morphism: preserves random elements. *)
Definition qbs_morphism (X Y : qbsType R) (f : X -> Y) : Prop :=
  forall alpha, qbs_Mx alpha -> qbs_Mx (f \o alpha).

Section qbs_id_instance.
Variable (X : qbsType R).
Let f : X -> X := idfun.
Let hf : qbs_morphism f := fun alpha halpha => halpha.
HB.instance Definition _ := @isQBSMorphism.Build R X X f hf.
Definition qbs_id : qbsHomType X X := f.
End qbs_id_instance.

Section qbs_comp_instance.
Variables (X Y Z : qbsType R).
Variable (f : qbsHomType X Y) (g : qbsHomType Y Z).
Let gf := (g : Y -> Z) \o (f : X -> Y).
Let hgf : qbs_morphism gf :=
  fun alpha halpha =>
    qbs_hom_proof _ (qbs_hom_proof _ halpha).
HB.instance Definition _ := @isQBSMorphism.Build R X Z gf hgf.
Definition qbs_comp : qbsHomType X Z := gf.
End qbs_comp_instance.

Section qbs_const_instance.
Variables (X Y : qbsType R) (y : Y).
Let f := fun _ : X => y.
Let hf : qbs_morphism f :=
  fun alpha _ => qbs_Mx_const y.
HB.instance Definition _ := @isQBSMorphism.Build R X Y f hf.
Definition qbs_const : qbsHomType X Y := f.
End qbs_const_instance.

(** Convenience wrappers: accept bare [measurable_fun setT] proofs. *)

Lemma qbs_Mx_compT (X : qbsType R) alpha (f : mR -> mR) :
  @qbs_Mx R X alpha -> measurable_fun setT f -> @qbs_Mx R X (alpha \o f).
Proof.
by move=> ha hf; exact: (@qbs_Mx_comp _ X alpha (mfun_Sub (mem_set hf)) ha).
Qed.

Lemma qbs_Mx_glueT (X : qbsType R)
    (P : mR -> nat) (Fi : nat -> mR -> X) :
  measurable_fun setT P ->
  (forall i, qbs_Mx (Fi i)) ->
  qbs_Mx (fun r => Fi (P r) r).
Proof.
by move=> hP hFi; exact: (@qbs_Mx_glue _ X (mfun_Sub (mem_set hP)) Fi hFi).
Qed.

(* 2. The R functor: measurableType -> qbsType *)

Lemma measurable_glue d (M : measurableType d)
  (P : mR -> nat) (Fi : nat -> mR -> M) :
  measurable_fun setT P ->
  (forall i, measurable_fun setT (Fi i)) ->
  measurable_fun setT (fun r => Fi (P r) r).
Proof.
move=> hP hFi _ U mU; rewrite setTI.
have -> : (fun r => Fi (P r) r) @^-1` U =
          \bigcup_i (P @^-1` [set i] `&` (Fi i) @^-1` U).
  rewrite eqEsubset; split => [r hUr | r [i _ [hPi hFir]]].
  - by exists (P r).
  - by rewrite /preimage /=; rewrite /preimage /= in hPi; rewrite hPi.
apply: bigcupT_measurable => i; apply: measurableI.
- by have := hP measurableT [set i] I; rewrite setTI; exact.
- by have := hFi i measurableT U mU; rewrite setTI; exact.
Qed.

Section R_qbs_instance.
Context d (M : measurableType d).
Let Mx := [set f : mR -> M | measurable_fun setT f].
Let ax1 : forall alpha (f : {mfun mR >-> mR}),
    Mx alpha -> Mx (alpha \o f).
Proof.
move=> alpha f ha; rewrite /Mx /=.
exact: measurableT_comp.
Qed.
Let ax2 : forall x : M, Mx (fun _ => x).
Proof. by move=> x; rewrite /Mx /=; exact: measurable_cst. Qed.
Let ax3 : forall (P : {mfun mR >-> nat}) (Fi : nat -> mR -> M),
    (forall i, Mx (Fi i)) -> Mx (fun r => Fi (P r) r).
Proof.
move=> P Fi hFi; rewrite /Mx /=.
exact: measurable_glue.
Qed.
HB.instance Definition _ := @isQBS.Build R M Mx ax1 ax2 ax3.
(** R functor: measurableType to qbsType via measurable funs. *)
Definition R_qbs : qbsType R := M.
End R_qbs_instance.

(** Concrete QBS instances for R, nat, bool. *)
Definition realQ : qbsType R := R_qbs mR.
Definition natQ : qbsType R := R_qbs nat.
Definition boolQ : qbsType R := R_qbs bool.

(* 3. Binary Product *)

Lemma prodQ_Mx_comp (X Y : qbsType R) :
  forall alpha (f : {mfun mR >-> mR}),
    (@qbs_Mx R X (fun r => (alpha r).1) /\
     @qbs_Mx R Y (fun r => (alpha r).2)) ->
    (@qbs_Mx R X (fun r => ((alpha \o f) r).1) /\
     @qbs_Mx R Y (fun r => ((alpha \o f) r).2)).
Proof.
move=> alpha f [h1 h2]; split.
- have -> : (fun r => ((alpha \o f) r).1) = (fun r => (alpha r).1) \o f by [].
  exact: qbs_Mx_comp h1.
- have -> : (fun r => ((alpha \o f) r).2) = (fun r => (alpha r).2) \o f by [].
  exact: qbs_Mx_comp h2.
Qed.

Lemma prodQ_Mx_const (X Y : qbsType R) :
  forall xy : X * Y,
    @qbs_Mx R X (fun _ : mR => xy.1) /\
    @qbs_Mx R Y (fun _ : mR => xy.2).
Proof.
by move=> [x y]; split; exact: qbs_Mx_const.
Qed.

Lemma prodQ_Mx_glue (X Y : qbsType R) :
  forall (P : {mfun mR >-> nat})
         (Fi : nat -> mR -> X * Y),
    (forall i, @qbs_Mx R X (fun r => (Fi i r).1) /\
               @qbs_Mx R Y (fun r => (Fi i r).2)) ->
    @qbs_Mx R X (fun r => (Fi (P r) r).1) /\
    @qbs_Mx R Y (fun r => (Fi (P r) r).2).
Proof.
move=> P Fi hFi; split.
- apply: (qbs_Mx_glue P (fun i r => (Fi i r).1)) => i.
  by have [] := hFi i.
- apply: (qbs_Mx_glue P (fun i r => (Fi i r).2)) => i.
  by have [] := hFi i.
Qed.

Section prodQ_instance.
Variables (X Y : qbsType R).
(* NB: We use (fun r => (f r).1) instead of (fst \o f) to avoid a universe
   constraint on Composition.u2 that would conflict with algebra_tactics.ring *)
HB.instance Definition _ :=
  @isQBS.Build R (X * Y)%type
    [set f | @qbs_Mx R X (fun r => (f r).1) /\
             @qbs_Mx R Y (fun r => (f r).2)]
    (@prodQ_Mx_comp X Y)
    (@prodQ_Mx_const X Y)
    (@prodQ_Mx_glue X Y).
(** Binary product QBS on (X * Y). *)
Definition prodQ : qbsType R := (X * Y)%type.
End prodQ_instance.

Arguments prodQ : clear implicits.

Section qbs_fst_instance.
Variables (X Y : qbsType R).
Let f : X * Y -> X := fst.
Let hf : qbs_morphism f :=
  fun alpha h => h.1.
HB.instance Definition _ :=
  @isQBSMorphism.Build R (prodQ X Y) X f hf.
Definition qbs_fst : qbsHomType (prodQ X Y) X := f.
End qbs_fst_instance.

Section qbs_snd_instance.
Variables (X Y : qbsType R).
Let f : X * Y -> Y := snd.
Let hf : qbs_morphism f :=
  fun alpha h => h.2.
HB.instance Definition _ :=
  @isQBSMorphism.Build R (prodQ X Y) Y f hf.
Definition qbs_snd : qbsHomType (prodQ X Y) Y := f.
End qbs_snd_instance.

Section qbs_pair_instance.
Variables (W X Y : qbsType R).
Variable (f : qbsHomType W X) (g : qbsHomType W Y).
Let fg := fun w : W => ((f : W -> X) w, (g : W -> Y) w).
Let hfg : qbs_morphism fg :=
  fun alpha halpha =>
    conj (qbs_hom_proof _ halpha) (qbs_hom_proof _ halpha).
HB.instance Definition _ :=
  @isQBSMorphism.Build R W (prodQ X Y) fg hfg.
Definition qbs_pair : qbsHomType W (prodQ X Y) := fg.
End qbs_pair_instance.

(* 4. Exponential (Function Space) *)

(* The carrier of expQ X Y is qbsHomType R X Y (bundled morphisms).
   The random elements are those g : mR -> qbsHomType R X Y such that
   the uncurried map (r, x) |-> g(r)(x) is a morphism prodQ realQ X -> Y. *)

Lemma expQ_Mx_comp (X Y : qbsType R) :
  forall alpha (f : {mfun mR >-> mR}),
    (qbs_morphism (fun p : realQ * X => (alpha p.1 : X -> Y) p.2)) ->
    qbs_morphism
      (fun p : realQ * X => ((alpha \o f) p.1 : X -> Y) p.2).
Proof.
move=> alpha f halpha beta [hb1 hb2].
have -> : (fun p : realQ * X => (alpha \o f) p.1 p.2) \o beta =
          (fun p : realQ * X => alpha p.1 p.2) \o
            (fun r => (f (fst (beta r)), snd (beta r))) by [].
apply: halpha; split => /=.
- have -> : (fun r : mR => f (beta r).1) =
            f \o (fun r => (beta r).1) by [].
  exact: measurableT_comp.
- exact: hb2.
Qed.

Lemma expQ_Mx_const (X Y : qbsType R) :
  forall g : qbsHomType X Y,
    qbs_morphism (fun p : realQ * X => ((fun _ : mR => g) p.1 : X -> Y) p.2).
Proof.
move=> g beta [_ hb2].
have -> : (fun p : realQ * X => (g : X -> Y) p.2) \o beta =
          (g : X -> Y) \o (fun r => (beta r).2) by [].
exact: qbs_hom_proof.
Qed.

Lemma expQ_Mx_glue (X Y : qbsType R) :
  forall (P : {mfun mR >-> nat})
    (Fi : nat -> mR -> qbsHomType X Y),
    (forall i, qbs_morphism
       (fun p : realQ * X => (Fi i p.1 : X -> Y) p.2)) ->
    qbs_morphism
      (fun p : realQ * X => ((fun r => Fi (P r) r) p.1 : X -> Y) p.2).
Proof.
move=> P Fi hFi beta [hb1 hb2].
set Q := mfun_Sub (mem_set
  (measurableT_comp (measurable_funPT P) hb1) :
  (fun r => P (fst (beta r))) \in mfun).
have -> : (fun p : realQ * X => Fi (P p.1) p.1 p.2) \o beta =
          (fun r => (fun i => (fun p : realQ * X => Fi i p.1 p.2) \o beta)
            (Q r) r) by [].
apply: (qbs_Mx_glue Q
  (fun i => (fun p : realQ * X => Fi i p.1 p.2) \o beta)).
by move=> i; exact: hFi i _ (conj hb1 hb2).
Qed.

Section expQ_instance.
Variables (X Y : qbsType R).
HB.instance Definition _ :=
  @isQBS.Build R (qbsHomType X Y)
    [set g : mR -> qbsHomType X Y |
      qbs_morphism (fun p : realQ * X => (g p.1 : X -> Y) p.2)]
    (@expQ_Mx_comp X Y)
    (@expQ_Mx_const X Y)
    (@expQ_Mx_glue X Y).
(** Exponential (function space) QBS. *)
Definition expQ : qbsType R := qbsHomType X Y.
End expQ_instance.

Arguments expQ : clear implicits.

(* 5. Key Theorems: Cartesian Closure *)

Section qbs_eval_instance.
Variables (X Y : qbsType R).
Let f := fun p : prodQ (expQ X Y) X => (p.1 : X -> Y) p.2.
Let hf : qbs_morphism f.
Proof.
move=> beta [hb1 hb2].
have hmorph : qbs_morphism
    (fun p : realQ * X => ((fst \o beta) p.1 : X -> Y) p.2).
  exact: hb1.
set gamma := (fun r : mR => (r, snd (beta r))) : mR -> realQ * X.
have hgamma : qbs_Mx gamma.
  split => /=.
  - have -> : (fun r : mR => (gamma r).1) = idfun by [].
    exact: measurable_id.
  - exact: hb2.
by have := hmorph gamma hgamma.
Qed.
HB.instance Definition _ :=
  @isQBSMorphism.Build R (prodQ (expQ X Y) X) Y f hf.
(** Evaluation: cartesian closed structure (eval). *)
Definition qbs_eval : qbsHomType (prodQ (expQ X Y) X) Y :=
  f.
End qbs_eval_instance.

(* Helper: constant paired with random element is random in product *)
Lemma prodQ_const_random (X Y : qbsType R) (x : X) (alpha : mR -> Y) :
  qbs_Mx alpha -> qbs_Mx (fun r => (x, alpha r)).
Proof.
move=> halpha; split => /=.
- exact: qbs_Mx_const.
- exact: halpha.
Qed.

Section qbs_curry_instance.
Variables (X Y Z : qbsType R).
Variable (f : qbsHomType (prodQ X Y) Z).
Variable (x : X).
Let curry_fun := fun y => (f : prodQ X Y -> Z) (x, y).
Let curry_proof : forall alpha, qbs_Mx alpha ->
    qbs_Mx (curry_fun \o alpha).
Proof.
by move=> alpha halpha; exact: qbs_hom_proof
  (prodQ_const_random x halpha).
Qed.
HB.instance Definition _ := @isQBSMorphism.Build R Y Z curry_fun curry_proof.
(** Curried function as a bundled QBS morphism Y -> Z. *)
Definition qbs_curry : qbsHomType Y Z := curry_fun.
End qbs_curry_instance.

(** ## Universal property of exponentials                            *)
(** The following lemmas state that [eval] and [curry] form the      *)
(** bijection underlying the cartesian closed structure on QBS.      *)
(** They are stated as pointwise equations and hold by [reflexivity].*)

(** Beta rule for cartesian closure: evaluating the curried form
    recovers the original morphism. The underlying function of
    [qbs_curry f] at [x] is [fun y => f (x, y)], so applying
    it at [y] yields [f (x, y)].

    Here we package the curried function at [x] as a [qbsHomType]
    directly to let HB resolve its structure; the [prodQ_const_random]
    witness provides the required [isQBSMorphism] instance. *)
Lemma qbs_morphism_curry_eval (X Y Z : qbsType R)
  (f : qbsHomType (prodQ X Y) Z) (x : X) (y : Y) :
  let cf : Y -> Z := fun y0 => (f : prodQ X Y -> Z) (x, y0) in
  cf y = (f : prodQ X Y -> Z) (x, y).
Proof. by []. Qed.

(** Eta rule for cartesian closure: the evaluation morphism applied
    to a pair [(h, y)] with [h : qbsHomType R Y Z] recovers the
    pointwise application [h y]. This shows that [eval] is a left
    inverse of [curry] at the level of underlying functions. *)
Lemma qbs_morphism_eval_curry (Y Z : qbsType R)
  (h : qbsHomType Y Z) (y : Y) :
  (fun p : prodQ (expQ Y Z) Y => (p.1 : Y -> Z) p.2) (h, y) =
  (h : Y -> Z) y.
Proof. by []. Qed.

(* 6. Unit QBS *)

Section unitQ_instance.
HB.instance Definition _ :=
  @isQBS.Build R unit
    [set _ : mR -> unit | True]
    (fun _ _ _ => I)
    (fun _ => I)
    (fun _ _ _ => I).
(** Terminal (unit) QBS. *)
Definition unitQ : qbsType R := unit.
End unitQ_instance.

Section qbs_unit_instance.
Variable (X : qbsType R).
Let f := fun _ : X => tt.
Let hf : qbs_morphism f := fun alpha _ => I.
HB.instance Definition _ :=
  @isQBSMorphism.Build R X unitQ f hf.
(* Unit is terminal: unique morphism to unit *)
Definition qbs_unit : qbsHomType X unitQ := f.
End qbs_unit_instance.

(* 7. sigma_Mx: the induced sigma-algebra *)

Definition sigma_Mx (X : qbsType R) : set (set X) :=
  [set U | forall alpha, qbs_Mx alpha ->
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

(* 8. Comparison Morphisms *)
(* Standard operations on R, nat, bool that are measurable
   are automatically QBS morphisms via R_qbs. *)

(* Addition as a bundled QBS morphism prodQ realQ realQ -> realQ *)
Definition qbs_add : qbsHomType (prodQ realQ realQ) realQ :=
  @QBSHom.Pack R (prodQ realQ realQ) realQ
    (fun p => (p.1 + p.2))
    (QBSHom.Class
      (@isQBSMorphism.Build R (prodQ realQ realQ) realQ _
        (fun alpha h => measurable_funD h.1 h.2))).

(* Multiplication as a bundled QBS morphism *)
Definition qbs_mul : qbsHomType (prodQ realQ realQ) realQ :=
  @QBSHom.Pack R (prodQ realQ realQ) realQ
    (fun p => (p.1 * p.2))
    (QBSHom.Class
      (@isQBSMorphism.Build R (prodQ realQ realQ) realQ _
        (fun alpha h => measurable_funM h.1 h.2))).

(* 9. Subspace QBS *)
(* Given a QBS X and a predicate P on X, the subspace sub_qbs X P has
   carrier {x : X | P x} and random elements alpha such that
   proj1_sig \o alpha is random in X. *)

Section sub_qbs_def.
Variable (X : qbsType R) (P : set X).

Let sub_car := {x : X | P x}.
Let sub_proj : sub_car -> X := @proj1_sig _ P.

(* NB: We use (fun r => sub_proj (alpha r)) instead of (sub_proj \o alpha)
   to avoid a universe constraint on Composition.u2 that would conflict with
   algebra_tactics.ring *)
Let sub_Mx : set (mR -> sub_car) :=
  [set alpha | qbs_Mx (fun r => sub_proj (alpha r))].

Lemma sub_qbs_Mx_comp : forall alpha
  (f : {mfun mR >-> mR}),
  sub_Mx alpha -> sub_Mx (alpha \o f).
Proof.
move=> alpha f halpha; rewrite /sub_Mx /=.
have -> : (fun r => sub_proj ((alpha \o f) r)) =
          (fun r => sub_proj (alpha r)) \o f by [].
exact: qbs_Mx_comp halpha.
Qed.

Lemma sub_qbs_Mx_const : forall x : sub_car,
  sub_Mx (fun _ => x).
Proof.
move=> x; rewrite /sub_Mx /=.
exact: qbs_Mx_const.
Qed.

Lemma sub_qbs_Mx_glue : forall (Q : {mfun mR >-> nat})
  (Fi : nat -> mR -> sub_car),
  (forall i, sub_Mx (Fi i)) ->
  sub_Mx (fun r => Fi (Q r) r).
Proof.
move=> Q Fi hFi; rewrite /sub_Mx /=.
exact: (qbs_Mx_glue Q (fun i r => sub_proj (Fi i r)) (fun i => hFi i)).
Qed.

HB.instance Definition _ :=
  @isQBS.Build R sub_car sub_Mx
    sub_qbs_Mx_comp sub_qbs_Mx_const sub_qbs_Mx_glue.
Definition sub_qbs : qbsType R := sub_car.

End sub_qbs_def.

(* 10. Generating QBS *)
(* Given a set G of functions R -> X, generate the smallest QBS
   containing G by closing under the three QBS axioms. *)

Inductive generating_Mx (T : Type) (G : set (mR -> T))
  : (mR -> T) -> Prop :=
  | gen_base : forall alpha, G alpha -> generating_Mx G alpha
  | gen_comp : forall alpha (f : {mfun mR >-> mR}),
      generating_Mx G alpha ->
      generating_Mx G (alpha \o f)
  | gen_const : forall x : T, generating_Mx G (fun _ => x)
  | gen_glue : forall (P : {mfun mR >-> nat})
      (Fi : nat -> mR -> T),
      (forall i, generating_Mx G (Fi i)) ->
      generating_Mx G (fun r => Fi (P r) r).

Section generating_qbs_instance.
Variables (T : Type) (G : set (mR -> T)).
HB.instance Definition _ :=
  @isQBS.Build R T (generating_Mx G)
    (fun alpha f ha => gen_comp f ha)
    (fun x => gen_const G x)
    (fun P Fi hFi => gen_glue P hFi).
Definition generating_qbs : qbsType R := T.
End generating_qbs_instance.

Lemma generating_qbs_incl (T : Type) (G : set (mR -> T)) :
  G `<=` @qbs_Mx R (generating_qbs G).
Proof. by move=> alpha halpha; exact: gen_base. Qed.

(* 11. Exponential morphisms *)

(* Helper: random element paired with constant is random in product *)
Lemma prodQ_random_const (X Y : qbsType R) (alpha : mR -> X) (y : Y) :
  qbs_Mx alpha -> qbs_Mx (fun r => (alpha r, y)).
Proof.
move=> halpha; split => /=.
- exact: halpha.
- exact: qbs_Mx_const.
Qed.

(* 12. Image QBS (map_qbs) *)
(* Given a QBS morphism f : X -> Y, the image QBS map_qbs f X has
   carrier Y and random elements generated by {f \o alpha | alpha in Mx(X)}.
   This uses generating_qbs to close under the three QBS axioms,
   ensuring all constant functions are included even if f is not surjective. *)

Definition map_qbs (X Y : qbsType R) (f : X -> Y)
  (hf : qbs_morphism f) : qbsType R :=
  generating_qbs [set beta : mR -> Y |
    exists alpha, qbs_Mx alpha /\ beta = f \o alpha].

Lemma map_qbs_random (X Y : qbsType R) (f : X -> Y)
  (hf : qbs_morphism f) (alpha : mR -> X) :
  qbs_Mx alpha -> @qbs_Mx R (map_qbs hf) (f \o alpha).
Proof.
move=> halpha; apply: gen_base; exists alpha; split => //.
Qed.

(* map_qbs is coarser than Y: every random element of map_qbs f X
   is also a random element of Y. *)
Lemma map_qbs_sub (X Y : qbsType R) (f : X -> Y)
  (hf : qbs_morphism f) :
  forall beta, @qbs_Mx R (map_qbs hf) beta -> @qbs_Mx R Y beta.
Proof.
move=> beta; elim=> {beta}.
- by move=> beta [alpha [halpha ->]]; exact: (hf _ halpha).
- by move=> alpha g _ hIH; exact: qbs_Mx_comp hIH.
- by move=> x; exact: qbs_Mx_const.
- by move=> P Fi hFi IH; exact: qbs_Mx_glue IH.
Qed.

(* map_qbs is functorial: identity *)
Lemma map_qbs_morphism_out (X Y Z : qbsType R) (f : X -> Y) (g : Y -> Z)
  (hf : qbs_morphism f) (hg : qbs_morphism g) :
  @qbs_morphism (map_qbs hf) Z g.
Proof.
by move=> beta /map_qbs_sub; exact: hg.
Qed.

(* The defining map f is a morphism from X to map_qbs f X *)
Lemma map_qbs_morph_from (X Y : qbsType R) (f : X -> Y)
  (hf : qbs_morphism f) :
  @qbs_morphism X (map_qbs hf) f.
Proof.
by move=> alpha halpha; exact: map_qbs_random halpha.
Qed.

(* 13. Order Structure on QBS *)
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
  (c1 : forall alpha (f : {mfun mR >-> mR}),
    Mx alpha -> Mx (alpha \o f))
  (c2 : forall x : T, Mx (fun _ => x))
  (c3 : forall (P : {mfun mR >-> nat}) (Fi : nat -> mR -> T),
    (forall i, Mx (Fi i)) -> Mx (fun r => Fi (P r) r)) :
  G `<=` Mx -> generating_Mx G `<=` Mx.
Proof.
move=> hG beta hbeta; elim: hbeta.
- by move=> alpha hGa; exact: hG _ hGa.
- by move=> alpha f _ hIH; exact: c1 hIH.
- by move=> x; exact: c2.
- by move=> P Fi hFi IH; exact: c3 IH.
Qed.

(* Sup (join) of two sets of random elements on the same type:
   Mx(sup) is the generating closure of their union. *)
Definition qbs_supT (T : Type) (MxX MxY : set (mR -> T)) : qbsType R :=
  generating_qbs [set alpha : mR -> T | MxX alpha \/ MxY alpha].

(* Left inclusion: MxX <= Mx(sup) *)
Lemma qbs_supT_ub_l (T : Type) (MxX MxY : set (mR -> T)) :
  qbs_leT MxX (@qbs_Mx R (qbs_supT MxX MxY)).
Proof.
by move=> alpha halpha; apply: gen_base; left; exact: halpha.
Qed.

(* Right inclusion: MxY <= Mx(sup) *)
Lemma qbs_supT_ub_r (T : Type) (MxX MxY : set (mR -> T)) :
  qbs_leT MxY (@qbs_Mx R (qbs_supT MxX MxY)).
Proof.
by move=> alpha halpha; apply: gen_base; right; exact: halpha.
Qed.

(* The sup is the least upper bound among QBS-closed sets *)
Lemma qbs_supT_least (T : Type) (MxX MxY MxZ : set (mR -> T))
  (c1 : forall alpha (f : {mfun mR >-> mR}),
    MxZ alpha -> MxZ (alpha \o f))
  (c2 : forall x : T, MxZ (fun _ => x))
  (c3 : forall (P : {mfun mR >-> nat}) (Fi : nat -> mR -> T),
    (forall i, MxZ (Fi i)) ->
    MxZ (fun r => Fi (P r) r)) :
  qbs_leT MxX MxZ ->
  qbs_leT MxY MxZ ->
  qbs_leT (@qbs_Mx R (qbs_supT MxX MxY)) MxZ.
Proof.
move=> hX hY.
apply: generating_qbs_least c1 c2 c3 _.
by move=> alpha /= -[/hX | /hY].
Qed.

End qbs.
