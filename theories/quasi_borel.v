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

(* ===================================================================== *)
(* Extensions: Subspaces, Generating sets, Structural morphisms          *)
(* ===================================================================== *)

(* ----- 11. Subspace QBS ----- *)
(* Given a QBS X and a predicate P on X, the subspace sub_qbs X P has
   carrier {x : X | P x} and random elements alpha such that
   proj1_sig \o alpha is random in X. *)

Section sub_qbs_def.
Variable (X : qbs) (P : set (qbs_car X)).

Let sub_car := {x : qbs_car X | P x}.
Let sub_proj : sub_car -> qbs_car X := @proj1_sig _ P.

Let sub_Mx : set (mR -> sub_car) :=
  [set alpha | qbs_random X (sub_proj \o alpha)].

Lemma sub_qbs_closed1 : forall alpha f,
  sub_Mx alpha -> measurable_fun setT f -> sub_Mx (alpha \o f).
Proof.
move=> alpha f halpha hf; rewrite /sub_Mx /=.
have -> : sub_proj \o (alpha \o f) = (sub_proj \o alpha) \o f by [].
exact: qbs_random_comp halpha hf.
Qed.

Lemma sub_qbs_closed2 : forall x : sub_car,
  sub_Mx (fun _ => x).
Proof.
move=> x; rewrite /sub_Mx /=.
have -> : sub_proj \o (fun _ : mR => x) = (fun _ => sub_proj x) by [].
exact: qbs_random_const.
Qed.

Lemma sub_qbs_closed3 : forall (Q : mR -> nat) (Fi : nat -> mR -> sub_car),
  measurable_fun setT Q ->
  (forall i, sub_Mx (Fi i)) ->
  sub_Mx (fun r => Fi (Q r) r).
Proof.
move=> Q Fi hQ hFi; rewrite /sub_Mx /=.
have -> : sub_proj \o (fun r => Fi (Q r) r) =
          (fun r => (fun i r => sub_proj (Fi i r)) (Q r) r) by [].
exact: (qbs_random_glue hQ (fun i => hFi i)).
Qed.

Definition sub_qbs : qbs :=
  @mkQBS sub_car sub_Mx sub_qbs_closed1 sub_qbs_closed2 sub_qbs_closed3.

End sub_qbs_def.

(* ----- 12. Generating QBS ----- *)
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

Definition generating_qbs (T : Type) (G : set (mR -> T)) : qbs :=
  @mkQBS T (generating_Mx G)
    (fun alpha f ha hf => gen_comp ha hf)
    (fun x => gen_const G x)
    (fun P Fi hP hFi => gen_glue hP hFi).

Lemma generating_qbs_incl (T : Type) (G : set (mR -> T)) :
  G `<=` qbs_random (generating_qbs G).
Proof. by move=> alpha hα; exact: gen_base. Qed.

(* ----- 13. Product swap and associators ----- *)

Lemma qbs_morph_swap (X Y : qbs) :
  qbs_morph (prodQ X Y) (prodQ Y X) (fun p => (p.2, p.1)).
Proof.
move=> alpha [h1 h2]; split => /=.
- have -> : fst \o (fun r : mR => ((alpha r).2, (alpha r).1)) =
            snd \o alpha by [].
  exact: h2.
- have -> : snd \o (fun r : mR => ((alpha r).2, (alpha r).1)) =
            fst \o alpha by [].
  exact: h1.
Qed.

Lemma qbs_morph_assoc_lr (X Y Z : qbs) :
  qbs_morph (prodQ (prodQ X Y) Z) (prodQ X (prodQ Y Z))
    (fun p => (p.1.1, (p.1.2, p.2))).
Proof.
move=> alpha [h12 h3].
have h12' : qbs_random (prodQ X Y) (fst \o alpha) by exact: h12.
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

Lemma qbs_morph_assoc_rl (X Y Z : qbs) :
  qbs_morph (prodQ X (prodQ Y Z)) (prodQ (prodQ X Y) Z)
    (fun p => ((p.1, p.2.1), p.2.2)).
Proof.
move=> alpha [h1 h23].
have h23' : qbs_random (prodQ Y Z) (snd \o alpha) by exact: h23.
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

(* ----- 14. Exponential morphisms ----- *)

(* Helper: random element paired with constant is random in product *)
Lemma prodQ_random_const (X Y : qbs) (alpha : mR -> X) (y : Y) :
  qbs_random X alpha -> qbs_random (prodQ X Y) (fun r => (alpha r, y)).
Proof.
move=> hα; split => /=.
- have -> : fst \o (fun r : mR => (alpha r, y)) = alpha by [].
  exact: hα.
- have -> : snd \o (fun r : mR => (alpha r, y)) = (fun _ => y) by [].
  exact: qbs_random_const.
Qed.

(* Application/evaluation composed with pairing: given f : W -> expQ X Y
   and g : W -> X, the map w |-> f(w)(g(w)) is a morphism W -> Y *)
Lemma qbs_morph_exp_comp (W X Y : qbs)
  (f : qbs_hom W (expQ X Y)) (g : qbs_hom W X) :
  qbs_morph W Y (fun w => qbs_hom_val (f w) (g w)).
Proof.
move=> alpha halpha.
have hf_alpha : qbs_random (expQ X Y) (f \o alpha).
  exact: (qbs_hom_proof f) _ halpha.
have hg_alpha : qbs_random X (g \o alpha).
  exact: (qbs_hom_proof g) _ halpha.
set beta := (fun r : mR => (r, g (alpha r))) : mR -> realQ * X.
have hbeta : qbs_random (prodQ realQ X) beta.
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
Lemma qbs_morph_arg_swap (X Y Z : qbs) (f : qbs_hom X (expQ Y Z)) :
  qbs_morph Y (expQ X Z)
    (fun y => @QBSHom X Z (fun x => qbs_hom_val (f x) y)
       (fun alpha halpha =>
          ((qbs_hom_proof f alpha halpha) :
             qbs_morph (prodQ realQ Y) Z
               (fun p : realQ * Y => qbs_hom_val ((f \o alpha) p.1) p.2))
          (fun r : mR => (r, y))
          (conj (@measurable_id _ mR setT) (qbs_random_const y))
       )).
Proof.
move=> beta hbeta /= gamma [hg1 hg2].
have hf_sg : qbs_random (expQ Y Z) (f \o (snd \o gamma)).
  exact: (qbs_hom_proof f) _ hg2.
have hbfg : qbs_random Y (beta \o (fst \o gamma)).
  exact: qbs_random_comp hbeta hg1.
set delta := (fun r : mR => (r, beta ((fst \o gamma) r))) : mR -> realQ * Y.
have hdelta : qbs_random (prodQ realQ Y) delta.
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

End QBS.
