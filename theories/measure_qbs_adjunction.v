(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals.
From mathcomp Require Import classical_sets.
From mathcomp Require Import measurable_structure.
From mathcomp Require Import measurable_function.
From mathcomp Require Import borel_hierarchy lebesgue_stieltjes_measure.
From mathcomp Require Import measurable_realfun.
From QBS Require Import quasi_borel standard_borel.

(**md**************************************************************************)
(* # Adjunction between Measurable Spaces and Quasi-Borel Spaces              *)
(*                                                                            *)
(* The R functor: Meas -> QBS sends a measurable space to its QBS of          *)
(* measurable functions. The L functor: QBS -> sigma-algebra sends a QBS      *)
(* to the sigma-algebra sigma_Mx of sets whose preimages under random         *)
(* elements are measurable. These form an adjunction L -| R.                  *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section mqa.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(** R functor properties.
    R_qbs is defined in quasi_borel.v. Here we show it is functorial. *)

(* If f is measurable, then f is a QBS morphism between R_qbs spaces *)
Lemma R_qbs_morph (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2)
    (f : M1 -> M2) :
  measurable_fun setT f ->
  @qbs_morphism R (@R_qbs R _ M1) (@R_qbs R _ M2) f.
Proof.
move=> hf alpha; rewrite /qbs_Mx /= => halpha.
exact: measurableT_comp hf halpha.
Qed.

(* R_qbs preserves identity *)
Lemma R_qbs_id (d : measure_display) (M : measurableType d) :
  @qbs_morphism R (@R_qbs R _ M) (@R_qbs R _ M) idfun.
Proof. exact: (@qbs_morphism_id R). Qed.

(* R_qbs preserves composition *)
Lemma R_qbs_comp (d1 d2 d3 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2)
    (M3 : measurableType d3)
    (f : M1 -> M2) (g : M2 -> M3) :
  measurable_fun setT f ->
  measurable_fun setT g ->
  @qbs_morphism R (@R_qbs R _ M1) (@R_qbs R _ M3) (g \o f).
Proof.
move=> hf hg.
apply: (@qbs_morphism_comp R (@R_qbs R _ M1) (@R_qbs R _ M2) (@R_qbs R _ M3)).
- exact: R_qbs_morph.
- exact: R_qbs_morph.
Qed.

(** L functor (sigma-algebra level).
    L sends a QBS to its induced sigma-algebra sigma_Mx. *)

(* sigma_Mx is already defined in quasi_borel.v as:
   sigma_Mx X = { U | forall alpha in Mx, alpha^{-1}(U) is measurable } *)

(* sigma_Mx contains the empty set *)
Lemma L_sigma_set0 (X : qbsType R) : @sigma_Mx R X set0.
Proof.
by move=> alpha _; rewrite preimage_set0; exact: measurable0.
Qed.

(* L_sigma collects the sigma-algebra properties *)
Definition L_sigma (X : qbsType R) : set (set X) := @sigma_Mx R X.
Arguments L_sigma : clear implicits.

Lemma L_sigma_measurableT (X : qbsType R) : L_sigma X setT.
Proof. exact: (@sigma_Mx_setT R X). Qed.

Lemma L_sigma_measurableC (X : qbsType R) (U : set X) :
  L_sigma X U -> L_sigma X (~` U).
Proof. exact: (@sigma_Mx_setC R X). Qed.

Lemma L_sigma_measurable_bigcup (X : qbsType R) (F : nat -> set X) :
  (forall i, L_sigma X (F i)) -> L_sigma X (\bigcup_i F i).
Proof. exact: (@sigma_Mx_bigcup R X). Qed.

(* L is functorial: QBS morphisms map to measurable functions *)
Lemma L_qbs_morph (X Y : qbsType R) (f : X -> Y) :
  @qbs_morphism R X Y f ->
  forall U, L_sigma Y U -> L_sigma X (f @^-1` U).
Proof.
move=> hf U hU alpha halpha.
have hfa : @qbs_Mx R Y (f \o alpha) by exact: hf.
exact: hU.
Qed.

(* L preserves identity *)
Lemma L_qbs_id (X : qbsType R) (U : set X) :
  L_sigma X U -> L_sigma X (idfun @^-1` U).
Proof. by []. Qed.

(* L preserves composition *)
Lemma L_qbs_comp (X Y Z : qbsType R) (f : X -> Y)
    (g : Y -> Z) :
  @qbs_morphism R X Y f ->
  @qbs_morphism R Y Z g ->
  forall U, L_sigma Z U -> L_sigma X ((g \o f) @^-1` U).
Proof.
move=> hf hg U hU alpha halpha.
have hfa : @qbs_Mx R Y (f \o alpha) by exact: hf.
have hgfa : @qbs_Mx R Z (g \o (f \o alpha)) by exact: hg.
exact: hU.
Qed.

(** Adjunction L -| R.
    For a QBS X and measurable space Y:
    Hom_QBS(X, R(Y)) ~ Hom_Meas(L(X), Y). *)

(* Left-to-right: a QBS morphism X -> R(Y) gives a "measurable" map
   w.r.t. L_sigma(X) and sigma(Y) *)
Lemma lr_adj_l2r (X : qbsType R) (d : measure_display)
    (Y : measurableType d) (f : X -> Y) :
  @qbs_morphism R X (@R_qbs R _ Y) f ->
  forall U, measurable U -> L_sigma X (f @^-1` U).
Proof.
move=> hf U hU alpha halpha.
have hfa : @qbs_Mx R (@R_qbs R _ Y) (f \o alpha) := hf _ halpha.
have := hfa measurableT U hU; rewrite setTI; exact.
Qed.

(* Right-to-left: a "measurable" map w.r.t. L_sigma(X) and sigma(Y)
   gives a QBS morphism X -> R(Y) *)
Lemma lr_adj_r2l (X : qbsType R) (d : measure_display)
    (Y : measurableType d) (f : X -> Y) :
  (forall U, measurable U -> L_sigma X (f @^-1` U)) ->
  @qbs_morphism R X (@R_qbs R _ Y) f.
Proof.
move=> hf alpha; rewrite /qbs_Mx /= => halpha _ U hU; rewrite setTI.
exact: (hf U hU alpha halpha).
Qed.

(** Biconditional form of the L-R adjunction at a single object: a function
    [f : X -> Y] is a QBS morphism into [R_qbs Y] iff measurable preimages
    land in [L_sigma X]. This is not a categorical naturality statement. *)
Lemma lr_adj_iff (X : qbsType R) (d : measure_display)
    (Y : measurableType d) (f : X -> Y) :
  (@qbs_morphism R X (@R_qbs R _ Y) f) <->
  (forall U, measurable U -> L_sigma X (f @^-1` U)).
Proof.
split.
- exact: lr_adj_l2r.
- exact: lr_adj_r2l.
Qed.

(** R preserves products.
    R(M1 x M2) has the same random elements as prodQ(R(M1), R(M2)). *)

(* The random elements of R_qbs applied to a product measurable type
   coincide with those of the QBS product of R_qbs spaces *)
Lemma R_preserves_prod (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2)
    (alpha : mR -> M1 * M2) :
  @qbs_Mx R (@R_qbs R _ [the measurableType _ of (M1 * M2)%type]) alpha <->
  @qbs_Mx R (@prodQ R (@R_qbs R _ M1) (@R_qbs R _ M2)) alpha.
Proof.
split.
- rewrite /qbs_Mx /= => halpha; split.
  + exact: measurableT_comp measurable_fst halpha.
  + exact: measurableT_comp measurable_snd halpha.
- rewrite /qbs_Mx /=; move=> [h1 h2]; apply/measurable_fun_pairP; split; exact.
Qed.

(** Standard Borel spaces.
    A measurable space is standard Borel if it is measurably isomorphic
    to a measurable subset of R. *)

(** [is_standard_borel M] holds when [M] admits measurable
    maps witnessing an isomorphism with a subset of R. *)
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

(** On standard Borel spaces the R functor is fully faithful:
    every QBS morphism R(M1) -> R(M2) is measurable. *)
Lemma R_full_faithful_standard_borel
    (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2) :
  is_standard_borel M1 ->
  is_standard_borel M2 ->
  forall (f : M1 -> M2),
    @qbs_morphism R (@R_qbs R _ M1) (@R_qbs R _ M2) f ->
    measurable_fun setT f.
Proof.
move=> [phi1 [psi1 [hphi1 [hpsi1 hpsi1phi1]]]]
       [phi2 [psi2 [hphi2 [hpsi2 hpsi2phi2]]]] f hf.
have hfpsi1 : measurable_fun setT (f \o psi1).
  exact: (hf psi1 hpsi1).
have heq : f = psi2 \o (phi2 \o f \o psi1) \o phi1.
  by apply: boolp.funext => x /=; rewrite hpsi1phi1 hpsi2phi2.
rewrite heq; apply: measurableT_comp; last exact: hphi1.
apply: measurableT_comp; first exact: hpsi2.
exact: measurableT_comp hphi2 hfpsi1.
Qed.

(* The unit of the adjunction: X -> R(L(X)) at the level of
   the identity function being a QBS morphism into
   the R_qbs of the L_sigma-measurable structure *)
Lemma adjunction_unit (X : qbsType R) (alpha : mR -> X) :
  @qbs_Mx R X alpha ->
  forall U, L_sigma X U -> measurable (alpha @^-1` U).
Proof. by move=> halpha U hU; exact: hU. Qed.

(* The counit: L(R(M)) refines sigma(M), i.e., every measurable set
   is in the induced sigma-algebra *)
Lemma adjunction_counit (d : measure_display) (M : measurableType d)
    (U : set M) :
  measurable U -> L_sigma (@R_qbs R _ M) U.
Proof.
move=> hU alpha; rewrite /qbs_Mx /= => halpha.
have := halpha measurableT U hU; rewrite setTI; exact.
Qed.

Local Open Scope ring_scope.

Let numR :=
  num_topology.numFieldTopology
    .Real_sort__canonical__topology_structure_Topological
    R.

(** Helper: measurability for functions into nat (discrete sigma-algebra).
    Every set in nat is measurable, so measurability of g reduces to
    measurability of singleton preimages. *)
Lemma measurable_fun_nat_discrete (d : measure_display) (T : measurableType d)
    (g : T -> nat) (D : set T) :
  (forall n : nat, measurable (D `&` g @^-1` [set n])) ->
  measurable_fun D g.
Proof.
move=> hg _ Y _; rewrite /measurable /=.
suff -> : D `&` g @^-1` Y = \bigcup_(n in setT)
  (fun n => if boolp.asbool (Y n) then D `&` g @^-1` [set n] else set0) n.
  apply: bigcup_measurable => n _.
  case: boolp.asboolP => _; [exact: hg | exact: measurable0].
rewrite eqEsubset; split => [r [hDr hYgr] | r [n _ /=]].
  exists (g r) => //=.
  case: boolp.asboolP => [_ | hNY].
    split => //; by rewrite /preimage /=.
  exfalso; exact: hNY hYgr.
case: boolp.asboolP => [hYn | _]; last by [].
move=> [hDr]; rewrite /preimage /= => ->.
split => //; exact: hYn.
Qed.

(** truncn : R -> nat is measurable.
    Preimages of singletons are intervals:
    - trunc^{-1}({0}) = (-inf, 1)
    - trunc^{-1}({n+1}) = [n+1, n+2) *)
Lemma measurable_truncn :
  measurable_fun [set: mR] (@truncn R : mR -> nat).
Proof.
apply: measurable_fun_nat_discrete => n; rewrite setTI.
case: n => [|n].
- suff -> : ((@truncn R : mR -> nat) @^-1` [set 0%N] : set mR) =
            ([set` `]-oo, 1%:R[] : set mR).
    exact: measurable_itv.
  rewrite eqEsubset; split => r.
    rewrite /preimage /= => /eqP htr.
    rewrite in_itv /=.
    have hTP := archimedean.Num.Theory.truncnP r.
    case: ifPn hTP => [h0 /andP [_ hr2] | hlt0 /eqP hn0].
      by rewrite (eqP htr) in hr2.
    apply: (preorder.Order.PreorderTheory.lt_trans _ ltr01).
    rewrite order.Order.TotalTheory.ltNge; exact: hlt0.
  rewrite /preimage /= in_itv /= => hr1.
  apply/eqP.
  have hTP := archimedean.Num.Theory.truncnP r.
  case: ifPn hTP => [h0 /andP [hr1' hr2'] | hlt0 /eqP //].
  rewrite truncn_eq //; apply/andP; split => //.
- suff -> : ((@truncn R : mR -> nat) @^-1` [set n.+1] : set mR) =
            ([set` `[n.+1%:R, n.+2%:R[] : set mR).
    exact: measurable_itv.
  rewrite eqEsubset; split => r.
    rewrite /preimage /= => /eqP htr.
    rewrite in_itv /=; apply/andP; split.
    + have hTP := archimedean.Num.Theory.truncnP r.
      case: ifPn hTP => [h0 /andP [hr _] | hlt0 /eqP hn].
        by rewrite (eqP htr) in hr.
      by rewrite hn in htr.
    + have hTP := archimedean.Num.Theory.truncnP r.
      case: ifPn hTP => [h0 /andP [_ hr] | hlt0 /eqP hn].
        by rewrite (eqP htr) in hr.
      by rewrite hn in htr.
  rewrite /preimage /= in_itv /= => /andP [hr1 hr2].
  apply/eqP; rewrite truncn_eq //.
    by apply/andP; split.
  exact: (preorder.Order.PreorderTheory.le_trans (ler0n _ _) hr1).
Qed.

(** nat is standard Borel: embed via [n%:R], retract via [truncn]. *)
Lemma nat_standard_borel : is_standard_borel nat.
Proof.
exists (fun n : nat => n%:R : mR), (@truncn R : mR -> nat).
split; first by move=> _ U _; rewrite setTI.
split; first exact: measurable_truncn.
exact: natrK.
Qed.

(** bool is standard Borel: embed via [b%:R], decode via [0 < r]. *)
Lemma bool_standard_borel : is_standard_borel bool.
Proof.
exists (fun b : bool => b%:R : mR),
       (fun r : mR => (0 < r)%R : bool).
split; first by move=> _ U _; rewrite setTI.
split.
  apply: (@measurable_fun_bool _ _ _ _ true).
  rewrite setTI.
  suff -> : ((fun r : mR => (0 < r)%R) @^-1` [set true] : set mR) =
            ([set` `]0%:R, +oo[] : set mR).
    exact: measurable_itv.
  rewrite eqEsubset; split => r /=.
    move=> hr; rewrite in_itv /=; apply/andP; split => //.
  by rewrite in_itv /= => /andP [].
move=> []; rewrite /=.
  by rewrite ltr01.
by rewrite order.Order.POrderTheory.ltxx.
Qed.

(** Standard Borel product closure via [encode_RR]/[decode_RR]. *)
Lemma prod_standard_borel (d1 d2 : measure_display)
    (M1 : measurableType d1) (M2 : measurableType d2) :
  is_standard_borel M1 -> is_standard_borel M2 ->
  is_standard_borel [the measurableType _ of (M1 * M2)%type].
Proof.
move=> [f1 [g1 [hf1 [hg1 hgf1]]]] [f2 [g2 [hf2 [hg2 hgf2]]]].
exists (fun xy : M1 * M2 =>
         @standard_borel.encode_RR R (f1 xy.1, f2 xy.2)),
       (fun r : mR =>
         let p := @standard_borel.decode_RR R r in
         (g1 p.1, g2 p.2)).
split.
  apply: measurableT_comp.
    exact: standard_borel.measurable_encode_RR.
  apply/measurable_fun_pairP; split.
  - exact: measurableT_comp hf1 measurable_fst.
  - exact: measurableT_comp hf2 measurable_snd.
split.
  apply/measurable_fun_pairP; split.
  - apply: measurableT_comp hg1 _.
    apply: measurableT_comp measurable_fst _.
    exact: standard_borel.measurable_decode_RR.
  - apply: measurableT_comp hg2 _.
    apply: measurableT_comp measurable_snd _.
    exact: standard_borel.measurable_decode_RR.
move=> [x1 x2] /=.
change ((let p := @standard_borel.decode_RR R
  (@standard_borel.encode_RR R (f1 x1, f2 x2))
  in (g1 p.1, g2 p.2)) = (x1, x2)).
by rewrite standard_borel.encode_RRK /= hgf1 hgf2.
Qed.

(** For standard Borel [M], [L_sigma (R_qbs M)] coincides with
    the original sigma-algebra. *)
Lemma standard_borel_lr_sets_ident (d : measure_display)
    (M : measurableType d) :
  is_standard_borel M ->
  forall U : set M, L_sigma (@R_qbs R _ M) U <-> measurable U.
Proof.
move=> [f [g [hf [hg hgf]]]] U; split.
- (* L_sigma -> measurable: use f, g to recover measurability.
     g is measurable so g is in Mx(R_qbs M), hence g^{-1}(U) is
     measurable. Then U = f^{-1}(g^{-1}(U)) since g(f(x)) = x,
     and f is measurable, so U is measurable. *)
  move=> hU.
  have hgU : measurable (g @^-1` U) by exact: (hU g hg).
  suff -> : U = f @^-1` (g @^-1` U).
    have := hf measurableT _ hgU; rewrite setTI; exact.
  rewrite eqEsubset; split => x /=.
    rewrite /preimage /= => hUx; by rewrite hgf.
  rewrite /preimage /= => hgfU; by rewrite -(hgf x).
- (* measurable -> L_sigma: this is adjunction_counit *)
  exact: adjunction_counit.
Qed.

Import constructive_ereal.

(** QBS on the extended reals via [R_qbs]. *)
Definition erealQ := @R_qbs R _ (\bar R : measurableType _).

Lemma measurable_contract_fin :
  measurable_fun [set: mR] (fun r : R => r / (1 + `|r|))%R.
Proof.
apply: continuous_measurable_fun => r.
apply: normed_module.cvgM; [exact: filter.cvg_id|].
apply: normed_module.cvgV.
  by apply: lt0r_neq0; rewrite ltr_pwDl // normr_ge0.
apply: pseudometric_normed_Zmodule.cvgD.
  exact: (@topology_structure.cvg_cst numR).
exact: pseudometric_normed_Zmodule.cvg_norm.
Qed.

Lemma measurable_contract :
  measurable_fun [set: \bar R] (@contract R : \bar R -> R).
Proof.
move=> _ U mU; rewrite setTI.
suff -> : (@contract R) @^-1` U =
  EFin @` ((fun r : R => r / (1 + `|r|))%R @^-1` U)
  `|` (if boolp.asbool (U 1%R) then [set +oo%E] else set0)
  `|` (if boolp.asbool (U (-1)%R) then [set -oo%E] else set0).
- apply: measurableU; [apply: measurableU|].
  + apply: measurable_image_EFin.
    have := @measurable_contract_fin measurableT U mU; rewrite setTI; exact.
  + by case: boolp.asboolP => _; [exact: emeasurable_set1 | exact: measurable0].
  + by case: boolp.asboolP => _; [exact: emeasurable_set1 | exact: measurable0].
- rewrite eqEsubset; split => x.
  + rewrite /preimage /= => hUx.
    case: x hUx => [r| | ] /= hU'.
    * by left; left; exists r.
    * by left; right; case: boolp.asboolP.
    * by right; case: boolp.asboolP.
  + rewrite /preimage /=.
    move=> [[[r hUr <-]|]|] /=; first done.
    * by case: boolp.asboolP => [hU1 [->]|_ []].
    * by case: boolp.asboolP => [hU1 [->]|_ []].
Qed.

(** The extended reals are standard Borel via [contract]/[expand]. *)
Lemma ereal_standard_borel : is_standard_borel (\bar R : measurableType _).
Proof.
exists (@contract R), (@expand R).
split; first exact: measurable_contract.
split; last exact: ereal.contractK.
move=> _ U mU; rewrite setTI.
rewrite /expand.
have -> : (fun r : R =>
  if 1 <= r then +oo%E else if r <= -1 then -oo%E else
  (r / (1 - `|r|))%:E) @^-1` U =
  ([set r : R | (1 <= r)%R] `&` (fun=> +oo%E) @^-1` U) `|`
  ([set r : R | (r <= -1)%R] `&` (fun=> -oo%E) @^-1` U) `|`
  ([set r : R | (-1 < r)%R /\ (r < 1)%R] `&`
   (fun r => (r / (1 - `|r|))%:E) @^-1` U).
  rewrite /preimage eqEsubset; split => r /=.
    case: ifPn => h1.
      by move=> hU'; left; left; split.
    case: ifPn => h2.
      by move=> hU'; left; right; split.
    move=> hU'; right; split => //.
    split; first by rewrite order.Order.TotalTheory.ltNge.
    by rewrite order.Order.TotalTheory.ltNge.
  move=> [[[h1 hU']|[h2 hU']]|[[h1 h2] hU']].
  - by rewrite h1.
  - case: ifPn => h1; [|by rewrite h2].
    have h12 := preorder.Order.PreorderTheory.le_trans h1 h2.
    by have := preorder.Order.PreorderTheory.le_trans h12 (lerN10 R);
       rewrite ler10.
  - rewrite ifF; last exact: order.Order.POrderTheory.lt_geF h2.
    by rewrite ifF // order.Order.POrderTheory.lt_geF //
       order.Order.TotalTheory.ltNge //
       order.Order.POrderTheory.ltW.
apply: measurableU; [apply: measurableU|].
- apply: measurableI.
  + suff -> : [set r : R | (1 <= r)%R] = [set r : R | r \in `[1%R, +oo[%R].
      exact: measurable_itv.
    by rewrite eqEsubset; split => r /=; rewrite in_itv /= andbT.
  + rewrite (_ : (fun=> +oo%E) @^-1` U =
      if boolp.asbool (U +oo%E) then setT else set0).
    * by case: boolp.asboolP => _;
        [exact: measurableT | exact: measurable0].
    * by rewrite /preimage; apply: boolp.funext => r /=;
         apply: boolp.propext; case: boolp.asboolP.
- apply: measurableI.
  + suff -> : [set r : R | (r <= -1)%R] =
              [set r : R | r \in `]-oo, (-1)%R]%R].
      exact: measurable_itv.
    by rewrite eqEsubset; split => r /=; rewrite in_itv /=.
  + rewrite (_ : (fun=> -oo%E) @^-1` U =
      if boolp.asbool (U -oo%E) then setT else set0).
    * by case: boolp.asboolP => _;
        [exact: measurableT | exact: measurable0].
    * by rewrite /preimage; apply: boolp.funext => r /=;
         apply: boolp.propext; case: boolp.asboolP.
- have h : measurable_fun ([set` `](-1)%R, 1%R[%R] : set mR)
      (EFin \o (fun r : R => r / (1 - `|r|))).
    apply/measurable_EFinP.
    apply: open_continuous_measurable_fun.
      exact: num_normedtype.interval_open.
    move=> r; rewrite /= inE => /andP [hr1 hr2].
    have h1 : (-1 < r)%R.
      by move: hr1; rewrite /= /preorder.Order.le /=.
    have h2 : (r < 1)%R.
      by move: hr2; rewrite /= /preorder.Order.le /=.
    apply: normed_module.cvgM; [exact: filter.cvg_id|].
    apply: normed_module.cvgV.
      apply: lt0r_neq0; rewrite subr_gt0 ltr_norml; apply/andP; split;
        [exact: h1 | exact: h2].
    apply: pseudometric_normed_Zmodule.cvgD.
      exact: (@topology_structure.cvg_cst numR).
    apply: pseudometric_normed_Zmodule.cvgN.
    exact: pseudometric_normed_Zmodule.cvg_norm.
  suff -> : [set r : R | (-1 < r /\ r < 1)%R] `&`
    (fun r => (r / (1 - `|r|))%:E) @^-1` U =
    ([set` `](-1)%R, 1%R[%R] : set mR) `&`
    (EFin \o (fun r : R => r / (1 - `|r|))) @^-1` U.
    exact: h _ U mU.
  congr (_ `&` _).
  by rewrite eqEsubset; split => r /=; rewrite in_itv /= => /andP.
Qed.

End mqa.
