(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals classical_sets boolp
  topology normedtype filter measurable_structure measurable_function
  borel_hierarchy lebesgue_stieltjes_measure measurable_realfun.
From QBS Require Import quasi_borel standard_borel.

(**md**************************************************************************)
(* # Adjunction between Measurable Spaces and Quasi-Borel Spaces              *)
(*                                                                            *)
(* The R functor: Meas -> QBS sends a measurable space to its QBS of          *)
(* measurable functions. The L functor: QBS -> sigma-algebra sends a QBS      *)
(* to the sigma-algebra sigma_Mx of sets whose preimages under random         *)
(* elements are measurable. These form an adjunction L -| R.                  *)
(*                                                                            *)
(* ```                                                                        *)
(*     L_sigma X == sigma-algebra induced by a QBS X (the L functor)          *)
(*   standard_borel_wit M == witness that measurableType M is standard Borel  *)
(*     erealQ == QBS on extended reals \bar R via R_qbs                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import order.Order.TTheory GRing.Theory Num.Def Num.Theory constructive_ereal.
Import boolp.

Local Open Scope classical_set_scope.

Section mqa.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(** R functor properties.
    R_qbs is defined in quasi_borel.v. Here we show it is functorial. *)

(* If f is measurable, then f is a QBS morphism between R_qbs spaces *)
Lemma R_qbs_morph d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (f : {mfun M1 >-> M2}) :
  qbs_morphism (X := R_qbs R M1) (Y := R_qbs R M2) f.
Proof.
move=> alpha; rewrite /qbs_Mx /= => halpha.
exact: measurableT_comp.
Qed.

(* R_qbs preserves identity *)
Lemma R_qbs_id d (M : measurableType d) :
  qbs_morphism (X := R_qbs R M) (Y := R_qbs R M) idfun.
Proof. exact: qbs_hom_proof. Qed.

(* R_qbs preserves composition *)
Lemma R_qbs_comp d1 d2 d3
    (M1 : measurableType d1) (M2 : measurableType d2)
    (M3 : measurableType d3)
    (f : {mfun M1 >-> M2}) (g : {mfun M2 >-> M3}) :
  qbs_morphism (X := R_qbs R M1) (Y := R_qbs R M3) (g \o f).
Proof.
by move=> alpha halpha; exact: (R_qbs_morph g (R_qbs_morph f halpha)).
Qed.

(** L functor (sigma-algebra level).
    L sends a QBS to its induced sigma-algebra sigma_Mx. *)

(* sigma_Mx is already defined in quasi_borel.v as:
   sigma_Mx X = { U | forall alpha in Mx, alpha^{-1}(U) is measurable } *)

(* sigma_Mx contains the empty set *)
Lemma L_sigma_set0 (X : qbsType R) : sigma_Mx (X := X) set0.
Proof.
by move=> alpha _; rewrite preimage_set0; exact: measurable0.
Qed.

(* L_sigma collects the sigma-algebra properties *)
Notation L_sigma X := (sigma_Mx (X := X)).

Lemma L_sigma_measurableT (X : qbsType R) : L_sigma X setT.
Proof. exact: sigma_Mx_setT. Qed.

Lemma L_sigma_measurableC (X : qbsType R) (U : set X) :
  L_sigma X U -> L_sigma X (~` U).
Proof. exact: sigma_Mx_setC. Qed.

Lemma L_sigma_measurable_bigcup (X : qbsType R) (F : nat -> set X) :
  (forall i, L_sigma X (F i)) -> L_sigma X (\bigcup_i F i).
Proof. exact: sigma_Mx_bigcup. Qed.

(* L is functorial: QBS morphisms map to measurable functions *)
Lemma L_qbs_morph (X Y : qbsType R) (f : X -> Y) :
  qbs_morphism f ->
  forall U, L_sigma Y U -> L_sigma X (f @^-1` U).
Proof.
by move=> hf U hU alpha halpha; exact: hU (hf _ halpha).
Qed.

(* L preserves identity *)
Lemma L_qbs_id (X : qbsType R) (U : set X) :
  L_sigma X U -> L_sigma X (idfun @^-1` U).
Proof. by []. Qed.

(* L preserves composition *)
Lemma L_qbs_comp (X Y Z : qbsType R) (f : X -> Y)
    (g : Y -> Z) :
  qbs_morphism f ->
  qbs_morphism g ->
  forall U, L_sigma Z U -> L_sigma X ((g \o f) @^-1` U).
Proof.
by move=> hf hg U hU alpha halpha; exact: hU (hg _ (hf _ halpha)).
Qed.

(** Adjunction L -| R.
    For a QBS X and measurable space Y:
    Hom_QBS(X, R(Y)) ~ Hom_Meas(L(X), Y). *)

(* Left-to-right: a QBS morphism X -> R(Y) gives a "measurable" map
   w.r.t. L_sigma(X) and sigma(Y) *)
Lemma lr_adj_l2r (X : qbsType R) d
    (Y : measurableType d) (f : X -> Y) :
  qbs_morphism (Y := R_qbs R Y) f ->
  forall U, measurable U -> L_sigma X (f @^-1` U).
Proof.
move=> hf U hU alpha halpha.
by have := (hf _ halpha) measurableT U hU; rewrite setTI; exact.
Qed.

(* Right-to-left: a "measurable" map w.r.t. L_sigma(X) and sigma(Y)
   gives a QBS morphism X -> R(Y) *)
Lemma lr_adj_r2l (X : qbsType R) d
    (Y : measurableType d) (f : X -> Y) :
  (forall U, measurable U -> L_sigma X (f @^-1` U)) ->
  qbs_morphism (Y := R_qbs R Y) f.
Proof.
move=> hf alpha; rewrite /qbs_Mx /= => halpha _ U hU; rewrite setTI.
exact: (hf U hU alpha halpha).
Qed.

(** Biconditional form of the L-R adjunction at a single object: a function
    [f : X -> Y] is a QBS morphism into [R_qbs Y] iff measurable preimages
    land in [L_sigma X]. This is not a categorical naturality statement. *)
Lemma lr_adj_iff (X : qbsType R) d
    (Y : measurableType d) (f : X -> Y) :
  (qbs_morphism (Y := R_qbs R Y) f) <->
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
Lemma R_preserves_prod d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (alpha : mR -> M1 * M2) :
  qbs_Mx (s := R_qbs R (M1 * M2)%type) alpha <->
  qbs_Mx (s := prodQ (R_qbs R M1) (R_qbs R M2)) alpha.
Proof.
split.
- rewrite /qbs_Mx /= => halpha; split.
  + exact: measurableT_comp.
  + exact: measurableT_comp.
- by rewrite /qbs_Mx /=; move=> [h1 h2]; apply/measurable_fun_pairP; split.
Qed.

(** Standard Borel spaces.
    A measurable space is standard Borel if it is measurably isomorphic
    to a measurable subset of R. *)

(** [standard_borel_wit M] witnesses that [M] admits measurable
    maps witnessing a retraction with R (standard Borel property). *)
Record standard_borel_wit d
    (M : measurableType d) := StandardBorelWit {
  sb_encode : {mfun M >-> mR} ;
  sb_decode : {mfun mR >-> M} ;
  sb_retractK : cancel sb_encode sb_decode
}.
Arguments sb_encode {d M}.
Arguments sb_decode {d M}.
Arguments sb_retractK {d M}.

(* R itself is standard Borel (via the identity) *)
Lemma R_standard_borel : standard_borel_wit mR.
Proof.
have hid : (id : mR -> mR) \in mfun by apply: mem_set; exact: measurable_id.
exact: {| sb_encode := mfun_Sub hid ; sb_decode := mfun_Sub hid |}.
Qed.

(** On standard Borel spaces the R functor is fully faithful:
    every QBS morphism R(M1) -> R(M2) is measurable. *)
Lemma R_full_faithful_standard_borel
    d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (sb1 : standard_borel_wit M1) (sb2 : standard_borel_wit M2)
    (f : M1 -> M2) :
    qbs_morphism (X := R_qbs R M1) (Y := R_qbs R M2) f ->
    measurable_fun setT f.
Proof.
move: sb1 sb2 => [phi1 psi1 hpsi1phi1]
       [phi2 psi2 hpsi2phi2] hf.
have hfpsi1 : measurable_fun setT (f \o psi1).
  exact: hf (measurable_funP psi1).
have heq : f = psi2 \o (phi2 \o f \o psi1) \o phi1.
  by apply: funext => x /=; rewrite hpsi1phi1 hpsi2phi2.
rewrite heq; apply: measurableT_comp; last exact: measurable_funP.
apply: measurableT_comp; first exact: measurable_funP.
exact: measurableT_comp (measurable_funP phi2) hfpsi1.
Qed.

(* The unit of the adjunction: X -> R(L(X)) at the level of
   the identity function being a QBS morphism into
   the R_qbs of the L_sigma-measurable structure *)
Lemma adjunction_unit (X : qbsType R) (alpha : mR -> X) :
  qbs_Mx alpha ->
  forall U, L_sigma X U -> measurable (alpha @^-1` U).
Proof. by move=> halpha U; exact. Qed.

(* The counit: L(R(M)) refines sigma(M), i.e., every measurable set
   is in the induced sigma-algebra *)
Lemma adjunction_counit d (M : measurableType d)
    (U : set M) :
  measurable U -> L_sigma (R_qbs R M) U.
Proof.
move=> hU alpha; rewrite /qbs_Mx /= => halpha.
by have := halpha measurableT U hU; rewrite setTI; exact.
Qed.

Local Open Scope ring_scope.

Local Notation truncnP := archimedean.Num.Theory.truncnP.
Local Notation interval_open := num_normedtype.interval_open.
Local Notation contractK := ereal.contractK.

(** Helper: measurability for functions into nat (discrete sigma-algebra).
    Every set in nat is measurable, so measurability of g reduces to
    measurability of singleton preimages. *)
Lemma measurable_fun_nat_discrete d (T : measurableType d)
    (g : T -> nat) (D : set T) :
  (forall n : nat, measurable (D `&` g @^-1` [set n])) ->
  measurable_fun D g.
Proof.
move=> hg _ Y _; rewrite /measurable /=.
suff -> : D `&` g @^-1` Y = \bigcup_(n in setT)
  (fun n => if asbool (Y n) then D `&` g @^-1` [set n] else set0) n.
  apply: bigcup_measurable => n _.
  by case: asboolP => _; [exact: hg | exact: measurable0].
rewrite eqEsubset; split => [r [hDr hYgr] | r [n _ /=]].
  exists (g r) => //=.
  case: asboolP => [_ | hNY].
    by split => //; rewrite /preimage /=.
  by exfalso; exact: hNY hYgr.
case: asboolP => [hYn | _]; last by [].
move=> [hDr]; rewrite /preimage /= => ->.
by split => //; exact: hYn.
Qed.

(** truncn : R -> nat is measurable.
    Preimages of singletons are intervals:
    - trunc^{-1}({0}) = (-inf, 1)
    - trunc^{-1}({n+1}) = [n+1, n+2) *)
Lemma measurable_truncn :
  measurable_fun [set: mR] (truncn : mR -> nat).
Proof.
apply: measurable_fun_nat_discrete => n; rewrite setTI.
case: n => [|n].
- suff -> : ((truncn : mR -> nat) @^-1` [set 0%N] : set mR) =
            ([set` `]-oo, 1%:R[] : set mR).
    exact: measurable_itv.
  rewrite eqEsubset; split => r.
    rewrite /preimage /= => /eqP htr.
    rewrite in_itv /=.
    have hTP := truncnP r.
    case: ifPn hTP => [h0 /andP [_ hr2] | hlt0 /eqP hn0].
      by rewrite (eqP htr) in hr2.
    apply: (lt_trans _ ltr01).
    by rewrite ltNge; exact: hlt0.
  rewrite /preimage /= in_itv /= => hr1.
  apply/eqP.
  have hTP := truncnP r.
  case: ifPn hTP => [h0 /andP [hr1' hr2'] | hlt0 /eqP //].
  by rewrite truncn_eq //; apply/andP; split.
- suff -> : ((truncn : mR -> nat) @^-1` [set n.+1] : set mR) =
            ([set` `[n.+1%:R, n.+2%:R[] : set mR).
    exact: measurable_itv.
  rewrite eqEsubset; split => r.
    rewrite /preimage /= => /eqP htr.
    rewrite in_itv /=; apply/andP; split.
    + have hTP := truncnP r.
      case: ifPn hTP => [h0 /andP [hr _] | hlt0 /eqP hn].
        by rewrite (eqP htr) in hr.
      by rewrite hn in htr.
    + have hTP := truncnP r.
      case: ifPn hTP => [h0 /andP [_ hr] | hlt0 /eqP hn].
        by rewrite (eqP htr) in hr.
      by rewrite hn in htr.
  rewrite /preimage /= in_itv /= => /andP [hr1 hr2].
  apply/eqP; rewrite truncn_eq //.
    by apply/andP; split.
  exact: (le_trans (ler0n _ _) hr1).
Qed.

(** nat is standard Borel: embed via [n%:R], retract via [truncn]. *)
Lemma nat_standard_borel : standard_borel_wit nat.
Proof.
have hf : (fun n : nat => n%:R : mR) \in mfun.
  by apply: mem_set => _ U _; rewrite setTI.
have hg : (truncn : mR -> nat) \in mfun. exact: mem_set measurable_truncn.
exact: {| sb_encode := mfun_Sub hf ; sb_decode := mfun_Sub hg ;
           sb_retractK := natrK |}.
Qed.

(** bool is standard Borel: embed via [b%:R], decode via [0 < r]. *)
Lemma bool_standard_borel : standard_borel_wit bool.
Proof.
have hf : (fun b : bool => b%:R : mR) \in mfun.
  by apply: mem_set => _ U _; rewrite setTI.
have hg_meas : measurable_fun setT (fun r : mR => (0 < r) : bool).
  apply: (measurable_fun_bool true).
  rewrite setTI.
  suff -> : ((fun r : mR => (0 < r)) @^-1` [set true] : set mR) =
            ([set` `]0%:R, +oo[] : set mR).
    exact: measurable_itv.
  rewrite eqEsubset; split => r /=.
    by move=> hr; rewrite in_itv /=; apply/andP; split.
  by rewrite in_itv /= => /andP [].
have hg : (fun r : mR => (0 < r) : bool) \in mfun. exact: mem_set hg_meas.
apply: {| sb_encode := mfun_Sub hf ; sb_decode := mfun_Sub hg |}.
move=> []; rewrite /=.
  by rewrite ltr01.
by rewrite ltxx.
Qed.

(** Standard Borel product closure via [encode_RR]/[decode_RR]. *)
Lemma prod_standard_borel d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (sb1 : standard_borel_wit M1) (sb2 : standard_borel_wit M2) :
  standard_borel_wit (M1 * M2)%type.
Proof.
move: sb1 sb2 => [f1 g1 hgf1] [f2 g2 hgf2].
have hf_meas : measurable_fun setT (fun xy : M1 * M2 =>
         encode_RR (f1 xy.1, f2 xy.2)).
  apply: measurableT_comp.
    exact: measurable_encode_RR.
  apply/measurable_fun_pairP; split.
  - exact: measurableT_comp (measurable_funP f1) measurable_fst.
  - exact: measurableT_comp (measurable_funP f2) measurable_snd.
have hf : (fun xy : (M1 * M2)%type =>
         encode_RR (f1 xy.1, f2 xy.2) : mR) \in mfun.
  by apply: mem_set; exact: hf_meas.
have hg_meas : measurable_fun setT (fun r : mR =>
         let p := decode_RR r in
         (g1 p.1, g2 p.2) : (M1 * M2)%type).
  apply/measurable_fun_pairP; split.
  - apply: measurableT_comp (measurable_funP g1) _.
    apply: measurableT_comp measurable_fst _.
    exact: measurable_decode_RR.
  - apply: measurableT_comp (measurable_funP g2) _.
    apply: measurableT_comp measurable_snd _.
    exact: measurable_decode_RR.
have hg : (fun r : mR => let p := decode_RR r in (g1 p.1, g2 p.2) :
         (M1 * M2)%type) \in mfun.
  by apply: mem_set; exact: hg_meas.
apply: {| sb_encode := mfun_Sub hf ; sb_decode := mfun_Sub hg |}.
move=> [x1 x2] /=.
change ((let p := decode_RR
  (encode_RR (f1 x1, f2 x2))
  in (g1 p.1, g2 p.2)) = (x1, x2)).
by rewrite encode_RRK /= hgf1 hgf2.
Qed.

(** For standard Borel [M], [L_sigma (R_qbs M)] coincides with
    the original sigma-algebra. *)
Lemma standard_borel_lr_sets_ident d
    (M : measurableType d) (sb : standard_borel_wit M) :
  forall U : set M, L_sigma (R_qbs R M) U <-> measurable U.
Proof.
move: sb => [f g hgf] U; split.
- (* L_sigma -> measurable: use f, g to recover measurability.
     g is measurable so g is in Mx(R_qbs M), hence g^{-1}(U) is
     measurable. Then U = f^{-1}(g^{-1}(U)) since g(f(x)) = x,
     and f is measurable, so U is measurable. *)
  move=> hU.
  have hgU : measurable (g @^-1` U). exact: (hU g (measurable_funP g)).
  suff -> : U = f @^-1` (g @^-1` U).
    by have := (measurable_funP f) measurableT _ hgU; rewrite setTI; exact.
  rewrite eqEsubset; split => x /=.
    by rewrite /preimage /= => hUx; rewrite hgf.
  by rewrite /preimage /= => hgfU; rewrite -(hgf x).
- (* measurable -> L_sigma: this is adjunction_counit *)
  exact: adjunction_counit.
Qed.

(** QBS on the extended reals via [R_qbs]. *)
Definition erealQ := R_qbs R (\bar R).

Lemma measurable_contract_fin :
  measurable_fun [set: mR] (fun r : R => r / (1 + `|r|)).
Proof.
apply: continuous_measurable_fun => r.
apply: cvgM; [exact: cvg_id|].
apply: cvgV.
  by apply: lt0r_neq0; rewrite ltr_pwDl // normr_ge0.
apply: cvgD.
  exact: cvg_cst.
exact: cvg_norm.
Qed.

Lemma measurable_contract :
  measurable_fun [set: \bar R] (contract (R := R)).
Proof.
move=> _ U mU; rewrite setTI.
suff -> : (contract (R := R)) @^-1` U =
  EFin @` ((fun r : R => r / (1 + `|r|)) @^-1` U)
  `|` (if asbool (U 1) then [set +oo%E] else set0)
  `|` (if asbool (U (-1)) then [set -oo%E] else set0).
- apply: measurableU; [apply: measurableU|].
  + apply: measurable_image_EFin.
    by have := measurable_contract_fin measurableT mU; rewrite setTI; exact.
  + by case: asboolP => _; [exact: emeasurable_set1 | exact: measurable0].
  + by case: asboolP => _; [exact: emeasurable_set1 | exact: measurable0].
- rewrite eqEsubset; split => x.
  + rewrite /preimage /= => hUx.
    case: x hUx => [r| | ] /= hU'.
    * by left; left; exists r.
    * by left; right; case: asboolP.
    * by right; case: asboolP.
  + rewrite /preimage /=.
    move=> [[[r hUr <-]|]|] /=; first done.
    * by case: asboolP => [hU1 [->]|_ []].
    * by case: asboolP => [hU1 [->]|_ []].
Qed.

(** The extended reals are standard Borel via [contract]/[expand]. *)
Lemma ereal_standard_borel : standard_borel_wit (\bar R).
Proof.
have hc : (contract (R := R) : \bar R -> mR) \in mfun.
  by apply: mem_set; exact: measurable_contract.
have he_meas : measurable_fun setT
  (expand (R := R) : mR -> \bar R).
move=> _ U mU; rewrite setTI.
rewrite /expand.
have -> : (fun r : R =>
  if 1 <= r then +oo%E else if r <= -1 then -oo%E else
  (r / (1 - `|r|))%:E) @^-1` U =
  ([set r : R | (1 <= r)] `&` (fun=> +oo%E) @^-1` U) `|`
  ([set r : R | (r <= -1)] `&` (fun=> -oo%E) @^-1` U) `|`
  ([set r : R | (-1 < r) /\ (r < 1)] `&`
   (fun r => (r / (1 - `|r|))%:E) @^-1` U).
  rewrite /preimage eqEsubset; split => r /=.
    case: ifPn => h1.
      by move=> hU'; left; left; split.
    case: ifPn => h2.
      by move=> hU'; left; right; split.
    move=> hU'; right; split => //.
    split; first by rewrite ltNge.
    by rewrite ltNge.
  move=> [[[h1 hU']|[h2 hU']]|[[h1 h2] hU']].
  - by rewrite h1.
  - case: ifPn => h1; [|by rewrite h2].
    have h12 := le_trans h1 h2.
    by have := le_trans h12 (lerN10 R);
       rewrite ler10.
  - by rewrite ifF; [rewrite ifF // lt_geF // ltNge // ltW|exact: lt_geF h2].
apply: measurableU; [apply: measurableU|].
- apply: measurableI.
  + suff -> : [set r : R | (1 <= r)] = [set r : R | r \in `[1, +oo[].
      exact: measurable_itv.
    by rewrite eqEsubset; split => r /=; rewrite in_itv /= andbT.
  + rewrite (_ : (fun=> +oo%E) @^-1` U =
      if asbool (U +oo%E) then setT else set0).
    * by case: asboolP => _;
        [exact: measurableT | exact: measurable0].
    * by rewrite /preimage; apply: funext => r /=;
         apply: propext; case: asboolP.
- apply: measurableI.
  + suff -> : [set r : R | (r <= -1)] =
              [set r : R | r \in `]-oo, (-1)]].
      exact: measurable_itv.
    by rewrite eqEsubset; split => r /=; rewrite in_itv /=.
  + rewrite (_ : (fun=> -oo%E) @^-1` U =
      if asbool (U -oo%E) then setT else set0).
    * by case: asboolP => _;
         [exact: measurableT | exact: measurable0].
    * by rewrite /preimage; apply: funext => r /=;
         apply: propext; case: asboolP.
- have h : measurable_fun ([set` `](-1), 1[] : set mR)
      (EFin \o (fun r : R => r / (1 - `|r|))).
    apply/measurable_EFinP.
    apply: open_continuous_measurable_fun.
      exact: interval_open.
    move=> r; rewrite /= inE => /andP [hr1 hr2].
    apply: cvgM; [exact: cvg_id|].
    apply: cvgV.
      apply: lt0r_neq0; rewrite subr_gt0 ltr_norml; apply/andP; split;
        [exact: hr1 | exact: hr2].
    apply: cvgD.
      exact: cvg_cst.
    apply: cvgN.
    exact: cvg_norm.
  suff -> : [set r : R | (-1 < r /\ r < 1)] `&`
    (fun r => (r / (1 - `|r|))%:E) @^-1` U =
    ([set` `](-1), 1[] : set mR) `&`
    (EFin \o (fun r : R => r / (1 - `|r|))) @^-1` U.
    exact: h _ U mU.
  congr (_ `&` _).
  by rewrite eqEsubset; split => r /=; rewrite in_itv /= => /andP.
have he : (expand (R := R) : mR -> \bar R) \in mfun.
  by apply: mem_set; exact: he_meas.
exact: {| sb_encode := mfun_Sub hc ; sb_decode := mfun_Sub he ;
           sb_retractK := contractK (R := R) |}.
Qed.

End mqa.
