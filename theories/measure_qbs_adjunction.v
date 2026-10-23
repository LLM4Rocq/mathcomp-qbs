(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals classical_sets boolp
  topology normedtype num_normedtype filter measurable_structure
  measurable_function borel_hierarchy lebesgue_stieltjes_measure
  measurable_realfun ereal.
From QBS Require Import quasi_borel standard_borel.

(**md**************************************************************************)
(* # Adjunction between Measurable Spaces and Quasi-Borel Spaces              *)
(*                                                                            *)
(* The R functor (R_qbs, quasi_borel.v) sends a measurable space to its QBS   *)
(* of measurable functions; the L functor (qbs_meas, quasi_borel.v) sends a   *)
(* QBS to its carrier with the sigma-algebra sigma_Mx. L -| R is              *)
(* qbs_morphism_measurableP (HKSY Prop. 15(1)). This file adds L on          *)
(* morphisms, the counit, standard Borel spaces, and fullness of R on         *)
(* standard Borel spaces (HKSY Prop. 15(2)).                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*   standard_borel_wit M == witness that measurableType M is standard Borel  *)
(*     erealQ == QBS on extended reals \bar R via R_qbs                       *)
(*   sigma_of Mx == sets measurable along all maps of Mx (L side)             *)
(*   Mx_of S == maps measurable for the set system S (R side)                 *)
(*   sigma_of_Mx_of == Galois connection S <= sigma_of Mx <-> Mx <= Mx_of S   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import order.Order.TTheory GRing.Theory Num.Def Num.Theory constructive_ereal.
Import MeasurableR.
Import boolp.

Local Open Scope classical_set_scope.

Section mqa.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

Implicit Types (X Y : qbsType R).

(** R functor properties.
    R_qbs is defined in quasi_borel.v. Here we show it is functorial. *)

(* If f is measurable, then f is a QBS morphism between R_qbs spaces *)
Lemma R_qbs_morphism d1 d2
    (M1 : measurableType d1) (M2 : measurableType d2)
    (f : {mfun M1 >-> M2}) :
  qbs_morphism (X := R_qbs R M1) (Y := R_qbs R M2) f.
Proof.
move=> alpha; rewrite /qbs_Mx /= => halpha.
exact: measurableT_comp.
Qed.

(** L functor on morphisms: a QBS morphism is measurable between the
    induced measurable spaces (the L functor is qbs_meas, see
    quasi_borel.v, and L -| R is qbs_morphism_measurableP). *)
Lemma qbs_morphism_measurable (X Y : qbsType R) (f : X -> Y) :
  qbs_morphism f ->
  measurable_fun [set: qbs_meas X] (f : qbs_meas X -> qbs_meas Y).
Proof.
move=> hf _ U mU; rewrite setTI qbs_measE => a ha.
exact: mU _ (hf _ ha).
Qed.

(** Counit of L -| R: the identity L (R M) -> M is measurable. *)
Lemma sigma_Mx_measurable d (M : measurableType d) (U : set M) :
  measurable U -> sigma_Mx (X := R_qbs R M) U.
Proof.
move=> mU a ha; rewrite -[X in measurable X]setTI.
exact: ha measurableT U mU.
Qed.

Lemma adjunction_counit d (M : measurableType d) :
  measurable_fun [set: qbs_meas (R_qbs R M)] (idfun : _ -> M).
Proof.
by move=> _ U mU; rewrite setTI qbs_measE; exact: sigma_Mx_measurable.
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
  rewrite /qbs_Mx /= => halpha; split; exact: measurableT_comp.
by rewrite /qbs_Mx /=; move=> [h1 h2]; apply/measurable_fun_pairP; split.
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
Definition R_standard_borel : standard_borel_wit mR.
Proof.
have hid : (id : mR -> mR) \in mfun by apply: mem_set; exact: measurable_id.
exact: {| sb_encode := mfun_Sub hid ; sb_decode := mfun_Sub hid |}.
Defined.

(** R is full on standard Borel domains (HKSY Prop. 15(2)): every QBS
    morphism R(M1) -> R(M2) is measurable when M1 is standard Borel. *)
Lemma R_qbs_full d1 d2 (M1 : measurableType d1) (M2 : measurableType d2)
    (sb : standard_borel_wit M1) (f : M1 -> M2) :
  qbs_morphism (X := R_qbs R M1) (Y := R_qbs R M2) f ->
  measurable_fun setT f.
Proof.
move: sb => [phi psi psiK] hf.
have -> : f = (f \o psi) \o phi by apply: funext => x /=; rewrite psiK.
exact: measurableT_comp (hf _ (measurable_funP psi)) (measurable_funP phi).
Qed.

Local Open Scope ring_scope.

(** nat is standard Borel: embed via [n%:R], retract via [truncn]. *)
Definition nat_standard_borel : standard_borel_wit nat.
Proof.
have hf : (fun n : nat => n%:R : mR) \in mfun.
  by apply: mem_set => _ U _; rewrite setTI.
have hg : (truncn : mR -> nat) \in mfun. exact: mem_set (@measurable_truncn R).
exact: {| sb_encode := mfun_Sub hf ; sb_decode := mfun_Sub hg ;
           sb_retractK := natrK |}.
Defined.

(** bool is standard Borel: embed via [b%:R], decode via [0 < r]. *)
Definition bool_standard_borel : standard_borel_wit bool.
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
Defined.

(** Standard Borel product closure via [encode_RR]/[decode_RR]. *)
Definition prod_standard_borel d1 d2
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
    exact: measurableT_comp (measurable_funP f1) measurable_fst.
  exact: measurableT_comp (measurable_funP f2) measurable_snd.
have hf : (fun xy : (M1 * M2)%type =>
         encode_RR (f1 xy.1, f2 xy.2) : mR) \in mfun.
  by apply: mem_set; exact: hf_meas.
have hg_meas : measurable_fun setT (fun r : mR =>
         let p := decode_RR r in
         (g1 p.1, g2 p.2) : (M1 * M2)%type).
  apply/measurable_fun_pairP; split.
    apply: measurableT_comp (measurable_funP g1) _.
    apply: measurableT_comp measurable_fst _.
    exact: measurable_decode_RR.
  apply: measurableT_comp (measurable_funP g2) _.
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
Defined.

(** For standard Borel [M], [sigma_Mx (R_qbs M)] coincides with
    the original sigma-algebra. *)
Lemma sigma_Mx_standard_borel d
    (M : measurableType d) (sb : standard_borel_wit M) :
  forall U : set M, sigma_Mx (X := R_qbs R M) U <-> measurable U.
Proof.
move: sb => [f g hgf] U; split.
- (* sigma_Mx -> measurable: use f, g to recover measurability.
     g is measurable so g is in Mx(R_qbs M), hence g^{-1}(U) is
     measurable. Then U = f^{-1}(g^{-1}(U)) since g(f(x)) = x,
     and f is measurable, so U is measurable. *)
  move=> hU.
  suff -> : U = f @^-1` (g @^-1` U).
    have := (measurable_funP f) measurableT _ (hU g (measurable_funP g)).
    by rewrite setTI; exact.
  rewrite eqEsubset; split => x /=.
    by rewrite /preimage /= => hUx; rewrite hgf.
  by rewrite /preimage /= => hgfU; rewrite -(hgf x).
- exact: sigma_Mx_measurable.
Qed.

(** QBS on the extended reals via [R_qbs]. *)
Definition erealQ := R_qbs R (\bar R).

Local Lemma measurable_contract_fin :
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

Local Lemma measurable_contract :
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
Definition ereal_standard_borel : standard_borel_wit (\bar R).
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
    by have := le_trans (le_trans h1 h2) (lerN10 R); rewrite ler10.
  - by rewrite !ifF ?(lt_geF h1) ?(lt_geF h2).
apply: measurableU; [apply: measurableU|].
- apply: measurableI.
  + suff -> : [set r : R | (1 <= r)] = [set r : R | r \in `[1, +oo[].
      exact: measurable_itv.
    by rewrite eqEsubset; split => r /=; rewrite in_itv /= andbT.
  + by rewrite functions.preimage_cst; case: ifPn => _;
      [exact: measurableT | exact: measurable0].
- apply: measurableI.
  + suff -> : [set r : R | (r <= -1)] =
              [set r : R | r \in `]-oo, (-1)]].
      exact: measurable_itv.
    by rewrite eqEsubset; split => r /=; rewrite in_itv /=.
  + by rewrite functions.preimage_cst; case: ifPn => _;
      [exact: measurableT | exact: measurable0].
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
Defined.

(** Order adjunction on a fixed carrier T (AFP rl_order_adjunction).
    [sigma_of Mx] is the L side: the sets measurable along every map of Mx
    ([sigma_Mx X = sigma_of qbs_Mx]); [Mx_of S] is the R side: the maps
    measurable for the set system S ([qbs_Mx (R_qbs M) = Mx_of measurable]).
    Both are antitone, and they form a (contravariant) Galois connection. *)
Definition sigma_of (T : Type) (Mx : set (mR -> T)) : set (set T) :=
  [set U | forall a, Mx a -> measurable (a @^-1` U)].

Definition Mx_of (T : Type) (S : set (set T)) : set (mR -> T) :=
  [set a | forall U, S U -> measurable (a @^-1` U)].

Lemma sigma_of_antitone (T : Type) (Mx1 Mx2 : set (mR -> T)) :
  Mx1 `<=` Mx2 -> sigma_of Mx2 `<=` sigma_of Mx1.
Proof. by move=> h U hU a /h; exact: hU. Qed.

Lemma Mx_of_antitone (T : Type) (S1 S2 : set (set T)) :
  S1 `<=` S2 -> Mx_of S2 `<=` Mx_of S1.
Proof. by move=> h a ha U /h; exact: ha. Qed.

Lemma sigma_of_Mx_of (T : Type) (S : set (set T)) (Mx : set (mR -> T)) :
  S `<=` sigma_of Mx <-> Mx `<=` Mx_of S.
Proof.
split=> h.
  by move=> a ha U hU; exact: h hU a ha.
by move=> U hU a ha; exact: h a ha U hU.
Qed.

Lemma sigma_MxE (X : qbsType R) :
  sigma_Mx (X := X) = sigma_of (qbs_Mx (s := X)).
Proof. by []. Qed.

Lemma qbs_Mx_R_qbs d (M : measurableType d) :
  qbs_Mx (s := R_qbs R M) = Mx_of (@measurable _ M).
Proof.
rewrite eqEsubset; split=> a ha.
  by move=> U mU; have := ha measurableT U mU; rewrite setTI.
by move=> _ U mU; rewrite setTI; exact: ha.
Qed.

(** Unit of the adjunction: random elements of X are measurable into L X
    (AFP L_max_of_measurables). *)
Lemma qbs_Mx_sub_Mx_of (X : qbsType R) :
  qbs_Mx (s := X) `<=` Mx_of (sigma_Mx (X := X)).
Proof. by apply/sigma_of_Mx_of. Qed.

End mqa.
