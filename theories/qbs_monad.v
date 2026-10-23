(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology classical_sets
  boolp numfun measure measurable_realfun lebesgue_measure lebesgue_integral
  lebesgue_stieltjes_measure probability.
From mathcomp Require Import giry kernel lebesgue_integral_fubini.
From QBS Require Import quasi_borel standard_borel probability_qbs.

(**md**************************************************************************)
(* # The probability monad on quasi-Borel spaces                              *)
(*                                                                            *)
(* Following Heunen, Kammar, Staton, Yang (LICS 2017), the random elements of *)
(* the probability monad P(X) are the maps r |-> [alpha, g r] for a random    *)
(* element alpha of X and a measurable map g : R -> giry R into probability   *)
(* measures. Bind is the Giry bind of mathcomp-analysis.                      *)
(*                                                                            *)
(* ```                                                                        *)
(*              giry_prob m m1 == m : giry T R given a proof m1 that m(T) = 1 *)
(*          qbs_prob_rep b a g == b r is represented by [a, g r] for every r  *)
(*                    monadP X == the QBS of probabilities on X               *)
(*             monadP_random X == its random elements                         *)
(*                qbs_return x == the Dirac probability at x                  *)
(*                qbs_bind p f == bind, for f : qbsHomType X (monadP Y)       *)
(*              monadP_map f p == pushforward of p along f : qbsHomType X Y   *)
(*                 qbs_join pp == multiplication P(P(X)) -> P(X)              *)
(*         qbs_strength (w, p) == strength W * monadP X -> monadP (W * X)     *)
(*             qbs_assoc U W X == associativity (U * W) * X -> U * (W * X)    *)
(*      qbs_returnQ, qbs_bindQ == return and bind as qbsHomType morphisms     *)
(*    qbs_joinQ, qbs_strengthQ == join and strength as qbsHomType morphisms   *)
(*       qbs_bind_internal X Y == bind as P(X) * (X => P(Y)) -> P(Y)          *)
(* qbs_swap X Y, monadP_pair p q == swap; monadic product of p, q             *)
(* ```                                                                        *)
(*                                                                            *)
(* The strength laws (unit, associativity, return, join) are                  *)
(* qbs_strength_snd, qbs_strength_assoc, qbs_strength_return and              *)
(* qbs_strength_join.                                                         *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section giry_prob.
Context d (T : measurableType d) (R : realType).

Lemma giry_bindE d' (T' : measurableType d') (mu : giry T' R)
    (g : T' -> giry T R) (mg : measurable_fun [set: T'] g) (A : set T) :
  measurable A -> giry_bind mu mg A = \int[mu]_x g x A.
Proof.
move=> mA; rewrite /giry_bind /= /giry_join /= giry_int_map//.
exact: measurable_giry_ev.
Qed.

Lemma giry_bind_setT d' (T' : measurableType d') (mu : giry T' R)
    (g : T' -> giry T R) (mg : measurable_fun [set: T'] g) :
  mu [set: T'] = 1 -> (forall x, g x [set: T] = 1) ->
  giry_bind mu mg [set: T] = 1.
Proof.
move=> mu1 g1; rewrite giry_bindE//.
under eq_integral do rewrite g1.
by rewrite integral_cst//= mu1 mule1.
Qed.

Definition giry_prob (m : giry T R) of m [set: T] = 1 : set T -> \bar R := m.

Context (m : giry T R) (m1 : m [set: T] = 1).

HB.instance Definition _ := Measure.on (giry_prob m1).
HB.instance Definition _ :=
  Measure_isProbability.Build _ _ _ (giry_prob m1) m1.

Lemma giry_probE A : giry_prob m1 A = m A. Proof. by []. Qed.

End giry_prob.

Section probability_monad.
Context (R : realType).
Local Notation mR := (measurableTypeR R).
Local Notation G := (giry mR R).
Implicit Types (W X Y Z : qbsType R).

Lemma qbs_prob_equivP X (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 <->
  forall U, sigma_Mx U -> qbs_prob_event X p1 U = qbs_prob_event X p2 U.
Proof. by []. Qed.

(** ** The QBS of probabilities *)

Record qbs_prob_rep X (b : mR -> qbs_prob X) (a : mR -> X) (g : mR -> G) :
    Prop := QbsProbRep {
  rep_random : qbs_Mx a ;
  rep_measurable : measurable_fun [set: mR] g ;
  rep_mass : forall r, g r [set: mR] = 1 ;
  rep_event : forall r U, sigma_Mx U ->
    qbs_prob_event X (b r) U = g r (a @^-1` U) }.

Definition monadP_random X : set (mR -> qbs_prob X) :=
  [set b | exists a g, qbs_prob_rep b a g].
Arguments monadP_random : clear implicits.

Lemma monadP_random_event X (b : mR -> qbs_prob X) (U : set X) :
  monadP_random X b -> sigma_Mx U ->
  measurable_fun [set: mR] (fun r => qbs_prob_event X (b r) U).
Proof.
move=> [a [g [ha mg _ hb]]] mU.
rewrite (_ : (fun r => _) = (giry_ev ^~ (a @^-1` U)) \o g).
  by apply/funext => r; rewrite /= hb.
exact: measurableT_comp (measurable_giry_ev (mU _ ha)) mg.
Qed.

(** Random elements of P(X) are saturated w.r.t. pointwise equivalence. *)
Lemma monadP_random_equiv X (b1 b2 : mR -> qbs_prob X) :
  (forall r, qbs_prob_equiv X (b1 r) (b2 r)) ->
  monadP_random X b1 -> monadP_random X b2.
Proof.
move=> e [a [g [ha mg g1 hb]]]; exists a, g; split => // r U mU.
by rewrite -hb// /qbs_prob_event; apply/esym/e.
Qed.

Local Lemma monadP_comp X (b : mR -> qbs_prob X) (f : {mfun mR >-> mR}) :
  monadP_random X b -> monadP_random X (b \o f).
Proof.
move=> [a [g [ha mg g1 hb]]]; exists a, (g \o f); split => //.
- exact: measurableT_comp mg (measurable_funPT f).
- by move=> r; exact: g1.
- by move=> r U mU; exact: hb.
Qed.

Local Lemma monadP_const X (p : qbs_prob X) :
  monadP_random X (fun=> p).
Proof.
exists (qbs_prob_alpha p), (fun=> qbs_prob_mu p : G); split => //.
  exact: qbs_prob_alpha_random.
by move=> _; exact: probability_setT.
Qed.

Local Lemma measurable_encode r :
  measurable_fun [set: mR] (fun t => encode_RR_mR (r, t)).
Proof.
exact: measurableT_comp (@measurable_RR_to_R R) (pair1_measurable _).
Qed.

Local Lemma measurable_decode1 :
  measurable_fun [set: mR] (fst \o @decode_RR_mR R).
Proof. exact: measurableT_comp measurable_fst (@measurable_R_to_RR R). Qed.

Local Lemma measurable_decode2 :
  measurable_fun [set: mR] (snd \o @decode_RR_mR R).
Proof. exact: measurableT_comp measurable_snd (@measurable_R_to_RR R). Qed.

(** Random elements of a product, read off a single seed through decoding. *)
Local Lemma qbs_Mx_decode_pair X Y (a : mR -> X) (b : mR -> Y) :
  qbs_Mx a -> qbs_Mx b ->
  qbs_Mx
    (fun s : mR => (a (decode_RR_mR s).1, b (decode_RR_mR s).2) : prodQ X Y).
Proof.
move=> ha hb; split.
  exact: qbs_Mx_compT ha measurable_decode1.
exact: qbs_Mx_compT hb measurable_decode2.
Qed.

Section glue.
Context X (P : {mfun mR >-> nat}) (F : nat -> mR -> qbs_prob X).
Hypothesis hF : forall i, monadP_random X (F i).

Let enc (n : nat) (y : mR) : mR := encode_RR_mR (n%:R%R, y).
Let menc n : measurable_fun [set: mR] (enc n) := measurable_encode _.
Let idx (r : mR) : nat := truncn (decode_RR_mR r).1.
Let snd' (r : mR) : mR := (decode_RR_mR r).2.

Let midx : measurable_fun [set: mR] idx :=
  measurableT_comp (@measurable_truncn R) measurable_decode1.

Let msnd : measurable_fun [set: mR] snd' := measurable_decode2.

Let idx_enc n y : idx (enc n y) = n.
Proof. by rewrite /idx /enc encode_RR_mRK /= natrK. Qed.

Let snd_enc n y : snd' (enc n y) = y.
Proof. by rewrite /snd' /enc encode_RR_mRK. Qed.

Local Lemma monadP_glue : monadP_random X (fun r => F (P r) r).
Proof.
have /choice[ag hag] : forall i, exists ag : (mR -> X) * (mR -> G),
    qbs_prob_rep (F i) ag.1 ag.2.
  by move=> i; have [a [g h]] := hF i; exists (a, g).
pose a' r := (ag (idx r)).1 (snd' r).
pose g' r := giry_map (menc (P r)) ((ag (P r)).2 r).
have a'enc n y : a' (enc n y) = (ag n).1 y by rewrite /a' idx_enc snd_enc.
exists a', g'; split.
- apply: (qbs_Mx_glueT (P := idx) (Fi := fun n => (ag n).1 \o snd')) midx _.
  by move=> n; exact: qbs_Mx_compT (rep_random (hag n)) msnd.
- apply: (measurable_glue (P := P)
    (Fi := fun n r => giry_map (menc n) ((ag n).2 r))) => [|n].
    exact: measurable_funPT.
  exact: measurableT_comp (measurable_giry_map _) (rep_measurable (hag n)).
- by move=> r; rewrite /g' /= /pushforward preimage_setT (rep_mass (hag _)).
- move=> r U mU; rewrite (rep_event (hag _))// /g' /= /pushforward.
  by congr (_ _); apply/seteqP; split => y /=; rewrite a'enc.
Qed.

End glue.

Definition monadP X : Type := qbs_prob X.
Arguments monadP : clear implicits.

HB.instance Definition _ X :=
  @isQBS.Build R (monadP X) (monadP_random X)
    (@monadP_comp X) (@monadP_const X) (@monadP_glue X).

Lemma monadP_randomE X : qbs_Mx (s := monadP X) = monadP_random X.
Proof. by []. Qed.

Lemma qbs_measurable_event X Y (f : qbsHomType X (monadP Y)) (U : set Y) :
  sigma_Mx U -> qbs_measurable X (fun x => qbs_prob_event Y (f x) U).
Proof.
by move=> mU b hb; apply: monadP_random_event mU; exact: qbs_hom_proof.
Qed.

(** ** Return *)

Definition qbs_return X (x : X) : monadP X :=
  mkQBSProb (fun=> x) (\d_(0 : mR))%R (qbs_Mx_const x).

Lemma qbs_return_event X (x : X) (U : set X) :
  qbs_prob_event X (qbs_return x) U = (x \in U)%:R%:E.
Proof.
rewrite /qbs_prob_event /= diracE /preimage /=.
by congr ((_ : bool)%:R%:E); apply/idP/idP; rewrite !inE.
Qed.

Lemma qbs_return_morphism X : qbs_morphism (X := X) (Y := monadP X)
  (@qbs_return X).
Proof.
move=> a ha; exists a, (@giry_ret _ mR R); split => //.
  exact: measurable_giry_ret.
by move=> r; exact: diracT.
Qed.

HB.instance Definition _ X :=
  @isQBSMorphism.Build R X (monadP X) (@qbs_return X)
    (@qbs_return_morphism X).

Lemma qbs_return_integral X (x : X) (h : X -> \bar R) :
  qbs_integral X (qbs_return x) h = h x.
Proof.
by rewrite /qbs_integral /= integral_cst//= diracT mule1.
Qed.

(** ** Bind *)

Section bind.
Context X Y (p : qbs_prob X) (f : qbsHomType X (monadP Y)).

Let hf : monadP_random Y (f \o qbs_prob_alpha p) :=
  qbs_hom_proof _ (qbs_prob_alpha_random p).

Let bind_a : mR -> Y := sval (cid hf).
Let bind_g : mR -> G := sval (cid (svalP (cid hf))).
Let bind_rep : qbs_prob_rep (f \o qbs_prob_alpha p) bind_a bind_g :=
  svalP (cid (svalP (cid hf))).

Let bind_mu : G := giry_bind (qbs_prob_mu p) (rep_measurable bind_rep).
Let bind_mu1 : bind_mu [set: mR] = 1.
Proof.
by apply: giry_bind_setT; [exact: probability_setT|exact: rep_mass bind_rep].
Qed.

Definition qbs_bind : monadP Y :=
  mkQBSProb bind_a (giry_prob bind_mu1) (rep_random bind_rep).

Lemma ge0_qbs_integral_bind (h : Y -> \bar R) :
  qbs_measurable Y h -> (forall y, 0 <= h y) ->
  qbs_integral Y qbs_bind h =
  \int[qbs_prob_mu p]_r qbs_integral Y (f (qbs_prob_alpha p r)) h.
Proof.
move=> mh h0; rewrite /qbs_integral /=.
have mha := mh _ (rep_random bind_rep).
rewrite [LHS](giry_int_bind (qbs_prob_mu p) (rep_measurable bind_rep)
  (h := h \o bind_a))//; first by move=> x; exact: h0.
rewrite /giry_int; apply: eq_integral => r _.
apply: (@ge0_integral_sigma_Mx R Y bind_a _ (bind_g r)) => //.
- exact: rep_random bind_rep.
- exact: qbs_prob_alpha_random.
- by move=> U mU; exact/esym/(rep_event bind_rep).
Qed.

Lemma qbs_bind_event (U : set Y) : sigma_Mx U ->
  qbs_prob_event Y qbs_bind U =
  \int[qbs_prob_mu p]_r qbs_prob_event Y (f (qbs_prob_alpha p r)) U.
Proof.
move=> mU; rewrite /qbs_prob_event /= giry_int_map//.
  exact: measurable_giry_ev (mU _ (rep_random bind_rep)).
by apply: eq_integral => r _; exact/esym/(rep_event bind_rep).
Qed.

End bind.

(** Bind with a fixed continuation is a morphism. *)
Lemma qbs_bind_morphism X Y Z (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) :
  qbs_morphism (X := X) (Y := monadP Z) (fun x => qbs_bind (f x) g).
Proof.
move=> a ha.
have [b1 [g1 r1]] : monadP_random Y (f \o a) := qbs_hom_proof _ ha.
have [b2 [g2 r2]] : monadP_random Z (g \o b1) :=
  qbs_hom_proof _ (rep_random r1).
exists b2, (fun r => giry_bind (g1 r) (rep_measurable r2)); split.
- exact: rep_random r2.
- exact: measurableT_comp (measurable_giry_bind _) (rep_measurable r1).
- by move=> r; apply: giry_bind_setT;
    [exact: (rep_mass r1)|exact: (rep_mass r2)].
- move=> r U mU; rewrite (giry_bindE _ _ (mU _ (rep_random r2))).
  rewrite [LHS]qbs_bind_event//.
  transitivity (\int[g1 r]_t qbs_prob_event Z (g (b1 t)) U).
    apply: (@ge0_integral_sigma_Mx R Y _ b1 _ (g1 r)
      (fun y => qbs_prob_event Z (g y) U)) => //.
    + exact: qbs_prob_alpha_random.
    + exact: rep_random r1.
    + exact: qbs_measurable_event.
    + by move=> V mV; exact: (rep_event r1).
  by apply: eq_integral => t _; rewrite (rep_event r2).
Qed.

Definition qbs_returnQ X : qbsHomType X (monadP X) := @qbs_return X.

Definition qbs_bindQ X Y Z (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) : qbsHomType X (monadP Z) :=
  HB.pack (fun x => qbs_bind (f x) g)
    (isQBSMorphism.Build R X (monadP Z) _ (qbs_bind_morphism f g)).

Lemma qbs_bindQE X Y Z (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) x :
  qbs_bindQ f g x = qbs_bind (f x) g.
Proof. by []. Qed.

(** ** Monad laws *)

Lemma qbs_bind_returnl X Y (x : X) (f : qbsHomType X (monadP Y)) :
  qbs_prob_equiv Y (qbs_bind (qbs_return x) f) (f x).
Proof.
apply/qbs_prob_equivP => U mU; rewrite qbs_bind_event//.
by rewrite /= integral_cst//= diracT mule1.
Qed.

Lemma qbs_bind_returnr X (p : qbs_prob X) :
  qbs_prob_equiv X (qbs_bind p (qbs_returnQ X)) p.
Proof.
apply/qbs_prob_equivP => U mU; rewrite qbs_bind_event//.
under eq_integral do rewrite qbs_return_event.
have mU' := mU _ (qbs_prob_alpha_random p).
rewrite /qbs_prob_event -[in RHS](setIT (qbs_prob_alpha p @^-1` U)).
by rewrite -integral_indic.
Qed.

Lemma qbs_bindA X Y Z (p : qbs_prob X) (f : qbsHomType X (monadP Y))
    (g : qbsHomType Y (monadP Z)) :
  qbs_prob_equiv Z (qbs_bind (qbs_bind p f) g) (qbs_bind p (qbs_bindQ f g)).
Proof.
apply/qbs_prob_equivP => U mU.
have mh := qbs_measurable_event g mU.
have h0 y : 0 <= qbs_prob_event Z (g y) U by [].
rewrite qbs_bind_event//.
rewrite -[LHS]/(qbs_integral Y (qbs_bind p f)
  (fun y => qbs_prob_event Z (g y) U)).
rewrite ge0_qbs_integral_bind// qbs_bind_event//.
by apply: eq_integral => r _; rewrite qbs_bindQE qbs_bind_event.
Qed.

(** ** Functorial action *)

Definition monadP_map X Y (f : qbsHomType X Y) (p : monadP X) :
    monadP Y :=
  mkQBSProb (f \o qbs_prob_alpha p) (qbs_prob_mu p)
    (qbs_hom_proof _ (qbs_prob_alpha_random p)).

Lemma sigma_Mx_preimage X Y (f : qbsHomType X Y) (U : set Y) :
  sigma_Mx U -> sigma_Mx (f @^-1` U).
Proof. by move=> mU a ha; exact: mU _ (qbs_hom_proof _ ha). Qed.

Lemma monadP_map_event X Y (f : qbsHomType X Y) p U :
  qbs_prob_event Y (monadP_map f p) U = qbs_prob_event X p (f @^-1` U).
Proof. by []. Qed.

Lemma monadP_map_morphism X Y (f : qbsHomType X Y) :
  qbs_morphism (X := monadP X) (Y := monadP Y) (monadP_map f).
Proof.
move=> b [a [g [ha mg g1 hb]]]; exists (f \o a), g; split => //.
  exact: qbs_hom_proof.
by move=> r U mU; rewrite /= monadP_map_event hb//; exact: sigma_Mx_preimage.
Qed.

HB.instance Definition _ X Y (f : qbsHomType X Y) :=
  @isQBSMorphism.Build R (monadP X) (monadP Y) (monadP_map f)
    (@monadP_map_morphism X Y f).

Lemma qbs_prob_ext X (p1 p2 : qbs_prob X) :
  qbs_prob_alpha p1 = qbs_prob_alpha p2 ->
  qbs_prob_mu p1 = qbs_prob_mu p2 -> p1 = p2.
Proof.
case: p1 p2 => [a1 m1 h1] [a2 m2 h2] /= ea em; subst a2 m2.
by congr mkQBSProb; exact: Prop_irrelevance.
Qed.

Lemma monadP_map_id X (p : qbs_prob X) : monadP_map (qbs_id X) p = p.
Proof. exact: qbs_prob_ext. Qed.

Lemma monadP_map_comp X Y Z (f : qbsHomType X Y) (g : qbsHomType Y Z)
    (p : qbs_prob X) :
  monadP_map (qbs_comp f g) p = monadP_map g (monadP_map f p).
Proof. exact: qbs_prob_ext. Qed.

Lemma monadP_map_bind X Y (f : qbsHomType X Y) (p : qbs_prob X) :
  qbs_prob_equiv Y (monadP_map f p) (qbs_bind p (qbs_comp f (qbs_returnQ Y))).
Proof.
apply/qbs_prob_equivP => U mU.
rewrite qbs_bind_event// monadP_map_event.
have mU' := sigma_Mx_preimage f mU.
under [RHS]eq_integral do rewrite /= qbs_return_event.
have mA := mU' _ (qbs_prob_alpha_random p).
by rewrite /qbs_prob_event -[in LHS](setIT (_ @^-1` _)) -integral_indic.
Qed.

(** ** Congruence with respect to qbs_prob_equiv *)

Lemma ge0_qbs_integral_equiv X (p1 p2 : qbs_prob X) (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, 0 <= h x) -> qbs_prob_equiv X p1 p2 ->
  qbs_integral X p1 h = qbs_integral X p2 h.
Proof.
move=> mh h0 e; apply: ge0_integral_sigma_Mx => //;
  exact: qbs_prob_alpha_random.
Qed.

Lemma qbs_bind_equiv_l X Y (p1 p2 : qbs_prob X) (f : qbsHomType X (monadP Y)) :
  qbs_prob_equiv X p1 p2 -> qbs_prob_equiv Y (qbs_bind p1 f) (qbs_bind p2 f).
Proof.
move=> e; apply/qbs_prob_equivP => U mU.
rewrite !qbs_bind_event//.
apply: (ge0_qbs_integral_equiv (h := fun x => qbs_prob_event Y (f x) U)) => //.
exact: qbs_measurable_event.
Qed.

Lemma qbs_bind_equiv_r X Y (p : qbs_prob X) (f g : qbsHomType X (monadP Y)) :
  (forall x, qbs_prob_equiv Y (f x) (g x)) ->
  qbs_prob_equiv Y (qbs_bind p f) (qbs_bind p g).
Proof.
move=> e; apply/qbs_prob_equivP => U mU.
by rewrite !qbs_bind_event//; apply: eq_integral => r _; exact: e.
Qed.

Lemma monadP_map_equiv X Y (f : qbsHomType X Y) (p1 p2 : qbs_prob X) :
  qbs_prob_equiv X p1 p2 ->
  qbs_prob_equiv Y (monadP_map f p1) (monadP_map f p2).
Proof. by move=> e U mU; exact: (e _ (sigma_Mx_preimage f mU)). Qed.

(** ** Join *)

Definition qbs_join X (pp : monadP (monadP X)) : monadP X :=
  qbs_bind pp (qbs_id (monadP X)).

Lemma qbs_join_morphism X :
  qbs_morphism (X := monadP (monadP X)) (Y := monadP X) (@qbs_join X).
Proof. exact: qbs_bind_morphism (qbs_id _) (qbs_id _). Qed.

HB.instance Definition _ X :=
  @isQBSMorphism.Build R (monadP (monadP X)) (monadP X) (@qbs_join X)
    (@qbs_join_morphism X).

Definition qbs_joinQ X : qbsHomType (monadP (monadP X)) (monadP X) :=
  @qbs_join X.

Lemma qbs_join_return X (p : monadP X) :
  qbs_prob_equiv X (qbs_join (qbs_return p)) p.
Proof. exact: qbs_bind_returnl p (qbs_id (monadP X)). Qed.

(** ** Strength *)

Section giry_section.
Context (g : mR -> G) (mg : measurable_fun [set: mR] g)
  (g1 : forall r, g r [set: mR] = 1).

Let kg : mR -> {measure set mR -> \bar R}%R := fun r => g r.

Let mkg U : measurable U -> measurable_fun [set: mR] (kg ^~ U).
Proof. by move=> mU; exact: measurableT_comp (measurable_giry_ev mU) mg. Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ kg mkg.
HB.instance Definition _ := Kernel_isProbability.Build _ _ _ _ _ kg g1.

Lemma measurable_giry_xsection (C : set (mR * mR)) : measurable C ->
  measurable_fun [set: mR] (fun r => g r (xsection C r)).
Proof.
by move=> mC; exact: (measurable_fun_xsection_finite_kernel kg (mem_set mC)).
Qed.

End giry_section.

Definition qbs_strength W X (wp : W * monadP X) : monadP (prodQ W X) :=
  mkQBSProb (fun r => (wp.1, qbs_prob_alpha wp.2 r))
    (qbs_prob_mu wp.2) (prodQ_const_random wp.1 (qbs_prob_alpha_random wp.2)).

Lemma qbs_strength_event W X (w : W) (p : monadP X) (U : set (prodQ W X)) :
  qbs_prob_event _ (qbs_strength (w, p)) U =
  qbs_prob_event X p [set x | U (w, x)].
Proof. by []. Qed.

Lemma sigma_Mx_section W X (w : W) (U : set (prodQ W X)) :
  sigma_Mx U -> sigma_Mx [set x : X | U (w, x)].
Proof. by move=> mU a ha; exact: mU _ (prodQ_const_random w ha). Qed.

Lemma qbs_strength_morphism W X :
  qbs_morphism (X := prodQ W (monadP X)) (Y := monadP (prodQ W X))
    (@qbs_strength W X).
Proof.
move=> c [hw [a [g [ha mg g1 hb]]]].
pose e r t : mR := encode_RR_mR (r, t).
have me r : measurable_fun [set: mR] (e r) := measurable_encode r.
pose b t : prodQ W X := ((c ((decode_RR_mR t).1)).1, a (decode_RR_mR t).2).
have be r t : b (e r t) = ((c r).1, a t) by rewrite /b /e encode_RR_mRK.
exists b, (fun r => giry_map (me r) (g r)); split.
- exact: qbs_Mx_decode_pair hw ha.
- apply: measurable_giry_codensity => // B mB.
  have mC : measurable ((@encode_RR_mR R) @^-1` B).
    by rewrite -[A in measurable A]setTI; exact: (@measurable_RR_to_R R).
  have := measurable_giry_xsection mg g1 mC.
  apply: eq_measurable_fun => r _; rewrite /= /pushforward; congr (_ _).
  by apply/seteqP; split => t; rewrite /xsection /= inE.
- by move=> r; rewrite /= /pushforward preimage_setT g1.
- move=> r U mU; rewrite /= qbs_strength_event (hb _ _ (sigma_Mx_section _ mU)).
  rewrite /pushforward; congr (_ _).
  by apply/seteqP; split => t /=; rewrite be.
Qed.

HB.instance Definition _ W X :=
  @isQBSMorphism.Build R (prodQ W (monadP X)) (monadP (prodQ W X))
    (@qbs_strength W X) (@qbs_strength_morphism W X).

Definition qbs_strengthQ W X :
    qbsHomType (prodQ W (monadP X)) (monadP (prodQ W X)) :=
  @qbs_strength W X.

Lemma qbs_strength_return W X (w : W) (x : X) :
  qbs_strength (w, qbs_return x) = qbs_return (w, x).
Proof. exact: qbs_prob_ext. Qed.

(** ** Integration is a morphism (HKSY Sec. V-C) *)

Lemma ge0_monadP_random_integral X (b : mR -> qbs_prob X) (h : X -> \bar R) :
  monadP_random X b -> qbs_measurable X h -> (forall x, 0 <= h x) ->
  measurable_fun [set: mR] (fun r => qbs_integral X (b r) h).
Proof.
move=> [a [g [ha mg _ hb]]] mh h0.
rewrite (_ : (fun r => _) = (giry_int ^~ (h \o a)) \o g).
  apply/funext => r /=; rewrite /giry_int /qbs_integral.
  apply: ge0_integral_sigma_Mx => //; first exact: qbs_prob_alpha_random.
  by move=> U mU; exact: hb.
exact: measurableT_comp (measurable_giry_int (mh _ ha) (fun=> h0 _)) mg.
Qed.

Lemma ge0_qbs_integral_morphism X (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, 0 <= h x) ->
  qbs_morphism (X := monadP X) (Y := R_qbs R (\bar R))
    (fun p => qbs_integral X p h).
Proof. by move=> mh h0 b hb; exact: ge0_monadP_random_integral. Qed.

Definition qbs_swap X Y : qbsHomType (prodQ X Y) (prodQ Y X) :=
  qbs_pair (qbs_snd X Y) (qbs_fst X Y).

(** ** Internal bind (HKSY Thm. 21): bind is a morphism
    P(X) * (X => P(Y)) -> P(Y), obtained from the strength and eval. *)

Definition qbs_bind_internal X Y :
    qbsHomType (prodQ (monadP X) (expQ X (monadP Y))) (monadP Y) :=
  qbs_bindQ (qbs_comp (qbs_swap _ _) (qbs_strengthQ _ _))
    (qbs_eval X (monadP Y)).

Lemma qbs_bind_internalE X Y (p : monadP X) (f : qbsHomType X (monadP Y)) :
  qbs_prob_equiv Y (qbs_bind_internal X Y (p, f)) (qbs_bind p f).
Proof.
apply/qbs_prob_equivP => U mU.
by rewrite qbs_bindQE !qbs_bind_event.
Qed.

(** ** Products and commutativity (HKSY Prop. 22) *)

(** The monadic product: p >>= (fun x => strength (x, q)). *)
Definition monadP_pair X Y (p : monadP X) (q : monadP Y) : monadP (prodQ X Y) :=
  qbs_bind p
    (qbs_comp (qbs_pair (qbs_id X) (qbs_const X q)) (qbs_strengthQ X Y)).

Lemma monadP_pair_event X Y (p : monadP X) (q : monadP Y) (U : set (prodQ X Y)) :
  sigma_Mx U ->
  qbs_prob_event _ (monadP_pair p q) U =
  \int[qbs_prob_mu p]_r qbs_prob_mu q
    [set t | U (qbs_prob_alpha p r, qbs_prob_alpha q t)].
Proof. by move=> mU; rewrite qbs_bind_event. Qed.

Section commutativity.
Context X Y (p : monadP X) (q : monadP Y).

Let ap := qbs_prob_alpha p.
Let aq := qbs_prob_alpha q.

(** The set of pairs of seeds landing in U is measurable. *)
Local Lemma measurable_seeds (U : set (prodQ X Y)) : sigma_Mx U ->
  measurable [set rt : mR * mR | U (ap rt.1, aq rt.2)].
Proof.
move=> mU.
have hb := qbs_Mx_decode_pair (qbs_prob_alpha_random p)
  (qbs_prob_alpha_random q).
have := (@measurable_RR_to_R R) measurableT _ (mU _ hb); rewrite setTI.
have E : (fun s : mR => (ap (decode_RR_mR s).1, aq (decode_RR_mR s).2) : X * Y)
    \o (@encode_RR_mR R) = (fun rt : mR * mR => (ap rt.1, aq rt.2) : X * Y).
  by apply/funext => rt; rewrite /comp encode_RR_mRK.
by rewrite -comp_preimage E.
Qed.

Lemma monadP_pair_comm :
  qbs_prob_equiv (prodQ X Y) (monadP_pair p q)
    (monadP_map (qbs_swap Y X) (monadP_pair q p)).
Proof.
apply/qbs_prob_equivP => U mU.
rewrite monadP_map_event monadP_pair_event//.
rewrite (monadP_pair_event _ _ (sigma_Mx_preimage (qbs_swap Y X) mU)).
have mA := measurable_seeds mU.
pose A := [set rt : mR * mR | U (ap rt.1, aq rt.2)].
pose f (rt : mR * mR) := ((\1_A rt : R)%:E).
have mf : measurable_fun [set: mR * mR] f.
  exact/measurable_EFinP/measurable_indic.
have f0 rt : 0 <= f rt by rewrite lee_fin indicE ler0n.
transitivity (\int[qbs_prob_mu p]_r \int[qbs_prob_mu q]_t f (r, t)).
  apply: eq_integral => r _.
  have mS : measurable [set t | U (ap r, aq t)].
    have := measurable_xsection r mA; congr measurable.
    by apply/seteqP; split => t; rewrite /xsection /= inE.
  by rewrite -[A in qbs_prob_mu q A]setIT -integral_indic.
rewrite (fubini_tonelli (m1 := qbs_prob_mu p) (m2 := qbs_prob_mu q) f mf f0).
apply: eq_integral => t _.
have mS : measurable [set r | (qbs_swap Y X @^-1` U) (aq t, ap r)].
  have := measurable_ysection t mA; congr measurable.
  by apply/seteqP; split => r; rewrite /ysection /= inE.
by rewrite -[A in qbs_prob_mu p A]setIT -integral_indic.
Qed.

End commutativity.

Lemma qbs_bind_map X Y Z (g : qbsHomType X Y) (p : monadP X)
    (f : qbsHomType Y (monadP Z)) :
  qbs_prob_equiv Z (qbs_bind (monadP_map g p) f) (qbs_bind p (qbs_comp g f)).
Proof.
apply/qbs_prob_equivP => U mU.
by rewrite !qbs_bind_event.
Qed.

(** Commutativity of the probability monad (HKSY Prop. 22(2)). *)
Lemma qbs_bind_comm X Y Z (p : monadP X) (q : monadP Y)
    (f : qbsHomType (prodQ X Y) (monadP Z)) :
  qbs_prob_equiv Z (qbs_bind (monadP_pair p q) f)
    (qbs_bind (monadP_pair q p) (qbs_comp (qbs_swap Y X) f)).
Proof.
apply: qbs_prob_equiv_trans (qbs_bind_map _ _ _).
exact/qbs_bind_equiv_l/monadP_pair_comm.
Qed.

(** ** Join and strength laws *)

Lemma qbs_join_map_return X (p : monadP X) :
  qbs_prob_equiv X (qbs_join (monadP_map (qbs_returnQ X) p)) p.
Proof.
apply: qbs_prob_equiv_trans (qbs_bind_map _ _ _) _.
exact: qbs_bind_returnr.
Qed.

Lemma qbs_join_assoc X (P : monadP (monadP (monadP X))) :
  qbs_prob_equiv X (qbs_join (qbs_join P))
    (qbs_join (monadP_map (qbs_joinQ X) P)).
Proof.
apply: qbs_prob_equiv_trans (qbs_bindA _ _ _) _.
apply: qbs_prob_equiv_sym; apply: qbs_prob_equiv_trans (qbs_bind_map _ _ _) _.
exact: qbs_bind_equiv_r.
Qed.

Lemma qbs_strength_natural W W' X X' (f : qbsHomType W W')
    (g : qbsHomType X X') (w : W) (p : monadP X) :
  qbs_strength (f w, monadP_map g p) =
  monadP_map (qbs_pair (qbs_comp (qbs_fst W X) f) (qbs_comp (qbs_snd W X) g))
    (qbs_strength (w, p)).
Proof. exact: qbs_prob_ext. Qed.

Lemma qbs_strength_snd W X (w : W) (p : monadP X) :
  monadP_map (qbs_snd W X) (qbs_strength (w, p)) = p.
Proof. exact: qbs_prob_ext. Qed.

Definition qbs_assoc (U W X : qbsType R) :
    qbsHomType (prodQ (prodQ U W) X) (prodQ U (prodQ W X)) :=
  qbs_pair (qbs_comp (qbs_fst _ X) (qbs_fst U W))
    (qbs_pair (qbs_comp (qbs_fst _ X) (qbs_snd U W)) (qbs_snd _ X)).

Lemma qbs_strength_assoc (U W X : qbsType R) (u : U) (w : W) (p : monadP X) :
  qbs_strength (u, qbs_strength (w, p)) =
  monadP_map (qbs_assoc U W X) (qbs_strength ((u, w), p)).
Proof. exact: qbs_prob_ext. Qed.

Lemma qbs_strength_join W X (w : W) (P : monadP (monadP X)) :
  qbs_prob_equiv (prodQ W X) (qbs_strength (w, qbs_join P))
    (qbs_join (monadP_map (qbs_strengthQ W X) (qbs_strength (w, P)))).
Proof.
apply/qbs_prob_equivP => U mU.
rewrite qbs_strength_event /qbs_join !qbs_bind_event//.
exact: sigma_Mx_section.
Qed.

End probability_monad.

Arguments monadP_random {R} X.
Arguments monadP {R} X.
