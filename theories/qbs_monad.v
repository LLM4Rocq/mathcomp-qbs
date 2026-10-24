(* QBS project. License: CeCILL-C.                                            *)
From HB Require Import structures.
From mathcomp Require Import boot algebra reals ereal topology classical_sets
  boolp numfun measure measurable_realfun lebesgue_measure lebesgue_integral
  lebesgue_stieltjes_measure probability.
From mathcomp Require Import giry kernel lebesgue_integral_fubini.
From QBS Require Import measurable_aux quasi_borel standard_borel
  probability_qbs.

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
(*          qbs_rep b a g == b r is represented by [a, g r] for every r       *)
(*                  probQ X == the QBS of probabilities on X (HKSY P(X))      *)
(*                qbs_return x == the Dirac probability at x                  *)
(*                qbs_bind p f == bind, for f : qbsHomType X (probQ Y)        *)
(*              qbs_map f p == pushforward of p along f : qbsHomType X Y      *)
(*                 qbs_join pp == multiplication P(P(X)) -> P(X)              *)
(*         strength (w, p) == strength W * P(X) -> P(W * X)                   *)
(*             assoc U W X == associativity (U * W) * X -> U * (W * X)        *)
(*      qbs_returnQ, qbs_bindQ == return and bind as qbsHomType morphisms     *)
(*    qbs_joinQ, strengthQ == join and strength as qbsHomType morphisms       *)
(*       qbs_bind_internal X Y == bind as P(X) * (X => P(Y)) -> P(Y)          *)
(* qbs_swap X Y, qbs_prod p q == swap; monadic product of p, q                *)
(* ```                                                                        *)
(*                                                                            *)
(* The monad laws (qbs_bind_returnl, qbs_bind_returnr, qbs_bindA), the        *)
(* strength laws (strength_snd, strength_assoc, strength_return,              *)
(* strength_join) and commutativity (qbs_bind_comm) are equalities,           *)
(* proved with qbs_eqP from the computation lemmas qbs_return_event,          *)
(* qbs_bind_event, qbs_map_event and strength_event.                          *)
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
Local Abbreviation mR := (measurableTypeR R).
Local Abbreviation G := (giry mR R).
Implicit Types (W X Y Z : qbsType R).

(** ** The QBS of probabilities *)

Record qbs_rep X (b : mR -> probQ X) (a : mR -> X) (g : mR -> G) :
    Prop := QbsProbRep {
  qbs_rep_random : qbs_Mx a ;
  qbs_rep_measurable : measurable_fun [set: mR] g ;
  qbs_rep_mass : forall r, g r [set: mR] = 1 ;
  qbs_rep_event : forall r U, sigma_Mx U ->
    qbs_event X (b r) U = g r (a @^-1` U) }.

Local Definition qbs_random X : set (mR -> probQ X) :=
  [set b | exists a g, qbs_rep b a g].
Local Arguments qbs_random : clear implicits.

Local Lemma qbs_random_comp X (b : mR -> probQ X) (f : {mfun mR >-> mR}) :
  qbs_random X b -> qbs_random X (b \o f).
Proof.
move=> [a [g [ha mg g1 hb]]]; exists a, (g \o f).
exact: QbsProbRep ha (measurableT_comp mg (measurable_funPT f))
  (fun r => g1 (f r)) (fun r => hb (f r)).
Qed.

Local Lemma qbs_random_const X (p : probQ X) :
  qbs_random X (fun=> p).
Proof.
exists (qbs_alpha p), (fun=> qbs_mu p); split=> //.
  exact: qbs_alpha_random.
by move=> _; exact: probability_setT.
Qed.

Local Lemma measurable_encode r :
  measurable_fun [set: mR] (fun t => encode_RR_mR (r, t)).
Proof.
exact: measurableT_comp measurable_RR_to_R (pair1_measurable _).
Qed.

Local Lemma measurable_decode1 :
  measurable_fun [set: mR] (fst \o decode_RR_mR).
Proof. exact: measurableT_comp measurable_fst measurable_R_to_RR. Qed.

Local Lemma measurable_decode2 :
  measurable_fun [set: mR] (snd \o decode_RR_mR).
Proof. exact: measurableT_comp measurable_snd measurable_R_to_RR. Qed.

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
Context X (P : {mfun mR >-> nat}) (F : nat -> mR -> probQ X).
Hypothesis hF : forall i, qbs_random X (F i).

Let enc (n : nat) (y : mR) : mR := encode_RR_mR (n%:R%R, y).
Let menc n : measurable_fun [set: mR] (enc n) := measurable_encode _.
Let idx (r : mR) : nat := truncn (decode_RR_mR r).1.
Let snd' (r : mR) : mR := (decode_RR_mR r).2.

Let midx : measurable_fun [set: mR] idx :=
  measurableT_comp measurable_truncn measurable_decode1.

Let msnd : measurable_fun [set: mR] snd' := measurable_decode2.

Let idx_enc n y : idx (enc n y) = n.
Proof. by rewrite /idx /enc encode_RR_mRK /= natrK. Qed.

Let snd_enc n y : snd' (enc n y) = y.
Proof. by rewrite /snd' /enc encode_RR_mRK. Qed.

Local Lemma qbs_random_glue : qbs_random X (fun r => F (P r) r).
Proof.
have /choice[ag hag] : forall i, exists ag : (mR -> X) * (mR -> G),
    qbs_rep (F i) ag.1 ag.2.
  by move=> i; have [a [g h]] := hF i; exists (a, g).
pose a' r := (ag (idx r)).1 (snd' r).
pose g' r := giry_map (menc (P r)) ((ag (P r)).2 r).
have a'enc n y : a' (enc n y) = (ag n).1 y by rewrite /a' idx_enc snd_enc.
exists a', g'; split.
- apply: (qbs_Mx_glueT (P := idx) (Fi := fun n => (ag n).1 \o snd')) midx _.
  by move=> n; exact: qbs_Mx_compT (qbs_rep_random (hag n)) msnd.
- apply: (measurable_glue (P := P)
    (Fi := fun n r => giry_map (menc n) ((ag n).2 r))) => [|n].
    exact: measurable_funPT.
  exact: measurableT_comp (measurable_giry_map _) (qbs_rep_measurable (hag n)).
- by move=> r; rewrite /g' /= /pushforward preimage_setT (qbs_rep_mass (hag _)).
- move=> r U mU; rewrite (qbs_rep_event (hag _))// /g' /= /pushforward.
  by congr (_ _); apply/seteqP; split=> y /=; rewrite a'enc.
Qed.

End glue.

HB.instance Definition _ X :=
  isQBS.Build R (probQ X) (@qbs_random_comp X) (@qbs_random_const X)
    (@qbs_random_glue X).

Lemma measurable_qbs_event X (b : mR -> probQ X) (U : set X) :
  qbs_Mx (s := probQ X) b -> sigma_Mx U ->
  measurable_fun [set: mR] (fun r => qbs_event X (b r) U).
Proof.
move=> [a [g [ha mg _ hb]]] mU.
rewrite (_ : (fun r => _) = (giry_ev ^~ (a @^-1` U)) \o g).
  by apply/funext => r; rewrite /= hb.
exact: measurableT_comp (measurable_giry_ev (mU _ ha)) mg.
Qed.

Lemma qbs_measurable_event X Y (f : qbsHomType X (probQ Y)) (U : set Y) :
  sigma_Mx U -> qbs_measurable X (fun x => qbs_event Y (f x) U).
Proof.
by move=> mU b hb; apply: measurable_qbs_event mU; exact: qbs_hom_proof.
Qed.

Lemma sigma_Mx_preimage X Y (f : qbsHomType X Y) (U : set Y) :
  sigma_Mx U -> sigma_Mx (f @^-1` U).
Proof. by move=> mU a ha; exact: mU _ (qbs_hom_proof _ ha). Qed.

Lemma sigma_Mx_section W X (w : W) (U : set (prodQ W X)) :
  sigma_Mx U -> sigma_Mx [set x : X | U (w, x)].
Proof. by move=> mU a ha; exact: mU _ (qbs_Mx_pair_cstl w ha). Qed.

(** The probability of an event is the integral of its indicator. *)
Lemma qbs_event_integral X (p : probQ X) (U : set X) :
  sigma_Mx U ->
  qbs_event X p U = qbs_integral X p (fun x => (x \in U)%:R%:E).
Proof.
move=> mU; have mU' := mU _ (qbs_alpha_random p).
by rewrite /qbs_event -[X in qbs_mu p X]setIT -integral_indic.
Qed.

(** ** Return *)

Definition qbs_return X (x : X) : probQ X :=
  mkQBSProb (fun=> x) (\d_(0 : mR))%R (qbs_Mx_const x).

Lemma qbs_return_event X (x : X) (U : set X) : sigma_Mx U ->
  qbs_event X (qbs_return x) U = (x \in U)%:R%:E.
Proof.
by move=> mU; rewrite qbs_event_mk// diracE.
Qed.

Lemma qbs_morphism_return X : qbs_morphism (X := X) (Y := probQ X)
  (@qbs_return X).
Proof.
move=> a ha; exists a, (@giry_ret _ mR R); split=> //.
- exact: measurable_giry_ret.
- by move=> r; exact: diracT.
- by move=> r U mU; rewrite qbs_return_event// /= diracE.
Qed.

HB.instance Definition _ X :=
  isQBSMorphism.Build R X (probQ X) (@qbs_return X)
    (@qbs_morphism_return X).

Lemma qbs_return_integral X (x : X) (h : X -> \bar R) : qbs_measurable X h ->
  qbs_integral X (qbs_return x) h = h x.
Proof.
by move=> mh; rewrite qbs_integral_mk// integral_cst//= diracT mule1.
Qed.

(** ** Bind *)

Section bind.
Context X Y (p : probQ X) (f : qbsHomType X (probQ Y)).

Let hf : qbs_random Y (f \o qbs_alpha p) :=
  qbs_hom_proof _ (qbs_alpha_random p).

Let bind_a : mR -> Y := sval (cid hf).
Let bind_g : mR -> G := sval (cid (svalP (cid hf))).
Let bind_rep : qbs_rep (f \o qbs_alpha p) bind_a bind_g :=
  svalP (cid (svalP (cid hf))).

Let bind_mu : G := giry_bind (qbs_mu p) (qbs_rep_measurable bind_rep).
Let bind_mu1 : bind_mu [set: mR] = 1.
Proof.
by apply: giry_bind_setT;
    [exact: probability_setT|exact: qbs_rep_mass bind_rep].
Qed.

Definition qbs_bind : probQ Y :=
  mkQBSProb bind_a (giry_prob bind_mu1) (qbs_rep_random bind_rep).

Lemma ge0_qbs_integral_bind (h : Y -> \bar R) :
  qbs_measurable Y h -> (forall y, 0 <= h y) ->
  qbs_integral Y qbs_bind h =
  qbs_integral X p (fun x => qbs_integral Y (f x) h).
Proof.
move=> mh h0; rewrite qbs_integral_mk//.
have mha := mh _ (qbs_rep_random bind_rep).
rewrite [LHS](giry_int_bind (qbs_mu p) (qbs_rep_measurable bind_rep)
  (h := h \o bind_a))//; first by move=> ?; exact: h0.
rewrite /giry_int; apply: eq_integral => r _.
apply: (ge0_integral_sigma_Mx (k := h)) => //.
- exact: qbs_rep_random bind_rep.
- exact: qbs_alpha_random.
- by move=> U mU; exact/esym/(qbs_rep_event bind_rep).
Qed.

Lemma qbs_bind_event (U : set Y) : sigma_Mx U ->
  qbs_event Y qbs_bind U =
  qbs_integral X p (fun x => qbs_event Y (f x) U).
Proof.
move=> mU; rewrite qbs_event_mk// /= giry_int_map//.
  exact: measurable_giry_ev (mU _ (qbs_rep_random bind_rep)).
by apply: eq_integral => r _; exact/esym/(qbs_rep_event bind_rep).
Qed.

End bind.

(** Bind with a fixed continuation is a morphism. *)
Lemma qbs_morphism_bind X Y Z (f : qbsHomType X (probQ Y))
    (g : qbsHomType Y (probQ Z)) :
  qbs_morphism (X := X) (Y := probQ Z) (fun x => qbs_bind (f x) g).
Proof.
move=> a ha.
have [b1 [g1 r1]] : qbs_random Y (f \o a) := qbs_hom_proof _ ha.
have [b2 [g2 r2]] : qbs_random Z (g \o b1) :=
  qbs_hom_proof _ (qbs_rep_random r1).
exists b2, (fun r => giry_bind (g1 r) (qbs_rep_measurable r2)); split.
- exact: qbs_rep_random r2.
- exact: measurableT_comp (measurable_giry_bind _) (qbs_rep_measurable r1).
- by move=> r; apply: giry_bind_setT;
    [exact: (qbs_rep_mass r1)|exact: (qbs_rep_mass r2)].
- move=> r U mU; rewrite (giry_bindE _ _ (mU _ (qbs_rep_random r2))).
  rewrite [LHS]qbs_bind_event//.
  transitivity (\int[g1 r]_t qbs_event Z (g (b1 t)) U).
    apply: ge0_integral_sigma_Mx => //.
    + exact: qbs_alpha_random.
    + exact: qbs_rep_random r1.
    + by move=> V mV; exact: (qbs_rep_event r1).
    + exact: qbs_measurable_event.
  by apply: eq_integral => t _; rewrite (qbs_rep_event r2).
Qed.

Definition qbs_returnQ X : qbsHomType X (probQ X) := @qbs_return X.

Definition qbs_bindQ X Y Z (f : qbsHomType X (probQ Y))
    (g : qbsHomType Y (probQ Z)) : qbsHomType X (probQ Z) :=
  HB.pack (fun x => qbs_bind (f x) g)
    (isQBSMorphism.Build R X (probQ Z) _ (qbs_morphism_bind f g)).

Lemma qbs_bindQE X Y Z (f : qbsHomType X (probQ Y))
    (g : qbsHomType Y (probQ Z)) x :
  qbs_bindQ f g x = qbs_bind (f x) g.
Proof. by []. Qed.

(** ** Monad laws *)

Lemma qbs_bind_returnl X Y (x : X) (f : qbsHomType X (probQ Y)) :
  qbs_bind (qbs_return x) f = f x.
Proof.
apply/qbs_eqP => U mU; rewrite qbs_bind_event// qbs_return_integral//.
exact: qbs_measurable_event.
Qed.

Lemma qbs_bind_returnr X (p : probQ X) : qbs_bind p (qbs_returnQ X) = p.
Proof.
apply/qbs_eqP => U mU; rewrite qbs_bind_event// qbs_event_integral//.
by apply: eq_integral => r _; rewrite qbs_return_event.
Qed.

Lemma qbs_bindA X Y Z (p : probQ X) (f : qbsHomType X (probQ Y))
    (g : qbsHomType Y (probQ Z)) :
  qbs_bind (qbs_bind p f) g = qbs_bind p (qbs_bindQ f g).
Proof.
apply/qbs_eqP => U mU; have mh := qbs_measurable_event g mU.
rewrite !qbs_bind_event// ge0_qbs_integral_bind//.
by apply: eq_integral => r _; rewrite qbs_bindQE qbs_bind_event.
Qed.

Lemma eq_qbs_bind X Y (p : probQ X) (f g : qbsHomType X (probQ Y)) :
  f =1 g -> qbs_bind p f = qbs_bind p g.
Proof.
move=> fg; apply/qbs_eqP => U mU; rewrite !qbs_bind_event//.
by apply: eq_integral => r _; rewrite fg.
Qed.

(** ** Functorial action *)

Definition qbs_map X Y (f : qbsHomType X Y) (p : probQ X) :
    probQ Y :=
  mkQBSProb (f \o qbs_alpha p) (qbs_mu p)
    (qbs_hom_proof _ (qbs_alpha_random p)).

Lemma qbs_map_event X Y (f : qbsHomType X Y) p U : sigma_Mx U ->
  qbs_event Y (qbs_map f p) U = qbs_event X p (f @^-1` U).
Proof. exact: qbs_event_mk. Qed.

Lemma qbs_map_integral X Y (f : qbsHomType X Y) p (h : Y -> \bar R) :
  qbs_measurable Y h ->
  qbs_integral Y (qbs_map f p) h = qbs_integral X p (h \o f).
Proof. exact: qbs_integral_mk. Qed.

Lemma qbs_map_integrable X Y (f : qbsHomType X Y) p (h : Y -> \bar R) :
  qbs_measurable Y h ->
  qbs_integrable Y (qbs_map f p) h <-> qbs_integrable X p (h \o f).
Proof. exact: qbs_integrable_mk. Qed.

Lemma qbs_map_variance X Y (f : qbsHomType X Y) p (h : Y -> R) :
  qbs_measurable Y (fun y => (h y)%:E) ->
  qbs_variance Y (qbs_map f p) h = qbs_variance X p (h \o f).
Proof. exact: qbs_variance_mk. Qed.

Lemma qbs_morphism_map X Y (f : qbsHomType X Y) :
  qbs_morphism (X := probQ X) (Y := probQ Y) (qbs_map f).
Proof.
move=> b [a [g [ha mg g1 hb]]]; exists (f \o a), g; split=> //.
  exact: qbs_hom_proof.
move=> r U mU; rewrite qbs_map_event// hb//.
exact: sigma_Mx_preimage.
Qed.

HB.instance Definition _ X Y (f : qbsHomType X Y) :=
  isQBSMorphism.Build R (probQ X) (probQ Y) (qbs_map f)
    (qbs_morphism_map f).

Lemma qbs_map_id X (p : probQ X) : qbs_map (qbs_id X) p = p.
Proof. by apply/qbs_eqP => U mU; rewrite qbs_map_event. Qed.

Lemma qbs_map_comp X Y Z (f : qbsHomType X Y) (g : qbsHomType Y Z)
    (p : probQ X) :
  qbs_map (qbs_comp f g) p = qbs_map g (qbs_map f p).
Proof.
apply/qbs_eqP => U mU; rewrite !qbs_map_event//.
exact: sigma_Mx_preimage.
Qed.

Lemma qbs_map_bind X Y (f : qbsHomType X Y) (p : probQ X) :
  qbs_map f p = qbs_bind p (qbs_comp f (qbs_returnQ Y)).
Proof.
apply/qbs_eqP => U mU; have mU' := sigma_Mx_preimage f mU.
rewrite qbs_bind_event// qbs_map_event// qbs_event_integral//.
by apply: eq_integral => r _; rewrite /= qbs_return_event.
Qed.

Lemma qbs_bind_map X Y Z (g : qbsHomType X Y) (p : probQ X)
    (f : qbsHomType Y (probQ Z)) :
  qbs_bind (qbs_map g p) f = qbs_bind p (qbs_comp g f).
Proof.
apply/qbs_eqP => U mU; rewrite !qbs_bind_event// qbs_map_integral//.
exact: qbs_measurable_event.
Qed.

(** ** Join *)

Definition qbs_join X (pp : probQ (probQ X)) : probQ X :=
  qbs_bind pp (qbs_id (probQ X)).

Lemma qbs_morphism_join X :
  qbs_morphism (X := probQ (probQ X)) (Y := probQ X) (@qbs_join X).
Proof. exact: qbs_morphism_bind (qbs_id _) (qbs_id _). Qed.

HB.instance Definition _ X :=
  isQBSMorphism.Build R (probQ (probQ X)) (probQ X) (@qbs_join X)
    (@qbs_morphism_join X).

Definition qbs_joinQ X : qbsHomType (probQ (probQ X)) (probQ X) :=
  @qbs_join X.

Lemma qbs_join_return X (p : probQ X) : qbs_join (qbs_return p) = p.
Proof. exact: qbs_bind_returnl p (qbs_id (probQ X)). Qed.

Lemma qbs_join_map_return X (p : probQ X) :
  qbs_join (qbs_map (qbs_returnQ X) p) = p.
Proof. by rewrite /qbs_join qbs_bind_map; exact: qbs_bind_returnr. Qed.

Lemma qbs_join_assoc X (P : probQ (probQ (probQ X))) :
  qbs_join (qbs_join P) = qbs_join (qbs_map (qbs_joinQ X) P).
Proof. by rewrite /qbs_join qbs_bindA qbs_bind_map; exact: eq_qbs_bind. Qed.

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

Definition strength W X (wp : W * probQ X) : probQ (prodQ W X) :=
  mkQBSProb (fun r => (wp.1, qbs_alpha wp.2 r))
    (qbs_mu wp.2) (qbs_Mx_pair_cstl wp.1 (qbs_alpha_random wp.2)).

Lemma strength_event W X (w : W) (p : probQ X) (U : set (prodQ W X)) :
  sigma_Mx U ->
  qbs_event _ (strength (w, p)) U =
  qbs_event X p [set x | U (w, x)].
Proof. exact: qbs_event_mk. Qed.

Lemma strength_integral W X (w : W) (p : probQ X)
    (h : prodQ W X -> \bar R) : qbs_measurable _ h ->
  qbs_integral _ (strength (w, p)) h = qbs_integral X p (fun x => h (w, x)).
Proof. exact: qbs_integral_mk. Qed.

Lemma qbs_morphism_strength W X :
  qbs_morphism (X := prodQ W (probQ X)) (Y := probQ (prodQ W X))
    (@strength W X).
Proof.
move=> c [hw [a [g [ha mg g1 hb]]]].
pose e r t : mR := encode_RR_mR (r, t).
have me r : measurable_fun [set: mR] (e r) := measurable_encode r.
pose b t : prodQ W X := ((c ((decode_RR_mR t).1)).1, a (decode_RR_mR t).2).
have be r t : b (e r t) = ((c r).1, a t) by rewrite /b /e encode_RR_mRK.
exists b, (fun r => giry_map (me r) (g r)); split.
- exact: qbs_Mx_decode_pair hw ha.
- apply: measurable_giry_codensity => // B mB.
  have mC : measurable (encode_RR_mR @^-1` B).
    by rewrite -[A in measurable A]setTI; exact: measurable_RR_to_R.
  have := measurable_giry_xsection mg g1 mC.
  apply: eq_measurable_fun => r _; rewrite /= /pushforward; congr (_ _).
  by apply/seteqP; split=> t; rewrite /xsection /= inE.
- by move=> r; rewrite /= /pushforward preimage_setT g1.
- move=> r U mU; rewrite /= strength_event//.
  rewrite (hb _ _ (sigma_Mx_section _ mU)) /pushforward; congr (_ _).
  by apply/seteqP; split=> t /=; rewrite be.
Qed.

HB.instance Definition _ W X :=
  isQBSMorphism.Build R (prodQ W (probQ X)) (probQ (prodQ W X))
    (@strength W X) (@qbs_morphism_strength W X).

Definition strengthQ W X :
    qbsHomType (prodQ W (probQ X)) (probQ (prodQ W X)) :=
  @strength W X.

Lemma strength_return W X (w : W) (x : X) :
  strength (w, qbs_return x) = qbs_return (w, x).
Proof.
apply/qbs_eqP => U mU.
by rewrite strength_event// !qbs_return_event//; exact: sigma_Mx_section.
Qed.

(** ** Integration is a morphism (HKSY Sec. V-C) *)

Lemma ge0_measurable_qbs_integral X (b : mR -> probQ X) (h : X -> \bar R) :
  qbs_Mx (s := probQ X) b -> qbs_measurable X h -> (forall x, 0 <= h x) ->
  measurable_fun [set: mR] (fun r => qbs_integral X (b r) h).
Proof.
move=> [a [g [ha mg _ hb]]] mh h0.
rewrite (_ : (fun r => _) = (giry_int ^~ (h \o a)) \o g).
  apply/funext => r /=; rewrite /giry_int /qbs_integral.
  apply: ge0_integral_sigma_Mx => //; first exact: qbs_alpha_random.
  by move=> U mU; exact: hb.
exact: measurableT_comp (measurable_giry_int (mh _ ha) (fun=> h0 _)) mg.
Qed.

Lemma ge0_qbs_morphism_integral X (h : X -> \bar R) :
  qbs_measurable X h -> (forall x, 0 <= h x) ->
  qbs_morphism (X := probQ X) (Y := measQ R (\bar R))
    (fun p => qbs_integral X p h).
Proof. by move=> mh h0 b hb; exact: ge0_measurable_qbs_integral. Qed.

Lemma ge0_qbs_measurable_integral X Y (f : qbsHomType X (probQ Y))
    (h : Y -> \bar R) : qbs_measurable Y h -> (forall y, 0 <= h y) ->
  qbs_measurable X (fun x => qbs_integral Y (f x) h).
Proof.
move=> mh h0 a ha.
exact: (ge0_measurable_qbs_integral (b := f \o a)) (qbs_hom_proof _ ha) mh h0.
Qed.

Definition qbs_swap X Y : qbsHomType (prodQ X Y) (prodQ Y X) :=
  qbs_pair (qbs_snd X Y) (qbs_fst X Y).

(** ** Internal bind (HKSY Thm. 21): bind is a morphism
    P(X) * (X => P(Y)) -> P(Y), obtained from the strength and eval. *)

Definition qbs_bind_internal X Y :
    qbsHomType (prodQ (probQ X) (expQ X (probQ Y))) (probQ Y) :=
  qbs_bindQ (qbs_comp (qbs_swap _ _) (strengthQ _ _))
    (qbs_eval X (probQ Y)).

Lemma qbs_bind_internalE X Y (p : probQ X) (f : qbsHomType X (probQ Y)) :
  qbs_bind_internal X Y (p, f) = qbs_bind p f.
Proof.
apply/qbs_eqP => U mU; rewrite qbs_bindQE !qbs_bind_event//=.
rewrite strength_integral//.
exact: (qbs_measurable_event (qbs_eval X (probQ Y))).
Qed.

(** ** Products and commutativity (HKSY Prop. 22) *)

(** The monadic product: p >>= (fun x => strength (x, q)). *)
Definition qbs_prod X Y (p : probQ X) (q : probQ Y) : probQ (prodQ X Y) :=
  qbs_bind p
    (qbs_comp (qbs_pair (qbs_id X) (qbs_const X q)) (strengthQ X Y)).

Lemma qbs_prod_event X Y (p : probQ X) (q : probQ Y)
    (U : set (prodQ X Y)) :
  sigma_Mx U ->
  qbs_event _ (qbs_prod p q) U =
  \int[qbs_mu p]_r qbs_mu q
    [set t | U (qbs_alpha p r, qbs_alpha q t)].
Proof.
move=> mU; rewrite qbs_bind_event//; apply: eq_integral => r _.
by rewrite /= strength_event.
Qed.

Section commutativity.
Context X Y (p : probQ X) (q : probQ Y).

Let ap := qbs_alpha p.
Let aq := qbs_alpha q.

(** The set of pairs of seeds landing in U is measurable. *)
Local Lemma measurable_seeds (U : set (prodQ X Y)) : sigma_Mx U ->
  measurable [set rt : mR * mR | U (ap rt.1, aq rt.2)].
Proof.
move=> mU.
have hb := qbs_Mx_decode_pair (qbs_alpha_random p)
  (qbs_alpha_random q).
have := measurable_RR_to_R measurableT (mU _ hb); rewrite setTI.
have E : (fun s : mR => (ap (decode_RR_mR s).1, aq (decode_RR_mR s).2))
    \o encode_RR_mR = (fun rt : mR * mR => (ap rt.1, aq rt.2)).
  by apply/funext => rt; rewrite /comp encode_RR_mRK.
by rewrite -comp_preimage E.
Qed.

Lemma qbs_prod_comm :
  qbs_prod p q = qbs_map (qbs_swap Y X) (qbs_prod q p).
Proof.
apply/qbs_eqP => U mU; have mU' := sigma_Mx_preimage (qbs_swap Y X) mU.
rewrite qbs_map_event// !qbs_prod_event//.
have mA := measurable_seeds mU.
pose A := [set rt : mR * mR | U (ap rt.1, aq rt.2)].
pose f (rt : mR * mR) := ((\1_A rt : R)%:E).
have mf : measurable_fun [set: mR * mR] f.
  exact/measurable_EFinP/measurable_indic.
have f0 rt : 0 <= f rt by rewrite lee_fin indicE ler0n.
transitivity (\int[qbs_mu p]_r \int[qbs_mu q]_t f (r, t)).
  apply: eq_integral => r _.
  have mS : measurable [set t | U (ap r, aq t)].
    have := measurable_xsection r mA; congr measurable.
    by apply/seteqP; split=> t; rewrite /xsection /= inE.
  by rewrite -[A in qbs_mu q A]setIT -integral_indic.
rewrite (fubini_tonelli (m1 := qbs_mu p) (m2 := qbs_mu q) f mf f0).
apply: eq_integral => t _.
have mS : measurable [set r | (qbs_swap Y X @^-1` U) (aq t, ap r)].
  have := measurable_ysection t mA; congr measurable.
  by apply/seteqP; split=> r; rewrite /ysection /= inE.
by rewrite -[A in qbs_mu p A]setIT -integral_indic.
Qed.

End commutativity.

(** Commutativity of the probability monad (HKSY Prop. 22(2)). *)
Lemma qbs_bind_comm X Y Z (p : probQ X) (q : probQ Y)
    (f : qbsHomType (prodQ X Y) (probQ Z)) :
  qbs_bind (qbs_prod p q) f =
  qbs_bind (qbs_prod q p) (qbs_comp (qbs_swap Y X) f).
Proof. by rewrite qbs_prod_comm qbs_bind_map. Qed.

(** ** Strength laws *)

Lemma strength_natural W W' X X' (f : qbsHomType W W')
    (g : qbsHomType X X') (w : W) (p : probQ X) :
  strength (f w, qbs_map g p) =
  qbs_map (qbs_pair (qbs_comp (qbs_fst W X) f) (qbs_comp (qbs_snd W X) g))
    (strength (w, p)).
Proof.
apply/qbs_eqP => U mU; have mS := sigma_Mx_section (f w) mU.
rewrite qbs_map_event// strength_event// qbs_map_event//.
by rewrite strength_event//; exact: sigma_Mx_preimage.
Qed.

Lemma strength_snd W X (w : W) (p : probQ X) :
  qbs_map (qbs_snd W X) (strength (w, p)) = p.
Proof.
apply/qbs_eqP => U mU; rewrite qbs_map_event// strength_event//.
exact: sigma_Mx_preimage.
Qed.

Definition assoc (U W X : qbsType R) :
    qbsHomType (prodQ (prodQ U W) X) (prodQ U (prodQ W X)) :=
  qbs_pair (qbs_comp (qbs_fst _ X) (qbs_fst U W))
    (qbs_pair (qbs_comp (qbs_fst _ X) (qbs_snd U W)) (qbs_snd _ X)).

Lemma strength_assoc (U W X : qbsType R) (u : U) (w : W) (p : probQ X) :
  strength (u, strength (w, p)) =
  qbs_map (assoc U W X) (strength ((u, w), p)).
Proof.
apply/qbs_eqP => V mV; have mS := sigma_Mx_section u mV.
have mA := sigma_Mx_preimage (assoc U W X) mV.
by rewrite qbs_map_event// !strength_event.
Qed.

Lemma strength_join W X (w : W) (P : probQ (probQ X)) :
  strength (w, qbs_join P) =
  qbs_join (qbs_map (strengthQ W X) (strength (w, P))).
Proof.
apply/qbs_eqP => U mU; have mS := sigma_Mx_section w mU.
rewrite strength_event// /qbs_join !qbs_bind_event//.
rewrite qbs_map_integral; first exact: (qbs_measurable_event (qbs_id _)).
rewrite strength_integral.
  exact: (qbs_measurable_event (qbs_comp (strengthQ W X) (qbs_id _))).
by apply: eq_integral => r _; rewrite /= strength_event.
Qed.

End probability_monad.

