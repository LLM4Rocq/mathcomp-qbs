(* Standard Borel Isomorphism and Independence *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import all_analysis.
From QBS Require Import quasi_borel probability_qbs.

Import Num.Def Num.Theory reals classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section StandardBorelAxioms.
Variable (R : realType).
Local Notation mR := (measurableTypeR R).
Axiom mR_prod_encode : mR * mR -> mR.
Axiom mR_prod_decode : mR -> mR * mR.
Axiom mR_prod_encode_measurable : measurable_fun setT mR_prod_encode.
Axiom mR_prod_decode_measurable : measurable_fun setT mR_prod_decode.
Axiom mR_prod_decode_encode : cancel mR_prod_encode mR_prod_decode.
Axiom mR_prod_encode_decode : cancel mR_prod_decode mR_prod_encode.
Lemma mR_prod_decode_fst_measurable :
  measurable_fun setT (fst \o mR_prod_decode).
Proof. exact: measurableT_comp measurable_fst mR_prod_decode_measurable. Qed.
Lemma mR_prod_decode_snd_measurable :
  measurable_fun setT (snd \o mR_prod_decode).
Proof. exact: measurableT_comp measurable_snd mR_prod_decode_measurable. Qed.
End StandardBorelAxioms.

Section ProperPairQBS.
Variable (R : realType).
Local Notation mR := (measurableTypeR R).

Definition qbs_pair_alpha_proper (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r => let d := @mR_prod_decode R r in
    (qbs_prob_alpha p d.1, qbs_prob_alpha q d.2).

Lemma qbs_pair_alpha_proper_random (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) :
  @qbs_random R (prodQ X Y) (qbs_pair_alpha_proper p q).
Proof.
split => /=.
- have -> : fst \o qbs_pair_alpha_proper p q =
            qbs_prob_alpha p \o (fst \o @mR_prod_decode R) by [].
  exact: qbs_random_comp (qbs_prob_alpha_random p) (mR_prod_decode_fst_measurable _).
- have -> : snd \o qbs_pair_alpha_proper p q =
            qbs_prob_alpha q \o (snd \o @mR_prod_decode R) by [].
  exact: qbs_random_comp (qbs_prob_alpha_random q) (mR_prod_decode_snd_measurable _).
Qed.

Axiom qbs_pair_mu_proper :
  forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y), probability mR R.
Axiom qbs_pair_mu_properE :
  forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
    (A : set mR), measurable A ->
    qbs_pair_mu_proper p q A =
    pushforward (qbs_prob_mu p \x qbs_prob_mu q) (@mR_prod_encode R) A.

Definition qbs_prob_pair_proper (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y) (qbs_pair_alpha_proper p q)
    (qbs_pair_mu_proper p q) (qbs_pair_alpha_proper_random p q).

Lemma qbs_integral_fst_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q)
    (fun xy => h (fst xy)) = @qbs_integral R X p h.
Proof. Admitted.

Lemma qbs_integral_snd_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q)
    (fun xy => h (snd xy)) = @qbs_integral R Y q h.
Proof. Admitted.

Lemma qbs_integral_pair_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hge0 : forall xy, 0 <= h xy)
  (hmeas : measurable_fun setT
    (fun r : mR * mR => h (qbs_prob_alpha p r.1, qbs_prob_alpha q r.2))) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q) h =
  @qbs_integral R X p (fun x => @qbs_integral R Y q (fun y => h (x, y))).
Proof. Admitted.

(* E[f * g] = E[f] * E[g] for independent non-negative random variables *)
Lemma qbs_integral_indep_mult_proper (X Y : qbs R)
  (pxy : qbs_prob (prodQ X Y))
  (f : X -> R) (g : Y -> R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (hindep : @qbs_prob_equiv R (prodQ X Y) pxy (qbs_prob_pair_proper px py))
  (hf0 : forall x, (0 <= f x)%R)
  (hg0 : forall y, (0 <= g y)%R)
  (hm : @qbs_measurable R (prodQ X Y)
          (fun xy : prodQ X Y => ((f (fst xy) * g (snd xy))%R)%:E))
  (hint1 : (qbs_prob_mu pxy).-integrable setT
             ((fun xy : prodQ X Y => ((f (fst xy) * g (snd xy))%R)%:E) \o
              qbs_prob_alpha pxy))
  (hint2 : (qbs_prob_mu (qbs_prob_pair_proper px py)).-integrable setT
             ((fun xy : prodQ X Y => ((f (fst xy) * g (snd xy))%R)%:E) \o
              qbs_prob_alpha (qbs_prob_pair_proper px py)))
  (hfg_meas : measurable_fun setT
    (fun r : mR * mR =>
      ((f (qbs_prob_alpha px r.1) * g (qbs_prob_alpha py r.2))%R)%:E))
  (hg_meas : measurable_fun setT
    ((fun y : Y => (g y)%:E) \o qbs_prob_alpha py))
  (hf_meas : measurable_fun setT
    ((fun x : X => (f x)%:E) \o qbs_prob_alpha px)) :
  @qbs_expect R (prodQ X Y) pxy (fun xy => f (fst xy) * g (snd xy))%R =
  (@qbs_expect R X px f * @qbs_expect R Y py g).
Proof.
rewrite /qbs_expect.
rewrite (qbs_integral_equiv hm hint1 hint2 hindep).
have hfg_ge0 : forall xy : X * Y,
  (0 : \bar R) <= ((f (fst xy) * g (snd xy))%R)%:E.
  by move=> xy; rewrite lee_fin; apply: mulr_ge0.
rewrite (@qbs_integral_pair_proper X Y px py
  (fun xy : X * Y => ((f (fst xy) * g (snd xy))%R)%:E)
  hfg_ge0 hfg_meas).
simpl.
have inner_eq : forall x : X,
  @qbs_integral R Y py (fun y : Y => ((f x * g y)%R)%:E) =
  (f x)%:E * @qbs_integral R Y py (fun y : Y => (g y)%:E).
  move=> x; rewrite /qbs_integral.
  under eq_integral do rewrite EFinM.
  apply: ge0_integralZl_EFin; [exact: measurableT | | | exact: hf0].
  - by move=> r _; rewrite lee_fin; apply: hg0.
  - exact: hg_meas.
have lhs_eq :
  @qbs_integral R X px
    (fun x : X => @qbs_integral R Y py (fun y : Y => (f x * g y)%:E)) =
  @qbs_integral R X px
    (fun x : X => (f x)%:E * @qbs_integral R Y py (fun y : Y => (g y)%:E)).
  rewrite /qbs_integral; apply: eq_integral => r _.
  exact: inner_eq (qbs_prob_alpha px r).
rewrite lhs_eq.
rewrite /qbs_integral.
apply: ge0_integralZr; [exact: measurableT | exact: hf_meas | |].
- by move=> r _; rewrite lee_fin; apply: hf0.
- apply: integral_ge0 => r _.
  by rewrite lee_fin; apply: hg0.
Qed.

End ProperPairQBS.
