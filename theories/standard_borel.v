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
Lemma mR_prod_decode_fst_measurable : measurable_fun setT (fst \o mR_prod_decode).
Proof. apply: measurableT_comp; first exact: measurable_fst. exact: mR_prod_decode_measurable. Qed.
Lemma mR_prod_decode_snd_measurable : measurable_fun setT (snd \o mR_prod_decode).
Proof. apply: measurableT_comp; first exact: measurable_snd. exact: mR_prod_decode_measurable. Qed.
Lemma mR_prod_encode_decode_encode (x : mR * mR) :
  mR_prod_encode (mR_prod_decode (mR_prod_encode x)) = mR_prod_encode x.
Proof. by rewrite mR_prod_decode_encode. Qed.
Lemma mR_prod_decode_encode_decode (r : mR) :
  mR_prod_decode (mR_prod_encode (mR_prod_decode r)) = mR_prod_decode r.
Proof. by rewrite mR_prod_encode_decode. Qed.
End StandardBorelAxioms.

Section ProperPairQBS.
Variable (R : realType).
Local Notation mR := (measurableTypeR R).

Definition qbs_pair_alpha_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r => let d := @mR_prod_decode R r in (qbs_prob_alpha p d.1, qbs_prob_alpha q d.2).

Lemma qbs_pair_alpha_proper_random (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y) :
  @qbs_random R (prodQ X Y) (qbs_pair_alpha_proper p q).
Proof.
split => /=.
- have -> : fst \o qbs_pair_alpha_proper p q = qbs_prob_alpha p \o (fst \o @mR_prod_decode R) by [].
  apply: (qbs_random_comp (qbs_prob_alpha_random p)). exact: mR_prod_decode_fst_measurable.
- have -> : snd \o qbs_pair_alpha_proper p q = qbs_prob_alpha q \o (snd \o @mR_prod_decode R) by [].
  apply: (qbs_random_comp (qbs_prob_alpha_random q)). exact: mR_prod_decode_snd_measurable.
Qed.

Axiom qbs_pair_mu_proper : forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y), probability mR R.
Axiom qbs_pair_mu_properE : forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
    (A : set mR), measurable A -> qbs_pair_mu_proper p q A =
    pushforward (qbs_prob_mu p \x qbs_prob_mu q) (@mR_prod_encode R) A.
Axiom qbs_pair_mu_proper_integralE : forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
    (f : mR -> \bar R), integral (qbs_pair_mu_proper p q) setT f =
    integral (pushforward (qbs_prob_mu p \x qbs_prob_mu q) (@mR_prod_encode R)) setT f.

Definition qbs_prob_pair_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y) (qbs_pair_alpha_proper p q) (qbs_pair_mu_proper p q) (qbs_pair_alpha_proper_random p q).

Lemma prob_integral_cst (X0 : qbs R) (p0 : qbs_prob X0) (c : \bar R) : \int[qbs_prob_mu p0]_x c = c.
Proof. transitivity (c * qbs_prob_mu p0 setT); first exact: integral_cst. by rewrite probability_setT mule1. Qed.

Lemma qbs_integral_fst_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y) (h : X -> \bar R)
  (hge0 : forall x, 0 <= h x) (hmeas : measurable_fun setT (h \o qbs_prob_alpha p)) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q) (fun xy => h (fst xy)) = @qbs_integral R X p h.
Proof.
rewrite /qbs_integral /=.
rewrite (qbs_pair_mu_proper_integralE p q (fun x => h (qbs_prob_alpha p (mR_prod_decode x).1))).
have hfm : measurable_fun setT (fun y : mR => h (qbs_prob_alpha p (mR_prod_decode y).1)).
  have -> : (fun y : mR => h (qbs_prob_alpha p (mR_prod_decode y).1)) = (h \o qbs_prob_alpha p) \o (fst \o @mR_prod_decode R) by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas (mR_prod_decode_fst_measurable (R:=R))).
rewrite (ge0_integral_pushforward (@mR_prod_encode_measurable R) _ measurableT hfm (fun x _ => hge0 _)).
rewrite preimage_setT.
have hcomp : ((fun y : mR => h (qbs_prob_alpha p (mR_prod_decode y).1)) \o @mR_prod_encode R) = (fun z : mR * mR => h (qbs_prob_alpha p z.1)).
  by apply: boolp.funext => r /=; rewrite mR_prod_decode_encode.
rewrite hcomp.
have hgm : measurable_fun setT (fun z : mR * mR => h (qbs_prob_alpha p z.1)).
  have -> : (fun z : mR * mR => h (qbs_prob_alpha p z.1)) = (h \o qbs_prob_alpha p) \o fst by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas measurable_fst).
rewrite (fubini_tonelli1 _ hgm (fun x => hge0 _)).
congr (integral _ setT _). apply: boolp.funext => x. rewrite /fubini_F.
rewrite (_ : (fun y => _) = functions.cst (h (qbs_prob_alpha p x))); last by apply: boolp.funext.
exact: prob_integral_cst.
Qed.

Lemma qbs_integral_snd_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y) (h : Y -> \bar R)
  (hge0 : forall y, 0 <= h y) (hmeas : measurable_fun setT (h \o qbs_prob_alpha q)) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q) (fun xy => h (snd xy)) = @qbs_integral R Y q h.
Proof.
rewrite /qbs_integral /=.
rewrite (qbs_pair_mu_proper_integralE p q (fun x => h (qbs_prob_alpha q (mR_prod_decode x).2))).
have hfm : measurable_fun setT (fun y : mR => h (qbs_prob_alpha q (mR_prod_decode y).2)).
  have -> : (fun y : mR => h (qbs_prob_alpha q (mR_prod_decode y).2)) = (h \o qbs_prob_alpha q) \o (snd \o @mR_prod_decode R) by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas (mR_prod_decode_snd_measurable (R:=R))).
rewrite (ge0_integral_pushforward (@mR_prod_encode_measurable R) _ measurableT hfm (fun x _ => hge0 _)).
rewrite preimage_setT.
have hcomp : ((fun y : mR => h (qbs_prob_alpha q (mR_prod_decode y).2)) \o @mR_prod_encode R) = (fun z : mR * mR => h (qbs_prob_alpha q z.2)).
  by apply: boolp.funext => r /=; rewrite mR_prod_decode_encode.
rewrite hcomp.
have hgm : measurable_fun setT (fun z : mR * mR => h (qbs_prob_alpha q z.2)).
  have -> : (fun z : mR * mR => h (qbs_prob_alpha q z.2)) = (h \o qbs_prob_alpha q) \o snd by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas measurable_snd).
rewrite (fubini_tonelli1 _ hgm (fun x => hge0 _)).
transitivity (\int[qbs_prob_mu p]_x \int[qbs_prob_mu q]_y h (qbs_prob_alpha q y)).
  by apply: eq_integral => x _; rewrite /fubini_F.
exact: prob_integral_cst.
Qed.

Lemma qbs_integral_pair_proper (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y) (h : X * Y -> \bar R)
  (hge0 : forall xy, 0 <= h xy) (hmeas : measurable_fun setT
    (fun r : mR * mR => h (qbs_prob_alpha p r.1, qbs_prob_alpha q r.2))) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q) h =
  @qbs_integral R X p (fun x => @qbs_integral R Y q (fun y => h (x, y))).
Proof.
rewrite /qbs_integral /= /qbs_pair_alpha_proper /=. rewrite qbs_pair_mu_proper_integralE.
set f := (fun x : mR => h (qbs_prob_alpha p (mR_prod_decode x).1, qbs_prob_alpha q (mR_prod_decode x).2)).
set g := (fun r : mR * mR => h (qbs_prob_alpha p r.1, qbs_prob_alpha q r.2)).
have hfg : f = g \o (@mR_prod_decode R) by apply: boolp.funext.
have hfm : measurable_fun setT f.
  rewrite hfg; apply: measurableT_comp; first exact: hmeas. exact: mR_prod_decode_measurable.
rewrite ge0_integral_pushforward; last first.
  - by move=> x _; exact: hge0.
  - exact: hfm.
  - exact: measurableT.
  - exact: mR_prod_encode_measurable.
rewrite preimage_setT.
have -> : f \o @mR_prod_encode R = g.
  apply: boolp.funext => r /=; rewrite /f /g. by rewrite mR_prod_decode_encode.
by rewrite (fubini_tonelli1 g hmeas (fun x => hge0 _)).
Qed.

End ProperPairQBS.
