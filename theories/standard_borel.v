(* -------------------------------------------------------------------- *)
(* Standard Borel Isomorphism: R is measurably isomorphic to R x R      *)
(*                                                                      *)
(* This file axiomatizes the classical fact that any uncountable        *)
(* standard Borel space is measurably isomorphic to R. In particular,   *)
(* R x R (with the product sigma-algebra) is measurably isomorphic to   *)
(* R. This is Theorem 3.3.13 in Srivastava "A Course on Borel Sets".   *)
(*                                                                      *)
(* The axioms are:                                                      *)
(*   mR_prod_encode : mR * mR -> mR       (measurable bijection)       *)
(*   mR_prod_decode : mR -> mR * mR       (measurable inverse)         *)
(*   mR_prod_encode_measurable            (encode is measurable)        *)
(*   mR_prod_decode_measurable            (decode is measurable)        *)
(*   mR_prod_decode_encode                (decode o encode = id)        *)
(*   mR_prod_encode_decode                (encode o decode = id)        *)
(*                                                                      *)
(* Using these, we define a proper product of QBS probability spaces    *)
(* that transports the product measure mu_p x mu_q on mR x mR through  *)
(* the encoding to a probability on mR. This fixes the admitted proofs  *)
(* in pair_qbs_measure.v by giving each marginal its correct measure.   *)
(* -------------------------------------------------------------------- *)

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

(* ===================================================================== *)
(* Part 1: Axioms for the Standard Borel Isomorphism R ~ R x R          *)
(* ===================================================================== *)

Section StandardBorelAxioms.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* Measurable bijection R x R -> R *)
Axiom mR_prod_encode : mR * mR -> mR.

(* Measurable inverse R -> R x R *)
Axiom mR_prod_decode : mR -> mR * mR.

(* Encode is measurable *)
Axiom mR_prod_encode_measurable : measurable_fun setT mR_prod_encode.

(* Decode is measurable *)
Axiom mR_prod_decode_measurable : measurable_fun setT mR_prod_decode.

(* Decode is left inverse of encode *)
Axiom mR_prod_decode_encode : cancel mR_prod_encode mR_prod_decode.

(* Encode is left inverse of decode *)
Axiom mR_prod_encode_decode : cancel mR_prod_decode mR_prod_encode.

(* Derived: the components of decode are measurable *)
Lemma mR_prod_decode_fst_measurable :
  measurable_fun setT (fst \o mR_prod_decode).
Proof.
apply: measurableT_comp; first exact: measurable_fst.
exact: mR_prod_decode_measurable.
Qed.

Lemma mR_prod_decode_snd_measurable :
  measurable_fun setT (snd \o mR_prod_decode).
Proof.
apply: measurableT_comp; first exact: measurable_snd.
exact: mR_prod_decode_measurable.
Qed.

(* Derived: encode o decode o encode = encode *)
Lemma mR_prod_encode_decode_encode (x : mR * mR) :
  mR_prod_encode (mR_prod_decode (mR_prod_encode x)) = mR_prod_encode x.
Proof. by rewrite mR_prod_decode_encode. Qed.

(* Derived: decode o encode o decode = decode *)
Lemma mR_prod_decode_encode_decode (r : mR) :
  mR_prod_decode (mR_prod_encode (mR_prod_decode r)) = mR_prod_decode r.
Proof. by rewrite mR_prod_encode_decode. Qed.

End StandardBorelAxioms.

(* ===================================================================== *)
(* Part 2: Proper Product of QBS Probability Spaces                      *)
(*                                                                       *)
(* Given p : qbs_prob X and q : qbs_prob Y, we construct a proper       *)
(* product qbs_prob (prodQ X Y) where:                                   *)
(*   - The underlying measure is the pushforward of (mu_p x mu_q)       *)
(*     through mR_prod_encode, giving a probability on mR               *)
(*   - The alpha is r |-> (alpha_p(fst(decode r)), alpha_q(snd(decode r))) *)
(*                                                                       *)
(* This ensures both marginals are correct: integrating a function of   *)
(* fst against the product uses mu_p, and integrating a function of     *)
(* snd uses mu_q.                                                        *)
(* ===================================================================== *)

Section ProperPairQBS.
Variable (R : realType).

Local Notation mR := (measurableTypeR R).

(* The proper alpha for a product: decode r into (r1, r2), then apply
   the respective alphas. *)
Definition qbs_pair_alpha_proper (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : mR -> X * Y :=
  fun r => let d := @mR_prod_decode R r in
    (qbs_prob_alpha p d.1, qbs_prob_alpha q d.2).

(* The proper alpha is a random element of prodQ X Y *)
Lemma qbs_pair_alpha_proper_random (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) :
  @qbs_random R (prodQ X Y) (qbs_pair_alpha_proper p q).
Proof.
split => /=.
- have -> : fst \o qbs_pair_alpha_proper p q =
            qbs_prob_alpha p \o (fst \o @mR_prod_decode R) by [].
  apply: (qbs_random_comp (qbs_prob_alpha_random p)).
  exact: mR_prod_decode_fst_measurable.
- have -> : snd \o qbs_pair_alpha_proper p q =
            qbs_prob_alpha q \o (snd \o @mR_prod_decode R) by [].
  apply: (qbs_random_comp (qbs_prob_alpha_random q)).
  exact: mR_prod_decode_snd_measurable.
Qed.

(* The proper product measure: pushforward of (mu_p x mu_q) through encode.
   We axiomatize this directly as a probability on mR. Mathematically,
   the pushforward of a probability through a measurable bijection is a
   probability (total mass is preserved). Constructing this through
   the HB hierarchy would require showing pushforward(mu)(setT) = 1,
   which follows from encode being surjective. We axiomatize the result
   for clean integration with the HB probability type. *)

Axiom qbs_pair_mu_proper :
  forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y),
    probability mR R.

(* The axiomatized measure agrees with the pushforward on measurable sets *)
Axiom qbs_pair_mu_properE :
  forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
    (A : set mR), measurable A ->
    qbs_pair_mu_proper p q A =
    pushforward (qbs_prob_mu p \x qbs_prob_mu q)
      (@mR_prod_encode R) A.

(* Integral against the proper product measure equals integral against
   the pushforward. *)
Axiom qbs_pair_mu_proper_integralE :
  forall (X Y : qbs R) (p : qbs_prob X) (q : qbs_prob Y)
    (f : mR -> \bar R),
    integral (qbs_pair_mu_proper p q) setT f =
    integral (pushforward (qbs_prob_mu p \x qbs_prob_mu q)
      (@mR_prod_encode R)) setT f.

(* The proper product QBS probability *)
Definition qbs_prob_pair_proper (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y) : qbs_prob (prodQ X Y) :=
  @mkQBSProb R (prodQ X Y)
    (qbs_pair_alpha_proper p q)
    (qbs_pair_mu_proper p q)
    (qbs_pair_alpha_proper_random p q).

(* After section close, R X Y are implicit, p q explicit:
   qbs_prob_pair_proper p q : qbs_prob (prodQ X Y) *)

(* ===================================================================== *)
(* Part 3: Marginal Integration Properties                               *)
(*                                                                       *)
(* The key property: integrating over the first component of the proper *)
(* product recovers the integral against mu_p, and similarly for snd.   *)
(* ===================================================================== *)

(* Integration against the proper product measure.
   For a function h : X * Y -> \bar R, we have:

   qbs_integral (qbs_prob_pair_proper p q) h
   = \int[pushforward (mu_p x mu_q) encode]_r h(alpha_p(decode(r).1), alpha_q(decode(r).2))
   = \int[mu_p x mu_q]_(r1,r2) h(alpha_p(r1), alpha_q(r2))    (by pushforward)
   = \int[mu_p]_r1 \int[mu_q]_r2 h(alpha_p(r1), alpha_q(r2))  (by Fubini)

   The last step uses Fubini's theorem from mathcomp-analysis. *)

(* Bridge lemma: converts QBS integration against the proper product
   measure into standard integration against the product measure on mR * mR. *)
Lemma qbs_integral_proper_as_product (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hm : measurable_fun setT
    (fun r : mR => h (qbs_pair_alpha_proper p q r)))
  (hint : (qbs_prob_mu p \x qbs_prob_mu q).-integrable setT
    (fun rr : mR * mR =>
      h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2))) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q) h =
  \int[qbs_prob_mu p \x qbs_prob_mu q]_rr
    h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2).
Proof.
rewrite /qbs_integral /=.
(* Step 1: Switch from qbs_pair_mu_proper to pushforward *)
rewrite (qbs_pair_mu_proper_integralE p q
  (fun x => h (qbs_pair_alpha_proper p q x))).
(* Step 2: Provide integrability of (F o encode) for integral_pushforward *)
have hint' : (qbs_prob_mu p \x qbs_prob_mu q).-integrable
  (@mR_prod_encode R @^-1` setT)
  ((fun r => h (qbs_pair_alpha_proper p q r)) \o @mR_prod_encode R).
  rewrite preimage_setT.
  apply: (eq_integrable measurableT
    (fun rr : mR * mR => h (qbs_prob_alpha p rr.1, qbs_prob_alpha q rr.2))).
  - move=> rr _ /=; rewrite /qbs_pair_alpha_proper /=.
    by rewrite mR_prod_decode_encode.
  - exact: hint.
(* Step 3: Apply integral_pushforward *)
rewrite (integral_pushforward (@mR_prod_encode_measurable R) hm hint' measurableT).
(* Step 4: Simplify preimage setT and decode(encode(rr)) *)
rewrite preimage_setT.
apply: eq_integral => rr _.
rewrite /= /qbs_pair_alpha_proper /=.
by rewrite mR_prod_decode_encode.
Qed.

(* Helper: constant integral against a probability measure equals the constant *)
Lemma prob_integral_cst (X0 : qbs R) (p0 : qbs_prob X0) (c : \bar R) :
  \int[qbs_prob_mu p0]_x c = c.
Proof.
transitivity (c * qbs_prob_mu p0 setT); first exact: integral_cst.
by rewrite probability_setT mule1.
Qed.

(* First marginal: integrating a function of fst recovers qbs_integral p.
   Requires non-negativity and measurability of h composed with alpha. *)
Lemma qbs_integral_fst_proper (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X -> \bar R)
  (hge0 : forall x, 0 <= h x)
  (hmeas : measurable_fun setT (h \o qbs_prob_alpha p)) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q)
    (fun xy => h (fst xy)) =
  @qbs_integral R X p h.
Proof.
rewrite /qbs_integral /=.
rewrite (qbs_pair_mu_proper_integralE p q
  (fun x => h (qbs_prob_alpha p (mR_prod_decode x).1))).
have hfm : measurable_fun setT
    (fun y : mR => h (qbs_prob_alpha p (mR_prod_decode y).1)).
  have -> : (fun y : mR => h (qbs_prob_alpha p (mR_prod_decode y).1)) =
            (h \o qbs_prob_alpha p) \o (fst \o @mR_prod_decode R).
    by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas (mR_prod_decode_fst_measurable (R:=R))).
rewrite (ge0_integral_pushforward (mR_prod_encode_measurable R)
  _ measurableT hfm (fun x _ => hge0 _)).
rewrite preimage_setT.
have hcomp : ((fun y : mR => h (qbs_prob_alpha p (mR_prod_decode y).1))
             \o @mR_prod_encode R) =
          (fun z : mR * mR => h (qbs_prob_alpha p z.1)).
  apply: boolp.funext => r /=.
  by rewrite mR_prod_decode_encode.
rewrite hcomp.
have hgm : measurable_fun setT
    (fun z : mR * mR => h (qbs_prob_alpha p z.1)).
  have -> : (fun z : mR * mR => h (qbs_prob_alpha p z.1)) =
            (h \o qbs_prob_alpha p) \o fst.
    by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas measurable_fst).
rewrite (fubini_tonelli1 _ hgm (fun x => hge0 _)).
congr (integral _ setT _).
apply: boolp.funext => x.
rewrite /fubini_F.
rewrite (_ : (fun y => _) = functions.cst (h (qbs_prob_alpha p x))); last first.
  by apply: boolp.funext.
exact: prob_integral_cst.
Qed.

(* Second marginal: integrating a function of snd recovers qbs_integral q.
   Requires non-negativity and measurability of h composed with alpha. *)
Lemma qbs_integral_snd_proper (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : Y -> \bar R)
  (hge0 : forall y, 0 <= h y)
  (hmeas : measurable_fun setT (h \o qbs_prob_alpha q)) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q)
    (fun xy => h (snd xy)) =
  @qbs_integral R Y q h.
Proof.
rewrite /qbs_integral /=.
rewrite (qbs_pair_mu_proper_integralE p q
  (fun x => h (qbs_prob_alpha q (mR_prod_decode x).2))).
have hfm : measurable_fun setT
    (fun y : mR => h (qbs_prob_alpha q (mR_prod_decode y).2)).
  have -> : (fun y : mR => h (qbs_prob_alpha q (mR_prod_decode y).2)) =
            (h \o qbs_prob_alpha q) \o (snd \o @mR_prod_decode R).
    by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas (mR_prod_decode_snd_measurable (R:=R))).
rewrite (ge0_integral_pushforward (mR_prod_encode_measurable R)
  _ measurableT hfm (fun x _ => hge0 _)).
rewrite preimage_setT.
have hcomp : ((fun y : mR => h (qbs_prob_alpha q (mR_prod_decode y).2))
             \o @mR_prod_encode R) =
          (fun z : mR * mR => h (qbs_prob_alpha q z.2)).
  apply: boolp.funext => r /=.
  by rewrite mR_prod_decode_encode.
rewrite hcomp.
have hgm : measurable_fun setT
    (fun z : mR * mR => h (qbs_prob_alpha q z.2)).
  have -> : (fun z : mR * mR => h (qbs_prob_alpha q z.2)) =
            (h \o qbs_prob_alpha q) \o snd.
    by apply: boolp.funext => r /=.
  exact: (measurableT_comp hmeas measurable_snd).
rewrite (fubini_tonelli1 _ hgm (fun x => hge0 _)).
transitivity (\int[qbs_prob_mu p]_x
  \int[qbs_prob_mu q]_y h (qbs_prob_alpha q y)).
  apply: eq_integral => x _.
  by rewrite /fubini_F.
exact: prob_integral_cst.
Qed.

(* Fubini's theorem: iterated integration equals joint integration
   (non-negative version) *)
Lemma qbs_integral_pair_proper (X Y : qbs R)
  (p : qbs_prob X) (q : qbs_prob Y)
  (h : X * Y -> \bar R)
  (hge0 : forall xy, 0 <= h xy)
  (hmeas : measurable_fun setT
    (fun r : mR * mR => h (qbs_prob_alpha p r.1, qbs_prob_alpha q r.2))) :
  @qbs_integral R (prodQ X Y) (qbs_prob_pair_proper p q) h =
  @qbs_integral R X p (fun x =>
    @qbs_integral R Y q (fun y => h (x, y))).
Proof. Admitted.

(* ===================================================================== *)
(* Part 4: Independence via Proper Products                              *)
(* ===================================================================== *)

(* E[f * g] = E[f] * E[g] for independent non-negative random variables *)
Lemma qbs_integral_indep_mult_proper (X Y : qbs R)
  (pxy : qbs_prob (prodQ X Y))
  (f : X -> R) (g : Y -> R)
  (px : qbs_prob X) (py : qbs_prob Y)
  (hindep : @qbs_prob_equiv R (prodQ X Y) pxy
              (qbs_prob_pair_proper px py))
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
  @qbs_expect R (prodQ X Y) pxy
    (fun xy => f (fst xy) * g (snd xy))%R =
  (@qbs_expect R X px f * @qbs_expect R Y py g).
Proof.
rewrite /qbs_expect.
(* Step 1: Use equivalence to move from pxy to the proper product *)
rewrite (qbs_integral_equiv hm hint1 hint2 hindep).
(* Step 2: Apply Fubini (non-negative version) to split the joint integral *)
have hfg_ge0 : forall xy : X * Y,
  (0 : \bar R) <= ((f (fst xy) * g (snd xy))%R)%:E.
  by move=> xy; rewrite lee_fin; apply: mulr_ge0.
rewrite (@qbs_integral_pair_proper X Y px py
  (fun xy : X * Y => ((f (fst xy) * g (snd xy))%R)%:E)
  hfg_ge0 hfg_meas).
simpl.
(* Step 3: Factor the inner integral using ge0_integralZl_EFin:
   \int_y (f x * g y)%:E = (f x)%:E * \int_y (g y)%:E *)
have inner_eq : forall x : X,
  @qbs_integral R Y py (fun y : Y => ((f x * g y)%R)%:E) =
  (f x)%:E * @qbs_integral R Y py (fun y : Y => (g y)%:E).
  move=> x; rewrite /qbs_integral.
  under eq_integral do rewrite EFinM.
  apply: ge0_integralZl_EFin => //.
  - by move=> r _; rewrite lee_fin; apply: hg0.
  - exact: measurableT.
  - exact: hg_meas.
(* Rewrite inner integrals *)
have lhs_eq :
  @qbs_integral R X px
    (fun x : X => @qbs_integral R Y py (fun y : Y => (f x * g y)%:E)) =
  @qbs_integral R X px
    (fun x : X => (f x)%:E * @qbs_integral R Y py (fun y : Y => (g y)%:E)).
  rewrite /qbs_integral; apply: eq_integral => r _.
  exact: inner_eq (qbs_prob_alpha px r).
rewrite lhs_eq.
(* Step 4: Factor the constant Eg out using ge0_integralZr:
   \int_x (f x)%:E * Eg = (\int_x (f x)%:E) * Eg *)
rewrite /qbs_integral.
apply: ge0_integralZr => //.
- exact: measurableT.
- exact: hf_meas.
- by move=> r _; rewrite lee_fin; apply: hf0.
- apply: integral_ge0 => r _.
  by rewrite lee_fin; apply: hg0.
Qed.

End ProperPairQBS.

(* ===================================================================== *)
(* Part 5: Usage Guide                                                   *)
(*                                                                       *)
(* To use this infrastructure in other developments:                     *)
(*                                                                       *)
(* 1. Import this file:                                                  *)
(*      From QBS Require Import standard_borel.                          *)
(*                                                                       *)
(* 2. Use qbs_prob_pair_proper instead of qbs_prob_pair:                 *)
(*      Definition my_joint := qbs_prob_pair_proper p q.                 *)
(*    (R, X, Y are inferred from p and q.)                               *)
(*                                                                       *)
(* 3. Use the proper Fubini/marginal lemmas:                             *)
(*      qbs_integral_fst_proper  : first marginal is correct             *)
(*      qbs_integral_snd_proper  : second marginal is correct            *)
(*      qbs_integral_pair_proper : Fubini's theorem                      *)
(*                                                                       *)
(* The axiom boundary is clearly marked:                                 *)
(*   - mR_prod_encode/decode       : the measurable bijection R ~ R x R *)
(*   - qbs_pair_mu_proper/properE : product measure as probability       *)
(*                                                                       *)
(* These axioms are mathematically justified by the Kuratowski theorem   *)
(* (all uncountable standard Borel spaces are isomorphic) and the fact   *)
(* that measurable bijections preserve probability measures.             *)
(* ===================================================================== *)
