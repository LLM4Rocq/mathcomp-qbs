(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology normedtype numfun measure
  lebesgue_integral lebesgue_integral_fubini lebesgue_stieltjes_measure
  probability.
From mathcomp.classical Require Import boolp.
From mathcomp.algebra_tactics Require Import ring.

Import Num.Def Num.Theory reals classical_sets GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NormalDensityAlgebra.
Variable (R : realType).
Local Open Scope ring_scope.

(* Completing the square: ax^2 + bx + c = a(x+b/(2a))^2 - (b^2-4ac)/(4a) *)
Lemma complete_the_square (a b c x : R) (ha : a != 0) :
  a * x ^+ 2 + b * x + c =
  a * (x + b / (a *+ 2)) ^+ 2 - (b ^+ 2 - a *+ 4 * c) / (a *+ 4).
Proof.
have ha4 : a *+ 4 != 0 by rewrite mulrn_eq0.
have ha2 : a *+ 2 != 0 by rewrite mulrn_eq0.
field. repeat split => //; rewrite ?mulrn_eq0 //.
Qed.

(* Product of two normal densities.
   N(m,s)(x) * N(m',s')(x) = K * N(mu_new, sigma_new)(x)
   where:
     mu_new    = (m*s'^2 + m'*s^2) / (s^2 + s'^2)
     sigma_new = s*s' / sqrt(s^2 + s'^2)
     K = normal_peak(sqrt(s^2+s'^2)) * normal_fun(m, sqrt(s^2+s'^2), m')

   This identity is essential for iteratively computing the normalizing
   constant: each observation contributes a Gaussian factor that can be
   combined with the prior using this identity (cf. Isabelle AFP
   normal_density_times). *)
Lemma normal_pdf_times (m m' s s' x : R) :
  s != 0 -> s' != 0 ->
  normal_pdf m s x * normal_pdf m' s' x =
  normal_peak (sqrtr (s ^+ 2 + s' ^+ 2)) *
  normal_fun m (sqrtr (s ^+ 2 + s' ^+ 2)) m' *
  normal_pdf ((m * s' ^+ 2 + m' * s ^+ 2) / (s ^+ 2 + s' ^+ 2))
             (s * s' / sqrtr (s ^+ 2 + s' ^+ 2)) x.
Proof.
move=> hs hs'.
have hS : s ^+ 2 + s' ^+ 2 != 0.
  by rewrite paddr_eq0 ?sqr_ge0 // !sqrf_eq0; apply/nandP; left.
have hSgt0 : (0 < s ^+ 2 + s' ^+ 2)%R.
  by apply: addr_gt0; rewrite exprn_even_gt0 //=.
have hsqS : sqrtr (s ^+ 2 + s' ^+ 2) != 0.
  by apply: lt0r_neq0; rewrite sqrtr_gt0.
have hsnew : s * s' / sqrtr (s ^+ 2 + s' ^+ 2) != 0.
  by rewrite mulf_neq0 ?invr_neq0 // mulf_neq0.
have hpi : (0 <= @trigo.pi R)%R := trigo.pi_ge0 R.
have hs2pi : (0 <= s ^+ 2 * @trigo.pi R)%R := mulr_ge0 (sqr_ge0 _) hpi.
have hS2pi : (0 <= (s ^+ 2 + s' ^+ 2) * @trigo.pi R)%R.
  by apply: mulr_ge0 => //; exact: addr_ge0 (sqr_ge0 _) (sqr_ge0 _).
rewrite (normal_pdfE _ hs) (normal_pdfE _ hs') (normal_pdfE _ hsnew).
rewrite [LHS]mulrACA [RHS]mulrACA.
congr (_ * _).
- (* peaksE *)
  rewrite /normal_peak -invfM -sqrtrM ?pmulrn_lge0 ?sqr_ge0 //.
  rewrite -[RHS]invfM -sqrtrM ?pmulrn_lge0 ?sqr_ge0 ?sqr_sqrtr
          ?addr_ge0 ?sqr_ge0 //.
  congr (_^-1); congr (sqrtr _).
  rewrite exprMn exprVn sqr_sqrtr ?addr_ge0 ?sqr_ge0 //.
  field. exact: hS.
  Unshelve.
  all: try by apply: mulr_ge0 => //; exact: sqr_ge0.
  all: try by apply: mulrn_wge0.
- (* funsE *)
  rewrite /normal_fun -exp.expRD -[RHS]exp.expRD.
  congr (sequences.expR _).
  rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 //.
  rewrite exprMn exprVn sqr_sqrtr ?addr_ge0 ?sqr_ge0 //.
  field.
  by rewrite hS hs hs'.
Qed.

End NormalDensityAlgebra.
