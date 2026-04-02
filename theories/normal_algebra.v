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

(* ===================================================================== *)
(* Helper definitions for iterating normal_pdf_times                     *)
(* ===================================================================== *)

(* After combining N(m,s,x) * N(m',s',x) via normal_pdf_times,
   the new parameters are: *)
Definition gaussian_prod_mu (m m' s s' : R) :=
  (m * s' ^+ 2 + m' * s ^+ 2) / (s ^+ 2 + s' ^+ 2).

Definition gaussian_prod_sigma (s s' : R) :=
  s * s' / sqrtr (s ^+ 2 + s' ^+ 2).

Definition gaussian_prod_scalar (m m' s s' : R) :=
  normal_peak (sqrtr (s ^+ 2 + s' ^+ 2)) *
  normal_fun m (sqrtr (s ^+ 2 + s' ^+ 2)) m'.

(* Restatement of normal_pdf_times using helper definitions *)
Lemma normal_pdf_times' (m m' s s' x : R) :
  s != 0 -> s' != 0 ->
  normal_pdf m s x * normal_pdf m' s' x =
  gaussian_prod_scalar m m' s s' *
  normal_pdf (gaussian_prod_mu m m' s s') (gaussian_prod_sigma s s') x.
Proof.
move=> hs hs'.
by rewrite /gaussian_prod_scalar /gaussian_prod_mu /gaussian_prod_sigma
           normal_pdf_times.
Qed.

(* Chaining lemma: accumulate a scalar factor through iteration *)
Lemma normal_pdf_times_chain (K m m' s s' x : R) :
  s != 0 -> s' != 0 ->
  K * normal_pdf m s x * normal_pdf m' s' x =
  K * gaussian_prod_scalar m m' s s' *
  normal_pdf (gaussian_prod_mu m m' s s') (gaussian_prod_sigma s s') x.
Proof.
move=> hs hs'.
by rewrite -mulrA normal_pdf_times' // mulrA.
Qed.

(* Squared sigma simplification: avoids nested square roots *)
Lemma gaussian_prod_sigma_sqr (s s' : R) :
  s != 0 -> s' != 0 ->
  (gaussian_prod_sigma s s') ^+ 2 =
  s ^+ 2 * s' ^+ 2 / (s ^+ 2 + s' ^+ 2).
Proof.
move=> hs hs'.
have hS : s ^+ 2 + s' ^+ 2 != 0.
  by rewrite paddr_eq0 ?sqr_ge0 // !sqrf_eq0; apply/nandP; left.
rewrite /gaussian_prod_sigma exprMn exprVn.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 //.
by field.
Qed.

(* Non-zero sigma preservation *)
Lemma gaussian_prod_sigma_neq0 (s s' : R) :
  s != 0 -> s' != 0 -> gaussian_prod_sigma s s' != 0.
Proof.
move=> hs hs'.
have hsqS : sqrtr (s ^+ 2 + s' ^+ 2) != 0.
  apply: lt0r_neq0; rewrite sqrtr_gt0.
  by apply: addr_gt0; rewrite exprn_even_gt0 //=.
by rewrite /gaussian_prod_sigma mulf_neq0 ?invr_neq0 // mulf_neq0.
Qed.

(* ===================================================================== *)
(* Phase 1: Integrate out the intercept b                                *)
(* ===================================================================== *)
(* The evidence integral is:
     integrate integrate obs(s,b) * N(0,3,s) * N(0,3,b) ds db

   As a function of b, each data point contributes:
     d(k*s+b, y_k) = normal_pdf(y_k - k*s, 1/2, b)

   The 5 data points (1,2.5), (2,3.8), (3,4.5), (4,6.2), (5,8.0) give:
     N(5/2-s, 1/2, b) * N(19/5-2s, 1/2, b) * N(9/2-3s, 1/2, b) *
     N(31/5-4s, 1/2, b) * N(8-5s, 1/2, b)

   We iteratively combine these with the prior N(0, 3, b) using
   normal_pdf_times. After each combination with a 1/2-variance factor,
   sigma^2 follows the recurrence: var_{k+1} = var_k / (4*var_k + 1).

   Concretely: var_0 = 9, var_k = 9/(36k+1).

   After integrating out b (using that integral of a normal pdf is 1),
   we get a scalar function of s times the remaining s-prior. *)

(* --- Variance recurrence ------------------------------------------------ *)

Local Notation ltW := order.Order.POrderTheory.ltW.

(* When combining N(mu, sqrtr(V), b) with N(m', 1/2, b), the new
   variance is V/(4V+1) because:
     sqrtr(V)^2 * (1/2)^2 / (sqrtr(V)^2 + (1/2)^2)
       = V * 1/4 / (V + 1/4) = V / (4V + 1)                          *)
Lemma var_recurrence (V : R) :
  (0 < V)%R ->
  (sqrtr V ^+ 2 * (2%:R ^-1) ^+ 2 / (sqrtr V ^+ 2 + (2%:R ^-1) ^+ 2) =
  V / (V *+ 4 + 1))%R.
Proof.
move=> hV.
have hV0 : V != 0 by apply: lt0r_neq0.
have hVn4 : (V *+ 4 + 1 != 0)%R.
  apply: lt0r_neq0.
  by rewrite addr_gt0 // ?ltr01 // mulrn_wgt0.
rewrite sqr_sqrtr; last exact: (ltW hV).
field. by rewrite mulr_natr.
Qed.

(* --- Concrete Phase 1 combination steps -------------------------------- *)

(* Step 0->1: N(0, 3, b) * N(5/2 - s, 1/2, b)
   sigma_new^2 = 9/37, mu_new = (90 - 36*s)/37
   scalar = normal_peak(sqrt(37/4)) * normal_fun(0, sqrt(37/4), 5/2 - s) *)

Lemma phase1_step01_sigma2 :
  3%:R ^+ 2 * (2%:R^-1 : R) ^+ 2 / (3%:R ^+ 2 + (2%:R^-1) ^+ 2) =
  9%:R / 37%:R.
Proof. by field. Qed.

Lemma phase1_step01_mu (s : R) :
  gaussian_prod_mu 0 (5%:R / 2%:R - s) 3%:R (2%:R^-1) =
  (90%:R - 36%:R * s) / 37%:R.
Proof. rewrite /gaussian_prod_mu. by field. Qed.

(* Step 1->2: N(mu1, sqrtr(9/37), b) * N(19/5 - 2*s, 1/2, b)
   sigma_new^2 = 9/73, mu_new = (1134 - 540*s)/365
   where mu1 = (90 - 36*s)/37 *)

Lemma phase1_step12_sigma2 :
  (9%:R / 37%:R) * (2%:R^-1 : R) ^+ 2 /
  (9%:R / 37%:R + (2%:R^-1) ^+ 2) = 9%:R / 73%:R.
Proof. by field. Qed.

Lemma phase1_step12_mu (s : R) :
  gaussian_prod_mu ((90%:R - 36%:R * s) / 37%:R)
                   (19%:R / 5%:R - 2%:R * s)
                   (sqrtr (9%:R / 37%:R))
                   (2%:R^-1) =
  (1134%:R - 540%:R * s) / 365%:R.
Proof.
rewrite /gaussian_prod_mu.
have h9_37 : (0 <= 9%:R / 37%:R :> R)%R.
  by apply: divr_ge0; rewrite ?ler0n.
rewrite sqr_sqrtr //.
by field.
Qed.

(* Step 2->3: N(mu2, sqrtr(9/73), b) * N(9/2 - 3*s, 1/2, b)
   sigma_new^2 = 9/109, mu_new = (1944 - 1080*s)/545
   where mu2 = (1134 - 540*s)/365 *)

Lemma phase1_step23_sigma2 :
  (9%:R / 73%:R) * (2%:R^-1 : R) ^+ 2 /
  (9%:R / 73%:R + (2%:R^-1) ^+ 2) = 9%:R / 109%:R.
Proof. by field. Qed.

Lemma phase1_step23_mu (s : R) :
  gaussian_prod_mu ((1134%:R - 540%:R * s) / 365%:R)
                   (9%:R / 2%:R - 3%:R * s)
                   (sqrtr (9%:R / 73%:R))
                   (2%:R^-1) =
  (1944%:R - 1080%:R * s) / 545%:R.
Proof.
rewrite /gaussian_prod_mu.
have h9_73 : (0 <= 9%:R / 73%:R :> R)%R.
  by apply: divr_ge0; rewrite ?ler0n.
rewrite sqr_sqrtr //.
by field.
Qed.

(* --- Combined product after 3 steps ------------------------------------ *)

(* After combining 3 data points with the prior:
   N(0,3,b) * N(5/2-s,1/2,b) * N(19/5-2s,1/2,b) * N(9/2-3s,1/2,b)
   = K1(s) * K2(s) * K3(s) * N(mu3(s), sqrtr(9/109), b)

   where Ki(s) are the scalar factors from each step. *)

(* Positivity lemmas for the intermediate variances *)
Lemma phase1_var1_gt0 : (0 < 9%:R / 37%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

Lemma phase1_var2_gt0 : (0 < 9%:R / 73%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

Lemma phase1_var3_gt0 : (0 < 9%:R / 109%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

(* The sqrtr of each variance is nonzero *)
Lemma phase1_sqrtr_var1_neq0 : sqrtr (9%:R / 37%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var1_gt0. Qed.

Lemma phase1_sqrtr_var2_neq0 : sqrtr (9%:R / 73%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var2_gt0. Qed.

Lemma phase1_sqrtr_var3_neq0 : sqrtr (9%:R / 109%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var3_gt0. Qed.

(* Helper: 2^-1 != 0 *)
Lemma half_neq0 : (2%:R^-1 : R) != 0.
Proof. by rewrite invr_neq0 // pnatr_eq0. Qed.

(* Helper: 3 != 0 *)
Lemma three_neq0 : (3%:R : R) != 0.
Proof. by rewrite pnatr_eq0. Qed.

(* The main Phase 1 result for the first 3 steps:
   Combine N(0,3,b) with 3 data-point factors. *)
Lemma phase1_combine3 (s b : R) :
  normal_pdf 0 3%:R b *
  normal_pdf (5%:R / 2%:R - s) (2%:R^-1) b *
  normal_pdf (19%:R / 5%:R - 2%:R * s) (2%:R^-1) b *
  normal_pdf (9%:R / 2%:R - 3%:R * s) (2%:R^-1) b =
  gaussian_prod_scalar 0 (5%:R / 2%:R - s) 3%:R (2%:R^-1) *
  gaussian_prod_scalar ((90%:R - 36%:R * s) / 37%:R)
                       (19%:R / 5%:R - 2%:R * s)
                       (sqrtr (9%:R / 37%:R)) (2%:R^-1) *
  gaussian_prod_scalar ((1134%:R - 540%:R * s) / 365%:R)
                       (9%:R / 2%:R - 3%:R * s)
                       (sqrtr (9%:R / 73%:R)) (2%:R^-1) *
  normal_pdf ((1944%:R - 1080%:R * s) / 545%:R)
             (sqrtr (9%:R / 109%:R)) b.
Proof.
(* Step 0->1: apply normal_pdf_times' with s=3, s'=1/2 *)
rewrite (normal_pdf_times' _ _ _ three_neq0 half_neq0).
rewrite phase1_step01_mu.
(* Now the sigma is gaussian_prod_sigma 3 (2^-1).
   We need to show it equals sqrtr(9/37). *)
have sigma01 : gaussian_prod_sigma 3%:R (2%:R^-1 : R) = sqrtr (9%:R / 37%:R).
  have hge0 : (0 <= gaussian_prod_sigma 3%:R (2%:R^-1 : R))%R.
    by apply: divr_ge0; rewrite ?mulr_ge0 ?invr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite -[LHS](ger0_norm hge0) -sqrtr_sqr.
  congr (sqrtr _).
  rewrite gaussian_prod_sigma_sqr ?pnatr_eq0 ?invr_neq0 ?pnatr_eq0 //.
  by field.
rewrite sigma01.
(* Step 1->2 *)
rewrite mulrA (normal_pdf_times_chain _ _ _ _ phase1_sqrtr_var1_neq0 half_neq0).
rewrite phase1_step12_mu.
have sigma12 : gaussian_prod_sigma (sqrtr (9%:R / 37%:R)) (2%:R^-1 : R) =
               sqrtr (9%:R / 73%:R).
  have hge0 : (0 <= gaussian_prod_sigma (sqrtr (9%:R / 37%:R)) (2%:R^-1 : R))%R.
    by apply: divr_ge0; rewrite ?mulr_ge0 ?invr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite -[LHS](ger0_norm hge0) -sqrtr_sqr.
  congr (sqrtr _).
  rewrite gaussian_prod_sigma_sqr ?invr_neq0 ?pnatr_eq0 //.
  rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
  by field.
rewrite sigma12.
(* Step 2->3 *)
rewrite mulrA (normal_pdf_times_chain _ _ _ _ phase1_sqrtr_var2_neq0 half_neq0).
rewrite phase1_step23_mu.
have sigma23 : gaussian_prod_sigma (sqrtr (9%:R / 73%:R)) (2%:R^-1 : R) =
               sqrtr (9%:R / 109%:R).
  have hge0 : (0 <= gaussian_prod_sigma (sqrtr (9%:R / 73%:R)) (2%:R^-1 : R))%R.
    by apply: divr_ge0; rewrite ?mulr_ge0 ?invr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite -[LHS](ger0_norm hge0) -sqrtr_sqr.
  congr (sqrtr _).
  rewrite gaussian_prod_sigma_sqr ?invr_neq0 ?pnatr_eq0 //.
  rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
  by field.
rewrite sigma23.
by rewrite !mulrA.
Qed.

End NormalDensityAlgebra.
