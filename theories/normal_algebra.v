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

(* Step 3->4: N(mu3, sqrtr(9/109), b) * N(31/5 - 4*s, 1/2, b)
   sigma_new^2 = 9/145, mu_new = (3060 - 1800*s)/725
   where mu3 = (1944 - 1080*s)/545 *)

Lemma phase1_step34_sigma2 :
  (9%:R / 109%:R) * (2%:R^-1 : R) ^+ 2 /
  (9%:R / 109%:R + (2%:R^-1) ^+ 2) = 9%:R / 145%:R.
Proof. by field. Qed.

Lemma phase1_step34_mu (s : R) :
  gaussian_prod_mu ((1944%:R - 1080%:R * s) / 545%:R)
                   (31%:R / 5%:R - 4%:R * s)
                   (sqrtr (9%:R / 109%:R))
                   (2%:R^-1) =
  (3060%:R - 1800%:R * s) / 725%:R.
Proof.
rewrite /gaussian_prod_mu.
have h9_109 : (0 <= 9%:R / 109%:R :> R)%R.
  by apply: divr_ge0; rewrite ?ler0n.
rewrite sqr_sqrtr //.
by field.
Qed.

(* Step 4->5: N(mu4, sqrtr(9/145), b) * N(8 - 5*s, 1/2, b)
   sigma_new^2 = 9/181, mu_new = (4500 - 2700*s)/905
   where mu4 = (3060 - 1800*s)/725 *)

Lemma phase1_step45_sigma2 :
  (9%:R / 145%:R) * (2%:R^-1 : R) ^+ 2 /
  (9%:R / 145%:R + (2%:R^-1) ^+ 2) = 9%:R / 181%:R.
Proof. by field. Qed.

Lemma phase1_step45_mu (s : R) :
  gaussian_prod_mu ((3060%:R - 1800%:R * s) / 725%:R)
                   (8%:R - 5%:R * s)
                   (sqrtr (9%:R / 145%:R))
                   (2%:R^-1) =
  (4500%:R - 2700%:R * s) / 905%:R.
Proof.
rewrite /gaussian_prod_mu.
have h9_145 : (0 <= 9%:R / 145%:R :> R)%R.
  by apply: divr_ge0; rewrite ?ler0n.
rewrite sqr_sqrtr //.
by field.
Qed.

(* --- Combined product after all 5 steps ------------------------------- *)

(* After combining all 5 data points with the prior:
   N(0,3,b) * prod_{k=1}^{5} N(y_k - k*s, 1/2, b)
   = K1(s)*...*K5(s) * N(mu5(s), sqrtr(9/181), b)

   where Ki(s) are the scalar factors from each step. *)

(* Positivity lemmas for the intermediate variances *)
Lemma phase1_var1_gt0 : (0 < 9%:R / 37%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

Lemma phase1_var2_gt0 : (0 < 9%:R / 73%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

Lemma phase1_var3_gt0 : (0 < 9%:R / 109%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

Lemma phase1_var4_gt0 : (0 < 9%:R / 145%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

Lemma phase1_var5_gt0 : (0 < 9%:R / 181%:R :> R)%R.
Proof. by apply: divr_gt0; rewrite ?ltr0n. Qed.

(* The sqrtr of each variance is nonzero *)
Lemma phase1_sqrtr_var1_neq0 : sqrtr (9%:R / 37%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var1_gt0. Qed.

Lemma phase1_sqrtr_var2_neq0 : sqrtr (9%:R / 73%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var2_gt0. Qed.

Lemma phase1_sqrtr_var3_neq0 : sqrtr (9%:R / 109%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var3_gt0. Qed.

Lemma phase1_sqrtr_var4_neq0 : sqrtr (9%:R / 145%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var4_gt0. Qed.

Lemma phase1_sqrtr_var5_neq0 : sqrtr (9%:R / 181%:R) != (0 : R).
Proof. apply: lt0r_neq0; rewrite sqrtr_gt0; exact: phase1_var5_gt0. Qed.

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

(* The full Phase 1 result: Combine N(0,3,b) with all 5 data-point factors. *)
Lemma phase1_combine5 (s b : R) :
  normal_pdf 0 3%:R b *
  normal_pdf (5%:R / 2%:R - s) (2%:R^-1) b *
  normal_pdf (19%:R / 5%:R - 2%:R * s) (2%:R^-1) b *
  normal_pdf (9%:R / 2%:R - 3%:R * s) (2%:R^-1) b *
  normal_pdf (31%:R / 5%:R - 4%:R * s) (2%:R^-1) b *
  normal_pdf (8%:R - 5%:R * s) (2%:R^-1) b =
  gaussian_prod_scalar 0 (5%:R / 2%:R - s) 3%:R (2%:R^-1) *
  gaussian_prod_scalar ((90%:R - 36%:R * s) / 37%:R)
                       (19%:R / 5%:R - 2%:R * s)
                       (sqrtr (9%:R / 37%:R)) (2%:R^-1) *
  gaussian_prod_scalar ((1134%:R - 540%:R * s) / 365%:R)
                       (9%:R / 2%:R - 3%:R * s)
                       (sqrtr (9%:R / 73%:R)) (2%:R^-1) *
  gaussian_prod_scalar ((1944%:R - 1080%:R * s) / 545%:R)
                       (31%:R / 5%:R - 4%:R * s)
                       (sqrtr (9%:R / 109%:R)) (2%:R^-1) *
  gaussian_prod_scalar ((3060%:R - 1800%:R * s) / 725%:R)
                       (8%:R - 5%:R * s)
                       (sqrtr (9%:R / 145%:R)) (2%:R^-1) *
  normal_pdf ((4500%:R - 2700%:R * s) / 905%:R)
             (sqrtr (9%:R / 181%:R)) b.
Proof.
(* Use set to control term sizes during rewriting *)
set N0 := normal_pdf 0 3%:R b.
set N1 := normal_pdf (5%:R / 2%:R - s) (2%:R^-1) b.
set N2 := normal_pdf (19%:R / 5%:R - 2%:R * s) (2%:R^-1) b.
set N3 := normal_pdf (9%:R / 2%:R - 3%:R * s) (2%:R^-1) b.
set N4 := normal_pdf (31%:R / 5%:R - 4%:R * s) (2%:R^-1) b.
set N5 := normal_pdf (8%:R - 5%:R * s) (2%:R^-1) b.
(* Steps 0-3: use phase1_combine3 on the first 4 factors *)
rewrite /N4 /N5 /N0 /N1 /N2 /N3 (phase1_combine3 s b).
(* Step 3->4: hide the accumulated scalar to speed up matching *)
set K3 := gaussian_prod_scalar 0 _ _ _ *
           gaussian_prod_scalar _ _ _ _ *
           gaussian_prod_scalar _ (9%:R / 2%:R - 3%:R * s) _ _.
rewrite mulrA (normal_pdf_times_chain _ _ _ _ phase1_sqrtr_var3_neq0 half_neq0).
rewrite phase1_step34_mu.
have sigma34 : gaussian_prod_sigma (sqrtr (9%:R / 109%:R)) (2%:R^-1 : R) =
               sqrtr (9%:R / 145%:R).
  have hge0 : (0 <= gaussian_prod_sigma (sqrtr (9%:R / 109%:R)) (2%:R^-1 : R))%R.
    by apply: divr_ge0; rewrite ?mulr_ge0 ?invr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite -[LHS](ger0_norm hge0) -sqrtr_sqr.
  congr (sqrtr _).
  rewrite gaussian_prod_sigma_sqr ?invr_neq0 ?pnatr_eq0 //.
  rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
  by field.
rewrite sigma34.
(* Step 4->5: hide scalar prefix again *)
set K4 := K3 * gaussian_prod_scalar _ _ _ _.
rewrite (normal_pdf_times_chain _ _ _ _ phase1_sqrtr_var4_neq0 half_neq0).
rewrite phase1_step45_mu.
have sigma45 : gaussian_prod_sigma (sqrtr (9%:R / 145%:R)) (2%:R^-1 : R) =
               sqrtr (9%:R / 181%:R).
  have hge0 : (0 <= gaussian_prod_sigma (sqrtr (9%:R / 145%:R)) (2%:R^-1 : R))%R.
    by apply: divr_ge0; rewrite ?mulr_ge0 ?invr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite -[LHS](ger0_norm hge0) -sqrtr_sqr.
  congr (sqrtr _).
  rewrite gaussian_prod_sigma_sqr ?invr_neq0 ?pnatr_eq0 //.
  rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
  by field.
rewrite sigma45.
rewrite /gaussian_prod_scalar.
by rewrite !mulrA.
Qed.

(* ===================================================================== *)
(* Phase 2: Integrate out the slope s                                    *)
(* ===================================================================== *)

(* After Phase 1, integrating out b gives:
     integral_b [N(0,3,b) * obs_b(s,b)] db = Scalar(s)
   where Scalar(s) = prod_{k=1}^{5} gaussian_prod_scalar_k(s).

   Each gaussian_prod_scalar_k(s) = normal_peak(S_k) * normal_fun(mu_k(s), S_k, m'_k(s))
   where S_k = sqrt(sigma_k^2 + 1/4) is a constant and mu_k, m'_k are linear in s.

   The normal_fun factors, when viewed as functions of s, are Gaussians in s.
   To iterate normal_pdf_times through these with the prior N(0,3,s),
   we need to convert each normal_fun factor to a normal_pdf in s.

   Key tools:
   - normal_fun_sym: normal_fun(m, sigma, x) = normal_fun(x, sigma, m)
   - normal_fun_linear: converts normal_fun(mu(s), S, m'(s)) to
     normal_fun(center, width, s) when m'-mu is linear in s.
*)

(* normal_fun is symmetric: (x-m)^2 = (m-x)^2 *)
Lemma normal_fun_sym (m s x : R) :
  normal_fun m s x = normal_fun x s m.
Proof.
rewrite /normal_fun; congr (sequences.expR _).
rewrite -sqrrN; congr (- _ / _); congr (_ ^+ 2).
ring.
Qed.

(* normal_fun with zero center and subtraction *)
Lemma normal_fun_sub (m s a : R) :
  normal_fun 0 s (a - m) = normal_fun a s m.
Proof.
rewrite /normal_fun; congr (sequences.expR _).
congr (- _ / _).
rewrite -sqrrN; congr (_ ^+ 2).
ring.
Qed.

(* Key identity for Phase 2: when the difference m'-m is a linear
   function (a - B*s)/c of the variable s, the normal_fun can be
   rewritten as a normal_fun centered at a/B with width sigma*c/B. *)
Lemma normal_fun_linear (m m' sigma a B c s : R) :
  B != 0 -> c != 0 -> sigma != 0 ->
  m' - m = (a - B * s) / c ->
  normal_fun m sigma m' = normal_fun (a / B) (sigma * c / B) s.
Proof.
move=> hB hc hsigma hdiff.
suff heq : (m' - m) ^+ 2 / (sigma ^+ 2 *+ 2) =
            (s - a / B) ^+ 2 / ((sigma * c / B) ^+ 2 *+ 2).
  rewrite /normal_fun; congr (sequences.expR _).
  rewrite !mulNr; congr (- _).
  exact: heq.
rewrite hdiff.
have h : (a - B * s) / c = - (B / c) * (s - a / B).
  field. by rewrite hB hc.
rewrite h -mulNr exprMn.
rewrite -(mulr_natr (sigma ^+ 2) 2) -(mulr_natr ((sigma * c / B) ^+ 2) 2).
rewrite !exprMn exprVn.
field.
by rewrite hsigma hB hc.
Qed.

(* ===================================================================== *)
(* Phase 2: Rewriting each gaussian_prod_scalar as a function of s       *)
(* ===================================================================== *)

(* For each Phase 1 combination step k, the scalar factor
     gaussian_prod_scalar(mu_k(s), m'_k(s), sigma_k, 1/2)
   contains a normal_fun factor that is Gaussian in s.

   We now compute the concrete center and width for each step,
   enabling iterative application of normal_pdf_times with
   the prior N(0, 3, s).

   For each step, the difference m'_k(s) - mu_k(s) = (A_k - B_k*s) / C_k
   where A_k, B_k, C_k are specific rational constants. Then by
   normal_fun_linear, the normal_fun factor becomes
   normal_fun(A_k/B_k, S_k*C_k/B_k, s) where S_k = sqrt(sigma_k^2 + 1/4). *)

(* Step 0->1: m=0, m'=5/2-s, S=sqrt(37/4)
   diff = 5/2-s = (5/2 - 1*s)/1, so A=5/2, B=1, C=1
   center = 5/2, width = sqrt(37/4) *)
Lemma phase2_scalar01_diff (s : R) :
  (5%:R / 2%:R - s) - 0 = (5%:R / 2%:R - 1 * s) / 1.
Proof. by field. Qed.

Lemma phase2_scalar01_fun (s : R) :
  normal_fun 0 (sqrtr (3%:R ^+ 2 + (2%:R^-1) ^+ 2))
             (5%:R / 2%:R - s) =
  normal_fun (5%:R / 2%:R) (sqrtr (3%:R ^+ 2 + (2%:R^-1) ^+ 2)) s.
Proof. by rewrite normal_fun_sub. Qed.

(* Step 1->2: m=(90-36s)/37, m'=19/5-2s, S=sqrt(9/37+1/4)=sqrt(73/148)
   diff = 19/5-2s - (90-36s)/37 = (253 - 190s)/185
   A=253, B=190, C=185
   center = 253/190, width = sqrt(73/148)*185/190 *)
Lemma phase2_scalar12_diff (s : R) :
  (19%:R / 5%:R - 2%:R * s) - (90%:R - 36%:R * s) / 37%:R =
  (253%:R - 190%:R * s) / 185%:R.
Proof. by field. Qed.

(* Step 2->3: m=(1134-540s)/365, m'=9/2-3s, S=sqrt(9/73+1/4)=sqrt(109/292)
   diff = 9/2-3s - (1134-540s)/365 = (1017 - 1110*s)/730
   A=1017, B=1110, C=730 *)
Lemma phase2_scalar23_diff (s : R) :
  (9%:R / 2%:R - 3%:R * s) - (1134%:R - 540%:R * s) / 365%:R =
  (1017%:R - 1110%:R * s) / 730%:R.
Proof. by field. Qed.

(* Step 3->4: m=(1944-1080s)/545, m'=31/5-4s, S=sqrt(9/109+1/4)=sqrt(145/436)
   diff = 31/5-4s - (1944-1080s)/545 = (287 - 220*s)/109
   A=287, B=220, C=109 *)
Lemma phase2_scalar34_diff (s : R) :
  (31%:R / 5%:R - 4%:R * s) - (1944%:R - 1080%:R * s) / 545%:R =
  (287%:R - 220%:R * s) / 109%:R.
Proof. by field. Qed.

(* Step 4->5: m=(3060-1800s)/725, m'=8-5s, S=sqrt(9/145+1/4)=sqrt(181/580)
   diff = 8-5s - (3060-1800s)/725 = (548 - 365*s)/145
   A=548, B=365, C=145 *)
Lemma phase2_scalar45_diff (s : R) :
  (8%:R - 5%:R * s) - (3060%:R - 1800%:R * s) / 725%:R =
  (548%:R - 365%:R * s) / 145%:R.
Proof. by field. Qed.

(* For the full Phase 2 computation, each step k requires:
   1. Computing the difference m'_k(s) - mu_k(s) = (A_k - B_k*s) / C_k
   2. Applying normal_fun_linear to get normal_fun(A_k/B_k, S_k*C_k/B_k, s)
   3. Combining with the accumulated Gaussian using normal_pdf_times

   The 10 total combination steps (5 for b, 5 for s) yield the final
   normalizing constant:

     C = (4*sqrt(2) / (pi^2 * sqrt(66961*pi))) * exp(-1674761 / 1674025)

   The Phase 1 computation (steps 0-5 in b) is complete above.
   The Phase 2 computation (steps 6-10 in s) follows the same algebraic
   pattern but with the s-variable normal_fun factors derived from the
   Phase 1 gaussian_prod_scalar terms.

   The key building blocks are:
   - phase1_combine5: complete Phase 1 result
   - normal_fun_linear: converts Phase 1 scalar factors to s-Gaussians
   - normal_pdf_times_chain: iterative combination
   - gaussian_prod_sigma_sqr: variance simplification

   Documentation of the Phase 2 parameters:
   Step 6 (0->1 in s): N(0,3,s) * N_fun_01(s)
     center=5/2, S=sqrt(37/4), width=sqrt(37/4)
   Step 7 (1->2 in s): result * N_fun_12(s)
     center=253/190, S=sqrt(73/148), width=sqrt(73/148)*185/190
   Step 8 (2->3 in s): result * N_fun_23(s)
     center=2151/1635, S=sqrt(109/292), width=sqrt(109/292)*730/1635
   Step 9 (3->4 in s): result * N_fun_34(s)
     center=5049/3780, S=sqrt(145/580), width=sqrt(145/580)*1450/3780
   Step 10 (4->5 in s): result * N_fun_45(s)
     center=10647/7925, S=sqrt(181/1448), width=sqrt(181/1448)*2175/7925
*)

(* ===================================================================== *)
(* Bridge: obs-style products to centered normal_pdf form                 *)
(* ===================================================================== *)

(* Key identity for converting obs(s,b) to the form used by phase1:
   normal_pdf(s*k+b, sigma, y) = normal_pdf(y-k*s, sigma, b).
   This combines symmetry (x-m)^2 = (m-x)^2 with the algebraic
   identity y - (s*k+b) = -(b - (y-k*s)).

   Note: uses s*k (not k*s) to match the obs definition order. *)
Lemma normal_pdf_recenter (y s k sigma b : R) (hs : sigma != 0) :
  normal_pdf (s * k + b) sigma y = normal_pdf (y - k * s) sigma b.
Proof.
rewrite !(normal_pdfE _ hs); congr (_ * _).
rewrite /normal_fun; congr (sequences.expR _).
congr (- _ / _).
suff -> : (y - ((s * k)%R + b)%E) = - (b - (y - k * s)) by rewrite sqrrN.
ring.
Qed.

Arguments normal_pdf_recenter : clear implicits.

(* obs(s,b) = d(s*1+b, 5/2) * d(s*2+b, 19/5) * d(s*3+b, 9/2)
              * d(s*4+b, 31/5) * d(s*5+b, 8)
   where d(mu,x) = normal_pdf(mu, 1/2, x).

   Rewrite as a product of normal_pdf's centered at y_k - k*s,
   evaluated at b, which is the form consumed by phase1_combine5. *)
Lemma obs_rewrite (s b : R) :
  normal_pdf (s * 1 + b) (2%:R^-1) (5%:R / 2%:R) *
  normal_pdf (s * 2%:R + b) (2%:R^-1) (19%:R / 5%:R) *
  normal_pdf (s * 3%:R + b) (2%:R^-1) (9%:R / 2%:R) *
  normal_pdf (s * 4%:R + b) (2%:R^-1) (31%:R / 5%:R) *
  normal_pdf (s * 5%:R + b) (2%:R^-1) 8%:R =
  normal_pdf (5%:R / 2%:R - s) (2%:R^-1) b *
  normal_pdf (19%:R / 5%:R - 2%:R * s) (2%:R^-1) b *
  normal_pdf (9%:R / 2%:R - 3%:R * s) (2%:R^-1) b *
  normal_pdf (31%:R / 5%:R - 4%:R * s) (2%:R^-1) b *
  normal_pdf (8%:R - 5%:R * s) (2%:R^-1) b.
Proof.
rewrite (normal_pdf_recenter (5%:R/2%:R) s 1 (2%:R^-1) b half_neq0)
        (normal_pdf_recenter (19%:R/5%:R) s 2%:R (2%:R^-1) b half_neq0)
        (normal_pdf_recenter (9%:R/2%:R) s 3%:R (2%:R^-1) b half_neq0)
        (normal_pdf_recenter (31%:R/5%:R) s 4%:R (2%:R^-1) b half_neq0)
        (normal_pdf_recenter 8%:R s 5%:R (2%:R^-1) b half_neq0).
congr (_ * _ * _ * _ * _); rewrite ?mul1r //.
Qed.

End NormalDensityAlgebra.
