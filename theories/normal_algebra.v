(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals ereal topology
  normedtype numfun measure sequences lebesgue_integral lebesgue_integral_fubini
  lebesgue_stieltjes_measure probability boolp trigo exp.
From mathcomp.algebra_tactics Require Import ring.

(**md**************************************************************************)
(* # Normal Density Algebra                                                  *)
(*                                                                           *)
(* Algebraic identities for products of normal (Gaussian) probability        *)
(* density functions, used to compute evidence integrals in Bayesian         *)
(* inference. The main result `normal_pdf_times` expresses the product       *)
(* of two normal PDFs as a scalar times a third normal PDF.                  *)
(*                                                                           *)
(* The file also develops the concrete Phase 1 and Phase 2 computations      *)
(* for the Bayesian linear regression example, iteratively combining         *)
(* normal PDFs via `normal_pdf_times_chain`.                                 *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import order.Order.POrderTheory.

Section normal_density_algebra.
Variable R : realType.
Local Open Scope ring_scope.

Implicit Types (m s x K : R) (n : nat).

(* Helper: 2^-1 != 0 *)
Let half_neq0 : (2%:R^-1 : R) != 0.
Proof. by rewrite invr_neq0 // pnatr_eq0. Qed.

(* Helper: 3 != 0 *)
Let three_neq0 : (3%:R : R) != 0.
Proof. by rewrite pnatr_eq0. Qed.

(* Helper: sqrtr of a positive rational is nonzero. *)
Local Lemma sqrtr_pnat_div_neq0 (a b : nat) :
  (0 < a)%N -> (0 < b)%N -> sqrtr (a%:R / b%:R : R) != 0.
Proof.
move=> ha hb; apply: lt0r_neq0; rewrite sqrtr_gt0.
by apply: divr_gt0; rewrite ltr0n.
Qed.

(* General identities about normal densities                             *)
Section normal_pdf_general.

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
have hSgt0 : 0 < s ^+ 2 + s' ^+ 2.
  by apply: addr_gt0; rewrite exprn_even_gt0 //=.
have hsqS : sqrtr (s ^+ 2 + s' ^+ 2) != 0.
  by apply: lt0r_neq0; rewrite sqrtr_gt0.
have hsnew : s * s' / sqrtr (s ^+ 2 + s' ^+ 2) != 0.
  by rewrite mulf_neq0 ?invr_neq0 // mulf_neq0.
have hpi : 0 <= pi := pi_ge0 R.
have hs2pi : 0 <= s ^+ 2 * pi := mulr_ge0 (sqr_ge0 _) hpi.
have hS2pi : 0 <= (s ^+ 2 + s' ^+ 2) * pi.
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
  by field; exact: hS.
- (* funsE *)
  rewrite /normal_fun -expRD -[RHS]expRD.
  congr (expR _).
  rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 //.
  rewrite exprMn exprVn sqr_sqrtr ?addr_ge0 ?sqr_ge0 //.
  field.
  by rewrite hS hs hs'.
Qed.

(* Helper definitions for iterating normal_pdf_times                     *)

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

(* Positivity of gaussian_prod_scalar: product of positive peak and fun *)
Lemma gaussian_prod_scalar_gt0 (m m' s s' : R) :
  s != 0 -> s' != 0 -> 0 < gaussian_prod_scalar m m' s s'.
Proof.
move=> hs hs'.
have hsqS : sqrtr (s ^+ 2 + s' ^+ 2) != 0.
  apply: lt0r_neq0; rewrite sqrtr_gt0.
  by apply: addr_gt0; rewrite exprn_even_gt0 //=.
rewrite /gaussian_prod_scalar.
apply: mulr_gt0; first exact: (normal_peak_gt0 hsqS).
rewrite /normal_fun; exact: expR_gt0.
Qed.

End normal_pdf_general.

(* Bayesian Phase 1: Integrate out the intercept b                       *)
Section bayesian_phase1_intercept.

(* Phase 1: Integrate out the intercept b                                *)

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

(* Variance recurrence *)

(* When combining N(mu, sqrtr(V), b) with N(m', 1/2, b), the new
   variance is V/(4V+1) because:
     sqrtr(V)^2 * (1/2)^2 / (sqrtr(V)^2 + (1/2)^2)
       = V * 1/4 / (V + 1/4) = V / (4V + 1)                          *)
Lemma var_recurrence (V : R) :
  0 < V ->
  sqrtr V ^+ 2 * (2%:R ^-1) ^+ 2 / (sqrtr V ^+ 2 + (2%:R ^-1) ^+ 2) =
  V / (V *+ 4 + 1).
Proof.
move=> hV.
have hV0 : V != 0 by apply: lt0r_neq0.
have hVn4 : V *+ 4 + 1 != 0.
  apply: lt0r_neq0.
  by rewrite addr_gt0 // ?ltr01 // mulrn_wgt0.
rewrite sqr_sqrtr; last exact: (ltW hV).
by field; rewrite mulr_natr.
Qed.

(* Concrete Phase 1 combination steps *)

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
have h9_37 : (0 <= 9%:R / 37%:R :> R).
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
have h9_73 : (0 <= 9%:R / 73%:R :> R).
  by apply: divr_ge0; rewrite ?ler0n.
rewrite sqr_sqrtr //.
by field.
Qed.

(* Step 3->4: N(mu3, sqrtr(9/109), b) * N(31/5 - 4*s, 1/2, b)
   sigma_new^2 = 9/145, mu_new = (612 - 360*s)/145
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
  (612%:R - 360%:R * s) / 145%:R.
Proof.
rewrite /gaussian_prod_mu.
have h9_109 : (0 <= 9%:R / 109%:R :> R).
  by apply: divr_ge0; rewrite ?ler0n.
rewrite sqr_sqrtr //.
by field.
Qed.

(* Step 4->5: N(mu4, sqrtr(9/145), b) * N(8 - 5*s, 1/2, b)
   sigma_new^2 = 9/181, mu_new = (900 - 540*s)/181
   where mu4 = (612 - 360*s)/145 *)

Lemma phase1_step45_sigma2 :
  (9%:R / 145%:R) * (2%:R^-1 : R) ^+ 2 /
  (9%:R / 145%:R + (2%:R^-1) ^+ 2) = 9%:R / 181%:R.
Proof. by field. Qed.

Lemma phase1_step45_mu (s : R) :
  gaussian_prod_mu ((612%:R - 360%:R * s) / 145%:R)
                   (8%:R - 5%:R * s)
                   (sqrtr (9%:R / 145%:R))
                   (2%:R^-1) =
  (900%:R - 540%:R * s) / 181%:R.
Proof.
rewrite /gaussian_prod_mu.
have h9_145 : (0 <= 9%:R / 145%:R :> R).
  by apply: divr_ge0; rewrite ?ler0n.
rewrite sqr_sqrtr //.
by field.
Qed.

(* Combined product after all 5 steps *)

(* After combining all 5 data points with the prior:
   N(0,3,b) * prod_{k=1}^{5} N(y_k - k*s, 1/2, b)
   = K1(s)*...*K5(s) * N(mu5(s), sqrtr(9/181), b)

   where Ki(s) are the scalar factors from each step. *)

(* Parameterized positivity for 9/n fractions *)
Lemma nine_div_gt0 (n : nat) : (0 < n)%N -> 0 < 9%:R / n%:R :> R.
Proof. by move=> hn; apply: divr_gt0; rewrite ?ltr0n. Qed.

Lemma sqrtr_nine_div_neq0 (n : nat) : (0 < n)%N ->
  sqrtr (9%:R / n%:R) != (0 : R).
Proof.
by move=> hn; apply: lt0r_neq0; rewrite sqrtr_gt0;
   exact: nine_div_gt0.
Qed.

(* The sqrtr of each variance is nonzero *)
Lemma phase1_sqrtr_var1_neq0 : sqrtr (9%:R / 37%:R) != (0 : R).
Proof. exact: sqrtr_nine_div_neq0. Qed.

Lemma phase1_sqrtr_var2_neq0 : sqrtr (9%:R / 73%:R) != (0 : R).
Proof. exact: sqrtr_nine_div_neq0. Qed.

Lemma phase1_sqrtr_var3_neq0 : sqrtr (9%:R / 109%:R) != (0 : R).
Proof. exact: sqrtr_nine_div_neq0. Qed.

Lemma phase1_sqrtr_var4_neq0 : sqrtr (9%:R / 145%:R) != (0 : R).
Proof. exact: sqrtr_nine_div_neq0. Qed.

Lemma phase1_sqrtr_var5_neq0 : sqrtr (9%:R / 181%:R) != (0 : R).
Proof. exact: sqrtr_nine_div_neq0. Qed.

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
  have hge0 : (0 <= gaussian_prod_sigma 3%:R (2%:R^-1 : R)).
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
  have hge0 : (0 <= gaussian_prod_sigma (sqrtr (9%:R / 37%:R)) (2%:R^-1 : R)).
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
  have hge0 : (0 <= gaussian_prod_sigma (sqrtr (9%:R / 73%:R)) (2%:R^-1 : R)).
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
  gaussian_prod_scalar ((612%:R - 360%:R * s) / 145%:R)
                       (8%:R - 5%:R * s)
                       (sqrtr (9%:R / 145%:R)) (2%:R^-1) *
  normal_pdf ((900%:R - 540%:R * s) / 181%:R)
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
  have hge0 : (0 <= gaussian_prod_sigma
    (sqrtr (9%:R / 109%:R)) (2%:R^-1 : R)).
    by apply: divr_ge0;
       rewrite ?mulr_ge0 ?invr_ge0 ?ler0n ?sqrtr_ge0.
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
  have hge0 : (0 <= gaussian_prod_sigma
    (sqrtr (9%:R / 145%:R)) (2%:R^-1 : R)).
    by apply: divr_ge0;
       rewrite ?mulr_ge0 ?invr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite -[LHS](ger0_norm hge0) -sqrtr_sqr.
  congr (sqrtr _).
  rewrite gaussian_prod_sigma_sqr ?invr_neq0 ?pnatr_eq0 //.
  rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
  by field.
rewrite sigma45.
rewrite /gaussian_prod_scalar.
by rewrite !mulrA.
Qed.

End bayesian_phase1_intercept.

(* Bayesian Phase 2: Integrate out the slope s                           *)
Section bayesian_phase2_slope.

(* Phase 2: Integrate out the slope s                                    *)

(* After Phase 1, integrating out b gives:
     integral_b [N(0,3,b) * obs_b(s,b)] db = Scalar(s)
   where Scalar(s) = prod_{k=1}^{5} gaussian_prod_scalar_k(s).

   Each gaussian_prod_scalar_k(s) =
     normal_peak(S_k) * normal_fun(mu_k(s), S_k, m'_k(s))
   where S_k = sqrt(sigma_k^2 + 1/4) is a constant and
   mu_k, m'_k are linear in s.

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
rewrite /normal_fun; congr (expR _).
rewrite -sqrrN; congr (- _ / _); congr (_ ^+ 2).
ring.
Qed.

(* normal_fun with zero center and subtraction *)
Lemma normal_fun_sub (m s a : R) :
  normal_fun 0 s (a - m) = normal_fun a s m.
Proof.
rewrite /normal_fun; congr (expR _).
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
  rewrite /normal_fun; congr (expR _).
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

(* Phase 2: Rewriting each gaussian_prod_scalar as a function of s       *)

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

(* Step 4->5: m=(612-360s)/145, m'=8-5s, S=sqrt(9/145+1/4)=sqrt(181/580)
   diff = 8-5s - (612-360s)/145 = (548 - 365*s)/145
   A=548, B=365, C=145 *)
Lemma phase2_scalar45_diff (s : R) :
  (8%:R - 5%:R * s) - (612%:R - 360%:R * s) / 145%:R =
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

(* Phase 2 Steps 0-2: Iteratively combine Phase 1 scalars with N(0,3,s) *)

(* Step 0: Combine N(0,3,s) with scalar01 *)

(* The scalar01 factor simplifies to a normal_pdf because the width
   equals S01 = sqrt(37/4), making the peaks cancel. *)
Lemma phase2_scalar01E (s : R) :
  gaussian_prod_scalar 0 (5%:R / 2%:R - s) 3%:R (2%:R^-1) =
  normal_pdf (5%:R / 2%:R) (sqrtr (37%:R / 4%:R)) s.
Proof.
rewrite /gaussian_prod_scalar.
have hsq : 3%:R ^+ 2 + (2%:R^-1 : R) ^+ 2 = 37%:R / 4%:R by field.
rewrite hsq normal_fun_sub.
have hsqrt_neq0 : sqrtr (37%:R / 4%:R : R) != 0.
  apply: lt0r_neq0; rewrite sqrtr_gt0.
  by apply: divr_gt0; rewrite ?ltr0n.
by rewrite (normal_pdfE _ hsqrt_neq0).
Qed.

(* Step 0 combination: N(0,3,s) * scalar01 via normal_pdf_times *)
Lemma phase2_step0 (s : R) :
  normal_pdf 0 3%:R s *
  gaussian_prod_scalar 0 (5%:R / 2%:R - s) 3%:R (2%:R^-1) =
  gaussian_prod_scalar 0 (5%:R / 2%:R) 3%:R (sqrtr (37%:R / 4%:R)) *
  normal_pdf (90%:R / 73%:R)
             (gaussian_prod_sigma 3%:R (sqrtr (37%:R / 4%:R))) s.
Proof.
rewrite phase2_scalar01E.
have hsqrt_neq0 := sqrtr_pnat_div_neq0 (a := 37) (b := 4) isT isT.
rewrite normal_pdf_times' //.
have -> : gaussian_prod_mu 0 (5%:R / 2%:R) 3%:R
            (sqrtr (37%:R / 4%:R : R)) = 90%:R / 73%:R.
  rewrite /gaussian_prod_mu.
  rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
  by field.
done.
Qed.

Lemma phase2_step0_sigma2 :
  (gaussian_prod_sigma 3%:R (sqrtr (37%:R / 4%:R : R))) ^+ 2 =
  333%:R / 73%:R.
Proof.
have hsqrt_neq0 := sqrtr_pnat_div_neq0 (a := 37) (b := 4) isT isT.
rewrite gaussian_prod_sigma_sqr ?pnatr_eq0 //.
rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
by field.
Qed.

Lemma phase2_step0_sigma_neq0 :
  gaussian_prod_sigma 3%:R (sqrtr (37%:R / 4%:R : R)) != 0.
Proof.
have hsqrt_neq0 := sqrtr_pnat_div_neq0 (a := 37) (b := 4) isT isT.
exact: gaussian_prod_sigma_neq0.
Qed.

(* Step 1: Combine result with scalar12 *)

(* S12 = sqrt(sqrtr(9/37)^2 + (1/2)^2) = sqrt(73/148) *)
Lemma phase2_S12 :
  sqrtr (9%:R / 37%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2 = 73%:R / 148%:R.
Proof.
rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
by field.
Qed.

(* Rewrite scalar12's normal_fun as a function of s.
   center = 253/190, width = sqrt(73/148) * 185/190. *)
Lemma phase2_scalar12_fun (s : R) :
  normal_fun ((90%:R - 36%:R * s) / 37%:R)
             (sqrtr (73%:R / 148%:R))
             (19%:R / 5%:R - 2%:R * s) =
  normal_fun (253%:R / 190%:R)
             (sqrtr (73%:R / 148%:R) * 37%:R / 38%:R) s.
Proof.
set S12 := sqrtr _.
have hS : S12 != (0 : R)
  := sqrtr_pnat_div_neq0 (a := 73) (b := 148) isT isT.
suff heq : ((19%:R / 5%:R - 2%:R * s) -
             (90%:R - 36%:R * s) / 37%:R) ^+ 2 /
            (S12 ^+ 2 *+ 2) =
            (s - 253%:R / 190%:R) ^+ 2 /
            ((S12 * 37%:R / 38%:R) ^+ 2 *+ 2).
  rewrite /normal_fun; congr (expR _).
  by rewrite !mulNr; congr (- _).
rewrite -(mulr_natr (S12 ^+ 2) 2)
        -(mulr_natr ((S12 * 37%:R / 38%:R) ^+ 2) 2).
rewrite !exprMn exprVn.
by field; rewrite hS.
Qed.

(* Width for step 1: W12 = sqrt(73/148) * 37/38 *)
Let W12 : R := sqrtr (73%:R / 148%:R) * 37%:R / 38%:R.

Lemma phase2_W12_neq0 : W12 != 0.
Proof.
apply: lt0r_neq0.
rewrite /W12.
apply: divr_gt0; last by rewrite ltr0n.
apply: mulr_gt0; last by rewrite ltr0n.
rewrite sqrtr_gt0.
by apply: divr_gt0; rewrite ?ltr0n.
Qed.

(* scalar12 = peak_ratio * normal_pdf *)
Lemma phase2_scalar12E (s : R) :
  gaussian_prod_scalar ((90%:R - 36%:R * s) / 37%:R)
                       (19%:R / 5%:R - 2%:R * s)
                       (sqrtr (9%:R / 37%:R)) (2%:R^-1) =
  normal_peak (sqrtr (73%:R / 148%:R)) /
  normal_peak W12 *
  normal_pdf (253%:R / 190%:R) W12 s.
Proof.
rewrite /gaussian_prod_scalar phase2_S12 /W12 phase2_scalar12_fun -/W12.
rewrite (normal_pdfE _ phase2_W12_neq0).
have hpeak : normal_peak W12 != 0.
  by apply: lt0r_neq0; exact: (normal_peak_gt0 phase2_W12_neq0).
by rewrite mulrA divfK.
Qed.

(* Accumulated sigma from step 0 *)
Let sigma0 : R := gaussian_prod_sigma 3%:R (sqrtr (37%:R / 4%:R)).

(* Step 1 combination *)
Lemma phase2_step1 (s : R) :
  let K0 := gaussian_prod_scalar 0 (5%:R / 2%:R) 3%:R
               (sqrtr (37%:R / 4%:R)) in
  K0 * normal_pdf (90%:R / 73%:R) sigma0 s *
  gaussian_prod_scalar ((90%:R - 36%:R * s) / 37%:R)
                       (19%:R / 5%:R - 2%:R * s)
                       (sqrtr (9%:R / 37%:R)) (2%:R^-1) =
  K0 * (normal_peak (sqrtr (73%:R / 148%:R)) / normal_peak W12) *
  gaussian_prod_scalar (90%:R / 73%:R) (253%:R / 190%:R) sigma0 W12 *
  normal_pdf (gaussian_prod_mu (90%:R / 73%:R) (253%:R / 190%:R) sigma0 W12)
             (gaussian_prod_sigma sigma0 W12) s.
Proof.
rewrite /= phase2_scalar12E.
(* LHS: (K0 * pdf1) * (pr * pdf2)
   Rearrange to: ((K0 * pr) * pdf1) * pdf2 *)
rewrite -mulrA (mulrCA (normal_pdf _ _ _)) !mulrA.
rewrite (normal_pdf_times_chain _ _ _ _
           phase2_step0_sigma_neq0 phase2_W12_neq0).
by rewrite !mulrA.
Qed.

(* Simplify sigma^2 from step 1 *)
Lemma phase2_step1_sigma2 :
  (gaussian_prod_sigma sigma0 W12) ^+ 2 =
  sigma0 ^+ 2 * W12 ^+ 2 / (sigma0 ^+ 2 + W12 ^+ 2).
Proof.
exact: gaussian_prod_sigma_sqr phase2_step0_sigma_neq0 phase2_W12_neq0.
Qed.

Lemma phase2_step1_sigma_neq0 :
  gaussian_prod_sigma sigma0 W12 != 0.
Proof.
exact: gaussian_prod_sigma_neq0 phase2_step0_sigma_neq0 phase2_W12_neq0.
Qed.

(* Step 2: Combine result with scalar23 *)

(* S23 = sqrt(sqrtr(9/73)^2 + (1/2)^2) = sqrt(109/292) *)
Lemma phase2_S23 :
  sqrtr (9%:R / 73%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2 = 109%:R / 292%:R.
Proof.
rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
by field.
Qed.

(* Rewrite scalar23's normal_fun as a function of s.
   center = 1017/1110, width = sqrt(109/292) * 730/1110. *)
Lemma phase2_scalar23_fun (s : R) :
  normal_fun ((1134%:R - 540%:R * s) / 365%:R)
             (sqrtr (109%:R / 292%:R))
             (9%:R / 2%:R - 3%:R * s) =
  normal_fun (1017%:R / 1110%:R)
             (sqrtr (109%:R / 292%:R) * 73%:R / 111%:R) s.
Proof.
set S23 := sqrtr _.
have hS : S23 != (0 : R)
  := sqrtr_pnat_div_neq0 (a := 109) (b := 292) isT isT.
suff heq : ((9%:R / 2%:R - 3%:R * s) -
             (1134%:R - 540%:R * s) / 365%:R) ^+ 2 /
            (S23 ^+ 2 *+ 2) =
            (s - 1017%:R / 1110%:R) ^+ 2 /
            ((S23 * 73%:R / 111%:R) ^+ 2 *+ 2).
  rewrite /normal_fun; congr (expR _).
  by rewrite !mulNr; congr (- _).
rewrite -(mulr_natr (S23 ^+ 2) 2)
        -(mulr_natr ((S23 * 73%:R / 111%:R) ^+ 2) 2).
rewrite !exprMn exprVn.
by field; rewrite hS.
Qed.

(* Width for step 2: W23 = sqrt(109/292) * 73/111 *)
Let W23 : R := sqrtr (109%:R / 292%:R) * 73%:R / 111%:R.

Lemma phase2_W23_neq0 : W23 != 0.
Proof.
apply: lt0r_neq0.
rewrite /W23.
apply: divr_gt0; last by rewrite ltr0n.
apply: mulr_gt0; last by rewrite ltr0n.
rewrite sqrtr_gt0.
by apply: divr_gt0; rewrite ?ltr0n.
Qed.

(* scalar23 = peak_ratio * normal_pdf *)
Lemma phase2_scalar23E (s : R) :
  gaussian_prod_scalar ((1134%:R - 540%:R * s) / 365%:R)
                       (9%:R / 2%:R - 3%:R * s)
                       (sqrtr (9%:R / 73%:R)) (2%:R^-1) =
  normal_peak (sqrtr (109%:R / 292%:R)) /
  normal_peak W23 *
  normal_pdf (1017%:R / 1110%:R) W23 s.
Proof.
rewrite /gaussian_prod_scalar phase2_S23 /W23 phase2_scalar23_fun -/W23.
rewrite (normal_pdfE _ phase2_W23_neq0).
have hpeak : normal_peak W23 != 0.
  by apply: lt0r_neq0; exact: (normal_peak_gt0 phase2_W23_neq0).
by rewrite mulrA divfK.
Qed.

(* Accumulated sigma from step 1 *)
Let sigma1 : R := gaussian_prod_sigma sigma0 W12.

(* Step 2 combination *)
Lemma phase2_step2 (s : R) :
  forall K1 : R,
  let mu1 := gaussian_prod_mu (90%:R / 73%:R) (253%:R / 190%:R)
               sigma0 W12 in
  K1 * normal_pdf mu1 sigma1 s *
  gaussian_prod_scalar ((1134%:R - 540%:R * s) / 365%:R)
                       (9%:R / 2%:R - 3%:R * s)
                       (sqrtr (9%:R / 73%:R)) (2%:R^-1) =
  K1 * (normal_peak (sqrtr (109%:R / 292%:R)) / normal_peak W23) *
  gaussian_prod_scalar mu1 (1017%:R / 1110%:R) sigma1 W23 *
  normal_pdf (gaussian_prod_mu mu1 (1017%:R / 1110%:R) sigma1 W23)
             (gaussian_prod_sigma sigma1 W23) s.
Proof.
move=> K1.
rewrite /= phase2_scalar23E.
(* Rearrange: K1 * pdf(mu1,sigma1,s) * (pr * pdf(c23,W23,s))
     = (K1 * pr) * pdf(mu1,sigma1,s) * pdf(c23,W23,s) *)
rewrite -mulrA (mulrCA (normal_pdf _ _ _)) !mulrA.
rewrite (normal_pdf_times_chain _ _ _ _
           phase2_step1_sigma_neq0 phase2_W23_neq0).
by rewrite !mulrA.
Qed.

Lemma phase2_step2_sigma_neq0 :
  gaussian_prod_sigma sigma1 W23 != 0.
Proof.
exact: gaussian_prod_sigma_neq0 phase2_step1_sigma_neq0 phase2_W23_neq0.
Qed.

(* Step 3: Combine result with scalar34 *)

(* S34 = sqrt(sqrtr(9/109)^2 + (1/2)^2) = sqrt(145/436) *)
Lemma phase2_S34 :
  sqrtr (9%:R / 109%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2 = 145%:R / 436%:R.
Proof.
rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
by field.
Qed.

(* Rewrite scalar34's normal_fun as a function of s.
   center = 287/220, width = sqrt(145/436) * 109/220. *)
Lemma phase2_scalar34_fun (s : R) :
  normal_fun ((1944%:R - 1080%:R * s) / 545%:R)
             (sqrtr (145%:R / 436%:R))
             (31%:R / 5%:R - 4%:R * s) =
  normal_fun (287%:R / 220%:R)
             (sqrtr (145%:R / 436%:R) * 109%:R / 220%:R) s.
Proof.
set S34 := sqrtr _.
have hS : S34 != (0 : R)
  := sqrtr_pnat_div_neq0 (a := 145) (b := 436) isT isT.
suff heq : ((31%:R / 5%:R - 4%:R * s) -
             (1944%:R - 1080%:R * s) / 545%:R) ^+ 2 /
            (S34 ^+ 2 *+ 2) =
            (s - 287%:R / 220%:R) ^+ 2 /
            ((S34 * 109%:R / 220%:R) ^+ 2 *+ 2).
  rewrite /normal_fun; congr (expR _).
  by rewrite !mulNr; congr (- _).
rewrite -(mulr_natr (S34 ^+ 2) 2)
        -(mulr_natr ((S34 * 109%:R / 220%:R) ^+ 2) 2).
rewrite !exprMn exprVn.
by field; rewrite hS.
Qed.

(* Width for step 3: W34 = sqrt(145/436) * 109/220 *)
Let W34 : R := sqrtr (145%:R / 436%:R) * 109%:R / 220%:R.

Lemma phase2_W34_neq0 : W34 != 0.
Proof.
apply: lt0r_neq0.
rewrite /W34.
apply: divr_gt0; last by rewrite ltr0n.
apply: mulr_gt0; last by rewrite ltr0n.
rewrite sqrtr_gt0.
by apply: divr_gt0; rewrite ?ltr0n.
Qed.

(* scalar34 = peak_ratio * normal_pdf *)
Lemma phase2_scalar34E (s : R) :
  gaussian_prod_scalar ((1944%:R - 1080%:R * s) / 545%:R)
                       (31%:R / 5%:R - 4%:R * s)
                       (sqrtr (9%:R / 109%:R)) (2%:R^-1) =
  normal_peak (sqrtr (145%:R / 436%:R)) /
  normal_peak W34 *
  normal_pdf (287%:R / 220%:R) W34 s.
Proof.
rewrite /gaussian_prod_scalar phase2_S34 /W34 phase2_scalar34_fun -/W34.
rewrite (normal_pdfE _ phase2_W34_neq0).
have hpeak : normal_peak W34 != 0.
  by apply: lt0r_neq0; exact: (normal_peak_gt0 phase2_W34_neq0).
by rewrite mulrA divfK.
Qed.

(* Accumulated sigma from step 2 *)
Let sigma2 : R := gaussian_prod_sigma sigma1 W23.

(* Step 3 combination *)
Lemma phase2_step3 (s : R) :
  forall K2 : R,
  let mu2 := gaussian_prod_mu
               (gaussian_prod_mu (90%:R / 73%:R) (253%:R / 190%:R)
                  sigma0 W12)
               (1017%:R / 1110%:R) sigma1 W23 in
  K2 * normal_pdf mu2 sigma2 s *
  gaussian_prod_scalar ((1944%:R - 1080%:R * s) / 545%:R)
                       (31%:R / 5%:R - 4%:R * s)
                       (sqrtr (9%:R / 109%:R)) (2%:R^-1) =
  K2 * (normal_peak (sqrtr (145%:R / 436%:R)) / normal_peak W34) *
  gaussian_prod_scalar mu2 (287%:R / 220%:R) sigma2 W34 *
  normal_pdf (gaussian_prod_mu mu2 (287%:R / 220%:R) sigma2 W34)
             (gaussian_prod_sigma sigma2 W34) s.
Proof.
move=> K2.
rewrite /= phase2_scalar34E.
(* Rearrange: K2 * pdf(mu2,sigma2,s) * (pr * pdf(c34,W34,s))
     = (K2 * pr) * pdf(mu2,sigma2,s) * pdf(c34,W34,s) *)
rewrite -mulrA (mulrCA (normal_pdf _ _ _)) !mulrA.
rewrite (normal_pdf_times_chain _ _ _ _
           phase2_step2_sigma_neq0 phase2_W34_neq0).
by rewrite !mulrA.
Qed.

Lemma phase2_step3_sigma_neq0 :
  gaussian_prod_sigma sigma2 W34 != 0.
Proof.
exact: gaussian_prod_sigma_neq0 phase2_step2_sigma_neq0 phase2_W34_neq0.
Qed.

(* Step 4: Combine result with scalar45 *)

(* S45 = sqrt(sqrtr(9/145)^2 + (1/2)^2) = sqrt(181/580) *)
Lemma phase2_S45 :
  sqrtr (9%:R / 145%:R) ^+ 2 + (2%:R^-1 : R) ^+ 2 = 181%:R / 580%:R.
Proof.
rewrite sqr_sqrtr; last by apply: divr_ge0; rewrite ?ler0n.
by field.
Qed.

(* Rewrite scalar45's normal_fun as a function of s.
   center = 548/365, width = sqrt(181/580) * 145/365. *)
Lemma phase2_scalar45_fun (s : R) :
  normal_fun ((612%:R - 360%:R * s) / 145%:R)
             (sqrtr (181%:R / 580%:R))
             (8%:R - 5%:R * s) =
  normal_fun (548%:R / 365%:R)
             (sqrtr (181%:R / 580%:R) * 29%:R / 73%:R) s.
Proof.
set S45 := sqrtr _.
have hS : S45 != (0 : R)
  := sqrtr_pnat_div_neq0 (a := 181) (b := 580) isT isT.
suff heq : ((8%:R - 5%:R * s) -
             (612%:R - 360%:R * s) / 145%:R) ^+ 2 /
            (S45 ^+ 2 *+ 2) =
            (s - 548%:R / 365%:R) ^+ 2 /
            ((S45 * 29%:R / 73%:R) ^+ 2 *+ 2).
  rewrite /normal_fun; congr (expR _).
  by rewrite !mulNr; congr (- _).
rewrite -(mulr_natr (S45 ^+ 2) 2)
        -(mulr_natr ((S45 * 29%:R / 73%:R) ^+ 2) 2).
rewrite !exprMn exprVn.
by field; rewrite hS.
Qed.

(* Width for step 4: W45 = sqrt(181/580) * 29/73 *)
Let W45 : R := sqrtr (181%:R / 580%:R) * 29%:R / 73%:R.

Lemma phase2_W45_neq0 : W45 != 0.
Proof.
apply: lt0r_neq0.
rewrite /W45.
apply: divr_gt0; last by rewrite ltr0n.
apply: mulr_gt0; last by rewrite ltr0n.
rewrite sqrtr_gt0.
by apply: divr_gt0; rewrite ?ltr0n.
Qed.

(* scalar45 = peak_ratio * normal_pdf *)
Lemma phase2_scalar45E (s : R) :
  gaussian_prod_scalar ((612%:R - 360%:R * s) / 145%:R)
                       (8%:R - 5%:R * s)
                       (sqrtr (9%:R / 145%:R)) (2%:R^-1) =
  normal_peak (sqrtr (181%:R / 580%:R)) /
  normal_peak W45 *
  normal_pdf (548%:R / 365%:R) W45 s.
Proof.
rewrite /gaussian_prod_scalar phase2_S45 /W45 phase2_scalar45_fun -/W45.
rewrite (normal_pdfE _ phase2_W45_neq0).
have hpeak : normal_peak W45 != 0.
  by apply: lt0r_neq0; exact: (normal_peak_gt0 phase2_W45_neq0).
by rewrite mulrA divfK.
Qed.

(* Accumulated sigma from step 3 *)
Let sigma3 : R := gaussian_prod_sigma sigma2 W34.

(* Step 4 combination *)
Lemma phase2_step4 (s : R) :
  forall K3 : R,
  let mu3 := gaussian_prod_mu
               (gaussian_prod_mu
                 (gaussian_prod_mu (90%:R / 73%:R) (253%:R / 190%:R)
                    sigma0 W12)
                 (1017%:R / 1110%:R) sigma1 W23)
               (287%:R / 220%:R) sigma2 W34 in
  K3 * normal_pdf mu3 sigma3 s *
  gaussian_prod_scalar ((612%:R - 360%:R * s) / 145%:R)
                       (8%:R - 5%:R * s)
                       (sqrtr (9%:R / 145%:R)) (2%:R^-1) =
  K3 * (normal_peak (sqrtr (181%:R / 580%:R)) / normal_peak W45) *
  gaussian_prod_scalar mu3 (548%:R / 365%:R) sigma3 W45 *
  normal_pdf (gaussian_prod_mu mu3 (548%:R / 365%:R) sigma3 W45)
             (gaussian_prod_sigma sigma3 W45) s.
Proof.
move=> K3.
rewrite /= phase2_scalar45E.
(* Rearrange: K3 * pdf(mu3,sigma3,s) * (pr * pdf(c45,W45,s))
     = (K3 * pr) * pdf(mu3,sigma3,s) * pdf(c45,W45,s) *)
rewrite -mulrA (mulrCA (normal_pdf _ _ _)) !mulrA.
rewrite (normal_pdf_times_chain _ _ _ _
           phase2_step3_sigma_neq0 phase2_W45_neq0).
by rewrite !mulrA.
Qed.

Lemma phase2_step4_sigma_neq0 :
  gaussian_prod_sigma sigma3 W45 != 0.
Proof.
exact: gaussian_prod_sigma_neq0 phase2_step3_sigma_neq0 phase2_W45_neq0.
Qed.

(* Phase 2: Combined result chaining all 5 steps                         *)

(* Intermediate means for Phase 2 (accumulated across steps) *)
Let mu0_s : R := 90%:R / 73%:R.
Let mu1_s : R := gaussian_prod_mu mu0_s (253%:R / 190%:R) sigma0 W12.
Let mu2_s : R := gaussian_prod_mu mu1_s (1017%:R / 1110%:R) sigma1 W23.
Let mu3_s : R := gaussian_prod_mu mu2_s (287%:R / 220%:R) sigma2 W34.

(* Public definitions for Phase 2 outputs *)
Definition phase2_final_mu : R :=
  gaussian_prod_mu mu3_s (548%:R / 365%:R) sigma3 W45.

Definition phase2_final_sigma : R :=
  gaussian_prod_sigma sigma3 W45.

Definition phase2_const : R :=
  gaussian_prod_scalar 0 (5%:R / 2%:R) 3%:R (sqrtr (37%:R / 4%:R)) *
  (normal_peak (sqrtr (73%:R / 148%:R)) / normal_peak W12) *
  gaussian_prod_scalar mu0_s (253%:R / 190%:R) sigma0 W12 *
  (normal_peak (sqrtr (109%:R / 292%:R)) / normal_peak W23) *
  gaussian_prod_scalar mu1_s (1017%:R / 1110%:R) sigma1 W23 *
  (normal_peak (sqrtr (145%:R / 436%:R)) / normal_peak W34) *
  gaussian_prod_scalar mu2_s (287%:R / 220%:R) sigma2 W34 *
  (normal_peak (sqrtr (181%:R / 580%:R)) / normal_peak W45) *
  gaussian_prod_scalar mu3_s (548%:R / 365%:R) sigma3 W45.

Lemma phase2_final_sigma_neq0 : phase2_final_sigma != 0.
Proof. exact: phase2_step4_sigma_neq0. Qed.

Lemma phase2_const_gt0 : 0 < phase2_const.
Proof.
rewrite /phase2_const.
have sqrtr37_neq0 := sqrtr_pnat_div_neq0 (a := 37) (b := 4) isT isT.
have sqrtr73_neq0 := sqrtr_pnat_div_neq0 (a := 73) (b := 148) isT isT.
have sqrtr109_neq0 := sqrtr_pnat_div_neq0 (a := 109) (b := 292) isT isT.
have sqrtr145_neq0 := sqrtr_pnat_div_neq0 (a := 145) (b := 436) isT isT.
have sqrtr181_neq0 := sqrtr_pnat_div_neq0 (a := 181) (b := 580) isT isT.
(* Factor 9: gps(mu3, 548/365, sigma3, W45) *)
apply: mulr_gt0; last first.
  exact: gaussian_prod_scalar_gt0 phase2_step3_sigma_neq0 phase2_W45_neq0.
(* Factor 8: peak(sqrt(181/580)) / peak(W45) *)
apply: mulr_gt0; last first.
  by apply: divr_gt0;
    [exact: normal_peak_gt0 sqrtr181_neq0|
     exact: normal_peak_gt0 phase2_W45_neq0].
(* Factor 7: gps(mu2, 287/220, sigma2, W34) *)
apply: mulr_gt0; last first.
  exact: gaussian_prod_scalar_gt0
    phase2_step2_sigma_neq0 phase2_W34_neq0.
(* Factor 6: peak(sqrt(145/436)) / peak(W34) *)
apply: mulr_gt0; last first.
  by apply: divr_gt0;
    [exact: normal_peak_gt0 sqrtr145_neq0|
     exact: normal_peak_gt0 phase2_W34_neq0].
(* Factor 5: gps(mu1, 1017/1110, sigma1, W23) *)
apply: mulr_gt0; last first.
  exact: gaussian_prod_scalar_gt0
    phase2_step1_sigma_neq0 phase2_W23_neq0.
(* Factor 4: peak(sqrt(109/292)) / peak(W23) *)
apply: mulr_gt0; last first.
  by apply: divr_gt0;
    [exact: normal_peak_gt0 sqrtr109_neq0|
     exact: normal_peak_gt0 phase2_W23_neq0].
(* Factor 3: gps(mu0, 253/190, sigma0, W12) *)
apply: mulr_gt0; last first.
  exact: gaussian_prod_scalar_gt0 phase2_step0_sigma_neq0 phase2_W12_neq0.
(* Factor 2: peak(sqrt(73/148)) / peak(W12) *)
apply: mulr_gt0; last first.
  by apply: divr_gt0;
    [exact: normal_peak_gt0 sqrtr73_neq0|
     exact: normal_peak_gt0 phase2_W12_neq0].
(* Factor 1: gps(0, 5/2, 3, sqrt(37/4)) *)
exact: gaussian_prod_scalar_gt0 three_neq0 sqrtr37_neq0.
Qed.

(* The combined Phase 2 result: scalar_of_s(s) * N(0,3,s) = C * N(mu, sigma, s).
   This chains all 5 Phase 2 combination steps. *)
Lemma phase2_combine5 (s : R) :
  normal_pdf 0 3%:R s *
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
  gaussian_prod_scalar ((612%:R - 360%:R * s) / 145%:R)
                       (8%:R - 5%:R * s)
                       (sqrtr (9%:R / 145%:R)) (2%:R^-1) =
  phase2_const * normal_pdf phase2_final_mu phase2_final_sigma s.
Proof.
(* Step 0: N(0,3,s) * scalar01 = K0 * N(90/73, sigma0, s) *)
rewrite phase2_step0.
(* After step 0, goal is left-associated:
   ((((K0 * N0) * G2) * G3) * G4) * G5 = ...
   phase2_step1 rewrites (K0 * N0) * G2 directly. *)
rewrite (phase2_step1 s).
(* After step 1: ((((K1 * N1) * G3) * G4) * G5) = ... *)
rewrite (phase2_step2 s).
(* After step 2: (((K2 * N2) * G4) * G5) = ... *)
rewrite (phase2_step3 s).
(* After step 3: ((K3 * N3) * G5) = ... *)
rewrite (phase2_step4 s).
(* Now LHS = K4 * N4, RHS = phase2_const * N(final_mu, final_sigma, s) *)
rewrite /phase2_const /phase2_final_mu /phase2_final_sigma.
by rewrite !mulrA.
Qed.

(* Bridge: obs-style products to centered normal_pdf form                 *)

(* Key identity for converting obs(s,b) to the form used by phase1:
   normal_pdf(s*k+b, sigma, y) = normal_pdf(y-k*s, sigma, b).
   This combines symmetry (x-m)^2 = (m-x)^2 with the algebraic
   identity y - (s*k+b) = -(b - (y-k*s)).

   Note: uses s*k (not k*s) to match the obs definition order. *)
Lemma normal_pdf_recenter (y s k sigma b : R) (hs : sigma != 0) :
  normal_pdf (s * k + b) sigma y = normal_pdf (y - k * s) sigma b.
Proof.
rewrite !(normal_pdfE _ hs); congr (_ * _).
rewrite /normal_fun; congr (expR _).
congr (- _ / _).
suff -> : (y - (s * k + b)) = - (b - (y - k * s)) by rewrite sqrrN.
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

End bayesian_phase2_slope.

End normal_density_algebra.
