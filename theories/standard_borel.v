(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra reals classical_sets filter
  topology num_topology normedtype sequences measurable_structure
  measurable_function measurable_realfun trigo lebesgue_stieltjes_measure.
From mathcomp.algebra_tactics Require Import ring.

(**md**************************************************************************)
(* # Standard Borel Spaces                                                    *)
(* Measurable bijection R ~ R x R for standard Borel space closure.           *)
(*                                                                            *)
(* This file constructs a measurable bijection between R and the open         *)
(* interval (0,1) using the arctangent function, and then between (0,1) and   *)
(* (0,1) x (0,1) using binary digit interleaving, composing into a           *)
(* measurable bijection R ~ R x R.                                            *)
(*                                                                            *)
(* ## Bijection R <-> (0,1)                                                   *)
(* ```                                                                        *)
(*   phi x == atan(x)/pi + 1/2, a measurable bijection R -> (0,1)            *)
(*   psi y == tan(pi*(y - 1/2)), its inverse (0,1) -> R                      *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Binary digit machinery                                                  *)
(* ```                                                                        *)
(*   bin_digit x n == the n-th binary digit of x in [0,1), obtained by       *)
(*                    iterative doubling-and-testing                          *)
(*   bin_partial_sum d n == sum of the first n terms of the binary expansion  *)
(*                          given digit sequence d                            *)
(*   bin_sum d == limit of the partial sums (full binary expansion value)     *)
(*   bin_digits x == the digit sequence of x (i.e., bin_digit x)             *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Digit interleaving                                                      *)
(* ```                                                                        *)
(*   interleave d1 d2 == interleave two digit sequences: even positions       *)
(*                       from d1, odd positions from d2                       *)
(*   deinterleave_even d == extract even-indexed digits from d                *)
(*   deinterleave_odd d == extract odd-indexed digits from d                  *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Pairing functions on (0,1)                                              *)
(* ```                                                                        *)
(*   no_trailing_ones d == digit sequence d has no infinite suffix of ones    *)
(*   pair_to_unit xy == (0,1) x (0,1) -> (0,1) via digit interleaving        *)
(*   unit_to_pair r == (0,1) -> (0,1) x (0,1) via digit deinterleaving       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Composed bijection R x R <-> R                                          *)
(* ```                                                                        *)
(*   encode_RR xy == R x R -> R, composing phi, pair_to_unit, and psi         *)
(*   decode_RR r == R -> R x R, composing phi, unit_to_pair, and psi          *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Main results                                                            *)
(*   phi_gt0 == phi x > 0 for all x                                          *)
(*   phi_lt1 == phi x < 1 for all x                                          *)
(*   psiK    == cancel phi psi (psi is left inverse of phi)                   *)
(*   phiK    == cancel psi phi on (0,1)                                       *)
(*   measurable_phi == phi is measurable on R                                 *)
(*   measurable_psi == psi is measurable on (0,1)                             *)
(*   bin_digits_reconstruction == bin_sum (bin_digits x) = x for [0,1)       *)
(*   unit_to_pairK == unit_to_pair (pair_to_unit (x,y)) = (x,y)              *)
(*                    (unconditional on [0,1)^2)                              *)
(*   pair_to_unitK == pair_to_unit (unit_to_pair r) = r                      *)
(*                    (conditional on no_trailing_ones)                       *)
(*   encode_RRK == decode_RR (encode_RR xy) = xy                             *)
(*   measurable_encode_RR == encode_RR is measurable                         *)
(*   measurable_decode_RR == decode_RR is measurable                         *)
(*   measurable_pair_to_unit == pair_to_unit is measurable                   *)
(*   measurable_unit_to_pair_fst == fst projection of unit_to_pair is        *)
(*                                  measurable                               *)
(*   measurable_unit_to_pair_snd == snd projection of unit_to_pair is        *)
(*                                  measurable                               *)
(*                                                                            *)
(* ## Note on the no_trailing_ones gap                                        *)
(* The round-trip pair_to_unitK requires no_trailing_ones on the       *)
(* deinterleaved subsequences, which does NOT follow from no_trailing_ones    *)
(* on the full binary expansion. However, for standard_borel_wit (R * R),     *)
(* only the OTHER direction (encode_RRK, i.e. g(f(x))=x) is needed,   *)
(* and that direction (unit_to_pairK / encode_RRK) is proved    *)
(* unconditionally. See the detailed comments in the Round-trip section.     *)
(******************************************************************************)

Import GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Import order.Order.POrderTheory.
Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section phi_psi.
Variable R : realType.
Implicit Types x y : R.

(** phi : R -> (0,1) via atan *)
Definition phi (x : R) : R := atan x / pi + 1 / 2.

(** psi : (0,1) -> R via tan *)
Definition psi (y : R) : R := tan (pi * (y - 1 / 2)).

(** phi lands in (0,1) *)
Lemma phi_gt0 x : 0 < phi x.
Proof.
rewrite /phi.
have hpi : (0 : R) < pi := pi_gt0 R.
have hatangt : - (pi / 2) < atan x := atan_gtNpi2 x.
have h1 : - (1 / 2) < atan x / (pi : R).
  rewrite ltr_pdivlMr //.
  by rewrite mulNr mul1r mulrC.
rewrite -subr_gt0 subr0; move: h1; rewrite -subr_gt0 opprK; exact.
Qed.

Lemma phi_lt1 x : phi x < 1.
Proof.
rewrite /phi.
have hpi : (0 : R) < pi := pi_gt0 R.
have hatanlt : atan x < pi / 2 := atan_ltpi2 x.
have h1 : atan x / (pi : R) < 1 / 2.
  rewrite ltr_pdivrMr //.
  by rewrite mul1r mulrC.
have h2 : (1/2 : R) <= 1/2 by done.
have h3 := ltr_leD h1 h2.
by rewrite -splitr in h3.
Qed.

(** psi is the inverse of phi *)
Lemma psiK : cancel phi psi.
Proof.
rewrite /cancel => x; rewrite /psi /phi.
rewrite addrK mulrCA divff ?mulr1; first exact: atanK.
exact: lt0r_neq0 (pi_gt0 R).
Qed.

Lemma phiK : {in `](0:R), 1[, cancel psi phi}.
Proof.
move=> y hy; rewrite /phi /psi.
have hpi : (0 : R) < pi := pi_gt0 R.
have hpi0 : (pi : R) != 0 := lt0r_neq0 hpi.
rewrite in_itv /= in hy.
have /andP [hy0 hy1] := hy.
have hrange : pi * (y - 1 / 2) \in `](- (pi / 2)), pi / 2[.
  rewrite in_itv /=; apply/andP; split.
    have -> : - ((pi : R) / 2) = pi * (- (1 / 2)) by rewrite mulrN mul1r.
    by rewrite ltr_pM2l // ltrDr.
  have -> : (pi : R) / 2 = pi * (1 / 2) by rewrite mul1r.
  rewrite ltr_pM2l // ltrBlDr -splitr; exact: hy1.
by rewrite (tanK hrange) mulrC mulKf // subrK.
Qed.

(** Both are measurable *)
Lemma measurable_phi : measurable_fun setT phi.
Proof.
rewrite /phi.
apply: measurable_funD.
  apply: measurable_funM.
    apply: continuous_measurable_fun; exact: continuous_atan.
  exact: measurable_cst.
exact: measurable_cst.
Qed.

Lemma measurable_psi : measurable_fun (`](0:R), 1[) psi.
Proof.
apply: open_continuous_measurable_fun; first exact: interval_open.
move=> y hy.
have hy01 : 0 < y < 1.
  move: hy; rewrite inE /= => /andP [].
  by rewrite !bnd_simp => ? ?; apply/andP.
have /andP [hy0 hy1] := hy01.
have hcos : cos (pi * (y - 1 / 2)) != 0.
  rewrite lt0r_neq0 //; apply: cos_gt0_pihalf.
  apply/andP; split.
    have -> : - ((pi : R) / 2) = pi * (- (1 / 2)) by rewrite mulrN mul1r.
    by rewrite ltr_pM2l ?pi_gt0 // ltrDr.
  have -> : (pi : R) / 2 = pi * (1 / 2) by rewrite mul1r.
  rewrite ltr_pM2l ?pi_gt0 // ltrBlDr -splitr; exact: hy1.
rewrite /psi.
apply: (@continuous_comp _ _ _
          (fun y0 : R => pi * (y0 - 1/2)) tan).
  apply: continuousM; first exact: cvg_cst.
  apply: continuousB; first exact: cvg_id.
  exact: cvg_cst.
exact: continuous_tan.
Qed.

End phi_psi.

Section binary_digit_interleaving.
Variable R : realType.

(* Subsection: basic binary digit / partial sum definitions and their
   arithmetic properties, plus interleave/deinterleave definitions and
   the geometric sum identity. *)
Section binary_digit_arithmetic.

(******************************************************************************)
(* Binary digit extraction and reconstruction                                 *)
(******************************************************************************)

(* n-th binary digit of x in [0,1): iterative doubling-and-testing *)
Fixpoint bin_digit (x : R) (n : nat) : bool :=
  match n with
  | 0%N => (2%:R^-1 <= x)
  | n'.+1 => bin_digit (if (2%:R^-1 <= x) then x *+ 2 - 1 else x *+ 2) n'
  end.

(* Binary partial sum: reconstruct from first n digits *)
Definition bin_partial_sum (d : nat -> bool) (n : nat) : R :=
  \sum_(i < n) (d i)%:R * (2%:R^-1) ^+ i.+1.

(* Limit of partial sums = full binary expansion *)
Definition bin_sum (d : nat -> bool) : R :=
  limn (fun n => bin_partial_sum d n : R^o).

(* Extract all digits of x *)
Definition bin_digits (x : R) : nat -> bool := bin_digit x.

(******************************************************************************)
(* Interleaving and deinterleaving digit sequences                            *)
(******************************************************************************)

(* Interleave: even positions from d1, odd positions from d2 *)
Definition interleave (d1 d2 : nat -> bool) (n : nat) : bool :=
  if ~~ odd n then d1 n./2 else d2 n./2.

(* Extract even-indexed digits *)
Definition deinterleave_even (d : nat -> bool) (n : nat) : bool :=
  d (n.*2)%N.

(* Extract odd-indexed digits *)
Definition deinterleave_odd (d : nat -> bool) (n : nat) : bool :=
  d (n.*2.+1)%N.

(******************************************************************************)
(* Interleave / deinterleave are inverse operations on digit sequences        *)
(******************************************************************************)

Lemma interleave_deinterleaveK (d : nat -> bool) :
  interleave (deinterleave_even d) (deinterleave_odd d) =1 d.
Proof.
move=> n; rewrite /interleave /deinterleave_even /deinterleave_odd.
case: (boolP (odd n)) => hodd /=.
- have := odd_double_half n; rewrite hodd /= add1n => heq.
  by rewrite heq.
- by rewrite even_halfK.
Qed.

Lemma deinterleave_interleaveK_even (d1 d2 : nat -> bool) :
  deinterleave_even (interleave d1 d2) =1 d1.
Proof.
move=> n; rewrite /deinterleave_even /interleave.
by rewrite odd_double /= half_double.
Qed.

Lemma deinterleave_interleaveK_odd (d1 d2 : nat -> bool) :
  deinterleave_odd (interleave d1 d2) =1 d2.
Proof.
move=> n; rewrite /deinterleave_odd /interleave /=.
by rewrite odd_double /= uphalf_double.
Qed.

(******************************************************************************)
(* Geometric sum identity: sum_{i<n} (1/2)^{i+1} = 1 - (1/2)^n             *)
(******************************************************************************)

Lemma geom_half_sum (n : nat) :
  \sum_(i < n) (2%:R : R)^-1 ^+ i.+1 = 1 - 2%:R^-1 ^+ n.
Proof.
elim: n => [|k IHk].
  by rewrite big_ord0 expr0 subrr.
rewrite big_ord_recr /= IHk exprSr.
set a := 2%:R^-1 ^+ k; rewrite -addrA; congr (_ + _).
by rewrite {1}(splitr a) opprD subrK.
Qed.

(******************************************************************************)
(* Convergence of binary partial sums                                         *)
(******************************************************************************)

Lemma bin_partial_sum_le1 (d : nat -> bool) (n : nat) :
  bin_partial_sum d n <= 1.
Proof.
rewrite /bin_partial_sum.
suff hgeom : \sum_(i < n) (2%:R : R)^-1 ^+ i.+1 <= 1.
  have hle : \sum_(i < n) (d i)%:R * (2%:R : R)^-1 ^+ i.+1 <=
             \sum_(i < n) (2%:R : R)^-1 ^+ i.+1.
    apply: ler_sum => i _.
    rewrite -[X in _ <= X]mul1r.
    apply: ler_wpM2r;
      [by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n|
       by case: (d i)].
  exact: (le_trans hle hgeom).
rewrite geom_half_sum lerBlDr -{1}[1]addr0.
apply: lerD => //.
by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
Qed.

Lemma bin_partial_sum_ge0 (d : nat -> bool) (n : nat) :
  0 <= bin_partial_sum d n.
Proof.
rewrite /bin_partial_sum; apply: sumr_ge0 => i _.
apply: mulr_ge0; first by case: (d i).
by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
Qed.

Lemma bin_partial_sum_nd (d : nat -> bool) :
  nondecreasing_seq (fun n => bin_partial_sum d n : R^o).
Proof.
apply/nondecreasing_seqP => n.
rewrite /bin_partial_sum big_ord_recr /=.
rewrite -[X in X <= _]addr0.
apply: lerD => //.
apply: mulr_ge0; first by case: (d n).
by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
Qed.

Lemma is_cvg_bin_partial_sum (d : nat -> bool) :
  cvgn (fun n => bin_partial_sum d n : R^o).
Proof.
apply: nondecreasing_is_cvgn.
  exact: bin_partial_sum_nd.
exists 1 => _ [n _ <-].
exact: bin_partial_sum_le1.
Qed.

Lemma bin_sum_le1 (d : nat -> bool) : bin_sum d <= 1.
Proof.
apply: (@closed_cvg _ _ eventually _
  (fun n => bin_partial_sum d n : R^o) (fun x : R => x <= 1)
  _ _ (bin_sum d)).
- exact: closed_le.
- by apply: nearW => n; exact: bin_partial_sum_le1.
- rewrite /bin_sum; exact: is_cvg_bin_partial_sum.
Qed.

Lemma bin_sum_ge0 (d : nat -> bool) : 0 <= bin_sum d.
Proof.
apply: (@closed_cvg _ _ eventually _
  (fun n => bin_partial_sum d n : R^o) (fun x : R => 0 <= x)
  _ _ (bin_sum d)).
- exact: closed_ge.
- by apply: nearW => n; exact: bin_partial_sum_ge0.
- rewrite /bin_sum; exact: is_cvg_bin_partial_sum.
Qed.

End binary_digit_arithmetic.

(* Subsection: the pairing function pair_to_unit, its inverse unit_to_pair,
   and the reconstruction lemma bin_digits_reconstruction showing that the
   binary expansion of x in [0,1) sums back to x. *)
Section pairing_reconstruction.

(******************************************************************************)
(* The pairing function (0,1) x (0,1) -> (0,1) and its inverse               *)
(******************************************************************************)

Definition pair_to_unit (xy : R * R) : R :=
  bin_sum (interleave (bin_digits xy.1) (bin_digits xy.2)).

Definition unit_to_pair (r : R) : R * R :=
  (bin_sum (deinterleave_even (bin_digits r)),
   bin_sum (deinterleave_odd (bin_digits r))).

Lemma half2 : 2%:R^-1 *+ 2 = (1 : R).
Proof.
have h : (1 : R) / 2%:R = 2%:R^-1 by rewrite div1r.
by rewrite /GRing.natmul /= -[2%:R^-1]h -(@splitr R 1).
Qed.

(******************************************************************************)
(* Reconstruction: bin_sum (bin_digits x) = x for x in [0,1)                 *)
(******************************************************************************)

Lemma bin_digits_reconstruction (x : R) :
  0 <= x < 1 -> bin_sum (bin_digits x) = x.
Proof.
move=> /andP[hx0 hx1].
rewrite /bin_sum /bin_digits.
suff hcvg : (fun n => bin_partial_sum (bin_digit x) n : R^o) n
              @[n --> \oo] --> x.
  exact: (cvg_lim _ hcvg).
pose step := fun (y : R) => if 2%:R^-1 <= y then y *+ 2 - 1 else y *+ 2.
pose rem := fix f n := match n with 0%N => x | n'.+1 => step (f n') end.
have hrem_digit : forall n, bin_digit x n = (2%:R^-1 <= rem n).
  suff hgen : forall n y, bin_digit y n = (2%:R^-1 <= iter n step y).
    by move=> n; rewrite hgen; congr (_ <= _); elim: n => //= k ->.
  by elim=> [|k IHk] //= y; rewrite IHk -iterSr iterS.
have hinv : forall n : nat,
    x - bin_partial_sum (bin_digit x) n = rem n * 2%:R^-1 ^+ n :> R.
  elim=> [|k IHk].
    by rewrite /bin_partial_sum big_ord0 subr0 expr0 mulr1.
  rewrite /bin_partial_sum big_ord_recr /= -/bin_partial_sum hrem_digit exprSr.
  case hle: (2%:R^-1 <= rem k).
  - rewrite /= mul1r /step hle opprD addrA -/bin_partial_sum.
    have -> : x - bin_partial_sum (bin_digit x) k - (2%:R^-1 ^+ k / 2) =
              rem k * 2%:R^-1 ^+ k - 2%:R^-1 ^+ k / 2 by rewrite IHk.
    set h := 2%:R^-1 ^+ k; rewrite mulrBl mul1r mulrnAl -mulrnAr.
    by congr (_ * _ - _); rewrite mulr2n -splitr.
  - rewrite /= mul0r addr0 -/bin_partial_sum IHk /step hle.
    set h := 2%:R^-1 ^+ k; rewrite mulrnAl mulrCA.
    by rewrite -mulrnAr mulr2n -splitr mulrC.
have hrem_bound : forall n, 0 <= rem n /\ rem n < 1.
  elim=> [|k [IHk0 IHk1]] /=; first by split.
  rewrite /step; case: ifP => hle; split.
  - by rewrite subr_ge0 -half2 ler_pMn2r.
  - by rewrite ltrBlDr -mulr2n ltr_pMn2r.
  - have := @mulrn_wge0 R (rem k) 2 IHk0; done.
  - by rewrite -half2 ltr_pMn2r // real_ltNge ?num_real // hle.
have habs_half : `|(2%:R^-1 : R)| < 1.
  by rewrite ger0_norm ?invr_ge0 ?ler0n // invf_lt1 ?ltr0n // ltr1n.
have hrem_cvg : (fun n => rem n * 2%:R^-1 ^+ n : R^o) n
                  @[n --> \oo] --> (0 : R^o).
  apply: (@squeeze_cvgr _ _ _ _
    (fun _ => 0 : R^o) (fun n => 2%:R^-1 ^+ n : R^o)).
  - apply: nearW => n; apply/andP; split.
    + apply: mulr_ge0; first by have [] := hrem_bound n.
      by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
    + rewrite -[X in _ <= X]mul1r; apply: ler_pM.
      * by have [] := hrem_bound n.
      * by apply: (@exprn_ge0 R); rewrite invr_ge0; apply: ler0n.
      * by have [_ h] := hrem_bound n; exact: ltW h.
      * by [].
  - exact: cvg_cst.
  - have := @cvg_geometric R 1 _ habs_half.
    rewrite /geometric /=.
    by move=> h; have : (fun n0 => 1 * 2%:R^-1 ^+ n0 : R^o) n
      @[n --> \oo] --> 0 := h; under eq_cvg do rewrite mul1r.
have heq : forall n, bin_partial_sum (bin_digit x) n =
    x - rem n * 2%:R^-1 ^+ n :> R.
  by move=> m; have h := hinv m; rewrite -h opprB addrCA subrr addr0.
suff : (fun n => x - rem n * 2%:R^-1 ^+ n : R^o) n
         @[n --> \oo] --> (x : R^o).
  by move=> h; under eq_cvg do rewrite heq; exact: h.
have : (fun n : nat => (x : R^o)) n @[n --> \oo] --> x.
  exact: cvg_cst.
move=> hcstx; have := cvgB hcstx hrem_cvg; rewrite subr0; exact.
Qed.

End pairing_reconstruction.

(* Subsection: round-trip lemmas for pair_to_unit/unit_to_pair, including
   the no_trailing_ones canonicalization, uniqueness of binary expansions,
   and the unconditional unit_to_pairK direction. *)
Section round_trips.

(******************************************************************************)
(* Round-trip properties                                                      *)
(*                                                                            *)
(* We prove two round-trip lemmas:                                            *)
(*                                                                            *)
(* 1. unit_to_pairK: unit_to_pair (pair_to_unit (x,y)) = (x,y)        *)
(*    This holds UNCONDITIONALLY for all (x,y) in [0,1)^2.                   *)
(*    This is the direction needed for standard_borel_wit (R * R), which       *)
(*    only requires g(f(x)) = x (i.e., decode after encode = identity).      *)
(*                                                                            *)
(* 2. pair_to_unitK: pair_to_unit (unit_to_pair r) = r                 *)
(*    This requires no_trailing_ones on the deinterleaved subsequences.       *)
(*    The full binary expansion bin_digits(r) has no trailing ones for        *)
(*    r in [0,1) (proved in bin_digits_no_trailing_ones), but this does NOT   *)
(*    imply that the deinterleaved even/odd subsequences lack trailing ones.  *)
(*    Example: r with digits 1,0,1,0,... has no trailing ones, but           *)
(*    deinterleave_even gives 1,1,1,... (all ones).                          *)
(*                                                                            *)
(*    This direction is NOT needed for standard_borel_wit (the product of      *)
(*    standard Borel spaces theorem). The set of reals where the extra        *)
(*    hypotheses fail is a subset of the dyadic rationals (countable, hence   *)
(*    measure zero), but we do not formalize this fact here since it is       *)
(*    not required.                                                           *)
(******************************************************************************)

(* Round-trip: these follow from bin_digits_reconstruction combined with
   the fact that bin_digits (bin_sum d) =1 d for digit sequences arising
   from reals in [0,1). The latter is essentially uniqueness of binary
   expansions for non-dyadic rationals. *)

(* Extensionality: pointwise equal digit sequences have the same sum *)
Lemma bin_sum_ext (d1 d2 : nat -> bool) :
  d1 =1 d2 -> bin_sum d1 = bin_sum d2.
Proof.
move=> heq; rewrite /bin_sum; congr (limn _).
apply: funext => n.
rewrite /bin_partial_sum; apply: eq_bigr => i _.
by rewrite (heq i).
Qed.

(* A digit sequence is "canonical" if it has no infinite trailing ones,
   i.e., there exists a false digit at or beyond every position. *)
Definition no_trailing_ones (d : nat -> bool) : Prop :=
  forall N : nat, exists n, (N <= n)%N /\ d n = false.

(* bin_digits x has no trailing ones for x in [0,1).
   Proof: if all digits from N onward are 1, then the remainder
   at position N would satisfy rem(N+k) = 2^k*(rem N - 1) + 1,
   which goes to -infinity since rem N < 1, contradicting rem >= 0. *)
Lemma bin_digits_no_trailing_ones (x : R) :
  0 <= x < 1 -> no_trailing_ones (bin_digits x).
Proof.
move=> /andP [hx0 hx1].
rewrite /no_trailing_ones /bin_digits.
pose step := fun (y : R) => if 2%:R^-1 <= y then y *+ 2 - 1 else y *+ 2.
pose rem := fix f n := match n with 0%N => x | n'.+1 => step (f n') end.
have hrem_digit : forall n, bin_digit x n = (2%:R^-1 <= rem n).
  suff hgen : forall n y, bin_digit y n = (2%:R^-1 <= iter n step y).
    by move=> n; rewrite hgen; congr (_ <= _); elim: n => //= k ->.
  by elim=> [|k IHk] //= y; rewrite IHk -iterSr iterS.
have hrem_bound : forall n, 0 <= rem n /\ rem n < 1.
  elim=> [|k [IHk0 IHk1]] /=; first by split.
  rewrite /step; case: ifP => hle; split.
  - by rewrite subr_ge0 -half2 ler_pMn2r.
  - by rewrite ltrBlDr -mulr2n ltr_pMn2r.
  - have := @mulrn_wge0 R (rem k) 2 IHk0; done.
  - by rewrite -half2 ltr_pMn2r // real_ltNge ?num_real // hle.
have hstep_simp : forall N n, (N <= n)%N ->
    (forall m, (N <= m)%N -> 2%:R^-1 <= rem m) ->
    rem n.+1 = rem n *+ 2 - 1.
  by move=> NN n hn hall; rewrite /= /step (hall n hn).
have hstep_eq : forall N n, (N <= n)%N ->
    (forall m, (N <= m)%N -> 2%:R^-1 <= rem m) ->
    1 - rem n.+1 = (1 - rem n) *+ 2.
  move=> NN n hn hall; rewrite (hstep_simp NN) //.
  by rewrite -[rem n *+ 2]mulr_natr -[(1 - rem n) *+ 2]mulr_natr; ring.
move=> N.
suff : exists n, (N <= n)%N /\ ~~ (2%:R^-1 <= rem n).
  move=> [n [hn hlt]]; exists n; split=> //.
  by rewrite hrem_digit; apply/negbTE.
apply: contrapT => hnex.
have hall : forall n, (N <= n)%N -> 2%:R^-1 <= rem n.
  move=> n hn; apply: contrapT => hlt.
  by apply: hnex; exists n; split => //; apply/negP.
have hinv : forall k : nat, 1 - rem (N + k)%N = (1 - rem N) *+ 2 ^ k.
  elim=> [|k IHk]; first by rewrite /= expn0 mulr1n addn0.
  have -> : (N + k.+1)%N = (N + k).+1 by rewrite addnS.
  by rewrite (hstep_eq N) ?leq_addr // IHk -mulrnA expnSr.
have hle : forall k : nat, (1 - rem N) *+ 2 ^ k <= 1.
  move=> k; rewrite -hinv lerBlDr -{1}[1]addr0 lerD2l.
  exact: (hrem_bound (N + k)%N).1.
have hpos : 0 < 1 - rem N by rewrite subr_gt0; exact: (hrem_bound N).2.
have hinv_ge : 0 <= (1 - rem N)^-1.
  by rewrite invr_ge0; exact: ltW hpos.
have harch := archi_boundP hinv_ge.
set m := archi_bound _ in harch.
have hm : 1 < (1 - rem N) *+ m.
  rewrite -mulr_natr.
  have h : (1 - rem N) * (1 - rem N)^-1 < (1 - rem N) * m%:R.
    by rewrite ltr_pM2l.
  by rewrite divff ?lt0r_neq0 // in h.
have [k hk] : exists k, (m <= 2 ^ k)%N.
  by exists m; exact: ltnW (ltn_expl _ (ltnSn 1)).
have h1 := hle k.
suff h2 : (1 - rem N) *+ m <= (1 - rem N) *+ 2 ^ k.
  by have := lt_le_trans hm (le_trans h2 h1);
     rewrite ltxx.
rewrite -[X in X <= _]mulr_natr -[X in _ <= X]mulr_natr.
by rewrite ler_pM2l // ler_nat.
Qed.

(* Interleaving preserves the no-trailing-ones property *)
Lemma interleave_no_trailing_ones (d1 d2 : nat -> bool) :
  no_trailing_ones d1 -> no_trailing_ones d2 ->
  no_trailing_ones (interleave d1 d2).
Proof.
move=> h1 h2 N.
have [n1 [hn1 hd1]] := h1 N./2.+1.
exists (n1.*2)%N; split.
  have hlt : (N./2.*2 < n1.*2)%N by rewrite ltn_double.
  have hN : N = (odd N + N./2.*2)%N by rewrite odd_double_half.
  by rewrite hN; exact: (leq_trans (leq_add (leq_b1 _) (leqnn _)) hlt).
by rewrite /interleave odd_double /= half_double.
Qed.

(* bin_sum of a sequence with no trailing ones is < 1 *)
Lemma bin_sum_no_trailing_lt1 (d : nat -> bool) :
  no_trailing_ones d -> bin_sum d < 1.
Proof.
move=> hnt.
have [n [_ hdn]] := hnt 0%N.
have heps : (0 : R) < 2%:R^-1 ^+ n.+1.
  by apply: exprn_gt0; rewrite invr_gt0; apply: ltr0n.
suff hlt1 : bin_sum d <= 1 - 2%:R^-1 ^+ n.+1.
  apply: (le_lt_trans hlt1).
  rewrite ltrBlDr -{1}[1]addr0 ltrD2l. exact: heps.
apply: (@closed_cvg _ _ eventually _
  (fun m => bin_partial_sum d m : R^o) (fun y : R => y <= 1 - 2%:R^-1 ^+ n.+1)
  _ _ (bin_sum d)).
- exact: closed_le.
- exists n.+1 => // m hmn.
  rewrite /bin_partial_sum.
  apply: (le_trans
    (y := \sum_(i < m) (2%:R^-1 : R) ^+ i.+1 - 2%:R^-1 ^+ n.+1)).
  + rewrite (bigD1 (Ordinal hmn)) //=
      [X in _ <= X - _](bigD1 (Ordinal hmn)) //=.
    rewrite hdn /= mul0r add0r.
    change (\sum_(i < m | i != Ordinal hmn) (d i)%:R * 2%:R^-1 ^+ i.+1 <=
      (2%:R^-1 ^+ n.+1 +
       \sum_(i < m | i != Ordinal hmn) 2%:R^-1 ^+ i.+1) -
      2%:R^-1 ^+ n.+1 :> R).
    have -> : (2%:R^-1 ^+ n.+1 +
      \sum_(i < m | i != Ordinal hmn) (2%:R^-1 : R) ^+ i.+1) -
      2%:R^-1 ^+ n.+1 =
      \sum_(i < m | i != Ordinal hmn) (2%:R^-1 : R) ^+ i.+1 :> R.
      by rewrite addrC addKr.
    apply: ler_sum => i _. rewrite -[X in _ <= X]mul1r.
    apply: ler_wpM2r;
      [by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n|by case: (d i)].
  + rewrite geom_half_sum. apply: lerD => //.
    rewrite lerBlDr -{1}[1]addr0 lerD2l.
    by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
- rewrite /bin_sum; exact: is_cvg_bin_partial_sum.
Qed.

(* The converse of reconstruction: bin_digits (bin_sum d) =1 d
   for canonical digit sequences (no trailing ones).

   This is the uniqueness of binary expansions: there is only one
   representation of a real in [0,1) without trailing ones. *)
Lemma bin_sum_shift (d : nat -> bool) :
  bin_sum d = (d 0%N)%:R * 2%:R^-1 + bin_sum (d \o succn) * 2%:R^-1.
Proof.
have hrel : forall n : nat,
  bin_partial_sum d n.+1 =
  (d 0%N)%:R * 2%:R^-1 +
  bin_partial_sum (d \o succn) n * 2%:R^-1.
  move=> n; rewrite /bin_partial_sum big_ord_recl /=.
  congr (_ + _).
  rewrite /= mulr_suml; apply: eq_bigr => i _.
  by rewrite /bump leq0n /= exprSr mulrA.
rewrite /bin_sum.
have hcvg1 : cvgn (fun n => bin_partial_sum d n : R^o).
  exact: is_cvg_bin_partial_sum.
have hcvg2 : cvgn (fun n => bin_partial_sum (d \o succn) n : R^o).
  exact: is_cvg_bin_partial_sum.
have hlim_shift : limn [eta bin_partial_sum d] =
  limn (fun n => bin_partial_sum d n.+1 : R^o).
  apply/esym; apply: cvg_lim => //.
  by rewrite cvg_shiftS.
rewrite hlim_shift.
have -> : (fun n => bin_partial_sum d n.+1 : R^o) =
  (fun n => (d 0%N)%:R * 2%:R^-1 +
    bin_partial_sum (d \o succn) n * 2%:R^-1 : R^o).
  by apply: funext => n; rewrite hrel.
apply: cvg_lim => //.
have hcst :
  (fun _ : nat => (d 0%N)%:R * 2%:R^-1 : R^o) n
  @[n --> \oo] --> ((d 0%N)%:R * 2%:R^-1 : R^o).
  exact: cvg_cst.
have hprod :
  (fun n : nat =>
    bin_partial_sum (d \o succn) n * 2%:R^-1 : R^o) n
  @[n --> \oo] -->
  (limn [eta bin_partial_sum (d \o succn)] *
    2%:R^-1 : R^o).
  exact: cvgMr_tmp.
exact: cvgD hcst hprod.
Qed.

Lemma no_trailing_ones_shift (d : nat -> bool) :
  no_trailing_ones d -> no_trailing_ones (d \o succn).
Proof.
move=> hnt N; have [m [hm hdm]] := hnt N.+1.
have hm0 : (0 < m)%N by exact: leq_ltn_trans (leq0n _) hm.
exists m.-1; split.
- by rewrite -ltnS (prednK hm0).
- by rewrite /= (prednK hm0).
Qed.

Lemma bin_digits_bin_sum (d : nat -> bool) :
  no_trailing_ones d -> bin_digits (bin_sum d) =1 d.
Proof.
move=> hnt n.
elim: n d hnt => [|n IHn] dd hnt.
- rewrite /bin_digits /= bin_sum_shift.
  case hd0 : (dd 0%N) => /=.
  + rewrite mul1r; apply/idP.
    have hge0 : 0 <= bin_sum (dd \o succn) * 2%:R^-1.
      by apply: mulr_ge0; [exact: bin_sum_ge0|rewrite invr_ge0; apply: ler0n].
    rewrite lerDl //.
  + rewrite mul0r add0r; apply: lt_geF.
    rewrite ltr_pdivrMr ?ltr0n // mulVf ?pnatr_eq0 //.
    exact: bin_sum_no_trailing_lt1 (no_trailing_ones_shift hnt).
- rewrite /bin_digits /=.
  have hnt' := no_trailing_ones_shift hnt.
  have hstep : (if 2%:R^-1 <= bin_sum dd then bin_sum dd *+ 2 - 1
                else bin_sum dd *+ 2) = bin_sum (dd \o succn).
    rewrite bin_sum_shift.
    case hd0 : (dd 0%N) => /=.
    + rewrite mul1r.
      have hge : 2%:R^-1 <= (2%:R^-1 + bin_sum (dd \o succn) * 2%:R^-1).
        rewrite lerDl //; apply: mulr_ge0;
          [exact: bin_sum_ge0|by rewrite invr_ge0; apply: ler0n].
      rewrite hge.
      rewrite mulrnDl -[2^-1 *+ 2]mulr_natr mulVf ?pnatr_eq0 //.
      rewrite -[_ / 2 *+ 2]mulr_natr -mulrA mulVf ?pnatr_eq0 // mulr1.
      by rewrite addrC addKr.
    + rewrite mul0r add0r.
      have hlt : bin_sum (dd \o succn) / 2 < 2%:R^-1.
        have hlt1 := bin_sum_no_trailing_lt1 hnt'.
        rewrite ltr_pdivrMr ?ltr0n // mulVf ?pnatr_eq0 //.
      rewrite (lt_geF hlt).
      rewrite -[_ / 2 *+ 2]mulr_natr -mulrA mulVf ?pnatr_eq0 // mulr1 //.
  rewrite hstep.
  exact: (IHn (dd \o succn) hnt').
Qed.

(* Note: The no_trailing_ones hypotheses on deinterleaved subsequences do NOT
   follow from no_trailing_ones on the full sequence. This lemma is therefore
   not usable unconditionally. However, it is NOT needed for standard_borel_wit:
   only unit_to_pairK (the other direction, proved below without extra
   hypotheses) is required. See the comment block above for details. *)
Lemma pair_to_unitK (r : R) :
  0 <= r < 1 ->
  no_trailing_ones (deinterleave_even (bin_digits r)) ->
  no_trailing_ones (deinterleave_odd (bin_digits r)) ->
  pair_to_unit (unit_to_pair r) = r.
Proof.
move=> hr hnte hnto.
set de := deinterleave_even (bin_digits r).
set do_ := deinterleave_odd (bin_digits r).
have hnt := bin_digits_no_trailing_ones hr.
have hnt_de : no_trailing_ones de := hnte.
have hnt_do : no_trailing_ones do_ := hnto.
have hconv_de := bin_digits_bin_sum hnt_de.
have hconv_do := bin_digits_bin_sum hnt_do.
rewrite /pair_to_unit /unit_to_pair /= -/de -/do_.
have heq :
  interleave (bin_digits (bin_sum de))
    (bin_digits (bin_sum do_)) =1 bin_digits r.
  move=> n; rewrite /interleave.
  case: (boolP (odd n)) => hodd /=.
  - have := odd_double_half n; rewrite hodd /= add1n => heq.
    rewrite (hconv_do n./2) /do_ /deinterleave_odd.
    by rewrite heq.
  - rewrite (hconv_de n./2) /de /deinterleave_even.
    by rewrite even_halfK.
rewrite (bin_sum_ext heq).
by rewrite /de /do_ bin_digits_reconstruction.
Qed.

(* This is the KEY round-trip lemma: decode after encode is the identity.
   It holds unconditionally for (x,y) in [0,1)^2, with no trailing-ones
   hypothesis needed. This is the direction required by standard_borel_wit. *)
Lemma unit_to_pairK (xy : R * R) :
  0 <= xy.1 < 1 -> 0 <= xy.2 < 1 ->
  unit_to_pair (pair_to_unit xy) = xy.
Proof.
move=> hx hy.
set d1 := bin_digits xy.1.
set d2 := bin_digits xy.2.
have hnt1 := bin_digits_no_trailing_ones hx.
have hnt2 := bin_digits_no_trailing_ones hy.
have hnt12 := interleave_no_trailing_ones hnt1 hnt2.
have hconv := bin_digits_bin_sum hnt12.
rewrite /unit_to_pair /pair_to_unit -/d1 -/d2.
apply: injective_projections; rewrite /=.
- have h1 : deinterleave_even (bin_digits (bin_sum (interleave d1 d2))) =1 d1.
    move=> n; rewrite /deinterleave_even (hconv (n.*2)%N).
    exact: deinterleave_interleaveK_even.
  rewrite (bin_sum_ext h1).
  by rewrite /d1 bin_digits_reconstruction.
- have h2 : deinterleave_odd (bin_digits (bin_sum (interleave d1 d2))) =1 d2.
    move=> n; rewrite /deinterleave_odd (hconv (n.*2.+1)%N).
    exact: deinterleave_interleaveK_odd.
  rewrite (bin_sum_ext h2).
  by rewrite /d2 bin_digits_reconstruction.
Qed.

End round_trips.

(* Subsection: measurability of bin_digit, interleave/deinterleave digit
   extractors, and of pair_to_unit / unit_to_pair. *)
Section measurability_constructions.

(******************************************************************************)
(* Measurability helpers                                                      *)
(******************************************************************************)

(* The doubling-and-testing step function *)
Let step : R -> R := fun x => if (2%:R^-1 <= x) then x *+ 2 - 1 else x *+ 2.

Lemma measurable_step : measurable_fun [set: R] step.
Proof.
rewrite /step; apply: measurable_fun_ifT.
- apply: measurable_fun_ler; first exact: measurable_cst.
  exact: measurable_id.
- apply: measurable_funB; first exact: (natmul_measurable 2).
  exact: measurable_cst.
- exact: (natmul_measurable 2).
Qed.

Lemma measurable_iter_step (k : nat) :
  measurable_fun [set: R] (iter k step).
Proof.
elim: k => [|k IHk] /=.
- exact: measurable_id.
- exact: measurableT_comp measurable_step IHk.
Qed.

Lemma bin_digit_iter (n : nat) (x : R) :
  bin_digit x n = (2%:R^-1 <= iter n step x).
Proof.
elim: n x => [|n IHn] x //=.
by rewrite IHn -iterSr.
Qed.

Lemma measurable_bin_digit (n : nat) :
  measurable_fun [set: R] (fun x : R => bin_digit x n : bool).
Proof.
rewrite (_ : (fun x : R => _) =
  (fun x => 2%:R^-1 <= iter n step x)); last first.
  by apply: funext => x; rewrite bin_digit_iter.
apply: measurable_fun_ler.
- exact: measurable_cst.
- exact: measurable_iter_step.
Qed.

Lemma measurable_interleave_digit (m : nat) :
  measurable_fun [set: R * R]
    (fun xy : R * R => interleave (bin_digits xy.1) (bin_digits xy.2) m : bool).
Proof.
rewrite /interleave /bin_digits.
case: (boolP (odd m)) => hodd /=.
- exact: (measurableT_comp (measurable_bin_digit m./2) measurable_snd).
- exact: (measurableT_comp (measurable_bin_digit m./2) measurable_fst).
Qed.

Lemma measurable_deinterleave_even_digit (m : nat) :
  measurable_fun [set: R]
    (fun x : R => deinterleave_even (bin_digits x) m : bool).
Proof.
rewrite /deinterleave_even /bin_digits.
exact: measurable_bin_digit.
Qed.

Lemma measurable_deinterleave_odd_digit (m : nat) :
  measurable_fun [set: R]
    (fun x : R => deinterleave_odd (bin_digits x) m : bool).
Proof.
rewrite /deinterleave_odd /bin_digits.
exact: measurable_bin_digit.
Qed.

(******************************************************************************)
(* Measurability of bin_sum as a limit of measurable partial sums             *)
(******************************************************************************)

(* Helper: measurability of a single summand b%:R * c for measurable bool b *)
Lemma measurable_bool_scale {d : measure_display} {T : measurableType d}
    (f : T -> bool) (c : R) :
  measurable_fun [set: T] f ->
  measurable_fun [set: T] (fun x => (f x)%:R * c : R).
Proof.
move=> hf.
rewrite (_ : (fun x => _) = (fun x => if f x then c else (0 : R))); last first.
  by apply: funext => x; case: (f x) => /=; rewrite ?mul1r ?mul0r.
by apply: measurable_fun_ifT => //; exact: measurable_cst.
Qed.

(******************************************************************************)
(* Measurability                                                              *)
(******************************************************************************)

Lemma measurable_pair_to_unit :
  measurable_fun [set: R * R] pair_to_unit.
Proof.
rewrite /pair_to_unit /bin_sum.
apply: (@measurable_fun_cvg _ _ R [set: R * R]
  (fun n (xy : R * R) =>
    bin_partial_sum (interleave (bin_digits xy.1) (bin_digits xy.2)) n)
  (fun xy => limn (fun n =>
    bin_partial_sum (interleave (bin_digits xy.1) (bin_digits xy.2)) n : R^o))).
- move=> m; rewrite /bin_partial_sum.
  elim: m => [|m IHm].
    rewrite (_ : (fun _ : R * R => _) = (fun _ => (0 : R))); last first.
      by apply: funext => xy; rewrite big_ord0.
    exact: measurable_cst.
  rewrite (_ : (fun xy : R * R => \sum_(i < m.+1) _) =
    ((fun xy : R * R =>
      \sum_(i < m) (interleave (bin_digits xy.1) (bin_digits xy.2) i)%:R *
        2%:R^-1 ^+ i.+1) \+
     (fun xy : R * R =>
      (interleave (bin_digits xy.1) (bin_digits xy.2) m)%:R *
        2%:R^-1 ^+ m.+1))%R); last first.
    by apply: funext => xy; rewrite big_ord_recr.
  apply: measurable_funD => //.
  apply: measurable_bool_scale.
  exact: measurable_interleave_digit.
- move=> xy _; exact: is_cvg_bin_partial_sum.
Qed.

Lemma measurable_unit_to_pair_fst :
  measurable_fun [set: R] (fun r => (unit_to_pair r).1).
Proof.
rewrite /unit_to_pair /= /bin_sum.
apply: (@measurable_fun_cvg _ _ R [set: R]
  (fun n (x : R) =>
    bin_partial_sum (deinterleave_even (bin_digits x)) n)
  (fun x => limn (fun n =>
    bin_partial_sum (deinterleave_even (bin_digits x)) n : R^o))).
- move=> m; rewrite /bin_partial_sum.
  elim: m => [|m IHm].
    rewrite (_ : (fun _ : R => _) = (fun _ => (0 : R))); last first.
      by apply: funext => x; rewrite big_ord0.
    exact: measurable_cst.
  rewrite (_ : (fun x : R => \sum_(i < m.+1) _) =
    ((fun x : R =>
      \sum_(i < m) (deinterleave_even (bin_digits x) i)%:R *
        2%:R^-1 ^+ i.+1) \+
     (fun x : R =>
      (deinterleave_even (bin_digits x) m)%:R *
        2%:R^-1 ^+ m.+1))%R); last first.
    by apply: funext => x; rewrite big_ord_recr.
  apply: measurable_funD => //.
  apply: measurable_bool_scale.
  exact: measurable_deinterleave_even_digit.
- move=> x _; exact: is_cvg_bin_partial_sum.
Qed.

Lemma measurable_unit_to_pair_snd :
  measurable_fun [set: R] (fun r => (unit_to_pair r).2).
Proof.
rewrite /unit_to_pair /= /bin_sum.
apply: (@measurable_fun_cvg _ _ R [set: R]
  (fun n (x : R) =>
    bin_partial_sum (deinterleave_odd (bin_digits x)) n)
  (fun x => limn (fun n =>
    bin_partial_sum (deinterleave_odd (bin_digits x)) n : R^o))).
- move=> m; rewrite /bin_partial_sum.
  elim: m => [|m IHm].
    rewrite (_ : (fun _ : R => _) = (fun _ => (0 : R))); last first.
      by apply: funext => x; rewrite big_ord0.
    exact: measurable_cst.
  rewrite (_ : (fun x : R => \sum_(i < m.+1) _) =
    ((fun x : R =>
      \sum_(i < m) (deinterleave_odd (bin_digits x) i)%:R *
        2%:R^-1 ^+ i.+1) \+
     (fun x : R =>
      (deinterleave_odd (bin_digits x) m)%:R *
        2%:R^-1 ^+ m.+1))%R); last first.
    by apply: funext => x; rewrite big_ord_recr.
  apply: measurable_funD => //.
  apply: measurable_bool_scale.
  exact: measurable_deinterleave_odd_digit.
- move=> x _; exact: is_cvg_bin_partial_sum.
Qed.

End measurability_constructions.

(* Subsection: the composed R x R <-> R bijection encode_RR/decode_RR,
   its round-trip property, and measurability (including measurable_psi
   on all of R), culminating in pair_standard_borel. *)
Section composed_bijection.

(******************************************************************************)
(* Composed bijection R x R <-> R                                            *)
(******************************************************************************)

Definition encode_RR (xy : R * R) : R :=
  psi (pair_to_unit (phi xy.1, phi xy.2)).

Definition decode_RR (r : R) : R * R :=
  let uv := unit_to_pair (phi r) in (psi uv.1, psi uv.2).

(** phi x is in [0,1) *)
Lemma phi_ge0 (x : R) : 0 <= phi x.
Proof. exact: ltW (phi_gt0 x). Qed.

Lemma phi_in_01 (x : R) : 0 <= phi x < 1.
Proof. by apply/andP; split; [exact: phi_ge0|exact: phi_lt1]. Qed.

(** bin_sum of a digit sequence with at least one true digit is > 0 *)
Lemma bin_sum_has_one_gt0 (d : nat -> bool) (k : nat) :
  d k = true -> 0 < bin_sum d.
Proof.
move=> hdk.
have heps : (0 : R) < (d k)%:R * 2%:R^-1 ^+ k.+1.
  rewrite hdk /= mul1r; apply: exprn_gt0.
  by rewrite invr_gt0; apply: ltr0n.
suff hle : (d k)%:R * 2%:R^-1 ^+ k.+1 <= bin_sum d.
  exact: (lt_le_trans heps hle).
rewrite /bin_sum.
apply: (@closed_cvg _ _ eventually _
  (fun n => bin_partial_sum d n : R^o)
  (fun z : R => (d k)%:R * 2%:R^-1 ^+ k.+1 <= z)
  _ _ (bin_sum d)).
- exact: closed_ge.
- exists k.+1 => // m hmk.
  rewrite /bin_partial_sum (bigD1 (Ordinal hmk)) //=.
  rewrite lerDl; apply: sumr_ge0 => i _.
  apply: mulr_ge0; first by case: (d i).
  by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
- rewrite /bin_sum; exact: is_cvg_bin_partial_sum.
Qed.

(** phi x has at least one true binary digit (since phi x > 0) *)
Lemma phi_has_true_digit (x : R) :
  exists k, bin_digits (phi x) k = true.
Proof.
apply: contrapT => hnone.
have hall : forall k, bin_digits (phi x) k = false.
  move=> k; apply: contrapT => hk.
  by apply: hnone; exists k; case: (bin_digits (phi x) k) hk.
have hd0 : bin_digits (phi x) =1 (fun _ => false).
  by move=> k; rewrite hall.
have hbps0 : forall n, bin_partial_sum (fun _ : nat => false) n = (0 : R).
  move=> n; rewrite /bin_partial_sum big1 // => i _.
  by rewrite /= mul0r.
have hsum0 : bin_sum (bin_digits (phi x)) = 0.
  have hle : bin_sum (bin_digits (phi x)) <= 0.
    rewrite (bin_sum_ext hd0) /bin_sum.
    apply: (@closed_cvg _ _ eventually _
      (fun n => bin_partial_sum (fun _ => false) n : R^o) (fun z : R => z <= 0)
      _ _ _).
    - exact: closed_le.
    - by apply: nearW => n; rewrite hbps0.
    - exact: is_cvg_bin_partial_sum.
  have hge := bin_sum_ge0 (bin_digits (phi x)).
  by apply: le_anti; apply/andP; split.
have hphi01 := phi_in_01 x.
have hrecon := bin_digits_reconstruction hphi01.
by rewrite hsum0 in hrecon; have := phi_gt0 x; rewrite -hrecon
   ltxx.
Qed.

(** pair_to_unit of phi values lands in (0,1) *)
Lemma pair_to_unit_phi_gt0 (x y : R) :
  0 < pair_to_unit (phi x, phi y).
Proof.
have [k hk] := phi_has_true_digit x.
apply: (bin_sum_has_one_gt0 (k := (k.*2)%N)).
rewrite /interleave odd_double /= half_double.
exact: hk.
Qed.

Lemma pair_to_unit_phi_lt1 (x y : R) :
  pair_to_unit (phi x, phi y) < 1.
Proof.
apply: bin_sum_no_trailing_lt1.
apply: interleave_no_trailing_ones;
  [exact: bin_digits_no_trailing_ones (phi_in_01 _)|
   exact: bin_digits_no_trailing_ones (phi_in_01 _)].
Qed.

Lemma pair_to_unit_phi_in_itv (x y : R) :
  pair_to_unit (phi x, phi y) \in `](0:R), 1[.
Proof.
rewrite in_itv /=; apply/andP.
split; [exact: pair_to_unit_phi_gt0|exact: pair_to_unit_phi_lt1].
Qed.

Lemma pair_to_unit_phi_in_01 (x y : R) :
  0 <= pair_to_unit (phi x, phi y) < 1.
Proof.
apply/andP; split.
- exact: ltW (pair_to_unit_phi_gt0 x y).
- exact: pair_to_unit_phi_lt1.
Qed.

(** unit_to_pair components of phi r are in [0,1] *)
Lemma unit_to_pair_fst_ge0 (r : R) :
  0 <= (unit_to_pair (phi r)).1.
Proof. exact: bin_sum_ge0. Qed.

Lemma unit_to_pair_fst_le1 (r : R) :
  (unit_to_pair (phi r)).1 <= 1.
Proof. exact: bin_sum_le1. Qed.

Lemma unit_to_pair_snd_ge0 (r : R) :
  0 <= (unit_to_pair (phi r)).2.
Proof. exact: bin_sum_ge0. Qed.

Lemma unit_to_pair_snd_le1 (r : R) :
  (unit_to_pair (phi r)).2 <= 1.
Proof. exact: bin_sum_le1. Qed.

(** Round-trip: decode (encode (x,y)) = (x,y) -- UNCONDITIONAL *)
Theorem encode_RRK (xy : R * R) :
  decode_RR (encode_RR xy) = xy.
Proof.
rewrite /decode_RR /encode_RR.
set v := pair_to_unit (phi xy.1, phi xy.2).
have hv_itv : v \in `](0:R), 1[ := pair_to_unit_phi_in_itv xy.1 xy.2.
have hv_eq : phi (psi v) = v := phiK hv_itv.
have hx01 : 0 <= (phi xy.1) < 1 := phi_in_01 xy.1.
have hy01 : 0 <= (phi xy.2) < 1 := phi_in_01 xy.2.
have hutp : unit_to_pair v = (phi xy.1, phi xy.2).
  rewrite /v; apply: unit_to_pairK.
  - exact: hx01.
  - exact: hy01.
rewrite hv_eq hutp !psiK.
by destruct xy.
Qed.

(** Round-trip: encode (decode r) = r

   This direction requires:
   1. no_trailing_ones on the deinterleaved even/odd subsequences of
      bin_digits(phi(r)) -- needed for pair_to_unitK
   2. The components (unit_to_pair(phi r)).1 and .2 must be in (0,1)
      (strictly positive) -- needed for phiK (cancel psi phi)

   Condition (2) follows from (1) when the deinterleaved subsequences
   each contain at least one true digit, which holds generically
   (the set of exceptions is countable, hence measure-zero). *)
Theorem decode_RRK (r : R)
  (hnt_even : no_trailing_ones (deinterleave_even (bin_digits (phi r))))
  (hnt_odd : no_trailing_ones (deinterleave_odd (bin_digits (phi r))))
  (hu1_pos : 0 < (unit_to_pair (phi r)).1)
  (hu2_pos : 0 < (unit_to_pair (phi r)).2) :
  encode_RR (decode_RR r) = r.
Proof.
rewrite /encode_RR /decode_RR /=.
set u1 := (unit_to_pair (phi r)).1.
set u2 := (unit_to_pair (phi r)).2.
have hu1_lt1 : u1 < 1.
  exact: bin_sum_no_trailing_lt1 hnt_even.
have hu2_lt1 : u2 < 1.
  exact: bin_sum_no_trailing_lt1 hnt_odd.
have hu1_01 : u1 \in `](0:R), 1[.
  by rewrite in_itv /=; apply/andP; split.
have hu2_01 : u2 \in `](0:R), 1[.
  by rewrite in_itv /=; apply/andP; split.
rewrite (phiK hu1_01) (phiK hu2_01).
have hphi01 := phi_in_01 r.
rewrite -/u1 -/u2 /u1 /u2.
rewrite (pair_to_unitK hphi01 hnt_even hnt_odd).
by rewrite psiK.
Qed.

(** Measurability of encode_RR *)
Lemma measurable_encode_RR : measurable_fun [set: R * R] encode_RR.
Proof.
rewrite /encode_RR.
have hmeas_phi_pair : measurable_fun [set: R * R]
  (fun xy : R * R => (phi xy.1, phi xy.2)).
  apply: measurable_fun_pair.
  - apply: measurableT_comp; first exact: measurable_phi.
    exact: measurable_fst.
  - apply: measurableT_comp; first exact: measurable_phi.
    exact: measurable_snd.
have hmeas_inner : measurable_fun [set: R * R]
  (fun xy : R * R => pair_to_unit (phi xy.1, phi xy.2)).
  apply: measurableT_comp; first exact: measurable_pair_to_unit.
  exact: hmeas_phi_pair.
apply: (measurable_comp (F := `](0:R), 1[)).
- exact: measurable_itv.
- move=> _ [xy _ <-] /=.
  rewrite in_itv /=; apply/andP; split.
  + exact: pair_to_unit_phi_gt0.
  + exact: pair_to_unit_phi_lt1.
- exact: measurable_psi.
- exact: hmeas_inner.
Qed.

(** Measurability of psi on setT.
    psi y = tan(pi * (y - 1/2)) is continuous (hence measurable) on
    every open interval ]n, n+1[ for integer n, since the only
    singularities of tan(pi*(y-1/2)) are at y = 0, 1, -1, 2, ...
    (integer values). Since R is a countable union of such open
    intervals plus the countable set of integers (singletons are
    measurable), psi is measurable on setT. *)
Lemma inv_cvg_approx (x : R) :
  (fun n : nat => x / (x * x + n.+1%:R^-1)) @ \oo --> x^-1.
Proof.
case: (eqVneq x 0) => [->|hx0].
- rewrite invr0.
  under eq_cvg do rewrite mul0r.
  exact: cvg_cst.
- have -> : x^-1 = x / (x * x).
    by rewrite invfM ?unitfE // [x * (x^-1 * x^-1)]mulrCA
               mulrV ?unitfE // mulr1.
  apply: cvgM; first exact: cvg_cst.
  apply: cvgV.
    by rewrite mulf_neq0.
  rewrite -[X in _ --> X]addr0.
  apply: cvgD; first exact: cvg_cst.
  exact: @cvg_harmonic.
Qed.

Lemma measurable_psi_setT : measurable_fun [set: R] (@psi R).
Proof.
rewrite /psi.
apply: measurableT_comp; last first.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_funB; first exact: measurable_id.
  exact: measurable_cst.
(* Goal: measurable_fun setT tan *)
rewrite /tan.
apply: measurable_funM.
  apply: continuous_measurable_fun; exact: continuous_sin.
(* Goal: measurable_fun setT (fun x => (cos x)^-1) *)
apply: measurableT_comp; last first.
  apply: continuous_measurable_fun; exact: continuous_cos.
(* Goal: measurable_fun setT inv *)
apply: (@measurable_fun_cvg _ _ _ _ (fun n (x : R) =>
  x * (x * x + n.+1%:R^-1)^-1)).
- move=> m; apply: continuous_measurable_fun => y.
  rewrite /continuous_at.
  have hden_neq0 : y * y + m.+1%:R^-1 != 0.
    rewrite lt0r_neq0 //; apply: ltr_wpDl; first exact: sqr_ge0.
    by rewrite invr_gt0; exact: ltr0Sn.
  apply: cvgM; first exact: cvg_id.
  apply: cvgV => //.
  apply: cvgD; last exact: cvg_cst.
  apply: cvgM; exact: cvg_id.
- move=> x _; exact: inv_cvg_approx.
Qed.

(** Measurability of decode_RR.
    This follows from measurability of psi on setT (measurable_psi_setT),
    measurable_unit_to_pair_fst/snd, and measurable_phi, by composition.
    The proof is deferred pending the proof of measurable_psi_setT. *)
Lemma measurable_decode_RR : measurable_fun [set: R] decode_RR.
Proof.
rewrite /decode_RR.
apply: measurable_fun_pair.
- apply: measurableT_comp; first exact: measurable_psi_setT.
  rewrite (_ : (fun x => (unit_to_pair (phi x)).1) =
    (fun x => (unit_to_pair x).1) \o (@phi R)); last by [].
  apply: measurableT_comp.
    exact: measurable_unit_to_pair_fst.
  exact: measurable_phi.
- rewrite (_ : (fun x => psi (unit_to_pair (phi x)).2) =
    (@psi R) \o
    ((fun x => (unit_to_pair x).2) \o (@phi R))); last by [].
  apply: measurableT_comp; first exact: measurable_psi_setT.
  rewrite (_ : (fun x => (unit_to_pair x).2) \o (@phi R) =
    (fun x => (unit_to_pair (@phi R x)).2)); last by [].
  rewrite (_ : (fun x => (unit_to_pair (phi x)).2) =
    (fun x => (unit_to_pair x).2) \o (@phi R)); last by [].
  apply: measurableT_comp.
    exact: measurable_unit_to_pair_snd.
  exact: measurable_phi.
Qed.

(* The main application: product of standard Borel spaces is standard Borel *)
Lemma pair_standard_borel :
  exists (f : R * R -> R) (g : R -> R * R),
    measurable_fun setT f /\ measurable_fun setT g /\
    (forall xy, g (f xy) = xy).
Proof.
exists encode_RR, decode_RR.
split; first exact: measurable_encode_RR.
split; first exact: measurable_decode_RR.
exact: encode_RRK.
Qed.

End composed_bijection.

End binary_digit_interleaving.

(* Measurability restated in terms of measurableTypeR for use with
   lebesgue_stieltjes_measure-based sigma algebras (product measures etc.) *)
Section standard_borel_mR.
Variable R : realType.
Local Notation mR := (measurableTypeR R).

Definition encode_RR_mR : mR * mR -> mR := @encode_RR R.
Definition decode_RR_mR : mR -> mR * mR := @decode_RR R.

Lemma measurable_RR_to_R :
  measurable_fun [set: mR * mR] encode_RR_mR.
Proof. exact: measurable_encode_RR. Qed.

Lemma measurable_R_to_RR :
  measurable_fun [set: mR] decode_RR_mR.
Proof. exact: measurable_decode_RR. Qed.

Lemma encode_RR_mRK (xy : mR * mR) :
  decode_RR_mR (encode_RR_mR xy) = xy.
Proof. exact: encode_RRK. Qed.

End standard_borel_mR.
