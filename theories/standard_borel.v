(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp.reals Require Import reals constructive_ereal.
From mathcomp.classical Require Import classical_sets filter.
From mathcomp.analysis Require Import topology_theory.num_topology.
From mathcomp.analysis Require Import normedtype_theory.normedtype sequences.
From mathcomp.analysis Require Import measure_theory.measurable_structure.
From mathcomp.analysis Require Import measure_theory.measurable_function.
From mathcomp.analysis Require Import lebesgue_stieltjes_measure.
From mathcomp.analysis Require Import measurable_realfun trigo exp.

(**md**************************************************************************)
(* # Standard Borel Spaces                                                     *)
(* Measurable bijection R ≅ R × R for standard Borel space closure.           *)
(*                                                                            *)
(* This file constructs a measurable bijection between R and the open         *)
(* interval (0,1) using the arctangent function, as the first step towards    *)
(* the R ≅ R × R construction.                                               *)
(*                                                                            *)
(* ```                                                                        *)
(*   phi x == atan(x)/pi + 1/2, a measurable bijection R -> (0,1)            *)
(*   psi y == tan(pi*(y - 1/2)), its inverse (0,1) -> R                      *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                               *)
(*   phi_gt0 == phi x > 0 for all x                                           *)
(*   phi_lt1 == phi x < 1 for all x                                           *)
(*   psiK    == cancel phi psi (psi is left inverse of phi)                   *)
(*   phiK    == cancel psi phi on (0,1)                                       *)
(*   measurable_phi == phi is measurable on R                                 *)
(*   measurable_psi == psi is measurable on (0,1)                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory reals classical_sets.
Import GRing.Theory.
Import numFieldTopology.Exports.

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
  by move: hy; rewrite inE /= => /andP []; rewrite !bnd_simp => ? ?;
     apply/andP.
have /andP [hy0 hy1] := hy01.
have hcos : cos (pi * (y - 1 / 2)) != 0.
  rewrite lt0r_neq0 //; apply: cos_gt0_pihalf.
  apply/andP; split.
    have -> : - ((pi : R) / 2) = pi * (- (1 / 2)) by rewrite mulrN mul1r.
    by rewrite ltr_pM2l ?pi_gt0 // ltrDr.
  have -> : (pi : R) / 2 = pi * (1 / 2) by rewrite mul1r.
  rewrite ltr_pM2l ?pi_gt0 // ltrBlDr -splitr; exact: hy1.
rewrite /psi.
apply: (@topology_structure.continuous_comp _ _ _
          (fun y0 : R => pi * (y0 - 1/2)) tan).
  apply: continuousM; first exact: topology_structure.cvg_cst.
  apply: continuousB; first exact: filter.cvg_id.
  exact: topology_structure.cvg_cst.
exact: continuous_tan.
Qed.

End phi_psi.

Section binary_digit_interleaving.
Variable R : realType.

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
      first by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
    by case: (d i).
  exact: (order.Order.POrderTheory.le_trans hle hgeom).
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
apply: (@topology_structure.closed_cvg _ _ eventually _
  (fun n => bin_partial_sum d n : R^o) (fun x : R => x <= 1)
  _ _ (bin_sum d)).
- exact: closed_le.
- by near=> n; exact: bin_partial_sum_le1.
- rewrite /bin_sum; exact: is_cvg_bin_partial_sum.
Unshelve. all: end_near.
Qed.

Lemma bin_sum_ge0 (d : nat -> bool) : 0 <= bin_sum d.
Proof.
apply: (@topology_structure.closed_cvg _ _ eventually _
  (fun n => bin_partial_sum d n : R^o) (fun x : R => 0 <= x)
  _ _ (bin_sum d)).
- exact: closed_ge.
- by near=> n; exact: bin_partial_sum_ge0.
- rewrite /bin_sum; exact: is_cvg_bin_partial_sum.
Unshelve. all: end_near.
Qed.

(******************************************************************************)
(* The pairing function (0,1) x (0,1) -> (0,1) and its inverse               *)
(******************************************************************************)

Definition pair_to_unit (xy : R * R) : R :=
  bin_sum (interleave (bin_digits xy.1) (bin_digits xy.2)).

Definition unit_to_pair (r : R) : R * R :=
  (bin_sum (deinterleave_even (bin_digits r)),
   bin_sum (deinterleave_odd (bin_digits r))).

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
  exact: (separation_axioms.cvg_lim _ hcvg).
pose step := fun (y : R) => if 2%:R^-1 <= y then y *+ 2 - 1 else y *+ 2.
pose rem := fix f n := match n with 0%N => x | n'.+1 => step (f n') end.
have hrem_digit : forall n, bin_digit x n = (2%:R^-1 <= rem n).
  suff hgen : forall n y, bin_digit y n = (2%:R^-1 <= iter n step y).
    by move=> n; rewrite hgen; congr (_ <= _); elim: n => //= k ->.
  by elim => [|k IHk] //= y; rewrite IHk -iterSr iterS.
have hinv : forall n : nat,
    x - bin_partial_sum (bin_digit x) n = rem n * 2%:R^-1 ^+ n :> R.
  elim => [|k IHk].
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
have half2 : 2%:R^-1 *+ 2 = (1 : R).
  have h : (1 : R) / 2%:R = 2%:R^-1 by rewrite div1r.
  by rewrite /GRing.natmul /= -[2%:R^-1]h -(@Num.Theory.splitr R 1).
have hrem_bound : forall n, 0 <= rem n /\ rem n < 1.
  elim => [|k [IHk0 IHk1]] /=; first by split.
  rewrite /step; case: ifP => hle; split.
  - by rewrite subr_ge0 -half2 ler_pMn2r.
  - by rewrite ltrBlDr -mulr2n ltr_pMn2r.
  - have := @Num.Theory.mulrn_wge0 R (rem k) 2 IHk0; done.
  - by rewrite -half2 ltr_pMn2r // Num.Theory.real_ltNge ?num_real // hle.
have habs_half : `|(2%:R^-1 : R)| < 1.
  by rewrite ger0_norm ?invr_ge0 ?ler0n // invf_lt1 ?ltr0n // ltr1n.
have hrem_cvg : (fun n => rem n * 2%:R^-1 ^+ n : R^o) n
                  @[n --> \oo] --> (0 : R^o).
  apply: (@squeeze_cvgr _ _ _ _
    (fun _ => 0 : R^o) (fun n => 2%:R^-1 ^+ n : R^o)).
  - near=> n; apply/andP; split.
    + by have [] := hrem_bound n.
    + by apply: exprn_ge0; rewrite invr_ge0; apply: ler0n.
    + by have [_ h] := hrem_bound n;
         exact: order.Order.POrderTheory.ltW h.
    + by [].
  - exact: topology_structure.cvg_cst.
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
  exact: topology_structure.cvg_cst.
by move=> hcstx; have := cvgB hcstx hrem_cvg; rewrite subr0.
Unshelve. all: end_near.
Qed.

(******************************************************************************)
(* Round-trip properties (up to dyadic rationals, a measure-zero set)         *)
(******************************************************************************)

(* Round-trip: these follow from bin_digits_reconstruction combined with
   the fact that bin_digits (bin_sum d) =1 d for digit sequences arising
   from reals in [0,1). The latter is essentially uniqueness of binary
   expansions for non-dyadic rationals. We leave these admitted pending
   the completion of bin_digits_reconstruction by the other agent, and
   the additional converse direction. *)

Lemma unit_to_pair_to_unit (r : R) :
  0 <= r < 1 -> pair_to_unit (unit_to_pair r) = r.
Proof. Admitted.

Lemma pair_to_unit_to_pair (xy : R * R) :
  0 <= xy.1 < 1 -> 0 <= xy.2 < 1 ->
  unit_to_pair (pair_to_unit xy) = xy.
Proof. Admitted.

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
rewrite (_ : (fun x : R => _) = (fun x => 2%:R^-1 <= iter n step x)); last first.
  by apply: boolp.funext => x; rewrite bin_digit_iter.
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
  by apply: boolp.funext => x; case: (f x) => /=; rewrite ?mul1r ?mul0r.
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
      by apply: boolp.funext => xy; rewrite big_ord0.
    exact: measurable_cst.
  rewrite (_ : (fun xy : R * R => \sum_(i < m.+1) _) =
    ((fun xy : R * R =>
      \sum_(i < m) (interleave (bin_digits xy.1) (bin_digits xy.2) i)%:R *
        2%:R^-1 ^+ i.+1) \+
     (fun xy : R * R =>
      (interleave (bin_digits xy.1) (bin_digits xy.2) m)%:R *
        2%:R^-1 ^+ m.+1))%R); last first.
    by apply: boolp.funext => xy; rewrite big_ord_recr.
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
      by apply: boolp.funext => x; rewrite big_ord0.
    exact: measurable_cst.
  rewrite (_ : (fun x : R => \sum_(i < m.+1) _) =
    ((fun x : R =>
      \sum_(i < m) (deinterleave_even (bin_digits x) i)%:R *
        2%:R^-1 ^+ i.+1) \+
     (fun x : R =>
      (deinterleave_even (bin_digits x) m)%:R *
        2%:R^-1 ^+ m.+1))%R); last first.
    by apply: boolp.funext => x; rewrite big_ord_recr.
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
      by apply: boolp.funext => x; rewrite big_ord0.
    exact: measurable_cst.
  rewrite (_ : (fun x : R => \sum_(i < m.+1) _) =
    ((fun x : R =>
      \sum_(i < m) (deinterleave_odd (bin_digits x) i)%:R *
        2%:R^-1 ^+ i.+1) \+
     (fun x : R =>
      (deinterleave_odd (bin_digits x) m)%:R *
        2%:R^-1 ^+ m.+1))%R); last first.
    by apply: boolp.funext => x; rewrite big_ord_recr.
  apply: measurable_funD => //.
  apply: measurable_bool_scale.
  exact: measurable_deinterleave_odd_digit.
- move=> x _; exact: is_cvg_bin_partial_sum.
Qed.

End binary_digit_interleaving.
