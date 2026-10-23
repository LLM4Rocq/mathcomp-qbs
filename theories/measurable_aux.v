(* QBS project. License: CeCILL-C.                                            *)
From mathcomp Require Import boot order algebra reals classical_sets boolp
  topology num_topology normedtype measurable_structure measurable_function
  measurable_realfun lebesgue_stieltjes_measure.

(**md**************************************************************************)
(* # Auxiliary measurability facts                                            *)
(*                                                                            *)
(* Facts about measurable functions on the reals that are not (yet) in        *)
(* mathcomp-analysis.                                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*                measurable_invr == x |-> x^-1 is measurable on R            *)
(*    measurable_fun_nat_discrete == a map into nat is measurable when the    *)
(*                                   preimages of singletons are              *)
(*              measurable_truncn == truncn : R -> nat is measurable          *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.POrderTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section measurable_aux.
Context {R : realType}.
Local Abbreviation mR := (measurableTypeR R).

Lemma measurable_invr : measurable_fun [set: mR] (@GRing.inv R).
Proof.
rewrite -(setUv [set (0 : mR)%R]); apply/measurable_funU => //.
  exact: measurableC.
split; first exact: measurable_fun_set1.
apply: open_continuous_measurable_fun.
  by apply/closed_openC/accessible_closed_set1; exact: hausdorff_accessible.
by move=> x /[!inE] /eqP x0; exact: inv_continuous.
Qed.

(** Helper: measurability for functions into nat (discrete sigma-algebra).
    Every set in nat is measurable, so measurability of g reduces to
    measurability of singleton preimages. *)
Lemma measurable_fun_nat_discrete d (T : measurableType d)
    (g : T -> nat) (D : set T) :
  (forall n : nat, measurable (D `&` g @^-1` [set n])) ->
  measurable_fun D g.
Proof.
move=> hg _ Y _; rewrite /measurable /=.
have -> : D `&` g @^-1` Y = \bigcup_(n in Y) (D `&` g @^-1` [set n]).
  apply/seteqP; split=> [r [Dr Ygr]|r [n Yn [Dr /= gr]]].
    by exists (g r).
  by split=> //; rewrite /preimage /= gr.
by apply: bigcup_measurable => n Yn; exact: hg.
Qed.

(** truncn : R -> nat is measurable.
    Preimages of singletons are intervals:
    - trunc^{-1}({0}) = (-inf, 1)
    - trunc^{-1}({n+1}) = [n+1, n+2) *)
Lemma measurable_truncn :
  measurable_fun [set: mR] (truncn : mR -> nat).
Proof.
apply: measurable_fun_nat_discrete => n; rewrite setTI.
have -> : (truncn : mR -> nat) @^-1` [set n] =
    if n is 0%N then [set` `]-oo, 1%:R[] else [set` `[n%:R, n.+1%:R[].
  apply/seteqP; split => r /=; rewrite /preimage /=.
  - case: n => [|n] h /=.
      by rewrite in_itv /= -real_truncn_le_nat ?num_real // h.
    have r1 : 1 <= r by rewrite -truncn_gt0 h.
    by rewrite in_itv /= -h truncn_itv // (le_trans ler01 r1).
  - case: n => [|n] /=; rewrite in_itv /=.
      by move=> r1; apply/truncn0Pn; rewrite real_ltNge ?num_real in r1.
    by move=> hr; apply: truncn_def.
by case: n => [|n]; exact: measurable_itv.
Qed.

End measurable_aux.
