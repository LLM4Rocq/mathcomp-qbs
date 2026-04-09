(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From mathcomp Require Import reals ereal topology classical_sets
  borel_hierarchy measure lebesgue_stieltjes_measure lebesgue_measure
  lebesgue_integral probability measurable_realfun.
From mathcomp.classical Require Import boolp.
From QBS Require Import quasi_borel coproduct_qbs probability_qbs
  measure_as_qbs_measure.

(**md****************************************************************)
(* # Higher-Order Probabilistic Programming Language                *)
(*                                                                  *)
(* A minimal higher-order PPL with denotational semantics in QBS.   *)
(* Types include reals, booleans, unit, products, function spaces,  *)
(* and the probability monad. Expressions are intrinsically typed   *)
(* and the denotational semantics maps each well-typed term to a    *)
(* QBS morphism from context to type.                               *)
(*                                                                  *)
(* Key constructions:                                               *)
(* ```                                                              *)
(*   ppl_type          == PPL types                                 *)
(*   type_denot R t    == QBS denotation of type t                  *)
(*   ctx_denot R G     == QBS denotation of context G               *)
(*   has_var G t       == de Bruijn variable membership witness     *)
(*   expr G t          == intrinsically typed expression            *)
(*   expr_denot e      == semantic function ctx -> type             *)
(*   expr_morphism e   == proof that expr_denot is a QBS morphism  *)
(*   e_lam / e_app     == higher-order: lambda and application     *)
(*   e_ret             == monadic return                            *)
(*   e_sample_uniform  == sample from Uniform[0,1]                 *)
(*   e_sample_normal   == sample from Normal(mu,sigma)             *)
(* ```                                                              *)
(********************************************************************)

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * PPL Types *)

Inductive ppl_type : Type :=
  | ppl_real
  | ppl_bool
  | ppl_unit
  | ppl_prod (t1 t2 : ppl_type)
  | ppl_fun (t1 t2 : ppl_type)
  | ppl_prob (t : ppl_type).

(** * Context membership (de Bruijn indices) *)

Definition ctx := seq ppl_type.

Inductive has_var : ctx -> ppl_type -> Type :=
  | var_here : forall G t,
      has_var (t :: G) t
  | var_there : forall G t s,
      has_var G t -> has_var (s :: G) t.

Section ppl_denot.
Variable R : realType.

Local Notation mR := (measurableTypeR R).

(** * Type Denotation *)

Fixpoint type_denot (t : ppl_type) : qbsType R :=
  match t with
  | ppl_real => realQ R
  | ppl_bool => boolQ R
  | ppl_unit => unitQ R
  | ppl_prod t1 t2 =>
      prodQ (type_denot t1) (type_denot t2)
  | ppl_fun t1 t2 =>
      expQ (type_denot t1) (type_denot t2)
  | ppl_prob t =>
      monadP (type_denot t)
  end.

(** * Context Denotation *)

Fixpoint ctx_denot (G : ctx) : qbsType R :=
  match G with
  | nil => unitQ R
  | t :: G' =>
      prodQ (type_denot t) (ctx_denot G')
  end.

(** * Variable Lookup *)

Fixpoint var_lookup G t (v : has_var G t) :
  ctx_denot G -> type_denot t :=
  match v with
  | var_here _ _ => fun env => fst env
  | var_there _ _ _ v' =>
      fun env => var_lookup v' (snd env)
  end.

Lemma var_lookup_morphism G t
  (v : has_var G t) :
  @qbs_morphism R (ctx_denot G)
    (type_denot t) (var_lookup v).
Proof.
elim: v => [G' t'|G' t' s v' IH] /=.
- exact: qbs_morphism_fst.
- move=> alpha halpha.
  exact: IH (qbs_morphism_snd halpha).
Qed.

(** * Expressions (intrinsically typed) *)

Inductive expr : ctx -> ppl_type -> Type :=
  (** Variable reference (de Bruijn). *)
  | e_var : forall G t,
      has_var G t -> expr G t
  (** Real literal. *)
  | e_real : forall G,
      R -> expr G ppl_real
  (** Boolean literal. *)
  | e_bool : forall G,
      bool -> expr G ppl_bool
  (** Unit value. *)
  | e_tt : forall G,
      expr G ppl_unit
  (** Pair introduction. *)
  | e_pair : forall G t1 t2,
      expr G t1 -> expr G t2 ->
      expr G (ppl_prod t1 t2)
  (** First projection. *)
  | e_fst : forall G t1 t2,
      expr G (ppl_prod t1 t2) -> expr G t1
  (** Second projection. *)
  | e_snd : forall G t1 t2,
      expr G (ppl_prod t1 t2) -> expr G t2
  (** Lambda abstraction (higher-order). *)
  | e_lam : forall G t1 t2,
      expr (t1 :: G) t2 ->
      expr G (ppl_fun t1 t2)
  (** Function application. *)
  | e_app : forall G t1 t2,
      expr G (ppl_fun t1 t2) ->
      expr G t1 ->
      expr G t2
  (** Monadic return. *)
  | e_ret : forall G t,
      expr G t ->
      expr G (ppl_prob t)
  (** Sample from Uniform[0,1]. *)
  | e_sample_uniform : forall G,
      expr G (ppl_prob ppl_real)
  (** Sample from Normal(mu,sigma). *)
  | e_sample_normal : forall G
      (mu sigma : R) (hsigma : (0 < sigma)%R),
      expr G (ppl_prob ppl_real).

(** * Morphism Bundle *)

(** A morphism bundle: function + morphism proof. *)
Definition morph (X Y : qbsType R) :=
  { f : X -> Y | @qbs_morphism R X Y f }.

(** Extract the underlying function from a morphism bundle. *)
Definition morph_fun (X Y : qbsType R)
  (m : morph X Y) : X -> Y := proj1_sig m.

(** Extract the morphism proof from a bundle. *)
Definition morph_pf (X Y : qbsType R)
  (m : morph X Y) :
  @qbs_morphism R X Y (morph_fun m) :=
  proj2_sig m.

(** Constant morphism. *)
Definition morph_const (X Y : qbsType R)
  (y : Y) : morph X Y :=
  exist _ (fun _ => y)
    (@qbs_morphism_const R X Y y).

(** Pair morphism. *)
Definition morph_pair (W X Y : qbsType R)
  (f : morph W X) (g : morph W Y) :
  morph W (prodQ X Y) :=
  exist _
    (fun w =>
      (morph_fun f w, morph_fun g w))
    (qbs_morphism_pair
      (morph_pf f) (morph_pf g)).

(** Fst morphism. *)
Definition morph_fst (X Y Z : qbsType R)
  (f : morph Z (prodQ X Y)) :
  morph Z X.
Proof.
exists (fun z => fst (morph_fun f z)).
move=> alpha halpha.
have h :=
  @morph_pf Z (prodQ X Y) f alpha halpha.
rewrite /qbs_Mx /= in h.
exact: h.1.
Defined.

(** Snd morphism. *)
Definition morph_snd (X Y Z : qbsType R)
  (f : morph Z (prodQ X Y)) :
  morph Z Y.
Proof.
exists (fun z => snd (morph_fun f z)).
move=> alpha halpha.
have h :=
  @morph_pf Z (prodQ X Y) f alpha halpha.
rewrite /qbs_Mx /= in h.
exact: h.2.
Defined.

(** Variable morphism. *)
Definition morph_var G t (v : has_var G t) :
  morph (ctx_denot G) (type_denot t) :=
  exist _ (var_lookup v)
    (var_lookup_morphism v).

(** Package a function and morphism proof into
    qbsHomType (bundled QBS morphism). *)
Definition mk_hom (X Y : qbsType R)
  (f : X -> Y)
  (hf : @qbs_morphism R X Y f) :
  @qbsHomType R X Y :=
  HB.pack f
    (@isQBSMorphism.Build R X Y f
      (fun alpha ha => hf alpha ha)).

(** Lambda morphism helper: the inner
    morphism for a fixed environment. *)
Lemma morph_lam_inner G t1 t2
  (f_body :
    prodQ (type_denot t1) (ctx_denot G) ->
    type_denot t2)
  (h_body : @qbs_morphism R
    (prodQ (type_denot t1) (ctx_denot G))
    (type_denot t2) f_body)
  (env : ctx_denot G) :
  @qbs_morphism R (type_denot t1)
    (type_denot t2)
    (fun x => f_body (x, env)).
Proof.
move=> alpha halpha.
apply: h_body; split => /=.
- exact: halpha.
- exact: qbs_Mx_const.
Qed.

(** Lambda morphism: curries a body morphism
    on prodQ (type_denot t1) (ctx_denot G) into
    a morphism to the exponential QBS. *)
Definition morph_lam G t1 t2
  (body : morph
    (prodQ (type_denot t1) (ctx_denot G))
    (type_denot t2)) :
  morph (ctx_denot G)
    (expQ (type_denot t1) (type_denot t2)).
Proof.
set f_body := morph_fun body.
set h_body := @morph_pf _ _ body.
exists (fun env =>
  @mk_hom (type_denot t1) (type_denot t2)
    (fun x => f_body (x, env))
    (morph_lam_inner h_body env)).
move=> alpha halpha.
rewrite /qbs_Mx /= => gamma hgamma.
apply: h_body; split => /=.
- have h := hgamma.
  rewrite /qbs_Mx /= in h.
  exact: h.2.
- have h := hgamma.
  rewrite /qbs_Mx /= in h.
  exact: qbs_Mx_comp halpha h.1.
Defined.

(** Application morphism: evaluates a function
    morphism at an argument morphism. *)
Definition morph_app G t1 t2
  (sf : morph (ctx_denot G)
    (expQ (type_denot t1) (type_denot t2)))
  (sa : morph (ctx_denot G)
    (type_denot t1)) :
  morph (ctx_denot G) (type_denot t2).
Proof.
exists (fun env =>
  (morph_fun sf env :
    type_denot t1 -> type_denot t2)
  (morph_fun sa env)).
move=> alpha halpha.
have := @qbs_morphism_eval R
  (type_denot t1) (type_denot t2)
  (fun r => (morph_fun sf (alpha r),
             morph_fun sa (alpha r))).
apply.
split => /=.
- exact: @morph_pf _ _ sf alpha halpha.
- exact: @morph_pf _ _ sa alpha halpha.
Defined.

(** Return morphism: wraps a value in the
    probability monad via qbs_return. *)
Definition morph_ret G t
  (s : morph (ctx_denot G) (type_denot t)) :
  morph (ctx_denot G) (monadP (type_denot t)).
Proof.
exists (fun env =>
  qbs_return (type_denot t)
    (morph_fun s env)
    (uniform_prob (@ltr01 R))).
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
exact: @qbs_Mx_const.
Defined.

(** Sample uniform morphism: constant
    Uniform[0,1] distribution. *)
Definition morph_sample_uniform G :
  morph (ctx_denot G)
    (monadP (realQ R)).
Proof.
exists (fun _ => @qbs_uniform R).
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
exact: @measurable_id _ mR setT.
Defined.

(** Sample normal morphism: constant
    Normal(mu,sigma) distribution. *)
Definition morph_sample_normal G
  (mu sigma : R) (hsigma : (0 < sigma)%R) :
  morph (ctx_denot G)
    (monadP (realQ R)).
Proof.
exists (fun _ =>
  @qbs_normal_distribution R
    mu sigma hsigma).
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
exact: @measurable_id _ mR setT.
Defined.

(** * Denotational Semantics *)

(** Maps each expression to a morphism bundle
    (function + QBS morphism proof). *)
Fixpoint expr_sem G t (e : expr G t) :
  morph (ctx_denot G) (type_denot t) :=
  match e with
  | e_var _ _ v => morph_var v
  | e_real G0 r =>
      @morph_const (ctx_denot G0) (realQ R) r
  | e_bool G0 b =>
      @morph_const (ctx_denot G0) (boolQ R) b
  | e_tt G0 =>
      @morph_const (ctx_denot G0) (unitQ R) tt
  | e_pair _ _ _ e1 e2 =>
      morph_pair (expr_sem e1) (expr_sem e2)
  | e_fst _ _ _ e0 =>
      morph_fst (expr_sem e0)
  | e_snd _ _ _ e0 =>
      morph_snd (expr_sem e0)
  | e_lam _ _ _ body =>
      morph_lam (expr_sem body)
  | e_app _ _ _ ef ea =>
      morph_app (expr_sem ef) (expr_sem ea)
  | e_ret _ _ e0 =>
      morph_ret (expr_sem e0)
  | e_sample_uniform G0 =>
      morph_sample_uniform G0
  | e_sample_normal G0 mu sigma hs =>
      @morph_sample_normal G0 mu sigma hs
  end.

(** Extract the denotation function. *)
Definition expr_denot G t (e : expr G t) :
  ctx_denot G -> type_denot t :=
  morph_fun (expr_sem e).

(** The denotation is always a QBS morphism. *)
Lemma expr_morphism G t (e : expr G t) :
  @qbs_morphism R (ctx_denot G)
    (type_denot t) (expr_denot e).
Proof. exact: morph_pf. Qed.

(** * Examples *)

(** Example 1: constant function  fun x => 42 *)
Definition ex_const :
  expr nil (ppl_fun ppl_real ppl_real) :=
  e_lam (e_real _ 42%:R).

(** Example 2: pairing  fun x => (x, x) *)
Definition ex_dup :
  expr nil
    (ppl_fun ppl_real
      (ppl_prod ppl_real ppl_real)) :=
  e_lam
    (e_pair
      (e_var (var_here _ _))
      (e_var (var_here _ _))).

(** Example 3: higher-order  fun f x => f x *)
Definition ex_apply :
  expr nil
    (ppl_fun (ppl_fun ppl_real ppl_real)
      (ppl_fun ppl_real ppl_real)) :=
  e_lam
    (e_lam
      (e_app
        (e_var (var_there ppl_real
          (var_here _ _)))
        (e_var (var_here _ _)))).

(** Example 4: monadic return  fun x => ret x *)
Definition ex_ret :
  expr nil
    (ppl_fun ppl_real (ppl_prob ppl_real)) :=
  e_lam (e_ret (e_var (var_here _ _))).

(** Example 5: sample from Uniform[0,1] *)
Definition ex_uniform :
  expr nil (ppl_prob ppl_real) :=
  e_sample_uniform _.

(** Example 6: higher-order probabilistic program
    fun f => ret (f 0) — apply f to 0 and return
    the result in the monad *)
Definition ex_ho_prob :
  expr nil
    (ppl_fun (ppl_fun ppl_real ppl_real)
      (ppl_prob ppl_real)) :=
  e_lam
    (e_ret
      (e_app
        (e_var (var_here _ _))
        (e_real _ 0%R))).

(** All denotations are QBS morphisms. *)
Lemma ex_const_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot (ppl_fun ppl_real ppl_real))
    (expr_denot ex_const).
Proof. exact: expr_morphism. Qed.

Lemma ex_apply_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot
      (ppl_fun (ppl_fun ppl_real ppl_real)
        (ppl_fun ppl_real ppl_real)))
    (expr_denot ex_apply).
Proof. exact: expr_morphism. Qed.

Lemma ex_ho_prob_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot
      (ppl_fun (ppl_fun ppl_real ppl_real)
        (ppl_prob ppl_real)))
    (expr_denot ex_ho_prob).
Proof. exact: expr_morphism. Qed.

End ppl_denot.
