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
(*   e_bind            == monadic bind (see limitations below)      *)
(*   e_sample_uniform  == sample from Uniform[0,1]                 *)
(*   e_sample_normal   == sample from Normal(mu,sigma)             *)
(*   e_sample_bernoulli == sample from Bernoulli(p)                *)
(* ```                                                              *)
(*                                                                  *)
(* ## Bind faithfulness                                             *)
(*                                                                  *)
(* The denotation of [e_bind e1 e2] is faithful in two cases:       *)
(* - [e2] is syntactically [e_ret e0] -> dispatched to              *)
(*   morph_bind_ret                                                 *)
(* - [e2] is syntactically [e_sample_*] -> dispatched to            *)
(*   morph_bind_const                                               *)
(*                                                                  *)
(* For all other shapes, [expr_sem] dispatches to                   *)
(* morph_bind_fallback, which returns a constant placeholder        *)
(* distribution at type_point. This means [expr_morphism] proves    *)
(* the result is a QBS morphism but the underlying function does    *)
(* NOT compute the program semantics.                               *)
(*                                                                  *)
(* The fundamental obstacle is that monadP_random_pw (pointwise)    *)
(* does not imply monadP_random (strong). Discharging the diagonal  *)
(* randomness obligation for general bind requires either the      *)
(* strong morphism condition or quotient types, neither of which   *)
(* is available without significant rework.                         *)
(*                                                                  *)
(* See expr_sem_bind_ret, expr_sem_bind_sample_uniform, and         *)
(* expr_sem_bind_sample_bernoulli for the equation lemmas that      *)
(* hold by reflexivity in the faithful cases.                       *)
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
  | ppl_sum (t1 t2 : ppl_type)
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
  | ppl_sum t1 t2 =>
      coprodQ (type_denot t1) (type_denot t2)
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
  (** Monadic bind: sequences a probabilistic
      computation with a continuation that may
      reference the bound value in its context. *)
  | e_bind : forall G t1 t2,
      expr G (ppl_prob t1) ->
      expr (t1 :: G) (ppl_prob t2) ->
      expr G (ppl_prob t2)
  (** Sample from Uniform[0,1]. *)
  | e_sample_uniform : forall G,
      expr G (ppl_prob ppl_real)
  (** Sample from Normal(mu,sigma). *)
  | e_sample_normal : forall G
      (mu sigma : R) (hsigma : (0 < sigma)%R),
      expr G (ppl_prob ppl_real)
  (** Sample from Bernoulli(p) with 0 <= p <= 1. *)
  | e_sample_bernoulli : forall G (p : R)
      (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R),
      expr G (ppl_prob ppl_bool)
  (** Sum type: left injection. *)
  | e_inl : forall G t1 t2,
      expr G t1 -> expr G (ppl_sum t1 t2)
  (** Sum type: right injection. *)
  | e_inr : forall G t1 t2,
      expr G t2 -> expr G (ppl_sum t1 t2)
  (** Sum type: case analysis. *)
  | e_case : forall G t1 t2 t,
      expr G (ppl_sum t1 t2) ->
      expr (t1 :: G) t ->
      expr (t2 :: G) t ->
      expr G t.

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
Qed.

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
Qed.

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
Qed.

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
Qed.

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
Qed.

(** Monadic bind where the continuation is a
    pure return: [do x <- m1; return (m2 x)].
    The diagonal randomness is discharged using
    [qbs_bind_alpha_random_return] together with
    the morphism proof of [m2]. This is the
    currently supported form of monadic bind:
    the general case needs the strong morphism
    condition, which cannot be discharged
    generically from the pointwise condition of
    [monadP] (see [probability_qbs.v]). *)
Definition morph_bind_ret G t1 t2
  (m1 : morph (ctx_denot G)
    (monadP (type_denot t1)))
  (m2 : morph (ctx_denot (t1 :: G))
    (type_denot t2)) :
  morph (ctx_denot G)
    (monadP (type_denot t2)).
Proof.
set f1 := morph_fun m1.
set h1 := @morph_pf _ _ m1.
set f2 := morph_fun m2.
set h2 := @morph_pf _ _ m2.
pose mu0 : probability mR R :=
  uniform_prob (@ltr01 R).
pose k env : type_denot t1 ->
  qbs_prob (type_denot t2) :=
  fun x => qbs_return (type_denot t2)
    (f2 (x, env)) mu0.
have diag : forall env,
  @qbs_Mx R (type_denot t2)
    (fun r => qbs_prob_alpha
      (k env (qbs_prob_alpha (f1 env) r)) r).
  move=> env; rewrite /k /=.
  apply: h2 => /=; split.
  - exact: (qbs_prob_alpha_random (f1 env)).
  - exact: qbs_Mx_const.
exists (fun env =>
  qbs_bind (type_denot t1) (type_denot t2)
    (f1 env) (k env) (diag env)).
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
rewrite /k /=.
exact: (diag (alpha r)).
Qed.

(** Monadic bind where the continuation is a
    constant probability distribution [p] (i.e.
    does not reference the bound variable). For
    such continuations the diagonal randomness
    is discharged by [qbs_bind_alpha_random_const],
    and the overall map [env ↦ bind (m1 env) _]
    is a morphism because [p] is independent of
    [env]. This captures the faithful denotation
    of [do _ <- m1; sample_*] where the sampler
    is a constant (no dependence on the bound
    variable). *)
Definition morph_bind_const G t1 t2
  (m1 : morph (ctx_denot G)
    (monadP (type_denot t1)))
  (p : qbs_prob (type_denot t2)) :
  morph (ctx_denot G)
    (monadP (type_denot t2)).
Proof.
exists (fun env =>
  qbs_bind (type_denot t1) (type_denot t2)
    (morph_fun m1 env)
    (fun _ => p)
    (@qbs_bind_alpha_random_const R
      (type_denot t1) (type_denot t2)
      (qbs_prob_alpha (morph_fun m1 env) 0%R)
      (fun _ => p))).
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
exact: (qbs_prob_alpha_random p).
Qed.

(** Canonical inhabitant of each PPL type. Used
    only to build a trivial default probability
    for the non-supported form of [e_bind]. *)
Fixpoint type_point (t : ppl_type) : type_denot t :=
  match t with
  | ppl_real => 0%R
  | ppl_bool => false
  | ppl_unit => tt
  | ppl_prod t1 t2 =>
      (type_point t1, type_point t2)
  | ppl_sum t1 t2 =>
      inl (type_point t1)
  | ppl_fun t1 t2 =>
      @mk_hom (type_denot t1) (type_denot t2)
        (fun _ => type_point t2)
        (@qbs_morphism_const R
          (type_denot t1) (type_denot t2)
          (type_point t2))
  | ppl_prob t' =>
      qbs_return (type_denot t')
        (type_point t')
        (uniform_prob (@ltr01 R))
  end.

(** [morph_bind_fallback] returns a CONSTANT placeholder distribution
    at the canonical inhabitant [type_point t2]. It is used as the
    last-resort case in [expr_sem] for [e_bind] when the continuation
    cannot be classified by [try_morph_of_ret] or [try_prob_of_sample].

    WARNING: When [expr_sem] dispatches to this fallback, the
    resulting denotation is NOT the program semantics. It is a valid
    QBS morphism (so [expr_morphism] proves the morphism property),
    but the underlying function ignores the actual computation.

    For programs that fall outside the faithful cases, use the
    explicit combinators [morph_bind_ret] and [morph_bind_const]
    directly, or restructure the program to use one of the
    faithful shapes. *)
Definition morph_bind_fallback G t2 :
  morph (ctx_denot G)
    (monadP (type_denot t2)).
Proof.
exists (fun _ =>
  qbs_return (type_denot t2)
    (type_point t2)
    (uniform_prob (@ltr01 R))).
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
exact: qbs_Mx_const.
Qed.

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
Qed.

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
Qed.

(** Sample bernoulli morphism: constant
    Bernoulli(p) distribution on [boolQ R]. *)
Definition morph_sample_bernoulli G (p : R)
  (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) :
  morph (ctx_denot G) (monadP (boolQ R)).
Proof.
exists (fun _ => @qbs_bernoulli R p hp0 hp1).
move=> alpha halpha.
rewrite /qbs_Mx /= => r.
exact: measurable_fun_ltr
  (@measurable_id _ mR setT)
  (@measurable_cst _ _ mR mR setT p).
Qed.

(** Left injection morphism: lifts a morphism
    into a sum type via [inl]. *)
Definition morph_inl G t1 t2
  (s : morph (ctx_denot G) (type_denot t1)) :
  morph (ctx_denot G)
    (coprodQ (type_denot t1) (type_denot t2)).
Proof.
exists (fun env => inl (morph_fun s env)).
move=> alpha halpha.
have h := @morph_pf _ _ s alpha halpha.
rewrite /qbs_Mx /=; left.
exists (fun r => morph_fun s (alpha r)).
split => //.
Qed.

(** Right injection morphism: lifts a morphism
    into a sum type via [inr]. *)
Definition morph_inr G t1 t2
  (s : morph (ctx_denot G) (type_denot t2)) :
  morph (ctx_denot G)
    (coprodQ (type_denot t1) (type_denot t2)).
Proof.
exists (fun env => inr (morph_fun s env)).
move=> alpha halpha.
have h := @morph_pf _ _ s alpha halpha.
rewrite /qbs_Mx /=; right; left.
exists (fun r => morph_fun s (alpha r)).
split => //.
Qed.

(** Case analysis over a sum inside a context.
    Given a scrutinee morphism [ss] producing
    [coprodQ X Y] from the context [Γ], a
    continuation [s1] on [t1::G] and a
    continuation [s2] on [t2::G], produces a
    morphism [Γ -> Z] by case analysis on the
    value of [ss]. *)
Definition morph_case G t1 t2 t
  (ss : morph (ctx_denot G)
    (coprodQ (type_denot t1) (type_denot t2)))
  (s1 : morph (ctx_denot (t1 :: G))
    (type_denot t))
  (s2 : morph (ctx_denot (t2 :: G))
    (type_denot t)) :
  morph (ctx_denot G) (type_denot t).
Proof.
unshelve eexists.
  refine (fun env =>
    match morph_fun ss env with
    | inl x => morph_fun s1 (x, env)
    | inr y => morph_fun s2 (y, env)
    end).
move=> alpha halpha.
have hscr :=
  @morph_pf _ _ ss alpha halpha.
rewrite /qbs_Mx /= in hscr.
rewrite /qbs_Mx /=.
pose target :=
  fun r : mR =>
    match morph_fun ss (alpha r) with
    | inl x => morph_fun s1 (x, alpha r)
    | inr y => morph_fun s2 (y, alpha r)
    end.
change
  (@qbs_Mx R (type_denot t) target).
case: hscr =>
  [[a [ha hdef]]
  |[[b' [hb hdef]]
   |[P [a [b' [hP [ha [hb hdef]]]]]]]].
- (* scrutinee factors through inl *)
  have -> :
    target = (fun r => morph_fun s1 (a r, alpha r)).
    apply: boolp.funext => r.
    rewrite /target /=.
    have htmp := hdef r.
    rewrite /= in htmp.
    by rewrite htmp.
  apply: (@morph_pf _ _ s1) => /=; split => //.
- (* scrutinee factors through inr *)
  have -> :
    target = (fun r => morph_fun s2 (b' r, alpha r)).
    apply: boolp.funext => r.
    rewrite /target /=.
    have htmp := hdef r.
    rewrite /= in htmp.
    by rewrite htmp.
  apply: (@morph_pf _ _ s2) => /=; split => //.
- (* scrutinee is a measurable gluing *)
  have -> :
    target = (fun r => if P r
      then morph_fun s1 (a r, alpha r)
      else morph_fun s2 (b' r, alpha r)).
    apply: boolp.funext => r.
    rewrite /target /=.
    have htmp := hdef r.
    rewrite /= in htmp.
    rewrite htmp; by case: (P r).
  set Pn : mR -> nat :=
    fun r => if P r then 0%N else 1%N.
  set Gi : nat -> mR -> type_denot t :=
    fun i =>
      if i == 0%N
      then fun r => morph_fun s1 (a r, alpha r)
      else fun r => morph_fun s2 (b' r, alpha r).
  have -> :
    (fun r : mR => if P r
      then morph_fun s1 (a r, alpha r)
      else morph_fun s2 (b' r, alpha r)) =
    (fun r => Gi (Pn r) r).
    apply: boolp.funext => r.
    rewrite /Gi /Pn; by case: (P r).
  apply: (@qbs_Mx_glue R (type_denot t) Pn Gi).
    rewrite /Pn.
    apply: (measurable_fun_ifT hP);
      exact: measurable_cst.
  move=> i; rewrite /Gi.
  case: (i == 0%N).
  + apply: (@morph_pf _ _ s1) => /=; split => //.
  + apply: (@morph_pf _ _ s2) => /=; split => //.
Qed.

(** * Denotational Semantics *)

(** Helper: extract, when [e] is syntactically
    of the form [e_ret e0], the morphism
    denotation of [e0] via the recursive
    [expr_sem]. The [return] clause of the
    dependent match exposes the type index so
    that in the [e_ret] branch the produced
    morphism has the right codomain. *)
Definition try_morph_of_ret
  (rec : forall G' t' (e' : expr G' t'),
    morph (ctx_denot G') (type_denot t'))
  G tp (e : expr G tp) :
  option (match tp with
          | ppl_prob t' =>
              morph (ctx_denot G) (type_denot t')
          | _ => unit
          end) :=
  match e in expr G' tp'
  return option (match tp' with
                 | ppl_prob t' =>
                     morph (ctx_denot G')
                       (type_denot t')
                 | _ => unit
                 end)
  with
  | e_ret G0 t0 e0 => Some (rec _ _ e0)
  | _ => None
  end.

(** Helper: extract, when [e] is syntactically a
    constant sampler ([e_sample_uniform],
    [e_sample_normal] or [e_sample_bernoulli]),
    the underlying [qbs_prob] distribution. The
    [return] clause exposes the type index so
    that each branch delivers the correct
    probability. These samplers are independent
    of the ambient context, so they give a
    continuation that does not reference the
    bound variable and the bind simplifies. *)
Definition try_prob_of_sample
  G tp (e : expr G tp) :
  option (match tp with
          | ppl_prob t' =>
              qbs_prob (type_denot t')
          | _ => unit
          end) :=
  match e in expr G' tp'
  return option (match tp' with
                 | ppl_prob t' =>
                     qbs_prob (type_denot t')
                 | _ => unit
                 end)
  with
  | e_sample_uniform _ =>
      Some (@qbs_uniform R)
  | e_sample_normal _ mu sigma hs =>
      Some (@qbs_normal_distribution R mu sigma hs)
  | e_sample_bernoulli _ p hp0 hp1 =>
      Some (@qbs_bernoulli R p hp0 hp1)
  | _ => None
  end.

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
  | e_bind G0 t1 t2 e1 e2 =>
      (** When [e2] is syntactically [e_ret e0],
          dispatch to [morph_bind_ret] for a
          faithful denotation. When [e2] is a
          constant sampler (uniform, normal,
          bernoulli), dispatch to
          [morph_bind_const] using the constant
          probability. Otherwise fall back to a
          placeholder since the general bind
          cannot be discharged from the pointwise
          morphism condition of [monadP]. *)
      match try_morph_of_ret
        (@expr_sem) e2
        : option (morph
            (ctx_denot (t1 :: G0))
            (type_denot t2))
      with
      | Some m2 => morph_bind_ret (expr_sem e1) m2
      | None =>
          match try_prob_of_sample e2
            : option (qbs_prob (type_denot t2))
          with
          | Some p =>
              @morph_bind_const G0 t1 t2
                (expr_sem e1) p
          | None => morph_bind_fallback G0 t2
          end
      end
  | e_sample_uniform G0 =>
      morph_sample_uniform G0
  | e_sample_normal G0 mu sigma hs =>
      @morph_sample_normal G0 mu sigma hs
  | e_sample_bernoulli G0 p hp0 hp1 =>
      @morph_sample_bernoulli G0 p hp0 hp1
  | e_inl _ _ t2 e0 =>
      @morph_inl _ _ t2 (expr_sem e0)
  | e_inr _ t1 _ e0 =>
      @morph_inr _ t1 _ (expr_sem e0)
  | e_case _ _ _ _ es e1 e2 =>
      morph_case (expr_sem es)
        (expr_sem e1) (expr_sem e2)
  end.

(** Extract the denotation function. *)
Definition expr_denot G t (e : expr G t) :
  ctx_denot G -> type_denot t :=
  morph_fun (expr_sem e).

(** [expr_morphism] proves that [expr_denot e] is a QBS morphism for
    every well-typed expression [e]. This is structural soundness:
    the denotation lives in the right type. It does NOT prove
    semantic faithfulness for [e_bind] outside the supported shapes
    (see the bind faithfulness section in the file header).

    A semantic correctness theorem of the form
    [expr_denot e = intended_meaning e] is not currently provided. *)
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

(** Example 7: monadic bind
    [do x <- sample uniform; return x]. Since
    the continuation is syntactically [e_ret],
    [expr_sem] dispatches to [morph_bind_ret]
    and the denotation is faithful (see
    [expr_sem_ex_bind] below). *)
Definition ex_bind :
  expr nil (ppl_prob ppl_real) :=
  e_bind
    (e_sample_uniform nil)
    (e_ret (e_var (var_here nil ppl_real))).

Lemma ex_bind_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot (ppl_prob ppl_real))
    (expr_denot ex_bind).
Proof. exact: expr_morphism. Qed.

(** A faithful denotation of
    [do x <- sample uniform; return x] using
    [morph_bind_ret] directly. Now that
    [expr_sem] detects the [bind/return] shape,
    this is equal to [expr_sem ex_bind]. *)
Definition ex_bind_faithful :
  morph (ctx_denot nil)
    (monadP (realQ R)) :=
  @morph_bind_ret nil ppl_real ppl_real
    (morph_sample_uniform nil)
    (morph_var (var_here nil ppl_real)).

Lemma ex_bind_faithful_morphism :
  @qbs_morphism R (ctx_denot nil)
    (monadP (realQ R))
    (morph_fun ex_bind_faithful).
Proof. exact: morph_pf. Qed.

(** [expr_sem] on a [bind/return] program is
    definitionally the faithful denotation via
    [morph_bind_ret]. *)
Lemma expr_sem_ex_bind :
  expr_sem ex_bind = ex_bind_faithful.
Proof. reflexivity. Qed.

(** General equation: when the continuation of
    a [e_bind] is syntactically [e_ret e0], the
    denotation dispatches to [morph_bind_ret]. *)
Lemma expr_sem_bind_ret G t1 t2
  (e1 : expr G (ppl_prob t1))
  (e0 : expr (t1 :: G) t2) :
  expr_sem (e_bind e1 (e_ret e0)) =
  morph_bind_ret (expr_sem e1) (expr_sem e0).
Proof. reflexivity. Qed.

(** General equation: when the continuation of a
    [e_bind] is syntactically [e_sample_uniform],
    dispatch to [morph_bind_const] with the
    uniform distribution. *)
Lemma expr_sem_bind_sample_uniform G t1
  (e1 : expr G (ppl_prob t1)) :
  expr_sem
    (e_bind e1 (e_sample_uniform (t1 :: G))) =
  @morph_bind_const G t1 ppl_real
    (expr_sem e1) (@qbs_uniform R).
Proof. reflexivity. Qed.

(** Analogous equation for [e_sample_bernoulli]. *)
Lemma expr_sem_bind_sample_bernoulli G t1
  (e1 : expr G (ppl_prob t1))
  (p : R) (hp0 : (0 <= p)%R) (hp1 : (p <= 1)%R) :
  expr_sem
    (e_bind e1
      (@e_sample_bernoulli (t1 :: G) p hp0 hp1)) =
  @morph_bind_const G t1 ppl_bool
    (expr_sem e1)
    (@qbs_bernoulli R p hp0 hp1).
Proof. reflexivity. Qed.

(** Example 8: sample from Bernoulli(0). *)
Lemma ex_bernoulli_p0 : (0 <= 0 :> R)%R.
Proof. by []. Qed.

Definition ex_bernoulli :
  expr nil (ppl_prob ppl_bool) :=
  @e_sample_bernoulli nil 0%R ex_bernoulli_p0 ler01.

Lemma ex_bernoulli_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot (ppl_prob ppl_bool))
    (expr_denot ex_bernoulli).
Proof. exact: expr_morphism. Qed.

(** Example 9: left injection into a sum type.
    [inl true : bool + real]. *)
Definition ex_inl_use :
  expr nil (ppl_sum ppl_bool ppl_real) :=
  @e_inl nil ppl_bool ppl_real (e_bool _ true).

Lemma ex_inl_use_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot (ppl_sum ppl_bool ppl_real))
    (expr_denot ex_inl_use).
Proof. exact: expr_morphism. Qed.

(** Example 10: right injection into a sum. *)
Definition ex_inr_use :
  expr nil (ppl_sum ppl_bool ppl_real) :=
  @e_inr nil ppl_bool ppl_real (e_real _ 42%:R).

Lemma ex_inr_use_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot (ppl_sum ppl_bool ppl_real))
    (expr_denot ex_inr_use).
Proof. exact: expr_morphism. Qed.

(** Example: monadic bind with a constant
    sampler continuation
    [do _ <- sample uniform; sample uniform].
    Dispatched to [morph_bind_const]. *)
Definition ex_bind_sample :
  expr nil (ppl_prob ppl_real) :=
  e_bind
    (e_sample_uniform nil)
    (e_sample_uniform (ppl_real :: nil)).

Lemma ex_bind_sample_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot (ppl_prob ppl_real))
    (expr_denot ex_bind_sample).
Proof. exact: expr_morphism. Qed.

(** Example 11: case analysis on a sum type.
    [case (inl true) of
       | inl b => b
       | inr _ => false]. *)
Definition ex_case :
  expr nil ppl_bool :=
  e_case
    ex_inl_use
    (e_var (var_here _ ppl_bool))
    (e_bool _ false).

Lemma ex_case_morphism :
  @qbs_morphism R (ctx_denot nil)
    (type_denot ppl_bool)
    (expr_denot ex_case).
Proof. exact: expr_morphism. Qed.

End ppl_denot.
