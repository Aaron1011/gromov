module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


@[expose] public section
set_option linter.style.longLine false

/-!
# `poly_tendsto` — a tactic for limits of polynomial-like quotients

Proves goals of the form
  `Filter.Tendsto (fun x => N x / D x) Filter.atTop (nhds 0)`
where `x` ranges over `ℕ` or `ℝ`, and `N`, `D` are polynomial-like expressions
in `x` (built from `+`, `-`, `*`, `/`, `^`, `x` itself and `x`-free atoms as
coefficients) whose degrees satisfy `deg N < deg D`.

Two proof strategies are tried in order:

1. **Polynomial reflection** (literal exponents only, top-level division):
   reify `N` and `D` into `Polynomial ℝ` terms, apply
   `Polynomial.div_tendsto_atTop_zero_of_degree_lt`, and discharge the degree
   side goals with `compute_degree!`. This handles denominators that are sums,
   like `(x + 1) ^ 3`.

2. **Monomial asymptotics** (supports symbolic `ℕ` exponents like `x ^ (d + 3)`,
   division nested inside products, and constant factors in the denominator):
   normalize the whole expression into a sum of monomials `c * x ^ e` over a
   single-monomial denominator, prove each `(fun x => c * x ^ eᵢ) =o[atTop]
   (fun x => x ^ e)` via `Asymptotics.isLittleO_pow_pow_atTop_of_lt` with the
   exponent comparison discharged by `omega`, combine with `IsLittleO.add`, and
   finish with `IsLittleO.tendsto_div_nhds_zero`. The function equality is
   discharged by `ring`.

A goal over `ℕ` is first reduced to one over `ℝ` by abstracting `(↑x : ℝ)` and
composing with `tendsto_natCast_atTop_atTop`. `Function.comp` in the goal is
unfolded and casts are normalized with `push_cast` beforehand.

If both strategies fail and every occurrence of the variable `x` lives inside a
common shifted subterm `x + c` (or `c + x`) with `c` constant — e.g.
`(x + c) ^ d / (x + c) ^ (d + 3)` — the limit is reduced to one in the shifted
variable via `tendsto_atTop_add_const_right` and the strategies are retried.
-/

open Filter Polynomial Asymptotics

namespace PolyTendsto

theorem tendsto_eval_div_zero (P Q : ℝ[X]) (dP dQ : ℕ)
    (hP : P.degree ≤ (dP : WithBot ℕ)) (hQ : Q.degree = (dQ : WithBot ℕ))
    (h : dP < dQ) :
    Tendsto (fun x => Polynomial.eval x P / Polynomial.eval x Q) atTop (nhds 0) := by
  apply Polynomial.div_tendsto_atTop_zero_of_degree_lt
  rw [hQ]
  exact lt_of_le_of_lt hP (by exact_mod_cast h)

theorem tendsto_natCast_comp {g : ℝ → ℝ}
    (h : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n : ℕ => g (n : ℝ)) atTop (nhds 0) :=
  h.comp tendsto_natCast_atTop_atTop

theorem tendsto_div_const_zero {f : ℝ → ℝ} (c : ℝ)
    (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun x => f x / c) atTop (nhds 0) := by
  simpa using h.div_const c

theorem tendsto_shift_comp {g : ℝ → ℝ} (c : ℝ)
    (h : Tendsto g atTop (nhds 0)) :
    Tendsto (fun x : ℝ => g (x + c)) atTop (nhds 0) :=
  h.comp (tendsto_atTop_add_const_right atTop c tendsto_id)

theorem tendsto_shift_comp' {g : ℝ → ℝ} (c : ℝ)
    (h : Tendsto g atTop (nhds 0)) :
    Tendsto (fun x : ℝ => g (c + x)) atTop (nhds 0) :=
  h.comp (tendsto_atTop_add_const_left atTop c tendsto_id)

public meta section

open Lean Elab Term Tactic Meta

/-! ## Path 1: polynomial reflection (literal exponents) -/

/-- Reify the real-valued expression `e` (in the free variable `x : ℝ`) into syntax
for a `Polynomial ℝ`, together with a syntactic upper bound on its degree.
Fails on symbolic exponents and on division. -/
partial def reifyPoly (x : Expr) (e : Expr) : TermElabM (Syntax.Term × ℕ) := do
  if e == x then
    return (← `((Polynomial.X : Polynomial ℝ)), 1)
  unless e.containsFVar x.fvarId! do
    let c ← exprToSyntax e
    return (← `((Polynomial.C ($c : ℝ) : Polynomial ℝ)), 0)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    let (pa, da) ← reifyPoly x a
    let (pb, db) ← reifyPoly x b
    return (← `($pa + $pb), max da db)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    let (pa, da) ← reifyPoly x a
    let (pb, db) ← reifyPoly x b
    return (← `($pa - $pb), max da db)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    let (pa, da) ← reifyPoly x a
    let (pb, db) ← reifyPoly x b
    return (← `($pa * $pb), da + db)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
    let some k := n.nat? |
      throwError "poly_tendsto: exponent is not a numeral: {n}"
    let (pa, da) ← reifyPoly x a
    return (← `($pa ^ $(quote k)), da * k)
  | (``Neg.neg, #[_, _, a]) =>
    let (pa, da) ← reifyPoly x a
    return (← `(-$pa), da)
  | _ => throwError "poly_tendsto: unsupported subexpression {e}"

/-! ## Path 2: monomial asymptotics (symbolic exponents) -/

/-- A formal monomial `± c₁ * ⋯ * cₖ * x ^ (s₁ + ⋯ + sₘ + expLit)` where the `cᵢ`
are `x`-free real terms and the `sⱼ` are (possibly symbolic) `ℕ` terms. -/
structure Mon where
  neg : Bool := false
  coeffs : List Syntax.Term := []
  expLit : Nat := 0
  expSyms : List Syntax.Term := []

def Mon.mul (a b : Mon) : Mon where
  neg := a.neg != b.neg
  coeffs := a.coeffs ++ b.coeffs
  expLit := a.expLit + b.expLit
  expSyms := a.expSyms ++ b.expSyms

def monsMul (as bs : List Mon) : TermElabM (List Mon) := do
  let r := as.flatMap fun a => bs.map a.mul
  if r.length > 64 then
    throwError "poly_tendsto: expression has too many monomials after expansion"
  return r

/-- Is this monomial list the constant `1` (trivial denominator)? -/
def monsTrivial : List Mon → Bool
  | [m] => !m.neg && m.coeffs.isEmpty && m.expLit == 0 && m.expSyms.isEmpty
  | _ => false

def Mon.negate (m : Mon) : Mon := { m with neg := !m.neg }

/-- Reify a real-valued expression in `x` as a formal rational function:
a pair (numerator monomials, denominator monomials). All rewriting steps used
here are unconditional field identities (no nonvanishing hypotheses needed),
so the final equality check can be discharged by `ring`. -/
partial def reifyRat (x : Expr) (e : Expr) : TermElabM (List Mon × List Mon) := do
  if e == x then
    return ([{ expLit := 1 }], [{}])
  unless e.containsFVar x.fvarId! do
    return ([{ coeffs := [← exprToSyntax e] }], [{}])
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    let (na, da) ← reifyRat x a
    let (nb, db) ← reifyRat x b
    unless monsTrivial da && monsTrivial db do
      throwError "poly_tendsto: cannot add fractions with nontrivial denominators in {e}"
    return (na ++ nb, [{}])
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    let (na, da) ← reifyRat x a
    let (nb, db) ← reifyRat x b
    unless monsTrivial da && monsTrivial db do
      throwError "poly_tendsto: cannot subtract fractions with nontrivial denominators in {e}"
    return (na ++ nb.map Mon.negate, [{}])
  | (``Neg.neg, #[_, _, a]) =>
    let (na, da) ← reifyRat x a
    return (na.map Mon.negate, da)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    let (na, da) ← reifyRat x a
    let (nb, db) ← reifyRat x b
    return (← monsMul na nb, ← monsMul da db)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
    let (na, da) ← reifyRat x a
    let (nb, db) ← reifyRat x b
    return (← monsMul na db, ← monsMul da nb)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
    match n.nat? with
    | some k =>
      let ra ← reifyRat x a
      let mut acc : List Mon × List Mon := ([{}], [{}])
      for _ in [0:k] do
        acc := (← monsMul acc.1 ra.1, ← monsMul acc.2 ra.2)
      return acc
    | none =>
      if a == x then
        return ([{ expSyms := [← exprToSyntax n] }], [{}])
      else
        throwError "poly_tendsto: symbolic exponent on a non-variable base in {e}"
  | _ => throwError "poly_tendsto: unsupported subexpression {e}"

/-- Exponent of a monomial as a `ℕ`-valued term. -/
def Mon.expTerm (m : Mon) : TermElabM Syntax.Term := do
  match m.expSyms with
  | [] => pure (quote m.expLit)
  | s :: rest => do
    let mut t := s
    for s' in rest do
      t ← `($t + $s')
    if m.expLit > 0 then
      t ← `($t + $(quote m.expLit))
    return t

/-- Coefficient of a monomial as an `ℝ`-valued term. -/
def Mon.coeffTerm (m : Mon) : TermElabM Syntax.Term := do
  let base ← match m.coeffs with
    | [] => `((1 : ℝ))
    | c :: rest => do
      let mut t := c
      for c' in rest do
        t ← `($t * $c')
      pure t
  if m.neg then `(-($base)) else pure base

/-- Build a proof term of `(fun x => Σᵢ cᵢ * x ^ eᵢ) =o[atTop] (fun x => x ^ eDen)`,
with each `eᵢ < eDen` discharged by `omega`. -/
def buildLittleO (numMons : List Mon) (eDen : Syntax.Term) : TermElabM Syntax.Term := do
  let mkMonTerm (m : Mon) : TermElabM Syntax.Term := do
    let c ← m.coeffTerm
    let e ← m.expTerm
    `(Asymptotics.IsLittleO.const_mul_left
        ((Asymptotics.isLittleO_pow_pow_atTop_of_lt (show ($e : ℕ) < ($eDen : ℕ) by omega) :
          (fun y : ℝ => y ^ ($e : ℕ)) =o[Filter.atTop] (fun y : ℝ => y ^ ($eDen : ℕ))))
        ($c : ℝ))
  match numMons with
  | [] => throwError "poly_tendsto: empty numerator"
  | m :: rest =>
    let mut acc ← mkMonTerm m
    for m' in rest do
      acc ← `(Asymptotics.IsLittleO.add $acc $(← mkMonTerm m'))
    return acc

/-- Collect subterms of `e` of the form `x + c` or `c + x` with `c` free of `x`.
Used to detect a "shifted variable" that all occurrences of `x` live inside. -/
partial def shiftCandidates (xv : Expr) (e : Expr) : Array Expr :=
  let sub := match e with
    | .app f a => shiftCandidates xv f ++ shiftCandidates xv a
    | .lam _ t b _ => shiftCandidates xv t ++ shiftCandidates xv b
    | .forallE _ t b _ => shiftCandidates xv t ++ shiftCandidates xv b
    | .letE _ t v b _ => shiftCandidates xv t ++ shiftCandidates xv v ++ shiftCandidates xv b
    | .mdata _ b => shiftCandidates xv b
    | .proj _ _ b => shiftCandidates xv b
    | _ => #[]
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, l, r]) =>
    if (l == xv && !r.containsFVar xv.fvarId!) ||
        (r == xv && !l.containsFVar xv.fvarId!) then
      sub.push e
    else sub
  | _ => sub

/-! ## The tactic -/

/-- Handle a goal `Tendsto f atTop (nhds 0)` with `f : ℝ → ℝ` a lambda.
If the direct proof paths fail, look for a shifted variable `x + c` covering all
occurrences of `x`, reduce to a limit in the shifted variable, and retry
(at most `fuel` times). -/
partial def realCase (f : Expr) (fuel : Nat := 2) : TacticM Unit := do
  let s ← saveState
  try
    realCaseDirect f
  catch e =>
    s.restore
    if fuel == 0 then throw e
    let .lam nm dom _ _ := f | throw e
    -- Find a shift `x + c` (or `c + x`) that all occurrences of `x` live inside.
    let shifted? ← withLocalDeclD nm dom fun xv => do
      let body := (f.beta #[xv]).headBeta
      let mut result : Option (Syntax.Term × Syntax.Term × Bool) := none
      for cand in shiftCandidates xv body do
        if result.isNone then
          let bodyAbs ← kabstract body cand
          unless bodyAbs.containsFVar xv.fvarId! do
            let gStx ← Term.exprToSyntax (Expr.lam `z (mkConst ``Real) bodyAbs .default)
            let (``HAdd.hAdd, #[_, _, _, _, l, r]) := cand.getAppFnArgs |
              throwError "poly_tendsto: internal error in shift detection"
            if l == xv then
              result := some (gStx, ← Term.exprToSyntax r, true)
            else
              result := some (gStx, ← Term.exprToSyntax l, false)
      pure result
    match shifted? with
    | none => throw e
    | some (gStx, cStx, xLeft) =>
      if xLeft then
        evalTactic (← `(tactic| refine PolyTendsto.tendsto_shift_comp ($cStx : ℝ) (g := $gStx) ?_))
      else
        evalTactic (← `(tactic| refine PolyTendsto.tendsto_shift_comp' ($cStx : ℝ) (g := $gStx) ?_))
      withMainContext do
        let tgt ← instantiateMVars (← (← getMainGoal).getType)
        let (``Filter.Tendsto, #[_, _, f', _, _]) := tgt.getAppFnArgs |
          throwError "poly_tendsto: internal error after shift reduction"
        realCase (← instantiateMVars f') (fuel - 1)
where
  /-- The two direct proof paths, with no shift reduction. -/
  realCaseDirect (f : Expr) : TacticM Unit := do
    let .lam nm dom _ _ := f |
      throwError "poly_tendsto: expected the function to be a lambda, got {f}"
    withLocalDeclD nm dom fun xv => do
      let body := (f.beta #[xv]).headBeta
      -- Path 1: structural polynomial reflection (literal exponents, top-level `/`).
      let pathA? : TermElabM (Option (Syntax.Term × ℕ × Syntax.Term × ℕ)) := do
        try
          match body.getAppFnArgs with
          | (``HDiv.hDiv, #[_, _, _, _, N, D]) =>
            let (P, dP) ← reifyPoly xv N
            let (Q, dQ) ← reifyPoly xv D
            if dP < dQ then return some (P, dP, Q, dQ) else return none
          | _ => return none
        catch _ => return none
      match ← pathA? with
      | some (P, dP, Q, dQ) =>
        let s ← saveState
        try
          evalTactic (← `(tactic|
            (refine Filter.Tendsto.congr ?_
              (PolyTendsto.tendsto_eval_div_zero $P $Q $(quote dP) $(quote dQ)
                (by compute_degree!) (by compute_degree!) (by norm_num))
             intro y
             simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
               Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C])))
        catch e =>
          -- e.g. the denominator's exact degree could not be certified; fall back to path 2.
          s.restore
          realCasePathB xv body <|> throw e
      | none => realCasePathB xv body
  /-- Path 2: normalize to monomials over a single-monomial denominator and
  prove via `IsLittleO`. -/
  realCasePathB (xv body : Expr) : TacticM Unit := do
    let (nums, dens) ← reifyRat xv body
    let [dmon] := dens |
      throwError "poly_tendsto: denominator does not normalize to a single monomial (got {dens.length}); this is only supported with literal exponents"
    let eDen ← dmon.expTerm
    let littleO ← buildLittleO nums eDen
    let base ← `(Asymptotics.IsLittleO.tendsto_div_nhds_zero $littleO)
    let proof ← if dmon.coeffs.isEmpty && !dmon.neg then pure base
      else do
        let c ← dmon.coeffTerm
        `(PolyTendsto.tendsto_div_const_zero ($c : ℝ) $base)
    evalTactic (← `(tactic| refine Filter.Tendsto.congr (fun y => ?_) $proof))
    evalTactic (← `(tactic| (try beta_reduce); ring))

/-- Core loop: dispatch on the domain of the function in the `Tendsto` goal. -/
partial def core : TacticM Unit := withMainContext do
  -- Normalize `Function.comp` and casts first.
  evalTactic (← `(tactic| try simp only [Function.comp_def]))
  evalTactic (← `(tactic| try push_cast))
  withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  match tgt.getAppFnArgs with
  | (``Filter.Tendsto, #[α, _β, f, _l₁, _l₂]) =>
    let f ← instantiateMVars f
    if α.isConstOf ``Nat then
      let .lam nm dom _ _ := f |
        throwError "poly_tendsto: expected the function to be a lambda, got {f}"
      let gStx ← withLocalDeclD nm dom fun n => do
        let body := (f.beta #[n]).headBeta
        let castN ← mkAppOptM ``Nat.cast #[mkConst ``Real, none, n]
        let bodyAbs ← kabstract body castN
        if bodyAbs.containsFVar n.fvarId! then
          throwError "poly_tendsto: variable {n} occurs outside a `ℝ`-cast in {body}"
        exprToSyntax (Expr.lam `y (mkConst ``Real) bodyAbs .default)
      evalTactic (← `(tactic| refine PolyTendsto.tendsto_natCast_comp (g := $gStx) ?_))
      withMainContext do
        let goal ← getMainGoal
        let tgt ← instantiateMVars (← goal.getType)
        let (``Filter.Tendsto, #[_, _, f, _, _]) := tgt.getAppFnArgs |
          throwError "poly_tendsto: internal error after cast reduction"
        realCase (← instantiateMVars f)
    else if α.isConstOf ``Real then
      realCase f
    else
      throwError "poly_tendsto: unsupported domain {α}"
  | _ => throwError "poly_tendsto: goal is not of the form `Filter.Tendsto f Filter.atTop (nhds 0)`"

/-- Prove goals of the form `Filter.Tendsto (fun x => N x / D x) Filter.atTop (nhds 0)`
for polynomial-like `N`, `D` with `deg N < deg D`, over `ℕ` or `ℝ`. Supports symbolic
`ℕ` exponents (e.g. `x ^ (d + 3)`) as long as the denominator is a single monomial,
in which case the degree comparisons are discharged by `omega`. -/
elab "poly_tendsto" : tactic => core

end

end PolyTendsto
