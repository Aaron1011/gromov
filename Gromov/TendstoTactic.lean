import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false

/-!
# `poly_tendsto` — a tactic for limits of polynomial-like quotients

Proves goals of the form
  `Filter.Tendsto (fun x => N x / D x) Filter.atTop (nhds 0)`
where `x` ranges over `ℕ` or `ℝ`, and `N`, `D` are polynomial-like literal
expressions in `x` (built from `+`, `-`, `*`, `^` with numeral exponents, `-`(neg),
`x` itself and `x`-free atoms) whose syntactic degrees satisfy `deg N < deg D`.

Strategy: reify `N` and `D` into `Polynomial ℝ` terms, apply
`Polynomial.div_tendsto_atTop_zero_of_degree_lt`, and discharge the degree side
goals with `compute_degree!`. A goal over `ℕ` is first reduced to one over `ℝ`
by composing with `tendsto_natCast_atTop_atTop`.
-/

open Filter Polynomial

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

open Lean Elab Term Tactic Meta

/-- Reify the real-valued expression `e` (in the free variable `x : ℝ`) into syntax
for a `Polynomial ℝ`, together with a syntactic upper bound on its degree. -/
partial def reify (x : Expr) (e : Expr) : TermElabM (Syntax.Term × ℕ) := do
  if e == x then
    return (← `((Polynomial.X : Polynomial ℝ)), 1)
  unless e.containsFVar x.fvarId! do
    let c ← exprToSyntax e
    return (← `((Polynomial.C ($c : ℝ) : Polynomial ℝ)), 0)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    let (pa, da) ← reify x a
    let (pb, db) ← reify x b
    return (← `($pa + $pb), max da db)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    let (pa, da) ← reify x a
    let (pb, db) ← reify x b
    return (← `($pa - $pb), max da db)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    let (pa, da) ← reify x a
    let (pb, db) ← reify x b
    return (← `($pa * $pb), da + db)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
    let some k := n.nat? |
      throwError "poly_tendsto: exponent is not a numeral: {n}"
    let (pa, da) ← reify x a
    return (← `($pa ^ $(quote k)), da * k)
  | (``Neg.neg, #[_, _, a]) =>
    let (pa, da) ← reify x a
    return (← `(-$pa), da)
  | _ => throwError "poly_tendsto: unsupported subexpression {e}"

/-- Core loop: dispatch on the domain of the function in the `Tendsto` goal. -/
partial def core : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  match tgt.getAppFnArgs with
  | (``Filter.Tendsto, #[α, _β, f, _l₁, _l₂]) =>
    let f ← instantiateMVars f
    let .lam nm dom _ _ := f |
      throwError "poly_tendsto: expected the function to be a lambda, got {f}"
    if α.isConstOf ``Nat then
      -- Reduce to a real-variable limit by abstracting `(↑x : ℝ)`.
      let gStx ← withLocalDeclD nm dom fun n => do
        let body := f.beta #[n]
        let castN ← mkAppOptM ``Nat.cast #[mkConst ``Real, none, n]
        let bodyAbs ← kabstract body castN
        if bodyAbs.containsFVar n.fvarId! then
          throwError "poly_tendsto: variable {n} occurs outside a `ℝ`-cast in {body}"
        exprToSyntax (Expr.lam `y (mkConst ``Real) bodyAbs .default)
      evalTactic (← `(tactic| refine PolyTendsto.tendsto_natCast_comp (g := $gStx) ?_))
      core
    else if α.isConstOf ``Real then
      withLocalDeclD nm dom fun xv => do
        let body := f.beta #[xv]
        let (``HDiv.hDiv, #[_, _, _, _, N, D]) := body.getAppFnArgs |
          throwError "poly_tendsto: expected a division, got {body}"
        let (P, dP) ← reify xv N
        let (Q, dQ) ← reify xv D
        unless dP < dQ do
          throwError "poly_tendsto: numerator degree bound {dP} is not less than denominator degree bound {dQ}"
        evalTactic (← `(tactic|
          (refine Filter.Tendsto.congr ?_
            (PolyTendsto.tendsto_eval_div_zero $P $Q $(quote dP) $(quote dQ)
              (by compute_degree!) (by compute_degree!) (by norm_num))
           intro y
           simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
             Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C])))
    else
      throwError "poly_tendsto: unsupported domain {α}"
  | _ => throwError "poly_tendsto: goal is not of the form `Filter.Tendsto f Filter.atTop (nhds 0)`"

/-- Prove goals of the form `Filter.Tendsto (fun x => N x / D x) Filter.atTop (nhds 0)`
for polynomial-like `N`, `D` with `deg N < deg D`, over `ℕ` or `ℝ`. -/
elab "poly_tendsto" : tactic => core

end PolyTendsto
