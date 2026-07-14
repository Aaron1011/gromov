import Mathlib.Algebra.Group.Gromov.TendstoTactic

-- Tests for the poly_tendsto tactic (see Mathlib/Algebra/Group/Gromov/TendstoTactic.lean)
example : Filter.Tendsto
    (fun x : ℕ ↦ (1 + (↑x + 1) * 2 + (↑x + 1) ^ 2) / (↑x + 1) ^ 3 : ℕ → ℝ)
    Filter.atTop (nhds 0) := by
  poly_tendsto

example : Filter.Tendsto (fun x : ℝ ↦ (x ^ 2 + 3 * x) / (x ^ 3 + 1))
    Filter.atTop (nhds 0) := by
  poly_tendsto

example : Filter.Tendsto (fun x : ℝ ↦ x / (x ^ 2 - 5)) Filter.atTop (nhds 0) := by
  poly_tendsto

example (a : ℝ) : Filter.Tendsto (fun x : ℕ ↦ (a * ↑x + 3) / ((↑x + 2) ^ 2))
    Filter.atTop (nhds 0) := by
  poly_tendsto

example : Filter.Tendsto (fun x : ℝ ↦ 5 / (x + 1)) Filter.atTop (nhds 0) := by
  poly_tendsto

example : Filter.Tendsto (fun x : ℝ ↦ (-x ^ 2 + 3) / (x ^ 3 - x)) Filter.atTop (nhds 0) := by
  poly_tendsto

example (c : ℝ) : Filter.Tendsto (fun x : ℕ ↦ (c * (↑x + 1) ^ 2 - ↑x) / ((↑x + 1) ^ 2 * (↑x - 3)))
    Filter.atTop (nhds 0) := by
  poly_tendsto

-- Symbolic exponents (path 2)
example (dbc a : ℝ) (d : ℕ) : Filter.Tendsto
    (fun R : ℕ ↦ dbc * (1 + ↑R) ^ 2 * (a * ↑R ^ d) / ↑R ^ (d + 3))
    Filter.atTop (nhds 0) := by
  poly_tendsto

-- the exact shape from Harmonic.lean (ℕ-valued constants, cast)
example (dbc : ℝ) (a d : ℕ) : Filter.Tendsto
    (fun R : ℕ ↦ dbc * (1 + ↑R) ^ 2 * (↑a * ↑R ^ d) / ↑R ^ (d + 3))
    Filter.atTop (nhds 0) := by
  poly_tendsto

-- composition form, symbolic exponents
example (a : ℝ) (d : ℕ) : Filter.Tendsto
    ((fun n : ℝ ↦ a * n ^ d / n ^ (d + 1)) ∘ (fun n : ℕ ↦ (n : ℝ)))
    Filter.atTop (nhds 0) := by
  poly_tendsto

-- real domain, symbolic exponents
example (d : ℕ) : Filter.Tendsto (fun x : ℝ ↦ (x ^ d + x ^ (d + 1)) / x ^ (d + 2))
    Filter.atTop (nhds 0) := by
  poly_tendsto

-- constant factor in the denominator
example (d : ℕ) : Filter.Tendsto (fun x : ℝ ↦ x ^ d / (2 * x ^ (d + 2)))
    Filter.atTop (nhds 0) := by
  poly_tendsto

-- division nested inside a product
example (a : ℝ) (d : ℕ) : Filter.Tendsto (fun x : ℝ ↦ a * (x ^ d / x ^ (d + 1)))
    Filter.atTop (nhds 0) := by
  poly_tendsto
