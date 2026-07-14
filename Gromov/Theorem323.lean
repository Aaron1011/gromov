import Mathlib
import Mathlib.Algebra.Group.Gromov.Defs

set_option linter.style.cdot false
set_option linter.style.whitespace false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V] (hV : Even (Module.finrank V))  [V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]


noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)

noncomputable def Q_R_lin (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R (fun g => u.val g) (fun g => v.val g)
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}

noncomputable def V_basis := Module.Basis.ofVectorSpace ℝ V
noncomputable def Q_R_matrix (R: ℝ) := ((Q_R_lin R (V := V)).toMatrix₂ V_basis V_basis)

omit V_decidable in
noncomputable def my_expr (d: ℝ) (R : ℕ) := #(S ^ R) * ((Q_R_matrix R (V := V)).det ^ ((1 : ℝ) / Module.finrank ℝ V)) / (R ^ d)

omit V_decidable in
noncomputable def growth_bound (d: ℝ) := Filter.liminf (fun (R: ℕ) => ENNReal.ofReal (my_expr (V := V) d R)) (Filter.atTop) ≠ ⊤


-- Todo - is the better way to declare theorem_3_23 so that the constant is not allowed to depend on V?
omit V in
structure V_Data where
  V: Submodule ℝ LipschitzH
  hV: FiniteDimensional ℝ V
  (V_even : Even (Module.finrank ℝ V))
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)


omit V in
lemma theorem_3_23 (d: ℝ): ∃ C: ℕ, ∀ data: V_Data, growth_bound (V := data.V) (V_finite := data.hV) (V_decidable := data.V_decidable) d → (Module.finrank ℝ data.V) < C := by
  have C: ℕ := sorry
  use C
  intro data h_growth

  sorry
