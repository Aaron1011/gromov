import Mathlib

/-!
# Norms of matrices

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

open scoped Matrix.Norms.L2Operator

lemma matrix_l2_norm_one {d: ℕ} (hd: 0 < d): ‖(1: Matrix (Fin d) (Fin d) ℂ)‖ = 1 := by
  rw [Matrix.l2_opNorm_def]
  have nonempty_fin: Nonempty (Fin d) := by
    refine Fin.pos_iff_nonempty.mp hd
  apply ContinuousLinearMap.opNorm_eq_of_bounds (by simp)
  .
    intro x
    simp
  . intro N hN mat_le
    simp at mat_le
    by_contra!
    have x_lt (x: EuclideanSpace ℂ (Fin d)) (x_ne: x ≠ 0): N * ‖x‖ < ‖x‖ := by
      apply mul_lt_of_lt_one_left
      . simpa using x_ne
      . exact this

    have nonzero_x: ∃ x: EuclideanSpace ℂ (Fin d), x ≠ 0 := by
      rw [← nontrivial_iff_exists_ne]
      infer_instance

    obtain ⟨x, x_ne⟩ := nonzero_x
    have my_lt := x_lt x x_ne
    have my_le := mat_le x
    linarith
