module

public import Mathlib

/-!
# Positive semidefinite matrices

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

@[expose] public section

-- TODO - generalize and upstream
-- Based on https://math.stackexchange.com/questions/1101184/show-that-if-x-succeq-y-then-detx-ge-dety
lemma matrix_psd_det_one {n: Type*} [Fintype n] [DecidableEq n] (A: Matrix n n ℝ) (ha: A.PosSemidef): 1 ≤ (A + 1).det := by
  have foo := ha.isHermitian.spectral_theorem
  have H := ha.isHermitian
  simp at foo
  rw [foo]
  conv =>
    rhs
    arg 1
    equals H.eigenvectorUnitary * ((Matrix.diagonal H.eigenvalues) + 1) * (star H.eigenvectorUnitary) =>
      rw [mul_add, add_mul]
      simp

  rw [Matrix.det_conj_of_mul_eq_one]
  .
    rw [← Matrix.diagonal_one']
    rw [Matrix.diagonal_add]
    simp
    apply Finset.one_le_prod
    intro i _
    have foo := ha.eigenvalues_nonneg
    grind
  . simp
  . simp
