import Mathlib
import Gromov.ToMathlib.LinearAlgebra.Matrix.PosDef
import Gromov.ToMathlib.LinearAlgebra.Matrix.ToMatrix

/-!
# Determinants of matrices of bilinear forms

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

/-- The determinant of `LinearMap.toMatrix₂` is invariant under reindexing the basis. -/
theorem LinearMap.toMatrix₂_reindex_det {R M ι κ : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R M) (e : ι ≃ κ) (B : M →ₗ[R] M →ₗ[R] R) :
    (LinearMap.toMatrix₂ (b.reindex e) (b.reindex e) B).det
      = (LinearMap.toMatrix₂ b b B).det := by
  rw [LinearMap.toMatrix₂_reindex, Matrix.det_submatrix_equiv_self]

/-- For two bases `b`, `c` of the same real vector space, the `LinearMap.toMatrix₂`
determinants differ by a fixed positive constant `K = (b.reindex e).det c)²` (the square of the
change-of-basis determinant), **uniformly in the bilinear form** `B`. In particular the ratio of
two such determinants (e.g. at different scales) is basis-independent. -/
theorem LinearMap.toMatrix₂_det_basis_change {M ι κ : Type*} [AddCommGroup M] [Module ℝ M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ M) (c : Module.Basis κ ℝ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ,
      (LinearMap.toMatrix₂ c c B).det = K * (LinearMap.toMatrix₂ b b B).det := by
  let e := b.indexEquiv c
  refine ⟨((b.reindex e).det ⇑c) ^ 2, ?_, fun B => ?_⟩
  · have hne : (b.reindex e).det ⇑c ≠ 0 := by
      rw [Module.Basis.det_apply]
      exact left_ne_zero_of_mul_eq_one (by
        rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one])
    positivity
  · rw [← LinearMap.toMatrix₂_reindex_det b e B,
        ← LinearMap.toMatrix₂_mul_basis_toMatrix (b₁ := b.reindex e) (b₂ := b.reindex e) c c B,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply]
    ring


open MatrixOrder in
lemma matrix_det_montone {n: Type*} [Fintype n] [DecidableEq n] (A B: Matrix n n ℝ) (hb: B.PosDef) (hab: (A - B).PosSemidef): B.det ≤ A.det := by

  have invert_sqrt: Invertible (CFC.sqrt B) := by
    apply Matrix.invertibleOfIsUnitDet
    rw [Matrix.PosSemidef.det_sqrt hb.posSemidef]
    simp
    rw [← ne_eq, Real.sqrt_ne_zero]
    . grind [hb.det_pos]
    . grind [hb.det_pos]

  have det_prod_eq: A.det = B.det * ((CFC.sqrt B)⁻¹ * (A - B) * (CFC.sqrt B)⁻¹ + 1).det := by
    conv =>
      lhs
      arg 1
      equals (CFC.sqrt B) * (CFC.sqrt B)⁻¹ * A * (CFC.sqrt B)⁻¹ * (CFC.sqrt B) =>
        simp

    rw [mul_assoc, mul_assoc, mul_assoc]
    rw [Matrix.det_mul]
    rw [← mul_assoc, ← mul_assoc]
    rw [Matrix.det_mul]
    ring
    rw [hb.posSemidef.det_sqrt]
    simp only [RCLike.sqrt_real]
    rw [Real.sq_sqrt (by grind [hb.det_pos])]
    rw [mul_sub]
    rw [sub_mul]
    conv =>
      rhs
      rhs
      rhs
      lhs
      rhs
      arg 1
      arg 2
      rw [← CFC.sqrt_mul_sqrt_self (a := B)]

    simp

  rw [det_prod_eq]
  rw [le_mul_iff_one_le_right]
  .
    apply matrix_psd_det_one
    rw [hb.posSemidef.inv_sqrt]
    have foo := (CFC.sqrt_nonneg B⁻¹)
    rw [Matrix.le_iff] at foo
    simp at foo
    nth_rw 2 [← foo.isHermitian.eq]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact hab
  . apply hb.det_pos

-- TODO - upstream. Mathlib only has `Finset.sum_biUnion` (which needs `PairwiseDisjoint`)
-- and the `ENNReal` `tsum` versions.
theorem Finset.sum_biUnion_le {κ α : Type*} [DecidableEq α] {s: Finset κ} {t: κ → Finset α}
    {f: α → ℝ} (hf: ∀ x, 0 ≤ f x): ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hnn: 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith
