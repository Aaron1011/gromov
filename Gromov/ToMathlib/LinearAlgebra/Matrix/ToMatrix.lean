module

public import Mathlib

/-!
# Matrices of bilinear maps

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

@[expose] public section

/-- Reindexing both bases of a `LinearMap.toMatrix₂` by an equiv turns it into a `submatrix`. -/
theorem LinearMap.toMatrix₂_reindex {R M ι κ : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R M) (e : ι ≃ κ) (B : M →ₗ[R] M →ₗ[R] R) :
    LinearMap.toMatrix₂ (b.reindex e) (b.reindex e) B
      = (LinearMap.toMatrix₂ b b B).submatrix e.symm e.symm := by
  ext i j
  simp [LinearMap.toMatrix₂_apply, Module.Basis.reindex_apply, Matrix.submatrix_apply]
