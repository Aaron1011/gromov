module

public import Mathlib
public import Gromov.ToMathlib.Analysis.Matrix.StarNormalEigen

/-!
# Unitary matrices: helper lemmas

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

public section

lemma diag_of_eigenspace_span {A: Type*} [Nontrivial A] [AddCommGroup A] [Module ℂ A] (g: A →ₗ[ℂ] A) (k: ℂ) (hg: Module.End.eigenspace g k = ⊤):
  g = k • 1 := by

  rw [LinearMap.ext_iff]
  intro x
  simp


  have x_mem: x ∈ Module.End.eigenspace g k := by
    simp [hg]

  rw [Module.End.mem_eigenspace_iff] at x_mem
  exact x_mem



lemma linearmap_comp_toContinuousLinearMap {P: Type*} [AddCommGroup P] [Module ℂ P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousSMul ℂ P] [T2Space P]  [FiniteDimensional ℂ P]  (a b: P →ₗ[ℂ] P):
  (a.comp b).toContinuousLinearMap = a.toContinuousLinearMap * b.toContinuousLinearMap := rfl

lemma unitary_preserves_norm (n: ℕ) (h: Matrix.unitaryGroup (Fin n) ℂ) (x: EuclideanSpace ℂ (Fin n)): ‖(Matrix.toEuclideanLin h.val) x‖ = ‖x‖ := by
  have h_unitary := Unitary.star_mul_self_of_mem h.property
  apply_fun Matrix.toEuclideanLin at h_unitary
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
  conv at h_unitary =>
    lhs
    equals (Matrix.toEuclideanLin (star h.val)) ∘ₗ (Matrix.toEuclideanLin (h.val)) =>
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      rw [← Matrix.toLin_mul]
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
  rw [Matrix.star_eq_conjTranspose] at h_unitary
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h_unitary

  apply_fun (fun f => LinearMap.toContinuousLinearMap f) at h_unitary
  simp [-EmbeddingLike.apply_eq_iff_eq] at h_unitary
  conv at h_unitary =>
    lhs
    rw [linearmap_comp_toContinuousLinearMap]
    rw [ContinuousLinearMap.mul_def]
    lhs
    rw [LinearMap.adjoint_toContinuousLinearMap]

  conv at h_unitary =>
    rhs
    equals 1 =>
      ext x
      simp
  rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self] at h_unitary
  specialize h_unitary x
  simp at h_unitary
  exact h_unitary


lemma ofIsCompl_adjoint_comp {P: Type*} [NormedAddCommGroup P] [CompleteSpace P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]  {p q : Submodule ℂ P} (h : IsCompl p q) (hpq: p ⟂ q) (φ : p →ₗ[ℂ] P) (ψ : q →ₗ[ℂ] P) (hφ: (LinearMap.adjoint φ) ∘ₗ φ = 1) (hφ_map: ∀ x: p, φ x ∈ p) (hψ: (LinearMap.adjoint ψ) ∘ₗ ψ = 1) (hψ_map: ∀ x: q, ψ x ∈ q):
  (LinearMap.ofIsCompl h (φ) (ψ)).adjoint ∘ₗ(LinearMap.ofIsCompl h φ ψ) = 1  := by
    rw [LinearMap.ext_iff]
    intro a
    obtain ⟨x, y, a_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h a
    rw [← a_eq]
    simp
    rw [LinearMap.ofIsCompl_eq_add]
    simp

    have adjoint_compl_p_eq : LinearMap.adjoint (p.projectionOnto q h) = p.subtype := by
      rw [eq_comm]
      simp [-Submodule.coe_projectionOnto_apply, LinearMap.eq_adjoint_iff]
      intro b hb z
      obtain ⟨x, y, z_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h z
      rw [← z_eq]
      simp
      rw [inner_add_right]
      simp
      have b_eq : b = (⟨b, hb⟩: p) := by simp
      rw [b_eq]
      apply Submodule.IsOrtho.inner_eq hpq (by simp [hb]) (by simp)

    have adjoint_compl_q_eq : LinearMap.adjoint (q.projectionOnto p h.symm) = q.subtype := by
      rw [eq_comm]
      simp [-Submodule.coe_projectionOnto_apply, LinearMap.eq_adjoint_iff]
      intro b hb z
      obtain ⟨x, y, z_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h z
      rw [← z_eq]
      simp
      rw [inner_add_right]
      simp
      have b_eq : b = (⟨b, hb⟩: q) := by simp
      rw [b_eq]
      apply Submodule.IsOrtho.inner_eq hpq.symm (by simp [hb]) (by simp)

    let temp := φ.adjoint

    have adjoint_phi_eq: (LinearMap.adjoint φ) =  (LinearMap.ofIsCompl h (LinearMap.domRestrict φ.adjoint p) 0) := by
      rw [eq_comm]
      rw [LinearMap.eq_adjoint_iff]
      intro c d
      simp
      obtain ⟨x, y, c_eq, _⟩ := Submodule.existsUnique_add_of_isCompl h c
      rw [← c_eq]
      simp
      rw [inner_add_left]

      rw [Submodule.isOrtho_iff_inner_eq] at hpq
      have my_inner := hpq (φ d) (by exact hφ_map d) y (by simp)
      rw [inner_eq_zero_symm] at my_inner
      simp [my_inner]
      nth_rw 2 [← inner_conj_symm]
      rw [← LinearMap.adjoint_inner_right]
      simp

    have adjoint_psi_eq: (LinearMap.adjoint ψ) =  (LinearMap.ofIsCompl h 0 (LinearMap.domRestrict ψ.adjoint q)) := by
      rw [eq_comm]
      rw [LinearMap.eq_adjoint_iff]
      intro c d
      simp
      obtain ⟨x, y, c_eq, _⟩ := Submodule.existsUnique_add_of_isCompl h c
      rw [← c_eq]
      simp
      rw [inner_add_left]

      rw [Submodule.isOrtho_iff_inner_eq] at hpq
      have my_inner := hpq x (by simp) (ψ d) (by exact hψ_map d)
      simp [my_inner]
      nth_rw 2 [← inner_conj_symm]
      rw [← LinearMap.adjoint_inner_right]
      simp

    simp [adjoint_compl_p_eq, adjoint_compl_q_eq]
    apply_fun (fun f => f x) at hφ
    simp at hφ
    simp [hφ]

    apply_fun (fun f => f y) at hψ
    simp at hψ
    simp [hψ]
    rw [adjoint_phi_eq]
    conv =>
      pattern ψ y
      equals (⟨ψ y, by apply hψ_map⟩ : q).val =>
        simp

    rw [LinearMap.ofIsCompl_apply_right]
    simp

    rw [adjoint_psi_eq]
    conv =>
      lhs
      rhs
      equals (⟨φ x, by apply hφ_map⟩ : p).val =>
        simp


    rw [LinearMap.ofIsCompl_apply_left]
    simp


lemma ofIsCompl_commute {P: Type*} [NormedAddCommGroup P] [CompleteSpace P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]  {p q : Submodule ℂ P} (h : IsCompl p q)
    (φ : p →ₗ[ℂ] P) (ψ : q →ₗ[ℂ] P)
    (a: P →ₗ[ℂ] P) (a_map_p: ∀ x: p, a x ∈ p) (a_map_q: ∀ x: q, a x ∈ q)
    (phi_a_comm: ∀ x: p, φ ⟨a x, a_map_p x⟩ = a (φ x))
    (psi_a_comm: ∀ x: q, ψ ⟨a x, a_map_q x⟩ = a (ψ x))
    : (LinearMap.ofIsCompl h (φ) (ψ)) * a = a * (LinearMap.ofIsCompl h (φ) (ψ)) := by

  rw [LinearMap.ext_iff]
  intro v
  obtain ⟨x, y, v_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h v
  rw [← v_eq]
  simp

  have a_x: a x = (⟨a x, a_map_p x⟩ : p).val := by simp
  have a_y: a y = (⟨a y, a_map_q y⟩ : q).val := by simp

  rw [a_x, a_y]
  rw [LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]
  rw [phi_a_comm]
  rw [psi_a_comm]


structure IsoData {n: ℕ} {G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)} (g: G) where
  a : ℕ
  b: ℕ
  ha: a ≠ 0
  hb: b ≠ 0
  hab: a + b = n
  A: Subgroup (Matrix.unitaryGroup (Fin a) ℂ)
  B: Subgroup (Matrix.unitaryGroup (Fin b) ℂ)
  iso: Subgroup.centralizer {g.val} ≃* A × B


-- TODO - cleanup and PR to mathlib
@[simp]
lemma isStarNormal_unitary_coe {n: ℕ} (f: Matrix.unitaryGroup (Fin n) ℂ): IsStarNormal (Matrix.toEuclideanLin f.val) := by
  apply isStarNormal_of_mem_unitary

  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  .
    have f_prop := f.property
    rw [Matrix.mem_unitaryGroup_iff'] at f_prop
    apply_fun Matrix.toEuclideanLin at f_prop
    rw [LinearMap.star_eq_adjoint]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [Matrix.star_eq_conjTranspose] at f_prop

    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    -- TODO - make a better lemma and PR to mathlib
    rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )] at f_prop
    rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    conv at f_prop =>
      lhs
      equals (f.val.conjTranspose.toEuclideanLin) * (f.val.toEuclideanLin) =>
        rfl


    rw [f_prop]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [LinearMap.ext_iff]
    intro x
    simp

  .
    have f_prop := f.property
    rw [Matrix.mem_unitaryGroup_iff] at f_prop
    apply_fun Matrix.toEuclideanLin at f_prop
    rw [LinearMap.star_eq_adjoint]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [Matrix.star_eq_conjTranspose] at f_prop

    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    -- TODO - make a better lemma and PR to mathlib
    rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )] at f_prop
    rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
    conv at f_prop =>
      lhs
      equals (f.val.toEuclideanLin) * (f.val.conjTranspose.toEuclideanLin) =>
        rfl

    rw [f_prop]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [LinearMap.ext_iff]
    intro x
    simp

@[simp]
lemma isStarNormal_unitary_coe_toLin {n: ℕ} (f: Matrix.unitaryGroup (Fin n) ℂ): IsStarNormal (Matrix.toLin ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis) ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis ) f.val) := by
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp
