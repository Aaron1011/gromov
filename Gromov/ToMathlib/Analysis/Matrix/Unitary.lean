import Mathlib
import Mathlib.Analysis.Matrix.StarNormalEigen

lemma diag_of_eigenspace_span {A: Type*} [Nontrivial A] [AddCommGroup A] [Module ℂ A] (g: A →ₗ[ℂ] A) (k: ℂ) (hg: Module.End.eigenspace g k = ⊤):
  g = k • 1 := by

  rw [LinearMap.ext_iff]
  intro x
  simp

  have has_eigenvalue: Module.End.HasEigenvalue g k := by
    rw [Module.End.hasEigenvalue_iff, hg]
    simp only [ne_eq, top_ne_bot, not_false_eq_true]

  have x_mem: x ∈ Module.End.eigenspace g k := by
    simp [hg]

  rw [Module.End.mem_eigenspace_iff] at x_mem
  exact x_mem

lemma linearmap_comp_eq_mul {P: Type*} [AddCommMonoid P] [Module ℂ P] (a b: P →ₗ[ℂ] P): a.comp b = a * b := rfl

-- FALSE - an element could be a sum of elements from p and q
-- lemma ofIsCompl_apply_prop {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E] {F : Type*} [AddCommGroup F] [Module R F] {p q : Submodule R E} (h : IsCompl p q) (φ : ↥p →ₗ[R] F) (ψ : ↥q →ₗ[R] F) (f_prop: F → Prop):
--     (∀ f, f_prop ((LinearMap.ofIsCompl h φ ψ) f)) ↔ (∀ p_val, f_prop (φ p_val)) ∧ (∀ q_val, f_prop (ψ q_val)) := by

--   refine ⟨?_, ?_⟩
--   .
--     intro all_mem
--     refine ⟨?_, ?_⟩
--     .
--       intro p_val
--       specialize all_mem p_val
--       simpa using all_mem
--     . intro q_val
--       specialize all_mem q_val
--       simpa using all_mem
--   .
--     intro sub_mem
--     intro f
--     by_cases f_mem_p: f ∈ p
--     .
--       have foo := sub_mem.1 ⟨f, f_mem_p⟩
--       have f_eq: f = (⟨f, f_mem_p⟩ : p) := by simp
--       rw [f_eq]
--       rw [LinearMap.ofIsCompl_left_apply]
--       exact foo
--     .
--       rw [isCompl_iff] at h
--       have f_mem_q: f ∈ q := by
--         have mem_top: f ∈ (⊤ : (Submodule R E)) := by simp
--         have bar := h.2
--         rw [codisjoint_iff] at bar
--         rw [← bar] at mem_top
--         rw [Submodule.mem_sup] at mem_top
--         obtain ⟨x, hx, y, hy, f_eq_add⟩ := mem_top


--       have foo := sub_mem.2 ⟨f, f_mem_q⟩
--       have f_eq: f = (⟨f, f_mem_q⟩ : q) := by simp
--       rw [f_eq]
--       rw [LinearMap.ofIsCompl_right_apply]
--       exact foo

lemma swap_terms_helper {A: Type*} [AddCommGroup A] (a b c d: A): (a + b) + (c + d) = a + c + b + d := by abel


-- lemma adjoint_eval_congr  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]  [FiniteDimensional ℂ E] (A B : E →ₗ[ℂ] E) (x : E)
--     (ha: A x = B x): (A.adjoint) x = (B.adjoint) x := by


--   rw [ext_iff_inner_left (𝕜 := ℂ)]
--   simp_rw [LinearMap.adjoint_inner_right]
--   intro v

--   have a_eq := LinearMap.adjoint_inner_left A x
--   have b_eq := LinearMap.adjoint_inner_left B x

--   have inner_eq: ∀ y: E, inner ℂ ((LinearMap.adjoint B) y) x = inner ℂ ((LinearMap.adjoint A) y) x := by
--     intro y
--     rw [a_eq]
--     rw [b_eq]
--     rw [ha]



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

    have adjoint_compl_p_eq : LinearMap.adjoint (p.linearProjOfIsCompl q h) = p.subtype := by
      rw [eq_comm]
      simp [-Submodule.coe_linearProjOfIsCompl_apply, LinearMap.eq_adjoint_iff]
      intro b hb z
      obtain ⟨x, y, z_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h z
      rw [← z_eq]
      simp
      rw [inner_add_right]
      simp
      have b_eq : b = (⟨b, hb⟩: p) := by simp
      rw [b_eq]
      apply Submodule.IsOrtho.inner_eq hpq (by simp [hb]) (by simp)

    have adjoint_compl_q_eq : LinearMap.adjoint (q.linearProjOfIsCompl p h.symm) = q.subtype := by
      rw [eq_comm]
      simp [-Submodule.coe_linearProjOfIsCompl_apply, LinearMap.eq_adjoint_iff]
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

    rw [LinearMap.ofIsCompl_right_apply]
    simp

    rw [adjoint_psi_eq]
    conv =>
      lhs
      rhs
      equals (⟨φ x, by apply hφ_map⟩ : p).val =>
        simp


    rw [LinearMap.ofIsCompl_left_apply]
    simp



    -- rw [add_comm]
    -- --rw [Function.comp_apply]
    -- simp only [map_add, LinearMap.adjoint_comp, LinearMap.add_apply, LinearMap.coe_comp,
    --   Function.comp_apply]

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
  rw [LinearMap.ofIsCompl_left_apply, LinearMap.ofIsCompl_right_apply]
  rw [phi_a_comm]
  rw [psi_a_comm]



structure IsoData {n: ℕ} {G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)} (g: G) where
  a : ℕ
  b: ℕ
  ha: a ≠ 0
  hab: a + b = n
  A: Subgroup (Matrix.unitaryGroup (Fin a) ℂ)
  B: Subgroup (Matrix.unitaryGroup (Fin b) ℂ)
  iso: Subgroup.centralizer {g.val} ≃* A × B

-- @[simp]
-- lemma isStarNormal_unitary_coe_toLin {n: ℕ} (f: Matrix.unitaryGroup (Fin n) ℂ)  (v : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))): IsStarNormal (Matrix.toLin v v f) := by
--   apply isStarNormal_of_mem_unitary

--   rw [Unitary.mem_iff]
--   refine ⟨?_, ?_⟩
--   .
--     have f_prop := f.property
--     rw [Matrix.mem_unitaryGroup_iff'] at f_prop
--     apply_fun Matrix.toEuclideanLin at f_prop
--     rw [LinearMap.star_eq_adjoint]
--     rw [Matrix.star_eq_conjTranspose] at f_prop

--     rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
--     -- TODO - make a better lemma and PR to mathlib
--     rw [Matrix.toLin_mul (v₂ := v)] at f_prop
--     rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop

--     conv at f_prop =>
--       lhs
--       equals (f.val.conjTranspose.toEuclideanLin) * (f.val.toEuclideanLin) =>
--         rfl


--     rw [f_prop]
--     rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
--     rw [LinearMap.ext_iff]
--     intro x
--     simp

--   .
--     have f_prop := f.property
--     rw [Matrix.mem_unitaryGroup_iff] at f_prop
--     apply_fun Matrix.toEuclideanLin at f_prop
--     rw [LinearMap.star_eq_adjoint]
--     rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
--     rw [Matrix.star_eq_conjTranspose] at f_prop

--     rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
--     -- TODO - make a better lemma and PR to mathlib
--     rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )] at f_prop
--     rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at f_prop
--     conv at f_prop =>
--       lhs
--       equals (f.val.toEuclideanLin) * (f.val.conjTranspose.toEuclideanLin) =>
--         rfl

--     rw [f_prop]
--     rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
--     rw [LinearMap.ext_iff]
--     intro x
--     simp

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

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 100000 in
lemma centralizer_iso {n: ℕ} [hn: NeZero n] (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g: G) (g_not: ∀ z: ℂ, g.val.val ≠ z • 1):
    Nonempty (IsoData g) := by



  obtain ⟨k, hk⟩ := Module.End.exists_eigenvalue g.val.val.toEuclideanLin
  by_cases gen_eigenspace_top: Module.End.maxGenEigenspace g.val.val.toEuclideanLin k = ⊤
  .
    rw [star_normal_maxGenEigenspace_eq_eigenspace (by simp)] at gen_eigenspace_top
    apply Module.End.HasEigenvalue.exists_hasEigenvector at hk

    have eq_diag := diag_of_eigenspace_span g.val.val.toEuclideanLin k gen_eigenspace_top
    specialize g_not k
    apply_fun (fun f =>  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis f) at eq_diag
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal] at eq_diag
    contradiction
  .
    have span := Module.End.iSup_maxGenEigenspace_eq_top g.val.val.toEuclideanLin
    rw [iSup_split_single _ k] at span
    rw [← codisjoint_iff] at span

    have a_b_compl: IsCompl _ _ := {
      disjoint := by
        have foo := Module.End.independent_genEigenspace (g.val.val.toEuclideanLin) ⊤
        rw [iSupIndep_def] at foo
        apply foo
      codisjoint := span
    }

    have other_ne_bot := Codisjoint.ne_bot_of_ne_top span gen_eigenspace_top
    rw [codisjoint_iff] at span

    have preserves := Module.End.mapsTo_genEigenspace_of_comm (f := g.val.val.toEuclideanLin) (g := g.val.val.toEuclideanLin) (by simp) k (Module.End.maxGenEigenspaceIndex g.val.val.toEuclideanLin k)
    rw [← Module.End.maxGenEigenspace_eq] at preserves
    rw [← iSup_ne_bot_subtype] at span




    -- nth_rw 1 [iSup_subtype] at span
    -- simp at span
    -- conv at span =>
    --   lhs
    --   rhs
    --   arg 1
    --   intro i
    --   arg 1
    --   intro hi‖

    have comm_g_h (h: Subgroup.centralizer {g.val}): Commute (Matrix.toEuclideanLin g.val.val) (Matrix.toEuclideanLin h.val.val) := by
      have foo := h.property
      rw [Subgroup.mem_centralizer_iff] at foo
      rw [commute_iff_eq]
      simp at foo
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      rw [← linearmap_comp_eq_mul]
      rw [← Matrix.toLin_mul]
      rw [← linearmap_comp_eq_mul]
      rw [← Matrix.toLin_mul]
      apply_fun (fun f => f.val) at foo
      simp at foo
      rw [foo]

    have other_invariant (h: Subgroup.centralizer {g.val}):  ⨆ (i : { i : Module.End.Eigenvalues g.val.val.toEuclideanLin // i.val ≠ k }), Module.End.maxGenEigenspace h.val.val.toEuclideanLin i ∈ (Module.End.invtSubmodule g.val.val.toEuclideanLin) := by
      apply SupClosed.iSup_mem
      . simp
      . simp
      .
        intro i
        simp
        apply Module.End.mapsTo_genEigenspace_of_comm
        rw [Commute.symm_iff]
        apply comm_g_h

    --simp_rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at other_invariant




    let map_first (h: Subgroup.centralizer {g.val}) := h.val.val.toEuclideanLin.restrict (Module.End.mapsTo_genEigenspace_of_comm (f := g.val.val.toEuclideanLin) (g := h.val.val.toEuclideanLin) (by
      apply comm_g_h
    ) k ⊤)

    --let a := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ _) (map_first 1)

    --let d := Module.finrank ℂ (Module.End.genEigenspace g.val.val.toEuclideanLin k ⊤)
    let d := (Module.finrank ℂ ↥((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤))
    let map_first_unitary (h: Subgroup.centralizer {g.val}): Matrix.unitaryGroup (Fin d) ℂ := {
      val := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ _) (map_first h)
      property := by


        rw [Matrix.mem_unitaryGroup_iff']

        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [Matrix.star_eq_conjTranspose]

        simp only [LinearMap.toMatrixOrthonormal_apply]
        simp []
        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [← LinearMap.toMatrix_adjoint]
          arg 2
        rw [← LinearMap.toMatrix_mul]

        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        rw [Matrix.toLin_toMatrix]
        rw [Matrix.toLin_one]
        conv =>
          rhs
          equals 1 =>
            ext a
            simp

        simp [map_first]
        have h_unitary := Unitary.star_mul_self_of_mem h.val.property
        apply_fun Matrix.toEuclideanLin at h_unitary
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        conv at h_unitary =>
          lhs
          equals (Matrix.toEuclideanLin (star h.val.val)) ∘ₗ (Matrix.toEuclideanLin (h.val.val)) =>
            rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            rw [← Matrix.toLin_mul]
        rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        rw [Matrix.star_eq_conjTranspose] at h_unitary
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h_unitary
        conv at h_unitary =>
          rhs
          rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          equals 1 =>
            ext z
            simp

        apply_fun (fun f => LinearMap.toContinuousLinearMap f)
        simp [-EmbeddingLike.apply_eq_iff_eq]
        conv =>
          lhs
          rw [← linearmap_comp_eq_mul]
          rw [linearmap_comp_toContinuousLinearMap]
          rw [ContinuousLinearMap.mul_def]
          lhs
          rw [LinearMap.adjoint_toContinuousLinearMap]

        conv =>
          rhs
          equals 1 =>
            ext z
            simp
        rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
        simp only [LinearMap.coe_toContinuousLinearMap']
        conv =>
          intro x
          rw [LinearMap.restrict_apply (by
            apply Module.End.mapsTo_genEigenspace_of_comm (by
              apply comm_g_h
            )
          )]
          simp
          rw [← LinearMap.coe_toContinuousLinearMap']


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
        intro x
        specialize h_unitary x.val
        exact h_unitary
        . exact LinearEquiv.injective LinearMap.toContinuousLinearMap
        . intro x y hxy
          simpa using hxy
    }


    let map_first_hom: MonoidHom (Subgroup.centralizer {g.val}) _ := {
      toFun := map_first_unitary
      map_one' := by
        simp [map_first_unitary, map_first]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          simp
          ext a
          simp
        . intro x y hxy
          simpa using hxy
      map_mul' := by
        intro x y
        simp [map_first_unitary, map_first]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          rw [LinearMap.ext_iff]
          intro a
          rw [← LinearMap.toMatrix_mul]
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          conv =>
            lhs
            arg 1
            arg 1
            -- TODO - figure out why toLin_mul doesn't work here
            equals ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑x)) ∘ₗ (((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑y))) =>
              rw [← Matrix.toLin_mul]

          rfl
        . intro x y hxy
          simpa using hxy
    }

    let first_range := map_first_hom.range


    let map_second (h: Subgroup.centralizer {g.val}) := h.val.val.toEuclideanLin.restrict
      (p :=  ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)))
      (q :=  ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)))
      (by
        --exact other_invariant h
        intro x hx
        apply LinearMap.mapsTo_biSup_of_mapsTo
        .
          intro z
          apply Module.End.mapsTo_maxGenEigenspace_of_comm
          apply comm_g_h
        . exact hx
      )


    let map_second_unitary (h: Subgroup.centralizer {g.val}): Matrix.unitaryGroup _ ℂ := {
      val := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ _) (map_second h)
      property := by
        -- TODO - deduplicate this with 'map_first_unitary'
        rw [Matrix.mem_unitaryGroup_iff']

        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [Matrix.star_eq_conjTranspose]

        simp only [LinearMap.toMatrixOrthonormal_apply]
        simp []
        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [← LinearMap.toMatrix_adjoint]
          arg 2
        rw [← LinearMap.toMatrix_mul]

        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        rw [Matrix.toLin_toMatrix]
        rw [Matrix.toLin_one]
        conv =>
          rhs
          equals 1 =>
            ext a
            simp

        simp [map_second]
        have h_unitary := Unitary.star_mul_self_of_mem h.val.property
        apply_fun Matrix.toEuclideanLin at h_unitary
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        conv at h_unitary =>
          lhs
          equals (Matrix.toEuclideanLin (star h.val.val)) ∘ₗ (Matrix.toEuclideanLin (h.val.val)) =>
            rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            rw [← Matrix.toLin_mul]
        rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        rw [Matrix.star_eq_conjTranspose] at h_unitary
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h_unitary
        conv at h_unitary =>
          rhs
          rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          equals 1 =>
            ext z
            simp

        apply_fun (fun f => LinearMap.toContinuousLinearMap f)
        simp [-EmbeddingLike.apply_eq_iff_eq]
        conv =>
          lhs
          rw [← linearmap_comp_eq_mul]
          rw [linearmap_comp_toContinuousLinearMap]
          rw [ContinuousLinearMap.mul_def]
          lhs
          rw [LinearMap.adjoint_toContinuousLinearMap]

        conv =>
          rhs
          equals 1 =>
            ext z
            simp
        rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
        simp only [LinearMap.coe_toContinuousLinearMap']
        conv =>
          intro x
          rw [LinearMap.restrict_apply (by
            apply LinearMap.mapsTo_biSup_of_mapsTo
            intro z
            apply Module.End.mapsTo_maxGenEigenspace_of_comm
            apply comm_g_h
          )]
          simp
          rw [← LinearMap.coe_toContinuousLinearMap']


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
        intro x
        specialize h_unitary x.val
        exact h_unitary
        . exact LinearEquiv.injective LinearMap.toContinuousLinearMap
        . intro x y hxy
          simpa using hxy
    }

    let map_second_hom: MonoidHom (Subgroup.centralizer {g.val}) _ := {
      toFun := map_second_unitary
      -- TODO - deduplicate these with 'map_first_hom'
      map_one' := by
        simp [map_second_unitary, map_second]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          simp
          ext a
          simp
        . intro x y hxy
          simpa using hxy
      map_mul' := by
        intro x y
        simp [map_second_unitary, map_second]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          rw [LinearMap.ext_iff]
          intro a
          rw [← LinearMap.toMatrix_mul]
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          conv =>
            lhs
            arg 1
            arg 1
            -- TODO - figure out why toLin_mul doesn't work here
            equals ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑x)) ∘ₗ (((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑y))) =>
              rw [← Matrix.toLin_mul]

          rfl
        . intro x y hxy
          simpa using hxy
    }

    let prod_hom := MonoidHom.prod map_first_hom.rangeRestrict map_second_hom.rangeRestrict
    let prod_iso := MulEquiv.ofBijective prod_hom (by
      unfold Function.Bijective
      refine ⟨?_, ?_⟩
      .
        -- TODO - this can probably be much simpler
        simp [prod_hom]
        intro x y hxy
        simp at hxy
        obtain ⟨first_eq, second_eq⟩ := hxy

        let map_first_x_new: ((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_first x a
          map_add' := by simp
          map_smul' := by simp
        }

        let map_second_x_new: ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_second x a
          map_add' := by simp
          map_smul' := by simp
        }

        let x_map := LinearMap.ofIsCompl a_b_compl (map_first_x_new) (map_second_x_new)

        let map_first_y_new: ((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_first y a
          map_add' := by simp
          map_smul' := by simp
        }

        let map_second_y_new: ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_second y a
          map_add' := by simp
          map_smul' := by simp
        }

        let y_map := LinearMap.ofIsCompl a_b_compl (map_first_y_new) (map_second_y_new)

        have first_eq_second: x_map = y_map := by
          simp [x_map]
          apply LinearMap.ofIsCompl_eq
          . intro z
            simp [y_map]
            simp [map_first_x_new, map_first_y_new]
            apply_fun (fun f => f.val) at first_eq
            simp at first_eq
            simp [map_first_hom, map_first_unitary] at first_eq
            rw [Function.Injective.eq_iff] at first_eq
            .
              rw [first_eq]
            . apply LinearEquiv.injective
          . intro z
            simp [y_map]
            simp [map_second_x_new, map_second_y_new]
            apply_fun (fun f => f.val) at second_eq
            simp at second_eq
            simp [map_second_hom, map_second_unitary] at second_eq
            congr



        have x_map_eq: x_map = x.val.val.toEuclideanLin := by
          simp [x_map]
          apply LinearMap.ofIsCompl_eq
          . intro z
            rfl
          . intro z
            rfl

        have y_map_eq: y_map = y.val.val.toEuclideanLin := by
          simp [x_map]
          apply LinearMap.ofIsCompl_eq
          . intro z
            rfl
          . intro z
            rfl


        rw [x_map_eq, y_map_eq] at first_eq_second
        simp at first_eq_second
        exact first_eq_second
      .
        intro a
        have first_prop := a.fst.property
        have second_prop := a.snd.property
        simp only [prod_hom]
        rw [MonoidHom.mem_range] at first_prop
        rw [MonoidHom.mem_range] at second_prop

        obtain ⟨x, hx⟩ := first_prop
        obtain ⟨y, hy⟩ := second_prop

        let map_first_x_new: ((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_first x a
          map_add' := by simp
          map_smul' := by simp
        }

        let map_second_y_new: ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_second y a
          map_add' := by simp
          map_smul' := by simp
        }

        have map_first_x_unitary: (ContinuousLinearMap.adjoint map_first_x_new.toContinuousLinearMap).comp map_first_x_new.toContinuousLinearMap = 1 := by
          rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
          intro z
          simp [map_first_x_new, map_first]
          apply unitary_preserves_norm

        apply_fun (fun f => f.toLinearMap) at map_first_x_unitary
        simp at map_first_x_unitary

        have map_second_y_unitary: (ContinuousLinearMap.adjoint map_second_y_new.toContinuousLinearMap).comp map_second_y_new.toContinuousLinearMap = 1 := by
          rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
          intro z
          simp [map_second_y_new, map_second]
          apply unitary_preserves_norm

        apply_fun (fun f => f.toLinearMap) at map_second_y_unitary
        simp at map_second_y_unitary

        let new := LinearMap.ofIsCompl a_b_compl map_first_x_new map_second_y_new
        use ⟨⟨(Matrix.toEuclideanLin.symm new), (by
          simp [Matrix.mem_unitaryGroup_iff']
          apply_fun (fun f => Matrix.toEuclideanLin f)
          . simp [-EmbeddingLike.apply_eq_iff_eq, new]
            rw [Matrix.star_eq_conjTranspose]
            simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            simp
            --rw [← linearmap_comp_eq_mul]
            nth_rw 1 [Matrix.toLin_mul (M₁ := (EuclideanSpace ℂ (Fin n))) (M₂ := (EuclideanSpace ℂ (Fin n))) (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis)]
            simp
            rw [← LinearMap.toMatrix_adjoint]
            simp


            --apply_fun (fun f => LinearMap.toContinuousLinearMap f)
            --simp [-EmbeddingLike.apply_eq_iff_eq]
            -- conv =>
            --   lhs
            --   rw [linearmap_comp_toContinuousLinearMap]
            --   rw [ContinuousLinearMap.mul_def]
            --   lhs
            --   rw [LinearMap.adjoint_toContinuousLinearMap]

            conv =>
              rhs
              equals 1 =>
                ext z
                simp



            apply ofIsCompl_adjoint_comp
            .
              rw [star_normal_maxGenEigenspace_eq_eigenspace (by simp)]
              conv =>
                rhs
                arg 1
                intro x
                arg 1
                intro x
                rw [star_normal_maxGenEigenspace_eq_eigenspace (by simp)]
              simp
              intro i hi
              apply eigenspace_orthogonal
              . simp
              . omega
            .
              apply map_first_x_unitary
            . simp [map_first_x_new]
            .
              apply map_second_y_unitary
            . simp [map_second_y_new]
          . intro x y hxy
            simpa using hxy
        )⟩, (by
          simp
          rw [Subgroup.mem_centralizer_iff]
          simp
          apply_fun (fun f => Matrix.toEuclideanLin f.val)
          simp only []
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          simp only [Matrix.toLin_symm, Submonoid.coe_mul]
          rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )]
          simp
          rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )]
          simp [new]
          rw [eq_comm]
          apply ofIsCompl_commute
          .
            sorry
          . sorry
          .
            intro z
            apply Module.End.mapsTo_maxGenEigenspace_of_comm
            rw [commute_iff_eq]
            rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            simp
          .
            intro x
            apply LinearMap.mapsTo_biSup_of_mapsTo
            .
              intro z
              apply Module.End.mapsTo_maxGenEigenspace_of_comm
              rw [commute_iff_eq]
              rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
              simp
            . exact hx
            -- intro z
            -- apply (Module.End.mem_invtSubmodule_iff_mapsTo _).mp
            -- sorry
          . intro a b hab
            simpa using hab
          -- rw [Matrix.toLin_toMatrix]
          -- simp_rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
          -- rw [LinearMap.ext_iff]
          -- intro v
          -- simp [new]
          -- obtain ⟨x, y, c_eq, _⟩ := Submodule.existsUnique_add_of_isCompl h v

          -- sorry
        )⟩


        apply Prod.ext
        .
          rw [Subtype.ext_iff]
          conv =>
            rhs
            rw [← hx]
          simp
          simp [map_first_hom, map_first_unitary]
          apply congrArg
          simp [map_first]
          rw [LinearMap.ext_iff]
          intro z
          rw [Subtype.ext_iff]
          simp [new]
          simp [map_first_x_new, map_first]
        .
          rw [Subtype.ext_iff]
          conv =>
            rhs
            rw [← hy]
          simp
          simp [map_second_hom, map_second_unitary]
          simp [map_second]
          rw [LinearMap.ext_iff]
          intro z
          rw [Subtype.ext_iff]
          simp [new]
          simp [map_second_y_new, map_second]
    )
    -- Submodule.finrank_add_eq_of_isCompl


    apply Nonempty.intro
    exact {
      a := d
      b := _
      hab := by
        have sum_eq := Submodule.finrank_add_eq_of_isCompl a_b_compl
        simp at sum_eq
        apply sum_eq
      ha := by
        rw [Nat.ne_zero_iff_zero_lt]
        unfold d
        rw [Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex]
        apply Module.End.pos_finrank_genEigenspace_of_hasEigenvalue
        . exact hk
        . by_contra!
          have eigen_one_le := Module.End.genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex (Matrix.toEuclideanLin g.val.val) k 1
          simp at this
          simp [this] at eigen_one_le
          rw [Module.End.hasEigenvalue_iff] at hk
          rw [Module.End.eigenspace_def] at hk
          rw [← Module.End.genEigenspace_one] at hk
          contradiction
      A := _
      B := _
      iso := prod_iso
    }
