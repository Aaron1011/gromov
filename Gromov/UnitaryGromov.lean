import Mathlib

open scoped Matrix.L2OpNorm ComplexInnerProductSpace

-- Lemma 3.29 (Shrinking Conjugators)
lemma shrinking_conjugators (n: ℕ) (g h: Matrix.unitaryGroup (Fin n) ℂ):
  ‖⁅g, h⁆.val - 1‖ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
  dsimp only [Bracket.bracket]
  calc
    _ = ‖((g* h).val - (h * g).val) * (g⁻¹ * h⁻¹)‖ := by
      rw [sub_mul]
      repeat rw [ ← Submonoid.coe_mul]
      conv =>
        rhs
        arg 1
        rhs
        arg 1
        equals 1 => group
      repeat rw [← mul_assoc]
      simp
    _ = ‖((g* h).val - (h * g).val)‖ := by
      rw [ ← Submonoid.coe_mul]
      rw [CStarRing.norm_mul_coe_unitary]
    _ = ‖(g* h).val - g - h + 1 - ((h*g).val - h - g + 1)‖ := by
      abel
    _ = ‖(g.val - 1)*(h.val - 1) - (h.val - 1)*(g.val - 1)‖ := by
      conv =>
        rhs
        repeat rw [mul_sub]
        repeat rw [sub_mul]
      field_simp
      abel_nf
    _ ≤ ‖(g.val - 1)*(h.val - 1)‖ + ‖(h.val - 1)*(g.val - 1)‖ := by
      apply norm_sub_le
    _ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
      have norm_sub_g := Matrix.l2_opNorm_mul (g.val - 1) (h.val - 1)
      have norm_sub_h := Matrix.l2_opNorm_mul (h.val - 1) (g.val - 1)
      rw [mul_comm] at norm_sub_h
      linarith


def FreshInnerProduct (V: Type*) := V

instance (V: Type*) [base_comm: AddCommGroup V]: AddCommGroup (FreshInnerProduct V) := base_comm
instance (V: Type*) [AddCommGroup V] [base_module: Module ℂ V]: Module ℂ (FreshInnerProduct V) := base_module

#synth InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 2))

noncomputable def toComplexEuclidean {E: Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℂ E] [ContinuousSMul ℂ E] [FiniteDimensional ℂ E] : E ≃L[ℂ] EuclideanSpace ℂ (Fin <| Module.finrank ℂ E) := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

attribute [-simp] PiLp.inner_apply
--  [NormedAddCommGroup V]  [CompleteSpace V] [InnerProductSpace ℂ V]
-- [MeasurableSpace H] [T2Space H] [BorelSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
lemma weyl_unitarian_trick (G: Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]  [LocallyCompactSpace G] (H: Subgroup G) [BorelSpace H] [LocallyCompactSpace H] [T2Space H] (V: Type*)  [AddCommGroup V] [TopologicalSpace V]  [Module ℂ V] [T2Space V] [ContinuousSMul ℂ V] [FiniteDimensional ℂ V]  [IsTopologicalAddGroup V] (h_compact: IsCompact (Set.univ : Set H)) (rep: H → (V →L[ℂ] V)ˣ) (h_cont: Continuous rep): True := by
  let integrand := fun (v w: V) (h: H) => ⟪toComplexEuclidean ((rep h).val v), toComplexEuclidean ((rep h).val w)⟫
  have continuous_integrand: ∀ v w: V, Continuous fun h: H => integrand v w h := by
    intro v w
    simp only [integrand, toComplexEuclidean]
    -- TODO - how do we prove that the representation is continuous?
    refine Continuous.inner ?_ ?_
    .
      apply Continuous.comp (by fun_prop)
      apply Continuous.comp (g := fun g => g.val v) (f := fun h => (rep h))
      .
        apply Continuous.comp (g := fun (r: V →L[ℂ] V) => r v) (f := fun (g: (V →L[ℂ] V)ˣ) => g.val)
        . fun_prop
        . exact Units.continuous_val
      . exact h_cont
    . apply Continuous.comp (by fun_prop)
      apply Continuous.comp (g := fun g => g.val w) (f := fun h => (rep h))
      .
        apply Continuous.comp (g := fun (r: V →L[ℂ] V) => r w) (f := fun (g: (V →L[ℂ] V)ˣ) => g.val)
        . fun_prop
        . exact Units.continuous_val
      . exact h_cont

  have integrable_on: ∀ v w: V, MeasureTheory.Integrable (integrand v w) (MeasureTheory.Measure.haar (G := H)) := by
    intro v w
    rw [← MeasureTheory.integrableOn_univ]
    apply ContinuousOn.integrableOn_compact h_compact
    apply (continuous_integrand v w).continuousOn

    -- dsimp [MeasureTheory.Integrable]
    -- refine ⟨?_, ?_⟩
    -- .
    --   simp [integrand]
    --   apply Measurable.aestronglyMeasurable
    --   apply Measurable.inner (f := fun h => (rep h).val v) (g := fun h => (rep h).val w)
    --   . apply Measurable.comp (g := fun q => q v) (f := fun h => (rep h).val)
    --     . exact Measurable.of_comap_le fun s a ↦ a
    --     . apply Measurable.comp (g := fun q => q.val) (f := fun x => (rep x))
    --       . exact Measurable.of_comap_le fun s a ↦ a
    --       . apply h_rep
    --       exact h_rep
    --   . apply Measurable.comp (g := fun q => q w) (f := fun h => (rep h).val)


    -- apply ContinuousOn.integrableOn_compact h_compact
    -- specialize continuous_integrand v w
    -- exact continuous_integrand.continuousOn

  let inner_product_core: InnerProductSpace.Core ℂ (FreshInnerProduct V) := {
    inner := fun v w => MeasureTheory.integral (MeasureTheory.Measure.haar) (integrand v w)
    conj_inner_symm := by
      intro x y
      simp only [integrand]
      rw [← integral_conj]
      simp
    re_inner_nonneg := by
      intro x
      simp [integrand]
      conv =>
        rhs
        arg 1
        arg 2
        intro h
        rw [← inner_self_ofReal_re]
      simp
      rw [integral_complex_ofReal]
      apply MeasureTheory.integral_nonneg
      rw [Pi.le_def]
      intro y
      simp
      rw [← RCLike.re_to_complex]
      apply inner_self_nonneg
    add_left := by
      intro a b c
      simp [integrand]
      rw [MeasureTheory.integral_add]
      . exact integrable_on a c
      . exact integrable_on b c
    smul_left := by
      intro x y z
      simp [integrand]
      rw [integral_mul_const_of_integrable (integrable_on x y)]
      rw [mul_comm]
    definite := by
      intro x hx
      simp only [integrand] at hx
      conv at hx =>
        lhs
        arg 2
        intro h
        rw [← inner_self_ofReal_re]

      simp at hx
      rw [integral_complex_ofReal] at hx
      norm_cast at hx
      rw [MeasureTheory.integral_eq_zero_iff_of_nonneg ?_] at hx
      .
        dsimp only [Filter.EventuallyEq] at hx
        conv at hx =>
          pattern MeasureTheory.Measure.haar
          rw [← MeasureTheory.Measure.restrict_univ (μ := MeasureTheory.Measure.haar)]


        obtain ⟨q, _, inner_q_zero⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae ?_ hx
        conv at inner_q_zero =>
          equals ⟪toComplexEuclidean ((rep q).val x), toComplexEuclidean ((rep q).val x)⟫ = 0 =>
            rw [← inner_self_ofReal_re]
            field_simp

        simp at inner_q_zero
        unfold DFunLike.coe at inner_q_zero
        have map_iff_zero := LinearMap.map_eq_zero_iff (f := (rep q).val.toLinearMap) (x := x) ?_
        .
          simp at map_iff_zero
          rw [← map_iff_zero]
          exact inner_q_zero
        .
          -- TODO - find a better way of doing this
          let my_map := (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := V)).toMonoidHom
          let f_map := (Units.map my_map) (rep q)
          let f_as_equiv := fun f => (LinearMap.GeneralLinearGroup.toLinearEquiv (R := ℂ) (M := V) f)
          simp [LinearMap.GeneralLinearGroup] at f_as_equiv
          have injective_f := (f_as_equiv f_map).injective
          simp [f_as_equiv, f_map] at injective_f
          exact injective_f
      .
        have foo := integrable_on x x
        simp [integrand] at foo
        have re_integrable := MeasureTheory.Integrable.re foo
        simp at re_integrable
        exact re_integrable
      .
        rw [Pi.le_def]
        intro y
        simp
        have foo := inner_self_nonneg (𝕜 := ℂ) (x := toComplexEuclidean ((rep y).val x))
        simp at foo
        exact foo
  }
  . exact Ne.symm (NeZero.ne' (MeasureTheory.Measure.haar Set.univ))
  .
    have compact_image: IsCompact (Set.range (rep)) := by
      sorry

    let new_inner := InnerProductSpace.ofCore inner_product_core

    let apply_rep (h: H) (v: FreshInnerProduct V): FreshInnerProduct V := (rep h).val v

    have v_preserves_inner: ∀ h: H, ∀ v w: FreshInnerProduct V, ⟪(apply_rep h v), (apply_rep h w)⟫ = ⟪v, w⟫ := by
      intro h v w
      unfold inner
      simp [InnerProductSpace.toInner, new_inner]
      dsimp [inner_product_core]
      simp [InnerProductSpace.ofCore]
      simp [apply_rep]
      simp [integrand]
      conv =>
        lhs
        arg 2
        intro f
        --rw [← ContinuousLinearMap.adjoint_inner_right]
      --simp_rw [← ContinuousLinearMap.mul_apply]
      simp_rw [← ContinuousLinearMap.smul_def]
      --simp_rw [inner_smul_left]
      sorry



    let new_inner_prod := fun (v w: V) => MeasureTheory.integral (MeasureTheory.Measure.haar) (integrand v w)
    sorry

-- A product of k unitary groups U(n_1) × U(n_2) × ... × U(n_k), where n_i < n for each n_i
abbrev UnitaryProd (k: ℕ) (n: ℕ) (n_i: Fin k → Fin n) := (i: Fin k) → Matrix.unitaryGroup (Fin (n_i i)) ℂ

lemma inductive_lemma (n: ℕ) (hn: n ≠ 0) (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g: G) (g_not_multiple_I: ∀ z: ℂ, g.val.val ≠ z • 1):
  ∃ k n, ∃ n_i, Nonempty (Subgroup.centralizer {g} ≃* UnitaryProd k n n_i) := by

  -- TODO - this must already exist somewhere
  have nontrivial_fin_n_c: Nontrivial ((Fin n) → ℂ) := by
    use (fun n => 1)
    use (fun n => 2)
    by_contra!
    have foo := congrFun this ⟨0, by omega⟩
    simp at foo

  -- View g as a linear endomorphism
  let g': Module.End _ _ := g.val.val.toLin'
  have exists_eigenvalue := Module.End.exists_eigenvalue g'

  have nonempty_eigenvalues: Nonempty g'.Eigenvalues := by
    obtain ⟨c, hc⟩ := exists_eigenvalue
    use c

  have two_eigenvalues: 2 ≤ Nat.card g'.Eigenvalues := by
    by_contra!
    have card_ne_zero: 0 < Nat.card g'.Eigenvalues := by
      rw [Nat.card_pos_iff]
      refine ⟨nonempty_eigenvalues, ?_⟩
      exact Finite.of_fintype g'.Eigenvalues

    have card_eq_one: Nat.card g'.Eigenvalues = 1 := by
      omega

    -- TODO - there must be a simpler way of proving this
    have unique_eigenvalues: Unique g'.Eigenvalues := {
      uniq := by
        intro x
        rw [Nat.card_eq_one_iff_exists] at card_eq_one
        obtain ⟨z, hz⟩ := card_eq_one
        have first := hz default
        have second := hz x
        rw [second, first]
    }
    sorry


    -- obtain ⟨c, hc⟩ := exists_eigenvalue
    -- obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hc
    -- have has_eigenvalue_iff_c: ∀ z: ℂ, g'.HasEigenvalue z ↔ z = c := by
    --   sorry



    -- have eigenspace_iff := fun μ => Module.End.hasEigenvalue_iff (f := g') (μ := μ)
    -- simp_rw [has_eigenvalue_iff_c] at eigenspace_iff
    -- simp at ei


  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/LinearMap.html#LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
  let a := g.val.val.eigenvalues_conjTranspose_mul_self_nonneg
  sorry
