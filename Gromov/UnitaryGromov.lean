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

def G' (n: ℕ) (ε: ℝ) (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)): Subgroup G := Subgroup.closure (Metric.ball (1 : G) ε)

--instance unitary_matrix_measure_space : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ) := borel _


lemma unitary_implies_det (n: ℕ) (m: Matrix (Fin n) (Fin n) ℂ): m ∈ Matrix.unitaryGroup (Fin n) ℂ → ‖m.det‖ = 1 := by
  intro hm
  have det_unit := Matrix.det_of_mem_unitary hm
  simp [unitary] at det_unit
  rw [Complex.mul_conj, Complex.conj_mul'] at det_unit
  norm_cast at det_unit
  have norm_ne_neg: ‖m.det‖ ≠ -1 := by
    have nonneg := norm_nonneg (m.det)
    linarith
  simp [norm_ne_neg] at det_unit
  exact det_unit.1

lemma unitary_preimage (n: ℕ): (fun (m: Matrix (Fin n) (Fin n) ℂ) => m * (star m)) ⁻¹' {1} = (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  ext a
  simp [Matrix.mem_unitaryGroup_iff]

lemma unitary_closed (n: ℕ): IsClosed (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  rw [← unitary_preimage]
  apply IsClosed.preimage
  . fun_prop
  . simp


instance unitary_proper (n: ℕ): ProperSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  apply ProperSpace.of_isClosed
  apply unitary_closed

#synth Nontrivial (Matrix (Fin 1) (Fin 1) ℂ)


instance compact_unitary (n: ℕ) [Nonempty (Fin n)]: CompactSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  rw [Metric.compactSpace_iff_isBounded_univ]
  rw [Metric.isBounded_iff]
  use 2
  intro x _ y _
  dsimp [dist]
  grw [dist_le_norm_add_norm]
  rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
  linarith

-- Lemma 3.31 (Volume Packing)
lemma volume_packing (n: ℕ) (hn: 0 < n) (ε: ℝ) (hε : 0 < ε): ∃ C: ℝ, ∀ (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)), (G' n ε G).FiniteIndex ∧ (G' n ε G).index ≤ C := by


  have nonempty_fin : Nonempty (Fin n) := by
    exact Fin.pos_iff_nonempty.mp hn

  let compacts_univ: TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin n) ℂ) := {
    carrier := Set.univ,
    isCompact' := by apply CompactSpace.isCompact_univ
    interior_nonempty' := by
      simp
  }

  borelize ↥(Matrix.unitaryGroup (Fin n) ℂ)
  let measure_haar: MeasureTheory.MeasureSpace (Matrix.unitaryGroup (Fin n) ℂ) := {
    volume := MeasureTheory.Measure.haarMeasure compacts_univ
  }

  use 1 / (MeasureTheory.volume (Metric.ball (1 : (Matrix.unitaryGroup (Fin n) ℂ) ) (ε / 2 / 2))).toReal

  intro G
  -- We can find a maximal subset I where ||a - b|| ≥ ε for distinct a, b in I
  let I_sets := { S | S ⊆ G.carrier ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ‖x.val - y.val‖ ≥ ε }
  have maximal_I := zorn_subset I_sets ?_
  . obtain ⟨I, hI⟩ := maximal_I
    have balls_cover: G.carrier ⊆ ⋃ (g ∈ I), Metric.ball g ε := by
      intro a ha
      by_cases a_dist_I: ∀ g ∈ I, ‖a.val - g.val‖ ≥ ε
      . have a_mem_I: a ∈ I := by
          have enlarge_I: {a} ∪ I ∈ I_sets := by
            simp [-Subtype.forall, I_sets]
            simp [Maximal] at hI
            have I_prop := hI.1
            simp [-Subtype.forall, I_sets] at I_prop
            refine ⟨?_, ?_⟩
            . apply Set.insert_subset ha I_prop.1
            . refine ⟨?_, ?_⟩
              . intro b hb a_neq_b
                apply a_dist_I b hb
              . intro c hc
                refine ⟨?_, ?_⟩
                . intro c_neq_a
                  rw [norm_sub_rev]
                  apply a_dist_I c hc
                . intro d hd c_neq_d
                  apply I_prop.2
                  . apply hc
                  . apply hd
                  . apply c_neq_d

          exact Maximal.mem_of_prop_insert hI enlarge_I

        .
          apply Set.mem_sUnion_of_mem (t := Metric.ball a ε)
          . simp [hε]
          . rw [Set.mem_range]
            use a
            -- TODO - this is a really weird way of doing this
            have nonempty_prop: Nonempty (a ∈ I) := by
              exact Nonempty.intro a_mem_I
            rw [Set.iUnion_const]
      . simp [-Subtype.forall, -Subtype.exists] at a_dist_I
        obtain ⟨b, b_mem, b_dist_le⟩ := a_dist_I
        rw [Set.mem_iUnion]
        use b
        simp [b_mem]
        simp [dist]
        rw [dist_eq_norm_sub]
        exact b_dist_le
    -- Note - Vikman uses ε/2, but using ε/4 made things easier (it might actually be false for ε/2)
    have disjoint_balls: I.PairwiseDisjoint (fun g => Metric.ball g ((ε/2)/2)) := by
      intro a a_mem b b_mem a_neq_b
      simp [Maximal] at hI
      have I_prop := hI.1
      simp [-Subtype.forall, I_sets] at I_prop
      have dist_ge := I_prop.2 a a_mem b b_mem a_neq_b
      simp [Disjoint]
      intro X X_subset_A X_subset_B
      by_contra!
      obtain ⟨x, hx⟩ := this
      specialize X_subset_A hx
      specialize X_subset_B hx
      simp at X_subset_A
      simp at X_subset_B
      simp [dist, dist_eq_norm_sub] at X_subset_A
      simp [dist, dist_eq_norm_sub] at X_subset_B
      have triangle := dist_triangle a x b
      simp [dist, dist_eq_norm_sub] at triangle
      rw [norm_sub_rev] at X_subset_A
      grw [X_subset_A, X_subset_B] at triangle
      simp at triangle
      linarith

    have translate_ball (d: ℝ) (hd: 0 < d) (g: (Matrix.unitaryGroup (Fin n) ℂ)): Metric.ball g d = (fun x => g * x) '' (Metric.ball (1: (Matrix.unitaryGroup (Fin n) ℂ)) d) := by
      ext a
      simp
      simp [dist, dist_eq_norm_sub]
      conv =>
        rhs
        arg 1
        arg 1
        equals (star g) * (a.val - g.val) =>
          rw [mul_sub]
          simp
      simp
      rw [CStarRing.norm_mem_unitary_mul]
      simp

    have volume_sum: MeasureTheory.volume (⋃ (g ∈ I), (Metric.ball g ((ε/2)/2))) ≤ 1 := by
      grw [MeasureTheory.measure_mono (t := Set.univ)]
      unfold MeasureTheory.volume
      simp [measure_haar]
      conv =>
        pattern Set.univ
        equals ↑compacts_univ =>
          simp [compacts_univ]

      . rw [MeasureTheory.Measure.haarMeasure_self]
      . simp



    have card_i_le: Nat.card I ≤ (1: ℝ) / (MeasureTheory.volume ((Metric.ball (1: (Matrix.unitaryGroup (Fin n) ℂ)) ((ε / 2)/2)))).toReal := by
      rw [le_div_iff₀]
      simp [MeasureTheory.volume] at volume_sum
      rw [MeasureTheory.measure_biUnion] at volume_sum
      conv at volume_sum =>
        lhs
        arg 1
        intro i
        rw [translate_ball _ (by linarith)]
      unfold MeasureTheory.volume at volume_sum
      simp [measure_haar] at volume_sum
      unfold MeasureTheory.volume
      simp [measure_haar]
      norm_cast
      norm_cast at volume_sum
      by_cases I_infinite: Infinite I
      . simp
      . have I_finite: I.Finite := by
          simpa using I_infinite
        norm_cast at volume_sum
        have finite_I: Finite I := by
          exact I_finite
        rw [ENat.card_eq_coe_natCard] at volume_sum
        norm_cast at volume_sum
        norm_cast
        rw [← ENNReal.toReal_le_toReal] at volume_sum
        rw [ENNReal.toReal_mul] at volume_sum
        simp at volume_sum
        . exact volume_sum
        .
          apply ENNReal.mul_ne_top
          . simp
          . simp
        . simp
      .
        apply Set.PairwiseDisjoint.countable_of_isOpen (s := fun g => Metric.ball g ((ε / 2)/2))
        . exact disjoint_balls
        . intro i hi
          exact Metric.isOpen_ball
        . intro i hi
          simp [hε]
      . exact disjoint_balls
      . intro b hb
        exact measurableSet_ball
      .
        conv =>
          lhs
          equals (0 : ENNReal).toReal => simp
        rw [ENNReal.toReal_lt_toReal]
        . unfold MeasureTheory.volume
          simp [measure_haar]
          apply IsOpen.measure_pos
          exact Metric.isOpen_ball
          simp [hε]
        . simp
        . unfold MeasureTheory.volume
          simp [measure_haar]

    -- Subgroup.index_le_of_leftCoset_cover_const


    have inter_subset (g) (hg: g ∈ G.carrier): Metric.ball (g : (Matrix.unitaryGroup (Fin n) ℂ)) ε ∩ G.carrier ⊆ (fun x => g * x.val) '' (G' n ε G).carrier := by
      rw [translate_ball]
      intro a ha
      simp only [Set.mem_image]

      have a_mem := Set.mem_of_mem_inter_left ha
      simp only [Set.mem_image] at a_mem
      obtain ⟨x, hx⟩ := a_mem
      have a_mem_g := Set.mem_of_mem_inter_right ha
      simp at a_mem_g
      have g_mul_x := hx.2
      rw [eq_comm] at g_mul_x
      rw [← inv_mul_eq_iff_eq_mul] at g_mul_x
      have x_mem_g: x ∈ G := by
        rw [← g_mul_x]
        apply Subgroup.mul_mem
        . simpa using hg
        . exact a_mem_g

      use ⟨x, x_mem_g⟩
      refine ⟨?_, ?_⟩
      .
        apply Subgroup.subset_closure
        exact hx.1
      .
        simp_rw [← g_mul_x]
        simp
      . exact hε

    sorry
    -- refine ⟨?_, ?_⟩
    -- . sorry
    -- .
    --   apply Subgroup.index_le_of_leftCoset_cover_const
    -- sorry
  . intro S S_subset S_chain
    use Set.sUnion S
    refine ⟨?_, ?_⟩
    .
      simp only [ne_eq, ge_iff_le, Subtype.mk.injEq, Set.mem_setOf_eq,
      Set.sUnion_subset_iff, Set.mem_sUnion, forall_exists_index, and_imp, I_sets]

      refine ⟨?_, ?_⟩
      . intro s hs
        simp [I_sets] at S_subset
        specialize S_subset hs
        simp at S_subset
        exact S_subset.1
      . simp [I_sets] at S_subset
        intro a M M_mem_S a_mem_M b N N_mem_S b_mem_N a_neq_b
        simp [IsChain] at S_chain
        specialize S_chain M_mem_S N_mem_S
        by_cases M_eq_N: M = N
        . rw [M_eq_N] at a_mem_M
          specialize S_subset N_mem_S
          simp at S_subset
          have a_b_dist := S_subset.2 a (by simp) (by simp [a_mem_M]) b (by simp) (by simp [b_mem_N]) (by simp [a_neq_b])
          exact a_b_dist
        .
          specialize S_chain M_eq_N
          match S_chain with
          | .inl h =>
            have a_mem_N := h a_mem_M
            specialize S_subset N_mem_S
            simp at S_subset
            have a_b_dist := S_subset.2 a (by simp) (by simp [a_mem_N]) b (by simp) (by simp [b_mem_N]) (by simp [a_neq_b])
            exact a_b_dist
          | .inr h =>
            have b_mem_M := h b_mem_N
            specialize S_subset M_mem_S
            simp at S_subset
            have a_b_dist := S_subset.2 a (by simp) (by simp [a_mem_M]) b (by simp) (by simp [b_mem_M]) (by simp [a_neq_b])
            exact a_b_dist


    . intro s hs
      exact Set.subset_sUnion_of_subset S s (fun ⦃a⦄ a ↦ a) hs

def FreshInnerProduct (V: Type*) := V

instance (V: Type*) [base_comm: AddCommGroup V]: AddCommGroup (FreshInnerProduct V) := base_comm
instance (V: Type*) [AddCommGroup V] [base_module: Module ℂ V]: Module ℂ (FreshInnerProduct V) := base_module

#synth InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 2))

noncomputable def toComplexEuclidean {E: Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℂ E] [ContinuousSMul ℂ E] [FiniteDimensional ℂ E] : E ≃L[ℂ] EuclideanSpace ℂ (Fin <| Module.finrank ℂ E) := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

attribute [-simp] PiLp.inner_apply
--  [NormedAddCommGroup V]  [CompleteSpace V] [InnerProductSpace ℂ V]
-- [MeasurableSpace H] [T2Space H] [BorelSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
lemma weyl_unitarian_trick (G: Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] (H: Subgroup G) [BorelSpace H] [LocallyCompactSpace H] [T2Space H] (V: Type*)  [AddCommGroup V] [TopologicalSpace V]  [Module ℂ V] [T2Space V] [ContinuousSMul ℂ V] [FiniteDimensional ℂ V]  [IsTopologicalAddGroup V] (h_compact: IsCompact (Set.univ : Set H)) (rep: H → (V →L[ℂ] V)ˣ) (h_cont: Continuous rep): True := by
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
