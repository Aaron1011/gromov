import Mathlib

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace
--open scoped ComplexInnerProductSpace


set_option linter.style.longLine false
set_option linter.style.commandStart false

-- Lemma 3.29 (Shrinking Conjugators)
lemma shrinking_conjugators (n : ℕ) (g h : Matrix.unitaryGroup (Fin n) ℂ) :
  ‖⁅g, h⁆.val - 1‖ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
  dsimp only [Bracket.bracket]
  calc
    _ = ‖((g* h).val - (h * g).val) * (g⁻¹ * h⁻¹)‖ := by
      rw [sub_mul]
      repeat rw [← Submonoid.coe_mul]
      conv =>
        rhs
        arg 1
        rhs
        arg 1
        equals 1 => group
      repeat rw [← mul_assoc]
      simp
    _ = ‖((g* h).val - (h * g).val)‖ := by
      rw [ ← Submonoid.coe_mul, CStarRing.norm_mul_coe_unitary]
    _ = ‖(g* h).val - g - h + 1 - ((h*g).val - h - g + 1)‖ := by abel_nf
    _ = ‖(g.val - 1)*(h.val - 1) - (h.val - 1)*(g.val - 1)‖ := by
      conv =>
        rhs
        repeat rw [mul_sub]
        repeat rw [sub_mul]
      field_simp
      abel_nf
    _ ≤ ‖(g.val - 1)*(h.val - 1)‖ + ‖(h.val - 1)*(g.val - 1)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
      linarith [Matrix.l2_opNorm_mul (g.val - 1) (h.val - 1),
                Matrix.l2_opNorm_mul (h.val - 1) (g.val - 1)]

def G' (n : ℕ) (ε : ℝ) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) : Subgroup G :=
  Subgroup.closure (Metric.ball (1 : G) ε)

--instance unitary_matrix_measure_space : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ) := borel _

lemma unitary_implies_det (n : ℕ) (m : Matrix (Fin n) (Fin n) ℂ) :
    m ∈ Matrix.unitaryGroup (Fin n) ℂ → ‖m.det‖ = 1 := by
  intro hm
  have det_unit := Matrix.det_of_mem_unitary hm
  simp [unitary, Complex.mul_conj, Complex.conj_mul'] at det_unit
  norm_cast at det_unit
  have norm_ne_neg : ‖m.det‖ ≠ -1 := by linarith [norm_nonneg (m.det)]
  simpa [norm_ne_neg] using det_unit.1

lemma unitary_preimage (n : ℕ) :
    (fun (m : Matrix (Fin n) (Fin n) ℂ) => m * (star m)) ⁻¹' {1} =
    (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  ext
  simp [Matrix.mem_unitaryGroup_iff]

lemma unitary_closed (n : ℕ) : IsClosed (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  rw [← unitary_preimage]
  apply IsClosed.preimage
  · fun_prop
  · simp


instance unitary_proper (n : ℕ) : ProperSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  apply ProperSpace.of_isClosed
  apply unitary_closed

#synth Nontrivial (Matrix (Fin 1) (Fin 1) ℂ)


instance compact_unitary (n : ℕ) [Nonempty (Fin n)] :
    CompactSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  rw [Metric.compactSpace_iff_isBounded_univ, Metric.isBounded_iff]
  use 2
  intro x _ y _
  dsimp [dist]
  grw [dist_le_norm_add_norm]
  rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
  linarith


abbrev diag_unitary (c : ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun _ => c)

lemma diag_mem_unitary (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) :
    diag_unitary c n ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.mpr <| by
  dsimp [star]
  simp [Complex.mul_conj', hc]

-- Note - `1 = det h'` comes from the fact that 'h' is equal to a commutator [a, b]
-- We specialize to 2 <= n, since we handle the 0 and 1 cases earlier in the proof.
-- This let us put '∃ C' before everything else, which is what we need to obtain a single ε
-- for all our h_n elements
lemma small_dist_matrix (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ (∀ h : Matrix (Fin n) (Fin n) ℂ, h.det = 1 → ∀ c : ℂ, ‖c‖ = 1 → h = diag_unitary c n → (‖h - 1‖ < C) → c = 1) := by

  -- by_cases n_eq_one : n = 1
  -- . use 1
  --   intro ε eps_lt h h_det c hc h_mul h_dist
  --   simp [diag_unitary] at h_mul

  --   have fin_sin_subsingleton : Subsingleton (Fin n) := by
  --     rw [n_eq_one]
  --     exact Fin.subsingleton_one

  have nezero_n : NeZero n := ⟨by omega⟩
  let dists := (fun (x : ℂ) => (‖x - 1‖ : ℝ)) '' ((Units.val '' (rootsOfUnity n ℂ).carrier \ {1}))
  --let dists := (fun x => ‖x - (1 : ℂ)‖) '' (Units.val '' (rootsOfUnity n ℂ).carrier \ {1})

  -- TODO - why can't we combine these into a single line?
  have foo := Set.Finite.exists_minimal (s := dists) ?_ ?_
  obtain ⟨min_dist, ⟨h_min, h_min_prop⟩⟩ := foo
  · refine ⟨min_dist, ?_, ?_⟩
    · simp only [dists, Set.mem_image] at h_min
      obtain ⟨x, x_mem, min_dist_eq⟩ := h_min
      simp at x_mem
      by_contra!
      by_cases min_dist_lt : min_dist < 0
      · rw [← min_dist_eq] at min_dist_lt
        linarith [norm_nonneg (x - 1)]

      simp [show min_dist = 0 by linarith, sub_eq_zero] at min_dist_eq
      have x_neq_one := x_mem.2
      contradiction

    intro h h_det c hc h_mul h_dist

    have c_nonzero : c ≠ 0 := by
      by_contra!
      rw [this] at hc
      simp at hc

    have ne_zero_n : NeZero n := by
      rw [neZero_iff]
      linarith

    let c_unit : Units ℂ := {
        val := c,
        inv := c⁻¹,
        val_inv := by field_simp
        inv_val := by field_simp
      }


    have det_eq_c_n : h.det = c^n := by
      rw [h_mul]
      simp


    rw [h_det] at det_eq_c_n

    rw [h_mul] at h_dist
    simp [diag_unitary] at h_dist

    conv at h_dist =>
      arg 1
      arg 1
      lhs
      equals c • (Matrix.diagonal (fun _ => 1)) =>
        rw [← Matrix.smul_one_eq_diagonal]
        simp

    rw [Matrix.diagonal_one] at h_dist
    conv at h_dist =>
      arg 1
      arg 1
      rhs
      equals (1 : ℂ) • 1 =>
        simp
    rw [← sub_smul] at h_dist
    rw [norm_smul] at h_dist
    conv at h_dist =>
      lhs
      rhs
      equals (1 : ℝ) =>
        bound

    simp at h_dist

    by_contra!

    have c_mem : c ∈ Units.val '' rootsOfUnity n ℂ := by
      use c_unit
      simp [c_unit]
      ext
      simp
      rw [← det_eq_c_n]

    have c_dist_e : min_dist < ‖ c - 1‖ := by
      have c_dist  := h_min_prop (y := ‖c - 1‖)
      simp [dists] at c_dist
      have dist_ge := c_dist c_unit ?_ ?_ ?_
      · by_contra!
        specialize dist_ge (by linarith)
        linarith
      · simp [c_unit]
        ext
        simp
        rw [det_eq_c_n]
      · simp [c_unit]
        rw [Units.ext_iff]
        simp
        simp [this]
      · simp [c_unit]
    linarith
  · simp [dists]
    apply Set.Finite.image
    apply Set.Finite.diff
    apply Set.Finite.image



    have fintype_roots := rootsOfUnity.fintype (k := n) (R  := ℂ)
    have finite_roots : Finite ↥(rootsOfUnity n ℂ) := by infer_instance
    -- TODO - how is this working???
    exact finite_roots
  · --have n_gt_one : 1 < n := by omega
    simp [dists]
    rw [Set.diff_nonempty]
    have roots_mem := Complex.mem_rootsOfUnity (n := n)
    simp

    let my_root : Units ℂ := {
      val := Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)),
      inv := (Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)))⁻¹
      val_inv := by simp
      inv_val := by simp
    }
    use my_root
    simp [my_root]
    refine ⟨?_, ?_⟩
    · ext
      simp
      rw [← Complex.exp_nat_mul, mul_comm]
      field_simp
    · simp [Units.ext_iff, Complex.exp_eq_one_iff]
      intro a
      conv =>
        arg 1
        rhs
        rw [mul_comm]
      field_simp
      by_contra!
      apply mul_left_cancel₀ at this
      · field_simp at this
        have abs_lt_one : ‖((1 : ℂ) / ↑n)‖ < 1 := by
          simp
          have div_le := Nat.cast_inv_le_one (α := ℝ) n
          by_cases inv_eq_one : (n : ℝ)⁻¹ = 1
          · simp at inv_eq_one div_le
            linarith
          · simpa [← ne_iff_lt_iff_le, show n ≠ 1 by omega] using div_le
        by_cases a_eq_zero : a = 0
        · simp [a_eq_zero] at this
          omega
        · simp [this] at abs_lt_one
          norm_cast at abs_lt_one
          linarith [Int.one_le_abs a_eq_zero]
      · norm_num

#print axioms small_dist_matrix

-- Lemma 3.31 (Volume Packing)
set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 500000 in
open Pointwise in
lemma volume_packing (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)), (G' n ε G).FiniteIndex ∧ (G' n ε G).index ≤ C := by


  have nonempty_fin : Nonempty (Fin n) := by
    exact Fin.pos_iff_nonempty.mp hn

  let compacts_univ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin n) ℂ) := {
    carrier := Set.univ,
    isCompact' := by apply CompactSpace.isCompact_univ
    interior_nonempty' := by
      simp
  }

  borelize ↥(Matrix.unitaryGroup (Fin n) ℂ)
  let measure_haar : MeasureTheory.MeasureSpace (Matrix.unitaryGroup (Fin n) ℂ) := {
    volume := MeasureTheory.Measure.haarMeasure compacts_univ
  }

  use 1 / (MeasureTheory.volume (Metric.ball (1 : (Matrix.unitaryGroup (Fin n) ℂ) ) (ε / 2 / 2))).toReal

  intro G
  -- We can find a maximal subset I where ||a - b|| ≥ ε for distinct a, b in I
  let I_sets := { S | S ⊆ G.carrier ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ‖x.val - y.val‖ ≥ ε }
  have maximal_I := zorn_subset I_sets ?_
  · obtain ⟨I, hI⟩ := maximal_I
    have balls_cover : G.carrier ⊆ ⋃ (g ∈ I), Metric.ball g ε := by
      intro a ha
      by_cases a_dist_I : ∀ g ∈ I, ‖a.val - g.val‖ ≥ ε
      · have a_mem_I : a ∈ I := by
          have enlarge_I : {a} ∪ I ∈ I_sets := by
            simp [-Subtype.forall, I_sets]
            simp [Maximal] at hI
            have I_prop := hI.1
            simp [-Subtype.forall, I_sets] at I_prop
            refine ⟨?_, ?_⟩
            · apply Set.insert_subset ha I_prop.1
            · refine ⟨?_, ?_⟩
              · intro b hb a_neq_b
                apply a_dist_I b hb
              · intro c hc
                refine ⟨?_, ?_⟩
                · intro c_neq_a
                  rw [norm_sub_rev]
                  apply a_dist_I c hc
                · intro d hd c_neq_d
                  apply I_prop.2
                  · apply hc
                  · apply hd
                  · apply c_neq_d

          exact Maximal.mem_of_prop_insert hI enlarge_I

        · apply Set.mem_sUnion_of_mem (t := Metric.ball a ε)
          · simp [hε]
          · rw [Set.mem_range]
            use a
            -- TODO - this is a really weird way of doing this
            have nonempty_prop : Nonempty (a ∈ I) := by
              exact Nonempty.intro a_mem_I
            rw [Set.iUnion_const]
      · simp [-Subtype.forall, -Subtype.exists] at a_dist_I
        obtain ⟨b, b_mem, b_dist_le⟩ := a_dist_I
        rw [Set.mem_iUnion]
        use b
        simp [b_mem]
        simp [dist]
        rw [dist_eq_norm_sub]
        exact b_dist_le
    -- Note - Vikman uses ε/2, but using ε/4 made things easier (it might actually be false for ε/2)
    have disjoint_balls : I.PairwiseDisjoint (fun g => Metric.ball g ((ε/2)/2)) := by
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
      have triangle := dist_triangle a x b
      simp [dist, dist_eq_norm_sub] at X_subset_A X_subset_B triangle
      rw [norm_sub_rev] at X_subset_A
      grw [X_subset_A, X_subset_B] at triangle
      simp at triangle
      linarith

    have translate_ball (d : ℝ) (hd : 0 < d) (g : (Matrix.unitaryGroup (Fin n) ℂ)): Metric.ball g d = (fun x => g * x) '' (Metric.ball (1 : (Matrix.unitaryGroup (Fin n) ℂ)) d) := by
      ext a
      simp [dist, dist_eq_norm_sub]
      conv =>
        rhs
        arg 1
        arg 1
        equals (star g) * (a.val - g.val) =>
          rw [mul_sub]
          simp
      simp [CStarRing.norm_mem_unitary_mul]

    have volume_sum : MeasureTheory.volume (⋃ (g ∈ I), (Metric.ball g ((ε/2)/2))) ≤ 1 := by
      grw [MeasureTheory.measure_mono (t := Set.univ)]
      unfold MeasureTheory.volume
      simp [measure_haar]
      conv =>
        pattern Set.univ
        equals ↑compacts_univ =>
          simp [compacts_univ]

      · rw [MeasureTheory.Measure.haarMeasure_self]
      · simp

    have card_i_le : ENat.card I ≤ (1 : ENNReal) / (MeasureTheory.volume ((Metric.ball (1 : (Matrix.unitaryGroup (Fin n) ℂ)) ((ε / 2)/2)))) := by
      rw [div_eq_mul_inv, mul_comm, ← ENNReal.mul_le_iff_le_inv, mul_comm]
      simp at volume_sum
      rw [MeasureTheory.measure_biUnion] at volume_sum
      conv at volume_sum =>
        lhs
        arg 1
        intro i
        rw [translate_ball _ (by linarith)]
      simpa [measure_haar] using volume_sum
      · apply Set.PairwiseDisjoint.countable_of_isOpen (s := fun g => Metric.ball g ((ε / 2)/2))
        · exact disjoint_balls
        · intro i hi
          exact Metric.isOpen_ball
        · intro i hi
          simp [hε]
      · exact disjoint_balls
      · intro i hi
        exact measurableSet_ball
      · apply LT.lt.ne'
        unfold MeasureTheory.volume
        simp [measure_haar]
        apply IsOpen.measure_pos
        exact Metric.isOpen_ball
        simp [hε]
      · unfold MeasureTheory.volume
        simp [measure_haar]
    -- Subgroup.index_le_of_leftCoset_cover_const

    have inter_subset (g) (hg : g ∈ G.carrier): Metric.ball (g : (Matrix.unitaryGroup (Fin n) ℂ)) ε ∩ G.carrier ⊆ (fun x => g * x.val) '' (G' n ε G).carrier := by
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
      have x_mem_g : x ∈ G := by
        rw [← g_mul_x]
        apply Subgroup.mul_mem
        · simpa using hg
        · exact a_mem_g

      use ⟨x, x_mem_g⟩
      refine ⟨?_, ?_⟩
      · apply Subgroup.subset_closure
        exact hx.1
      · simp_rw [← g_mul_x]
        simp
      · exact hε

    have card_lt_top : (ENat.card I).toENNReal < ⊤ := by
      grw [card_i_le]
      simp
      unfold MeasureTheory.volume
      simp [measure_haar]
      apply IsOpen.measure_pos
      exact Metric.isOpen_ball
      simp [hε]
    norm_cast at card_lt_top
    rw [WithTop.lt_top_iff_ne_top] at card_lt_top
    simp at card_lt_top
    rw [ENat.card_eq_top] at card_lt_top
    simp at card_lt_top

    have fintype_I : Fintype I := by
      exact Set.Finite.fintype card_lt_top

    have i_mem_G : ∀ i ∈ I, i ∈ G := by
      intro i i_mem
      simp [Maximal] at hI
      have I_prop := hI.1
      simp [-Subtype.forall, I_sets] at I_prop
      apply (I_prop.1 i_mem)

    --have g_hsmul : HSMul G (Set G) (Set G) := by
    --  infer_instance


    have cosets_cover : (⋃ i ∈ I.toFinset.attach, (((⟨i.val, i_mem_G i.val (Set.mem_toFinset.mp i.property)⟩ : G) • (((G' n ε G)) : Set G)) : (Set G))) = (Set.univ : Set G) := by
      have balls_inter_cover : G.carrier ⊆ ⋃ g ∈ I, ((Metric.ball g ε) ∩ G.carrier) := by
        intro g hg
        specialize balls_cover hg
        simp only [Set.mem_iUnion] at balls_cover
        obtain ⟨i, i_mem, g_mem_i⟩ := balls_cover
        simp only [Set.mem_iUnion]
        use i
        use i_mem
        exact Set.mem_inter g_mem_i hg


      simp
      ext a
      simp only [Set.mem_univ, iff_true]
      have a_mem_g : a.val ∈ G.carrier := by simp
      specialize balls_inter_cover a_mem_g
      simp only [Set.mem_iUnion] at balls_inter_cover
      obtain ⟨i, i_mem, a_mem_i⟩ := balls_inter_cover
      have i_mem_G : i ∈ G.carrier := by
        simp [Maximal] at hI
        have I_prop := hI.1
        simp [-Subtype.forall, I_sets] at I_prop
        apply (I_prop.1 i_mem)
      specialize inter_subset i i_mem_G
      have a_mem := inter_subset a_mem_i
      simp only [Set.mem_image] at a_mem
      obtain ⟨x, hx, a_eq_mul⟩ := a_mem
      simp only [Set.mem_iUnion]
      have i_mem_finset : i ∈ I.toFinset := by
        exact Set.mem_toFinset.mpr i_mem
      use ⟨i, i_mem_finset⟩
      simp
      rw [Set.mem_smul_set]
      use x
      refine ⟨?_, ?_⟩
      · exact hx
      · rw [Subtype.ext_iff]
        simp [a_eq_mul]

    refine ⟨?_, ?_⟩
    · apply Subgroup.finiteIndex_of_leftCoset_cover_const cosets_cover
    · have I_subset_G : I ⊆ G := by
        simp [Maximal] at hI
        have i_mem := hI.1
        simp [I_sets] at i_mem
        exact i_mem.1


      norm_cast at card_i_le
      grw [Subgroup.index_le_of_leftCoset_cover_const (s := I.toFinset.attach) (g := fun a => (⟨a.val, by (
        have a_mem := a.prop
        have a_mem_i : a.val ∈ I := by
          exact Set.mem_toFinset.mp a_mem
        exact I_subset_G a_mem_i
      )⟩ : G))]

      rw [le_div_iff₀]
      · rw [Finset.card_attach, ← Set.ncard_eq_toFinset_card']
        simp at card_i_le
        rw [← Set.Finite.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.toReal_le_toReal] at card_i_le
        simpa using card_i_le
        · apply ENNReal.mul_ne_top
          · simp
          · simp [measure_haar]
        · simp
        · exact card_lt_top
      · simp [measure_haar]
        conv =>
          lhs
          equals (0 : ENNReal).toReal => simp
        rw [ENNReal.toReal_lt_toReal]
        apply IsOpen.measure_pos _ Metric.isOpen_ball (by simp [hε])
        · simp
        · simp
      · exact cosets_cover

    --  (g := fun g => Metric.ball g ((ε / 2) / 2))

    --have coset_bound := Subgroup.index_le_of_leftCoset_cover_const (H := G' n ε G) (s := I)
    --sorry
    -- refine ⟨?_, ?_⟩
    -- . sorry
    -- .
    --   apply Subgroup.index_le_of_leftCoset_cover_const
    -- sorry
  · intro S S_subset S_chain
    refine ⟨S.sUnion, ?_, ?_⟩
    · simp only [ne_eq, ge_iff_le, Set.mem_setOf_eq,
      Set.sUnion_subset_iff, Set.mem_sUnion, forall_exists_index, and_imp, I_sets]

      refine ⟨?_, ?_⟩
      · intro s hs
        simp [I_sets] at S_subset
        specialize S_subset hs
        simp at S_subset
        exact S_subset.1
      · simp [I_sets] at S_subset
        intro a M M_mem_S a_mem_M b N N_mem_S b_mem_N a_neq_b
        simp [IsChain] at S_chain
        specialize S_chain M_mem_S N_mem_S
        by_cases M_eq_N : M = N
        · rw [M_eq_N] at a_mem_M
          specialize S_subset N_mem_S
          simp at S_subset
          exact S_subset.2 a (by simp) (by simp [a_mem_M]) b (by simp) (by simp [b_mem_N]) (by simp [a_neq_b])
        · specialize S_chain M_eq_N
          match S_chain with
          | .inl h =>
            have a_mem_N := h a_mem_M
            specialize S_subset N_mem_S
            simp at S_subset
            exact S_subset.2 a (by simp) (by simp [a_mem_N]) b (by simp) (by simp [b_mem_N]) (by simp [a_neq_b])
          | .inr h =>
            have b_mem_M := h b_mem_N
            specialize S_subset M_mem_S
            simp at S_subset
            exact S_subset.2 a (by simp) (by simp [a_mem_M]) b (by simp) (by simp [b_mem_M]) (by simp [a_neq_b])


    · intro s hs
      exact Set.subset_sUnion_of_subset S s (fun ⦃a⦄ a ↦ a) hs

#print axioms volume_packing


def FreshInnerProduct (V : Type*) := V

instance (V : Type*) [base_comm : AddCommGroup V]: AddCommGroup (FreshInnerProduct V) := base_comm
instance (V : Type*) [AddCommGroup V] [base_module : Module ℂ V]: Module ℂ (FreshInnerProduct V) := base_module

#synth InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 2))

noncomputable def toComplexEuclidean {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℂ E] [ContinuousSMul ℂ E] [FiniteDimensional ℂ E] : E ≃L[ℂ] EuclideanSpace ℂ (Fin <| Module.finrank ℂ E) := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

attribute [-simp] MeasureTheory.Measure.inv_eq_self

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
lemma new_weyl_unitarian_trick {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]  (H : Subgroup (V →L[ℂ] V)ˣ)   [LocallyCompactSpace H] [CompactSpace H]: ∃ S : Subgroup ↥(Matrix.unitaryGroup (Fin (Module.finrank ℂ V)) ℂ), Nonempty (S ≃* H) := by
  let integrand := fun (v w : FreshInnerProduct V) (h : H) => ⟪(h.val.val v), (h.val.val w)⟫
  have continuous_integrand : ∀ v w : FreshInnerProduct V, Continuous fun h : H => integrand v w h := by
    intro v w
    simp only [integrand]
    fun_prop

  borelize (V →L[ℂ] V)ˣ

  --

  have finite_dimensional_fresh : FiniteDimensional ℂ (FreshInnerProduct V) := inferInstanceAs (FiniteDimensional ℂ V)

  have integrable_on : ∀ v w : V, MeasureTheory.Integrable (integrand v w) (MeasureTheory.Measure.haar.inv (G := H)) := by
    intro v w
    rw [← MeasureTheory.integrableOn_univ]
    apply ContinuousOn.integrableOn_compact
    · exact CompactSpace.isCompact_univ
    · apply (continuous_integrand v w).continuousOn


  let inner_product_core : InnerProductSpace.Core ℂ (FreshInnerProduct V) := {
    inner := fun v w => MeasureTheory.integral (MeasureTheory.Measure.haar.inv) (integrand v w)
    conj_inner_symm := by
      intro x y
      simp only [integrand]
      rw [← integral_conj]
      simp_rw [inner_conj_symm]
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
      · exact integrable_on a c
      · exact integrable_on b c
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
      · dsimp only [Filter.EventuallyEq] at hx
        conv at hx =>
          pattern MeasureTheory.Measure.haar.inv
          rw [← MeasureTheory.Measure.restrict_univ (μ := MeasureTheory.Measure.haar.inv)]


        obtain ⟨q, _, inner_q_zero⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae ?_ hx
        conv at inner_q_zero =>
          equals ⟪(q.val.val x), (q.val.val x)⟫ = 0 =>
            rw [← inner_self_ofReal_re]
            field_simp


        simp at inner_q_zero
        have map_iff_zero := LinearMap.map_eq_zero_iff (f := q.val.val.toLinearMap) (x := x) ?_
        · simp at map_iff_zero
          rw [← map_iff_zero]
          exact inner_q_zero
        · -- TODO - find a better way of doing this
          let my_map := (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := V)).toMonoidHom
          let f_map := (Units.map my_map) q.val
          let f_as_equiv := fun f => (LinearMap.GeneralLinearGroup.toLinearEquiv (R := ℂ) (M := V) f)
          simp [LinearMap.GeneralLinearGroup] at f_as_equiv
          have injective_f := (f_as_equiv f_map).injective
          simp [f_as_equiv, f_map] at injective_f
          exact injective_f
      · have foo := integrable_on x x
        simp [integrand] at foo
        simpa using MeasureTheory.Integrable.re foo
      · rw [Pi.le_def]
        intro y
        simpa using inner_self_nonneg (𝕜 := ℂ) (x := (y.val.val x))
  }
  · exact Ne.symm (NeZero.ne' (MeasureTheory.Measure.haar.inv Set.univ))

  let new_inner := InnerProductSpace.ofCore inner_product_core
  let normed_add := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := (FreshInnerProduct V))


  have proper_fresh : ProperSpace (FreshInnerProduct V) := by
    apply FiniteDimensional.proper_rclike ℂ _

  have complete_fresh : CompleteSpace (FreshInnerProduct V) := by
    apply complete_of_proper

  let apply_rep (h : H) (v : FreshInnerProduct V): FreshInnerProduct V := h.val.val v

  have v_preserves_inner : ∀ h : H, ∀ v w : FreshInnerProduct V, ⟪(apply_rep h v), (apply_rep h w)⟫ = ⟪v, w⟫ := by
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

    have mul_right_inv := MeasureTheory.Measure.inv.instIsMulRightInvariant (μ := MeasureTheory.Measure.haar (G := H))
    have mul_left := MeasureTheory.integral_mul_right_eq_self (f := integrand v w) (μ := (MeasureTheory.Measure.haar.inv (G := H)))
    simp only [integrand] at mul_left
    conv at mul_left =>
      intro g
      lhs
      simp

    apply mul_left
  · -- finDimVectorspaceEquiv
    have rank_eq := Module.finrank_eq_rank' ℂ (FreshInnerProduct V)
    have V_equiv := (finDimVectorspaceEquiv (Module.finrank ℂ (FreshInnerProduct V)) rank_eq.symm).toContinuousLinearEquiv
    let V_equiv_fresh : V ≃L[ℂ] (FreshInnerProduct V) := ContinuousLinearEquiv.ofFinrankEq ?_
    have V_map_equiv := ContinuousLinearEquiv.arrowCongr V_equiv V_equiv
    have first := V_equiv.toLinearEquiv
    --have V_linear_arrow_congr := LinearEquiv.arrowCongr V_equiv.toLinearEquiv V_equiv.toLinearEquiv
    let V_fresh_arrow := ContinuousLinearEquiv.arrowCongr V_equiv_fresh V_equiv_fresh

    let new_H_matrix := ContinuousLinearMap.toLinearMap '' (Units.val '' H.carrier)
    -- Deliberate defeq abuse, so that things line up with our integral (which is over plain V)
    let new_H_coe : Set ((FreshInnerProduct V) →ₗ[ℂ] (FreshInnerProduct V)) := new_H_matrix

    have H_hom := Units.coeHom (V →ₗ[ℂ] V)

    have euclidean_linear := LinearEquiv.ofFinrankEq (R := ℂ) V _ finrank_euclideanSpace_fin.symm

    have V_basis := stdOrthonormalBasis ℂ (FreshInnerProduct V)

    let H_matrix := (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) '' new_H_coe


    --let H_matrix := LinearMap.toMatrix' '' (ContinuousLinearMap.toLinearMap '' (V_map_equiv '' (V_fresh_arrow '' (Units.val '' H.carrier))))


    --let H_matrix := LinearMap.toMatrix' '' (ContinuousLinearMap.toLinearMap '' (V_fresh_arrow '' (V_map_equiv '' (Units.val '' H.carrier))))
    have H_mem_unitary : ∀ h ∈ H_matrix, h ∈ Matrix.unitaryGroup (Fin (Module.finrank ℂ (FreshInnerProduct V))) ℂ := by
      intro h h_mem
      simp [H_matrix, new_H_coe, new_H_matrix] at h_mem
      obtain ⟨a, a_mem, ha⟩ := h_mem
      rw [Matrix.mem_unitaryGroup_iff']

      -- defeq abuse - we don't actually want to apply our equivalence from V to FreshInnerProduct V here,
      -- since it might not be the identity, which would break 'mulLeft'
      -- Instead, first convert to plain LinearMap (which we can use defeq abuse with, due to not having
      -- the bundled topology with ContinuousLinearMap)
      let a_fresh : (FreshInnerProduct V) →ₗ[ℂ] (FreshInnerProduct V) := a.val.toLinearMap
      let to_fresh (v : V): FreshInnerProduct V := v

      -- LinearMap.norm_map_iff_inner_map_map
      -- have preserves_inner_iff := (LinearMap.norm_map_iff_inner_map_map a_fresh).mpr ?_
      -- . simp [a_fresh, a_map] at preserves_inner_iff
      --   rw [← LinearMap.star_eq_adjoint] at preserves_inner_iff
      --   rw [← ha]
      --   rw [← ContinuousLinearMap.mul_def] at preserves_inner_iff
      --   apply_fun V_map_equiv at preserves_inner_iff
      --   apply_fun LinearMap.toMatrix' at preserves_inner_iff
      --   sorry
      have preserves_inner : ∀ (x y : V), ⟪a_fresh x, a_fresh y⟫ = ⟪to_fresh x, to_fresh y⟫ := by
        intro v w
        unfold inner
        simp [InnerProductSpace.toInner, new_inner]
        dsimp [inner_product_core]
        simp [InnerProductSpace.ofCore]
        simp [integrand]
        conv =>
          lhs
          arg 2

        have mul_right_inv := MeasureTheory.Measure.inv.instIsMulRightInvariant (μ := MeasureTheory.Measure.haar (G := H))
        have mul_left := MeasureTheory.integral_mul_right_eq_self (f := integrand v w) (μ := (MeasureTheory.Measure.haar.inv (G := H)))
        simp only [integrand] at mul_left
        conv at mul_left =>
          intro g
          lhs
          simp

        have my_mul := mul_left ⟨a, a_mem⟩
        simp at my_mul
        simp [a_fresh]
        exact my_mul

      conv at preserves_inner =>
        intro x y
        lhs
        equals ⟪a_fresh.adjoint (a_fresh x), y⟫ =>
          apply (LinearMap.adjoint_inner_left  _ _ _).symm

      conv at preserves_inner =>
        intro x y
        right
        arg 2
        equals (LinearMap.id (M := FreshInnerProduct V) (R := ℂ)) x =>
          rfl

      conv at preserves_inner =>
        intro x y
        lhs
        arg 2
        rw [← Module.End.mul_apply]

      have inner_specialized (x : FreshInnerProduct V) := preserves_inner x x
      rw [ext_inner_map] at inner_specialized
      rw [← ha]
      simp [a_fresh] at inner_specialized
      apply_fun (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) at inner_specialized
      rw [LinearMap.toMatrix_id] at inner_specialized
      rw [Matrix.star_eq_conjTranspose]
      rw [← LinearMap.toMatrix_adjoint]
      rw [LinearMap.toMatrix_mul] at inner_specialized
      exact inner_specialized



    let H_matrix_subgroup : Subgroup (Matrix.unitaryGroup (Fin (Module.finrank ℂ V)) ℂ) := {
      carrier := Set.range (fun (h : H_matrix) => ⟨h.val, H_mem_unitary h (by simp)⟩),
      mul_mem' := by
        intro x y hx hy
        simp
        use (x * y).val
        simp
        simp at hx
        simp at hy
        simp [H_matrix]
        simp [H_matrix] at hx
        simp [H_matrix] at hy
        obtain ⟨a, ⟨p, p_mem, p_eq_a⟩, a_eq_x⟩ := hx
        obtain ⟨b, ⟨q, q_mem, q_eq_b⟩, b_eq_y⟩ := hy
        simp [new_H_coe, new_H_matrix] at q_mem
        simp [new_H_coe, new_H_matrix] at p_mem
        obtain ⟨y, y_mem, y_eq_q⟩ := q_mem
        obtain ⟨x, x_mem, x_eq_p⟩ := p_mem
        simp [new_H_coe, new_H_matrix]
        refine ⟨?_, rfl⟩
        · refine ⟨x * y, H.mul_mem x_mem y_mem, ?_⟩
          · simp
            conv =>
              lhs
              arg 2
              equals x.val.toLinearMap * y.val.toLinearMap =>
                rfl
            rw [LinearMap.toMatrix_mul, y_eq_q, x_eq_p, p_eq_a, q_eq_b, ← a_eq_x, ← b_eq_y]
      one_mem' := by
        simp [H_matrix, new_H_coe, new_H_matrix]
        use 1
        refine ⟨by simp, ?_⟩
        apply LinearMap.toMatrix_one _
      inv_mem' := by
        simp
        intro a ha b hb a_eq_b
        refine ⟨a⁻¹, ?_, ?_⟩
        · simp [H_matrix, new_H_coe, new_H_matrix] at ⊢ hb
          obtain ⟨x, x_mem, x_eq_b⟩ := hb
          refine ⟨x⁻¹, H.inv_mem x_mem, ?_⟩
          rw [← a_eq_b]
          apply_fun Inv.inv at x_eq_b
          rw [← x_eq_b, eq_comm]
          apply Matrix.inv_eq_right_inv
          rw [← LinearMap.toMatrix_mul]
          conv =>
            arg 1
            arg 2
            equals (x.val * x⁻¹.val).toLinearMap =>
              rfl
          simp
          apply LinearMap.toMatrix_one
        · rw [Matrix.mem_unitaryGroup_iff] at ha
          apply Matrix.inv_eq_right_inv at ha
          simp [ha, Subtype.ext_iff]
    }

    let remove_fresh (h : FreshInnerProduct V →ₗ[ℂ] FreshInnerProduct V): (V →ₗ[ℂ] V) := h

    · use H_matrix_subgroup
      apply Nonempty.intro
      exact {
        toFun := fun h => ⟨{
          val := ((remove_fresh (h.val.val.toLin V_basis.toBasis V_basis.toBasis)).toContinuousLinearMap),
          inv := ((remove_fresh (h.val.val⁻¹.toLin V_basis.toBasis V_basis.toBasis)).toContinuousLinearMap),
          val_inv := by
            simp [remove_fresh]
            ext a
            simp
            conv =>
              lhs
              equals Matrix.toLin V_basis.toBasis V_basis.toBasis (h.val.val * h.val.val⁻¹) a =>
                rw [eq_comm]
                apply Matrix.toLin_mul_apply
            rw [Matrix.mul_nonsing_inv]
            · simp
            · apply Matrix.UnitaryGroup.det_isUnit
          inv_val := by
            simp [remove_fresh]
            ext a
            simp
            conv =>
              lhs
              equals Matrix.toLin V_basis.toBasis V_basis.toBasis (h.val.val⁻¹ * h.val.val) a =>
                rw [eq_comm]
                apply Matrix.toLin_mul_apply
            rw [Matrix.nonsing_inv_mul]
            · simp
            · apply Matrix.UnitaryGroup.det_isUnit
        }, by (
          simp [remove_fresh]
          have h_prop := h.property
          simp only [H_matrix_subgroup] at h_prop
          rw [← Subgroup.mem_carrier] at h_prop
          simp only [] at h_prop
          rw [Set.mem_range] at h_prop
          obtain ⟨a, ha⟩ := h_prop
          have a_prop := a.property
          simp only [H_matrix, new_H_coe, new_H_matrix] at a_prop
          rw [Set.mem_image] at a_prop
          obtain ⟨b, b_mem, b_eq_a⟩ := a_prop
          rw [Set.mem_image] at b_mem
          simp_rw [Set.mem_image] at b_mem
          obtain ⟨c, ⟨d, d_mem, d_eq_c⟩, c_eq_b⟩ := b_mem
          simp_rw [← ha, ← b_eq_a]
          simp
          simp_rw [← c_eq_b, ← d_eq_c]
          conv =>
            arg 2
            arg 1
            equals d.val =>
              rfl

          simp
          rw [Subgroup.mem_carrier] at d_mem
          exact d_mem
        )⟩
        invFun := fun h => ⟨⟨(LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) h.val.val.toLinearMap, by (
          apply H_mem_unitary
          simp [H_matrix, new_H_coe, new_H_matrix]
          use h
          simp
        )⟩, by (
          simp [H_matrix_subgroup, H_matrix, new_H_coe, new_H_matrix]
          use h
          simp
        )⟩,
        left_inv := by
          intro h
          simp
          rw [Subtype.ext_iff]
          simp [remove_fresh]
        right_inv := by
          intro h
          simp
          simp [remove_fresh]
          ext a
          simp
        map_mul' := by
          intro x y
          simp [remove_fresh]
          ext a
          simp
          apply Matrix.toLin_mul_apply
      }
    · rfl

#print axioms new_weyl_unitarian_trick

-- A product of k unitary groups U(n_1) × U(n_2) × ... × U(n_k), where n_i < n for each n_i
abbrev UnitaryProd (k : ℕ) (n : ℕ) (n_i : Fin k → Fin n) := (i : Fin k) → Matrix.unitaryGroup (Fin (n_i i)) ℂ

structure InductiveLemmaData (n : ℕ) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g : G) where
  k : ℕ
  k_pos : 0 < k
  n_i : Fin k → ℕ
  n_i_lt : ∀ i : Fin k, n_i i < n
  positive_n_i : ∀ i : Fin k, n_i i ≠ 0
  groups : (i : Fin k) → Subgroup (Matrix.unitaryGroup (Fin (n_i i)) ℂ)
  iso : Subgroup.centralizer {g} ≃* ((i : Fin k) → (groups i))

-- Lemma 3.30
lemma inductive_lemma (n : ℕ) (hn : 2 ≤ n) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g : G) (g_not_multiple_I : ∀ z : ℂ, g.val.val ≠ z • 1):
  Nonempty (InductiveLemmaData n G g) := by

  let g_end : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' g
  -- TODO - is there a better way to write the space as a finite union of generalized eigenspaces?
  have eigenspace_span := Module.End.iSup_maxGenEigenspace_eq_top g_end
  rw [← iSup_ne_bot_subtype] at eigenspace_span
  have subtype_eq : { z : ℂ // g_end.maxGenEigenspace z ≠ ⊥ } = { z : ℂ // ∃ n, g_end.HasGenEigenvalue z n} := by
    simp only [Module.End.maxGenEigenspace]
    simp_rw [Module.End.genEigenspace_top]
    conv =>
      lhs
      arg 1
      intro z
      simp
      arg 1
      intro x
      rw [← ne_eq]
      rw [← Module.End.hasGenEigenvalue_iff]

  have finite_eigenvalues := Module.End.finite_hasEigenvalue g_end
  have subtype_finite : Finite { z : ℂ // ∃ n, g_end.HasGenEigenvalue z n} := by
    have finite_setof : Finite (setOf g_end.HasEigenvalue) := by
      simp
      exact finite_eigenvalues
    apply Finite.of_injective (β := setOf g_end.HasEigenvalue) (f := fun z => (by
      have z_mem := Classical.choose_spec z.prop
      let other := Module.End.hasEigenvalue_of_hasGenEigenvalue z_mem
      exact ⟨z, other⟩
    ))
    simp
    exact Isometry.injective fun x1 ↦ congrFun rfl

  have nontrival_coord : Nontrivial (Fin n → ℂ) := by
    have nontrivial_fin : Nontrivial (Fin n) := by
      exact Fin.nontrivial_iff_two_le.mpr hn
    infer_instance

  have n_gt : 0 < n := by omega

  let list_eigenvalues := finite_eigenvalues.toFinset.toList

  have two_eigenvalues : 2 ≤ list_eigenvalues.length := by
    by_contra!
    by_cases len_eq_zero : list_eigenvalues.length = 0
    · simp [list_eigenvalues] at len_eq_zero
      obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue g_end
      have eigenvalues_nonempty : setOf g_end.HasEigenvalue ≠ ∅ := by
        rw [← Set.nonempty_iff_ne_empty]
        apply Set.nonempty_of_mem hz
      contradiction
    · have len_eq_one : list_eigenvalues.length = 1 := by
        omega

      obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue g_end
      have z_gen_eigen : g_end.HasGenEigenvalue z 1 := by
        rw [Module.End.hasGenEigenvalue_iff]
        exact hz
      rw [Module.End.hasGenEigenvalue_iff] at z_gen_eigen
      -- Since we only have a single eigenvalue, we only have one non-bot maxGenEigenspace
      have unique_subtype : Unique { i // g_end.maxGenEigenspace i ≠ ⊥ } := by
        exact {
          default := ⟨z, by (
            simp only [Module.End.maxGenEigenspace]
            simp_rw [Module.End.genEigenspace_top]
            rw [ne_eq]
            rw [iSup_eq_bot]
            simp
            use 1
          )⟩
          uniq := by
            intro x
            have x_prop := x.property
            simp only [Module.End.maxGenEigenspace] at x_prop
            simp_rw [Module.End.genEigenspace_top] at x_prop
            rw [ne_eq] at x_prop
            rw [iSup_eq_bot] at x_prop
            simp at x_prop
            obtain ⟨y, hy⟩ := x_prop
            rw [← ne_eq] at hy
            rw [← Module.End.hasGenEigenvalue_iff] at hy
            have y_eigen := Module.End.hasEigenvalue_of_hasGenEigenvalue hy
            simp [list_eigenvalues] at len_eq_one
            rw [Finset.card_eq_one] at len_eq_one
            obtain ⟨p, hp⟩ := len_eq_one
            -- TODO - clean this up
            have eigenvalues_eq_singleton : setOf g_end.HasEigenvalue = {p} := by
              ext a
              refine ⟨?_, ?_⟩
              · intro ha
                have foo := Set.Finite.mem_toFinset finite_eigenvalues (a := a)
                simp only [] at foo
                simp only [Set.mem_setOf_eq] at ha
                have mem_finite := foo.mpr ha
                rw [hp] at mem_finite
                simpa using mem_finite
              · intro ha
                simp at ha
                have a_mem_finset : a ∈ finite_eigenvalues.toFinset := by
                  rw [hp]
                  simp
                  exact ha
                simp at a_mem_finset
                exact a_mem_finset

            simp at eigenvalues_eq_singleton
            have x_mem : x.val ∈ setOf g_end.HasEigenvalue := by
              simp
              exact y_eigen

            have z_mem : z ∈ setOf g_end.HasEigenvalue := by
              simp
              exact hz
            rw [eigenvalues_eq_singleton] at z_mem
            simp at z_mem
            rw [eigenvalues_eq_singleton] at x_mem
            simp at x_mem
            ext
            simp
            rw [x_mem]
            rw [← z_mem]
        }


      rw [iSup_unique] at eigenspace_span
      rw [Module.End.maxGenEigenspace] at eigenspace_span
      -- We need to somehow use the fact that the matrix is unitary, and conclude
      -- than 'genEigenspace ⊤ = genEeingespace 1', so a single eigenspace spans the whole space.
      -- THis implies that g is diagonal, contradicting 'g_not_multiple_I'
      sorry
      -- conv at eigenspace_span =>
      --   arg 1
      --   arg 1
      --   arg 2
      --   arg 1
      --   equals ⟨z, by (
      --     simp [Module.End.genEigenspace_top]
      --     use 1

      --   )⟩ =>
      --     apply Unique.default_eq

      -- rw [Module.End.genEigenspace_one] at eigenspace_span
      -- rw [Module.End.genEigenspace_top] at eigenspace_span

  have nontrivial_len :  Nontrivial (Fin list_eigenvalues.length) := by
    exact Fin.nontrivial_iff_two_le.mpr two_eigenvalues

  let first_subspace := Module.End.genEigenspace g_end (list_eigenvalues.get ⟨0, by linarith⟩) ⊤
  obtain ⟨second_subspace, first_compl_second⟩ := Submodule.exists_isCompl first_subspace
  --have i_j_disjoint := Module.End.disjoint_genEigenspace g_end vals_neq ⊤ ⊤

  have first_generalized_eigenvalue : g_end.HasGenEigenvalue (list_eigenvalues.get ⟨0, by linarith⟩) 1 := by
    rw [Module.End.hasGenEigenvalue_iff_hasEigenvalue]
    · have zero_mem : list_eigenvalues.get ⟨0, by linarith⟩ ∈ list_eigenvalues := by
        simp [list_eigenvalues]

      unfold list_eigenvalues at zero_mem
      simp only [Finset.mem_toList] at zero_mem
      simp at zero_mem
      exact zero_mem
    · simp


  have first_not_bot := Module.End.hasGenEigenvalue_iff.mp first_generalized_eigenvalue
  -- simp [IsCompl] at first_compl_second
  -- have j_top_not_bot : second_subspace ≠ ⊥ := by
  --   rw [← bot_lt_iff_ne_bot] at first_not_bot
  --   grw [Module.End.genEigenspace_le_maximal] at first_not_bot
  --   rw [bot_lt_iff_ne_bot] at first_not_bot
  --   exact j_not_bot


  have foo := Module.End.pos_finrank_genEigenspace_of_hasEigenvalue (f := g_end) (μ := 1) (k := 2)
  exact Nonempty.intro {
    k := 2,
    k_pos := by
      linarith
    n_i := fun i => if i = 0 then (Module.finrank ℂ (first_subspace)) else Module.finrank ℂ (second_subspace),
    n_i_lt := fun i => by
      split_ifs
      calc
        _ < Module.finrank ℂ (Fin n → ℂ) := by
          apply Submodule.finrank_lt
          by_contra!
          sorry
          -- have distinct : ∃ j : Fin list_eigenvalues.length, i ≠ j := by
          --   have foo := exists_ne i
          --   obtain ⟨j, hj⟩ := foo
          --   use j
          --   exact hj.symm

          -- obtain ⟨j, hj⟩ := distinct
          -- have vals_neq : list_eigenvalues.get i ≠ list_eigenvalues.get j := by
          --   simp [list_eigenvalues]
          --   have no_dup := Finset.nodup_toList finite_eigenvalues.toFinset
          --   rw [List.Nodup.getElem_inj_iff]
          --   . omega
          --   . exact no_dup


          --   --rw [List.Nodup.get_inj_iff no_dup]
          -- let j_subspace := Module.End.genEigenspace g_end (list_eigenvalues.get j) ⊤
          -- have i_j_disjoint := Module.End.disjoint_genEigenspace g_end vals_neq ⊤ ⊤

          -- have j_mem_tolist : list_eigenvalues.get j ∈ list_eigenvalues := by
          --   simp [list_eigenvalues]

          -- unfold list_eigenvalues at j_mem_tolist
          -- simp only [Finset.mem_toList] at j_mem_tolist
          -- simp at j_mem_tolist
          -- have j_generalized_eigenvalue : g_end.HasGenEigenvalue (list_eigenvalues.get j) 1 := by
          --   rw [Module.End.hasGenEigenvalue_iff_hasEigenvalue]
          --   . exact j_mem_tolist
          --   . simp

          -- -- Our 'j' eigenspace is not the trivial (bot) space
          -- have j_not_bot := Module.End.hasGenEigenvalue_iff.mp j_generalized_eigenvalue
          -- have j_top_not_bot : (g_end.genEigenspace (list_eigenvalues.get j)) ⊤ ≠ ⊥ := by
          --   rw [← bot_lt_iff_ne_bot] at j_not_bot
          --   grw [Module.End.genEigenspace_le_maximal] at j_not_bot
          --   rw [bot_lt_iff_ne_bot] at j_not_bot
          --   exact j_not_bot

          -- -- The i and j spaces are disjoint and j is not ⊥, so i is not ⊤
          -- have i_ne_top : (g_end.genEigenspace (list_eigenvalues.get i)) ⊤ ≠ ⊤ := by
          --   by_contra!
          --   rw [this] at i_j_disjoint
          --   simp at i_j_disjoint
          --   contradiction

          -- contradiction



        _ ≤ n := by
          simp
      sorry




    positive_n_i := by
      -- intro i
      -- have i_mem_tolist : list_eigenvalues.get i ∈ list_eigenvalues := by
      --   simp [list_eigenvalues]

      -- unfold list_eigenvalues at i_mem_tolist
      -- simp only [Finset.mem_toList] at i_mem_tolist
      -- simp at i_mem_tolist
      -- have increasing := Module.End.genEigenspace_le_maximal g_end (list_eigenvalues.get i) 1
      -- apply Submodule.finrank_mono at increasing
      -- have pos_rank := Module.End.pos_finrank_genEigenspace_of_hasEigenvalue (k := 1) i_mem_tolist (by simp)
      -- simp at pos_rank
      -- simp at increasing
      -- grw [increasing] at pos_rank
      -- simp only [Fin.eta, List.get_eq_getElem, ne_eq, list_eigenvalues]
      sorry
      --linarith
    groups := fun i => (by
    --  --let mapped := Submodule.map g.val.val.toLin' (g_end.genEigenspace (list_eigenvalues.get i) ⊤)
    --  let g_restrict := g_end.restrict (p := g_end.genEigenspace (list_eigenvalues.get i) ⊤) (q := g_end.genEigenspace (list_eigenvalues.get i) ⊤) (by sorry)

    --  let dim := (Module.finrank ℂ (Module.End.genEigenspace g_end (list_eigenvalues.get ⟨i, by (
    --   simp
    -- )⟩) ⊤))
    --  have ⟨k, basis⟩ := Submodule.basisOfPid (Pi.basisFun _ _) ((g_end.genEigenspace (list_eigenvalues.get i)) ⊤) (ι := Fin (n))
    --  let g_restrict_matrix := (LinearMap.toMatrix basis basis) g_restrict
    --  have rank_eq := Submodule.finrank_eq_rank _ _ ((g_end.genEigenspace 1) ⊤)
     sorry
      --have preserves := Module.End.mapsTo_genEigenspace_of_comm ?_ (f := g_end) (g := Matrix.toLin' g)
    )
    iso := by sorry
    --iso := Subgroup.centralizer {g} ≃* (fun i => G)
  }

  -- Module.End.maxGenEigenspace_eq_genEigenspace_finrank

  -- simp [Module.End.maxGenEigenspace] at eigenspace_span
  -- simp_rw [Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex] at eigenspace_span

  -- --rw [iSup_congr_Prop] at eigenspace_span
  -- --rw [subtype_eq] at eigenspace_span
  -- -- Module.End.hasGenEigenvalue_iff
  -- conv at eigenspace_span =>
  --   lhs
  --   arg 1

  -- have f_map (h : G) (h_comm : Commute g h): True := by
  --   have preserves := Module.End.mapsTo_genEigenspace_of_comm ?_ (f := g_end) (g := Matrix.toLin' h.val.val)

  --   -- Module.End.maxGenEigenspace_eq_genEigenspace_finrank
  --   -- LinearMap.toMatrix'

  --   let h_end :  Module.End ℂ (Fin n → ℂ) := Matrix.toLin' h
  --   have test_preserves := preserves 1 ⊤
  --   let h_restrict := h_end.restrict test_preserves
  --   have ⟨k, basis⟩ := Submodule.basisOfPid (by sorry) ((g_end.genEigenspace 1) ⊤) (ι := Fin 2)
  --   let h_restrict_matrix := (LinearMap.toMatrix basis basis) h_restrict
  --   have rank_eq := Submodule.finrank_eq_rank _ _ ((g_end.genEigenspace 1) ⊤)


  --   sorry

  -- -- TODO - this must already exist somewhere
  -- have nontrivial_fin_n_c : Nontrivial ((Fin n) → ℂ) := by
  --   use (fun n => 1)
  --   use (fun n => 2)
  --   by_contra!
  --   have foo := congrFun this ⟨0, by omega⟩
  --   simp at foo

  -- -- View g as a linear endomorphism
  -- let g': Module.End _ _ := g.val.val.toLin'
  -- have exists_eigenvalue := Module.End.exists_eigenvalue g'

  -- have nonempty_eigenvalues : Nonempty g'.Eigenvalues := by
  --   obtain ⟨c, hc⟩ := exists_eigenvalue
  --   use c

  -- have two_eigenvalues : 2 ≤ Nat.card g'.Eigenvalues := by
  --   by_contra!
  --   have card_ne_zero : 0 < Nat.card g'.Eigenvalues := by
  --     rw [Nat.card_pos_iff]
  --     refine ⟨nonempty_eigenvalues, ?_⟩
  --     exact Finite.of_fintype g'.Eigenvalues

  --   have card_eq_one : Nat.card g'.Eigenvalues = 1 := by
  --     omega

  --   -- TODO - there must be a simpler way of proving this
  --   have unique_eigenvalues : Unique g'.Eigenvalues := {
  --     uniq := by
  --       intro x
  --       rw [Nat.card_eq_one_iff_exists] at card_eq_one
  --       obtain ⟨z, hz⟩ := card_eq_one
  --       have first := hz default
  --       have second := hz x
  --       rw [second, first]
  --   }
  --   sorry


  --   -- obtain ⟨c, hc⟩ := exists_eigenvalue
  --   -- obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hc
  --   -- have has_eigenvalue_iff_c : ∀ z : ℂ, g'.HasEigenvalue z ↔ z = c := by
  --   --   sorry



  --   -- have eigenspace_iff := fun μ => Module.End.hasEigenvalue_iff (f := g') (μ := μ)
  --   -- simp_rw [has_eigenvalue_iff_c] at eigenspace_iff
  --   -- simp at ei


  -- -- https ://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/LinearMap.html#LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
  -- let a := g.val.val.eigenvalues_conjTranspose_mul_self_nonneg
  -- sorry

#check Pi.commSemigroup

-- A sufficiently small epsilon to use for the h_n elements in Theorem 3.8 (independent of the choice of n)
noncomputable def H_n_eps {d : ℕ} (hd : 2 ≤ d): ℝ := (min ((1 : ℝ) / 60) ((small_dist_matrix d hd).choose / 2))

-- H_n_eps is less than 1/2
lemma H_n_eps_lt {d : ℕ} (hd : 2 ≤ d) : H_n_eps hd < ((1 : ℝ) / 4) := by
  simp [H_n_eps]
  left
  norm_num

lemma H_n_eps_lt_one_fifty {d : ℕ} (hd : 2 ≤ d) : H_n_eps hd < ((1 : ℝ) / 50) := by
  simp [H_n_eps]
  left
  norm_num

lemma H_n_eps_pos {d : ℕ} (hd : 2 ≤ d) : 0 < H_n_eps hd := by
  simp [H_n_eps]
  have small_pos := (small_dist_matrix d hd).choose_spec
  linarith


open scoped Finset
open scoped Pointwise


structure HnData where
  d : ℕ
  hd : 2 ≤ d
  G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)
  G_central_trivial : ∀ g : G, g ∈ Set.center G → ∃ z : ℂ, g.val.val = z • 1
  S : Set G
  S_generates : Subgroup.closure S = ⊤
  S_finite : S.Finite
  S_one: 1 ∈ S
  S_inv: ∀ s ∈ S, s⁻¹ ∈ S
  S_dist : ∀ s ∈ S, ‖s.val.val - 1‖ ≤ (H_n_eps hd)
  S_poly_const: ℕ
  S_poly_const_pos: 0 ≠ S_poly_const
  S_poly_deg: ℕ
  S_poly: ∀ r: ℕ, #(S_finite.toFinset ^ r) ≤ S_poly_const * (r ^ S_poly_deg)
  h : S
  h_nontrivial : ¬ ∃(z : ℂ), h.val.val.val = z • 1

structure Theorem3_8_Data (data: HnData) where
  g: data.G
  g_nontrivial : ¬ ∃ z : ℂ, g.val.val = z • 1
  g_dist_nonzero : ‖g.val.val - 1‖ ≠ 0
  g_dist : ‖g.val.val - 1‖ ≤ (H_n_eps data.hd)


-- The element of S in the left-hand side of the commutator in theorem_3_8_h_n
theorem theorem_3_8_h_n_left_S (data: HnData) (prev: Theorem3_8_Data data): ∃ s : data.S, ∀ z : ℂ, ⁅s.val.val, prev.g.val⁆.val ≠ z • 1 := by
  by_contra!
  have comm_eq_id : ∀ s : data.S, ⁅s.val.val, prev.g.val⁆ = 1 := by
    intro s
    obtain ⟨z, comm_eq_z⟩ := this s
    have norm_z : ‖z‖ = 1 := by
      have z_mul_unitary : z • 1 ∈ Matrix.unitaryGroup (Fin data.d) ℂ := by
        rw [← comm_eq_z]
        simp


      have det_unitary := Matrix.det_of_mem_unitary z_mul_unitary
      simp at det_unitary
      apply CStarRing.norm_of_mem_unitary at det_unitary
      simp at det_unitary
      have d_ne_zero : data.d ≠ 0 := by
        have hd := data.hd
        omega
      have z_pow := (pow_eq_one_iff_of_ne_zero (a := ‖z‖) d_ne_zero).mp det_unitary
      have norm_pos : 0 ≤ ‖z‖ := by
        positivity
      have norm_not_neg : ‖z‖ ≠ -1 := by
        linarith

      simp [norm_not_neg] at z_pow
      exact z_pow
    have det_one : ⁅s.val.val, prev.g.val⁆.val.det = 1 := by
      simp [Bracket.bracket]
      rw [Matrix.star_eq_conjTranspose]
      rw [Matrix.star_eq_conjTranspose]
      rw [mul_comm]
      rw [mul_assoc]
      nth_rw 2 [mul_comm]
      rw [mul_assoc]
      rw [← Matrix.det_mul]
      rw [← Matrix.star_eq_conjTranspose]
      rw [← Matrix.star_eq_conjTranspose]
      rw [Matrix.UnitaryGroup.star_mul_self]
      rw [← mul_assoc]
      rw [← Matrix.det_mul]
      rw [Matrix.UnitaryGroup.star_mul_self]
      simp

    have prev_prop := prev.g_dist
    have norm_le := shrinking_conjugators data.d s.val prev.g.val
    grw [data.S_dist s, prev_prop] at norm_le
    · have two_mul_le : 2 * (H_n_eps data.hd) ≤ 1 := by
        grw [H_n_eps_lt data.hd]
        norm_num
      grw [two_mul_le] at norm_le
      · simp at norm_le


        --rw [comm_eq_z] at norm_le
        let C := (small_dist_matrix data.d data.hd).choose

        have H_eps_lt_C : H_n_eps data.hd < C := by
          rw [H_n_eps]
          unfold C
          grw [min_le_right]
          simp
          have my_spec := (small_dist_matrix data.d data.hd).choose_spec
          have gt_zero := my_spec.1
          linarith

        unfold C at H_eps_lt_C


        obtain ⟨C_pos, small_eps⟩ := (small_dist_matrix data.d data.hd).choose_spec
        have z_eq_one := small_eps ⁅s.val.val, prev.g.val⁆.val det_one z norm_z (by
          simp [diag_unitary]
          rw [← Matrix.smul_one_eq_diagonal]
          exact comm_eq_z
        ) (by
          grw [norm_le]
          exact H_eps_lt_C
        )
        simp [z_eq_one] at comm_eq_z
        exact comm_eq_z
      · -- TODO - deduplicate this
        simp [H_n_eps]
        have C_pos := (small_dist_matrix data.d data.hd).choose_spec.1
        linarith
    · simp [H_n_eps]
      have C_pos := (small_dist_matrix data.d data.hd).choose_spec.1
      linarith
    · simp
  · have subgroup_le := Subgroup.closure_le_centralizer_centralizer data.S
    simp [data.S_generates] at subgroup_le
    have prev_mem_centralizer : prev.g ∈ Subgroup.centralizer data.S := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h_comm := comm_eq_id ⟨s, hs⟩
      simp [Bracket.bracket] at h_comm
      rw [mul_assoc] at h_comm
      apply eq_inv_of_mul_eq_one_left at h_comm
      simp at h_comm
      rw [Subtype.ext_iff]
      simp
      exact h_comm

    have prev_central := subgroup_le prev_mem_centralizer
    have prev_trivial := data.G_central_trivial _ prev_central
    have prev_nontrivial := prev.g_nontrivial
    contradiction


-- 'h' is our initial element - we define ε in terms of ‖h - 1‖, so that we can obtain the proper bound
-- for the commutators in the inductive case
set_option maxHeartbeats 500000 in
noncomputable def theorem_3_8_h_n (data : HnData) (n : ℕ): Theorem3_8_Data data := match hn : n with
  | 0 => {
    g := data.h,
    g_nontrivial := data.h_nontrivial,
    g_dist_nonzero := by
      by_contra!
      simp at this
      rw [sub_eq_zero] at this
      have h_nontrivial := data.h_nontrivial
      simp at h_nontrivial
      have h_neq := h_nontrivial 1
      simp at h_neq
      simp at this
      contradiction
    ,
    g_dist := data.S_dist data.h data.h.property
  }
  | k + 1 => by
    -- TODO - why do we get a heartbeat timeout if we inline 'prev'?
    let prev := (theorem_3_8_h_n data k)
    use ⁅(theorem_3_8_h_n_left_S data prev).choose.val, prev.g⁆
    · rw [not_exists]
      exact (theorem_3_8_h_n_left_S data prev).choose_spec
    · by_contra!
      simp at this
      rw [sub_eq_zero] at this
      have my_nontrivial := (theorem_3_8_h_n_left_S data prev).choose_spec 1
      simp at my_nontrivial
      simp at this
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      rw [commutatorElement_eq_one_iff_mul_comm] at my_nontrivial
      rw [Subtype.ext_iff] at this
      simp at this
      contradiction
    · have my_shrink := shrinking_conjugators data.d (theorem_3_8_h_n_left_S data prev).choose prev.g
      conv =>
        lhs
        arg 1
        lhs
        equals ⁅ (theorem_3_8_h_n_left_S data prev).choose.val.val, prev.g.val ⁆.val =>
          rw [commutatorElement_def, commutatorElement_def]
          rfl
      grw [my_shrink]
      have prev_prop := prev.g_dist
      grw [prev_prop]
      have comm_choose_le := data.S_dist (theorem_3_8_h_n_left_S data prev).choose (by simp)
      grw [comm_choose_le]
      have two_mul_le : 2 * (H_n_eps data.hd) ≤ 1 := by
        grw [H_n_eps_lt data.hd]
        norm_num
      grw [two_mul_le]
      · simp
      · linarith [H_n_eps_pos data.hd]
      · linarith [H_n_eps_pos data.hd]


termination_by n
decreasing_by
  simp

#print axioms theorem_3_8_h_n

lemma unitary_shrink {n : ℕ} (a b : Matrix.unitaryGroup (Fin n) ℂ): ‖(a * b).val - 1‖ ≤ ‖a.val - 1‖ + ‖b.val - 1‖ := by
  conv =>
    lhs
    arg 1
    arg 1
    equals (a.val - 1) * b + b =>
      rw [sub_mul]
      field_simp

  rw [← add_sub]
  grw [norm_add_le]
  rw [CStarRing.norm_mul_coe_unitary]

lemma coe_comm_g {data : HnData} (a b : data.G): ⁅a.val, b.val⁆ = ⁅a, b⁆.val := by
  rw [commutatorElement_def]
  rw [commutatorElement_def]
  norm_cast

lemma H_n_upper_bound (data : HnData) (n : ℕ): ‖(theorem_3_8_h_n data (n + 1)).g.val.val - 1‖ ≤ 2 * (H_n_eps data.hd) * ‖(theorem_3_8_h_n data (n)).g.val.val - 1‖ := by
  conv =>
    lhs
    unfold theorem_3_8_h_n
  simp
  have coe_comm_g (a b : data.G): ⁅a.val, b.val⁆ = ⁅a, b⁆.val := by
    rw [commutatorElement_def]
    rw [commutatorElement_def]
    norm_cast

  rw [← coe_comm_g]
  grw [shrinking_conjugators]
  grw [data.S_dist]
  simp

lemma H_n_upper_bound_iter (data : HnData) {a : ℕ} (n : ℕ): ‖(theorem_3_8_h_n data (a + n)).g.val.val - 1‖ ≤ ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ * 2^n * (H_n_eps data.hd)^n  := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [← add_assoc]
    grw [H_n_upper_bound]
    grw [ih]
    abel_nf
    · ring_nf
      rfl
    · simp
      have H_eps_pos := H_n_eps_pos data.hd
      linarith


lemma H_n_single_pow {n : ℕ} {m : ℕ} (data : HnData): ‖((theorem_3_8_h_n data n).g.val^m).val - 1‖ ≤ m * ‖(theorem_3_8_h_n data n).g.val.val - 1‖ := by
  induction m with
  | zero =>
    simp [pow_zero]
  | succ m ih =>
    rw [pow_succ]
    grw [unitary_shrink]
    grw [ih]
    field_simp
    rw [add_mul]
    simp

lemma H_n_pow_le  {a k : ℕ } {m : ℕ} (a_k_lt : a + k ≤ m)  (pows : Fin m → ℕ) (data : HnData):
  ‖(List.ofFn (fun (i : Fin (k)) => (theorem_3_8_h_n data (a + i)).g^(pows ⟨(a + i), by (have foo := i.isLt; omega)⟩))).prod.val.val - 1‖ ≤ ∑ (i : Fin k), (pows ⟨(a + i), by (have foo := i.isLt; omega)⟩) * ‖(theorem_3_8_h_n data (a + i)).g.val.val - 1‖ := by
  induction k with
  | zero =>
    simp [List.ofFn, List.prod_nil]
  | succ k ih =>
    simp only [ne_eq, List.ofFn_succ']
    simp only [Fin.coe_castSucc, Fin.val_last, List.concat_eq_append, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, Subgroup.val_list_prod,
      List.map_ofFn]

    rw [Subgroup.coe_mul]
    grw [unitary_shrink]
    have prev_le := ih (by linarith)
    grw [prev_le]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_range_succ]
    rw [SubmonoidClass.coe_pow]
    grw [H_n_single_pow]
    simp
    nth_rw 2 [← Finset.sum_attach]


    conv =>
      rhs
      arg 2
      intro x
      equals if h : ↑x < k then ↑(pows ⟨↑(a + x), by omega⟩) * ‖(theorem_3_8_h_n data ↑(a + x)).g.val.val - 1‖ else 0 =>
        have x_lt_m := x.property
        rw [Finset.mem_range] at x_lt_m
        have x_lt_m_succ : x.val < k + 1 := by
          omega
        simp [x_lt_m, x_lt_m_succ]

    rw [← Finset.sum_attach]


-- Equation 3.16
lemma H_n_prod_le_k {a k : ℕ } {m : ℕ} (a_k_lt : a + k + 1 ≤ m) (c : ℝ) (c_pos : 0 < c) (c_lt : c < 1 / 40) (pows : Fin m → ℕ) (data : HnData)
 (pows_le : ∀ i : Fin m, (pows i) ≤ c * (H_n_eps data.hd)⁻¹) :
  ‖(List.ofFn (fun (i : Fin (k)) => (theorem_3_8_h_n data ((a + 1) + i)).g^(pows ⟨((a + 1) + i), by omega⟩))).prod.val.val - 1‖ ≤ ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ / 10 := by


  grw [H_n_pow_le]
  grw [Finset.sum_le_sum (g := (fun i : Fin (k) => (c * (H_n_eps data.hd)⁻¹) * ‖(theorem_3_8_h_n data ((a + 1) + i)).g.val.val - 1‖))]
  · rw [← Finset.mul_sum]
    grw [Finset.sum_le_sum (g := (fun i : Fin (k) => ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ * 2^(1 + i.val) * (H_n_eps data.hd)^(1 + i.val)))]
    · have eps_nonneg := H_n_eps_pos data.hd
      simp
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      simp_rw [← mul_pow]
      simp_rw [add_comm]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
      rw [Finset.sum_fin_eq_sum_range]
      rw [Finset.sum_congr (s₁ := Finset.range k) (s₂ := Finset.range k) (g := fun i => (2 * H_n_eps data.hd) ^ i)]

      nth_rw 4 [mul_comm]
      rw [Finset.range_eq_Ico, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      grw [geom_sum_Ico_le_of_lt_one]
      have eps_ne_zero := H_n_eps_pos data.hd
      field_simp
      -- TODO - make this a lemma
      have two_mul_le : 2 * (H_n_eps data.hd) < (1 / 2) := by
        have foo := H_n_eps_lt data.hd
        linarith
      nth_grw 2 [two_mul_le]
      field_simp
      norm_num
      have eps_ne_zero : 0 ≠ (H_n_eps data.hd) := by
        have foo := H_n_eps_pos data.hd
        linarith


      ring_nf
      field_simp [eps_ne_zero]

      grw [c_lt]
      ring
      rfl
      · positivity
      · grw [H_n_eps_lt data.hd]
        norm_num
      · rfl
      · intro x hx
        simp at hx
        simp [hx]
    · simp [c_pos]
      have pos := H_n_eps_pos data.hd
      linarith
    -- H_n_upper_bound_iter
    · intro i hi
      rw [add_assoc]
      grw [H_n_upper_bound_iter data]
  · intro i hi
    grw [pows_le]
  · omega

#print axioms H_n_prod_le_k

#synth Semiring (Matrix (Fin 2) (Fin 2) ℂ)


lemma norm_sub_swap (n: ℕ) (a b: Matrix (Fin n) (Fin n) ℂ): ‖a - b‖ = ‖b - a‖ := by
  rw [← neg_sub]
  rw [norm_neg]




  --rw [my_sub] at my_pow



noncomputable def f (a: ℝ) (x: ℝ): ℝ := 1 + (2*x - 1)*a - (1 + a)^x

lemma f_one_eq_zero (a: ℝ): f a 1 = 0 := by
  simp [f]
  ring

lemma f_deriv (a: ℝ) (ha: 0 < 1 + a) (x: ℝ): (deriv (f a)) x = 2*a - (Real.log (1 + a))*(1 + a)^x := by
  unfold f
  simp_rw [← add_sub]
  rw [deriv_const_add]
  rw [← Pi.sub_def]
  rw [deriv_sub]
  · rw [deriv_mul_const]
    · rw [deriv_sub_const, deriv_const_mul]
      · simp
        have deriv_pow := (Real.hasStrictDerivAt_const_rpow (a := 1 + a) ha x).hasDerivAt.deriv
        simp [deriv_pow, mul_comm]
      · simp
    · simp
      apply DifferentiableAt.const_mul
      simp
  · apply DifferentiableAt.mul_const
    simp
    apply DifferentiableAt.const_mul
    simp
  · apply (Real.hasStrictDerivAt_const_rpow _ _).hasDerivAt.differentiableAt
    exact ha


lemma f_deriv_at_one (a: ℝ) (a_pos: 0 < a) (a_lt: a < 1) (ha: 0 < 1 + a): 0 < (deriv (f a) 1) := by
  rw [f_deriv _ ha]
  grw [Real.log_le_sub_one_of_pos]
  · have a_mul_self := mul_lt_of_lt_one_left (a := a) (b := a) (by linarith) (by linarith)
    have a_le_self: a + a ≤ 2 * a := by linarith
    have a_plus_lt : a + a^2 < a + a := by simp [pow_two, a_mul_self]
    simp only [add_sub_cancel_left, Real.rpow_one, sub_pos, gt_iff_lt]
    linarith
  simp [ha]


lemma f_deriv_lower (a: ℝ) (ha: 0 < 1 + a) (a_pos: 0 < a) (x: ℝ) (f_zero: (deriv (f a)) x = 0): (Real.log 2) / a ≤ x := by
  rw [f_deriv _ ha] at f_zero
  rw [sub_eq_zero] at f_zero
  nth_rw 2 [mul_comm] at f_zero
  apply div_eq_of_eq_mul at f_zero
  · apply_fun Real.log at f_zero
    rw [Real.log_rpow] at f_zero
    apply div_eq_of_eq_mul at f_zero
    rw [Real.log_div, Real.log_mul] at f_zero
    rw [← f_zero]

    have log_plus_le: Real.log (1 + a) ≤ a := by
      grw [Real.log_le_sub_one_of_pos]
      · simp
      · exact ha

    grw [log_plus_le]
    · simp
    · grw [log_plus_le]
      · simp
        apply Real.log_nonneg
        simp
      · apply Real.log_pos
        simp [a_pos]
    · apply Real.log_pos
      simp [a_pos]
    · apply Real.log_pos
      simp [a_pos]
    · simp
    · linarith
    · linarith
    · have pos: 0 < Real.log (1 + a) := by
        apply Real.log_pos
        simp [a_pos]
      linarith
    · have pos: 0 < Real.log (1 + a) := by
        apply Real.log_pos
        simp [a_pos]
      linarith
    · exact ha
  · have pos: 0 < Real.log (1 + a) := by
      apply Real.log_pos
      simp [a_pos]
    linarith

lemma f_pos_on (a: ℝ) (ha: 0 < 1 + a) (a_pos: 0 < a) (a_lt: a < 1)  (a_lt_log: a < Real.log 2): ∀ x ∈ Set.Ioc 1 (Real.log 2 / a), 0 < f a x := by

  have deriv_nonzero: ∀ x ∈ Set.Ico 1 (Real.log 2 / a), (deriv (f a)) x ≠  0 := by
    intro x hx
    by_contra!
    have x_eq := f_deriv_lower a ha a_pos x this
    have x_lt := hx.right
    linarith

  have one_lt : 1 < Real.log (2) / a := by
    rw [lt_div_iff₀]
    . simp
      exact a_lt_log
    . exact a_pos

  have f_strict := strictMonoOn_of_deriv_pos (f := f a) (D := Set.Icc 1 ((Real.log (2 )) / a)) (by apply convex_Icc) ?_ ?_
  .
    intro x hx
    have f_lt := f_strict.lt_iff_lt (a := 1) (b := x) ?_ ?_
    rw [f_one_eq_zero] at f_lt
    have x_prop := hx.left
    simp [x_prop] at f_lt
    . exact f_lt
    . simp
      linarith
    . simp
      simp at hx
      refine ⟨by linarith, hx.right⟩
  . apply Continuous.continuousOn
    unfold f
    have one_plus: 1 + a ≠ 0 := by linarith
    fun_prop (disch:=assumption)
  .

    intro x hx
    simp at hx

    have deriv_pos: 0 ≤ (deriv (f a)) x := by
      by_contra!
      have foo := ContinuousOn.surjOn_Icc (f := deriv (f a)) (a := x) (b := 1) (s := Set.Ico 1 ((Real.log 2) / a)) ?_ ?_ ?_

      have zero_mem: 0 ∈ (Set.Icc (deriv (f a) x) (deriv (f a) 1)) := by
        simp
        refine ⟨by linarith, ?_⟩
        have my_deriv := f_deriv_at_one a a_pos a_lt ha
        linarith


      unfold Set.SurjOn at foo
      have deriv_zero := foo zero_mem
      rw [Set.mem_image] at deriv_zero
      obtain ⟨y, y_mem, y_deriv⟩ := deriv_zero
      have y_nonzero := deriv_nonzero y y_mem
      . contradiction
      . apply Continuous.continuousOn
        unfold f
        have one_plus: ∀ x: ℝ, 1 + a ≠ 0 := by
          intro x
          linarith
        fun_prop (disch:=assumption)
      . simp
        refine ⟨by linarith, hx.right⟩
      . simp
        exact one_lt

    have not_zero := deriv_nonzero x ?_
    . exact lt_of_le_of_ne deriv_pos (id (Ne.symm not_zero))
    . simp
      refine ⟨by linarith, hx.right⟩

#print axioms f_pos_on



lemma H_n_single_pow_lower_bound {n : ℕ} {m : ℕ} (m_gt: 1 ≤ m) (data : HnData) (m_lt: m < (1/2) / ‖(theorem_3_8_h_n data n).g.val.val - 1‖) : ‖((theorem_3_8_h_n data n).g.val.val^m) - 1‖ ≥ ‖((theorem_3_8_h_n data n).g.val).val - 1‖ := by

  --rw [SubgroupClass.coe_zpow]
  push_cast
  -- TODO: figure out how to get 'SubgroupClass.coe_zpow' to fire for Matrix.unitaryGroup

  --have my_coe := unitary.coe_zpow (R := Matrix (Fin data.d) (Fin data.d) ℂ) (U := (theorem_3_8_h_n data n).val.val) (z := m)
  conv =>
    lhs
    arg 1
    lhs
    arg 1
    equals (1 + ((theorem_3_8_h_n data n).g.val.val - 1)) =>
      field_simp

  rw [norm_sub_swap]
  have m_eq: m = (m - 1) + 1 := by
    omega

  rw[add_comm]
  rw [Commute.add_pow (by simp)]
  rw[Finset.sum_range_succ']
  conv =>
    lhs
    arg 1
    rhs
    simp

  nth_rw 1 [m_eq]
  rw [Finset.sum_range_succ']
  simp
  rw [← ge_iff_le]
  rw [← sub_eq_add_neg]
  grw [(norm_sub_norm_le _ _).ge]
  rw [norm_neg]
  --grw [norm_sum_le]



  have nonempty_d: Nonempty (Fin data.d) := by
    have data_pos := data.hd
    exact Fin.pos_iff_nonempty.mp (by linarith)

  have my_pow := Commute.add_pow (y := 1) (x := ‖((theorem_3_8_h_n data n).g.val.val - 1)‖) (n := m - 1 + 1) (by simp)
  rw [Finset.sum_range_succ'] at my_pow
  simp at my_pow
  rw [Finset.sum_range_succ'] at my_pow
  simp at my_pow
  rw [← m_eq] at my_pow
  rw [add_assoc] at my_pow
  apply sub_eq_of_eq_add at my_pow
  norm_cast at my_pow
  rw [← m_eq] at my_pow
  -- conv at my_pow =>
  --   rhs
  --   arg 2
  --   intro x
  --   rw [← norm_pow]
  -- simp_rw [norm_pow] at my_pow
  grw [norm_sum_le]

  grw [Finset.sum_le_sum (g := fun i => ‖((theorem_3_8_h_n data n).g.val.val - 1)‖ ^ (i + 1 + 1) * (m.choose (i + 1 + 1)))]
  .
    rw [← my_pow]

    have S_le : (1 + ‖((theorem_3_8_h_n data n).g).val.val - 1‖)^m - ((‖(theorem_3_8_h_n data n).g.val.val - 1‖) * (m : ℝ) + 1) ≤ (m - 1) * ‖(theorem_3_8_h_n data n).g.val.val - 1‖ := by
      by_cases m_eq_one: m = 1
      .
        simp [m_eq_one]
        rw [add_comm]
      .
        simp at m_eq_one
        have my_bound := f_pos_on ‖((theorem_3_8_h_n data n).g.val.val - 1)‖  ?_ ?_ ?_ ?_ m ?_
        simp [f] at my_bound
        rw [two_mul] at my_bound
        rw [← add_sub] at my_bound
        rw [add_mul] at my_bound
        rw [← add_assoc] at my_bound
        apply sub_left_lt_of_lt_add at my_bound
        rw [← gt_iff_lt] at my_bound
        rw [← ge_iff_le]
        grw [my_bound]
        simp
        ring_nf
        . rfl
        . positivity
        .
          have val_ne := (theorem_3_8_h_n data n).g_dist_nonzero
          positivity
        .
          have val_le := (theorem_3_8_h_n data n).g_dist
          grw [val_le]
          grw [H_n_eps_lt]
          norm_num
        .
          have val_le := (theorem_3_8_h_n data n).g_dist
          grw [val_le]
          grw [H_n_eps_lt]
          norm_num
          rw [← gt_iff_lt]
          grw [Real.log_two_gt_d9.gt]
          norm_num
        . simp
          refine ⟨by omega, ?_⟩
          grw [← ge_iff_le]
          grw [Real.log_two_gt_d9.gt]
          simp
          grw [m_lt]
          simp
          apply div_le_div₀
          . norm_num
          . norm_num
          . have ne_zero := (theorem_3_8_h_n data n).g_dist_nonzero
            positivity
          . rfl


    rw [add_comm]
    grw [S_le]
    nth_rw 2 [sub_mul]
    rw [mul_comm]
    rw [← mul_comm]
    simp
    have my_smul := norm_smul (m : ℂ) ((theorem_3_8_h_n data n).g.val.val - 1)
    simp at my_smul
    rw [← my_smul]
    conv =>
      rhs
      rhs
      lhs
      arg 1
      equals ((theorem_3_8_h_n data n).g.val.val - 1) * m =>
        rw [Matrix.smul_eq_mul_diagonal]
        rw [← Matrix.diagonal_natCast]

    ring_nf
    rfl

  . intro i hi
    grw [norm_mul_le]
    grw [norm_pow_le]
    --rw [← Matrix.diagonal_natCast']
    -- TODO - separate this into a lemma about Matrix.l2_opNorm for a diagonal matrix
    nth_rw 2 [Matrix.l2_opNorm_def]
    grw [ContinuousLinearMap.opNorm_le_bound (M := m.choose (i + 1 + 1))]
    . simp
    .
      intro x
      simp
      rw [Matrix.toEuclideanLin_apply]
      simp
      rw [norm_smul]
      simp

  --apply_fun Norm.norm at my_pow

#synth DivisionMonoid (Matrix.unitaryGroup (Fin 2) ℂ)

-- --@[norm_cast]
-- theorem new_coe_inv {R: Type*} [DivInvMonoid R] [StarMul R] (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) := by
--   eq_inv_of_mul_eq_one_right <| unitary.coe_mul_star_self _

-- @[norm_cast]
-- theorem new_coe_zpow {R: Type*} [DivInvMonoid R] [StarMul R] (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U : R) ^ z := by
--   cases z
--   · simp [SubmonoidClass.coe_pow]
--   · simp [new_coe_inv]

#synth DivInvMonoid (Matrix (Fin 2) (Fin 2) ℂ)

  -- have my_bound := f_pos_on ‖((theorem_3_8_h_n data n).val.val.val - 1)‖ ?_ ?_ ?_ ?_
  -- simp [f] at my_bound

-- TODO: upstream to mathlib
lemma list_ofFn_drop {M: Type*} (a k: ℕ) (f: Fin (k + a) → M): (List.ofFn f).drop a = List.ofFn (fun (i: Fin k) => f ⟨a + i, by omega⟩) := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    rw [List.ofFn_congr (n := (k + a) + 1) (by linarith)]
    simp
    have list_eq := ih (fun i => f i.succ)
    rw [list_eq]
    simp
    funext b
    group

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
lemma words_distinct {m : ℕ} (k: Fin m) (c : ℝ) (c_pos : 0 < c) (c_lt : c < 1 / 40)
 (data : HnData)
 (pows_i : Fin m → ℕ)
 (pows_j: Fin m → ℕ)
 (pows_i_le : ∀ i : Fin m, (pows_i i) ≤ c * (H_n_eps data.hd)⁻¹)
 (pows_j_le : ∀ i : Fin m, (pows_j i) ≤ c * (H_n_eps data.hd)⁻¹)
 (pows_lt_eq: ∀ j : Fin m, j < k → pows_i j = pows_j j)
 (pows_j_lt_k: (pows_j k) < (pows_i k)):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^(pows_i i))).prod ≠ (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^(pows_j i))).prod := by

  --have find := Fin.isSome_find_iff.mpr pows_ne
  --let k := (Fin.find (fun i => pows_i i ≠ pows_j i)).get find

  by_contra!

  nth_rw 2 [← List.prod_take_mul_prod_drop (i := k)] at this
  rw [← List.prod_take_mul_prod_drop (i := k)] at this
  -- TODO - generalize this and PR to mathlib
  conv at this =>
    lhs
    lhs
    arg 1
    equals List.take k (List.ofFn fun (i: Fin k) ↦ ((theorem_3_8_h_n data i).g ^ pows_i ⟨i, by omega⟩)) =>
      --clear a_k_lt pows_i_le pows_j_le pows_ne this
      ext i l
      rw [List.getElem?_take]
      rw [List.getElem?_take]
      simp
      by_cases i_lt_k: i < k
      .
        simp [i_lt_k]
        have i_lt_m: i < m := by omega
        simp [i_lt_m]
      . simp [i_lt_k]

  conv at this =>
    rhs
    lhs
    arg 1
    equals List.take k (List.ofFn fun (i: Fin k) ↦ ((theorem_3_8_h_n data i).g ^ pows_j ⟨i, by omega⟩)) =>
      --clear a_k_lt pows_i_le pows_j_le pows_ne this
      ext i l
      rw [List.getElem?_take]
      rw [List.getElem?_take]
      simp
      by_cases i_lt_k: i < k
      .
        simp [i_lt_k]
        have i_lt_m: i < m := by omega
        simp [i_lt_m]
      . simp [i_lt_k]


  conv at this =>
    lhs
    lhs
    arg 1
    arg 2
    arg 1
    intro i
    rw [pows_lt_eq _ (by
      have i_prop := i.is_lt
      exact i_prop
    )]


  -- have tail_eq: (List.drop (↑k) (List.ofFn fun i ↦ (theorem_3_8_h_n data ↑i).val ^ pows_i i)).prod = (List.drop (↑k) (List.ofFn fun i ↦ (theorem_3_8_h_n data ↑i).val ^ pows_j i)).prod := by
  --   nth_rw 2 [List.ofFn_congr (n := m - k + k) (by
  --     omega
  --   )]
  --   rw [List.ofFn_congr (n := m - k + k) (by
  --     omega
  --   )]
  --   rw [list_ofFn_drop]
  --   rw [list_ofFn_drop]
  --   apply congr (rfl)
  --   ext i g
  --   by_cases i_lt_m: i < (m - k)
  --   .
  --     simp [i_lt_m]
  --     rw [pows_lt_eq]
  --     rw [Fin.lt_iff_val_lt_val]
  --   simp
  --   conv =>
  --     lhs
  --     rhs
  --     intro h
  --     rw [pows_lt_eq _ (by simp)]
  --   rw [pows_lt_eq]


  --   sorry

  --simp at cancel_lhs


  rw [mul_right_inj] at this
  nth_rw 2 [List.ofFn_congr (n := m - k + k) (by
    omega
  )] at this
  rw [List.ofFn_congr (n := m - k + k) (by
    omega
  )] at this
  rw [list_ofFn_drop] at this
  rw [list_ofFn_drop] at this
  nth_rw 2 [List.ofFn_congr (n := m - k - 1 + 1) (by
    omega
  )] at this
  rw [List.ofFn_congr (n := m - k - 1 + 1) (by
    omega
  )] at this
  rw [List.ofFn_succ] at this
  rw [List.prod_cons] at this
  rw [List.ofFn_succ] at this
  rw [List.prod_cons] at this
  apply inv_mul_eq_of_eq_mul at this
  rw [← mul_assoc] at this
  simp at this
  rw [← zpow_natCast] at this
  rw [← zpow_natCast] at this
  rw [← zpow_neg] at this
  rw [← zpow_add] at this


  ring_nf at this
  have rhs_le := H_n_prod_le_k (c := c) (m := m) (k := (m - k - 1)) (a := k) (by omega) c_pos c_lt pows_j data pows_j_le
  ring_nf at rhs_le
  rw [← this] at rhs_le


    --rw [list_ofFn_drop]

  -- Fin (5)
  -- Fin (5 + 0)
  -- Fin (0 + 5)

  have lhs_ge: ‖((theorem_3_8_h_n data (k)).g ^ (-(pows_j ⟨k, by omega⟩ : ℤ) + (pows_i ⟨k, by omega⟩))).val.val * (List.ofFn fun (i: Fin (m - k - 1)) ↦ (theorem_3_8_h_n data (1 + i + k)).g ^ pows_i ⟨1 + i + k, by omega⟩).prod.val.val - 1‖ ≥ (9 / 10) * ‖(theorem_3_8_h_n data k).g.val.val - 1‖ := by
    have m_minus_k: m - k - 1 + 1 = m - k := by
      omega
    -- conv =>
    --   lhs
    --   arg 1
    --   lhs
    --   rhs
    --   arg 1
    --   arg 1
    --   arg 1
    --   rw [List.ofFn_congr (n := (m - k - 1 - 1) + 1) (by
    --     omega
    --   )]

    -- rw [List.ofFn_succ]
    -- rw [List.prod_cons]
    -- norm_cast
    -- rw [← mul_assoc]
    -- norm_cast
    -- rw [← zpow_natCast]
    -- conv =>
    --   lhs
    --   arg 1
    --   lhs
    --   arg 1
    --   arg 1
    --   lhs
    --   rhs
    --   simp

    --rw [← zpow_natCast]
    conv =>
      lhs
      arg 1
      equals ((((theorem_3_8_h_n data ↑k).g ^ (-(pows_j k : ℤ) + ↑(pows_i k)))).val.val - 1) * (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (1 + i + k)).g^(pows_i (⟨1 + i + k, by omega⟩) ))).prod + (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (1 + i + k)).g^(pows_i (⟨1 + i + k, by omega⟩) ))).prod - 1 =>
        rw [sub_mul]
        simp


    have pows_nat: (-((pows_j k) : ℤ) + (pows_i k)) = (((-(pows_j k) : ℤ) + (pows_i k))).toNat := by
      simp
      linarith


    rw [← add_sub]
    grw [(norm_sub_le_norm_add _ _).ge]
    rw [CStarRing.norm_mul_mem_unitary]
    rw [pows_nat]
    rw [zpow_natCast]
    rw [SubmonoidClass.coe_pow]
    rw [SubmonoidClass.coe_pow]
    grw [H_n_single_pow_lower_bound]

    -- TODO : figure out why we can't use 'simp_rw' here
    conv =>
      lhs
      rhs
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      intro i
      simp only [add_comm]
      arg 1
      arg 1
      arg 2
      equals (k.val + 1) + i =>
        group

    conv =>
      lhs
      rhs
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      intro i
      arg 2
      arg 1
      arg 1
      equals (k.val + 1) + i =>
        group

    grw [H_n_prod_le_k (c := c)]
    . linarith
    .
      rw [add_assoc]
      rw [m_minus_k]
      simp
    . exact c_pos
    . exact c_lt
    . exact pows_i_le
    .
      linarith
    .
      conv =>
        lhs
        equals (-((pows_j k) : ℝ) + ((pows_i k) : ℝ)) =>
          rw [add_comm]
          rw [← sub_eq_add_neg]
          rw [add_comm]
          rw [← sub_eq_add_neg]
          simp
          rw [Nat.cast_sub (by linarith)]

      rw [add_comm]
      rw [← sub_eq_add_neg]
      have pow_j_ge: 0 ≤ (pows_j k : ℝ) := by
        have pows_j_pos := pows_j_le k
        positivity
      grw [pows_i_le]
      grw [pow_j_ge.ge]
      simp
      grw [c_lt]
      apply mul_lt_mul
      . norm_num
      .
        rw [inv_le_inv₀]
        .
          have my_prop := (theorem_3_8_h_n data k).g_dist
          exact my_prop
        . apply H_n_eps_pos
        . have my_prop := (theorem_3_8_h_n data k).g_dist_nonzero
          positivity
      . simp
        apply H_n_eps_pos
      . norm_num
      . simp
        have foo := H_n_eps_pos data.hd
        linarith
    . simp [-SubmonoidClass.coe_list_prod]

--#synth GroupWithZero (Matrix (Fin 2) (Fin 2) ℂ)

  -- have lhs_le: ‖((theorem_3_8_h_n data (k)).val ^ (-(pows_j ⟨k, by omega⟩ : ℤ))).val.val * (List.ofFn fun (i: Fin (m - k)) ↦ (theorem_3_8_h_n data (i + k)).val ^ pows_i ⟨i + k, by omega⟩).prod.val.val - 1‖ ≤ (1 / 10) * ‖(theorem_3_8_h_n data k).val.val.val - 1‖ := by

  --   let foo := (theorem_3_8_h_n data (k)).val.val.val ^ ((-1: ℤ))
  --   have m_minus_pos: 0 < m - k := by
  --     omega
  --   have m_minus_k: m - k - 1 + 1 = m - k := by
  --     omega
  --   rw [List.ofFn_congr (n := (m - k - 1) + 1) (by
  --     rw [m_minus_k]
  --   )]
  --   rw [List.ofFn_succ]
  --   simp [-zpow_neg, -Subgroup.val_list_prod, -SubmonoidClass.coe_list_prod]
  --   rw [← mul_assoc]
  --   norm_cast
  --   rw [← zpow_natCast]
  --   rw [← zpow_add]
  --   rw [← List.prod_cons]

  --   let combined_pows (i: Fin (m - k + 1)) := if (i.val - 1) = 0 then ((-(pows_j k : ℤ) + (pows_i k))) else pows_i (⟨i - 1 + k, by omega⟩)

  --   conv =>
  --     lhs
  --     arg 1
  --     lhs
  --     arg 1
  --     arg 1
  --     arg 1
  --     equals List.ofFn (fun (i: Fin (m - k)) => (theorem_3_8_h_n data (i + k)).val^(combined_pows (⟨i + 1, by omega⟩))) =>
  --       ext i l
  --       simp [combined_pows]
  --       by_cases i_eq_zero: i = 0
  --       .
  --         simp [i_eq_zero]
  --       .
  --         rw [List.getElem?_cons]
  --         simp [i_eq_zero]
  --         by_cases i_lt: i < m - k
  --         .
  --           have i_minus_lt: i - 1 < m - k - 1 := by omega
  --           have i_minus_plus: i - 1 + 1 = i := by omega
  --           simp [i_lt, i_minus_lt, i_minus_plus]
  --         .
  --           simp [i_lt]
  --           simp at i_lt
  --           have not_lt: ¬(i - 1 < m - k - 1) := by omega
  --           simp [not_lt]



  --   grw [H_n_prod_le_k]





  rw [ge_iff_le] at lhs_ge

  have one_tenth_lt:  1 / 10 * ‖(theorem_3_8_h_n data ↑k).g.val.val - 1‖ < (9 / 10) * ‖(theorem_3_8_h_n data ↑k).g.val.val - 1‖ := by
    apply mul_lt_mul
    . norm_num
    . simp
    .
      have ne_zero := (theorem_3_8_h_n data ↑k).g_dist_nonzero
      positivity
    . norm_num




  have add_swap (a b : ℕ): 1 + a + b = 1 + b + a := by
    omega

  have add_swap_pows_i (a b: ℕ) (add_lt: 1 + a + b < m): pows_i ⟨1 + a + b, by omega⟩ = pows_i ⟨1 + b + a, by omega⟩ := by
    simp_rw [add_swap]


  grw [lhs_ge] at one_tenth_lt
  ring_nf at one_tenth_lt
  conv at rhs_le =>
    lhs
    arg 1
    lhs
    rhs
    rhs
    rhs
    arg 1
    arg 1
    intro i
    rw [add_swap_pows_i]
    lhs
    rw [add_swap]


  norm_cast at rhs_le
  norm_cast at one_tenth_lt
  --have new_le := lt_of_lt_of_le one_tenth_lt rhs_le
  grw [rhs_le] at one_tenth_lt
  simp at one_tenth_lt
  --linarith

  -- have m_minus_k: m - k - 1 + 1 = m - k := by sorry
  -- conv at offset_eq =>
  --   rhs
  --   arg 1
  --   lhs
  --   rhs
  --   arg 1
  --   arg 1
  --   arg 1
  --   rw [List.ofFn_congr (n := (m - k - 1) + 1) (by
  --     rw [m_minus_k]
  --   )]

  -- rw [List.ofFn_succ] at offset_eq
  -- rw [List.prod_cons] at offset_eq
  -- norm_cast at offset_eq
  -- rw [← mul_assoc] at offset_eq
  -- conv at offset_eq =>
  --   rhs
  --   arg 1
  --   arg 1
  --   arg 1
  --   arg 1
  --   arg 1
  --   norm_cast
  --   arg 2
  --   simp



  -- rw [← zpow_natCast] at offset_eq
  -- rw [← zpow_add] at offset_eq
  -- rw [add_comm] at offset_eq
  -- rw [← sub_eq_add_neg] at offset_eq
  -- rw [sub_self] at offset_eq
  -- rw [zpow_zero] at offset_eq

  -- conv at offset_eq =>
  --   lhs
  --   rw [List.ofFn_congr (n := (m - k - 1) + 1) (by
  --     rw [m_minus_k]
  --   )]
  -- rw [List.ofFn_succ] at offset_eq
  -- rw [List.prod_cons] at offset_eq
  -- rw [← mul_assoc] at offset_eq
  -- conv at offset_eq =>
  --   lhs
  --   arg 1
  --   lhs
  --   arg 1
  --   arg 1
  --   arg 1
  --   simp
  --   rw [← zpow_neg_one]
  --   rw [← zpow_natCast]
  --   rw [← zpow_mul]
  --   rw [← zpow_natCast]
  --   rw [← zpow_add]
  --   simp

  -- conv at offset_eq =>
  --   lhs
  --   arg 1
  --   equals ((((theorem_3_8_h_n data ↑k).val ^ (-(pows_j k : ℤ) + ↑(pows_i k)))).val.val - 1) * (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (i.succ + k)).val^(pows_i (⟨i.succ + k, by omega⟩) ))).prod + (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (i.succ + k)).val^(pows_i (⟨i.succ + k, by omega⟩) ))).prod - 1  =>
  --     rw [sub_mul]
  --     simp



  -- rw [← List.prod_cons] at offset_eq
  -- rw [← List.ofFn_succ] at offset_eq





  --   -- List.ofFn_succ








  -- sorry

#print axioms words_distinct

-- ContinuousLinearMap.norm_id


lemma matrix_l2_norm_one {d: ℕ} (hd: 0 < d): ‖(1: Matrix (Fin d) (Fin d) ℂ)‖ = 1 := by
  rw [Matrix.l2_opNorm_def]
  have nonempty_fin: Nonempty (Fin d) := by
    refine Fin.pos_iff_nonempty.mp hd
  apply ContinuousLinearMap.opNorm_eq_of_bounds (by simp)
  .
    intro x
    simp
    rw [Matrix.toEuclideanLin_apply]
    simp
  . intro N hN mat_le
    simp at mat_le
    simp [Matrix.toEuclideanLin_apply] at mat_le
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


instance matrix_norm_one_class (n: ℕ) (hd: Nonempty (Fin n)) : NormOneClass (Matrix (Fin n) (Fin n) ℂ) where
  norm_one := matrix_l2_norm_one (by exact Fin.pos')

def H_n_C: ℝ := 8

lemma list_prod_pow {T: Type*} [Group T] (m: ℕ) (elems: Fin m → T) (pows: Fin m → ℕ):
  (List.ofFn (fun (i: Fin m) => (elems i)^(pows i))).prod = (List.ofFn (fun (i : Fin m) => List.replicate (pows i) (elems i))).flatten.prod := by

  induction m with
  | zero =>
    simp
  | succ m ih =>
    have prod_eq := ih (Fin.init elems) (Fin.init pows)
    rw [List.ofFn_succ']
    rw [List.ofFn_succ']
    simp
    simpa using prod_eq

lemma list_prod_pow_new {T: Type*} [Group T] (m: ℕ) (elems: Fin m → T) (pows: Fin m → ℕ):
  (List.ofFn (fun (i: Fin m) => (elems i)^(pows i))).prod = (List.ofFn (fun (i : Fin m) => List.replicate (pows i) (elems i))).flatten.prod := by

  induction m with
  | zero =>
    simp
  | succ m ih =>
    have prod_eq := ih (Fin.init elems) (Fin.init pows)
    rw [List.ofFn_succ']
    rw [List.ofFn_succ']
    simp
    simpa using prod_eq




-- This lemma is in terms of elements of G - we use this to build up our statement in terms of elements of the finite generate set S
lemma H_n_pows_mem_ball_G {m : ℕ}
  (m_gt: 0 < m) (data : HnData) (pows : Fin m → ℕ)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (pows_le : ∀ i : Fin m, (pows i) ≤ ⌊c * (H_n_eps data.hd)⁻¹⌋₊):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod.val ∈ (data.G.carrier ^ (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹)))) := by

  let replicate_pow (i: Fin m) := List.replicate (pows i) ((theorem_3_8_h_n data i).g)
  let nested_list := List.ofFn (fun (i : Fin (m)) => replicate_pow i)
  let nested_prod := List.prod_flatten (l := nested_list)
  conv at nested_prod =>
    rhs
    equals (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod =>
      simp [nested_list, replicate_pow]
      apply congr (rfl)
      ext i g
      simp



  --rw [← nested_prod]
  rw [Set.mem_pow]
  -- We have an upper bound for the list, so pad out the list with '1's to reach the upper bound
  let base_list := (fun (i: Fin (nested_list.flatten.length)) => nested_list.flatten[i])
  let full_list := Fin.append base_list (fun (i: Fin (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) - nested_list.flatten.length)) => 1)
  --let full_list_new := nested_list.flatten ++ (List.replicate (2 * (Nat.floor (c * ε⁻¹)) * (2 ^ m) - nested_list.flatten.length) 1)

  have len_le_upper: nested_list.flatten.length ≤ (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹))) := by
    simp [nested_list, replicate_pow]
    simp [Fin.sum_ofFn]
    grw [Finset.sum_le_card_nsmul (n := ⌊ (c * (H_n_eps data.hd)⁻¹)⌋₊)]
    . simp
    . intro x _
      apply pows_le



  use (fun i => full_list (i.cast (by omega)))
  .


    conv =>
      lhs
      equals (List.ofFn (fun (i: Fin ((m * (Nat.floor (c * (H_n_eps data.hd)⁻¹))))) => (full_list (i.cast (by omega))))).prod.val =>
        simp
        apply congr (rfl)
        ext i g
        simp



    simp only [full_list, base_list]
    rw [← List.ofFn_congr]
    rw [List.ofFn_fin_append]
    rw [list_prod_pow]
    conv =>
      lhs
      arg 1
      arg 1
      lhs
      equals nested_list.flatten =>
        ext i g
        simp
        grind

    dsimp [nested_list, replicate_pow]
    rw [List.prod_append]
    . simp [-List.prod_flatten]
    . omega


#print axioms H_n_pows_mem_ball_G

-- Unfold the commutators from theorem_3_8_h_n as a list of elements
noncomputable def theorem_3_8_h_n_list (data: HnData) (m: ℕ): List (data.S) :=
  match m with
  | 0 => [data.h]
  | a + 1 => [(theorem_3_8_h_n_left_S data (theorem_3_8_h_n data a)).choose]
              ++ theorem_3_8_h_n_list data a
              ++ [⟨(theorem_3_8_h_n_left_S data (theorem_3_8_h_n data a)).choose.val⁻¹, (by
                apply data.S_inv
                simp
              )⟩]
              ++ (List.map (fun s => ⟨s.val⁻¹, by apply data.S_inv; simp⟩) (theorem_3_8_h_n_list data a)).reverse


set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
lemma theorem_3_8_h_n_list_prod_eq (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data m).unattach.prod = (theorem_3_8_h_n data m).g := by
  induction m with
  | zero =>
    unfold theorem_3_8_h_n_list
    simp [theorem_3_8_h_n]
  | succ a ih =>
    unfold theorem_3_8_h_n_list
    simp [theorem_3_8_h_n]
    simp [Bracket.bracket]
    rw [ih]
    conv =>
      lhs
      rhs
      rhs
      rhs
      arg 1
      arg 1
      equals List.map Inv.inv (theorem_3_8_h_n_list data a).unattach =>
        ext i g
        simp


    rw [← List.prod_inv_reverse]
    rw [ih]
    group

-- Note - this is (2^(m - 1)) in Vikman, since the list in indexed starting at 1 in the paper
lemma theorem_3_8_h_n_list_length_initial_upper_bound  (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data (m)).length ≤ (3 * (2 ^ (m))) - 2 := by
  induction m with
  | zero =>
    unfold theorem_3_8_h_n_list
    simp
  | succ a ih =>
    unfold theorem_3_8_h_n_list
    -- TODO - can grind somehow solve all of this?
    simp
    grw [ih]
    ring
    rw [Nat.sub_mul]
    ring
    zify
    rw [Nat.cast_sub]
    .
      push_cast
      ring
      rw [Nat.cast_sub]
      . push_cast
        ring
        rfl
      .
        by_cases a_eq_zero: a = 0
        .
          simp [a_eq_zero]
        .
          have a_eq_sub_succ: a = (a - 1) + 1 := by omega
          rw [a_eq_sub_succ]
          rw [Nat.pow_succ]
          rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          apply Nat.le_mul_of_pos_right
          positivity
    .
      rw [← ge_iff_le]
      grw [(Nat.one_le_pow _ _ ?_).ge]
      . norm_num
      . norm_num



-- The c' constant from Vikman
def c' := 3

-- TODO - figure out how to merge this with 'theorem_3_8_h_n_list_length_initial_upper_bound'
lemma theorem_3_8_h_n_list_length_upper_bound  (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data (m)).length ≤ c' * (2 ^ m) := by
  grw [theorem_3_8_h_n_list_length_initial_upper_bound data m]
  simp [c']


lemma list_concat_unattach {T: Type*} {p: T → Prop} (l: List { x: T // p x}) (a: { x: T // p x}): (l.concat a).unattach = l.unattach.concat a.val := by
  simp


lemma H_n_pows_mem_ball_S {m : ℕ}
  (m_gt: 0 < m) (data : HnData) (pows : Fin m → ℕ)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (pows_le : ∀ i : Fin m, (pows i) ≤ ⌊c * (H_n_eps data.hd)⁻¹⌋₊):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod.val ∈ Subtype.val '' (data.S ^ ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m))) := by

  rw [Set.mem_image]
  simp_rw [Set.mem_pow]
  use (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod


  -- A list with the same product as g_list, but expressed in terms of elements of S
  let g_as_s_list := (List.ofFn (fun (i: Fin m) => List.replicate (pows i) (theorem_3_8_h_n_list data i))).flatten.flatten



  have g_as_list_prod_eq_pow: g_as_s_list.unattach.prod = (List.ofFn (fun (i: Fin m) => (List.replicate (pows i) (theorem_3_8_h_n_list data i)).flatten.unattach.prod)).unattach.prod := by
    dsimp [g_as_s_list]
    clear m_gt
    induction m with
    | zero =>
      simp
    | succ m ih =>
      have prev_prod := ih (Fin.init pows) (by
        intro i
        apply pows_le
      )
      nth_rw 2 [List.ofFn_succ']
      simp only [Fin.init] at prev_prod
      conv =>
        rhs
        pattern List.ofFn _
        arg 1
        intro i
        simp


      rw [List.ofFn_succ']
      conv at prev_prod =>
        rhs
        pattern List.ofFn _
        arg 1
        intro i
        simp


      rw [list_concat_unattach]
      rw [List.prod_concat]
      rw [← prev_prod]
      simp


  have g_list_mem := H_n_pows_mem_ball_G m_gt data pows c c_pos c_lt pows_le
  rw [Set.mem_pow] at g_list_mem
  obtain ⟨g_list, g_list_prod⟩ := g_list_mem


  have lists_prod_eq: g_as_s_list.unattach.prod = (List.ofFn g_list).unattach.prod := by
    rw [g_as_list_prod_eq_pow]
    conv =>
      rhs
      unfold List.unattach
    simp only [List.map_ofFn]
    rw [Function.comp_def]
    rw [g_list_prod]
    simp
    simp_rw [theorem_3_8_h_n_list_prod_eq]
    unfold List.unattach
    simp [Function.comp_def]


  have g_as_s_list_len: g_as_s_list.length ≤ c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m) := by
    simp [g_as_s_list]
    rw [List.sum_ofFn]
    simp
    grw [Finset.sum_le_sum (g := fun i => (pows i) * c' * (2 ^ m))]
    .
      grw [Finset.sum_le_card_nsmul (n := ⌊c * (H_n_eps data.hd)⁻¹⌋₊ * c' * (2^m))]
      .
        simp
        ring
        rfl
      .
        intro i _
        grw [pows_le]
    . intro i _
      grw [theorem_3_8_h_n_list_length_upper_bound]
      ring
      grw [i.isLt]
      simp


  let padded_list := Fin.append (fun (i: Fin (g_as_s_list.length)) => g_as_s_list[i]) (fun (i: Fin (((c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m)) - g_as_s_list.length))) => ⟨1, data.S_one⟩)



  refine ⟨?_, rfl⟩
  .
    --use g_list
    use (fun i => padded_list (i.cast (by omega)))
    conv =>
      lhs
      equals (List.ofFn (fun i => padded_list i)).unattach.prod =>
        simp
        apply congr (rfl)
        ext i g
        nth_rw 2 [List.ofFn_congr (n := (c' * ⌊c * (H_n_eps data.hd)⁻¹⌋₊ * m * 2 ^ m))]
        . simp
        . omega


    rw [List.ofFn_fin_append]
    simp
    rw [Subtype.ext_iff]
    rw [lists_prod_eq]
    conv at g_list_prod =>
      lhs
      equals (List.ofFn g_list).unattach.prod =>
        apply congr rfl
        ext i g
        simp
    rw [g_list_prod]

#print axioms H_n_pows_mem_ball_S


-- In Vikman, this is (1 + ⌊c * (H_n_eps data.hd)⁻¹⌋₊) (since the powers include the upper bound of c*ε ⁻¹)
-- However, the proof works fine with the weaker lower bound ⌊c * (H_n_eps data.hd)⁻¹⌋₊
-- so I'm using that instead (since it avoids the need to deal with different Fin values)
lemma H_n_ball_S_card {m : ℕ}
  (m_gt: 0 < m) (data : HnData)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40):
  (⌊c * (H_n_eps data.hd)⁻¹⌋₊)^m ≤  #(data.S_finite.toFinset ^ ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m))) := by



  let my_set: Finset (Fin m → Fin (⌊c * (H_n_eps data.hd)⁻¹⌋₊)) := Finset.univ
  have my_card := Finset.card_univ (α := (Fin m → Fin (⌊c * (H_n_eps data.hd)⁻¹⌋₊)))
  rw [Fintype.card_pi_const] at my_card
  conv at my_card =>
    rhs
    simp


  rw [← my_card]
  apply Finset.card_le_card_of_injOn (f := fun pows => (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^((pows i).val))).prod)
  .
    intro pows _
    simp
    -- TODO - modify H_n_pows_mem_ball_S so that this can just be 'apply'
    have my_pows := H_n_pows_mem_ball_S m_gt data (fun i => (pows i).val) c c_pos c_lt ?_
    .
      rw [Set.mem_image] at my_pows
      obtain ⟨g, g_mem, g_eq⟩ := my_pows
      rw [← Subtype.ext_iff] at g_eq
      rw [← g_eq]
      exact g_mem
    . intro i
      simp
  .
    intro pows_i _ pows_j _
    contrapose
    intro pows_neq
    rw [funext_iff] at pows_neq
    simp at pows_neq

    have exists_minimal_k := exists_minimal_of_wellFoundedLT (fun (i: Fin m) => pows_i i ≠ pows_j i) pows_neq
    obtain ⟨k, k_minimal⟩ := exists_minimal_k
    -- TODO - figure out why this pushes a goal of 'False' if we don't use 'generalizing'
    wlog pow_j_lt_i: (pows_j k).val < (pows_i k).val generalizing pows_i pows_j

    .
      conv at k_minimal =>
        arg 1
        intro i
        rw [ne_comm]


      have words_neq := this (pows_j := pows_i) (pows_i := pows_j) (by simp) (by simp) ?_ k_minimal ?_
      .
        rw [eq_comm]
        exact words_neq
      .
        obtain ⟨x, hx⟩ := pows_neq
        use x
        exact fun a ↦ hx (id (Eq.symm a))
      .
        have k_neq := k_minimal.prop
        omega
    .
      simp at k_minimal

      have eps_pos := H_n_eps_pos data.hd

      have prods_neq := words_distinct (m := m) k c c_pos c_lt data (fun i => pows_i i) (fun i => pows_j i) ?_ ?_ ?_ ?_
      . simpa using prods_neq
      .
        intro i
        simp
        rw [← Nat.le_floor_iff]
        omega
        positivity
      . intro i
        simp
        rw [← Nat.le_floor_iff]
        omega
        positivity
      .
        intro j hk
        simp
        have foo := Minimal.not_prop_of_lt k_minimal hk
        simp at foo
        exact congrArg Fin.val foo
      .
        simpa using pow_j_lt_i


#print axioms H_n_ball_S_card

abbrev swap_le {a b: ℝ} (_: a ≤ b): Prop := b < a

-- Our lower bound gives us a contradiction with polynomial growth
lemma H_n_contradiction (data : HnData)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (c_mul_pos: 1 ≤ c * (H_n_eps data.hd)⁻¹)
  (eps_div_lt: (H_n_eps data.hd) < c / (Real.exp (4 + ↑data.S_poly_deg * Real.log 2) + 1))
  : False := by



  let m: ℕ := max (max (⌈1 + |(↑data.S_poly_deg - Real.log ↑data.S_poly_const)|⌉₊) (1 + ⌈((Real.log ↑data.S_poly_const + ↑data.S_poly_deg * Real.log (↑c' * ↑⌊c * (H_n_eps data.hd)⁻¹⌋₊)) /
    (Real.log ↑⌊c * (H_n_eps data.hd)⁻¹⌋₊ - ↑data.S_poly_deg * Real.log 2 - 4))⌉₊)) (1 + ⌈Real.exp ↑data.S_poly_deg⌉₊)

  have m_gt: 0 < m := by
    simp [m]
  have ne_zero_of_pos (r: ℝ): 0 < r → r ≠ 0 := by
    intro r_pos r_eq
    rw [r_eq] at r_pos
    linarith

  have upper_bound := data.S_poly ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m))
  have lower_bound := H_n_ball_S_card m_gt data c c_pos c_lt
  have ineq := le_trans lower_bound upper_bound
  rify at ineq
  rw [← Real.log_le_log_iff] at ineq
  .
    simp at ineq
    rw [Real.log_mul] at ineq
    .
      simp at ineq
      rw [Real.log_mul] at ineq
      simp at ineq
      rw [mul_add] at ineq
      rw [← add_assoc] at ineq
      rw [← tsub_le_iff_right] at ineq
      rw [add_comm] at ineq
      rw [← mul_assoc] at ineq
      nth_rw 4 [mul_comm] at ineq
      rw [mul_assoc] at ineq
      rw [← mul_sub] at ineq

      have reverse_ineq: swap_le ineq := by
        unfold swap_le

        have log_m_gt:  ↑data.S_poly_deg < Real.log ↑m := by
          rw [← Real.exp_lt_exp]
          rw [Real.exp_log]
          .
            unfold m
            apply Nat.lt_of_ceil_lt
            apply lt_max_of_lt_right
            simp
          . simp
            omega


        rw [Real.log_mul]
        .
          rw [mul_add]
          rw [add_comm]
          rw [← add_assoc]
          nth_grw 2 [log_m_gt]
          rw [← pow_two]
          nth_grw 3 [Real.log_le_rpow_div (ε := (1 / 2))]
          simp
          rw [mul_pow]
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul]
          simp
          norm_num
          rw [← lt_tsub_iff_right]
          rw [← mul_sub]
          rw [← div_lt_iff₀]
          .
            dsimp [m]
            apply Nat.lt_of_ceil_lt
            apply lt_max_of_lt_left
            apply lt_max_of_lt_right
            simp
          .
            simp
            rw [lt_tsub_iff_right]
            rw [← Real.exp_lt_exp]
            rw [Real.exp_log]
            .
              rw [← gt_iff_lt]
              grw [(Nat.sub_one_lt_floor _).gt]
              rw [gt_iff_lt]
              rw [lt_tsub_iff_right]
              field_simp
              rw [lt_div_iff₀']
              rw [← lt_div_iff₀]
              .
                exact eps_div_lt
              . positivity
              . apply H_n_eps_pos
            .
              simp
              rw [Nat.floor_pos]
              exact c_mul_pos
          . simp
          . simp
          . simp
        .
          simp
          refine ⟨by simp [c'], ?_⟩
          exact c_mul_pos
        . simp
          omega

      unfold swap_le at reverse_ineq
      . linarith
      . have m_ne_zero: m ≠ 0 := by
          omega
        simp [c', m_ne_zero]
        exact c_mul_pos

      . simp


    .
      exact Nat.cast_ne_zero.mpr (id (Ne.symm data.S_poly_const_pos))
    .


      apply ne_zero_of_pos
      apply pow_pos
      simp
      apply mul_pos
      .
        simp [c']
        rw [Nat.floor_pos]
        exact c_mul_pos
      . exact Nat.cast_pos'.mpr m_gt
  .
    norm_cast
    apply Nat.pow_pos
    rw [Nat.floor_pos]
    exact c_mul_pos
  .
    apply mul_pos
    . simp
      exact Nat.zero_lt_of_ne_zero (id (Ne.symm data.S_poly_const_pos))
    .
      apply pow_pos
      simp [c']
      apply mul_pos
      . simp
        rw [Nat.floor_pos]
        exact c_mul_pos
      . exact Nat.cast_pos'.mpr m_gt


#print axioms H_n_contradiction

-- Note - Vikman proves a much weaker statement (an upper boud n terms of 2^n)
-- The norms are actually bounded by a constant, which makes the rest of the proof easier
-- (it's not obvious how to get the "It follows that all the words" part to work with the exponential bound)
-- WRONG - this should be using the word norm, not the matrix norm
set_option synthInstance.maxHeartbeats 90000 in
set_option maxHeartbeats 1200000 in
lemma bad_h_n_norm_const_bound (data : HnData) (n: ℕ): ‖(theorem_3_8_h_n data n).g.val.val‖ ≤ H_n_C := by


  have d_pos: 0 < data.d := by linarith [data.hd]

  have s_norm_le (s: data.S): ‖s.val.val.val‖ ≤ 2 := by
    conv =>
      lhs
      equals ‖(s.val.val.val + -1) + 1‖ => simp
    grw [norm_add_le]
    rw [matrix_l2_norm_one d_pos]

    rw [← sub_eq_add_neg]
    grw [data.S_dist _ (by simp)]
    grw [H_n_eps_lt]
    norm_num

  induction n with
  | zero =>
    simp [theorem_3_8_h_n, H_n_C]
    grw [s_norm_le]
    norm_num
  | succ n ih =>
    simp [theorem_3_8_h_n, H_n_C]
    simp [Bracket.bracket]
    grw [Matrix.l2_opNorm_mul]
    grw [Matrix.l2_opNorm_mul]
    grw [Matrix.l2_opNorm_mul]
    simp

    have eq_sub_minus: ‖(theorem_3_8_h_n data n).g.val.val‖ = ‖((theorem_3_8_h_n data n).g.val.val - 1) + 1‖ := by
      simp

    grw [eq_sub_minus]
    --grw [norm_add_le]
    -- H_n_upper_bound_iter
    grw [s_norm_le]
    grw [norm_add_le]

    have n_eq_zero_plus: n = 0 + n := by simp
    rw [n_eq_zero_plus]
    grw [H_n_upper_bound_iter]
    simp [theorem_3_8_h_n]
    have foo := H_n_eps_pos data.hd
    have four_inv: (4: ℝ)⁻¹ = (2: ℝ)^(-2 : ℤ) := by norm_num

    grw [data.S_dist _ (by simp)]
    .
      grw [H_n_eps_lt]
      rw [matrix_l2_norm_one d_pos]
      norm_num
      simp
      rw [mul_add]
      simp
      rw [mul_add]
      ring
      rw [mul_assoc]
      rw [← pow_succ]
      rw [four_inv]
      rw [← zpow_natCast]
      rw [← zpow_mul]
      rw [← zpow_natCast]
      rw [← zpow_add₀ (by simp)]

      rw [← zpow_natCast]
      rw [← zpow_mul]
      rw [← zpow_natCast]
      rw [← zpow_add₀ (by simp)]
      rw [add_assoc]
      conv =>
        lhs
        arg 2
        rhs
        lhs
        equals 2^(-(n * 2 : ℤ)) =>
          ring
          rfl

      conv =>
        lhs
        arg 2
        lhs
        equals 2^(-(n : ℤ) + 1) =>
          ring
          simp
          rw [mul_two]
          simp
          ring

      have neg_le: (2: ℝ) ^ (-(n: ℤ) + 1) ≤ (2 ^ (1 : ℤ)) := by
        apply zpow_le_zpow_right₀
        . simp
        . simp

      have neg_mul_le: (2: ℝ) ^ (-(n * 2: ℤ)) ≤ 1 := by
        apply zpow_le_one_of_nonpos₀
        . simp
        . simp

      grw [neg_le]
      grw [neg_mul_le]
      norm_num
    . simp [theorem_3_8_h_n]
      have pos := H_n_eps_pos data.hd
      positivity


    -- have foo := H_n_eps_pos data.hd

    -- by_cases n_eq_zero: n = 0
    -- .
    --   simp [n_eq_zero]
    --   simp [theorem_3_8_h_n]
    --   grw [data.S_dist _ (by simp)]
    --   .
    --     simp [matrix_l2_norm_one]
    --     grw [H_n_eps_lt]
    --     norm_num


    -- have n_sub_eq: n = n - 1 + 1 := by
    --   omega
    -- rw [n_sub_eq]
    -- grw [H_n_upper_bound_iter]
    -- ring_nf
    -- rw [← le_div_iff₀]
    -- .
    --   rw [div_eq_mul_inv]
    --   rw [mul_assoc]
    --   norm_num
    --   -- TODO - we get a terrible error message without the simp:
    --   -- "Tactic `grewrite` failed: ‖↑↑↑(theorem_3_8_h_n data n)‖ ≤ 4 * 2 ^ n is not a relation"
    --   simp at ih
    --   grw [ih]
    --   ring_nf


    -- .
    --   simp

--#print axioms h_n_norm_const_bound


lemma H_n_eps_pow_lt_self (data: HnData) (n: ℕ) (hn: 0 < n): (H_n_eps data.hd) ^ n ≤ H_n_eps data.hd := by
  by_cases hn_eq_one: n = 1
  . simp [hn_eq_one]
  apply (pow_lt_self_of_lt_one₀ ?_ ?_ ?_).le
  . apply H_n_eps_pos
  .
    linarith [H_n_eps_lt data.hd]
  . omega



-- Note that the right-hand side of the bound doesn't end up using 'c'
-- WRONG: We need to be using the word distance (norm) here, not the matrix norm
-- The norm ‖x‖ in Vikman is the matrix norm, while |x| is the word norm
lemma bad_H_n_prod_exp_bound {m : ℕ}
  (m_gt: 0 < m) (k: ℝ) (data : HnData) (pows : Fin m → ℕ)
  (pows_le: ∀ i : Fin m, (pows i) ≤ k)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (pows_le : ∀ i : Fin m, (pows i) ≤ c * (H_n_eps data.hd)⁻¹):
  ‖(List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod.val.val‖ ≤ 2 * m * (2 ^ m) := by

  have new_bound := H_n_pow_le (m := m) (k := m) (a := 0) (by omega) pows data
  simp [-Subgroup.val_list_prod, -SubmonoidClass.coe_list_prod] at new_bound

  have norm_add_sub (a: Matrix (Fin data.d) (Fin data.d) ℂ): ‖a‖ = ‖a - 1 + 1‖ := by
    simp

  rw [norm_add_sub]
  grw [norm_add_le]
  grw [new_bound]

  have d_pos: 0 < data.d := by linarith [data.hd]

  grw [Finset.sum_le_card_nsmul (n := c * (2^m))]
  .
    simp
    rw [matrix_l2_norm_one d_pos]
    rw [mul_assoc]
    grw [c_lt]
    have one_fourty_le: (1 / 40: ℝ) ≤ 1 := by norm_num
    grw [one_fourty_le]
    simp
    rw [two_mul]
    apply add_le_add
    . ring_nf
      rfl
    .
      conv =>
        rhs
        equals (m * 2^m : ℝ) =>
          ring

      norm_cast
      apply one_le_mul
      . omega
      . exact Nat.one_le_two_pow

  . intro x _
    grw [pows_le]
    have h_pos := H_n_eps_pos data.hd
    by_cases x_eq_zero: x = ⟨0, by omega⟩
    .
      simp [x_eq_zero, theorem_3_8_h_n]
      grw [data.S_dist _ (by simp)]
      field_simp
      apply one_le_pow₀
      simp
    .
      simp at x_eq_zero
      have x_val_ne: x.val ≠ 0 := by
        by_contra!
        simp_rw [← this] at x_eq_zero
        simp at x_eq_zero
      have x_sub_eq: x.val = 0 + x.val := by
        grind
      rw [x_sub_eq]
      grw [H_n_upper_bound_iter]
      simp [theorem_3_8_h_n]
      grw [data.S_dist _ (by simp)]
      ring
      field_simp
      grw [H_n_eps_pow_lt_self]
      ring
      rw [pow_two]
      ring_nf
      rw [pow_two]
      rw [← mul_assoc]
      rw [mul_comm]
      rw [mul_assoc]
      field_simp
      grw [H_n_eps_lt]
      ring_nf
      grw [x.isLt]
      have one_four_le: (1 / 4: ℝ) ≤ 1 := by norm_num
      grw [one_four_le]
      . simp
      . simp
      . grind


-- lemma S_ball_card_bound (data: HnData) (m: ℕ) (ε: ℝ)
--   (c: ℝ)
--   (c_pos: 0 < c)
--   (c_lt: c < 1 / 40)
--   (n : ℕ) (hn : n ≠ 0) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ))
-- : (1 + c * (H_n_eps data.hd)⁻¹)^m ≤ #((G' n ε G).carrier ^ (2 * m * (2 ^ m)) ) := by


--   simp


-- TODO - deduplicate with with 'mem_S_prod_list'
lemma mem_closure_prod_list {G: Type*} [Group G] (S: Set G) (S_eq_Sinv: S = S⁻¹) (x: G) (hx: x ∈ Subgroup.closure S): ∃ l: List S, l.unattach.prod = x := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  specialize foo hx
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  conv at mem_s =>
    intro y hy
    rw [← S_eq_Sinv]
    simp
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold List.unattach
  simp [prod_eq]

open Classical

lemma mem_list_choose {T: Type*} (p: List T → Prop) {h: ∃ l, p l} {x: T} (hx: x ∈ h.choose): ∃ l, x ∈ l ∧ p l := by
  use h.choose
  refine ⟨hx, h.choose_spec⟩


-- Theorem 3.8, case with only trivial elements in the center
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
lemma central_trivial_virtually_abelian (n : ℕ) (hn : 2 ≤ n) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG)
  (G_central_trivial : ∀ g : G, g ∈ Set.center G → ∃ z : ℂ, g.val.val = z • 1)
  (G'_central_trivial : ∀ g : (G' n (H_n_eps hn) G), g ∈ Set.center (G' n (H_n_eps hn) G) → ∃ z : ℂ, g.val.val.val = z • 1)
  (G'_finite_index: (G' n (H_n_eps hn) G).FiniteIndex)
  : ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by

  by_cases all_mul_identity : ∀ h : (G' n (H_n_eps hn) G), ∃ z : ℂ, h.val.val.val = z • 1
  · use (G' n (H_n_eps hn) G)
    refine ⟨?_, ?_⟩
    · refine { is_comm := ?_ }
      refine { comm := ?_ }
      intro a b
      have a_diag := all_mul_identity a
      have b_diag := all_mul_identity b
      obtain ⟨a_z, a_eq⟩ := a_diag
      obtain ⟨b_z, b_eq⟩ := b_diag
      ext i j
      simp
      rw [a_eq, b_eq]
      simp
      group
    · infer_instance
  ·
    simp [-Subtype.forall, -Subtype.exists] at all_mul_identity
    obtain ⟨x, hx⟩ := all_mul_identity

    have G_fg: Group.FG G := by
      exact (Group.fg_iff_subgroup_fg G).mpr G_FG

    have G'_fg := Subgroup.fg_of_index_ne_zero (G' n (H_n_eps hn) G)

    rw [Group.fg_def] at G'_fg
    rw [Subgroup.fg_iff] at G'_fg
    obtain ⟨S', S'_generates, S'_finite⟩ := G'_fg

    -- Add identity and inverses to S' to make things easier
    let S'' := S' ∪ S'⁻¹
    have S''_finite: Set.Finite S'' := by
      dsimp [S'']
      simp
      apply S'_finite

    -- have S''_union_S''inv: S'' ∪ S''⁻¹ = S'' := by
    --   dsimp [S'']
    --   simp [-Set.union_singleton]
    --   rw [Set.union_assoc]
    --   apply Set.subset_union_left

    have S''_eq_S''inv: S'' = S''⁻¹ := by
      unfold S''
      simp
      rw [Set.union_comm]


    have S''_generates: Subgroup.closure S'' = ⊤ := by
      dsimp [S'']
      rw [Subgroup.closure_union]
      simp [S'_generates]


    have s_list (s: S'') := (mem_closure_prod_list ((Metric.ball (1 : G) (H_n_eps hn)) ∪ (Metric.ball (1 : G) (H_n_eps hn))⁻¹) (by
      simp
      rw [Set.union_comm]
    ) s (by
      have s_prop := s.val.property
      simp only [G'] at s_prop
      rw [Subgroup.closure_union]
      simp [s_prop]
    ))

    -- We may need to manually union this with S⁻¹, since the inverse of the produces
    -- could be chosen to be built with different elements (not the inverses of the ones in the original list)
    let pre_S := ⋃ s : S''_finite.toFinset, (s_list ⟨s, by (
      have foo := s.property
      rw [Set.Finite.mem_toFinset] at foo
      exact foo
    )⟩).choose.unattach.toFinset.toSet ∪ {1}
    let S := pre_S ∪ pre_S⁻¹ ∪ {1}

    have S_dist: ∀ s ∈ S, ‖s.val.val - 1‖ < H_n_eps hn := by
      intro s hs
      dsimp [S] at hs

      rw [Set.union_assoc] at hs
      cases hs
      . rename_i s_mem
        dsimp [pre_S] at s_mem
        rw [Set.mem_iUnion] at s_mem
        obtain ⟨y, y_mem⟩ := s_mem
        simp only [List.coe_toFinset, List.mem_unattach, Set.mem_union, Set.mem_inv,
          Set.mem_setOf_eq] at y_mem
        obtain ⟨s_mem_S'', s_mem_choose⟩ := y_mem
        simp at s_mem_S''
        simp [dist] at s_mem_S''
        rw [dist_eq_norm_sub] at s_mem_S''
        rw [dist_eq_norm_sub] at s_mem_S''
        conv at s_mem_S'' =>
          right
          arg 1
          arg 1
          equals (star s.val.val * 1 - (star s.val.val) * s.val.val) =>
            simp

        rw [← mul_sub] at s_mem_S''
        rw [← unitary.coe_star] at s_mem_S''
        rw [CStarRing.norm_coe_unitary_mul] at s_mem_S''
        nth_rw 2 [norm_sub_rev] at s_mem_S''
        simp at s_mem_S''
        . exact s_mem_S''
        .
          rename_i s_eq_one
          simp at s_eq_one
          simp [s_eq_one]
          have foo := H_n_eps_pos hn
          linarith
      .
        -- TODO - deduplicate most of this with the above case
        rename_i s_mem
        rw [Set.union_comm] at s_mem
        cases s_mem
        . rename_i s_mem_one
          simp at s_mem_one
          simp [s_mem_one]
          apply H_n_eps_pos

        rename_i s_mem
        dsimp [pre_S] at s_mem
        rw [Set.iUnion_inv] at s_mem
        rw [Set.mem_iUnion] at s_mem
        obtain ⟨y, y_mem⟩ := s_mem
        simp only [List.coe_toFinset, List.mem_unattach, Set.mem_union, Set.mem_inv,
          Set.mem_setOf_eq] at y_mem
        obtain ⟨s_mem_S'', s_mem_choose⟩ := y_mem
        simp at s_mem_S''
        simp [dist] at s_mem_S''
        rw [dist_eq_norm_sub] at s_mem_S''
        rw [dist_eq_norm_sub] at s_mem_S''
        rw [or_comm] at s_mem_S''
        conv at s_mem_S'' =>
          right
          arg 1
          arg 1
          equals (star s.val.val * 1 - (star s.val.val) * s.val.val) =>
            simp

        rw [← mul_sub] at s_mem_S''
        rw [← unitary.coe_star] at s_mem_S''
        rw [CStarRing.norm_coe_unitary_mul] at s_mem_S''
        nth_rw 2 [norm_sub_rev] at s_mem_S''
        simp at s_mem_S''
        . exact s_mem_S''
        .
          rename_i s_eq_one
          simp at s_eq_one
          simp [s_eq_one]
          have foo := H_n_eps_pos hn
          linarith

    have subsset_closure_top (A B: Set G) (hA: Subgroup.closure A = ⊤) (a_subset: A ⊆ Subgroup.closure B): Subgroup.closure B = ⊤ := by
      apply Subgroup.closure_mono at a_subset
      rw [hA] at a_subset
      simp at a_subset
      exact a_subset
    -- have S_generates: Subgroup.closure S = ⊤ := by
    --   dsimp [S, pre_S]
    --   simp_rw [Subgroup.closure_union]
    --   conv =>
    --     lhs
    --     lhs
    --     lhs
    --     equals ⊤ =>

    --       --have foo := ⨆ (i: { x // x ∈ S''_finite.toFinset }) i = ⊤ := by
    --       --  sorry
    --       -- { x // x ∈ S''_finite.toFinset }
    --       --have iunion_s_eq_top:

    --       apply subsset_closure_top (A := ((G' n (H_n_eps hn) G)).subtype '' S'')
    --       .
    --         rw [← MonoidHom.map_closure]
    --         rw [S''_generates]
    --         sorry


    --       . intro a ha
    --         simp at ha
    --       sorry
    --   sorry
    --   --simp

    have S_finite: Set.Finite S := by
      dsimp [S]
      apply Set.Finite.union
      .
        simp
        dsimp [pre_S]
        apply Set.Finite.sUnion
        .
          apply Set.finite_range
        .
          intro y hy
          rw [Set.mem_range] at hy
          obtain ⟨x, x_mem, y_eq⟩ := hy
          apply Set.Finite.union
          . apply Finset.finite_toSet
          . simp
      . simp

    have S_union_Sinv: S ∪ S⁻¹ = S := by
      dsimp [S]
      simp [-Set.union_singleton]
      grind

    have S_eq_Sinv: S = S⁻¹ := by
      rw [← S_union_Sinv]
      simp
      rw [Set.union_comm]

    have S_generates: Subgroup.closure S = (G' n (H_n_eps hn) G) := by
      -- apply_fun (Subgroup.map (G' n (H_n_eps hn) G).subtype) at S''_generates
      -- conv at S''_generates =>
      --   rhs
      --   equals (G' n (H_n_eps hn) G) =>
      --     ext a
      --     simp

      -- rw [← S''_generates]
      ext a
      unfold S
      rw [Subgroup.closure_union]
      simp
      rw [Subgroup.closure_union]
      simp
      unfold pre_S
      refine ⟨?_, ?_⟩
      . intro ha
        -- TODO - only the 'mem' case is non-trivial. We probably don't actually need a full induction proof
        induction ha using Subgroup.closure_induction with
        | one =>
          simp [G']
        | mem x hx =>
          rw [Set.mem_iUnion] at hx
          obtain ⟨y, y_mem⟩ := hx
          have y_prop := y.property
          rw [Set.Finite.mem_toFinset] at y_prop
          have my_spec := (s_list ⟨y, y_prop⟩).choose_spec
          cases y_mem
          .
            rename_i y_mem
            simp at y_mem
            obtain ⟨x_dist, x_mem⟩ := y_mem
            simp [G']
            apply Subgroup.mem_closure_of_mem
            simp
            cases x_dist
            . rename_i x_dist_le
              exact x_dist_le
            . rename_i x_inv_dist

              -- TODO - deduplicate this, in particular the 'CStarRing.norm_coe_unitary_mul' code
              simp [dist] at x_inv_dist
              rw [dist_eq_norm_sub] at x_inv_dist
              conv at x_inv_dist =>
                lhs
                arg 1
                equals (star x.val.val * 1 - (star x.val.val) * x.val.val) =>
                  simp

              rw [← mul_sub] at x_inv_dist
              rw [← unitary.coe_star] at x_inv_dist
              rw [CStarRing.norm_coe_unitary_mul] at x_inv_dist
              rw [norm_sub_rev] at x_inv_dist
              simp [dist]
              rw [dist_eq_norm_sub]
              exact x_inv_dist
          .
            rename_i x_mem_one
            simp at x_mem_one
            simp [x_mem_one]
        | mul x y hx hy x_mem y_mem =>
          apply Subgroup.mul_mem
          . exact x_mem
          . exact y_mem
        | inv x hx x_mem =>
          apply Subgroup.inv_mem
          exact x_mem
      .
        intro ha
        apply_fun (Subgroup.map (G' n (H_n_eps hn) G).subtype) at S''_generates
        conv at S''_generates =>
          rhs
          equals (G' n (H_n_eps hn) G) =>
            ext a
            simp

        rw [← S''_generates] at ha
        simp at ha
        obtain ⟨a_mem_g', a_mem_closure⟩ := ha
        rw [← Subgroup.mem_toSubmonoid] at a_mem_closure
        rw [Subgroup.closure_toSubmonoid] at a_mem_closure
        obtain ⟨l, l_mem, l_prod_eq⟩ := Submonoid.exists_list_of_mem_closure a_mem_closure
        rw [Subtype.ext_iff] at l_prod_eq
        simp at l_prod_eq
        rw [← l_prod_eq]
        apply Subgroup.list_prod_mem
        intro x x_mem_l
        simp at x_mem_l
        obtain ⟨x_mem_g', x_mem_l⟩ := x_mem_l
        have x_mem_ball := l_mem _ x_mem_l

        rw [Subgroup.closure_iUnion]
        rw [← S''_eq_S''inv] at x_mem_ball
        simp at x_mem_ball
        apply Subgroup.mem_iSup_of_mem (i := ⟨⟨x, x_mem_g'⟩, (by simp; apply x_mem_ball)⟩)
        have my_spec := (s_list  ⟨⟨x, x_mem_g'⟩, x_mem_ball⟩).choose_spec
        simp at my_spec
        conv =>
          arg 2
          rw [← my_spec]

        apply Subgroup.list_prod_mem
        intro b b_mem
        apply Subgroup.mem_closure_of_mem
        apply Set.mem_union_left
        simpa using b_mem


        -- intro ha
        -- unfold G' at ha
        -- induction ha using Subgroup.closure_induction with
        -- | mem x hx =>

        --   sorry
        -- | one =>
        --   simp
        -- | mul x y hx hy x_mem y_mem =>
        --   apply Subgroup.mul_mem
        --   exact x_mem
        --   exact y_mem
        -- | inv x hx x_mem =>
        --   apply Subgroup.inv_mem
        --   exact x_mem





    have nontrivial_h: ∃ h: S, ∀ z: ℂ,  h.val.val.val ≠ z • 1 := by
      by_contra!

      have x_mem_closure: x.val ∈ Subgroup.closure S := by
        rw [S_generates]
        simp


      rw [← Subgroup.mem_toSubmonoid] at x_mem_closure
      rw [Subgroup.closure_toSubmonoid] at x_mem_closure
      obtain ⟨l, l_mem, l_prod_eq⟩ := Submonoid.exists_list_of_mem_closure x_mem_closure
      simp_rw [S_union_Sinv] at l_mem

      have list_prod_trivial: ∃ z: ℂ, l.unattach.unattach.prod = z • 1 := by
        apply List.prod_induction (p := fun a => ∃ z: ℂ, a = z • 1)
        .
          intro a b a_diag b_diag
          obtain ⟨a_z, a_eq⟩ := a_diag
          obtain ⟨b_z, b_eq⟩ := b_diag
          use b_z * a_z
          rw [a_eq, b_eq]
          rw [mul_smul]
          simp
        . use 1
          simp
        .
          intro x x_mem
          rw [List.mem_unattach] at x_mem
          obtain ⟨a, ha⟩ := x_mem
          rw [List.mem_unattach] at ha
          obtain ⟨b, hb⟩ := ha
          have mem_s := l_mem _ hb
          have x_diag := this ⟨_, mem_s⟩
          exact x_diag

      obtain ⟨z, l_prod_eq_diag⟩ := list_prod_trivial
      have x_neq := hx z
      rw [← l_prod_eq_diag] at x_neq
      rw [← l_prod_eq] at x_neq
      dsimp [List.unattach] at x_neq
      simp at x_neq

    obtain ⟨h, h_nontrivial⟩ := nontrivial_h


    let h_n_data: HnData := {
      d := n
      hd := hn
      G := Subgroup.map G.subtype (G' n (H_n_eps hn) G)
      G_central_trivial := by
        intro g hg
        apply G'_central_trivial ⟨⟨⟨g.val.val, by simp⟩, by (
          simp
          have prop := g.property
          rw [Subgroup.mem_map] at prop
          obtain ⟨q, q_mem, g_eq_q⟩ := prop
          rw [← g_eq_q]
          simp
        )⟩, by (
          simp
          have prop := g.property
          rw [Subgroup.mem_map] at prop
          obtain ⟨q, q_mem, g_eq_q⟩ := prop
          simp_rw [← g_eq_q]
          simp
          exact q_mem
        )⟩
        rw [← Subgroup.coe_center]
        rw [← Subgroup.coe_center] at hg
        simp
        simp at hg
        rw [Subgroup.mem_center_iff]
        rw [Subgroup.mem_center_iff] at hg
        intro a
        have foo := hg ⟨⟨a.val, by (
          simp
        )⟩, by(
          simp
        )⟩
        simp at foo
        simp [Subtype.ext_iff]
        rw [Subtype.ext_iff] at foo
        simp at foo
        rw [Subtype.ext_iff] at foo
        simpa using foo

      S := (Finset.image (fun a => (⟨a.val.val, by (
        simp
        simp [G']
        apply Subgroup.mem_closure_of_mem
        simp
        simp [dist]
        rw [dist_eq_norm_sub]
        have a_prop := a.property
        rw [Set.Finite.mem_toFinset] at a_prop
        have a_dist := S_dist a a_prop
        exact a_dist
      )⟩: (Subgroup.map G.subtype (G' n (H_n_eps hn) G)))) S_finite.toFinset.attach).toSet
      S_generates := by
        simp
        have orig_S'' := S''_generates
        apply_fun (Subgroup.map (G' n (H_n_eps hn) G).subtype) at S''_generates
        conv at S''_generates =>
          rhs
          equals (G' n (H_n_eps hn) G) =>
            ext a
            simp

        apply_fun (Subgroup.map ({
          toFun := fun a => (⟨a.val, (by
            have prop := a.property
            rw [Subgroup.mem_map] at prop
            obtain ⟨x, x_mem, x_eq⟩ := prop
            rw [← x_eq]
            simp
          )⟩ : G),
          map_one' := by
            simp
          map_mul' := by
            intro a b
            simp
        })) using (?_)
        . conv =>
            rhs
            equals (G' n (H_n_eps hn) G) =>
              ext a
              rw [Subgroup.mem_map]
              refine ⟨?_, ?_⟩
              .
                intro exists_x
                obtain ⟨x, x_mem, a_eq⟩ := exists_x
                simp at a_eq
                have x_prop := x.property
                rw [Subgroup.mem_map] at x_prop
                obtain ⟨y, y_mem, x_eq_y⟩ := x_prop
                rw [← a_eq]
                conv =>
                  arg 2
                  simp [← x_eq_y]
                exact y_mem
              . intro a_mem
                use ⟨a, ?_⟩
                . refine ⟨by simp, ?_⟩
                  simp
                . rw [Subgroup.mem_map]
                  use ⟨a, ?_⟩
                  . refine ⟨by simp; apply a_mem, ?_⟩
                    simp
                  . simp

          conv =>
            rhs
            rw [← S''_generates]
          ext a
          rw [Subgroup.mem_map]
          refine ⟨?_, ?_⟩
          .
            intro ha
            simp at ha
            simp
            obtain ⟨b, b_mem, a_mem_g, b_mem_closure, a_eq_b⟩ := ha
            use ?_
            . conv =>
                arg 2
                simp only [← a_eq_b]

              rw [orig_S'']
              simp
            . obtain ⟨b_mem, b_mem_g'⟩ := a_mem_g
              rw [← a_eq_b]
              simp [b_mem_g']
          . intro ha
            use ⟨a, ?_⟩
            . refine ⟨?_, by simp⟩
              rw [Subgroup.mem_map] at ha
              obtain ⟨b, b_mem, a_eq_b⟩ := ha
              have b_prop := b.property
              conv at b_prop =>
                arg 1
                rw [← S_generates]

              conv =>
                arg 2
                simp [← a_eq_b]

              rw [←  Subgroup.mem_map_iff_mem (f := Subgroup.subtype _)]
              conv =>
                arg 1
                equals Subgroup.map G.subtype (G' n (H_n_eps hn) G) =>
                  sorry
              . simp
              . simp
            . simp at ha
              simp
              obtain ⟨a_mem_g', a_mem_closure⟩ := ha
              apply a_mem_g'
      S_finite := by
        simp
        apply Set.finite_range
      S_one := by
        simp
        dsimp [S]
        apply Set.mem_union_right
        simp
      S_inv := by
        intro s hs
        rw [Finset.coe_image]
        rw [Finset.coe_image] at hs
        rw [Set.mem_image] at hs
        obtain ⟨x, x_mem, s_eq⟩ := hs
        rw [Set.mem_image]
        use ⟨x⁻¹, ?_⟩
        .
          simp
          rw [← s_eq]
          rfl
        . simp

          nth_rw 1 [S_eq_Sinv]
          simp
          have x_prop := x.property
          rw [Set.Finite.mem_toFinset] at x_prop
          exact x_prop
      S_dist := by
        intro s hs
        rw [Finset.coe_image] at hs
        rw [Set.mem_image] at hs
        obtain ⟨x, x_mem, s_eq⟩ := hs
        have x_prop := x.property
        rw [Set.Finite.mem_toFinset] at x_prop
        have s_dist := S_dist x x_prop
        rw [← s_eq]
        linarith
      S_poly_const := sorry
      S_poly_const_pos := sorry
      S_poly_deg := sorry
      S_poly := sorry
      h := ⟨⟨h.val.val, by (
        have h_prop := h.property
        simp only [S] at h_prop
        simp
        cases h_prop
        . rename_i h_mem
          . cases h_mem
            . rename_i h_prop
              dsimp [pre_S] at h_prop
              rw [Set.mem_iUnion] at h_prop
              obtain ⟨y, y_mem⟩ := h_prop
              simp [-Set.mem_inv] at y_mem
              have h_dist := S_dist h (by simp)
              simp [G']
              apply Subgroup.mem_closure_of_mem
              simp
              simp [dist]
              rw [dist_eq_norm_sub]
              exact h_dist
            . rename_i h_prop
              -- TODo: deduplicate
              dsimp [pre_S] at h_prop
              simp_rw [Set.iUnion_inv] at h_prop
              rw [Set.mem_iUnion] at h_prop
              obtain ⟨y, y_mem⟩ := h_prop
              simp [-Set.mem_inv] at y_mem
              have h_dist := S_dist h (by simp)
              simp [G']
              apply Subgroup.mem_closure_of_mem
              simp
              simp [dist]
              rw [dist_eq_norm_sub]
              exact h_dist
        . rename_i h_mem
          simp at h_mem
          simp [G']
          simp [h_mem]
      )⟩, by simp⟩
      h_nontrivial := by
        simpa using h_nontrivial
    }

    have contra := H_n_contradiction h_n_data (1 / 50) ?_ ?_ ?_ ?_
    . contradiction
    . simp
    . simp
      norm_num
    .
      rw [← div_le_iff₀']
      .
        rw [le_inv_comm₀]
        .
          simp
          simp [H_n_eps]
          left
          norm_num
        . simp
        . apply H_n_eps_pos
      . simp
    .
      simp
      sorry


-- Helper for theorem 3.8
-- TODO - the name is bad, rename it to not include 'central'
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 2000000 in
lemma compact_lie_virtually_abelian (n : ℕ) (hn : n ≠ 0) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG): ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by
  by_cases n_eq_one : n = 1
  · have fin_sin_subsingleton : Subsingleton (Fin n) := by
      rw [n_eq_one]
      exact Fin.subsingleton_one
    have all_diag : ∀ h : G, h.val.val.IsDiag := by
      intro h
      apply Matrix.isDiag_of_subsingleton

    have all_comm : ∀ (a b : G), a.val.val * b.val.val = b.val.val * a.val.val := by
      intro a b
      have diag_a := all_diag a
      have diag_b := all_diag b
      rw [Matrix.isDiag_iff_diagonal_diag] at diag_a
      rw [Matrix.isDiag_iff_diagonal_diag] at diag_b
      rw [← diag_a, ← diag_b]
      simp
      intro i
      rw [mul_comm]

    use ⊤
    refine ⟨?_, ?_⟩
    · exact {
        is_comm := by
          exact {
            comm := by
              intro a b
              rw [Subtype.ext_iff]
              simp
              rw [Subtype.ext_iff]
              simp
              rw [Subtype.ext_iff]
              simp
              apply all_comm
          }
      }
    · exact Subgroup.instFiniteIndexTop
  · have nontrivial_centrer_implies_virtual (G : Subgroup ↥(Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG) (nontrivial_central : ∃ g : G, (∀ z : ℂ, g.val.val ≠ z • 1) ∧ g ∈ Set.center G): ∃ N : Subgroup G, IsMulCommutative ↥N ∧ N.FiniteIndex := by
      obtain ⟨g, g_not_multiple_I, g_central⟩ := nontrivial_central
      -- have G_subset_centralizer :  ⊆ (Subgroup.centralizer {g}).carrier := by
      --   intro a ha
      --   simp
      --   rw [Subgroup.mem_centralizer_iff]
      --   intro b hb
      --   simp at hb
      --   rw [hb]
      --   rw [Set.mem_center_iff] at g_central
      --   have g_comm := g_central.comm ⟨a, ha⟩
      --   rw [Subtype.ext_iff] at g_comm
      --   simp at g_comm
      --   apply g_comm

      have all_mem_central : ∀ a : G, a ∈ Subgroup.centralizer {g} := by
        intro a b b_mem
        simp at b_mem
        rw [b_mem]
        rw [Set.mem_center_iff] at g_central
        have g_comm := g_central.comm a
        exact g_comm

      have n_ge_two : 2 ≤ n := by
        omega
      obtain ⟨data⟩ := inductive_lemma n n_ge_two G g g_not_multiple_I
      -- TODO - PR this to mathlib
      have subgroup_fg : ∀ i : Fin (data.k), (data.groups i).FG := by
        intro i
        have iso := data.iso
        have centralizer_fg : (Subgroup.centralizer {g}).FG := by
          conv =>
            arg 1
            equals ⊤ =>
              simp
              exact g_central
          rw [← Group.fg_def]
          exact (Group.fg_iff_subgroup_fg G).mpr G_FG
        -- TODO - why doesn't `Pi.evalMonoidHom' work here?
        let i_hom : ((j : Fin data.k) → ↥(data.groups j)) →* (data.groups i) := {
          toFun := fun f => f i,
          map_one' := Pi.one_apply i,
          map_mul' := by
            intro x y
            simp

        }
        rw [Subgroup.fg_iff_submonoid_fg] at centralizer_fg
        have map_prod_fg := Submonoid.FG.map (P := ⊤) ?_ data.iso.toMonoidHom
        · simp at map_prod_fg
          rw [← Monoid.fg_def] at map_prod_fg
          have range_fg := Monoid.fg_range i_hom
          rw [MonoidHom.mrange_eq_top.mpr] at range_fg
          rw [Monoid.fg_def] at range_fg
          --simp [i_hom] at range_fg
          have map_factor := Submonoid.FG.map (P := ⊤) ?_ i_hom
          rw [Subgroup.fg_iff_submonoid_fg]
          conv at map_factor =>
            arg 1
            equals ⊤ =>
              ext a
              simp
              -- TODO - deduplicate this
              use (fun j => if hij : i = j then (
                have group_equiv : data.groups i ≃* data.groups j := by
                  rw [hij]

                group_equiv a
              ) else 1)
              simp [i_hom]
          rw [← Monoid.fg_def] at map_factor
          · exact (Monoid.fg_iff_submonoid_fg (data.groups i).toSubmonoid).mp map_factor
          · exact Monoid.fg_def.mp map_prod_fg
          · intro a
            use (fun j => if hij : i = j then (
              have group_equiv : data.groups i ≃* data.groups j := by
                rw [hij]

              group_equiv a
            ) else 1)
            simp [i_hom]


        --rw [← Monoid.fg_iff_submonoid_fg] at centralizer_fg

        rw [← Subgroup.fg_iff_submonoid_fg] at centralizer_fg
        rw [← Subgroup.top_toSubmonoid, ← Subgroup.fg_iff_submonoid_fg, ← Group.fg_def]
        exact (Group.fg_iff_subgroup_fg (Subgroup.centralizer {g})).mpr centralizer_fg
        -- rw [← Monoid.FG.fg_top]
        -- obtain ⟨S, hS⟩ := centralizer_fg
        -- let pre_S' := Finset.image (fun s => (⟨s, all_mem_central s⟩: (Subgroup.centralizer {g}))) S
        -- let S' := Finset.image iso pre_S'
        -- let pre_target := Finset.image (fun f => f i) S'
        -- let target := Finset.image (Subgroup.subtype _) pre_target
        -- unfold Subgroup.FG
        -- use target
        -- simp [target, pre_target, S', pre_S']
        -- ext a





        -- sorry
      -- The abelian subgroup of G_i.
      let Gi' := fun i : Fin (data.k) => compact_lie_virtually_abelian (data.n_i i) (data.positive_n_i i) (data.groups i) (subgroup_fg i)
      -- Page 48 : Let Gᵢ := πᵢ⁻¹(πᵢ(G)′) = {g ∈ G : πᵢ(g) ∈ πᵢ(G)′}
      let inv_image : Fin (data.k) → Subgroup G := fun i : Fin (data.k) => {
        carrier := { a : G | (data.iso ⟨a, all_mem_central a⟩) i ∈ (Classical.choose (Gi' i)) },
        mul_mem' := by
          intro _ _ ha hb
          simpa [ha, hb, ← Pi.mul_apply, ← MulEquiv.map_mul] using Subgroup.mul_mem _ ha hb
        one_mem' := by
          simp
          conv =>
            arg 2
            arg 2
            equals 1 => simp

          rw [MulEquiv.map_one]
          simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ⊢ ha

          conv =>
            arg 2
            arg 2
            equals ⟨a, all_mem_central a⟩⁻¹ =>
              ext
              simp
          simpa [MulEquiv.map_inv, Pi.inv_apply, Subgroup.inv_mem_iff]
      }

      -- TODO - figure out a way to make this proof less horrible (maybe somehow avoid Classical.choose)
      have inv_image_comm (a b) (ha : ∀ i, a ∈ inv_image i) (hb : ∀ i, b ∈ inv_image i): a * b = b * a := by
        simp [inv_image] at ha hb
        have symm_mul := MulEquiv.symm_apply_apply (e := data.iso) ⟨(a * b), (by
          apply Subgroup.mul_mem
          · apply all_mem_central
          · apply all_mem_central
        )⟩
        have symm_mul_swap := MulEquiv.symm_apply_apply (e := data.iso) ⟨(b * a), (by
          apply Subgroup.mul_mem
          · apply all_mem_central
          · apply all_mem_central
        )⟩
        rw [Subtype.ext_iff] at symm_mul
        simp only [] at symm_mul
        rw [Subtype.ext_iff] at symm_mul_swap
        simp only [] at symm_mul_swap
        rw [← symm_mul, ← symm_mul_swap, ← Subtype.ext_iff]
        apply congrArg
        funext i
        specialize ha i
        specialize hb i

        have comm_subgroup := (Classical.choose_spec (Gi' i)).1.is_comm.comm
        have a_b_comm := comm_subgroup ⟨_, ha⟩ ⟨_, hb⟩
        rw [Subtype.ext_iff] at a_b_comm
        simp at a_b_comm

        conv =>
          lhs
          arg 2
          equals ⟨a, all_mem_central a⟩ * ⟨b, all_mem_central b⟩ =>
            simp only [MulMemClass.mk_mul_mk]

        conv =>
          rhs
          arg 2
          equals ⟨b, all_mem_central b⟩ * ⟨a, all_mem_central a⟩ => simp only [MulMemClass.mk_mul_mk]



        rw [MulEquiv.map_mul]
        rw [MulEquiv.map_mul]
        simp
        rw [a_b_comm]
      let G' := ⨅ (i : Fin (data.k)), inv_image i

      have G'_comm : ∀ a b : G', a * b = b * a := by
        intro a b
        have a_mem := a.property
        have b_mem := b.property
        rw [Subgroup.mem_iInf] at a_mem
        apply Subtype.ext_val
        simp

        have a_val := a.property
        have b_val := b.property
        dsimp [G'] at a_val
        dsimp [G'] at b_val
        rw [Subgroup.mem_iInf] at a_val
        rw [Subgroup.mem_iInf] at b_val
        have a_b_comm := inv_image_comm a b a_val b_val
        exact a_b_comm

      have inv_image_finite_index : ∀ i : Fin (data.k), (inv_image i).FiniteIndex := by
        intro i
        have finite_index_subgroup := (Classical.choose_spec (Gi' i)).2
        have finite_quotient := @Subgroup.finite_quotient_of_finiteIndex _ _ _ finite_index_subgroup

        have subgroup_union_coset := QuotientGroup.univ_eq_iUnion_smul ((Classical.choose (Gi' i)))
        --apply Subgroup.finiteIndex_of_leftCoset_cover_const (g := id)

        apply @Subgroup.finiteIndex_of_finite_quotient _ _ _ ?_
        apply Finite.of_injective (β := (data.groups i) ⧸ (Classical.choose (Gi' i))) (f := fun a => (
          data.iso ⟨a.out, all_mem_central _⟩ i
        ))
        intro x y hxy
        simp at hxy
        rw [← QuotientGroup.out_eq' (a := x), ← QuotientGroup.out_eq' (a := y), QuotientGroup.eq]
        simp [inv_image]

        rw [QuotientGroup.eq] at hxy
        conv at hxy =>
          arg 2
          lhs
          equals (data.iso ⟨x.out, all_mem_central _⟩)⁻¹ i =>
            simp
        rwa [← MulEquiv.map_inv, ← Pi.mul_apply, ← MulEquiv.map_mul] at hxy

        --simp [inv_image]
        -- Subgroup.finiteIndex_iff_finite_quotient
        --apply Subgroup.finiteIndex_of_leftCoset_cover_const
        --sorry



      let G' := ⨅ (i : (Fin (data.k))), inv_image i
      have G'_abeliean : IsMulCommutative G' := by
        exact {
          is_comm := by
            exact {
              comm := by
                exact G'_comm
            }
        }

      have G'_finite_index : G'.FiniteIndex := by
        apply Subgroup.finiteIndex_iInf
        apply inv_image_finite_index

      --unfold UnitaryProd at centralizer_iso
      use G'
    by_cases nontrivial_central : ∃ g : G, (∀ z : ℂ, g.val.val ≠ z • 1) ∧ g ∈ Set.center G
    · exact nontrivial_centrer_implies_virtual G G_FG nontrivial_central
    · -- Case two - we have no non-trivial central elements

      have two_le_n: 2 ≤ n := by
        omega
      simp only [ne_eq, not_exists, not_and] at nontrivial_central
      let ε: ℝ := (H_n_eps two_le_n)
      have hε : 0 < ε := by
        simp [ε]
        apply H_n_eps_pos

      obtain ⟨C, G_eps⟩:= volume_packing n (by omega) ε hε
      specialize G_eps G


      by_cases G'_nontrivial_central : ∃ g : (G' n ε G), (∀ z : ℂ, g.val.val.val ≠ z • 1) ∧ g ∈ Set.center (G' n ε G)
      · have G'_virtual := nontrivial_centrer_implies_virtual (Subgroup.map G.subtype (G' n ε G)) (by
          have G'_finite := G_eps.1
          have G_FG_other : Group.FG G := by
            exact (Group.fg_iff_subgroup_fg G).mpr G_FG
          have G'_FG := Subgroup.fg_of_index_ne_zero (G' n ε G)
          -- TODO - PR this to mathlib
          rw [Subgroup.fg_iff_submonoid_fg]
          apply Submonoid.FG.map
          rw [← Subgroup.fg_iff_submonoid_fg]
          exact (Group.fg_iff_subgroup_fg (G' n ε G)).mp G'_FG
        ) (by
          obtain ⟨g, hg⟩ := G'_nontrivial_central
          use ⟨g, by simp⟩
          refine ⟨?_, ?_⟩
          · intro z
            simp
            have g_prop := hg.1 z
            simpa using g_prop
          · have g_mem := hg.2
            rw [Set.mem_center_iff]
            rw [Set.mem_center_iff] at g_mem
            exact {
              comm := by
                -- TODO - make this less horrible
                intro a
                obtain ⟨b, b_mem, b_map⟩ := Subgroup.mem_map.mpr a.property
                simpa [Subtype.ext_iff, commute_iff_eq, ← b_map] using g_mem.comm ⟨b, b_mem⟩
              left_assoc := by intros; group
              right_assoc := by intros; group
            }
        )
        -- We view G' as a subgroup of the unitary group
        --have G'_virtual := central_implies_virtually_abelian n hn (Subgroup.map G.subtype (G' n ε G))
        obtain ⟨N, N_comm, N_finite_index⟩ := G'_virtual

        have G'_iso := Subgroup.equivMapOfInjective (G' n ε G) G.subtype (by simp)
        let G'_hom := G'_iso.symm.toMonoidHom
        refine ⟨Subgroup.map (Subgroup.subtype _) <| Subgroup.map G'_hom N, ?_, ?_⟩
        · simp [G'_hom]
          apply Subgroup.map_isMulCommutative
        · rw [Subgroup.finiteIndex_iff, Subgroup.index_map]
          rw [Subgroup.finiteIndex_iff] at N_finite_index G_eps
          simpa [G'_hom] using ⟨N_finite_index, G_eps.1⟩

        -- use Subgroup.comap G.subtype (Subgroup.map (Subgroup.subtype _) N)
        -- refine ⟨?_, ?_⟩
        -- .
        --   sorry
        -- . rw [Subgroup.finiteIndex_iff]
        --   rw [Subgroup.index_comap]
        --   rw [Subgroup.index_map]
        --   sorry

        --let inner := (Subgroup.map G.subtype (G' n ε G)).subtype
        --let bar := Subgroup.map inner N


        --let bar := N.subtype
        --let other := bar.subtype.range
        --let foo := Subgroup.map (Subgroup.subtype _) N

        --let foo := Subgroup.comap ((Subgroup.map (G.subtype (G' n ε G))).subtype) N
      · simp at hn
        have target := central_trivial_virtually_abelian n (by omega) G G_FG ?_ ?_ G_eps.1
        · exact target
        · intro g hg
          specialize nontrivial_central g
          rw [← not_imp_not] at nontrivial_central
          simp at nontrivial_central
          exact nontrivial_central hg
        · intro g hg
          simp only [ne_eq, not_exists, not_and] at G'_nontrivial_central
          specialize G'_nontrivial_central g
          rw [← not_imp_not] at G'_nontrivial_central
          simp at G'_nontrivial_central
          exact G'_nontrivial_central hg
termination_by (n, G.index)
decreasing_by
  · apply Prod.Lex.left
    exact data.n_i_lt i

#print axioms compact_lie_virtually_abelian
