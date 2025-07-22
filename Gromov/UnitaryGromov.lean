import Mathlib

open scoped Matrix.L2OpNorm ComplexInnerProductSpace
--open scoped ComplexInnerProductSpace


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


def diag_unitary (c: ℂ)  (n: ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun _ => c)

lemma diag_mem_unitary (c: ℂ) (hc: ‖c‖ = 1) (n: ℕ): diag_unitary c n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  dsimp [diag_unitary]
  rw [Matrix.mem_unitaryGroup_iff]
  dsimp [star]
  simp
  rw [Complex.mul_conj']
  simp [hc]

-- Note - `1 = det h'` comes from the fact that 'h' is equal to a commutator [a, b]
lemma small_dist_matrix (n: ℕ) (hn: 0 < n) (h: Matrix.unitaryGroup (Fin n) ℂ) (h_det: h.val.det = 1) (ε : ℝ) (hε: 0 < ε)
  (h_dist: ‖h.val - 1‖ < ε) (c: ℂ) (hc: ‖c‖ = 1) (h_mul: h = diag_unitary c n): ∃ C: ℝ, ε < C → c = 1 := by
  rw [h_mul] at h_dist
  simp [diag_unitary] at h_dist

  conv at h_dist =>
    arg 1
    arg 1
    lhs
    equals c • (Matrix.diagonal (fun _ => 1)) =>
      rw [← Matrix.smul_one_eq_diagonal]
      simp

  have c_nonzero: c ≠ 0 := by
    by_contra!
    rw [this] at hc
    simp at hc

  have ne_zero_n: NeZero n := by
    rw [neZero_iff]
    linarith

  let c_unit: Units ℂ := {
      val := c,
      inv := c⁻¹,
      val_inv := by field_simp
      inv_val := by field_simp
    }

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
  have det_eq_c_n: h.val.det = c^n := by
    rw [h_mul]
    simp [diag_unitary]


  rw [h_det] at det_eq_c_n
  by_cases n_eq_one: n = 1
  . rw [n_eq_one] at det_eq_c_n
    simp at det_eq_c_n
    rw [eq_comm] at det_eq_c_n
    simp [det_eq_c_n]

  have n_gt_one: 1 < n := by omega
  let dists := (fun (x: ℂ) => (‖x - 1‖ : ℝ)) '' ((Units.val '' (rootsOfUnity n ℂ).carrier \ {1}))
  --let dists := (fun x => ‖x - (1: ℂ)‖) '' (Units.val '' (rootsOfUnity n ℂ).carrier \ {1})

  -- TODO - why can't we combine these into a single line?
  have foo := Set.Finite.exists_minimal (s := dists) ?_ ?_
  obtain ⟨min_dist, h_min_dist⟩ := foo
  . simp [Minimal] at h_min_dist
    use min_dist
    intro eps_lt



    by_contra!

    have c_mem : c ∈ Units.val '' rootsOfUnity n ℂ := by
      use c_unit
      simp [c_unit]
      ext
      simp
      rw [← det_eq_c_n]

    have c_dist_e: ε ≤ ‖ c - 1‖ := by
      grw [eps_lt]
      have c_dist  := h_min_dist.2 (y := ‖c - 1‖)
      simp [dists] at c_dist
      have dist_ge := c_dist c_unit ?_ ?_ ?_
      .
        by_contra!
        specialize dist_ge (by linarith)
        linarith
      . simp [c_unit]
        ext
        simp
        rw [det_eq_c_n]
      . simp [c_unit]
        rw [Units.ext_iff]
        simp
        simp [this]
      . simp [c_unit]
    linarith
  .
    simp [dists]
    apply Set.Finite.image
    apply Set.Finite.diff
    apply Set.Finite.image


    have fintype_roots := rootsOfUnity.fintype (k := n) (R  := ℂ)
    have finite_roots: Finite ↥(rootsOfUnity n ℂ) := by infer_instance
    -- TODO - how is this working???
    exact finite_roots
  .
    simp [dists]
    rw [Set.diff_nonempty]
    have roots_mem := Complex.mem_rootsOfUnity (n := n)
    simp

    let my_root: Units ℂ := {
      val := Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)),
      inv := (Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)))⁻¹
      val_inv := by simp
      inv_val := by simp
    }
    use my_root
    simp [my_root]
    refine ⟨?_, ?_⟩
    . ext
      simp
      rw [← Complex.exp_nat_mul]
      rw [mul_comm]
      field_simp
    .
      rw [Units.ext_iff]
      simp
      rw [Complex.exp_eq_one_iff]
      simp
      intro a
      conv =>
        arg 1
        rhs
        rw [mul_comm]
      field_simp
      by_contra!
      apply mul_left_cancel₀ at this
      .
        field_simp at this
        have abs_lt_one: ‖((1: ℂ) / ↑n)‖ < 1 := by
          simp
          have div_le := Nat.cast_inv_le_one (α := ℝ) n
          by_cases inv_eq_one: (n : ℝ)⁻¹ = 1
          .
            simp at inv_eq_one
            linarith
          .
            rw [← ne_iff_lt_iff_le] at div_le
            simp [n_eq_one] at div_le
            exact div_le
        by_cases a_eq_zero: a = 0
        . rw [a_eq_zero] at this
          simp at this
          omega
        .
          have abs_a := Int.one_le_abs a_eq_zero
          rw [this] at abs_lt_one
          simp at abs_lt_one
          norm_cast at abs_lt_one
          linarith
      . norm_num
        have pos := Real.pi_pos
        linarith

#print axioms small_dist_matrix

-- Lemma 3.31 (Volume Packing)
set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 500000 in
open Pointwise in
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



    have card_i_le: ENat.card I ≤ (1: ENNReal) / (MeasureTheory.volume ((Metric.ball (1: (Matrix.unitaryGroup (Fin n) ℂ)) ((ε / 2)/2)))) := by
      rw [div_eq_mul_inv]
      rw [mul_comm]
      rw [← ENNReal.mul_le_iff_le_inv]
      rw [mul_comm]
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
      exact volume_sum
      .
        apply Set.PairwiseDisjoint.countable_of_isOpen (s := fun g => Metric.ball g ((ε / 2)/2))
        . exact disjoint_balls
        . intro i hi
          exact Metric.isOpen_ball
        . intro i hi
          simp [hε]
      . exact disjoint_balls
      . intro i hi
        exact measurableSet_ball
      .
        apply LT.lt.ne'
        unfold MeasureTheory.volume
        simp [measure_haar]
        apply IsOpen.measure_pos
        exact Metric.isOpen_ball
        simp [hε]
      .
        unfold MeasureTheory.volume
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

    have card_lt_top: (ENat.card I).toENNReal < ⊤ := by
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

    have fintype_I: Fintype I := by
      exact Set.Finite.fintype card_lt_top

    have i_mem_G: ∀ i ∈ I, i ∈ G := by
      intro i i_mem
      simp [Maximal] at hI
      have I_prop := hI.1
      simp [-Subtype.forall, I_sets] at I_prop
      apply (I_prop.1 i_mem)

    --have g_hsmul: HSMul G (Set G) (Set G) := by
    --  infer_instance


    have cosets_cover: (⋃ i ∈ I.toFinset.attach, (((⟨i.val, i_mem_G i.val (Set.mem_toFinset.mp i.property)⟩ : G) • (((G' n ε G)) : Set G)) : (Set G))) = (Set.univ : Set G) := by
      have balls_inter_cover: G.carrier ⊆ ⋃ g ∈ I, ((Metric.ball g ε) ∩ G.carrier) := by
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
      have a_mem_g: a.val ∈ G.carrier := by simp
      specialize balls_inter_cover a_mem_g
      simp only [Set.mem_iUnion] at balls_inter_cover
      obtain ⟨i, i_mem, a_mem_i⟩ := balls_inter_cover
      have i_mem_G: i ∈ G.carrier := by
        simp [Maximal] at hI
        have I_prop := hI.1
        simp [-Subtype.forall, I_sets] at I_prop
        apply (I_prop.1 i_mem)
      specialize inter_subset i i_mem_G
      have a_mem := inter_subset a_mem_i
      simp only [Set.mem_image] at a_mem
      obtain ⟨x, hx, a_eq_mul⟩ := a_mem
      simp only [Set.mem_iUnion]
      have i_mem_finset: i ∈ I.toFinset := by
        exact Set.mem_toFinset.mpr i_mem
      use ⟨i, i_mem_finset⟩
      simp
      rw [Set.mem_smul_set]
      use x
      refine ⟨?_, ?_⟩
      . exact hx
      .
        rw [Subtype.ext_iff]
        simp [a_eq_mul]

    refine ⟨?_, ?_⟩
    .
      apply Subgroup.finiteIndex_of_leftCoset_cover_const cosets_cover
    .
      have I_subset_G: I ⊆ G := by
        simp [Maximal] at hI
        have i_mem := hI.1
        simp [I_sets] at i_mem
        exact i_mem.1


      norm_cast at card_i_le
      grw [Subgroup.index_le_of_leftCoset_cover_const (s := I.toFinset.attach) (g := fun a => (⟨a.val, by (
        have a_mem := a.prop
        have a_mem_i: a.val ∈ I := by
          exact Set.mem_toFinset.mp a_mem
        exact I_subset_G a_mem_i
      )⟩ : G))]

      simp at card_i_le
      rw [le_div_iff₀]
      .
        rw [Finset.card_attach]
        rw [← Set.ncard_eq_toFinset_card']

        rw [← Set.Finite.cast_ncard_eq] at card_i_le
        simp at card_i_le
        rw [← ENNReal.toReal_le_toReal] at card_i_le
        simp at card_i_le
        exact card_i_le
        . apply ENNReal.mul_ne_top
          . simp
          . unfold MeasureTheory.volume
            simp [measure_haar]
        . simp
        . exact card_lt_top
      .
        unfold MeasureTheory.volume
        simp [measure_haar]
        conv =>
          lhs
          equals (0: ENNReal).toReal => simp
        rw [ENNReal.toReal_lt_toReal]
        apply IsOpen.measure_pos
        exact Metric.isOpen_ball
        simp [hε]
        . simp
        . simp
      . apply cosets_cover

    --  (g := fun g => Metric.ball g ((ε / 2) / 2))

    --have coset_bound := Subgroup.index_le_of_leftCoset_cover_const (H := G' n ε G) (s := I)
    --sorry
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

#print axioms volume_packing

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

structure InductiveLemmaData (n: ℕ) (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g: G) where
  k: ℕ
  k_pos: 0 < k
  n_i: Fin k → ℕ
  n_i_lt: ∀ i: Fin k, n_i i < n
  positive_n_i: ∀ i: Fin k, n_i i ≠ 0
  groups: (i: Fin k) → Subgroup (Matrix.unitaryGroup (Fin (n_i i)) ℂ)
  iso: Subgroup.centralizer {g} ≃* ((i: Fin k) → (groups i))

-- Lemma 3.30
lemma inductive_lemma (n: ℕ) (hn: n ≠ 0) (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g: G) (g_not_multiple_I: ∀ z: ℂ, g.val.val ≠ z • 1):
  Nonempty (InductiveLemmaData n G g) := by

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

#check Pi.commSemigroup

-- Theorem 3.8, case with only trivial elements in the center
lemma central_trivial_virtually_abelian (n: ℕ) (hn: n ≠ 0) (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG: G.FG) (ε: ℝ) (hε: 0 < ε)
  (G_central_trivial: ∀ g: G, g ∈ Set.center G → ∃ z: ℂ, g.val.val = z • 1)
  (G'_central_trivial: ∀ g: (G' n ε G), g ∈ Set.center (G' n ε G) → ∃ z: ℂ, g.val.val.val = z • 1)
  : ∃ N: Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by

  sorry

-- Theorem 3.8
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
lemma central_implies_virtually_abelian (n: ℕ) (hn: n ≠ 0) (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG: G.FG): ∃ N: Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by
  by_cases n_eq_one: n = 1
  .
    have fin_sin_subsingleton: Subsingleton (Fin n) := by
      rw [n_eq_one]
      exact Fin.subsingleton_one
    have all_diag: ∀ h: G, h.val.val.IsDiag := by
      intro h
      apply Matrix.isDiag_of_subsingleton

    have all_comm: ∀ (a b: G), a.val.val * b.val.val = b.val.val * a.val.val := by
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
    .
      exact {
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
    . exact Subgroup.instFiniteIndexTop
  .
    have nontrivial_centrer_implies_virtual (G: Subgroup ↥(Matrix.unitaryGroup (Fin n) ℂ)) (G_FG: G.FG) (nontrivial_central: ∃ g: G, (∀ z: ℂ, g.val.val ≠ z • 1) ∧ g ∈ Set.center G): ∃ N: Subgroup G, IsMulCommutative ↥N ∧ N.FiniteIndex := by
      obtain ⟨g, g_not_multiple_I, g_central⟩ := nontrivial_central
      -- have G_subset_centralizer:  ⊆ (Subgroup.centralizer {g}).carrier := by
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

      have all_mem_central: ∀ a : G, a ∈ Subgroup.centralizer {g} := by
        intro a b b_mem
        simp at b_mem
        rw [b_mem]
        rw [Set.mem_center_iff] at g_central
        have g_comm := g_central.comm a
        exact g_comm

      obtain ⟨data⟩ := inductive_lemma n hn G g g_not_multiple_I
      -- TODO - PR this to mathlib
      have subgroup_fg: ∀ i: Fin (data.k), (data.groups i).FG := by
        intro i
        have iso := data.iso
        have centralizer_fg: (Subgroup.centralizer {g}).FG := by
          sorry
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
        .
          simp at map_prod_fg
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
              sorry
          rw [← Monoid.fg_def] at map_factor
          . exact (Monoid.fg_iff_submonoid_fg (data.groups i).toSubmonoid).mp map_factor
          . exact Monoid.fg_def.mp map_prod_fg
          .
            intro a
            use (fun j => if hij: i = j then (
              have n_i_eq: Fin (data.n_i i ) = Fin (data.n_i j) := by
                rw [hij]

              have n_i_equiv : Fin (data.n_i i) ≃ Fin (data.n_i j) := by
                rw [hij]

              let a_map := Matrix.reindex n_i_equiv n_i_equiv (α := ℂ)
              ⟨⟨a_map a, by sorry⟩, by sorry⟩
            ) else 1)
            simp [i_hom]


        obtain ⟨S, hS⟩ := centralizer_fg
        let pre_S' := Finset.image (fun s => (⟨s, all_mem_central s⟩: (Subgroup.centralizer {g}))) S
        let S' := Finset.image iso pre_S'
        let pre_target := Finset.image (fun f => f i) S'
        let target := Finset.image (Subgroup.subtype _) pre_target
        unfold Subgroup.FG
        use target
        simp [target, pre_target, S', pre_S']
        ext a





        sorry
      -- The abelian subgroup of G_i.
      let Gi' := fun i: Fin (data.k) => central_implies_virtually_abelian (data.n_i i) (data.positive_n_i i) (data.groups i) (subgroup_fg i)
      -- Page 48: Let Gᵢ := πᵢ⁻¹(πᵢ(G)′) = {g ∈ G : πᵢ(g) ∈ πᵢ(G)′}
      let inv_image : Fin (data.k) → Subgroup G := fun i: Fin (data.k) => {
        carrier := { a : G | (data.iso ⟨a, all_mem_central a⟩) i ∈ (Classical.choose (Gi' i)) },
        mul_mem' := by
          intro a b ha hb
          simp at ha
          simp at hb
          have mul_mem := Subgroup.mul_mem _ ha hb
          rw [← Pi.mul_apply] at mul_mem
          rw [← MulEquiv.map_mul] at mul_mem
          simp
          simp at mul_mem
          exact mul_mem
        one_mem' := by
          simp
          conv =>
            arg 2
            arg 2
            equals 1 => simp

          rw [MulEquiv.map_one]
          simp
          apply Subgroup.one_mem
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha
          simp only [Set.mem_setOf_eq]

          conv =>
            arg 2
            arg 2
            equals ⟨a, all_mem_central a⟩⁻¹ =>
              ext
              simp
          rw [MulEquiv.map_inv]
          rw [Pi.inv_apply]
          rw [Subgroup.inv_mem_iff]
          exact ha
      }

      -- TODO - figure out a way to make this proof less horrible (maybe somehow avoid Classical.choose)
      have inv_image_comm (a b) (ha: ∀ i, a ∈ inv_image i) (hb: ∀ i, b ∈ inv_image i): a * b = b * a := by
        simp [inv_image] at ha hb
        have symm_mul := MulEquiv.symm_apply_apply (e := data.iso) ⟨(a * b), (by
          apply Subgroup.mul_mem
          . apply all_mem_central
          . apply all_mem_central
        )⟩
        have symm_mul_swap := MulEquiv.symm_apply_apply (e := data.iso) ⟨(b * a), (by
          apply Subgroup.mul_mem
          . apply all_mem_central
          . apply all_mem_central
        )⟩
        rw [Subtype.ext_iff] at symm_mul
        simp only [] at symm_mul
        rw [Subtype.ext_iff] at symm_mul_swap
        simp only [] at symm_mul_swap
        rw [← symm_mul]
        rw [← symm_mul_swap]
        rw [← Subtype.ext_iff]
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
            simp only [MulMemClass.mk_mul_mk, inv_image]

        conv =>
          rhs
          arg 2
          equals ⟨b, all_mem_central b⟩ * ⟨a, all_mem_central a⟩ =>
            simp only [MulMemClass.mk_mul_mk, inv_image]



        rw [MulEquiv.map_mul]
        rw [MulEquiv.map_mul]
        simp
        rw [a_b_comm]
      let G' := ⨅ (i : Fin (data.k)), inv_image i

      have G'_comm: ∀ a b: G', a * b = b * a := by
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

      have inv_image_finite_index: ∀ i: Fin (data.k), (inv_image i).FiniteIndex := by
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
        rw [← QuotientGroup.out_eq' (a := x)]
        rw [← QuotientGroup.out_eq' (a := y)]
        rw [QuotientGroup.eq]
        simp [inv_image]

        rw [QuotientGroup.eq] at hxy
        conv at hxy =>
          arg 2
          lhs
          equals (data.iso ⟨x.out, all_mem_central _⟩)⁻¹ i =>
            simp
        rw [← MulEquiv.map_inv] at hxy
        rw [← Pi.mul_apply] at hxy
        rw [← MulEquiv.map_mul] at hxy
        exact hxy




        --simp [inv_image]
        -- Subgroup.finiteIndex_iff_finite_quotient
        --apply Subgroup.finiteIndex_of_leftCoset_cover_const
        --sorry



      let G' := ⨅ (i : (Fin (data.k))), inv_image i
      have G'_abeliean: IsMulCommutative G' := by
        exact {
          is_comm := by
            exact {
              comm := by
                exact G'_comm
            }
        }

      have G'_finite_index: G'.FiniteIndex := by
        apply Subgroup.finiteIndex_iInf
        apply inv_image_finite_index

      --unfold UnitaryProd at centralizer_iso
      use G'
    by_cases nontrivial_central: ∃ g: G, (∀ z: ℂ, g.val.val ≠ z • 1) ∧ g ∈ Set.center G
    . exact nontrivial_centrer_implies_virtual G G_FG nontrivial_central
    .
      -- Case two - we have no non-trivial central elements
      simp only [ne_eq, exists_and_left, not_exists, not_and] at nontrivial_central
      let ε: ℝ := 2
      have hε : 0 < ε := by
        simp [ε]

      obtain ⟨C, G_eps⟩:= volume_packing n (by omega) ε hε
      specialize G_eps G


      by_cases G'_nontrivial_central: ∃ g: (G' n ε G), (∀ z: ℂ, g.val.val.val ≠ z • 1) ∧ g ∈ Set.center (G' n ε G)
      .
        have G'_virtual := nontrivial_centrer_implies_virtual (Subgroup.map G.subtype (G' n ε G)) (by
          have G'_finite := G_eps.1
          have G_FG_other: Group.FG G := by
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
          . intro z
            simp
            have g_prop := hg.1 z
            simpa using g_prop
          .
            have g_mem := hg.2
            rw [Set.mem_center_iff]
            rw [Set.mem_center_iff] at g_mem
            exact {
              comm := by
                -- TODO - make this less horrible
                intro a
                have a_prop := a.property
                rw [Subgroup.mem_map] at a_prop
                obtain ⟨b, b_mem, b_map⟩ := a_prop
                have foo := g_mem.comm ⟨b, b_mem⟩
                rw [Subtype.ext_iff] at foo
                rw [Subtype.ext_iff] at foo
                simp at foo
                rw [Subtype.ext_iff]
                rw [Subtype.ext_iff] at foo
                simp at foo
                simp
                rw [← b_map]
                rw [Subtype.ext_iff]
                simp
                exact foo
              left_assoc := by
                intro b c
                group
              mid_assoc := by
                intro a b
                group
              right_assoc := by
                intro a b
                group
            }
        )
        -- We view G' as a subgroup of the unitary group
        --have G'_virtual := central_implies_virtually_abelian n hn (Subgroup.map G.subtype (G' n ε G))
        obtain ⟨N, N_comm, N_finite_index⟩ := G'_virtual

        have G'_iso := Subgroup.equivMapOfInjective (G' n ε G) G.subtype (by simp)
        let G'_hom := G'_iso.symm.toMonoidHom
        let other := Subgroup.map G'_hom N
        let latest := Subgroup.map (Subgroup.subtype _) other
        use latest
        refine ⟨?_, ?_⟩
        . simp [latest, other, G'_hom]
          apply Subgroup.map_isMulCommutative
        . simp [latest, other, G'_hom]
          rw [Subgroup.finiteIndex_iff]
          rw [ Subgroup.index_map]
          simp
          rw [Subgroup.finiteIndex_iff] at N_finite_index
          rw [Subgroup.finiteIndex_iff] at G_eps
          refine ⟨N_finite_index, G_eps.1⟩


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
      .
        have target := central_trivial_virtually_abelian n hn G G_FG ε hε ?_ ?_
        . exact target
        .
          intro g hg
          specialize nontrivial_central g
          rw [← not_imp_not] at nontrivial_central
          simp at nontrivial_central
          exact nontrivial_central hg
        . intro g hg
          simp only [ne_eq, exists_and_left, not_exists,
            not_and] at G'_nontrivial_central
          specialize G'_nontrivial_central g
          rw [← not_imp_not] at G'_nontrivial_central
          simp at G'_nontrivial_central
          exact G'_nontrivial_central hg
termination_by (n, G.index)
decreasing_by
  . apply Prod.Lex.left
    exact data.n_i_lt i
