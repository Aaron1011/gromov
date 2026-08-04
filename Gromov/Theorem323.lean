module

public import Mathlib
public import Gromov.BoundedDoubling

/-!
# Theorem 3.23

`theorem_3_23` and the resulting finite-dimensionality of the space of Lipschitz harmonic
functions.

Root of the Theorem 3.23 hierarchy: importing it pulls in the cutoff inequality, the quadratic
form, the packing argument and the Poincaré inequality.
-/

public section

set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

set_option maxHeartbeats 2500000 in
lemma theorem_3_23 (d: ℕ) (hd: 0 < d): ∃ C: ℕ, ∀ v_data: V_Wrapper, growth_bound (V_basis v_data.V) d → (Module.finrank ℝ v_data.V) < C := by
  let w := ⌈Real.logb 16 ((16^4) * #(S) * Real.exp (4 * a (d)))⌉₊
  let C: ℕ := 1 + (⌈2 * Real.exp (w * (a d))⌉₊)
  use C
  intro v_data h_growth

  let data: GoodScalesData (V_basis v_data.V) := {
    w := ⌈Real.logb 16 ((16^4) * #(S) * Real.exp (4 * a (d)))⌉₊
    d := d
    hw := by
      simp
      apply Real.logb_pos
      . simp
      . apply one_lt_mul
        .
          have card_s: 1 ≤ #(S) := by
            simp
            apply S_nonempty
          grw [← card_s]
          simp
          norm_num
        .
          norm_num
          simp [a]
          positivity
    hd := hd
    w_gt := by
      rw [Nat.lt_ceil]
      simp
      rw [Real.lt_logb_iff_rpow_lt]
      .
        have mul_pos: 1 < ↑(#S) * Real.exp (4 * a d) := by
          apply one_lt_mul
          . simp
            apply S_nonempty
          . simp [a]
            positivity
        linarith
      . simp
      . have S_ne: #(S) ≠ 0 := by
          have foo :=  S_card_ne_zero_re
          simpa using foo
        positivity
    h_growth := h_growth
  }

  obtain ⟨U, U_sub_v, hU_dim, bounded_double⟩ := exists_bounded_doubling_subspace data

  let phi_u := (phi data).domRestrict (U.submoduleOf v_data.V)
  have phi_u_inj: Function.Injective phi_u := by
    -- `phi_u` lands in a nested linear-map type; naming `f` explicitly avoids a
    -- metavariable whose instance would need a deeper `synthPending` than the default.
    rw [← LinearMap.ker_eq_bot (f := phi_u)]
    rw [LinearMap.ker_eq_bot' (f := phi_u)]
    intro u hu

    have u_le := lemma_3_26_a data u
    simp [phi_u] at hu
    simp [hu] at u_le

    have u_bound := harmonic_r2_inequality u (by
      have u_prop := u.val.val.harmonic
      simp [Harmonic] at u_prop
      simp [Laplace_b]
      ext a
      simp
      nth_rw 1 [u_prop]
      simp [f_conv_mu]
    ) (4 * R_2 data) (by simp [R_2])
    simp [B_r] at u_le
    conv at u_bound =>
      lhs
      arg 1
      equals (Metric.closedBall 1 (8 * (R_2 data))).toFinset =>
        simp
        ring

    grw [u_bound] at u_le
    .
      have u_double := bounded_double u (by
        exact u.prop
      )
      conv at u_double =>
        lhs
        simp [Q_R]

      simp_rw [← pow_two] at u_double
      grw [Finset.sum_le_sum_of_subset_of_nonneg (t := (finite_closed_ball 1 (16 * (R_2 data))).toFinset)] at u_le
      .
        simp [finite_closed_ball] at u_le
        grw [u_double] at u_le
        .
          by_cases u_zero: u = 0
          . exact u_zero
          .
            have r_pos := R'_pos v_data.V
            have r_ratio_le: (R_1 data + 1) / (4 * R_2 data) ≤ 4 * ((16: ℝ) ^ (-(data.w : ℝ))) := by
              simp [R_1, R_2]
              field_simp
              have i_diff := (GoodScales data).i_diff_mem
              simp at i_diff
              have one_le: (1: ℝ) ≤ 2*(16^((GoodScales data).i_1)) := by
                norm_num
                apply one_le_mul_of_one_le_of_one_le
                . simp
                . rw [one_le_pow_iff_of_nonneg]
                  . simp
                  . simp
                  . simp
                    have h_i := (GoodScales data).i_1_pos
                    grind
              grw [one_le]
              rw [← mul_add]
              rw [← two_mul]
              ring
              rw [← pow_add]
              apply mul_le_mul
              .
                rw [pow_le_pow_iff_right₀]
                . grind
                . simp
              . norm_num
              . simp
              . simp

            conv at u_le =>
              rhs
              equals GeneratesNS.C * Real.exp (2 * a data.d) * (((↑(R_1 data) + 1) / ((↑(4 * R_2 data : ℝ))))^2 * ↑(#S) * (Real.exp (2 * a data.d) * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val)) =>
                ring

            grw [r_ratio_le] at u_le
            ring_nf at u_le
            .
              have le_half: Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val ≤ (2: ℝ)⁻¹ * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val := by
                have qr_nonneg : 0 ≤ Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val :=
                  Q_R_self_nonneg _ _
                have ha : (0:ℝ) ≤ a data.d := by simp only [a]; positivity
                have hE1 : (1:ℝ) ≤ Real.exp (a data.d) := Real.one_le_exp ha
                have hE4 : (1:ℝ) ≤ Real.exp (a data.d) ^ 4 := one_le_pow₀ hE1
                have hEpos : (0:ℝ) < Real.exp (a data.d) := Real.exp_pos _
                have he4 : Real.exp (4 * a data.d) = Real.exp (a data.d) ^ 4 := by
                  rw [← Real.exp_nat_mul]; norm_num
                have he2 : Real.exp (a data.d * 2) = Real.exp (a data.d) ^ 2 := by
                  rw [show a data.d * 2 = 2 * a data.d from by ring, ← Real.exp_nat_mul]; norm_num
                have he2sq : Real.exp (a data.d * 2) ^ 2 = Real.exp (a data.d) ^ 4 := by
                  rw [he2]; ring
                have hS0 : (0:ℝ) < ↑(#S) := by exact_mod_cast Finset.card_pos.mpr S_nonempty
                have hXpos : (0:ℝ) < 16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4 := by positivity
                have h16w : (16:ℝ) ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4 ≤ (16:ℝ) ^ (↑data.w : ℝ) := by
                  rw [← he4]
                  have hlog : (16:ℝ) ^ Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d))
                      = 16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d) :=
                    Real.rpow_logb (by norm_num) (by norm_num) (by rw [he4]; exact hXpos)
                  have hle : Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d)) ≤ (↑data.w : ℝ) := by
                    have hdef : data.w = ⌈Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d))⌉₊ := rfl
                    rw [hdef]; exact_mod_cast Nat.le_ceil _
                  calc 16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d)
                      = (16:ℝ) ^ Real.logb 16 (16 ^ 4 * ↑(#S) * Real.exp (4 * a data.d)) := hlog.symm
                    _ ≤ (16:ℝ) ^ (↑data.w : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
                have ht0 : (0:ℝ) ≤ (16:ℝ) ^ (-↑data.w : ℝ) := Real.rpow_nonneg (by norm_num) _
                have htX : (16:ℝ) ^ (-↑data.w : ℝ) * (16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4) ≤ 1 := by
                  calc (16:ℝ) ^ (-↑data.w : ℝ) * (16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4)
                      ≤ (16:ℝ) ^ (-↑data.w : ℝ) * (16:ℝ) ^ (↑data.w : ℝ) :=
                        mul_le_mul_of_nonneg_left h16w ht0
                    _ = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
                have hsq : ((16:ℝ) ^ (-↑data.w : ℝ) * (16 ^ 4 * ↑(#S) * Real.exp (a data.d) ^ 4)) ^ 2 ≤ 1 := by
                  nlinarith [htX, mul_nonneg ht0 (le_of_lt hXpos)]
                have hM8 : (0:ℝ) ≤ ((16:ℝ) ^ (-↑data.w : ℝ)) ^ 2 * (↑(#S)) ^ 2 * Real.exp (a data.d) ^ 4 * 16 ^ 8 := by
                  positivity
                have hP : ((16:ℝ) ^ (-↑data.w : ℝ)) ^ 2 * (↑(#S)) ^ 2 * Real.exp (a data.d) ^ 4 * 16 ^ 8 ≤ 1 := by
                  nlinarith [hsq, hE4, hM8]
                have key : GeneratesNS.C * Real.exp (a data.d * 2) ^ 2 * (16 ^ (-↑data.w : ℝ)) ^ 2 * ↑(#S)
                    * 16 ≤ 2⁻¹ := by
                  rw [he2sq]; simp only [GeneratesNS.C]
                  nlinarith [hP, hM8]
                calc Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val
                    ≤ (GeneratesNS.C * Real.exp (a data.d * 2) ^ 2 * (16 ^ (-↑data.w : ℝ)) ^ 2 * ↑(#S)
                        * 16) * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val := by nlinarith [u_le]
                  _ ≤ 2⁻¹ * Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val := by nlinarith [key, qr_nonneg]

              have Q_r_zero: Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val = 0 := by
                by_contra!
                rw [mul_comm] at le_half
                have foo := one_le_of_le_mul_left₀ (by
                  have nonneg: 0 ≤ Q_R ↑(R_2 data) ⇑u.val.val ⇑u.val.val :=
                    Q_R_self_nonneg _ _
                  grind
                ) le_half
                norm_num at foo

              rw [← Submodule.coe_eq_zero]
              by_contra hne
              exact absurd Q_r_zero (ne_of_gt (Q_R_pos_on_R' (↑u) hne _ (R'_le_R_2 data)))
            . apply mul_nonneg (by positivity)
              exact Q_R_self_nonneg _ _
            . simp [GeneratesNS.C]
              positivity

        . simp [GeneratesNS.C]
          positivity
      .
        simp [GeneratesNS.C]
        positivity
      . intro a ha
        simp
        simp at ha
        grind
      . intro i hi _
        positivity
    .
      simp [GeneratesNS.C]
      positivity

  apply LinearMap.finrank_le_finrank_of_injective at phi_u_inj
  simp at phi_u_inj
  simp [dim] at hU_dim
  norm_cast at hU_dim
  grw [hU_dim]

  conv at phi_u_inj =>
    lhs
    equals Module.finrank ℝ U =>
      exact (Submodule.submoduleOfEquivOfLe U_sub_v).finrank_eq

  grw [phi_u_inj]
  have card_eq: #(B_finite data).toFinset = #(B_finsets data) := by
    have hR1 : (0:ℝ) ≤ ↑(R_1 data) := Nat.cast_nonneg _
    have hcoe := (X_j_finite data).coe_toFinset
    have hinj1 : Set.InjOn (fun a => Metric.closedBall a (↑(R_1 data):ℝ)) (X_j data) :=
      B_ball_injective_on data (↑(R_1 data)) hR1 le_rfl
    have hinj2 : Set.InjOn (fun a => (finite_closed_ball a (R_1 data)).toFinset) (X_j data) := by
      intro a ha b hb hab
      exact hinj1 ha hb (Set.Finite.toFinset_inj.mp hab)
    have hB : (B_finite data).toFinset
        = Finset.image (fun a => Metric.closedBall a (↑(R_1 data):ℝ)) (X_j_finite data).toFinset := by
      ext s
      simp only [Set.Finite.mem_toFinset, B, Set.mem_image, Finset.mem_image, Finset.mem_coe]
    rw [hB, B_finsets, Finset.card_image_of_injOn (hinj1.mono hcoe.le),
      Finset.card_image_of_injOn (hinj2.mono hcoe.le)]
  rw [← card_eq]
  rify
  grw [card_B_le_exp_wa]
  simp [C]
  conv =>
    lhs
    equals 0 + 2 * Real.exp (↑data.w * a data.d) =>
      simp
  apply add_le_add
  . simp
  . apply Nat.le_ceil

open scoped Topology

-- TODO - do we really need the double by_contra here?
-- Theorem 3.19
set_option maxHeartbeats 2500000 in
@[expose]
instance Lipschitz_finite_dimensional: FiniteDimensional ℝ LipschitzH := by
  classical
  by_contra!
  have B := Module.Basis.ofVectorSpace ℝ LipschitzH

  have B_infinite: Infinite ((Module.Basis.ofVectorSpaceIndex ℝ LipschitzH)) := by
    by_contra fin_basis
    simp at fin_basis
    have finite_module := Module.Finite.of_basis B
    have finite_dim: FiniteDimensional ℝ LipschitzH := by
      infer_instance
    contradiction

  obtain ⟨d, hd⟩ := hGS.g_growth
  obtain ⟨C, V_bound⟩ := theorem_3_23 ((d + 3) + (d + 3)) (by simp)

  obtain ⟨fin_basis_idx, card_fin_basis_idx⟩ := B_infinite.exists_subset_card_eq _ (2 + C * 2)
  let fin_basis := Finset.image (B) fin_basis_idx
  let large_v: V_Wrapper := {
    V := Submodule.span ℝ fin_basis
    V_finite := by infer_instance
    V_even := by
      rw [finrank_span_finset_eq_card]
      .
        simp [fin_basis]
        rw [Finset.card_image_of_injective]
        . grind
        .

          exact Module.Basis.injective B
      .
        simp [fin_basis]
        apply LinearIndepOn.id_image
        exact Module.Basis.linearIndepOn B ↑fin_basis_idx
    V_nontrivial := by
      rw [nontrivial_iff]
      have one_lt: 1 < #fin_basis_idx := by
        grind
      rw [Finset.one_lt_card_iff] at one_lt
      obtain ⟨a, b, ha, hb, a_neq⟩ := one_lt
      use ⟨B a, by simp [fin_basis, ha]⟩
      use ⟨B b, by simp [fin_basis, hb]⟩
      simp
      apply (Module.Basis.injective _).ne
      exact a_neq
  }
  -- `large_v.V` does not reduce on its own inside `rw`, so name the (definitional) equation.
  have large_v_V: large_v.V = Submodule.span ℝ fin_basis := rfl
  specialize V_bound large_v ?_
  .
    simp [growth_bound, my_expr]

    norm_cast
    conv =>
      arg 1
      intro a
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [Nat.pow_add]
    push_cast
    conv =>
      arg 1
      intro a
      rw [div_mul_eq_div_mul_one_div]
      rw [mul_comm _ (1 / _)]
      rw [← mul_assoc]

    conv =>
      pattern (𝓝[>] 0)
      equals (𝓝[>] (0 * 0)) => simp

    apply Filter.TendstoNhdsWithinIoi.mul (by simp) (by simp)
    .
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      simp
      let R'' := ⌈R'_ large_v.V⌉₊
      rw [← Filter.tendsto_add_atTop_iff_nat R'']
      --  Filter.tendsto_add_atTop_iff_nat
      apply squeeze_zero_nhdsGT (g := (fun (R: ℕ) => (det_bound_const (V_basis large_v.V) * (1 + (R + R'')) ^ 2 * ((a * (R + R'')^d : ℝ))) / ((R + R'') ^ (↑d + 3) : ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro R R_pos
        have det_pos := (Q_R_matrix_pos_def (V_basis large_v.V) (R + R'') (by
          -- TODO - why is this so messy?
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ large_v.V)
          rw [add_comm]
          simp
          grind
        )).det_pos
        norm_cast at det_pos
        positivity
      .
        apply Filter.Eventually.of_forall
        intro R
        have foo := det_bound (V_basis large_v.V) (R := R + R'') (by
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ (V := large_v.V))
          rw [add_comm]
          simp
          grind
        )
        simp
        rw [one_div] at foo
        push_cast at foo
        refine le_trans (mul_le_mul_of_nonneg_right foo (by positivity)) ?_
        by_cases const_zero: det_bound_const (V_basis large_v.V) = 0
        .
          simp [const_zero]

        field_simp
        rw [mul_div_assoc]
        rw [mul_div_assoc]
        rw [mul_assoc]
        rw [mul_le_mul_iff_right₀]
        .
          by_cases r_zero: (R + R'') = 0
          .
            norm_cast
            simp [r_zero]
          .
            grw [s_growth (R + R'') (by grind)]
            norm_cast
            simp
            rw [mul_div_assoc]
        .
          have nonneg := det_bound_const_nonneg (V_basis large_v.V)
          grind
      . poly_tendsto
    .
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      apply squeeze_zero_nhdsGT (g := (fun (n: ℝ) => (a * n^d : ℝ) / (n ^ (↑d + 3))) ∘ (fun (n: ℕ) => (n: ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro n hn
        have card_nonzero: (0: ℝ) < #(S ^ n) := by
          simp
          apply Finset.Nonempty.pow
          apply S_nonempty

        norm_cast
        positivity
      .
        apply Filter.Eventually.of_forall
        intro n
        by_cases hn: n = 0
        .
          simp [hn]
        .
          grw [s_growth n (by grind)]
          norm_cast
          simp
      . poly_tendsto
  .
    rw [large_v_V, finrank_span_finset_eq_card] at V_bound
    .
      simp [fin_basis] at V_bound
      rw [Finset.card_image_of_injective] at V_bound
      .
        simp [card_fin_basis_idx] at V_bound
        grind
      . exact Module.Basis.injective B
    .
      simp [fin_basis]
      apply LinearIndepOn.id_image
      exact Module.Basis.linearIndepOn B ↑fin_basis_idx

#synth FiniteDimensional ℝ LipschitzH
#print axioms Lipschitz_finite_dimensional

end GeneratesNS
