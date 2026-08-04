import Mathlib
import Gromov.QuadraticForm

/-!
# The bundled subspace `V_Wrapper` and good scales

The `V_Wrapper` class bundling the standing hypotheses on `V`, and the scale functions `f`, `h`
used to locate a scale at which the growth of `V` is almost multiplicative.
-/

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

open scoped Topology

-- Everything in this section freely references fields from V_Wrapper
section V_Wrapper_Section

/-- The standing hypotheses on the subspace `V`, bundled.

This is a `class` purely so that `open V_Wrapper` plus `variable [V_Wrapper]` below lets the whole
section talk about a single fixed `V` by name. Registering the two instance-valued projections
below means `FiniteDimensional`/`Nontrivial` for that `V` are found automatically wherever a
`V_Wrapper` is in scope — including at a call site that merely has `(data : V_Wrapper)` as an
ordinary hypothesis, which is how `theorem_3_23` quantifies over all such subspaces.
(`DecidableEq` needs no field: it follows from `LipschitzH_DecidableEq`.) -/
class V_Wrapper where
  V: Submodule ℝ LipschitzH
  V_finite: FiniteDimensional ℝ V
  V_nontrivial: Nontrivial V
  V_even: Even (Module.finrank ℝ V)

attribute [instance] V_Wrapper.V_finite V_Wrapper.V_nontrivial

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def R' := R'_ V

noncomputable def Q_R_single (R : ℝ) (u: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g)^2

omit v_wrapper_inst in
lemma Q_R_single_eq (R: ℝ) (u : G → ℝ): Q_R_single R u = Q_R R u u := by
  unfold Q_R_single Q_R
  simp_rw [pow_two]

-- Finding good scales:

noncomputable def dim (V: Type*) [AddCommMonoid V] [Module ℝ V] : ℝ := Module.finrank ℝ V

noncomputable def i₀ : ℕ := Nat.clog 16 ⌈R'⌉₊

omit [Nonempty ι] in
lemma Q_R_matrix_pos_def_i₀ (b : Module.Basis ι ℝ V) (R: ℝ) (hR: 16 ^ (i₀) ≤ R): (Q_R_matrix b R).PosDef := by
  apply Q_R_matrix_pos_def
  simp [i₀] at hR
  have foo := Nat.le_pow_clog (b := 16) (x := ⌈R'_ V⌉₊) (by simp)
  have r_ceil := Nat.le_ceil (R')
  unfold R' at r_ceil
  grw [r_ceil]
  grw [foo]
  simp
  unfold R' at hR
  grw [hR]

noncomputable def f (b : Module.Basis ι ℝ V) (R: ℕ): ℝ := #(S ^ R) * (Q_R_matrix b R).det ^ (dim V)⁻¹
noncomputable def h (b : Module.Basis ι ℝ V) (i: ℕ): ℝ := Real.log (f b (16 ^ i))

-- Matrix.le_iff

omit [Nonempty ι] in
lemma f_monotone_on (bas : Module.Basis ι ℝ V): MonotoneOn (f bas) (Set.Ici ⌈R'⌉₊) := by
  intro x hx y hy hxy
  unfold f
  grw [Finset.pow_subset_pow_right (n := y)]
  .
    rw [mul_le_mul_iff_right₀]
    .
      rw [Real.rpow_le_rpow_iff]
      .
        apply matrix_det_montone
        .
          apply Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
        .
          unfold Q_R_matrix
          rw [← map_sub]
          rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
          apply Q_R_lin_sub_pos_semi_def
          simpa using hxy
      .
        have foo := Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
        grind [foo.det_pos]
      .
        have foo := Q_R_matrix_pos_def bas y (by simp [R'] at hy; exact hy)
        grind [foo.det_pos]
      . simp [dim]
        exact Module.finrank_pos
    .
      simp
      apply Finset.Nonempty.pow
      apply S_nonempty

  . apply Real.rpow_nonneg
    have foo := Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
    grind [foo.det_pos]
  . apply hGS.one_mem
  . exact hxy

lemma h_montone_on (bas : Module.Basis ι ℝ V): MonotoneOn (h bas) (Set.Ici i₀) := by
  unfold h
  rw [← Function.comp_def]
  apply MonotoneOn.comp
  . apply Real.strictMonoOn_log.monotoneOn
  .
    rw [← Function.comp_def]
    apply MonotoneOn.comp
    . apply f_monotone_on bas
    .
      conv =>
        arg 1
        equals fun n => 16 ^ n =>
          simp
      apply (pow_right_monotone (by simp)).monotoneOn
    . intro a ha
      simp [i₀] at ha
      simp
      rw [Nat.clog_le_iff_le_pow] at ha
      .
        rify at ha
        grw [Nat.le_ceil (a := R')]
        exact ha
      . simp
  .
    intro a ha
    simp
    simp at ha
    simp [f]
    apply mul_pos
    . simp
      apply Finset.Nonempty.pow
      apply S_nonempty
    .
      apply Real.rpow_pos_of_pos
      apply (Q_R_matrix_pos_def_i₀ bas _ ?_).det_pos
      rw [pow_le_pow_iff_right₀]
      . exact ha
      . simp

lemma growth_implies_lim_h (b : Module.Basis ι ℝ V) (d: ℕ) (h_growth: growth_bound b d): Filter.Tendsto (fun (i: ℕ) => (h b i - d * i * Real.log 16)) Filter.atTop Filter.atBot := by
  unfold growth_bound my_expr at h_growth
  have pow_tendsto: Filter.Tendsto (fun n => 16 ^ n) Filter.atTop Filter.atTop := by
    apply StrictMono.tendsto_atTop
    apply pow_right_strictMono₀
    simp

  have log_tendsto := Real.tendsto_log_nhdsGT_zero
  -- Real.tendsto_log_nhdsNE_zero
  have comp_pow := Filter.Tendsto.comp h_growth pow_tendsto
  have comp_log := log_tendsto.comp comp_pow
  simp [Function.comp_def] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀] at comp_log
  conv at comp_log =>
    arg 1
    intro x
    rw [Real.log_div (by
      rw [mul_ne_zero_iff]
      refine ⟨?_, ?_⟩
      . simp
        grind [S_nonempty]
      .
        have det_pos := (Q_R_matrix_pos_def_i₀ b (16 ^ (x + i₀)) (by
          rw [add_comm]
          rw [pow_add]
          simp
          norm_cast
          apply Nat.one_le_pow
          simp
        )).det_pos

        rw [Real.rpow_ne_zero]
        . grind
        . grind
        .
          norm_cast
          rw [inv_eq_zero]
          norm_cast
          rw [← ne_eq, Nat.ne_zero_iff_zero_lt]
          apply Module.finrank_pos
    ) (by simp)]
    simp
  simp [h, f, dim]
  simp_rw [← mul_assoc] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀]
  simp
  exact comp_log

#print axioms growth_implies_lim_h

noncomputable def a (d: ℕ) := 4 * d * Real.log 16

lemma exists_j_0_for_h (b : Module.Basis ι ℝ V) (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound b d): ∃ j_0: ℕ, h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * j_0) < w * (a d) := by
  by_contra!

  have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (i₀ + 3 * w * n)) (m := 0) (n := N) (by simp)
  simp_rw [eq_comm, sub_eq_iff_eq_add] at h_sum

  have h_gt (N: ℕ): h b (i₀ + (3 * w * N)) ≥ 4 * d * w * N * (Real.log 16) + h b i₀ := by
    rw [h_sum]
    grw [← Finset.card_nsmul_le_sum (n := w * (a d))]
    .
      simp
      simp [a]
      grind
    . intro n hn
      apply this

  have h_diff_ge (N: ℕ): h b (i₀ + (3 * w * N)) - d * (i₀ + 3 * w * N) * Real.log 16 ≥ d * (w * N - i₀) * (Real.log 16) + h b i₀ := by
    grw [h_gt]
    simp
    grind

  have rhs_diverges: Filter.Tendsto (fun N => d * (w * N - i₀) * (Real.log 16) + h b i₀) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    rw [Filter.tendsto_mul_const_atTop_of_pos (by positivity)]
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    simp_rw [sub_eq_add_neg]
    apply Filter.tendsto_atTop_add_const_right
    conv =>
      arg 1
      equals fun x => w * x =>
        simp
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    apply Filter.tendsto_id

  apply growth_implies_lim_h at h_growth
  rw [Filter.tendsto_atTop_atBot] at h_growth
  rw [Filter.tendsto_atTop_atTop] at rhs_diverges

  obtain ⟨positive_start, h_positive_start⟩ := rhs_diverges 1
  obtain ⟨negative_start, h_negative_start⟩ := h_growth 0

  specialize h_positive_start (max ⌈positive_start⌉₊ negative_start) (by
    apply le_max_of_le_left
    apply Nat.le_ceil
  )
  -- TODO - why can't grind just solve this?
  specialize h_negative_start (i₀ + 3 * w * max ⌈positive_start⌉₊ negative_start) (by
    conv =>
      lhs
      equals 0 + negative_start => simp
    apply Nat.add_le_add
    . simp
    .
      conv =>
        lhs
        equals 1 * negative_start => simp
      apply Nat.mul_le_mul
      . grind
      . simp
  )

  have h_ge_one := h_diff_ge (max ⌈positive_start⌉₊ negative_start)
  norm_cast at h_ge_one
  norm_cast at h_positive_start
  grw [← h_positive_start] at h_ge_one
  grind

structure Lemma3_24_data (b : Module.Basis ι ℝ V) (d w: ℕ) where
  i_1 : ℕ
  i_2 : ℕ
  i_1_ge: i₀ ≤ i_1
  i_2_ge: i₀ ≤ i_2
  i_1_pos: 0 < i_1
  i_2_pos: 0 < i_2
  i_diff_mem: i_2 - i_1 ∈ Set.Ioo w (3 * w)
  h_diff_lt_w: h b (i_2 + 1) - h b i_1 < w * (a d)
  first_h_i: h b (i_1 + 1) - h b i_1 < (a d)
  second_h_i : h b (i_2 + 1) - h b i_2 < (a d)

lemma lemma_3_24 (b : Module.Basis ι ℝ V) (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound b d): Nonempty (Lemma3_24_data b d w) := by
  obtain ⟨j_0, h_j_0⟩ := exists_j_0_for_h b w d hw hd h_growth
  let m := i₀ + 3 * w * j_0

  have exists_i1: ∃ i_1: ℕ, i_1 ∈ Set.Ico m (m + w) ∧ h b (i_1 + 1) - h b i_1 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (m + n)) (m := 0) (n := w) (by simp)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h b (m + w) - h b (m) ≤ h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on b
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on b
        . simp [m]
        . simp [m]
        . simp [m]

    have h_le_w_a_d : h b (m  + w) - h b m ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h b (m + w) - h b m := by
      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
      . intro x hx
        apply this
        simpa using hx
    grind

  -- TODO - can this be deduplicated with exists_i1 ?
  have exists_i2: ∃ i_2: ℕ, i_2 ∈ Set.Ico (m + 2*w) (m + 3 * w) ∧ h b (i_2 + 1) - h b i_2 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (m + n)) (m := (2 * w)) (n := (3 * w)) (by grind)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h b (m + 3 * w) - h b (m + 2 * w) ≤ h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on b
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on b
        . simp [m]
        . simp [m]
          grind
        . simp [m]

    have h_le_w_a_d : h b (m  + 3 * w) - h b (m + 2 * w) ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h b (m + 3 * w) - h b (m + 2* w) := by

      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
        rw [← Nat.sub_mul]
        simp
      . intro x hx
        apply this
        simp
        simp at hx
        exact hx
    grind

  obtain ⟨i_1, h_i_1⟩ := exists_i1
  obtain ⟨i_2, h_i_2⟩ := exists_i2
  have diff_i_lt: h b (i_2 + 1) - h b i_1 < w * (a d) := by
    grw [h_montone_on b _ _ (b := i₀ + 3 * w * (j_0 + 1))]
    .
      apply LE.le.trans_lt ?_ h_j_0
      apply sub_le_sub_left
      apply h_montone_on b
      . simp
      . simp
        grind
      . grind
    . simp at h_i_2
      grind
    . simp
      simp at h_i_2
      grind
    . simp [m]

  have foo := h_i_1.1
  simp at foo
  have i_1_ge := foo.1
  simp [m] at i_1_ge
  have i_0_pos: 0 < i₀ := by
    simp [i₀]
    apply Nat.clog_pos
    . simp
    . simp [R']
      rw [Nat.lt_ceil]
      simp [R'_]
      have r_pos := R'_pos V
      exact r_pos
  apply Nonempty.intro
  exact {
    i_1 := i_1
    i_2 := i_2
    i_1_ge := by grind
    i_2_ge := by grind
    i_1_pos := by grind
    i_2_pos := by grind
    i_diff_mem := by grind
    h_diff_lt_w := diff_i_lt
    first_h_i := h_i_1.2
    second_h_i := h_i_2.2
  }

-- Controlled cover

end V_Wrapper_Section

end GeneratesNS
