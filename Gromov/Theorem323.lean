import Mathlib
import Mathlib.Algebra.Group.Gromov.Defs
import Mathlib.Algebra.Group.Gromov.TendstoTactic

set_option linter.style.cdot false
set_option linter.style.whitespace false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

--variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V] (hV : Even (Module.finrank V))  [V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]

noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)
noncomputable def Q_R_lin (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R (fun g => u.val g) (fun g => v.val g)
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}

open scoped Topology


-- These definitions go outside, since we need to explicitly vary the V that we pass in for the theorem statement
noncomputable def V_basis (V: Submodule ℝ LipschitzH) := Module.Basis.ofVectorSpace ℝ V
noncomputable def Q_R_matrix (V: Submodule ℝ LipschitzH) (R: ℝ) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)] := ((Q_R_lin V R).toMatrix₂ (V_basis V) (V_basis V))
noncomputable def my_expr (V: Submodule ℝ LipschitzH) (d: ℝ) (R : ℕ) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)] := #(S ^ R) * ((Q_R_matrix V R).det ^ ((1 : ℝ) / Module.finrank ℝ V)) / (R ^ d)
-- This is a liminf < ∞ in Vikman, but we can actually prove that it goes to 0, which makes things much easier to work with
noncomputable def growth_bound (V: Submodule ℝ LipschitzH) (d: ℝ) [finite_V : FiniteDimensional ℝ V] [decidable_V : DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]  := Filter.Tendsto (fun (R: ℕ) => my_expr V d R) (Filter.atTop) ((𝓝[>] 0))

lemma Q_R_lin_symm (V: Submodule ℝ LipschitzH) (R: ℝ): (Q_R_lin V R).IsSymm := {
  eq := by
    intro u v
    simp [Q_R_lin, Q_R]
    simp_rw [mul_comm]
}

lemma Q_R_lin_hermetian (V: Submodule ℝ LipschitzH) (R: ℝ) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]: (Q_R_matrix V R).IsHermitian := by
  rw [Q_R_matrix, ← LinearMap.isSymm_iff_isHermitian_toMatrix]
  apply Q_R_lin_symm


lemma v_r_all_nonzero (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V]: ∃ R: ℝ, ∀ u ∈ V, u ≠ 0 → ∃ g ∈ Metric.closedBall 1 R, u g ≠ 0 := by
  let zero_ball (n: ℕ): Submodule ℝ V := {
      carrier := {v: V | ∀ g ∈ Metric.closedBall 1 n, v.val g = 0}
      add_mem' := by
        intro a b ha hb
        simp at ha hb
        simp
        grind
      zero_mem' := by
        simp
      smul_mem' := by
        intro c x hx
        simp at hx
        simp
        intro g hg
        grind
  }

  let f: ℕ →o (Submodule ℝ V)ᵒᵈ := {
    toFun := zero_ball
    monotone' := by
      intro a b hab x hx
      simp [zero_ball] at hx
      simp [zero_ball]
      intro g hg
      apply hx g
      grw [hab] at hg
      exact hg
  }
  have artintian: IsArtinian ℝ V := by infer_instance
  rw [← monotone_stabilizes_iff_artinian] at artintian
  specialize artintian f
  obtain ⟨n, hn⟩ := artintian

  have inter_zero: ⨅ n: ℕ, zero_ball n = 0 := by
    ext a
    simp only [Submodule.mem_iInf, Submodule.zero_eq_bot, Submodule.mem_bot]
    refine ⟨?_, ?_⟩
    .
      intro hi
      ext g
      specialize hi (WordNorm g)
      simp [zero_ball] at hi
      specialize hi g
      simp [dist, WordDist_one] at hi
      simp [hi]
    . intro hi
      simp [hi]

  rw [← Antitone.iInf_nat_add (k := n)] at inter_zero
  .
    conv at inter_zero =>
      lhs
      arg 1
      intro k
      equals zero_ball n =>
        specialize hn (k + n) (by simp)
        simp [f] at hn
        exact hn.symm

    simp at inter_zero
    simp [zero_ball] at inter_zero
    use n
    intro u hu
    rw [Set.ext_iff] at inter_zero
    specialize inter_zero ⟨u, hu⟩
    simp at inter_zero
    intro u_ne_zero
    simp [u_ne_zero] at inter_zero
    simp
    exact inter_zero
  . intro a b hab
    simp [zero_ball]
    intro u hu hg
    intro g g_dist
    specialize hg g
    grw [hab] at g_dist
    specialize hg g_dist
    exact hg



noncomputable def R'_ (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V] : ℝ := (v_r_all_nonzero V).choose


lemma Q_R_matrix_pos_def (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)] (R: ℝ) (hR: (R'_ V) ≤ R): (Q_R_matrix V R).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Q_R_lin_hermetian V _)
  intro x hx
  simp [Q_R_matrix]
  conv =>
    rhs
    lhs
    equals (star x) => simp
  rw [star_dotProduct_toMatrix₂_mulVec]
  simp only [Q_R_lin, Q_R, DFunLike.coe]
  rw [Finset.sum_pos_iff_of_nonneg]
  .
    by_contra!
    simp_rw [← pow_two] at this
    simp only [sq_nonpos_iff] at this

    have foo := (v_r_all_nonzero V).choose_spec ((V_basis V).equivFun.symm x) (by apply Submodule.coe_mem) ?_
    .
      obtain ⟨g, g_mem, x_g_nonzero⟩ := foo
      specialize this g ?_
      .
        simp
        unfold R'_ at hR
        grw [hR] at g_mem
        simpa using g_mem
      . simp at this
        simp at x_g_nonzero
        contradiction
    .
      conv =>
        rhs
        equals (0: V) =>
          simp

      rw [ne_eq, ← Subtype.ext_iff]
      rw [← ne_eq]
      rw [LinearEquiv.map_ne_zero_iff]
      exact hx
  . intro y hy
    rw [← pow_two]
    positivity

#print sorries Q_R_matrix_pos_def

-- Everything in this section freely references fields from V_Wrapper
section V_Wrapper_Section

class V_Wrapper where
  V: Submodule ℝ LipschitzH
  V_finite: FiniteDimensional ℝ V
  V_nontrivial: Nontrivial V
  V_even: Even (Module.finrank ℝ V)
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ V)

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

local instance v_finite_dim_inst: FiniteDimensional ℝ V := v_wrapper_inst.V_finite
local instance v_nontrivial_inst: Nontrivial V := v_wrapper_inst.V_nontrivial
local instance V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ V) := v_wrapper_inst.V_decidable

private noncomputable def R' := R'_ V


-- Todo - is the better way to declare theorem_3_23 so that the constant is not allowed to depend on V?
-- TODO - can this somehow be merged with V_wrapper?
structure V_Data where
  V: Submodule ℝ LipschitzH
  hV: FiniteDimensional ℝ V
  (V_even : Even (Module.finrank ℝ V))
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)


noncomputable def Q_R_single (R : ℝ) (u: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g)^2

lemma Q_R_single_eq (R: ℝ) (u : G → ℝ): Q_R_single R u = Q_R R u u := by
  unfold Q_R_single Q_R
  simp_rw [pow_two]





-- Finding good scales:

private noncomputable def dim (V: Type*) [AddCommMonoid V] [Module ℝ V] : ℝ := Module.finrank ℝ V

private noncomputable def i₀ : ℕ := Nat.clog 16 ⌈R'⌉₊

lemma Q_R_matrix_pos_def_i₀ (R: ℝ) (hR: 16 ^ (i₀) ≤ R): (Q_R_matrix V R).PosDef := by
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

private noncomputable def f (R: ℕ): ℝ := #(S ^ R) * (Q_R_matrix V R).det ^ (dim V)⁻¹
private noncomputable def h (i: ℕ): ℝ := Real.log (f (16 ^ i))

lemma growth_implies_lim_h (d: ℕ) (h_growth: growth_bound V d): Filter.Tendsto (fun (i: ℕ) => (h i - d * i * Real.log 16)) Filter.atTop Filter.atBot := by
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
        have det_pos := (Q_R_matrix_pos_def_i₀ (16 ^ (x + i₀)) (by
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

structure Lemma3_24_data (d: ℕ) where
  i_1 : ℕ
  i_2 : ℕ
  w: ℕ
  i_1_ge: i₀ ≤ i_1
  i_2_ge: i₀ ≤ i_2
  i_diff_mem: i_2 - i_1 ∈ Set.Ioo w (3 * w)
  h_diff_lt_w: h (i_2 + 1) - h i_1 < w * (a d)
  first_h_i: h (i_1 + 1) - h i_1 < (a d)
  second_h_i : h (i_2 + 1) - h i_2 < (a d)

lemma exists_j_0_for_h (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound V d): ∃ j_0: ℕ, h (i₀ + 3 * w * (j_0 + 1)) - h (i₀ + 3 * w * j_0) < w * (a d) := by
  by_contra!

  have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h (i₀ + 3 * w * n)) (m := 0) (n := N) (by simp)
  simp_rw [eq_comm, sub_eq_iff_eq_add] at h_sum

  have h_gt (N: ℕ): h (i₀ + (3 * w * N)) ≥ 4 * d * w * N * (Real.log 16) + h i₀ := by
    rw [h_sum]
    grw [← Finset.card_nsmul_le_sum (n := w * (a d))]
    .
      simp
      simp [a]
      grind
    . intro n hn
      apply this

  have h_diff_ge (N: ℕ): h (i₀ + (3 * w * N)) - d * (i₀ + 3 * w * N) * Real.log 16 ≥ d * (w * N - i₀) * (Real.log 16) + h i₀ := by
    grw [h_gt]
    simp
    grind

  have rhs_diverges: Filter.Tendsto (fun N => d * (w * N - i₀) * (Real.log 16) + h i₀) Filter.atTop Filter.atTop := by
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
    have le_max: negative_start ≤ max ⌈positive_start⌉₊ negative_start := by
      simp
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


end V_Wrapper_Section

lemma theorem_3_23 (d: ℝ): ∃ C: ℕ, ∀ data: V_Data, (growth_bound data.V d (finite_V := data.hV) (decidable_V := data.V_decidable)) → (Module.finrank ℝ data.V) < C := by
  have C: ℕ := sorry
  use C
  intro data h_growth


  sorry
