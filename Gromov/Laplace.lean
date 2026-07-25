import Mathlib
import Gromov.ToMathlib.GroupTheory.CosetCover
import Gromov.ToMathlib.GroupTheory.FiniteAbelian.Basic
import Gromov.Complexification
import Gromov.Defs
import Gromov.Harmonic
import Gromov.UnitaryGromov
import Gromov.UnipotentGromov
import Gromov.NilpotentFinite
import Gromov.ToMathlib.GroupTheory.Closure
import Gromov.ToMathlib.Data.ENNReal.Basic
import Gromov.ToMathlib.Data.List.Finite
import Gromov.ToMathlib.Algebra.Group.Pointwise.Finset

/-!
# The discrete Laplacian on `Lp 2`
-/

set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open MeasureTheory

-- Proposition 3.17.1: "∆ is bounded" from Vikman
-- The paper also proves that the Laplace operator is self-adjoint as part of this step,
-- but we split it out
lemma laplace_bounded (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ₑ ≤ 2 * ‖f‖ₑ := by
  unfold Laplace
  unfold conv_mu_lp2
  simp_rw [f_conv_mu]
  grw [enorm_sub_le]
  --grw [norm_sub_le]
  --grw [norm_add_le]
  --grw [MeasureTheory.eLpNorm_sub_le]
  simp_rw [← smul_eq_mul]
  simp_rw [← Pi.smul_def]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [enorm_smul]
  --rw [MeasureTheory.eLpNorm_const_smul]
  conv =>
    lhs
    rhs
    rhs
    arg 1
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  rw [MeasureTheory.Lp.enorm_toLp]
  grw [MeasureTheory.eLpNorm_sum_le]
  simp_rw [← Function.comp_def]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
      apply MeasureTheory.AEStronglyMeasurable.of_discrete
    ) (by
    exact {
      measurable := by
        apply Measurable.of_discrete
      map_eq := by
        simp [MeasureTheory.volume]
    }
  )]
  simp
  rw [Real.enorm_of_nonneg (by simp)]
  rw [← mul_assoc]
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul]
  field_simp
  rw [div_self (by
    have foo := hS
    simp at foo
    simp
    exact Finset.nonempty_iff_ne_empty.mp foo
  )]
  simp
  rw [two_mul]
  . rw [← MeasureTheory.Lp.enorm_def]
  -- TODO - inline these in the right places
  . simp
  .
    intro i hs
    apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . norm_num
  .
    apply MeasureTheory.memLp_finsetSum
    intro s hs
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      apply MeasureTheory.Lp.memLp f
    . apply AEMeasurable.of_discrete

lemma laplace_bounded' (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ ≤ 2 * ‖f‖ := by
  have bounded := laplace_bounded f
  rw [← ofReal_norm_eq_enorm] at bounded
  rw [← ofReal_norm_eq_enorm] at bounded
  simp_rw [← ENNReal.ofReal_ofNat] at bounded
  rw [← ENNReal.ofReal_mul] at bounded
  .
    rw [ENNReal.ofReal_le_ofReal_iff] at bounded
    . exact bounded
    . simp
  . simp

open scoped RealInnerProductSpace
-- Proposition 3.17.2: "∆ is positive semidefinite" from Vikman
set_option maxHeartbeats 200000 in
lemma laplace_positive_semidefinite (f: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): 0 ≤ ⟪f, (Laplace  f)⟫ := by
  unfold Laplace
  rw [inner_sub_right]
  rw [real_inner_self_eq_norm_sq]
  rw [conv_mu_lp2]
  rw [MeasureTheory.L2.inner_def]
  simp_rw [tolp_apply]
  simp_rw [f_conv_mu]
  simp_rw [← smul_eq_mul]
  simp_rw [inner_smul_right]
  simp_rw [inner_sum]
  rw [integral_const_mul]
  rw [MeasureTheory.integral_finset_sum]

  -- I couldn't figure how to to handle 'toLp (∑ x ∈ S), so I ended up manipulating the integral to avoid dealing with it
  have comp_smul_left (i: G) := MeasureTheory.Lp.coeFn_compMeasurePreserving (g := f) (f := fun a => i * a) (μ := volume) (by
    exact measurePreserving_mul_left volume i
  )
  simp_rw [ae_eq_everywhere] at comp_smul_left
  have congr_comp (i: G) (x: G) := congrFun (comp_smul_left i) x
  simp only [Function.comp_apply] at congr_comp
  simp_rw [smul_eq_mul]
  simp_rw [← congr_comp]
  simp_rw [← MeasureTheory.L2.inner_def]

  let f_eq_coe: f = f := by rfl
  nth_rw 1 [← MeasureTheory.Lp.toLp_coeFn (f := f) (hf := Lp.memLp f)] at f_eq_coe


  conv =>
    rhs
    rhs
    rhs
    arg 2
    intro x
    rw [← f_eq_coe]
    rw [MeasureTheory.Lp.toLp_compMeasurePreserving]
    simp



    --rw [MeasureTheory.Lp.toLp_compMeasurePreserving]

  -- We've now packed everything back up in an inner product -
  -- we no longer need to deal with commuting toLp and Finset.sum


  --simp [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]

  --rw [← MeasureTheory.L2.inner_def]


  -- have comp_mul_mem_lp (i: G) (f: MeasureTheory.Lp ℝ 2 (μ := volume)): MemLp (f ∘ (fun x => i * x)) 2 (μ := volume) := by
  --   apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
  --   . apply MeasureTheory.Lp.memLp f
  --   . exact measurePreserving_mul_left volume i


  -- conv =>
  --   rhs
  --   rhs
  --   rhs
  --   arg 2
  --   equals ∑ x ∈ S, MemLp.toLp (fun i => f (i • x)) (by
  --     apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
  --     . apply MeasureTheory.Lp.memLp f
  --     . exact measurePreserving_mul_right volume x
  --   ) =>

  --     apply Lp.ext
  --     rw [ae_eq_everywhere]
  --     funext a
  --     --simp
  --     rw [tolp_apply]
  --     conv =>
  --       rhs
  --     rw [Finsupp.sum_apply'']

  --     rw [eq_comm]
  --     refine Finset.induction_on S ?_ ?_
  --     .
  --       simp only [Finset.sum_empty]
  --       rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
  --       simp
  --     .
  --       intro a s ha sum_eq
  --       rw [Finset.sum_insert ha]
  --       rw [Finset.sum_insert ha]
  --       rw [← sum_eq]
  --       rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_add _ _)]
  --       simp





  --rw [inner_smul_right]
  --rw [inner_sum]

  let conv_f_delta_lp (i: G) :=  MemLp.toLp (Conv (f) (delta i⁻¹)) (μ := volume) (p := 2) (by
    simp_rw [f_conv_delta_helper]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume _
  )


  -- conv =>
  --   rhs
  --   rhs
  --   rhs
  --   arg 2
  --   intro i
  --   rhs
  --   equals conv_f_delta_lp i =>
  --     unfold conv_f_delta_lp
  --     simp_rw [f_conv_delta_helper]
  --     simp
    -- arg 1
    -- intro i
    -- rhs
    -- equals fun x => (fun i => (MemLp.toLp _  (comp_mul_mem_lp i f)) x) i =>
    --   funext x
    --   simp
    --   rw [tolp_apply]
    --   simp

  have sum_le := Finset.sum_le_sum (g := fun i => ‖f‖ * ‖conv_f_delta_lp i‖) (f := fun i => ⟪f, conv_f_delta_lp i⟫) (s := S) (by
    intro s hs
    have foo := norm_inner_le_norm (x := f) (y := conv_f_delta_lp s) (𝕜 := ℝ)
    rw [Real.norm_eq_abs] at foo
    exact real_inner_le_norm f (conv_f_delta_lp s)
  )
  rw [← ge_iff_le]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rhs
    equals conv_f_delta_lp x =>
      apply Lp.ext
      rw [ae_eq_everywhere]
      funext g
      rw [tolp_apply]
      simp [conv_f_delta_lp]
      rw [tolp_apply]
      rw [f_conv_delta]
      simp


  calc
    _ ≥ ‖f‖ ^ 2 - 1 / ↑(#S) * ∑ i ∈ S, ‖f‖ * ‖conv_f_delta_lp i‖ := by

      apply sub_le_sub_left
      simp
      gcongr
    _ ≥ 0 := by
      unfold conv_f_delta_lp
      simp_rw [f_conv_delta_helper]
      conv =>
        lhs
        rhs
        rhs
        arg 2
        intro x
        rhs
        equals ‖f‖ =>
          simp
          rw [← Function.comp_def]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := volume)]
          . simp [norm]
          . apply MeasureTheory.AEStronglyMeasurable.of_discrete
          . exact measurePreserving_mul_left volume x
      simp
      have s_card_ne_zero: (#S : ℝ) ≠ 0 := by
        simp
        have foo := hS
        simp at foo
        exact Finset.nonempty_iff_ne_empty.mp foo

      rw [← mul_assoc]
      simp [s_card_ne_zero]
      rw [pow_two]
  .
    intro s hs
    simp

    have mem_lp_h_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp f) mem_lp_h_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1

end GeneratesNS
