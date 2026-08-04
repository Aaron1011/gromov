import Mathlib
import Gromov.Harmonic.LaplaceLinear

/-!
# Self-adjointness and the spectrum of the Laplacian

`laplace_self_adjoint`, `laplace_positive_semidefinite`, and that `0` lies in the spectrum of
`Δ`.
-/

set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

lemma laplace_smul (k: ℝ) (f: (Lp ℝ 2 volume (α := G))): Laplace (k • f) = k • (Laplace f) := by
  simp [Laplace, conv_mu_lp2]
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
  simp_rw [conv_smul]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [smul_sub]


lemma norm_conv_mu_le  (f: (Lp ℝ 2 volume (α := G))): ‖conv_mu_lp2 f‖ ≤ ‖f‖ := by
  simp [conv_mu_lp2]
  simp [f_conv_mu]
  simp_rw [← smul_eq_mul]
  rw [← Pi.smul_def]
  rw [MeasureTheory.eLpNorm_const_smul]
  -- TODO - deduplicate this with 'laplace_bounded'
  conv =>
    lhs
    rhs
    rhs
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  have card_s_ne: (#S : ℝ) ≠ 0 := by
    simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

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
  . simp
    field_simp
    rfl
  .
    apply WithTop.mul_ne_top
    .
      rw [Real.enorm_of_nonneg (by simp)]
      apply ENNReal.ofReal_ne_top
    .
      apply ENNReal.sum_ne_top.mpr
      intro s hs
      rw [← Function.comp_def]
      conv =>
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
      rw [← lt_top_iff_ne_top]
      apply (MeasureTheory.Lp.memLp f).2
  . intro s hs
    apply AEStronglyMeasurable.of_discrete
  .
    simp

open scoped RealInnerProductSpace
lemma inner_laplace_zero (f: (Lp ℝ 2 volume (α := G))) (hf: ⟪Laplace f, f⟫ = 0): Laplace f = 0 := by
  have inner_le := real_inner_le_norm (conv_mu_lp2 f) f

  by_cases norm_f_zero: ‖f‖ = 0
  .
    simp at norm_f_zero
    simp [Laplace, conv_mu_lp2]
    simp [f_conv_mu]
    simp_rw [norm_f_zero]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    simp
    simp_rw [← Pi.zero_def]
    rw [MeasureTheory.MemLp.toLp_zero]

  simp [Laplace] at hf
  rw [inner_sub_left] at hf
  rw [real_inner_self_eq_norm_sq] at hf
  rw [sub_eq_zero] at hf
  rw [eq_comm] at hf
  rw [pow_two] at hf
  rw [hf] at inner_le
  nth_rw 2 [mul_comm] at inner_le
  rw [mul_le_mul_iff_of_pos_left] at inner_le
  have conv_le_f := norm_conv_mu_le f
  have f_norm_eq: ‖f‖ = ‖conv_mu_lp2 f‖ := by
    linarith

  have f_sub_norm := norm_sub_sq_real f (conv_mu_lp2 f)
  rw [real_inner_comm] at f_sub_norm
  rw [hf] at f_sub_norm
  rw [← f_norm_eq] at f_sub_norm
  rw [← pow_two] at f_sub_norm
  group at f_sub_norm
  rw [zpow_two] at f_sub_norm
  rw [mul_self_eq_zero] at f_sub_norm
  simp at f_sub_norm
  simpa [Laplace] using f_sub_norm
  simpa using norm_f_zero


lemma F_n_norm_eq_one: ∀ n, MeasureTheory.eLpNorm (F_n n) 2 MeasureTheory.volume (α := G) = 1 := by
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add]
  simp [F_n, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow]

  intro n
  simp [f_n_nonneg]
  have norm_one := f_n_norm_one (n)
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add] at norm_one
  simp_rw [Real.enorm_eq_ofReal_abs] at norm_one
  simp [f_n_nonneg, abs_of_nonneg] at norm_one
  simp [norm_one]


lemma harmonic_abs_max_implies_const (f: G → ℝ) (hf: Laplace_b  f = 0) (a: G) (h_max: ∀ g: G, |f g| ≤ |f a|): f = fun _ => f a := by
  by_cases f_a_pos: 0 ≤ f a
  .
    have lt_f_a: ∀ g: G, f g ≤ f a := by
      intro g
      by_cases f_g_pos: 0 ≤ f g
      . specialize h_max g
        rw [abs_eq_self.mpr ?_] at h_max
        rw [abs_eq_self.mpr f_a_pos] at h_max
        . exact h_max
        . exact f_g_pos
      . linarith
    exact harmonic_maximum_implies_const f hf a lt_f_a
  .
    have f_neg_le: ∀ g, (-f) g ≤ (-f) a := by
      intro g
      simp at f_a_pos
      simp
      specialize h_max g
      rw [abs_of_neg f_a_pos] at h_max
      by_cases f_g_pos: 0 ≤ f g
      . rw [abs_of_nonneg f_g_pos] at h_max
        linarith
      . simp at f_g_pos
        rw [abs_of_neg f_g_pos] at h_max
        linarith
    have neg_const := harmonic_maximum_implies_const (-f) ?_ a f_neg_le
    .
      apply_fun (fun h => -h) at neg_const
      simp at neg_const
      rw [Pi.neg_def] at neg_const
      simpa using neg_const
    .
      simp_rw [Laplace_b]
      simp_rw [Laplace_b] at hf
      conv =>
        lhs
        rhs
        arg 1
        equals (-1 : ℝ) • f =>
          simp
      rw [conv_smul]
      simp
      rw [add_comm]
      rw [← sub_eq_add_neg]
      rw [sub_eq_zero]
      rw [sub_eq_zero] at hf
      exact hf.symm


set_option maxHeartbeats 500000 in
lemma laplace_zero_iff_zero (g: (Lp ℝ 2 volume (α := G))) (eq_zero: Laplace g = 0): g = 0 := by
  by_cases g_has_maximum: ∃ a: G, ∀ b: G, ‖g b‖ ≤ ‖g a‖
  .
    obtain ⟨a, ha⟩ := g_has_maximum
    have laplace_b_zero: Laplace_b  g = 0 := by
      simp [Laplace, conv_mu_lp2, f_conv_mu] at eq_zero
      simp_rw [Laplace_b, f_conv_mu]
      apply_fun (fun f => f.val.cast) at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at eq_zero
      field_simp at eq_zero
      field_simp
      exact eq_zero

    simp [Laplace_b] at laplace_b_zero
    simp [f_conv_mu] at laplace_b_zero
    rw [sub_eq_zero] at laplace_b_zero

    have g_const := harmonic_abs_max_implies_const g (by
      simp [Laplace_b]
      simp [f_conv_mu]
      nth_rw 1 [laplace_b_zero]
      simp
    ) a (by simpa using ha)
    have new_g_const_zero := MeasureTheory.memLp_const_iff_enorm (p := 2) (by simp) (by simp) (c := g a) (μ := volume (α := G)) (by simp)
    rw [← g_const] at new_g_const_zero
    simp [MeasureTheory.Lp.memLp] at new_g_const_zero
    simp [volume, my_haar_eq_count] at new_g_const_zero
    have g_infinity := hGS.g_infinite
    rw [← not_infinite_iff_finite] at new_g_const_zero
    simp [hGS.g_infinite] at new_g_const_zero


    have g_eq_zero: g.val.cast = 0 := by
      rw [g_const]
      rw [new_g_const_zero]
      ext a
      simp

    ext
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    exact g_eq_zero
  . rename _ => g_no_maximum
    simp at g_no_maximum
    have integrable_g := MeasureTheory.MemLp.integrable_sq (MeasureTheory.Lp.memLp g)
    simp [Integrable, HasFiniteIntegral] at integrable_g
    obtain ⟨_, integral_lt⟩ := integrable_g
    rw [lintegral_g_eq_add] at integral_lt
    rw [lt_top_iff_ne_top] at integral_lt
    by_contra g_ne_zero
    simp at g_ne_zero
    have nonzero_val: ∃ a: G, g a ≠ 0 := by
      rw [MeasureTheory.Lp.ext_iff] at g_ne_zero
      rw [ae_eq_everywhere] at g_ne_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at g_ne_zero
      exact Function.ne_iff.mp g_ne_zero

    obtain ⟨a, ha⟩ := nonzero_val
    have finite_gt := ENNReal.finite_const_le_of_tsum_ne_top integral_lt (ε := ‖|g a|‖ₑ ^ 2) (by
      simpa using ha
    )
    have maximal := Set.Finite.exists_maximalFor (f := fun h => |g h|) _ finite_gt (by
      apply Set.nonempty_of_mem (x := a)
      simp
    )
    obtain ⟨m, m_in_g, hm⟩ := maximal
    simp at m_in_g
    -- Obtain an element greater than the maximum
    obtain ⟨p, hp⟩ := g_no_maximum m
    have p_gt := hm (j := p) ?_ ?_
    .
      have not_g_le := not_lt_of_ge p_gt
      contradiction
    .
      simp
      grw [m_in_g]
      rw [← ENNReal.toReal_le_toReal]
      .
        simp
        rw [sq_le_sq]
        linarith
      . simp
      . simp
    linarith


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

lemma tolp_apply (f: G → ℝ) {p: ENNReal}  (hf: MeasureTheory.MemLp f p) (g: G): (MeasureTheory.MemLp.toLp f hf) g = f g := by
  have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
  rw [ae_eq_everywhere] at eq_fun
  nth_rw 2 [← eq_fun]
  rfl


open scoped RealInnerProductSpace
lemma laplace_self_adjoint (f h: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): ⟪f, (Laplace  h)⟫ = ⟪(Laplace  f), h⟫ := by

  simp [MeasureTheory.L2.inner_def]



  -- MeasureTheory.Lp.coeFn_smul

  conv =>
    lhs
    arg 2
    intro g
    rw [mul_comm]
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    simp
    rw [mul_sub]
    rhs
    equals (f g • (conv_mu_lp2 h)) g =>
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
      simp

  conv =>
    lhs
    arg 2
    intro g
    rhs
    unfold conv_mu_lp2
    rw [← MeasureTheory.MemLp.toLp_const_smul]

  simp_rw [f_conv_mu]
  simp_rw [Pi.smul_def]
  simp
  simp_rw [← mul_assoc]
  simp_rw [mul_comm]
  simp_rw [mul_assoc]
  simp_rw [Finset.mul_sum]


  conv =>
    lhs
    arg 2
    intro g
    rhs
    arg 1
    rhs
    arg 1
    intro i


  simp_rw [tolp_apply]
  rw [integral_sub]
  rw [MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.integral_mul_left_eq_self (g := s⁻¹)]
    simp
  rw [← MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro g
    rw [← Finset.mul_sum]
    rw [Finset.sum_bijective (s := S) (t := S) (e := fun s => s⁻¹) (g := fun i => (f (i * g) * (h g))) (by
      refine ⟨?_, ?_⟩
      . exact inv_injective
      . exact inv_surjective
    ) (by
      intro a
      refine ⟨?_, ?_⟩
      . apply hGS.has_inv a
      . simpa using (hGS.has_inv a⁻¹)
    ) (by
      simp
    )]

  simp_rw [Finset.mul_sum]
  rw [← integral_sub]
  simp_rw [← mul_assoc]
  simp_rw [← Finset.sum_mul]
  simp_rw [mul_comm]
  conv =>
    lhs
    arg 2
    intro a
    rw [mul_comm]
    rw [← mul_sub]


  conv =>
    rhs
    arg 2
    intro g
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    unfold conv_mu_lp2
    simp [f_conv_mu]
    rw [tolp_apply]


  simp_rw [Finset.mul_sum]
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s⁻¹ * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s⁻¹
    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1


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


  -- We've now packed everything back up in an inner product -
  -- we no longer need to deal with commuting toLp and Finset.sum


  let conv_f_delta_lp (i: G) :=  MemLp.toLp (Conv (f) (delta i⁻¹)) (μ := volume) (p := 2) (by
    simp_rw [f_conv_delta_helper]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume _
  )


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


noncomputable def Δ := Laplace_linear.mkContinuous _ (laplace_bounded')

lemma Δ_symmetric: Δ.IsSymmetric := by
  unfold LinearMap.IsSymmetric
  intro x hx
  unfold Δ
  -- TODO - why doesn't this fire automatically?
  simp [LinearMap.mkContinuous]
  simp [Laplace_linear]
  rw [laplace_self_adjoint]

lemma Δ_spectrum_subset: spectrum ℝ Δ ⊆ Set.Icc 0 2 := by
  intro a ha
  have restricts := ContinuousLinearMap.IsPositive.spectrumRestricts (f := Δ) (by
    rw [ContinuousLinearMap.isPositive_def]
    refine ⟨?_, ?_⟩
    .
      apply Δ_symmetric
    .
      intro x
      simp [ContinuousLinearMap.reApplyInnerSelf_apply]
      unfold Δ
      simp [LinearMap.mkContinuous]
      simp [Laplace_linear]
      rw [← laplace_self_adjoint]
      apply laplace_positive_semidefinite
  )
  simp
  have a_nonneg: 0 ≤ a := by
    have zero_eq: (0: ℝ) = (0: NNReal) := by
      simp
    rw [zero_eq]
    apply (SpectrumRestricts.nnreal_le_iff restricts).mp
    . simp
    . exact ha


  refine ⟨?_, ?_⟩
  .
    exact a_nonneg
  .
    have norm_le: ‖a‖ ≤ ‖(2: ℝ)‖ := by
      have foo := spectrum.norm_le_norm_mul_of_mem ha

      simp at foo
      simp [Δ] at foo
      grw [← (ContinuousLinearMap.opNorm_le_iff (M := ‖2‖) (f := Δ) ?_).mpr]
      .
        have h := spectrum.norm_le_norm_mul_of_mem ha
        rw [ContinuousLinearMap.one_def] at h
        grw [ContinuousLinearMap.norm_id_le] at h
        simpa using h
      . intro x
        simp [Δ, LinearMap.mkContinuous, Laplace_linear]
        have bound := laplace_bounded x
        simp [enorm] at bound
        norm_cast at bound
      . simp

    simp at norm_le
    rw [abs_of_nonneg] at norm_le
    . exact norm_le
    . exact a_nonneg


lemma laplace_spectrum_contains_zero (f_n_limit: f_n_conv_delta_tendsto): 0 ∈ spectrum ℝ Δ := by
  rw [spectrum.zero_mem_iff]
  by_contra this
  obtain ⟨f, hf⟩ := this

  have inv_bounded := ContinuousLinearMap.isBoundedLinearMap (𝕜 := ℝ) (f.inv)

  have nontrival_lp : Nontrivial ↥(Lp ℝ 2 (volume (α := G))) := by
    rw [nontrivial_iff]
    use 0
    use MemLp.toLp (Pi.single 1 1) (by
      apply Continuous.memLp_of_hasCompactSupport
      . apply continuous_of_discreteTopology
      . simp [HasCompactSupport, tsupport]
    )
    simp
    rw [MeasureTheory.Lp.ext_iff]
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    conv =>
      arg 1
      lhs
      equals 0 =>
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    by_contra!
    apply_fun (fun f => f 1) at this
    simp at this

  have norm_mul_bound := ContinuousLinearEquiv.one_le_norm_mul_norm_symm (ContinuousLinearEquiv.ofUnit f)

  have inv_norm_ge (n: ℕ) : (1 : ENNReal) / (eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G))) ≤ ENNReal.ofReal ‖f.inv‖ := by

    calc
    _ = (eLpNorm (F_n n) 2 (μ := volume (α := G))) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      rw [F_n_norm_eq_one]
    _ = (eLpNorm ((f.inv (f.val (F_n_lp2 n)))) 2) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      simp [F_n_lp2]
      simp_rw [← mul_apply_eq_comp]
      simp
      rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    _ ≤ ENNReal.ofReal ‖f.inv‖ := by
      have other := ContinuousLinearMap.ratio_le_opNorm (f := f.inv) (x := (((F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n))))
      conv at other =>
        lhs
        rw [Lp.norm_def]


      conv =>
        lhs
        arg 1
        arg 1
        rhs
        rhs
        rhs
        simp [hf, Δ, Laplace, Laplace_linear]
      simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, Laplace]
      apply_fun ENNReal.ofReal at other
      -- TODO - consider removing @[simp] from 'AddSubgroupClass.coe_sub'
      simp only [map_sub, ofReal_norm] at other
      simp only [← Units.inv_eq_val_inv]
      simp only [F_n_lp2, Laplace_b, ← hf, conv_mu_lp2]
      --simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
      by_cases norm_f_eq_zero: ‖F_n_lp2 n - conv_mu_lp2 (F_n_lp2 n)‖ = 0
      . rw [norm_eq_zero] at norm_f_eq_zero
        have foo := laplace_zero_iff_zero (F_n_lp2 n) (by
          simp [Laplace]
          exact norm_f_eq_zero
        )
        simp [F_n_lp2] at foo
        apply_fun (fun f => (f: (G → ℝ))) at foo
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at foo
        conv at foo =>
          rhs
          equals 0 =>
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
        simp [foo]
        unfold Conv
        simp
        have const_zero: (fun (x: G) => (0 : ℝ)) = 0 := by rfl
        conv =>
          pattern MemLp.toLp _ _
          equals 0 =>
            simp_rw [ae_eq_everywhere.mp (MeasureTheory.AEEqFun.coeFn_zero)]
            simp
            simp_rw [const_zero]
            simp
        simp
        simp_rw [ae_eq_everywhere.mp (MeasureTheory.AEEqFun.coeFn_zero)]
        simp
      rw [ENNReal.ofReal_div_of_pos] at other
      .
        simp only [ofReal_norm, Lp.enorm_def] at other
        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
        simp only [F_n_lp2, conv_mu_lp2] at other
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
        rw [ENNReal.ofReal_toReal] at other
        .
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
          simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
          simp at other
          simp
          simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
          exact other
        .
          rw [← ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          apply MeasureTheory.Lp.eLpNorm_ne_top
      . simpa using norm_f_eq_zero
      . exact ENNReal.ofReal_mono
  .
    rw [isBoundedLinearMap_iff] at inv_bounded
    obtain ⟨M, M_pos, le_M⟩ := inv_bounded.2

    have foo := F_n_conv_mu_lim f_n_limit
    rw [ENNReal.tendsto_atTop_zero] at foo
    obtain ⟨n, hn⟩ := foo  ((1: ENNReal) /(2 * ‖f.inv‖ₑ)) (by
      simp
      rw [ENNReal.mul_eq_top]
      simp
    )
    specialize hn n (by simp)

    rw [Lp.enorm_def] at hn
    specialize inv_norm_ge n
    simp [Laplace_b] at inv_norm_ge
    rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at hn
    simp only [F_n_lp2, conv_mu_lp2] at hn
    simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at hn
    grw [hn] at inv_norm_ge
    simp at inv_norm_ge

    have norm_nonzero :‖f.inv‖ ≠ 0 := by
      by_contra!
      simp at this

    simp [enorm] at inv_norm_ge
    norm_cast at inv_norm_ge
    rw [two_mul] at inv_norm_ge
    simp at inv_norm_ge

end GeneratesNS
