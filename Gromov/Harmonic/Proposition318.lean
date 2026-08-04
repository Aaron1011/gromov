module

public import Mathlib
public import Gromov.Harmonic.SelfAdjoint

/-!
# Proposition 3.18

`proposition_3_18` and the auxiliary functions `G_n` used to produce an almost-harmonic
sequence.
-/

public section

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

open scoped RealInnerProductSpace

set_option maxHeartbeats 600000 in
lemma laplace_g_n (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto): ∃ g: (Lp ℝ 2 volume (α := G)), ‖Laplace g‖ ≤ (1 : ℝ) / n ∧ ⟪Laplace g, g⟫ = 1 := by

  let eps := ((1: ℝ) / n)^2
  -- selfAdjoint.mem_spectrum_eq_re

  let P: Polynomial ℝ := (Polynomial.X^2 - eps • Polynomial.X)

  let Δ := Laplace_linear.mkContinuous _ (laplace_bounded')

  have spec_inter: spectrum ℝ Δ ∩ Set.Ioo 0 eps ≠ ∅ := by
    by_contra!
    have zero_isolated: spectrum ℝ Δ ∩ (Set.Ico 0 eps) = {0} := by
      ext a
      simp
      refine ⟨?_, ?_⟩
      .
        intro ha
        obtain ⟨a_mem_spec, a_range⟩ := ha
        by_contra a_nonzero
        have a_mem: a ∈ Set.Ioo 0 eps := by
          grind

        have a_mem_empty: a ∈ (∅ : Set ℝ) := by
          rw [← this]
          grind

        simp at a_mem_empty
      .
        intro ha
        simp [ha]
        refine ⟨?_, by simp [eps, hn]⟩
        apply laplace_spectrum_contains_zero hf

    have zero_mem := laplace_spectrum_contains_zero hf
    rw [spectrum.mem_iff] at zero_mem
    simp at zero_mem

    let ramp: ℝ → ℝ := fun x => max 0 (min 1 (x / eps))

    have self_adjoint_cx_del: IsSelfAdjoint (Cx.mapCLM Δ) := by
      apply Cx.isSelfAdjoint_mapCLM
      apply Δ_symmetric.isSelfAdjoint


    let Q := cfc (1 - ramp) (Cx.mapCLM Δ)
    have laplace_q: (Cx.mapCLM Δ) * Q = cfc (0: ℝ → ℝ) (Cx.mapCLM Δ) := by
      unfold Q
      nth_rw 1 [← cfc_id (a := Cx.mapCLM Δ) ℝ]
      rw [← cfc_mul (hf := by exact continuousOn_id) (hg := by fun_prop)]
      apply cfc_congr
      intro x hx
      simp [ramp, max_def']
      norm_num
      split_ifs
      .
        rw [Cx.spectrum_mapCLM] at hx
        rename_i x_div
        apply Δ_spectrum_subset at hx
        simp [eps] at x_div
        have x_nonpos := nonpos_of_mul_nonpos_left x_div (by simp [hn])
        left
        simp at hx
        grind
      . simp [min_def']
        split_ifs
        .

          by_cases x_eq: x = eps
          . simp [x_eq, eps]
            field_simp
            simp
          .
            rename_i x_div_le
            rw [div_le_one₀ (by simp [eps]; positivity)] at x_div_le
            have x_lt: x < eps := by
              grind


            have x_mem_zero: x ∈ ({0} : Set ℝ) := by
              rw [← zero_isolated]
              simp
              refine ⟨?_, ?_⟩
              .
                rw [Cx.spectrum_mapCLM] at hx
                exact hx
              .
                rw [Cx.spectrum_mapCLM] at hx
                apply Δ_spectrum_subset at hx
                simp at hx
                grind

            simp at x_mem_zero
            simp [x_mem_zero]
        . simp


    simp at laplace_q
    have one_mem_q_spec: 1 ∈ spectrum ℝ Q := by
      rw [cfc_map_spectrum (hf := by fun_prop)]
      simp [ramp]
      use 0
      rw [Cx.spectrum_mapCLM]
      refine ⟨laplace_spectrum_contains_zero hf, ?_⟩
      right
      simp

    have nontrivial_cx: Nontrivial (Cx ↥(Lp ℝ 2 volume (α := G))  →L[ℂ] Cx ↥(Lp ℝ 2 volume (α := G))) := by

      use 1
      use 0
      simp
      rw [ContinuousLinearMap.ext_iff]
      simp
      let hf := (finsupp_lp_top (Pi.single 1 1) (by
        simp
      ) 2)
      rw [← my_haar_eq_count] at hf
      use (hf.toLp, 0)
      apply_fun (fun a => a.fst)
      simp
      rw [MeasureTheory.Lp.ext_iff]
      have haar_eq_volume: myHaar = volume := by
        simp [volume]
      simp_rw [haar_eq_volume]
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
      simp
      rw [funext_iff]
      simp
      use 1
      simp

    have Q_nonzero: Q ≠ 0 := by
      by_contra!
      simp [this] at one_mem_q_spec

    apply ContinuousLinearMap.exists_ne_zero at Q_nonzero
    obtain ⟨x, hx⟩ := Q_nonzero
    have laplace_q_x: (Cx.mapCLM Δ) (Q x) = 0 := by
      rw [← ContinuousLinearMap.mul_apply]
      simp [laplace_q]

    by_cases fst_nonzero: (Q x).fst ≠ 0
    .
      simp at laplace_q_x
      apply_fun (fun a => a.fst) at laplace_q_x
      simp at laplace_q_x
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at laplace_q_x
      apply laplace_zero_iff_zero at laplace_q_x
      contradiction
    .
      have snd_nonzero: (Q x).snd ≠ 0 := by
        by_contra!
        simp at fst_nonzero
        have Q_zero: (Q x) = 0 := by
          apply Cx.ext
          all_goals {
            simp
            grind
          }
        contradiction

      -- TODO - deduplicate this
      simp at laplace_q_x
      apply_fun (fun a => a.snd) at laplace_q_x
      simp at laplace_q_x
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at laplace_q_x
      apply laplace_zero_iff_zero at laplace_q_x
      contradiction


  rw [← Set.nonempty_iff_ne_empty] at spec_inter
  obtain ⟨a, ha⟩ := spec_inter


  have a_spec := Set.mem_of_mem_inter_left ha
  have a_lt := Set.mem_of_mem_inter_right ha


  have mem_spec: P.eval a ∈ spectrum ℝ (Polynomial.aeval Δ P) := by
    apply spectrum.subset_polynomial_aeval
    simp
    use a

  have p_a_neg: P.eval a < 0 := by
    simp [P]
    simp at ha
    nlinarith

  have eval_symm: (((Polynomial.aeval Δ) P)).IsSymmetric := by
    simp [P]
    apply LinearMap.IsSymmetric.sub
    . apply LinearMap.IsSymmetric.pow
      apply Δ_symmetric
    . apply LinearMap.IsSymmetric.smul
      . simp
      . apply Δ_symmetric


  have not_pos := ContinuousLinearMap.IsPositive.spectrumRestricts (f := (Polynomial.aeval Δ P)).mt ?_
  .
    simp [ContinuousLinearMap.IsPositive, eval_symm] at not_pos
    obtain ⟨x, hx, x_inner⟩ := not_pos
    simp [ContinuousLinearMap.reApplyInnerSelf, P] at x_inner
    have laplace_inner_nonzero: √⟪Laplace ⟨x, hx⟩, ⟨x, hx⟩⟫ ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      by_contra!
      --
      have nonneg := laplace_positive_semidefinite ⟨x, hx⟩
      rw [laplace_self_adjoint] at nonneg
      have foo := inner_laplace_zero ⟨x, hx⟩ (by
        grind
      )
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at x_inner
      simp [foo] at x_inner
      apply laplace_zero_iff_zero at foo
      simp [foo] at x_inner


    use ((√⟪Laplace ⟨x, hx⟩, ⟨x, hx⟩⟫)⁻¹) • ⟨x, hx⟩
    rw [inner_sub_left] at x_inner
    refine ⟨?_, ?_⟩
    .
      rw [norm_eq_sqrt_real_inner]
      simp [Δ, LinearMap.mkContinuous, Laplace_linear] at x_inner
      rw [← laplace_self_adjoint] at x_inner
      simp [inner_smul_left] at x_inner
      simp
      rw [laplace_smul]
      rw [norm_smul]
      simp
      rw [← Real.lt_sqrt] at x_inner
      . grw [x_inner]
        rw [Real.sqrt_mul]
        ring
        rw [abs_of_nonneg]
        .
          field_simp
          simp [eps]
          grind
        . simp
        . simp [eps]
      . simp

    .
      rw [laplace_smul]
      rw [inner_smul_left, inner_smul_right]
      simp
      field_simp
      rw [Real.sq_sqrt]
      rw [← laplace_self_adjoint]
      apply laplace_positive_semidefinite
  . rw [SpectrumRestricts.nnreal_iff]
    simp
    use P.eval a


  -- -- simp [P] at a_spec
  -- -- rw [spectrum.mem_iff] at a_spec
  -- -- --rw [LinearMap.isUnit_iff_ker_eq_bot] at a_spec
  -- -- rw [ContinuousLinearMap.isUnit_iff_bijective] at a_spec


  -- This whole proof is completely wrong - it needs to use the spectral theorem


#print axioms laplace_g_n


lemma measure_preserving_inv: MeasurePreserving Inv.inv ((MeasureTheory.volume (α := G))) (MeasureTheory.volume (α := G)) := {
  measurable := by
    exact measurable_inv
  map_eq := by
    simp [volume]
    simp [my_haar_eq_count]
}


lemma measure_preserving_unop_tomul: MeasurePreserving (fun (x: Additive (G)) ↦ (Additive.toMul x)) myHaarAddOpp volume := by
  apply MeasureTheory.MeasurePreserving.id


@[expose]
noncomputable def G_n (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto) := Classical.choose (laplace_g_n n hn hf)


lemma lp_summable {p: ℕ} (hp: 0 < p) (f: (Lp ℝ p volume (α := G))): Summable (fun g: G => |(f g)|^p) := by
  have f_norm := (MeasureTheory.Lp.memLp f).2
  simp [eLpNorm, eLpNorm'] at f_norm
  have not_le: ¬(p = 0) := by linarith
  simp [not_le] at f_norm
  rw [lintegral_g_eq_add] at f_norm
  rw [lt_top_iff_ne_top] at f_norm
  rw [Ne] at f_norm
  rw [ENNReal.rpow_eq_top_iff] at f_norm
  simp at f_norm
  simp [not_le] at f_norm
  simp_rw [Real.enorm_eq_ofReal_abs] at f_norm
  conv at f_norm =>
    arg 1
    lhs
    arg 1
    intro g
    rw [← ENNReal.ofReal_pow (by simp)]
  apply ENNReal.summable_toReal at f_norm
  conv at f_norm =>
    arg 1
    intro x
    rw [ENNReal.toReal_ofReal (by
      simp
    )]
  exact f_norm

lemma lp2_summable (f: (Lp ℝ 2 volume (α := G))): Summable (fun g: G => (f g)^2) := by
  conv =>
    arg 1
    intro g
    rw [← sq_abs]
  apply lp_summable (p := 2) (by simp) f


lemma summable_f_mul_translate (f: (Lp ℝ 2 volume (α := G))) (i: G): Summable (fun x => (f x) * (f (i * x))) := by
  have lp_mul := (MeasureTheory.MemLp.mul (φ := f) (f := fun x => f (i * x)) (p := 2) (q := 2) (r := 1) (μ := volume) ?_ ?_).2
  .
    simp [MemLp, eLpNorm, eLpNorm'] at lp_mul
    rw [lintegral_g_eq_add] at lp_mul
    simp [Real.enorm_eq_ofReal_abs] at lp_mul
    simp [← ENNReal.ofReal_mul] at lp_mul
    rw [lt_top_iff_ne_top] at lp_mul
    apply ENNReal.summable_toReal at lp_mul
    conv at lp_mul =>
      arg 1
      intro x
      rw [ENNReal.toReal_ofReal (by
        apply mul_nonneg
        . simp
        . simp
      )]
    apply Summable.of_abs
    simp_rw [abs_mul]
    exact lp_mul
  .
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume i
  . apply Lp.memLp f


-- Note - this is stated incorrectly in Vikman
-- The RHS should have a squared norm
set_option maxRecDepth 40000 in
lemma proposition_3_18 (f: (Lp ℝ 2 volume (α := G))): (∑' g: G, (f g) * (Laplace f) g) = ((2) * (#(S) : ℝ))⁻¹ * ∑ s ∈ S, ‖(f - (conv_finsupp_lp2 f (delta s) (by simp [delta])))‖^2 := by
  simp_rw [Laplace]
  simp_rw [conv_mu_lp2]
  simp_rw [f_conv_mu]
  conv =>
    enter [1, 1, g, 2, 1, 1, 2, 1, g, 2, 2, s]
    rw[ ← inv_inv s]
    rw [← f_conv_delta (s := s⁻¹) (f := f.val.cast)]

  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
  simp only [Pi.sub_apply]
  conv =>
    lhs
    arg 1
    intro g
    lhs
    rw [← inv_mul_cancel_left₀ (a := 2) (by simp) (f g)]


  simp_rw [mul_assoc]
  rw [Summable.tsum_mul_left]
  simp_rw [← mul_assoc]

  conv =>
    lhs
    rhs
    arg 1
    intro g
    rw [mul_sub]
  rw [Summable.tsum_sub]
  have sum_f: ∀ c: ℝ, c = (#(S) : ℝ)⁻¹ * ∑ s ∈ S, c := by
    intro g
    simp
    have card_nonneg: #(S) ≠ 0 := by
      exact Finset.card_ne_zero.mpr S_nonempty
    field_simp
  conv =>
    lhs
    rhs
    lhs
    arg 1
    intro g
    rw [mul_assoc]
    rw [← pow_two]
    rw [sum_f (c := (f g)^2)]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_mul_left]
  have f_norm := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := 2) (by simp) (by simp) (f := f.val.cast) (μ := volume (α := G))
  simp_rw [lintegral_g_eq_add] at f_norm
  simp [enorm] at f_norm
  apply_fun ENNReal.toReal at f_norm
  norm_cast at f_norm
  rw [← ENNReal.toReal_rpow] at f_norm
  rw [ENNReal.tsum_toReal_eq] at f_norm
  simp at f_norm
  apply_fun (fun x => x^2) at f_norm
  nth_rw 2 [← Real.rpow_natCast] at f_norm
  rw [← Real.rpow_mul] at f_norm
  simp at f_norm
  have f_summable := lp_summable (p := 2) (by simp) f
  conv =>
    lhs
    rhs
    lhs
    rhs
    rhs
    rw [Summable.tsum_finsetSum (by
      intro i hi
      apply lp2_summable
    )]
    rw [← f_norm]

  conv =>
    lhs
    rhs
    rhs
    arg 1
    intro b
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    rw [← mul_assoc]
    rw [mul_comm (2 * _)]
    rw [mul_assoc]
    rw [mul_assoc]
    rw [Finset.mul_sum]
    rw [← mul_assoc]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_finsetSum (by
    intro i hi
    simp [f_conv_delta]
    apply summable_f_mul_translate
  )]
  simp_rw [f_conv_delta]
  simp only [inv_inv]
  let f_conv := fun (s: G) => conv_finsupp_lp2 f (delta s) (by
    simp [delta]
  )
  have real_inner : ∀ a b : ℝ, ⟪a, b⟫ = a * b := fun a b => by rw [show (⟪a, b⟫ : ℝ) = b * a from rfl, mul_comm]
  have inner_f_conv := fun (s: G) => MeasureTheory.L2.inner_def (𝕜 := ℝ) (f := f) (g := f_conv s)
  simp [f_conv, conv_finsupp_lp2] at inner_f_conv
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at inner_f_conv
  conv at inner_f_conv =>
    intro a
    rhs
    -- TODO  - deduplicate this with the 'have lp_mul' block above
    rw [MeasureTheory.integral_countable (by
      simp [f_conv_delta]
      simp [Integrable]
      refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
      simp [HasFiniteIntegral]
      simp [Real.enorm_eq_ofReal_abs]
      rw [lintegral_g_eq_add]
      rw [lt_top_iff_ne_top]
      simp_rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul]
      rw [← ENNReal.ofReal_tsum_of_nonneg]
      . apply ENNReal.ofReal_ne_top
      . intro n
        positivity
      .
        apply Summable.abs
        simp_rw [mul_comm]
        apply summable_f_mul_translate
    )]
  simp [volume, my_haar_eq_count, f_conv_delta] at inner_f_conv
  conv =>
    lhs
    rhs
    rhs
    rhs
    arg 1
    rw [S_eq_Sinv ]

  simp only [Finset.sum_inv_index]

  simp_rw [mul_comm] at inner_f_conv
  simp_rw [← inner_f_conv]
  -- Split '2 * ‖f‖^2 into two copies of ‖f‖^2, and convert one into ‖Conv f delta‖^2
  rw [two_mul]
  conv =>
    lhs
    rhs
    lhs
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.eLpNorm_comp_measurePreserving (f := fun x => s⁻¹ * x) (ν := volume) (by apply AEStronglyMeasurable.of_discrete) (by apply measurePreserving_mul_left)]


  simp_rw [Function.comp_def]
  simp_rw [← f_conv_delta]
  have card_s_ne: #(S) ≠ 0 := by
    simp
    exact Finset.nonempty_iff_ne_empty.mp S_nonempty
  simp_rw [norm_sub_sq_real]
  simp only [MeasureTheory.Lp.norm_def]
  simp_rw [conv_finsupp_lp2]
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  eta_reduce
  ring
  . apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    apply summable_f_mul_translate
  .
    apply tsum_nonneg
    intro g
    apply sq_nonneg
  . simp
  . apply summable_sum
    intro s hs
    apply lp2_summable
  .
    apply Summable.mul_left
    apply summable_sum
    intro s hs
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    simp_rw [← pow_two]
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [← mul_assoc]
    simp_rw [Finset.mul_sum]
    apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    simp_rw [mul_comm]
    simp_rw [mul_assoc]
    apply Summable.mul_left
    apply summable_f_mul_translate
  .
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [mul_sub]
    apply Summable.sub
    . simp_rw [← pow_two]
      apply lp2_summable
    .
      simp_rw [← mul_assoc]
      simp_rw [Finset.mul_sum]
      apply summable_sum
      intro s hs
      simp_rw [f_conv_delta]
      simp_rw [mul_comm]
      simp_rw [mul_assoc]
      apply Summable.mul_left
      apply summable_f_mul_translate

lemma g_n_laplace_enorm_le (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto): ‖Laplace (G_n n hn hf)‖ₑ ≤ 1/n := by
  have g_n_prop := (laplace_g_n n hn hf).choose_spec
  rw [← ofReal_norm]
  rw [show ((1 : ENNReal)/(n : ENNReal)) = ENNReal.ofReal (1/(n:ℝ)) by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast]]
  exact ENNReal.ofReal_le_ofReal g_n_prop.1


open scoped RealInnerProductSpace in
lemma g_n_conv_norm (n: ℕ) (hn: 0 < n) (hf: f_n_conv_delta_tendsto): ⟪Laplace (G_n n hn hf), (G_n n hn hf)⟫ = 1 := by
  have g_n_prop := (laplace_g_n n hn hf).choose_spec
  exact g_n_prop.2


#print sorries proposition_3_18
#print axioms proposition_3_18


lemma g_sub_norm_gt (hf: f_n_conv_delta_tendsto) (n: ℕ) : ∃ s ∈ S, ‖(G_n (n + 1) (by simp) hf) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) hf) (delta s) (by simp [delta]))‖^2 > 1 := by
  by_contra!
  have card_le := Finset.sum_le_card_nsmul S _ (1 : ℝ) this
  have sum_norm := (proposition_3_18 (G_n (n + 1) (by simp) hf) )
  have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace (G_n (n + 1) (by simp) hf)) (G_n (n + 1) (by simp) hf) (𝕜 := ℝ) (α := G)
  have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp) hf)).2
  have real_inner : ∀ a b : ℝ, ⟪a, b⟫ = b * a := fun a b => rfl
  rw [integral_eq_eq_sum] at g_inner_laplace
  .
    simp_rw [real_inner] at g_inner_laplace
    simp_rw [← g_inner_laplace] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    rw [g_n_prop] at sum_norm
    rw [eq_inv_mul_iff_mul_eq₀] at sum_norm
    simp at sum_norm
    rw [← sum_norm] at card_le
    simp at card_le
    rw [mul_le_iff_le_one_left] at card_le
    . norm_num at card_le
    . simp
      have foo := S_nonempty
      grind
    .
      simp
      grind

  .
    rw [MeasureTheory.L2.inner_def] at g_n_prop
    apply MeasureTheory.integrable_of_integral_eq_one at g_n_prop
    exact g_n_prop


lemma g_sub_norm_single_s (hf: f_n_conv_delta_tendsto): ∃ s ∈ S, { n: ℕ | ‖(G_n (n + 1) (by simp) hf) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) hf) (delta s) (by simp [delta]))‖^2 > 1 }.Infinite := by

  have frequent := Filter.Frequently.of_forall (f := Filter.atTop) (g_sub_norm_gt hf)
  simp at frequent
  obtain ⟨s, s_mem, s_frequently⟩ := frequent
  rw [Nat.frequently_atTop_iff_infinite] at s_frequently
  use s
  refine ⟨s_mem, ?_⟩
  simpa using s_frequently


lemma lipschitzWith_mul_prod  {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C)
  (g: G) (s: List S): dist (f (s.unattach.prod * g)) (f g) ≤ C * s.length := by

  induction s with
  | nil =>
    simp
  | cons head tail ih =>
    simp
    have triangle := dist_triangle (f (head * tail.unattach.prod * g)) (f (tail.unattach.prod * g)) (f g)
    grw [triangle]
    grw [ih]
    rw [mul_assoc]
    grw [hf _ _ (by simp)]
    grind


lemma lipschitzWith_discrete {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C):
    LipschitzWith C f := by

  apply LipschitzWith.of_dist_le_mul
  intro x y

  have prod_eq := word_norm_prod (y * x⁻¹) (WordNorm (y * x⁻¹)) rfl
  obtain ⟨l, l_prod, l_len⟩ := prod_eq
  simp [ProdS] at l_prod

  have mul_prod := lipschitzWith_mul_prod f hf x l
  simp [l_prod] at mul_prod
  rw [dist_comm]
  grw [mul_prod]
  simp [dist, WordDist, l_len]


lemma conv_neg_left (f g: G → ℝ): Conv (-f) g = -(Conv f g) := by
  conv =>
    pattern -f
    equals (-1 : ℝ) • f => simp

  rw [conv_smul]
  simp

lemma laplace_b_sub (f g: G → ℝ): Laplace_b (f - g) = Laplace_b f - Laplace_b g := by
  simp [Laplace_b]
  nth_rw 3 [sub_eq_add_neg]
  rw [conv_add_left]
  .
    rw [conv_neg_left]
    ring_nf
  .
    apply conv_exists_fin_supp
    right
    apply mu_finsupp
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp


-- DO NOT REMOVE `f_n_limit` - this will be needed by the spectral theorem part of the proof

end GeneratesNS
