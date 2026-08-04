module

public import Mathlib
public import Gromov.Harmonic.MuConv

/-!
# The Laplacian as a linear map on `L²`

`Laplace_linear`, the normalised functions `F_n`, and the limit `F_n_conv_mu_lim`.
-/

@[expose] public section

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

set_option maxHeartbeats 60000 in
noncomputable def nontrivial_harmonic_common (k: ℕ) (seq: ℕ → ℕ) (h_seq: Filter.Tendsto seq Filter.atTop Filter.atTop) (F: G → ℝ) (H_n: ℕ → G → ℝ) (h_conv_lipschitz: ∀ n, LipschitzWith k (Conv (H_n n) (f_n n)))
(tendsto_F: Filter.Tendsto ((fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) Filter.atTop (nhds F))
(H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1): LipschitzH := by

  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n (seq n)) (f_n (seq n)),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  let F_lipschitzh: LipschitzH := {
    toFun := (fun (g: G) => F g),
    lipschitz := by
      use k
      have closed_lipschitz := isClosed_setOf_lipschitzWith (α := G) (β := ℝ) k
      apply IsClosed.isSeqClosed at closed_lipschitz
      simp [IsSeqClosed] at closed_lipschitz
      have F_lipschitz := closed_lipschitz (p := F) (x := (fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) (by
        intro n
        apply h_conv_lipschitz
      ) tendsto_F
      exact F_lipschitz
    harmonic := by
      simp [Harmonic]
      intro g
      rw [tendsto_pi_nhds] at tendsto_F
      have lim_f_sum := tendsto_finset_sum (ι := S) (M := ℝ) (s := Finset.univ) (a := fun s => F (s.val * g)) (f := (fun (s: S) n ↦ Conv (H_n (seq n)) (f_n (seq n)) (s.val *g))) (x := Filter.atTop (α := ℕ)) ?_

      -- TODO - figure out why lean hangs without this
      have my_mul : ContinuousMul ℝ := instIsTopologicalRingReal.toContinuousMul
      have lim_f_mul_sum := Filter.Tendsto.const_mul ((#S) : ℝ)⁻¹ lim_f_sum
      .
        have lim_f_g := tendsto_F g
        have lim_f_g_sub := Filter.Tendsto.sub lim_f_g lim_f_mul_sum

        have laplace_conv_tendsto_zero: Filter.Tendsto (fun n => eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤) Filter.atTop (nhds 0) := by
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => 0) (h := fun (n: ℕ) => ENNReal.ofReal ((2: ℝ) / ((seq n) + 1) : ℝ))
          . simp
          .
            rw [← ENNReal.tendsto_toReal_iff]
            conv =>
              arg 1
              intro n
              rw [ENNReal.toReal_ofReal (by
                norm_cast
                positivity
              )]
            conv =>
              arg 1
              intro n
              rhs
              equals ((((((seq n) + 1): ℕ)) : ℕ ) : ℝ) => simp
            conv =>
              arg 1
              equals (fun (n: ℕ) => (2 : ℝ) / (n) ) ∘ (fun n => (seq n) + 1) =>
                ext n
                simp
            apply Filter.Tendsto.comp
            .
              conv =>
                arg 1
                equals (fun (n: ℕ) => (2 : ℝ) / ((n) : ℕ)) =>
                  ext n
                  simp
              apply tendsto_const_div_atTop_nhds_zero_nat
            .
              apply Filter.Tendsto.comp
              . conv =>
                  arg 1
                  equals fun n => n + 1 =>
                    simp
                apply Filter.tendsto_add_atTop_nat

              . simp
                exact h_seq
            . simp
            . simp
          . rw [Pi.le_def]
            intro x
            simp
          . rw [Pi.le_def]
            intro n
            simp
            have bound_by_norm_one := conv_laplce_norm (seq n)
            have norm_le_two_div := f_n_sub_conv  (seq n)
            nth_rw 1 [eLpNorm] at bound_by_norm_one
            simp at bound_by_norm_one
            grw [bound_by_norm_one]
            have h_norm := H_n_norm (seq n)
            simp [eLpNorm, eLpNorm'] at h_norm
            rw [h_norm]
            simp
            simp_rw [Laplace_b]
            simp [eLpNorm] at norm_le_two_div
            exact norm_le_two_div

        rw [← ENNReal.tendsto_toReal_iff] at laplace_conv_tendsto_zero

        have laplace_real_tendsto_zero: Filter.Tendsto (fun n => |(Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) (g))|) Filter.atTop (nhds 0)  := by
          apply squeeze_zero (g := fun n => (eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤ volume).toReal)
          .
            intro n
            simp
          . intro n
            have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) x‖ₑ) (μ := volume)
            simp [volume] at ae_le
            rw [my_haar_eq_count] at ae_le
            rw [count_ae_everywhere] at ae_le
            specialize ae_le g
            simp [eLpNorm, eLpNorm']
            simp [eLpNormEssSup]
            rw [← ENNReal.toReal_le_toReal] at ae_le
            simp only [toReal_enorm, Real.norm_eq_abs, OrderTop.bddAbove] at ae_le
            simp [volume]
            rw [my_haar_eq_count]
            exact ae_le
            . simp
            .
              -- TODO - deduplicate this
              have bound_by_norm_one := conv_laplce_norm (seq n) H_n
              have norm_le_two_div := f_n_sub_conv (seq n)
              nth_rw 1 [eLpNorm] at bound_by_norm_one
              simp at bound_by_norm_one
              have h_norm := H_n_norm (seq n)
              simp [eLpNorm, eLpNorm'] at h_norm
              rw [h_norm] at bound_by_norm_one
              simp only [eLpNormEssSup] at bound_by_norm_one
              simp [volume] at bound_by_norm_one
              rw [my_haar_eq_count] at bound_by_norm_one
              rw [← lt_top_iff_ne_top]
              grw [bound_by_norm_one]
              simp_rw [Laplace_b]
              simp [volume] at norm_le_two_div
              rw [my_haar_eq_count] at norm_le_two_div
              grw [norm_le_two_div]
              apply ENNReal.ofReal_lt_top
          . apply laplace_conv_tendsto_zero

        simp_rw [Laplace_b] at laplace_real_tendsto_zero
        simp_rw [f_conv_mu] at laplace_real_tendsto_zero
        beta_reduce at laplace_real_tendsto_zero
        conv at laplace_real_tendsto_zero =>
          arg 1
          rw [← Function.comp_def]
        rw [← tendsto_zero_iff_abs_tendsto_zero] at laplace_real_tendsto_zero
        --simp_rw [Function.comp_def] at lim_f_g_sub
        conv at laplace_real_tendsto_zero =>
          arg 1
          intro n
          simp

        conv at lim_f_g_sub =>
          arg 1
          intro n
          rw [← Finset.sum_subtype (s := S) (f := fun s => Conv (H_n (seq n)) (f_n (seq n)) (s * g)) (h := by
            intro s
            simp
          )]
        have lim_eq := tendsto_nhds_unique laplace_real_tendsto_zero lim_f_g_sub
        rw [eq_comm] at lim_eq
        rw [sub_eq_zero] at lim_eq
        rw [lim_eq]
        norm_cast
        rw [← Finset.sum_subtype (s := S) (f := fun i => (F (i * g)))]
        simp
        . intro n
          -- TODO - deduplicate this. I'm sure there's lots of other versions of it scattered around this file
          rw [← lt_top_iff_ne_top]
          grw [conv_laplce_norm]
          rw [H_n_norm]
          simp
          simp_rw [Laplace_b]
          grw [MeasureTheory.eLpNorm_sub_le]
          rw [f_n_norm_one]
          simp_rw [f_conv_mu]
          simp_rw [← smul_eq_mul]
          rw [← Pi.smul_def]
          rw [MeasureTheory.eLpNorm_const_smul]
          conv =>
            lhs
            rhs
            rhs
            arg 1
            equals ∑ x ∈ S, (fun g => f_n (seq n) (x • g)) =>
              funext g
              simp


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
          simp_rw [f_n_norm_one]
          simp
          field_simp
          norm_cast
          rw [Real.enorm_eq_ofReal_abs]
          simp
          norm_cast
          apply ENNReal.mul_lt_top
          . simp
          . simp
          .
            intro s hs
            apply AEStronglyMeasurable.of_discrete
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . simp


        . simp
      . intro s hs
        apply tendsto_F
  }
  exact F_lipschitzh

lemma counting_le_essSup (f: G → ℝ): ∀ g : G, ‖f g‖ₑ ≤ essSup  (fun g => ‖f g‖ₑ) volume := by
  intro g
  have ae_le := ENNReal.ae_le_essSup (fun g => ‖f g‖ₑ) (μ := volume)
  simp [MeasureTheory.volume] at ae_le
  rw [my_haar_eq_count] at ae_le
  rw [count_ae_everywhere] at ae_le
  specialize ae_le g
  simp
  simp [volume]
  rw [my_haar_eq_count]
  exact ae_le

lemma essSup_eq_elpNorm_top (f: G → ℝ): (essSup (fun g => ‖f g‖ₑ) volume) = (eLpNorm f ⊤ volume) := by
  rfl


noncomputable def Laplace_linear: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) →ₗ[ℝ] (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) := {
  toFun := Laplace
  map_add' := by
    intro x y
    simp [Laplace]
    simp [conv_mu_lp2]
    have coe_add := MeasureTheory.Lp.coeFn_add x y
    rw [ae_eq_everywhere] at coe_add
    norm_cast
    simp_rw [coe_add]
    conv =>
      pattern Conv _ _
      rw [conv_add_left (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      ) (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      )]

    rw [MeasureTheory.MemLp.toLp_add]
    . abel
    .
      have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 x)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
    . have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 y)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
  map_smul' := by
    intro c f
    simp [Laplace, conv_mu_lp2]
    have smul_ae := MeasureTheory.Lp.coeFn_smul c f
    rw [ae_eq_everywhere] at smul_ae
    simp_rw [smul_ae]
    simp_rw [conv_smul]
    rw [MeasureTheory.MemLp.toLp_const_smul]
    rw [smul_sub]
}


instance volume_finite_compact: IsFiniteMeasureOnCompacts (volume (α := G)) := by
  simp [volume]
  rw [my_haar_eq_count]
  exact {
    lt_top_of_isCompact := by
      intro k hk
      have finite := IsCompact.finite hk DiscreteTopology.isDiscrete
      exact Measure.count_apply_lt_top.mpr finite
  }


lemma finsupp_lp_top (f: G → ℝ) (hf: f.support.Finite) (p: ENNReal): MeasureTheory.MemLp f p (Measure.count) := by
  rw [← my_haar_eq_count]
  apply Continuous.memLp_of_hasCompactSupport
  . apply continuous_of_discreteTopology
  .
    simp [HasCompactSupport]
    rw [isCompact_iff_finite]
    simp [tsupport]
    exact hf


noncomputable def F_n (n : ℕ) := Real.sqrt ∘ (f_n  n)
noncomputable def F_n_lp2 (n : ℕ) := MeasureTheory.MemLp.toLp (F_n  n) (by
  simp [volume]
  rw [my_haar_eq_count]
  apply finsupp_lp_top
  simp [F_n]
  apply Set.Finite.subset (s := (f_n n).support)
  .
    unfold f_n
    apply f_n_fin_supp
  .
    apply Function.support_comp_subset
    simp
) (μ := volume (α := G)) (p := 2)


instance volume_mul_left_invariant: (volume (α := G)).IsMulLeftInvariant := by
  simp [volume]
  rw [my_haar_eq_count]
  infer_instance

omit hGS in
lemma abs_sub_le_abs_add (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): |a - b| ≤ |a + b| := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  .
    rw [le_abs]
    grind
  . rw [le_abs]
    grind

lemma norm_sub_squared_le (a b : ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): (a - b)^2 ≤ |a^2 - b^2| := by
  conv =>
    lhs
    rw [← sq_abs]
    rw [pow_two]

  rw [sq_sub_sq]
  rw [abs_mul]
  nth_rw 2 [mul_comm]
  -- TODO - why doesn't grw work here?
  apply mul_le_mul
  . simp
  . apply abs_sub_le_abs_add a b ha hb
  . simp
  . simp


def f_n_conv_delta_tendsto: Prop :=  ∀ s: S, Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0)


lemma f_conv_delta_helper (f: G → ℝ) (s: G): (Conv  f (delta s)) = fun g => f (s⁻¹ * g) := by
  funext g
  exact f_conv_delta f g s


-- Lemma 3.16 in Vikman

-- The case split statement in Vikman

lemma F_n_conv_mu_lim (f_n_limit: f_n_conv_delta_tendsto):
    Filter.Tendsto (fun n => ‖(F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n)‖ₑ) Filter.atTop (nhds 0) := by

  have f_n_sub_norm: ∀ s ∈ S, ∀ (i : ℕ), ∑' (g : G), ‖f_n i g - f_n i (s * g)‖ₑ ≠ ⊤ := by
    intro s hs n
    have foo := f_n_norm_one n
    rw [← lt_top_iff_ne_top]
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)] at foo
    rw [lintegral_g_eq_add] at foo
    simp at foo
    grw [ENNReal.tsum_le_tsum (g := fun g => ‖f_n n g‖ₑ + ‖(f_n n (s * g))‖ₑ)]
    .
      rw [ENNReal.tsum_add]
      rw [ENNReal.add_lt_top]
      . refine ⟨?_, ?_⟩
        . simp [foo]
        .
          grw [ENNReal.tsum_comp_le_tsum_of_injective (g := fun a =>  ‖f_n n a‖ₑ)]
          .
            simp [foo]
          . intro a b hab
            simpa using hab
    .
      intro a
      grw [enorm_sub_le]

  rw [← ENNReal.tendsto_toReal_iff]
  .
    have S_ne: (#S : ℝ) ≠ 0 := by
      simp
      have foo := hGS.hS
      simp at foo
      grind

    simp_rw [MeasureTheory.Lp.enorm_def]
    simp_rw [conv_mu_lp2, f_conv_mu]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    conv =>
      arg 1
      intro n
      arg 1
      arg 1
      lhs
      equals (1 / (#S : ℝ)) • ∑ s ∈ S, ↑↑(F_n_lp2 n) =>
        simp
        conv =>
          rhs
          equals ((#S : ℝ))⁻¹ • (#S : ℝ) • (F_n_lp2 n).val.cast =>
            norm_cast
            simp
        simp [S_ne]

    conv =>
      arg 1
      intro n
      arg 1
      arg 1
      rhs
      equals (1 / ↑(#S : ℝ)) • ∑ s ∈ S, (fun g => (F_n_lp2 n) (s * g)) =>
        ext a
        simp

    simp_rw [← smul_sub]
    simp_rw [← Finset.sum_sub_distrib]
    rw [ENNReal.toReal_zero]


    apply squeeze_zero (g := fun n => (1 / ↑(#S : ℝ)) • ∑ x ∈ S, (eLpNorm ((F_n_lp2 n).val.cast - (fun (g: G) => (F_n_lp2 n) (x * g))) 2 volume).toReal)
    . simp
    .
      intro n
      rw [eLpNorm_const_smul]
      grw [eLpNorm_sum_le]
      .
        simp
        rw [ENNReal.toReal_sum]
        intro s hs
        rw [← lt_top_iff_ne_top]
        grw [eLpNorm_sub_le]
        .
          rw [ENNReal.add_lt_top]
          . refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              simp_rw [← Function.comp_def]
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . simp
      .
        apply ENNReal.mul_ne_top (by simp)
        rw [ENNReal.sum_ne_top]
        -- TODO - deduplicate this
        intro s hs
        rw [← lt_top_iff_ne_top]
        grw [eLpNorm_sub_le]
        .
          rw [ENNReal.add_lt_top]
          . refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              simp_rw [← Function.comp_def]
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . simp
      . intro s hs
        apply AEStronglyMeasurable.of_discrete
      . simp
    .
      conv =>
        rhs
        equals nhds ((1 / ↑(#S : ℝ)) • 0) =>
          simp

      apply Filter.Tendsto.const_smul
      conv =>
        rhs
        equals nhds (∑ x_1 ∈ S⁻¹, (0: ℝ)) =>
          simp
      conv =>
        arg 1
        intro x
        arg 1
        equals S⁻¹ =>
          apply S_eq_Sinv
      apply tendsto_finset_sum
      intro s hs
      conv =>
        arg 1
        intro n
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)]
        rw [lintegral_g_eq_add]

      simp
      apply squeeze_zero (g := (fun n ↦ ((∑' (g : G), ‖(f_n n) g - (f_n n) (s * g)‖ₑ) ^ (2 : ℝ)⁻¹).toReal))
      . simp
      .
        intro n
        rw [ENNReal.toReal_le_toReal]
        .
          apply ENNReal.rpow_le_rpow
          .
            apply ENNReal.tsum_le_tsum
            intro g
            rw [Real.enorm_eq_ofReal_abs]
            rw [Real.enorm_eq_ofReal_abs]
            rw [← ENNReal.ofReal_pow]
            .
              apply ENNReal.ofReal_le_ofReal
              simp [F_n_lp2]
              simp [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
              simp [F_n]
              conv =>
                rhs
                arg 1
                equals (Real.sqrt (f_n n g))^2 - (Real.sqrt (f_n n (s * g)))^2 =>
                  rw [Real.sq_sqrt]
                  .
                    rw [Real.sq_sqrt]
                    . apply f_n_nonneg
                  . apply f_n_nonneg

              apply norm_sub_squared_le
              . simp
              . simp
            . simp
          . simp
        .
          rw [← lt_top_iff_ne_top]
          have norm_sub_lt: eLpNorm (((F_n_lp2 n).val.cast) - ((F_n_lp2 n) ∘ fun a ↦ s * a)) 2 volume < ⊤ := by
            grw [eLpNorm_sub_le]
            rw [ENNReal.add_lt_top]
            refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
            . apply AEStronglyMeasurable.of_discrete
            . apply AEStronglyMeasurable.of_discrete
            . simp
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)] at norm_sub_lt
          rw [lintegral_g_eq_add] at norm_sub_lt
          simp at norm_sub_lt
          exact norm_sub_lt
        .
          apply ENNReal.rpow_ne_top_of_nonneg
          . simp
          . apply f_n_sub_norm s (by rw [S_eq_Sinv]; simp [hs])
      .
        unfold f_n_conv_delta_tendsto at f_n_limit
        simp at hs
        specialize f_n_limit ⟨s⁻¹, hs⟩
        conv at f_n_limit =>
          arg 1
          intro n
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)]
          rw [lintegral_g_eq_add]

        simp_rw [f_conv_delta_helper] at f_n_limit
        simp at f_n_limit
        conv =>
          rhs
          equals nhds (0 ^ (2 : ℝ)⁻¹) =>
            simp
        simp_rw [← ENNReal.toReal_rpow]
        apply Filter.Tendsto.rpow_const
        .
          rw [← ENNReal.tendsto_toReal_iff] at f_n_limit
          . exact f_n_limit
          .
            apply f_n_sub_norm s (by rw [S_eq_Sinv]; simp [hs])
          . simp
        . simp
  . intro n
    rw [MeasureTheory.Lp.enorm_def]
    apply MeasureTheory.Lp.eLpNorm_ne_top
  . simp

#print axioms F_n_conv_mu_lim

#synth TopologicalSpace ↥(Lp ℝ 2 volume (α := G))

end GeneratesNS
