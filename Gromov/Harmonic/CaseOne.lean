module

public import Mathlib
public import Gromov.Harmonic.Proposition318

/-!
# Existence of a nontrivial harmonic function: first case

`nontrivial_harmonic_case_one`.
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma nontrivial_harmonic_case_one (f_n_limit: ∀ s: S, (Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by


  let H_n (n: ℕ) (s: G): (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) :=
    (1 / (‖(((G_n (n + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) f_n_limit) (delta s) (by simp [delta]))))‖)) •
      MeasureTheory.Lp.compMeasurePreserving (Inv.inv) (measure_preserving_inv) (((G_n (n + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) f_n_limit) (delta s) (by simp [delta]))))

  obtain ⟨s, s_mem_S, s_infinite⟩ := g_sub_norm_single_s f_n_limit
  let seq := Nat.nth ({n | ‖(G_n (n + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (G_n (n + 1) (by simp) f_n_limit) (delta s) (by simp))‖ ^ 2 > 1})
  have seq_mono : StrictMono seq := Nat.nth_strictMono s_infinite


  have H_n_norm (n: ℕ): ‖H_n (seq n) s‖ₑ = 1 := by
    conv =>
      rhs
      equals ‖(1: ℝ)‖ₑ => simp
    rw [enorm_eq_iff_norm_eq]
    unfold H_n
    have norm_gt := Nat.nth_mem_of_infinite s_infinite n
    rw [norm_smul]
    rw [MeasureTheory.Lp.norm_compMeasurePreserving]
    field_simp
    simp
    rw [mul_inv_cancel₀]
    simp [seq]
    simp at norm_gt
    by_contra!
    simp only [Set.ofPred] at this
    simp [this] at norm_gt
    norm_num at norm_gt

  have seq_add_pos: ∀ {n}, 0 < (seq (n + 1)) := by
    intro n
    have prev_lt := (seq_mono.lt_iff_lt (a := n) (b := n + 1)).mpr (by simp)
    grind

  have h_n_f_lipschitz: ∀ n: ℕ, LipschitzWith ((2 * #(S))^((2 : ℝ)⁻¹)) (Conv (H_n (seq (n)) s) (G_n ((seq n) + 1) (by simp) f_n_limit)) := by
    intro n
    let G'_n := (G_n ((seq n) + 1) (by simp))
    apply lipschitzWith_discrete
    intro g y hy
    rw [Real.dist_eq]
    rw [← Real.norm_eq_abs]
    rw [norm_sub_rev]
    have y_eq_inv_inv: y = y⁻¹⁻¹ := by simp
    rw [y_eq_inv_inv]
    rw [← f_conv_delta (f := Conv (↑↑(H_n (seq (n)) s)) (G_n ((seq n) + 1) (by simp) f_n_limit))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [← neg_one_smul ℝ]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        rw [← ENNReal.ofReal_le_ofReal_iff]
        .
          rw [ofReal_norm_eq_enorm]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [my_haar_eq_count]
          rw [← my_haar_eq_count]
          conv =>
            lhs
            arg 1
            arg 0
            unfold Conv
          eta_reduce
          simp_rw [my_haar_eq_count]
          conv =>
            arg 1
            arg 3
            equals myHaarAddOpp =>
              exact my_add_haar_eq_count.symm

          refine le_trans (ENNReal.eLpNorm_top_convolution_le (μ := myHaarAddOpp) (c := 1) (p := 2) (q := 2) (hpq := inferInstance) (by apply AEMeasurable.of_discrete) (by apply AEMeasurable.of_discrete) (by intro a b; simp)) ?_
          .
            simp [norm, volume] at H_n_norm
            rw [my_add_haar_eq_count]
            simp [H_n_norm]

            have sum_norm := proposition_3_18 (G'_n f_n_limit)
            have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace (G'_n f_n_limit)) (G'_n f_n_limit) (𝕜 := ℝ) (α := G)
            have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp) f_n_limit)).2
            rw [integral_eq_eq_sum] at g_inner_laplace
            replace g_inner_laplace := g_inner_laplace.trans sum_norm
            rw [g_n_conv_norm _ _ f_n_limit] at g_inner_laplace
            rw [inv_mul_eq_div] at g_inner_laplace
            rw [eq_div_iff_mul_eq] at g_inner_laplace

            .
              simp [eLpNorm, eLpNorm']
              simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, MeasureTheory.Lp.norm_def, eLpNorm, eLpNorm', conv_finsupp_lp2] at g_inner_laplace
              rw [← ENNReal.ofReal_rpow_of_pos]
              .
                have hkey : (∫⁻ (a : Additive G), ‖(H_n (seq n) s : Additive G → ℝ) a‖ₑ ^ 2 ∂Measure.count) ^ (2 : ℝ)⁻¹ = 1 := by
                  have h := H_n_norm n
                  show (∫⁻ (a : G), ‖(H_n (seq n) s : G → ℝ) a‖ₑ ^ 2 ∂Measure.count) ^ (2 : ℝ)⁻¹ = 1
                  simpa [MeasureTheory.Lp.enorm_def, eLpNorm, eLpNorm', one_div, volume,
                    my_haar_eq_count] using h
                rw [hkey, one_mul]
                apply ENNReal.rpow_le_rpow
                .
                  generalize_proofs p_1 p_2 p_3
                  -- TODO - make this less horrible
                  grw [Finset.single_le_sum (f := (fun g => ∫⁻ (a : Additive G), ‖(G_n ((seq n) + 1) (by simp) f_n_limit) a + Conv (-↑↑(G_n ((seq n) + 1) (by simp) f_n_limit)) (delta g) a‖ₑ ^ 2 ∂Measure.count)) (s := S) (hf := by simp) (h := (by rw [S_eq_Sinv]; simp [hy]))]


                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.toReal_pow] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_mul] at g_inner_laplace
                  simp  [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_inner_laplace
                  simp at g_inner_laplace
                  rw [← neg_one_smul ℝ]
                  simp_rw [conv_smul]
                  simp
                  simp_rw [← sub_eq_add_neg]
                  simp [G'_n] at g_inner_laplace
                  apply_fun ENNReal.ofReal at g_inner_laplace
                  simp at g_inner_laplace
                  rw [g_inner_laplace]
                  norm_cast
                  rw [ENNReal.ofReal_sum_of_nonneg]
                  .
                    conv =>
                      rhs
                      arg 2
                      intro i
                      rw [ENNReal.ofReal_toReal (by
                        simp [f_conv_delta_helper]
                        have g_norm := MeasureTheory.Lp.eLpNorm_lt_top ((G_n ((seq n) + 1) (by simp) f_n_limit) - (Lp.compMeasurePreserving (fun x => i⁻¹ * x) (by
                          apply measurePreserving_mul_left
                        ) (G_n ((seq n) + 1) (by simp) f_n_limit)))
                        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at g_norm
                        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)] at g_norm
                        simp [eLpNorm, eLpNorm', Lp.compMeasurePreserving] at g_norm
                        rw [ENNReal.rpow_lt_top_iff_of_pos (by simp)] at g_norm
                        grind
                      )]
                    simp [volume]
                    simp_rw [my_haar_eq_count]
                    apply le_refl
                  . simp
                . simp
              .
                simpa using S_nonempty

              -- Finset.single_le_sum
            . simp
              grind
            .
              apply MeasureTheory.Integrable.of_integral_ne_zero
              rw [← g_inner_laplace]
              simp [G'_n]
              have foo := g_n_conv_norm (seq (n) + 1) (by simp) f_n_limit
              grind
        .
          exact NNReal.coe_nonneg _
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
        .
          refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
          rw [← my_add_haar_eq_count]
          rw [← neg_one_smul ℝ]
          rw [conv_smul]
          simp
          rw [← Pi.neg_def]
          simp [Conv]
          rw [← Function.comp_def (β := Additive G)]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := Measure.count)]
          .
            conv =>
              arg 1
              arg 1
              arg 1
              equals ↑↑(G_n ((seq (n)) + 1) (by simp) f_n_limit) ∘ Additive.toMul =>
                rfl

            conv =>
              arg 1
              arg 1
              arg 2
              equals (delta y⁻¹) ∘ Additive.toMul =>
                rfl

            rw [← my_add_haar_eq_count]
            grw [ENNReal.eLpNorm_convolution_le_enorm_mul (p := 2) (q := 1)]
            .
              refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ?_) ?_
              · exact MeasureTheory.MemLp.eLpNorm_lt_top (MeasureTheory.MemLp.comp_measurePreserving (ν := volume) (Lp.memLp _) measure_preserving_unop_tomul)
              · refine MeasureTheory.MemLp.eLpNorm_lt_top (MeasureTheory.MemLp.comp_measurePreserving (ν := volume) ?_ measure_preserving_unop_tomul)
                apply Continuous.memLp_of_hasCompactSupport
                · fun_prop
                · simp [HasCompactSupport, tsupport]
            . simp
            . simp
            . simp
            . simp
            . apply AEMeasurable.of_discrete
            . apply AEMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [my_add_haar_eq_count]
            apply MeasurePreserving.id
    . rw [← my_haar_eq_count]
      apply Lp.memLp
    . rw [← my_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp

  -- Now rename Hn ∗Gn such that we have added a constant so that Hn ∗Gn(e) = 0
  let new_seq: ℕ → ℕ := seq
  let H_G_conv_zero (n: ℕ) (g: G) := ((Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp) f_n_limit)) g) - (Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp) f_n_limit) 1)


  -- TODO - can the lipschitz constant can be improved?
  have H_G_conv_zero_lipschitz: ∀ n: ℕ, LipschitzWith ((((2 * #(S))^((2 : ℝ)⁻¹))) + 0) (H_G_conv_zero n) := by
    intro n
    simp only [H_G_conv_zero]
    simp only [new_seq]
    apply LipschitzWith.sub
    .
      apply h_n_f_lipschitz
    . apply LipschitzWith.const


  have H_n_conv_zero_eq: ∀ n: ℕ, (H_G_conv_zero (n) 1) - (H_G_conv_zero (n) s⁻¹) = ‖(G_n ((new_seq n) + 1) (by simp) f_n_limit) - (conv_finsupp_lp2 (((G_n ((new_seq n) + 1) (by simp) f_n_limit))) (delta s) (by simp [delta]))‖ := by
    intro n
    simp [H_G_conv_zero]
    have s_inv_eq: s⁻¹ = s⁻¹ * 1 := by
      simp
    rw [s_inv_eq]
    rw [← f_conv_delta  (f := Conv ((H_n ((new_seq n)) s)) ((G_n ((new_seq n) + 1) (by simp) f_n_limit)))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [← neg_one_smul ℝ]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        simp [H_n, conv_finsupp_lp2]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
        rw [conv_smul]
        conv =>
          lhs
          lhs
          arg 0
          unfold Conv

        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        simp only [convolution,
          ContinuousLinearMap.coe_sub', ContinuousLinearMap.mul_apply', Pi.smul_apply, smul_eq_mul]
        simp
        have t_fake_inv: ∀ (t: G), (t: (Additive G))⁻¹ = -(Additive.ofMul t) := by
          intro t
          rfl

        simp [t_fake_inv, Additive.ofMul]
        have one_g_eq: (1 : G) = (0 : (Additive G)) := rfl
        simp_rw [one_g_eq]
        simp_rw [zero_sub]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rhs
          rhs
          equals (conv_finsupp_lp2 (-(G_n (new_seq n + 1) (by simp) f_n_limit)) (delta s) (by simp [delta])) (-t) =>
            simp [conv_finsupp_lp2]
            simp_rw [tolp_apply]
            norm_cast
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]

        simp [conv_finsupp_lp2]
        norm_cast
        simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [← neg_one_smul (R := ℝ) (M := G → ℝ)]
        simp_rw [conv_smul]
        simp
        rw [MeasureTheory.MemLp.toLp_neg (by
          rw [f_conv_delta_helper]
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
          . apply MeasureTheory.Lp.memLp
          .
            exact measurePreserving_mul_left volume s⁻¹
        )]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [← Pi.sub_apply]
        have real_inner: ∀ a b : ℝ, ⟪a, b⟫ = a * b := fun a b => by
          rw [show (⟪a, b⟫ : ℝ) = b * a from rfl, mul_comm]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rw [← Pi.add_apply]
          rw [← Pi.mul_apply]


        rw [MeasureTheory.integral_neg_eq_self]
        simp_rw [Pi.mul_apply]
        simp_rw [← real_inner]
        conv =>
          lhs
          rhs
          equals ‖(G_n (new_seq n + 1) (by simp) f_n_limit) - (MemLp.toLp (Conv ((G_n ((new_seq n) + 1) (by simp) f_n_limit)) (delta s)) (by
              rw [f_conv_delta_helper]
              rw [← Function.comp_def]
              apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
              . apply MeasureTheory.Lp.memLp
              .
                exact measurePreserving_mul_left volume s⁻¹
            ))‖^2 =>
            rw [← real_inner_self_eq_norm_sq]
            rw [MeasureTheory.L2.inner_def]
            simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
            rfl

        rw [pow_two]
        rw [real_inner]
        have key : ∀ a : ℝ, a⁻¹ * (a * a) = a := by
          intro a
          rcases eq_or_ne a 0 with h | h
          · simp [h]
          · field_simp
        exact key _
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
      .
        -- TODO - deduplicate this
        simp [f_conv_delta_helper]
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.neg
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          .
            simp [volume]
            rw [my_haar_eq_count]
            refine MeasurePreserving.mul_left Measure.count s⁻¹ ?_
            apply MeasureTheory.MeasurePreserving.id
    . rw [← my_haar_eq_count]
      apply Lp.memLp
    . rw [← my_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp [delta]


  have compact_with_fixed_g (g: G): IsCompact (closure ( (Set.range (fun n => H_G_conv_zero n g)))) := by

    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]


    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have new_compact_closure: IsCompact (closure (Set.range (fun n => H_G_conv_zero n))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]

    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have arzela_tendsto := IsCompact.tendsto_subseq new_compact_closure (x := fun n => (
    H_G_conv_zero n
  )) (by
    intro n
    apply _root_.subset_closure
    simp
  )
  obtain ⟨arzela_lim, arzela_lim_mem, arzela_seq, arzela_seq_mono, tendsto_arzela_lim⟩ := arzela_tendsto
  rw [tendsto_pi_nhds] at tendsto_arzela_lim

  have tendsto_one := tendsto_arzela_lim 1
  have tendsto_s_inv := tendsto_arzela_lim s⁻¹
  simp at tendsto_one
  simp at tendsto_s_inv

  have abs_tendsto : ∀ z: ℝ, Filter.Tendsto (fun x => |x|) (nhds z) (nhds |z|)  := by
    intro z
    apply Continuous.tendsto
    fun_prop

  have tendsto_sub := tendsto_one.sub tendsto_s_inv
  use {
    toFun := fun g => arzela_lim g
    lipschitz := by
      use ⟨(((↑(#S) * 2) ^ (2 : ℝ)⁻¹)), by positivity⟩
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq]

      have new_tendsto_sub := (abs_tendsto _).comp ((tendsto_arzela_lim x).sub (tendsto_arzela_lim y))
      have sub_le := le_of_tendsto new_tendsto_sub (b := ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist x y)) ?_
      . norm_cast
        norm_cast at sub_le
      . apply Filter.Eventually.of_forall
        intro n
        have foo := (H_G_conv_zero_lipschitz (arzela_seq n)).dist_le_mul x y
        rw [Real.dist_eq] at foo
        simp
        norm_cast
        simp at foo
        norm_cast at foo
        ring_nf at foo
        ring_nf
        exact foo

    harmonic := by
      simp [Harmonic]
      intro x
      rw [← sub_eq_zero]

      have sum_lim := tendsto_finset_sum (s := S) (fun s hs => tendsto_arzela_lim (s * x))
      have tendsto_sub := (tendsto_arzela_lim x).sub (sum_lim.const_mul ((#S : ℝ))⁻¹)
      norm_cast

      have lim_zero := squeeze_zero (t₀ := Filter.atTop)
        (f := (fun x_1 ↦ |((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 x - (↑(#S))⁻¹ * ∑ c ∈ S, ((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 (c * x)|))
        (g := fun n => (1 / (n + 1)))
        ?_ ?_ ?_
      .
        have target_eq_zero := tendsto_nhds_unique ((abs_tendsto _).comp tendsto_sub) (lim_zero)
        rw [abs_eq_zero] at target_eq_zero
        rw [sub_eq_zero] at target_eq_zero
        simp [target_eq_zero]
      . simp
      . intro n
        simp
        conv =>
          lhs
          arg 1
          equals Laplace_b (H_G_conv_zero (arzela_seq n)) x =>
            simp [Laplace_b]
            simp [f_conv_mu]


        have ae_le := ENNReal.ae_le_essSup (fun x ↦ ENNReal.ofReal |Laplace_b (H_G_conv_zero (arzela_seq n)) x|) (μ := volume)
        simp [volume] at ae_le
        rw [my_haar_eq_count] at ae_le
        rw [count_ae_everywhere] at ae_le
        specialize ae_le x
        rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
        grw [ae_le]

        simp [H_G_conv_zero]
        intro i
        rw [← Pi.sub_def]
        rw [laplace_b_sub]
        simp
        rw [sub_eq_add_neg]
        grw [abs_add_le]
        simp
        rw [laplace_conv_eq_laplace_right_of_lp2]
        .
          simp [Conv]
          grw [ENNReal.ofReal_add_le]
          rw [← Real.enorm_eq_ofReal_abs]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [haar_eq_haar_add]
          conv =>
            lhs
            arg 1
            arg 1
            arg 2
            equals (Laplace_b (G_n ((new_seq (arzela_seq n)) + 1) (by simp) f_n_limit)) ∘ Additive.toMul =>
              rfl

          conv =>
            lhs
            arg 1
            arg 1
            arg 1
            equals (H_n (new_seq (arzela_seq n)) s) ∘ Additive.toMul =>
              rfl

          refine le_trans (add_le_add_left (ENNReal.eLpNorm_convolution_le_enorm_mul (G := Additive G) (L := ContinuousLinearMap.mul ℝ ℝ) (p := 2) (q := 2) (r := ⊤) (μ := myHaarAddOpp) ?_ ?_ ?_ ?_ ?_ ?_) _) ?_
          · simp
          · simp
          · simp
          · rw [ENNReal.inv_top, zero_add]; exact ENNReal.inv_two_add_inv_two
          · apply AEMeasurable.of_discrete
          · apply AEMeasurable.of_discrete
          .
            conv =>
              lhs
              arg 1
              arg 1
              arg 2
              arg 1
              equals ↑↑(H_n (seq (arzela_seq n)) s) => rfl


            rw [show eLpNorm (↑↑(H_n (seq (arzela_seq n)) s)) 2 myHaarAddOpp = 1 from by
                  have h := H_n_norm (arzela_seq n)
                  rw [MeasureTheory.Lp.enorm_def] at h
                  rw [my_add_haar_eq_count,
                      show (Measure.count : Measure (Additive G)) = myHaar from my_haar_eq_count.symm]
                  exact h]
            simp [enorm]
            have g_norm := g_n_laplace_enorm_le (seq (arzela_seq n) + 1) (by simp) f_n_limit
            rw [MeasureTheory.Lp.enorm_def] at g_norm
            simp only [Laplace] at g_norm
            rw [laplace_b_const]
            simp [Laplace_b]
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_norm
            simp only [conv_mu_lp2] at g_norm
            rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_norm
            refine le_trans (le_of_eq (eLpNorm_comp_measurePreserving (by apply AEStronglyMeasurable.of_discrete) measure_preserving_unop_tomul)) ?_
            grw [g_norm]
            norm_cast
            simp
            norm_cast
            rw [ENNReal.ofReal_inv_of_pos (by positivity)]
            simp
            norm_cast
            have seq_le_n : n ≤ seq (arzela_seq n) := by
              have n_arzela : n ≤ arzela_seq n := by
                apply StrictMono.le_apply arzela_seq_mono
              apply LE.le.trans n_arzela

              apply StrictMono.le_apply seq_mono

            omega

        .
          -- TODO - deduplicate this
          simp [ConvExists]
          rw [my_add_haar_eq_count]
          apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
          . infer_instance
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [← Function.comp_def]
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
          .
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
        . rw [← my_haar_eq_count]
          apply Lp.memLp
        . rw [← my_haar_eq_count]
          apply Lp.memLp
      .
        simp
        simp_rw [inv_eq_one_div]
        apply tendsto_one_div_add_atTop_nhds_zero_nat
  }
  intro z
  by_contra!
  have lim_ge := ge_of_tendsto tendsto_sub (b := 1) (by
    apply Filter.Eventually.of_forall
    intro n
    rw [H_n_conv_zero_eq]
    simp [new_seq, seq]
    have norm_gt := Nat.nth_mem_of_infinite s_infinite ((arzela_seq n))
    simp at norm_gt
    apply le_of_lt
    exact norm_gt
  )

  apply_fun (fun f => f 1 - f s⁻¹) at this
  simp [ConstLipschitzH] at this
  norm_cast at this
  grind


-- Case two of Theorem 3.6

end GeneratesNS
