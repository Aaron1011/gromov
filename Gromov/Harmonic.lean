module

public import Mathlib
public import Gromov.Harmonic.CaseOne

/-!
# Existence of a nontrivial harmonic function

`nontrivial_harmonic_case_two` and the main result `exists_nontrivial_harmonic`.

Root of the `Gromov.Harmonic` hierarchy.
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

set_option maxHeartbeats 2000000 in
lemma nontrivial_harmonic_case_two (f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by
  obtain ⟨s, hs⟩ := f_n_limit
  let H_n := fun n g => if  ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) ≠ 0 then ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) / |((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)| else 1

  -- TODO - why can't we write '∞' here
  have H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1 := by
    intro n
    simp [H_n]
    simp [MeasureTheory.eLpNormEssSup]
    simp [MeasureTheory.volume]
    rw [my_haar_eq_count]
    simp
    have h_norm_one: ∀ x, ‖H_n n x‖ₑ = 1 := by
      simp [H_n]
      intro g
      split_ifs
      . simp
      .

        rename_i foo
        by_cases val_pos: 0 ≤ ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)
        .
          rw [abs_of_nonneg val_pos]
          rw [div_self]
          . simp
          . exact foo
        .
          rw [abs_of_neg]
          .
            rw [div_neg_self]
            .
              simp
            . exact foo
          . linarith

    unfold H_n at h_norm_one
    simp at h_norm_one
    simp_rw [h_norm_one]
    simp

  have H_n_diff_pos: ∀ n: ℕ,  ∀ (i : G), 0 ≤ H_n n i⁻¹ * f_n n i - H_n n i⁻¹ * f_n n ((↑s)⁻¹ * i) := by
    intro n g
    simp [H_n]
    simp [f_conv_delta]
    split_ifs
    . linarith
    .
      rename_i diff_zero
      by_cases val_pos: 0 ≤ f_n n g - f_n n ((↑s)⁻¹ * g)
      .
        rw [abs_of_nonneg val_pos]
        rw [div_self]
        . linarith
        . assumption
      .
        rw [abs_of_neg]
        . rw [div_neg_self]
          . linarith
          . assumption
        .
          simpa using val_pos

  have fn_sub_norm: ∀ n: ℕ, eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 = ENNReal.ofReal |((Conv (H_n n) (f_n n)) 1) - ((Conv (H_n n) (f_n n)) s⁻¹)| := by
    intro n
    simp [eLpNorm, eLpNorm']
    rw [lintegral_g_eq_add]
    conv =>
      lhs
      arg 1
      intro g
      rw [Real.enorm_eq_ofReal_abs]
      arg 1
      equals (H_n n g⁻¹) * (f_n n g - (Conv (f_n n) (delta s.val)) g) =>
        simp [H_n]
        split_ifs
        .
          rename_i diff_eq_zero
          simp [diff_eq_zero]
        .
          rename_i diff_ne_zero
          by_cases val_pos: 0 ≤ ((f_n n g) - (Conv (f_n n) (delta s.val)) g)
          .
            rw [abs_of_nonneg]
            .
             rw [div_self]
             simp
             apply diff_ne_zero
            . exact val_pos
          .
            rw [abs_of_neg]
            .
              rw [div_neg_self]
              simp
              exact diff_ne_zero
            .
              simpa using val_pos

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]


    conv =>
      rhs
      arg 1
      arg 1
      rw [← Summable.tsum_sub (by
        apply summable_of_hasFiniteSupport
        change (Function.support _).Finite
        simp only [Function.support_mul]
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => ((Additive.toMul a))⁻¹) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      ) (by
        apply summable_of_hasFiniteSupport
        change (Function.support _).Finite
        simp only [Function.support_mul]
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * ((Additive.toMul a))⁻¹ ) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      )]
    simp_rw [mul_sub]
    simp_rw [f_conv_delta]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    rw [ENNReal.ofReal_eq_ofReal_iff]
    rw [← Function.Injective.tsum_eq (γ := G) (β := Additive (G)) (g := fun a => Additive.ofMul (a⁻¹))]
    simp
    rw [abs_of_nonneg]
    rfl
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    .
      simp
      apply Function.Injective.comp
      . exact neg_injective
      . exact fun ⦃a₁ a₂⦄ a ↦ a
    .
      simp
      intro g hg
      use g⁻¹
      simp
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    . simp
    . apply H_n_diff_pos n
    .
      simp_rw [← mul_sub]
      apply summable_of_hasFiniteSupport
      change (Function.support _).Finite
      simp only [Function.support_mul]
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Function.support_sub _ _)
      simp
      refine ⟨?_, ?_⟩
      . apply f_n_fin_supp
      .
        apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * a) (ht := f_n_fin_supp n)
        . intro a ha
          simpa using ha
        . simp


  have haar_eq_haar_add : myHaar = myHaarAddOpp := by
    rfl

  have h_conv_f_bounded (n: ℕ): eLpNorm (Conv (H_n n) (f_n n)) ⊤ ≤ 1 := by
    unfold Conv
    eta_reduce
    simp only [volume]
    rw [haar_eq_haar_add]
    have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
      (g := f_n n) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
      (by simp) (by simp) (by simp) (by simp)
      (by apply AEMeasurable.of_discrete)
      (by apply AEMeasurable.of_discrete)
    refine le_trans my_norm ?_
    have norm_one := f_n_norm_one (n )
    simp [volume] at norm_one
    rw [haar_eq_haar_add] at norm_one
    simp only  [volume] at H_n_norm
    rw [haar_eq_haar_add] at H_n_norm
    refine le_trans (mul_le_mul' (mul_le_mul' (show ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 by simp [enorm]) (le_of_eq (H_n_norm n))) (le_of_eq norm_one)) ?_
    simp

  have conv_laplce_norm (n: ℕ): eLpNorm ((Laplace_b ((Conv (H_n n)) (f_n n)))) ⊤ (μ := volume (α := G)) ≤ eLpNorm (H_n n) ⊤ * (eLpNorm (Laplace_b (f_n n)) 1 (μ := volume (α := G))) := by
    rw [laplace_conv_eq_laplace_right]
    .
      unfold Conv
      eta_reduce
      simp only [volume]
      rw [haar_eq_haar_add]

      have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
        (g := Laplace_b (f_n n)) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
        (by simp)
        (by simp)
        (by simp)
        (by simp)
        (by apply AEMeasurable.of_discrete)
        (by apply AEMeasurable.of_discrete)


      refine le_trans my_norm ?_
      have h1 : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by simp [enorm]
      calc ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp
          ≤ 1 * eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp := by gcongr
        _ = eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp := by rw [one_mul]
    .
      apply conv_exists_fin_supp
      right
      exact f_n_fin_supp n
    . apply f_n_nonneg
    . exact f_n_fin_supp n


  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n n) (f_n n),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  have abs_conv_le_one: ∀ g: G, ∀ n: ℕ,  |Conv (H_n n) (f_n n) g| ≤ 1 := by
    intro g n
    have norm_bound := h_conv_f_bounded n
    simp [eLpNorm, eLpNormEssSup] at norm_bound
    have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Conv (H_n n) (f_n n) x‖ₑ) (μ := volume)
    simp [volume] at ae_le
    rw [my_haar_eq_count] at ae_le
    rw [count_ae_everywhere] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at norm_bound
    norm_cast at ae_le
    simp [volume] at norm_bound
    rw [my_haar_eq_count] at norm_bound
    specialize ae_le g
    have ennreal_bound := le_trans ae_le norm_bound
    norm_cast at ennreal_bound

  have conv_h_n_lipschitz (n: ℕ): LipschitzWith 2 (conv_h_n_cont n) := by
    unfold conv_h_n_cont
    simp [LipschitzWith]
    intro x y
    by_cases x_eq_y: x = y
    . simp [x_eq_y]
    .
      norm_cast
      rw [edist_dist]
      rw [Real.dist_eq]
      rw [edist_dist]
      conv =>
        rhs
        equals ENNReal.ofReal (2 * (dist x y)) =>
          rw [ENNReal.ofReal_mul]
          . simp
          . linarith
      rw [ENNReal.ofReal_le_ofReal_iff]
      .
        grw [abs_sub]
        grw [abs_conv_le_one x]
        grw [abs_conv_le_one y]
        rw [one_add_one_eq_two]
        simp
        simp [dist]
        have dist_ne_zero: dist x y ≠ 0 := by
          exact dist_ne_zero.mpr x_eq_y
        simp [dist] at dist_ne_zero
        omega
      . simp [dist]


  have compact_closure_f: IsCompact (closure ( (Set.range (fun n => (Conv (H_n n) (f_n n)))))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2
    intro x hx y hy
    simp at hx
    simp at hy
    obtain ⟨n, h_x_n⟩ := hx
    obtain ⟨m, h_y_m⟩ := hy
    rw [Real.dist_eq]
    grw [abs_sub]
    rw [← h_x_n, ← h_y_m]
    grw [abs_conv_le_one]
    grw [abs_conv_le_one]
    linarith


  rw [Filter.not_tendsto_iff_exists_frequently_notMem] at hs
  obtain ⟨eps, h_eps, frequently_gt_eps⟩ := hs
    -- We obtain a subsequence where all of the points satisfy the 'norm > ε' condition
  obtain ⟨eps_seq, mono_eps_seq, eps_seq_gt_x⟩ := Filter.extraction_of_frequently_atTop frequently_gt_eps

  -- Along this sequence, the evauation of 'Conv H_n f_n' at is leq to 1,
  -- so it's in a compact set


  have h_n_pointwise_converge := IsCompact.tendsto_subseq compact_closure_f (x := fun n => (Conv (H_n (eps_seq n)) (f_n (eps_seq n)))) (by
    intro n
    apply Set.mem_of_subset_of_mem (_root_.subset_closure)
    simp
  )
  -- We now have a sequence of functions which converges pointwise, where all of the
  -- elements of the sequence satisfy the 'norm > ε' condition
  obtain ⟨F, F_mem, seq, seq_mono, tendsto_F⟩ := h_n_pointwise_converge
  let F_lipschitzh := nontrivial_harmonic_common 2 (eps_seq ∘ seq) (by
    apply Filter.Tendsto.comp (x := Filter.atTop) (y := Filter.atTop)
    . exact StrictMono.tendsto_atTop mono_eps_seq
    . exact StrictMono.tendsto_atTop seq_mono
  ) F H_n conv_h_n_lipschitz tendsto_F H_n_norm
  use F_lipschitzh
  intro z
  have not_conv_tendsto_zero: ¬Filter.Tendsto (fun n => ENNReal.ofReal |Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) 1 - Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) (↑s)⁻¹|) Filter.atTop (nhds 0) := by
    rw [Filter.not_tendsto_iff_exists_frequently_notMem]
    use eps
    refine ⟨h_eps, ?_⟩
    simp_rw [← fn_sub_norm]
    apply Filter.Frequently.of_forall
    intro n
    exact eps_seq_gt_x (seq n)

  have F_non_const: F 1 ≠ F s⁻¹ := by
    by_contra!
    rw [← sub_eq_zero] at this
    rw [tendsto_pi_nhds] at tendsto_F
    have lim_f_sub := Filter.Tendsto.sub (tendsto_F 1) (tendsto_F s⁻¹)
    rw [this] at lim_f_sub
    simp_rw [Function.comp_def] at lim_f_sub
    rw [tendsto_zero_iff_abs_tendsto_zero] at lim_f_sub
    rw [Function.comp_def] at lim_f_sub
    have f_sub_ennreal := ENNReal.tendsto_ofReal lim_f_sub
    simp only [ENNReal.ofReal_zero] at f_sub_ennreal
    contradiction

  by_contra!
  -- TODO - there must be a cleaner way
  have app_one_eq: F_lipschitzh 1 = ConstLipschitzH z (1: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_one_eq
  simp [DFunLike.coe] at app_one_eq

  have app_s_inv_eq: F_lipschitzh s⁻¹ = ConstLipschitzH z (s⁻¹: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_s_inv_eq
  simp [DFunLike.coe] at app_s_inv_eq
  rw [← app_one_eq] at app_s_inv_eq
  norm_cast at app_s_inv_eq
  rw [eq_comm] at app_s_inv_eq
  simp [nontrivial_harmonic_common] at app_s_inv_eq
  contradiction


#synth OrderTopology ENNReal

-- Theorem 3.6 - a non-constant harmonic function exists on G
theorem exists_nontrivial_harmonic: ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by
  by_cases f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))
  . exact nontrivial_harmonic_case_two f_n_limit
  .
    simp at f_n_limit
    exact nontrivial_harmonic_case_one (by
      intro s
      exact f_n_limit s.val s.property
    )

end GeneratesNS
