module

public import Mathlib
public import Gromov.Vendor.Carleson
public import Gromov.Defs
public import Gromov.LipschitzNorm
public import Gromov.Theorem323
public import Gromov.TendstoTactic
public import Gromov.TendstoNhdsMul

/-!
# Convolution on a finitely generated group
-/

public section

set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

-- TODO - can we replace 'conv_assoc' with this?
lemma conv_assoc_of_lp2 {f g h: G → ℝ} (hf: MemLp f 2 Measure.count) (hg: MemLp g 2 Measure.count) (h_finsupp: h.support.Finite): Conv (Conv f g) h = Conv f (Conv g h) := by
  unfold Conv
  funext x


  have h_lp_n (n: ℕ): MemLp h n myHaarAddOpp := by
    apply Continuous.memLp_of_hasCompactSupport (X := Additive G) (μ := myHaarAddOpp)
    . apply continuous_of_discreteTopology
    .
      simp [HasCompactSupport]
      apply Set.Finite.isCompact
      simp [tsupport]
      exact h_finsupp

  conv =>
    lhs
    arg 1
    simp
    eta_reduce
  rw [MeasureTheory.convolution_assoc (L := ContinuousLinearMap.mul ℝ ℝ) (L₂ := ContinuousLinearMap.mul ℝ ℝ) (L₃ := ContinuousLinearMap.mul ℝ ℝ) (L₄ := ContinuousLinearMap.mul ℝ ℝ)]
  . rfl
  . intro x y z
    simp
    rw [mul_assoc]
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  .
    apply Filter.Eventually.of_forall
    intro a
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      exact hf
    . exact hg
  . apply Filter.Eventually.of_forall
    intro a
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      apply MeasureTheory.MemLp.abs
      exact hg
    . apply MeasureTheory.MemLp.abs
      rw [← my_add_haar_eq_count]
      apply h_lp_n
  .
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      apply MeasureTheory.MemLp.abs
      exact hf
    .
      unfold MeasureTheory.MemLp
      refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
      rw [← my_add_haar_eq_count]
      grw [ENNReal.eLpNorm_convolution_le_enorm_mul' (p := 2) (q := 1)]
      .
        simp
        apply ENNReal.mul_lt_top
        .
          simp_rw [← Real.norm_eq_abs]
          rw [MeasureTheory.eLpNorm_norm]
          rw [my_add_haar_eq_count]
          exact MemLp.eLpNorm_lt_top hg
        .
          simp_rw [← Real.norm_eq_abs]
          rw [MeasureTheory.eLpNorm_norm]
          rw [my_add_haar_eq_count]
          rw [← my_add_haar_eq_count]
          have foo := h_lp_n 1
          simp at foo
          exact MemLp.eLpNorm_lt_top foo
      . simp
      . simp
      . simp
      . simp
      . apply AEStronglyMeasurable.of_discrete
      . apply AEStronglyMeasurable.of_discrete

-- Proving associativity in full generality is very annoying
-- Fortunately, we only need to use it once, so we can use restrictive hypothesis that match
-- the functions we invoke this with
lemma conv_assoc {f g h: G → ℝ} (h_fg: ConvExists f g) (h_gh: ConvExists g h) (g_finsupp: g.support.Finite) (g_nonneg: ∀ a : G, 0 ≤ g a) (h_finsupp: h.support.Finite) (h_nonneg: ∀ a : G, 0 ≤ h a): Conv (Conv f g) h = Conv f (Conv g h) := by
  unfold Conv
  unfold ConvExists at h_fg
  funext x
  conv =>
    lhs
    arg 1
    simp
    eta_reduce
  rw [MeasureTheory.convolution_assoc (L := ContinuousLinearMap.mul ℝ ℝ) (L₂ := ContinuousLinearMap.mul ℝ ℝ) (L₃ := ContinuousLinearMap.mul ℝ ℝ) (L₄ := ContinuousLinearMap.mul ℝ ℝ)]
  . rfl
  . intro x y z
    simp
    rw [mul_assoc]
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  .
    apply Filter.Eventually.of_forall
    exact h_fg
  . apply Filter.Eventually.of_forall
    intro a
    conv =>
      arg 1
      intro b
      rw [Real.norm_of_nonneg (g_nonneg b)]

    conv =>
      arg 2
      intro b
      rw [Real.norm_of_nonneg (h_nonneg b)]
    apply h_gh a
  .

    have g_supp_compact: HasCompactSupport fun x ↦ ‖g x‖ := by
      apply HasCompactSupport.intro (K := g.support)
      . apply Set.Finite.isCompact
        apply g_finsupp
      . simp

    have h_supp_compact: HasCompactSupport fun x ↦ ‖h x‖ := by
      apply HasCompactSupport.intro (K := h.support)
      . apply Set.Finite.isCompact
        apply h_finsupp
      . simp

    apply HasCompactSupport.convolutionExists_right
    .
      apply HasCompactSupport.convolution
      .
        apply g_supp_compact
      . apply h_supp_compact
    . apply Continuous.locallyIntegrable
      exact continuous_of_discreteTopology
    .
      apply HasCompactSupport.continuous_convolution_right
      . apply h_supp_compact
      .
        apply Continuous.locallyIntegrable
        exact continuous_of_discreteTopology
      . exact continuous_of_discreteTopology

lemma mu_conv_finsupp (m: ℕ): (muConv  m).support.Finite := by
  induction m with
  | zero =>
    simp [muConv]
    apply mu_finsupp
  | succ n ih =>
    unfold muConv
    rw [Function.iterate_succ_apply']

    conv =>
      arg 1
      arg 1
      rw [conv_eq_sum' (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      )]


      intro g
      rw [tsum_eq_sum (s := (Finset.image Additive.ofMul (ih).toFinset)) (by
        intro a ha
        simp at ha
        simp
        unfold muConv at ha
        left
        have foo := ha (a.toMul)
        simp at foo
        exact foo
      )]


    apply Set.Finite.subset (ht := Finset.support_sum _ _)
    .

      simp [-Function.mem_support]
      apply Set.Finite.biUnion'
      . exact ih
      .
        intro i hi
        apply Set.Finite.inter_of_right
        apply Set.Finite.of_injOn (f := fun x => x * i⁻¹) (t := (mu_finsupp ).toFinset)
        .
          intro x hx
          simp at hx
          simp
          exact hx
        .
          intro y hy z hz
          simp
        . simp
          apply (mu_finsupp )

lemma conv_sum {T: Type*} (H: Finset T) (f: T → G → ℝ) (h: G → ℝ) (h_finsupp: h.support.Finite): Conv (∑ t ∈ H, f t) h = ∑ t ∈ H, (Conv (f t) h) := by
  funext g
  rw [conv_eq_sum]
  .
    simp
    conv =>
      rhs
      arg 2
      intro t
      rw [conv_eq_sum (by
        apply conv_exists_fin_supp
        right
        exact h_finsupp
      )]

    conv =>
      lhs
      arg 1
      intro a
      rw [Finset.sum_mul]

    rw [Summable.tsum_finsetSum]
    intro s hs
    apply summable_of_hasFiniteSupport
    change (Function.support _).Finite
    simp only [Function.support_mul]
    apply Set.Finite.inter_of_right
    rw [← Function.comp_def]
    rw [Function.support_comp_eq_preimage]
    apply Set.Finite.preimage
    .
      intro y hy z hz
      simp
    . exact h_finsupp
  . apply conv_exists_fin_supp
    right
    exact h_finsupp

-- The convolution of an Lp2 function with a finitely-supported function is LP2
--set_option maxHeartbeats 1000000 in
@[expose]
noncomputable def conv_finsupp_lp2 (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))) (g : G → ℝ) (hg : g.support.Finite): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := MeasureTheory.MemLp.toLp (Conv f g) (by
  simp [MemLp]
  refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
  have norm_bound := ENNReal.eLpNorm_convolution_le_enorm_mul (G := Additive G)  (f := f) (g := g) (E' := ℝ) (E := ℝ) (F := ℝ) (𝕜 := ℝ) (p := 2) (q := 1) (r := 2) (μ := myHaarAddOpp) (ContinuousLinearMap.mul ℝ ℝ)
    (by simp) (by simp) (by simp) (by simp) (by apply AEMeasurable.of_discrete) (by apply AEMeasurable.of_discrete)

  unfold Conv
  eta_reduce
  rw [my_add_haar_eq_count]
  dsimp [volume]
  simp_rw [my_haar_eq_count]
  rw [my_add_haar_eq_count] at norm_bound
  refine lt_of_le_of_lt norm_bound ?_
  apply WithTop.mul_lt_top
  . apply WithTop.mul_lt_top
    . exact enorm_lt_top
    . rw [← my_add_haar_eq_count]
      apply (MeasureTheory.Lp.memLp f).2
  .
    simp [eLpNorm, eLpNorm']
    rw [MeasureTheory.lintegral_count]
    rw [tsum_eq_sum (s := hg.toFinset) (β := Additive G)]
    . simp_rw [Real.enorm_eq_ofReal_abs]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      . -- TODO - why can't simp' find this?
        apply ENNReal.ofReal_lt_top
      . simp
    . intro b hb
      have hgb : g b = 0 := by
        by_contra hne
        exact hb (hg.mem_toFinset.mpr (Function.mem_support.mpr hne))
      rw [hgb]
      simp
)

end GeneratesNS
