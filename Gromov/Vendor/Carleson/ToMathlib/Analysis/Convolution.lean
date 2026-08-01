/-
Copyright (c) 2024 The Carleson project contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.Convolution

/-!
# Vendored from the Carleson project

Port of the part of `Carleson/ToMathlib/Analysis/Convolution.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`) that is needed for
`ConvolutionExists.of_memLp_memLp`.
-/

set_option linter.style.header false

@[expose] public section

open scoped Convolution

namespace MeasureTheory

universe u𝕜 uG uE uE' uF

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  {f : G → E} {g : G → E'}

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F]
variable {L : E →L[𝕜] E' →L[𝕜] F}

variable [MeasurableSpace G]

/-- This implies both of the following theorems `ConvolutionExists.of_memLp_memLp` and
`enorm_convolution_le_eLpNorm_mul_eLpNorm`. -/
lemma lintegral_enorm_convolution_integrand_le_eLpNorm_mul_eLpNorm [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ] [μ.IsNegInvariant]
    [μ.IsAddLeftInvariant] {p q : ENNReal} (hpq : p.HolderConjugate q)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ ‖f x‖ * ‖g y‖)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (x₀ : G) :
    ∫⁻ a, ‖L (f a) (g (x₀ - a))‖ₑ ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  rw [eLpNorm_comp_measurePreserving (p := q) hg (μ.measurePreserving_sub_left x₀) |>.symm]
  replace hpq : 1 / 1 = 1 / p + 1 / q := by
    simpa using (ENNReal.HolderConjugate.inv_add_inv_eq_one p q).symm
  replace hpq : ENNReal.HolderTriple p q 1 := ⟨by simpa [eq_comm] using hpq⟩
  have hg' : AEStronglyMeasurable (g <| x₀ - ·) μ :=
    hg.comp_quasiMeasurePreserving <| quasiMeasurePreserving_sub_left μ x₀
  have hL' : ∀ᵐ (x : G) ∂μ, ‖L (f x) (g (x₀ - x))‖ ≤ (1 : NNReal) * ‖f x‖ * ‖g (x₀ - x)‖ := by
    simpa using Filter.Eventually.of_forall (fun x ↦ hL x (x₀ - x))
  simpa [eLpNorm, eLpNorm', Function.comp_def] using
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf hg' (L ·) _ hL' (hpqr := hpq)

/-- If `MemLp f p μ` and `MemLp g q μ`, where `p` and `q` are Hölder conjugates, then the
convolution of `f` and `g` exists everywhere. -/
theorem ConvolutionExists.of_memLp_memLp [AddGroup G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [SFinite μ] [μ.IsNegInvariant] [μ.IsAddLeftInvariant]
    [μ.IsAddRightInvariant] {p q : ENNReal} (hpq : p.HolderConjugate q)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ ‖f x‖ * ‖g y‖) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfp : MemLp f p μ) (hgq : MemLp g q μ) :
    ConvolutionExists f g L μ := by
  refine fun x ↦ ⟨AEStronglyMeasurable.convolution_integrand_snd L hf hg x, ?_⟩
  apply lt_of_le_of_lt (lintegral_enorm_convolution_integrand_le_eLpNorm_mul_eLpNorm hpq hL hf hg x)
  exact ENNReal.mul_lt_top hfp.eLpNorm_lt_top hgq.eLpNorm_lt_top

end MeasureTheory
