/-
Copyright (c) 2024 The Carleson project contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Vendored from the Carleson project

Verbatim port of `Carleson/ToMathlib/MeasureTheory/Measure/Haar/Unique.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`).

Generalizes Mathlib's `IsHaarMeasure.isInvInvariant_of_regular` (which requires a commutative
group) to any regular bi-invariant Haar measure. This is what makes the non-abelian version of
Young's convolution inequality go through.
-/

set_option linter.style.header false

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

namespace MeasureTheory
namespace Measure

-- This is a generalization of `IsHaarMeasure.isInvInvariant_of_regular`, using the same proof.
/-- Any regular bi-invariant Haar measure is invariant under inversion. -/
@[to_additive /-- Any regular bi-invariant additive Haar measure is invariant under negation. -/]
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_isMulRightInvariant (μ : Measure G)
    [μ.IsHaarMeasure] [LocallyCompactSpace G] [μ.IsMulRightInvariant] [μ.Regular] :
    IsInvInvariant μ := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    simpa [map_map continuous_inv.measurable continuous_inv.measurable] using this
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

end Measure
end MeasureTheory
