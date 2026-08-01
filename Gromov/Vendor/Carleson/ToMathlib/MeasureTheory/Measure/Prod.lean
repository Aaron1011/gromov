/-
Copyright (c) 2024 The Carleson project contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Vendored from the Carleson project

Verbatim port of `Carleson/ToMathlib/MeasureTheory/Measure/Prod.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`).
-/

set_option linter.style.header false

@[expose] public section

namespace MeasureTheory

open MeasureTheory Measure Function
open scoped ENNReal

variable {α β : Type*}

variable [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

-- Proof copied from `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`
theorem AEMeasurable.lintegral_prod_right' [SFinite ν] ⦃f : α × β → ℝ≥0∞⦄
    (hf : AEMeasurable f (μ.prod ν)) : AEMeasurable (fun (x : α) ↦ ∫⁻ (y : β), f (x, y) ∂ν) μ :=
  ⟨fun x ↦ ∫⁻ y, hf.mk f (x, y) ∂ν, hf.measurable_mk.lintegral_prod_right', by
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using lintegral_congr_ae hx⟩

theorem AEMeasurable.lintegral_prod_right [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) : AEMeasurable (fun x ↦ ∫⁻ y, f x y ∂ν) μ :=
  hf.lintegral_prod_right'

end MeasureTheory
