/-
Copyright (c) 2024 The Carleson project contributors.
Released under Apache 2.0 license.
-/
module

public import Gromov.Vendor.Carleson.ToMathlib.Analysis.Convolution
public import Gromov.Vendor.Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Gromov.Vendor.Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities
public import Gromov.Vendor.Carleson.ToMathlib.MeasureTheory.Measure.Haar.Unique
public import Gromov.Vendor.Carleson.ToMathlib.MeasureTheory.Measure.Prod

/-!
# Vendored code from the Carleson project

Code ported from <https://github.com/fpvandoorn/carleson> (branch `young-add-group`), pared down
to what this development needs: the non-abelian form of **Young's convolution inequality** and
the existence of convolutions of `L^p`/`L^q` functions.

Importing this module supplies, sorry-free:

* `ENNReal.ConvolutionExists.of_memLp_memLp`
* `ENNReal.eLpNorm_top_convolution_le` (and `'`)
* `ENNReal.eLpNorm_convolution_le_enorm_mul` (and `'`)

which are the theorems previously stubbed out in
`Gromov.ToMathlib.Algebra.Group.CarlesonYoung`.
-/

set_option linter.style.header false
