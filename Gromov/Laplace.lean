module

public import Mathlib
public import Gromov.ToMathlib.GroupTheory.CosetCover
public import Gromov.Complexification
public import Gromov.Defs
public import Gromov.Harmonic
public import Gromov.UnitaryGromov
public import Gromov.UnipotentGromov
public import Gromov.NilpotentFinite
public import Gromov.ToMathlib.GroupTheory.Closure
public import Gromov.ToMathlib.Data.ENNReal.Basic
public import Gromov.ToMathlib.Data.List.Finite
public import Gromov.ToMathlib.Algebra.Group.Pointwise.Finset

/-!
# The discrete Laplacian on `Lp 2`
-/

public section

set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open MeasureTheory


open scoped RealInnerProductSpace

end GeneratesNS
