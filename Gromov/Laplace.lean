import Mathlib
import Gromov.ToMathlib.GroupTheory.CosetCover
import Gromov.Complexification
import Gromov.Defs
import Gromov.Harmonic
import Gromov.UnitaryGromov
import Gromov.UnipotentGromov
import Gromov.NilpotentFinite
import Gromov.ToMathlib.GroupTheory.Closure
import Gromov.ToMathlib.Data.ENNReal.Basic
import Gromov.ToMathlib.Data.List.Finite
import Gromov.ToMathlib.Algebra.Group.Pointwise.Finset

/-!
# The discrete Laplacian on `Lp 2`
-/

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
