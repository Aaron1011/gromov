import Mathlib

/-!
# Pointwise operations on finsets

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

open scoped Pointwise

-- TODO - generalize from InvolutiveInv and upstream to mathlib
lemma finset_union_inv {α : Type*}  [DecidableEq α] [InvolutiveInv α] {s t : Finset α}: (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := by
  ext a
  simp

lemma finset_union_neg {α : Type*}  [DecidableEq α] [InvolutiveNeg α] {s t : Finset α}: -(s ∪ t) = -s ∪ -t := by
  ext a
  simp
