import Mathlib

/-!
# Extended non-negative reals

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

lemma lt_top_mul {a b c : ENNReal} (hab: a ≤ b * c) (hb: b < ⊤) (hc: c < ⊤) : a < ⊤ := by
  have b_c_not_top: b * c < ⊤ := by
    apply WithTop.mul_lt_top (hb) (hc)
  grw [hab]
  exact b_c_not_top
