import Mathlib

lemma my_lemma (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): a + b + 25 ≤ b + a + 100 := by
  refine letI goal := _; (?_ : zeta% goal)
  let f (y : ℝ) : ℝ := by
    haveI h : zeta% goal := sorry
    haveI hby : b = y := sorry
    exact letI lhs := _; letI h' : lhs ≤ _ := (by rewrite [hby] at h; exact h); lhs
  clear goal
  grw [Finset.single_le_sum (f := zeta% f) (s := {b})]
  . simp
    grind

  . simp
    grind
  . simp

#print axioms my_lemma
