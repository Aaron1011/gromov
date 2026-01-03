import Mathlib

lemma finite_of_nilpotent_fg_order {G: Type*} [Group G] [Group.FG G] [Group.IsNilpotent G] (m: ℕ) (hm: 0 < m) (hg: ∀ g : G, g^m = 1): Finite G := by
  sorry
