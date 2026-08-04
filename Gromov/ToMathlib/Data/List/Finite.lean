module

public import Mathlib

/-!
# Finiteness of lists of bounded length

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

public section

@[expose]
instance simple_finite_list {G: Type*} (P: Finset G) (n: ℕ): Finite { l: List P | l.length ≤ n } := by
  apply List.finite_length_le
