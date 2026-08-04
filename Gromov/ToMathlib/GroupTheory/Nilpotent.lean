module

public import Mathlib

/-!
# Nilpotent groups

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

@[expose] public section

-- TODO - can the injectivity requirement be removed?
lemma map_nilpotent {G H: Type*} [Group G] [Group H] (A: Subgroup G) (f: G →* H) (hf: Function.Injective f) (hG: Group.IsNilpotent A): Group.IsNilpotent (Subgroup.map f A) := by
  rw [← Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ _ _)]
  . exact hG
  . exact hf
