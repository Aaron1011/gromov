import Mathlib

/-!
# Lexicographic order on products

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

-- TODO - generalize and upstream to mathlib
lemma prod_lex_has_unbounded {f: ℕ → Lex (ℕ × ℕ)} (hf: StrictMono f):
  ¬BddAbove (Set.range (Prod.fst ∘ f)) ∨ ¬BddAbove (Set.range (Prod.snd ∘ f)) := by
  by_contra!
  obtain ⟨fst_bounded, snd_bounded⟩ := this
  have fst_max := Nat.sSup_mem (s := Set.range (Prod.fst ∘ f)) (by apply Set.range_nonempty) fst_bounded
  simp at fst_max
  obtain ⟨fst_max, h_fst_max⟩ := fst_max
  replace h_fst_max : (f fst_max).1 = sSup (Set.range (Prod.fst ∘ f)) := h_fst_max

  have f_gt := hf (a := fst_max) (b := 1 + fst_max) (by omega)

  rw [Prod.Lex.lt_iff] at f_gt
  cases f_gt
  .
    rename_i f_gt_max
    conv at f_gt_max =>
      lhs
      equals (f fst_max).1 => rfl
    conv at f_gt_max =>
      rhs
      equals (f (1 + fst_max)).1 => rfl

    rw [h_fst_max] at f_gt_max


    have f_succ_le := le_csSup fst_bounded (a := (f (1 + fst_max)).1) ⟨1 + fst_max, rfl⟩
    rw [← h_fst_max] at f_succ_le
    linarith
  .
    rename_i h
    obtain ⟨fst_eq, snd_lt⟩ := h

    have bdd_above_subset: BddAbove { a: ℕ | ∃ n: ℕ, (f n).1 = (f fst_max).1 ∧ (f n).2 = a } := by
      apply BddAbove.mono (t := Set.range (Prod.snd ∘ f))
      . intro a ha
        obtain ⟨m, -, hm⟩ := ha
        exact ⟨m, hm⟩
      . apply snd_bounded

    have snd_max := Nat.sSup_mem (by
      use (f fst_max).2
      simp
      use fst_max
    ) bdd_above_subset
    obtain ⟨snd_max, f_snd_max_eq, h_snd_max⟩ := snd_max
    have f_gt_snd := hf (a := snd_max) (b := 1 + snd_max) (by omega)
    rw [Prod.Lex.lt_iff] at f_gt_snd
    cases f_gt_snd
    .
      rename_i fst_component_gt

      conv at fst_component_gt =>
        lhs
        equals (f snd_max).1 => rfl
      conv at fst_component_gt =>
        rhs
        equals (f (1 + snd_max)).1 => rfl

      have f_succ_le := le_csSup fst_bounded (a := (f (1 + snd_max)).1) ⟨1 + snd_max, rfl⟩
      rw [← h_fst_max] at f_succ_le
      linarith
    . rename_i fst_eq_snd_lt
      obtain ⟨new_fst_eq, new_snd_lt⟩ := fst_eq_snd_lt
      conv at new_fst_eq =>
        lhs
        equals (f snd_max).1 => rfl
      conv at new_snd_lt =>
        rhs
        equals (f (1 + snd_max)).2 => rfl


      have f_succ_le := le_csSup bdd_above_subset (a := (f (1 + snd_max)).2) (by
        simp
        use 1 + snd_max
        refine ⟨?_, rfl⟩
        rw [← f_snd_max_eq]
        rw [new_fst_eq]
        rfl
      )
      rw [← h_snd_max] at f_succ_le
      conv at new_snd_lt =>
        lhs
        equals (f snd_max).2 => rfl
      linarith
