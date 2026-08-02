import Mathlib

/-!
# Infixes of lists

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

open scoped Finset

-- TODO - should this use List.splitBy or List.splitOnP in some way?
-- TODO - cleanup the proof and upstream to mathlib
lemma list_adjacent_elements {A: Type*} (l: List A) (p: A → Bool) (n : ℕ):
    (∃ l', l' <:+: l ∧ n ≤ l'.length ∧ ∀ a ∈ l', p a) ∨ ((l.length - 1) / n) ≤ (l.countP (fun a => !(p a))):= by


  rw [or_iff_not_imp_left]
  intro no_adjacent_seq


  simp at no_adjacent_seq

  -- Strong induction on list lengths
  induction l using Nat.strongRecMeasure (f := List.length)
  case ind l ih =>
    by_cases non_matching: ∀ a ∈ l, p a
    .

      have len_lt: l.length < n := by
        by_contra!
        specialize no_adjacent_seq l (by
          simp
        ) this
        obtain ⟨a, a_mem, not_p_a⟩ := no_adjacent_seq
        specialize non_matching a a_mem
        grind

      have len_sub_lt: l.length - 1 < n := by
        omega

      apply Nat.div_eq_of_lt at len_sub_lt
      rw [len_sub_lt]
      simp
    .

      simp [-List.mem_cons] at non_matching
      obtain ⟨a, a_mem, not_p_a⟩ := non_matching

      have hn: 0 < n := by
        by_contra!
        specialize no_adjacent_seq [] (by
          simp
        ) (by
          simpa using this
        )
        simp at no_adjacent_seq

      have list_eq: l = (l.takeWhile p) ++ (l.dropWhile p) := by
        simp

      have takeWhile_lt_n: (l.takeWhile p).length < n := by
        by_contra!
        specialize no_adjacent_seq (l.takeWhile p) (by
          apply List.IsPrefix.isInfix
          apply List.takeWhile_prefix
        ) (this)

        obtain ⟨x, hx_mem, not_p_x⟩ := no_adjacent_seq
        apply List.mem_takeWhile_imp at hx_mem
        grind

      have count_p: l.countP (fun a => !(p a)) = (l.dropWhile p).countP (fun a => !(p a)) := by
        nth_rw 1 [list_eq]
        rw [List.countP_append]
        simp
        intro a ha
        apply List.mem_takeWhile_imp at ha
        exact ha


      have count_tail_eq: (l.dropWhile p).countP (fun a => !(p a)) = 1 + (l.dropWhile p).tail.countP (fun a => !(p a)) := by


        have dropWhile_not_nil: (l.dropWhile p) ≠ [] := by
          by_contra!
          rw [this] at list_eq
          simp at list_eq
          rw [list_eq] at a_mem
          apply List.mem_takeWhile_imp at a_mem
          grind

        apply List.exists_cons_of_ne_nil at dropWhile_not_nil
        obtain ⟨head, tail, h_eq⟩ := dropWhile_not_nil
        rw [h_eq]
        simp
        rw [List.countP_cons]
        simp

        have not_head := List.head?_dropWhile_not p l
        simp [h_eq] at not_head
        simp [not_head]
        rw [add_comm]


      rw [count_p]
      rw [count_tail_eq]

      have l_length_eq : l.length = (l.takeWhile p).length + (l.dropWhile p).length := by
        nth_rw 1 [list_eq]
        rw [List.length_append]

      by_cases l_len_le: l.length ≤ n
      . have l_len_sub: l.length - 1 < n := by
          omega

        apply Nat.div_eq_of_lt at l_len_sub
        rw [l_len_sub]
        simp
      .


        have drop_length: l.length - n < (l.dropWhile p).length := by
          omega

        have drop_tail_length: l.length - n  ≤ (l.dropWhile p).tail.length := by
          simp
          omega

        have ih_drop := ih (l.dropWhile p).tail (by
          simp
          omega
        ) (by
            intro x hx x_len
            have foo := no_adjacent_seq x ?_ x_len
            .
              obtain ⟨b, hb, not_p_b⟩ := foo
              use b
            .
              -- TODO - why can't grind figure this the main goal without help?

              have tail_sub: (l.dropWhile p).tail <:+: (l.dropWhile p) := by
                apply List.IsSuffix.isInfix
                apply List.tail_suffix

              grw [hx]
              grw [tail_sub]
              apply List.IsSuffix.isInfix
              apply List.dropWhile_suffix
        )

        rw [← ge_iff_le]
        grw [ih_drop.ge]
        grw [drop_tail_length.ge]
        conv =>
          arg 1
          equals 1 + (((l.length - 1) / n) - 1) =>
            rw [← Nat.sub_mul_div]
            simp
            rw [Nat.sub_right_comm]

        rw [Nat.add_sub_of_le]

        rw [Nat.one_le_div_iff hn]
        omega

#print axioms list_adjacent_elements
