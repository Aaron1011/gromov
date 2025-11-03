import Mathlib

structure DerivedSets {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v : (Fin n) → ℤ) (p q : Finset ℕ) where
  p': Finset ℕ
  q': Finset ℕ
  nontrivial: p' ≠ {}
  h_prime: p'.sum (fun k => A^k • v) = q'.sum (fun k => A^k • v)
  supp_disj: Disjoint p' q'
  p'_derived: p' ⊆ p
  q'_derived: q' ⊆ q


-- ∑ p = ∑ q
-- A + ∑ p = ∑ q

--

lemma poly_cancel {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v: (Fin n) → ℤ) (p q : Finset ℕ) (hpq: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)) (hp : ∃ a: ℕ, a ∈ p ∧ a ∉ q) : Nonempty (DerivedSets A v p q) := by
  clear hpq
  induction p using Finset.induction_on generalizing q with
  | empty =>
    simp at hp
  | insert a s ha ih =>

    by_cases a_mem_q: a ∈ q
    .
      -- rw [Finset.sum_insert] at hpq
      -- have orig_hpq := hpq
      -- conv at hpq =>
      --   rhs
      --   arg 1
      --   equals insert a (q \ {a}) =>
      --     grind
      -- simp [Finset.sum_insert] at hpq
      obtain ⟨b, b_mem, b_not_mem⟩ := hp
      obtain ⟨prev⟩ := ih (q \ {a}) (by grind)
      apply Exists.nonempty

      have s_not_mem_prev: a ∉ prev.p' := by
        have prev_p_subset := prev.p'_derived
        grind

      by_cases a_mem_prev_q': a ∈ prev.q'
      .
        have prev_prime := prev.h_prime


        use {
          p' := prev.p'
          q' := prev.q'
          nontrivial := prev.nontrivial
          h_prime := prev.h_prime
          supp_disj := prev.supp_disj
          p'_derived := by
            have prev_derived := prev.p'_derived
            grind
          q'_derived := by
            have prev_derived := prev.q'_derived
            grind
        }
      .
        have prev_prime := prev.h_prime
        use {
          p' := prev.p'
          q' := prev.q'
          nontrivial := by
            exact prev.nontrivial
          supp_disj := by
            have prev_disj := prev.supp_disj
            exact prev_disj
          h_prime := by
            exact prev.h_prime
            -- have prev_h_prime := prev.h_prime
            -- rw [Finset.sum_insert]
            -- rw [prev_h_prime]


            --rw [orig_hpq]
          p'_derived := by
            have prev_derived := prev.p'_derived
            grind
          q'_derived := by
            have prev_derived := prev.q'_derived
            grind
        }
    .
      --rw [Finset.sum_insert] at hpq
      by_cases s_subset: s ⊆ q
      .

        obtain ⟨prev⟩ := ih (q) (by sorry)
        apply Exists.nonempty

        sorry
      .
        rw [Finset.not_subset] at s_subset
        obtain ⟨b, hb, b_not_mem⟩ := hp
        simp at hb

        obtain ⟨prev⟩ := ih (q) (s_subset)
        apply Exists.nonempty
        use {
          p' := prev.p',
          q' := prev.q',
          nontrivial := by
            exact prev.nontrivial
            --simp
          supp_disj := by
            exact prev.supp_disj
            -- simp
            -- have prev_disj := prev.supp_disj
            -- have prev_q_derived := prev.q'_derived
            -- grind
          h_prime := by
            exact prev.h_prime
            -- have prev_h_prime := prev.h_prime
            -- rw [Finset.sum_insert]
            -- rw [prev_h_prime]
          p'_derived := by
            have prev_derived := prev.p'_derived
            grind
          q'_derived := by
            have prev_derived := prev.q'_derived
            grind
        }


    -- by_cases s_empty: s = {}
    -- .
    --   simp [s_empty] at hpq
    --   simp [s_empty]
    --   simp at hp
    --   simp [s_empty] at hp
    --   grind
    -- .
    --   obtain ⟨b, hb, b_not_mem⟩ := hp

    --   by_cases s_eq_q: s = q
    --   .
    --     grind
    --   .
    --     by_cases q_extra: ∃ b ∈ q, b ∉ s
    --     .

    --     have prev := ih q (by grind) (by sorry)
    --     exact {
    --       p' := {}
    --     }
    --   sorry
