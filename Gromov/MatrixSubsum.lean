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

  induction p using Finset.induction_on generalizing q with
  | empty =>
    simp at hp
  | insert a s ha ih =>

    by_cases a_mem_q: a ∈ q
    .
      rw [Finset.sum_insert] at hpq
      conv at hpq =>
        rhs
      have prev := ih (q \ {a}) (by sorry)

    by_cases s_empty: s = {}
    .
      simp [s_empty] at hpq
      simp [s_empty]
      simp at hp
      simp [s_empty] at hp
      grind
    .
      obtain ⟨b, hb, b_not_mem⟩ := hp

      by_cases s_eq_q: s = q
      .
        grind
      .
        by_cases q_extra: ∃ b ∈ q, b ∉ s
        .

        have prev := ih q (by grind) (by sorry)
        exact {
          p' := {}
        }
      sorry
