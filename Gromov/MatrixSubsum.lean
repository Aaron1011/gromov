import Mathlib

structure DerivedSets {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v : (Fin n) → ℤ) (p q : Finset ℕ) where
  nontrivial: p \ q ≠ {}
  h_prime: (p \ q).sum (fun k => A^k • v) = (q \ p).sum (fun k => A^k • v)
  supp_disj: Disjoint (p \ q) (q \ p)

-- ∑ p = ∑ q
-- A + ∑ p = ∑ q

--

lemma poly_cancel {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v: (Fin n) → ℤ) (p q : Finset ℕ) (hpq: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)) (hp : ∃ a: ℕ, a ∈ p ∧ a ∉ q) : Nonempty (DerivedSets A v p q) := by

  rw [← Finset.sdiff_union_inter (s := p) (t := q)] at hpq
  rw [Finset.sum_union] at hpq
  .
    have p_inter_subset : p ∩ q ⊆ q := by
      simp
    rw [←  Finset.sum_sdiff p_inter_subset] at hpq
    simp at hpq
    apply Exists.nonempty
    use {
      nontrivial := by
        simp
        grind
      h_prime := by
        exact hpq
      supp_disj := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        grind
    }
  . apply Finset.disjoint_sdiff_inter
