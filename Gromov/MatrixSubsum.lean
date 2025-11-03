import Mathlib

structure DerivedSets {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v : (Fin n) → ℤ) (p q : Finset ℕ) where
  h_prime: (p \ q).sum (fun k => A^k • v) = (q \ p).sum (fun k => A^k • v)
  supp_disj: Disjoint (p \ q) (q \ p)


def poly_cancel {n: ℕ} (A: Matrix (Fin n) (Fin n) ℤ) (v: (Fin n) → ℤ) (p q : Finset ℕ) (hpq: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)) : DerivedSets A v p q := ({
  h_prime := by
    have p_inter_subset : p ∩ q ⊆ q := by
      simp
    rw [← Finset.sdiff_union_inter (s := p) (t := q)] at hpq
    rw [Finset.sum_union (by apply Finset.disjoint_sdiff_inter)] at hpq
    rw [←  Finset.sum_sdiff p_inter_subset] at hpq
    simpa using hpq
  supp_disj := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    grind
} : DerivedSets A v p q)


lemma subsums_unique {d: ℕ} (A: Matrix (Fin d) (Fin d) ℤ) (v: (Fin d) → ℤ) (N₀ N: ℕ) (hn: N₀ ≤ N) (p q: Finset ℕ)
  (hp: p ⊆ Finset.Ico N₀ N) (hq: q ⊆ Finset.Ico N₀ N) (hpq: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)):
    p = q := by

  induction N, hn using Nat.le_induction generalizing p q with
  | base =>
    simp at hp
    simp at hq
    grind
  | succ n hmn ih =>

    by_cases n_both: n ∈ p ∧ n ∈ q
    .
      have p_eq: p = (p \ {n}) ∪ {n} := by
        grind
      have q_eq: q = (q \ {n}) ∪ {n} := by
        grind
      rw [p_eq, q_eq] at hpq
      rw [Finset.sum_union] at hpq
      rw [Finset.sum_union] at hpq
      simp at hpq

      have diff_eq := ih (p \ {n}) (q \ {n}) (by
        intro c hc
        simp at hc
        have c_mem := hp hc.1
        simp
        simp at c_mem
        omega
      ) (by
        intro c hc
        simp at hc
        have c_mem := hq hc.1
        simp
        simp at c_mem
        omega
      ) hpq
      . grind
      . simp
      . simp
    .
      by_cases n_neither: n ∉ p ∧ n ∉ q
      .
        have p_eq: p = (p \ {n}) := by grind
        have q_eq: q = (q \ {n}) := by grind
        rw [p_eq, q_eq] at hpq
        have diff_eq := ih (p \ {n}) (q \ {n}) (by
          intro c hc
          simp at hc
          have c_mem := hp hc.1
          simp
          simp at c_mem
          omega
        ) (by
          intro c hc
          simp at hc
          have c_mem := hq hc.1
          simp
          simp at c_mem
          omega
        ) hpq
        grind
      .
        wlog n_mem_p: n ∈ p
        .
          have swapped := this A v N₀ N n hmn ih q p hq hp hpq.symm (by grind) (by grind) (by grind)
          exact swapped.symm
        .
          rw [not_and_or] at n_neither
          rw [not_and_or] at n_both

          have n_mem_or: n ∈ p ∨ n ∈ q := by
            grind

          clear n_mem_or n_neither
          simp [n_mem_p] at n_both

          have q_n_diff : q \ {n} = q := by grind
          have n_q_diff: {n} \ q = {n} := by grind
          have data := poly_cancel A v p q hpq
          have h_sum := data.h_prime
          have p_eq: p = (p \ {n}) ∪ {n} := by grind
          nth_rw 1 [p_eq] at h_sum
          rw [Finset.union_sdiff_distrib] at h_sum
          rw [Finset.sum_union] at h_sum
          simp [n_q_diff] at h_sum

          rw [add_comm] at h_sum
