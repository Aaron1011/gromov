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

lemma interval_sum_le {d: ℕ} (A: Matrix (Fin d) (Fin d) ℤ) (v: (Fin d) → ℤ) (hv: ‖v‖ ≠ 0) (k: ℤ) (hk: 3 ≤ (k : ℝ)) (hva: A.mulVec v = k • v) (a b: ℕ):
    ∑ i ∈ Finset.Ico a b, ‖(A ^ i).mulVec v‖ < ‖(A ^ b).mulVec v‖ := by


  have mul_pow_exact: ∀ n: ℕ, ‖(A ^ n).mulVec v‖ = |k| ^ n * ‖v‖ := by
    intro n
    induction n with
    | zero =>
      simp
    | succ j ih =>
      rw [pow_succ]
      rw [← Matrix.mulVec_mulVec]
      rw [hva]
      rw [Matrix.mulVec_smul]
      rw [norm_smul]
      rw [ih]
      rw [Int.norm_eq_abs]
      norm_num
      ring

  have mul_pow: ∀ n: ℕ, 3 ^ n * ‖v‖ ≤ ‖(A ^ n).mulVec v‖ := by
    intro n
    induction n with
    | zero =>
      simp
    | succ j ih =>
      nth_rw 2 [pow_succ]
      rw [← Matrix.mulVec_mulVec]
      rw [hva]
      rw [Matrix.mulVec_smul]
      rw [norm_smul]
      rw [pow_succ']
      rw [mul_assoc]
      grw [ih]


      have three_le: 3 ≤ ‖k‖ := by
        grw [hk]
        norm_num
        rw [Int.norm_eq_abs]
        apply le_abs_self

      grw [three_le]

  by_cases b_le: b ≤ a
  .
    have ico_empty: Finset.Ico a b = ∅ := by
      simpa using b_le


    simp [ico_empty]
    by_contra!
    have norm_le := mul_pow b
    rw [this] at norm_le
    simp at norm_le
    rw [mul_nonpos_iff] at norm_le
    simp at norm_le
    cases norm_le
    . rename_i v_zero
      simp [v_zero] at hv
    . rename_i le_zero
      simp at le_zero
      rw [← Real.rpow_natCast] at le_zero
      have pow_pos := Real.rpow_pos_of_pos (x := 3) (by norm_num) b
      linarith
  .
    simp at b_le
    induction b, b_le using Nat.le_induction with
    | base =>
      simp
      rw [mul_pow_exact]
      rw [mul_pow_exact]
      simp
      rw [pow_succ]
      nth_rw 3 [mul_comm]
      rw [mul_assoc]
      nth_rw 2 [mul_comm]
      rw [lt_mul_iff_one_lt_right]
      .
        rw [lt_abs]
        grind
      . positivity
    | succ n hmn ih =>
      rw [Finset.sum_Ico_succ_top]
      rw [pow_succ]
      rw [← Matrix.mulVec_mulVec]
      rw [hva]
      rw [Matrix.mulVec_smul]
      rw [norm_smul]
      rw [mul_pow_exact]
      rw [Int.norm_eq_abs]
      ring
      nth_rw 2 [mul_comm]
      rw [← mul_assoc]
      norm_cast
      simp
      rw [← pow_succ']
      rw [mul_pow_exact] at ih
      apply_fun (fun x => x + |k| ^ n * ‖v‖) at ih
      .
        simp only [] at ih

        norm_cast at ih
        simp at ih
        grw [ih]
        rw [← two_mul]


        have two_lt_k: (2: ℝ) < |(k : ℝ)| := by
          norm_cast
          rw [lt_abs]
          norm_cast at hk
          left
          linarith



        have two_mul_le:  2 * (|↑k| ^ n * ‖v‖) < |↑k| * (|↑k| ^ n * ‖v‖) := by
          apply mul_lt_mul
          . exact two_lt_k
          . simp
          . positivity
          . positivity

        nth_rw 2 [← mul_assoc] at two_mul_le
        rw [← pow_succ'] at two_mul_le
        exact two_mul_le
      . simp
        intro a b hab
        simp
        exact hab
      . linarith

#print axioms interval_sum_le

set_option maxHeartbeats 3000000 in
lemma subsums_unique {d: ℕ} (A: Matrix (Fin d) (Fin d) ℤ) (v: (Fin d) → ℤ) (N₀ N: ℕ) (hv: ‖v‖ ≠ 0) (k: ℤ) (hk: 3 ≤ (k : ℝ))  (hva: A.mulVec v = k • v) (hn: N₀ ≤ N) (p q: Finset ℕ)
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
          have swapped := this A v N₀ N hv k hk hva n hmn ih q p hq hp hpq.symm (by grind) (by grind) (by grind)
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
          .
            simp [n_q_diff] at h_sum

            have q_diff_eq: q \ p = (q \ p) \ {n} := by
              grind

            rw [q_diff_eq] at h_sum
            rw [add_comm] at h_sum
            apply eq_add_neg_of_add_eq at h_sum
            apply_fun norm at h_sum



            have first_subset: (q \ p) \ {n} ⊆ Finset.Ico N₀ (n) := by
              intro a ha
              simp
              simp at ha
              have a_mem := hq ha.1.1
              simp at a_mem
              grind

            have second_subset: (p \ {n}) \ q ⊆ Finset.Ico N₀ n := by
              intro a ha
              simp
              simp at ha
              have a_mem := hp ha.1.1
              simp at a_mem
              grind

            have a_pow_le: ‖(A ^ n).mulVec v‖ < ‖(A ^ n).mulVec v‖ := by
              nth_rw 1 [h_sum]
              rw [← Finset.sum_indicator_subset _ first_subset]
              rw [← Finset.sum_indicator_subset _ second_subset]
              rw [← sub_eq_add_neg]
              rw [← Finset.sum_sub_distrib]
              grw [norm_sum_le]
              grw [Finset.sum_le_sum (g := (fun x ↦ ‖(A ^ x).mulVec v‖))]
              .
                apply interval_sum_le (k := k)
                . exact hv
                . exact hk
                . exact hva

              . intro a ha
                simp [Set.indicator]
                split
                . rename_i a_mem_q
                  split
                  . rename_i a_mem_other
                    simp
                  . simp
                . split
                  . simp
                  . simp

            simp at a_pow_le









              -- have first_diff := Finset.sum_sdiff (f := fun n => (A^n).mulVec v) first_subset
              -- simp at first_diff


              -- rw [← Finset.sum_sdiff first_subset]




              -- grw [abs_add_le]
              -- simp
              -- have first_subset: q \ p ⊆ ()
              -- rw [Finset.sum_subset]
              -- rw [neg_eq_neg_one_mul]
              -- rw [Finset.mul_sum]
              -- rw [← Finset.sum_union]

              -- rw [← Finset.sum_sdiff_eq_sub]
              -- . sorry
              -- . intro a ha
              --   simp
              --   simp at ha
              --   have first := ha.1.1
              --   have second := ha.2
              --   grind
              -- sorry


          .
            rw [Finset.disjoint_iff_ne]
            intro a ha b hb
            grind

#print axioms subsums_unique
