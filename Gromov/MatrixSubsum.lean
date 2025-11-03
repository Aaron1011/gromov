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

  rw [← Finset.sdiff_union_inter (s := p) (t := q)] at hpq
  rw [Finset.sum_union] at hpq
  .
    have p_inter_subset : p ∩ q ⊆ q := by
      simp
    rw [←  Finset.sum_sdiff p_inter_subset] at hpq
    simp at hpq
    apply Exists.nonempty
    use {
      p' := p \ q
      q' := q \ p
      nontrivial := by
        simp
        grind
      h_prime := by
        exact hpq
      p'_derived := by
        simp
      q'_derived := by
        simp
      supp_disj := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        grind
    }
  . apply Finset.disjoint_sdiff_inter


  induction p using Finset.induction_on generalizing q with
  | empty =>
    simp at hp
  | insert a s ha ih =>

    by_cases s_subset: s ⊆ q
    .
      rw [Finset.sum_insert ha] at hpq

      apply Exists.nonempty
      use {
        p' := {a}
        q' := q \ s
        nontrivial := by simp
        h_prime := by
          simp
          rw [← Finset.sum_sdiff s_subset] at hpq
          simp at hpq
          exact hpq
        supp_disj := by
          rw [Finset.disjoint_iff_ne]
          intro b hb
          simp at hb
          intro c hc
          grind
        p'_derived := by
          simp
        q'_derived := by
          simp
      }
    .
      rw [Finset.not_subset] at s_subset
      by_cases a_mem_q: a ∈ q
      .
        rw [Finset.sum_insert] at hpq
        have orig_hpq := hpq
        conv at hpq =>
          rhs
          arg 1
          equals insert a (q \ {a}) =>
            grind
        simp [Finset.sum_insert] at hpq
        obtain ⟨b, b_mem, b_not_mem⟩ := hp
        obtain ⟨prev⟩ := ih (q \ {a}) (by exact hpq) (by grind)

        have s_not_mem_prev: a ∉ prev.p' := by
          have prev_p_subset := prev.p'_derived
          grind

        by_cases a_mem_prev_q': a ∈ prev.q'
        .
          have prev_prime := prev.h_prime

          apply Exists.nonempty
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
          apply Exists.nonempty
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
              grw [prev_derived]
              simp
          }
        . exact ha
      .
        rw [Finset.sum_insert ha] at hpq


        apply Exists.nonempty
        use {
          p' := {a} ∪ (s \ q)
          q' := q \ s
          nontrivial := by simp
          supp_disj := by
            rw [Finset.disjoint_iff_ne]
            intro b hb
            simp at hb
            intro c hc
            simp at hc
            obtain ⟨c_mem, c_not_mem_s⟩ := hc
            by_contra!
            cases hb
            . rename_i b_eq_a
              rw [← b_eq_a] at a_mem_q
              rw [this] at a_mem_q
              contradiction
            . rename_i b_mem_or
              cases b_mem_or
              . rename_i b_not_q
                rw [← this] at c_mem
                contradiction
          h_prime := by
            simp
            rw [Finset.sum_insert]

            rw [Finset.sum_sdiff]

            sorry
          p'_derived := by
            simp
          q'_derived := by
            simp
        }
        --rw [Finset.insert_eq] at hpq
       --rw [Finset.sum_insert a_mem_q] at hpq
        --rw [Finset.sum_insert] at hpq
        -- obtain ⟨b, hb, b_not_mem⟩ := hp
        -- simp at hb

        -- obtain ⟨prev⟩ := ih (q) (by sorry) (s_subset)
        -- apply Exists.nonempty
        -- use {
        --   p' := prev.p',
        --   q' := prev.q',
        --   nontrivial := by
        --     exact prev.nontrivial
        --     --simp
        --   supp_disj := by
        --     exact prev.supp_disj
        --     -- simp
        --     -- have prev_disj := prev.supp_disj
        --     -- have prev_q_derived := prev.q'_derived
        --     -- grind
        --   h_prime := by
        --     exact prev.h_prime
        --     -- have prev_h_prime := prev.h_prime
        --     -- rw [Finset.sum_insert]
        --     -- rw [prev_h_prime]
        --   p'_derived := by
        --     have prev_derived := prev.p'_derived
        --     grw [prev_derived]
        --     simp
        --   q'_derived := by
        --     have prev_derived := prev.q'_derived
        --     exact prev_derived
        -- }


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
