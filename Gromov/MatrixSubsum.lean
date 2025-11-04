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


theorem hasEigenvalue_of_isRoot_min  {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : Module.End R M} {μ : R} [IsDomain R] [Module.Finite R M] (h : (minpoly R f).IsRoot μ) : f.HasEigenvalue μ := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr h
  obtain ⟨v, hv⟩ : ∃ v : M, q.aeval f v ≠ 0 := by
    by_contra! h_contra
    have := minpoly.min R f
      ((Polynomial.monic_X_sub_C μ).of_mul_monic_left (hq ▸ minpoly.monic (Algebra.IsIntegral.isIntegral f)))
      (LinearMap.ext h_contra)
    rw [hq, Polynomial.degree_mul, Polynomial.degree_X_sub_C, Polynomial.degree_eq_natDegree] at this
    · norm_cast at this; grind
    · rintro rfl
      exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral f) (mul_zero (Polynomial.X - Polynomial.C μ) ▸ hq)
  refine Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.mpr ⟨?_, hv⟩)
  apply_fun (fun a => (Polynomial.aeval f) a) at hq
  simp
  simpa [sub_eq_zero, hq] using congr($(minpoly.aeval R f) v)

-- TODO - upstream to mathlib
theorem hasEigenvalue_of_isRoot_charpoly  {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : Module.End R M} {μ : R} [IsDomain R] [Module.Finite R M] [Module.Free R M] (h : (f.charpoly).IsRoot μ) : f.HasEigenvalue μ := by
  simp at h
  rw [LinearMap.eval_charpoly] at h
  have nontrivial_ker := LinearMap.bot_lt_ker_of_det_eq_zero h
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h
  apply Submodule.exists_mem_ne_zero_of_ne_bot at h
  obtain ⟨v, v_mem, v_nonzero⟩ := h
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  rw [Module.End.hasEigenvector_iff]
  simp
  simp at v_mem
  rw [sub_eq_zero] at v_mem
  rw [eq_comm] at v_mem
  refine ⟨v_mem, v_nonzero⟩

-- TODO - upstream to mathlib
def complexOfIntHom: ℤ →+* ℂ := {
  toFun := fun z => (z: ℂ),
  map_zero' := by simp,
  map_one' := by simp,
  map_add' := by intros; simp,
  map_mul' := by intros; simp
}

-- TODO - an integer matrix might not have integer eigenvalues, so this statement is probably wrong
lemma int_matrix_eigenvalue {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (v: (Fin d) → ℤ):
    (∀ (k : ℂ), Module.End.HasEigenvalue ((A.val.map complexOfIntHom).toLin') k → ‖k‖ = 1) ∨ (∃ (k: ℂ), (Module.End.HasEigenvalue ((A.val.map complexOfIntHom).toLin') k) ∧ 1 < ‖k‖) := by

  rw [Classical.or_iff_not_imp_left]
  intro not_all_one
  simp at not_all_one



  obtain ⟨k, hk, hk_not_one⟩ := not_all_one
  wlog norm_k_gt: ‖k‖ < 1
  .

    have foo := this A⁻¹ v k sorry
    sorry
  .

    --
    have a_det_unit := Matrix.isUnits_det_units A
    rw [Int.isUnit_iff] at a_det_unit
    let A_C := A.val.map complexOfIntHom
    have det_eq := Matrix.det_eq_prod_roots_charpoly A_C
    have foo := Matrix.charpoly_map A.val complexOfIntHom

    have char_nonzero: A_C.charpoly ≠ 0 := by
      by_contra!
      simp [A_C, complexOfIntHom] at this
      have char_monic := Matrix.charpoly_monic A_C
      simp [A_C, complexOfIntHom] at char_monic
      apply Polynomial.Monic.ne_zero at char_monic
      contradiction

    by_contra! eigenvalues_le_one

    have roots_prod_le: ‖A_C.charpoly.roots.prod‖ < 1 := by
      rw [Multiset.prod_eq_prod_toEnumFinset]
      rw [Complex.norm_prod]
      conv =>
        rhs
        equals ∏ i ∈ A_C.charpoly.roots.toEnumFinset, 1 =>
          simp

      apply Finset.prod_lt_prod
      .
        intro i hi
        simp at hi
        have is_root := (Polynomial.rootMultiplicity_pos (p := A_C.charpoly) ?_ (x := i.1)).mp (by omega)
        .
          by_contra!
          simp at this

          have eval_char := Matrix.eval_charpoly A_C i.1
          rw [Polynomial.IsRoot.def] at is_root
          rw [is_root] at eval_char
          simp [this] at eval_char
          rw [Matrix.det_neg] at eval_char
          simp at eval_char

          have det_nonzero :=  Matrix.det_ne_zero_of_left_inverse (A := A_C) (B := (A.inv).map complexOfIntHom) ?_
          . contradiction
          .
            simp [-Matrix.coe_units_inv, A_C]
            rw [← Matrix.map_mul]
            simp
        .
          apply char_nonzero
      . intro i hi
        simp at hi
        have is_root := (Polynomial.rootMultiplicity_pos (p := A_C.charpoly) ?_ (x := i.1)).mp (by omega)
        .
          rw [← Matrix.charpoly_toLin'] at is_root
          have i_eigen := hasEigenvalue_of_isRoot_charpoly is_root
          exact eigenvalues_le_one i.1 i_eigen

        . apply char_nonzero
        -- hasEigenvalue_of_isRoot_charpoly
      .
        have k_root := Module.End.isRoot_of_hasEigenvalue hk
        have min_poly_div := Matrix.minpoly_dvd_charpoly A_C
        use (k, 0)
        simp
        refine ⟨?_, ?_⟩
        .
          refine ⟨?_, ?_⟩
          .
            exact char_nonzero
          .
            simp at k_root
            have root_char := Polynomial.IsRoot.dvd k_root min_poly_div
            simp at root_char
            exact root_char
        . norm_cast


    simp [A_C] at roots_prod_le

    have cast_det := Int.cast_det A.val (R := ℂ)
    -- TODO - this can be way simpler
    cases a_det_unit
    . rename_i det_eq_one
      apply_fun (fun a => (a: ℂ)) at det_eq_one
      rw [cast_det] at det_eq_one
      simp [A_C, complexOfIntHom] at det_eq
      rw [det_eq_one] at det_eq
      simp [complexOfIntHom] at roots_prod_le
      rw [← det_eq] at roots_prod_le
      norm_num at roots_prod_le
    . rename_i det_eq_neg_one
      apply_fun (fun a => (a: ℂ)) at det_eq_neg_one
      rw [cast_det] at det_eq_neg_one
      simp [A_C, complexOfIntHom] at det_eq
      rw [det_eq_neg_one] at det_eq
      simp [complexOfIntHom] at roots_prod_le
      rw [← det_eq] at roots_prod_le
      norm_num at roots_prod_le



    -- Matrix.eval_charpoly

    --rw [← Matrix.charpoly_toLin'] at det_eq

    --sorry

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
