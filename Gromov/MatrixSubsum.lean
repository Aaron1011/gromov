import Mathlib

open scoped Finset
open scoped Pointwise

structure DerivedSets {R: Type*} [NormedCommRing R] {n: ℕ} (A: Matrix (Fin n) (Fin n) R) (v : (Fin n) → R) (p q : Finset ℕ) where
  h_prime: (p \ q).sum (fun k => A^k • v) = (q \ p).sum (fun k => A^k • v)
  supp_disj: Disjoint (p \ q) (q \ p)


def poly_cancel  {R: Type*} [NormedCommRing R] {n: ℕ} (A: Matrix (Fin n) (Fin n) R) (v: (Fin n) → R) (p q : Finset ℕ) (hpq: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)) : DerivedSets A v p q := ({
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

lemma mul_pow_exact {d: ℕ} {R: Type*} [RCLike R] [NormSMulClass R ((Fin d) → R)]   (A: Matrix (Fin d) (Fin d) R) (v: (Fin d) → R) (k: R)  (hva: A.mulVec v = k • v): ∀ n: ℕ, (A ^ n).mulVec v = (k ^ n) • v := by
  intro n
  induction n with
  | zero =>
    simp
  | succ j ih =>
    rw [pow_succ]
    rw [← Matrix.mulVec_mulVec]
    rw [hva]
    rw [Matrix.mulVec_smul]
    rw [ih]
    rw [pow_succ']
    ring_nf
    rw [mul_smul]


lemma interval_sum_le {R: Type*} {d: ℕ} [RCLike R] [ NormSMulClass R (Fin d → R)] (A: Matrix (Fin d) (Fin d) R) (v: (Fin d) → R) (hv: ‖v‖ ≠ 0) (k: R) (hk: 3 ≤ ‖k‖) (hva: A.mulVec v = k • v) (a b: ℕ):
    ∑ i ∈ Finset.Ico a b, ‖(A ^ i).mulVec v‖ < ‖(A ^ b).mulVec v‖ := by




  have mul_pow: ∀ n: ℕ, 3 ^ n * ‖v‖ ≤ ‖(A ^ n).mulVec v‖ := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, one_mul, Matrix.one_mulVec, le_refl]
    | succ j ih =>
      nth_rw 2 [pow_succ]
      rw [← Matrix.mulVec_mulVec]
      rw [hva]
      rw [Matrix.mulVec_smul]
      rw [norm_smul]
      rw [pow_succ']
      rw [mul_assoc]
      grw [ih]
      grw [hk]

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
      rw [← Real.rpow_natCast] at le_zero
      have pow_pos := Real.rpow_pos_of_pos (x := 3) (by norm_num) b
      linarith
  .
    simp at b_le
    induction b, b_le using Nat.le_induction with
    | base =>
      simp
      rw [mul_pow_exact A v k hva]
      rw [mul_pow_exact A v k hva]
      rw [pow_succ]
      rw [mul_smul]
      rw [norm_smul]
      rw [norm_smul]
      rw [norm_smul]
      rw [← mul_assoc]
      rw [mul_lt_mul_iff_left₀]
      rw [lt_mul_iff_one_lt_right]
      .
        linarith
      . simp
        positivity
      . simpa using hv
    | succ n hmn ih =>
      rw [Finset.sum_Ico_succ_top]
      rw [pow_succ]
      rw [← Matrix.mulVec_mulVec]
      rw [hva]
      rw [Matrix.mulVec_smul]
      rw [norm_smul]
      rw [mul_pow_exact A v k hva]
      -- ring
      -- nth_rw 2 [mul_comm]
      -- rw [← mul_assoc]
      norm_cast
      -- simp
      -- rw [mul_assoc]

      --rw [← pow_succ']
      rw [mul_pow_exact A v k hva] at ih
      apply_fun (fun x => x + ‖k‖ ^ n * ‖v‖) at ih
      .
        simp only [] at ih

        norm_cast at ih
        simp at ih
        grw [ih]
        rw [← two_mul]


        have two_lt_k: (2: ℝ) < ‖k‖:= by
          linarith



        have two_mul_le:  2 * (‖k‖ ^ n * ‖v‖) < ‖k‖  * (‖k‖  ^ n * ‖v‖) := by
          apply mul_lt_mul
          . exact two_lt_k
          . simp
          . positivity
          . positivity

        nth_rw 2 [← mul_assoc] at two_mul_le
        rw [← pow_succ'] at two_mul_le
        exact mul_le_mul_of_nonneg_right two_lt_k.le (norm_nonneg _)
      .
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

-- TODO - this can probably be generalized to any matrix with a determinant of +/- 1,
-- and then upstreamed to mathlib
lemma int_matrix_eigenvalue {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ):
    (∀ (k : ℂ), Module.End.HasEigenvalue ((A.val.map (Int.castRingHom ℂ)).toLin') k → ‖k‖ = 1) ∨ (∃ (k: ℂ), (Module.End.HasEigenvalue ((A.val.map (Int.castRingHom ℂ)).toLin') k) ∧ 1 < ‖k‖) := by

  rw [Classical.or_iff_not_imp_left]
  intro not_all_one
  simp at not_all_one



  obtain ⟨k, hk, hk_not_one⟩ := not_all_one
  -- wlog norm_k_gt: ‖k‖ < 1
  -- .

  --   have foo := this A⁻¹ v k⁻¹ ?_ (by simpa using hk_not_one) ?_
  --   .
  --     obtain ⟨j, hj, j_norm⟩ := foo
  --     use j⁻¹
  --     refine ⟨?_, ?_⟩
  --     . sorry
  --     . simp

  --     exact foo
  --   .

  --     apply Module.End.HasEigenvalue.exists_hasEigenvector at hk
  --     obtain ⟨v, hv, v_nonzero⟩ := hk
  --     simp at hv
  --     apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  --     rw [Module.End.hasEigenvector_iff]
  --     simp

  --     sorry
    -- .
    --   simp
    --   rw [inv_lt_one₀]
    --   . grind
    --   . grind
  .

    --
    have a_det_unit := Matrix.isUnits_det_units A
    rw [Int.isUnit_iff] at a_det_unit
    let A_C := A.val.map (Int.castRingHom ℂ)
    have det_eq := Matrix.det_eq_prod_roots_charpoly A_C
    have foo := Matrix.charpoly_map A.val (Int.castRingHom ℂ)

    have char_nonzero: A_C.charpoly ≠ 0 := by
      by_contra!
      simp [A_C, Int.castRingHom] at this
      have char_monic := Matrix.charpoly_monic A_C
      simp [A_C, Int.castRingHom] at char_monic
      apply Polynomial.Monic.ne_zero at char_monic
      contradiction


    by_cases k_gt: 1 < ‖k‖
    . use k
      simp
      refine ⟨hk, k_gt⟩

    simp at k_gt
    have k_lt: ‖k‖ < 1 := by
      grind


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

          have det_nonzero :=  Matrix.det_ne_zero_of_left_inverse (A := A_C) (B := (A.inv).map (Int.castRingHom ℂ)) ?_
          . contradiction
          .
            simp [-Matrix.coe_units_inv, A_C, -Int.coe_castRingHom]
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
      simp [A_C, Int.castRingHom] at det_eq
      rw [det_eq_one] at det_eq
      --simp [Int.castRingHom] at roots_prod_le
      rw [← det_eq] at roots_prod_le
      norm_num at roots_prod_le
    . rename_i det_eq_neg_one
      apply_fun (fun a => (a: ℂ)) at det_eq_neg_one
      rw [cast_det] at det_eq_neg_one
      simp [A_C, Int.castRingHom] at det_eq
      rw [det_eq_neg_one] at det_eq
      rw [← det_eq] at roots_prod_le
      norm_num at roots_prod_le


#print axioms int_matrix_eigenvalue

set_option maxHeartbeats 1200000 in
lemma subsums_unique {d: ℕ} (A: Matrix (Fin d) (Fin d) ℂ) (v: (Fin d) → ℂ) (N₀ N: ℕ) (hv: ‖v‖ ≠ 0) (k: ℂ) (hk: 3 ≤ ‖k‖)  (hva: A.mulVec v = k • v) (hn: N₀ ≤ N) (p q: Finset ℕ)
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

lemma int_matrix_exponential_growth {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℂ)ˣ) (v: (Fin d) → ℂ) (v_ne_zero: ‖v‖ ≠ 0) (k: ℂ) (hv: A.val.mulVec v = k • v) (k_gt: 1 < ‖k‖):
    ∃ N₀, ∀ N, 2^(N - N₀) ≤ #((Finset.image (fun a => a.sum (fun b => (((A^(N₀))).val^b.val).mulVec v)) ((Finset.Ico N₀ N)).attach.powerset)) := by
  have mul_v := mul_pow_exact A.val v k hv

  have pow_le: 3 ≤ ‖k‖^(Nat.ceil (Real.logb ‖k‖ 3)) := by
    rw [Real.le_pow_iff_log_le]
    rw [← div_le_iff₀]
    .
      rw [← Real.log_div_log]
      exact Nat.le_ceil (Real.log 3 / Real.log ‖k‖)
    . apply Real.log_pos
      grind
    . simp
    . linarith

  use (Nat.ceil (Real.logb ‖k‖ 3))
  intro N
  by_cases N_le: N ≤ Nat.ceil (Real.logb ‖k‖ 3)
  .
    simp [N_le]
    apply Finset.powerset_nonempty
  simp at N_le
  rw [Finset.card_image_of_injective]
  .
    simp
  .
    intro a b hab

    have mul_one := mul_v 1
    simp at mul_one

    have sums_eq := subsums_unique (A^(⌈Real.logb ‖k‖ 3⌉₊)) (v) (Nat.ceil (Real.logb ‖k‖ 3)) N (by
      simpa using v_ne_zero
      -- refine ⟨?_, by simpa using v_ne_zero⟩
      -- intro k_zero
      -- simp [k_zero] at k_gt
      -- norm_num at k_gt
    ) (k^(Nat.ceil (Real.logb ‖k‖ 3))) (by simp [pow_le]) (by
      simp
      rw [mul_v]
    ) (by omega) (a.image Subtype.val) (b.image Subtype.val) ?_ ?_ ?_
    . rw [Finset.image_inj] at sums_eq
      . exact sums_eq
      . simp
    .
      intro x hx
      simp at hx
      rw [Finset.mem_Ico]
      obtain ⟨⟨le_x, other⟩, hy⟩ := hx
      refine ⟨?_, by omega⟩
      simp
      exact le_x
    .
      intro x hx
      simp at hx
      rw [Finset.mem_Ico]
      obtain ⟨⟨le_x, other⟩, hy⟩ := hx
      refine ⟨?_, by omega⟩
      simp
      exact le_x
    . simp
      simp at hab
      exact hab

#print axioms int_matrix_exponential_growth


lemma map_preserves_eigen {F: Type*} {d: ℕ} [Field F] [FiniteDimensional F ((Fin d → F))] {d: ℕ} (A: (Matrix (Fin d) (Fin d) F)) (f: F →+* ℂ): ∀ k: Module.End.Eigenvalues A.toLin', Module.End.HasEigenvalue (A.map f).toLin' (f k) := by
  intro k
  have hk := k.prop
  obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hk
  have v_spec := hv
  rw [Module.End.hasEigenvector_iff] at v_spec
  apply Module.End.HasEigenvector.apply_eq_smul at hv
  let map_vec := fun (j: (Fin d) → F) => (fun (i: Fin d) => f (j i))
  apply_fun map_vec at hv
  simp [map_vec] at hv
  rw [funext_iff] at hv
  simp_rw [RingHom.map_mulVec] at hv
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := f ∘ v)
  rw [Module.End.hasEigenvector_iff]
  simp
  refine ⟨?_, ?_⟩
  . ext j
    rw [hv]
    simp
    left
    rfl
  .
    rw [funext_iff]
    simp_rw [Function.comp_apply, Pi.zero_apply, map_eq_zero]
    rw [← funext_iff]
    exact v_spec.2



lemma int_matrix_poly_growth_eigenvalue {d p: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ)
  (a b : ℕ)
  (h_poly: ∀ v, ∀ N_1 , ∃ N_2, #((Finset.image (fun a => a.sum (fun b => ((((A.val.map (Int.castRingHom ℂ))^(N_1)))^b.val).mulVec v)) ((Finset.Ico N_1 N_2)).attach.powerset)) ≤ a * b^(2*(N_2 - N_1))):
  ∀ k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin', ‖k.val‖ = 1 := by

    cases int_matrix_eigenvalue A
    .
      rename_i eigen_norm_one
      intro k
      apply eigen_norm_one k k.property
    .
      rename_i gt_one
      obtain ⟨k, kh, one_lt_k⟩ := gt_one
      apply Module.End.HasEigenvalue.exists_hasEigenvector at kh
      obtain ⟨v, hv⟩ := kh
      rw [Module.End.hasEigenvector_iff] at hv
      have map_v := hv.1
      simp at map_v

      have foo := int_matrix_exponential_growth (d := d)
        (A.map ((Int.castRingHom ℂ).mapMatrix (m := Fin d))) v (by simpa using hv.2) k (by simpa using map_v)
        one_lt_k



      obtain ⟨N, hN⟩ := foo
      specialize h_poly v N
      obtain ⟨N_2, card_le⟩ := h_poly
      specialize hN N_2





      sorry

theorem LinearMap.toMatrix'_pow {R : Type*} [CommSemiring R] {m : Type*} [Fintype m] [DecidableEq m] (f : (m → R) →ₗ[R] m → R) (n: ℕ):
    LinearMap.toMatrix' (f^n) = (LinearMap.toMatrix' f)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rw [LinearMap.toMatrix'_mul]
    rw [pow_succ]
    rw [ih]


lemma int_matrix_unipotent {d: ℕ} (hd: 0 < d) (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1): ∃ a m, 0 < a ∧ (A.val^a - 1)^m = 0 := by
  classical
  let A_C := (A.val.map (Int.castRingHom ℂ ))

  have char_nonzero: A_C.charpoly ≠ 0 := by
    by_contra!
    have monic := A_C.charpoly_monic
    simp [this] at monic

  have eigen_nonzero: ∀ (k : Module.End.Eigenvalues A_C.toLin'), k.val ≠ 0 := by
    intro k
    by_contra!
    have eigen_zero := LinearMap.hasEigenvalue_zero_tfae (A_C.toLin')
    have det_zero := (eigen_zero.out 0 3).mp
    have has_k := k.prop
    conv at has_k =>
      lhs
      equals k.val => rfl

    simp [this] at has_k
    specialize det_zero has_k
    have a_det := Matrix.GeneralLinearGroup.det_ne_zero A
    unfold A_C at det_zero
    simp at det_zero
    conv at det_zero =>
      lhs
      arg 1
      equals (A.val).map (Int.castRingHom ℂ) =>
        simp
    rw [← RingHom.mapMatrix_apply] at det_zero
    simp at det_zero
    apply_fun (fun a => (Int.castRingHom ℂ) a) at a_det
    . conv at a_det =>
        rhs
        simp
      rw [RingHom.map_det] at a_det
      simp at a_det
      contradiction
    . simp
      exact Int.cast_injective

  have eigen_root_unity: ∀ (k : Module.End.Eigenvalues A_C.toLin'), ∃ n, 0 < n ∧ k.val^n = 1 := by
    intro k
    have k_prop := k.property
    conv at k_prop =>
      equals Module.End.HasEigenvalue A_C.toLin' (↑k) =>
        rfl
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at k_prop



    have k_mem_roots: ↑k.val ∈ A_C.toLin'.charpoly.rootSet ℂ := by
      simp at k_prop
      simp [Polynomial.mem_rootSet]
      refine ⟨char_nonzero, ?_⟩
      exact k_prop

    have foo := Polynomial.pow_eq_one_of_mahlerMeasure_eq_one ?_ ?_ ?_ (z := (k.val : ℂ)) (p := A.val.charpoly)
    . obtain ⟨n, hn, z_pow⟩ := foo
      use n
    .
      rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
      rw [Polynomial.Monic.leadingCoeff]
      .
        simp
        apply Multiset.prod_eq_one
        intro x hx
        simp at hx
        obtain ⟨a, ⟨charpoly_nonzero, a_root⟩, x_eq⟩ := hx
        rw [← x_eq]
        simp
        apply le_of_eq
        apply eigen_one_complex ⟨a, ?_⟩
        conv =>
          equals Module.End.HasEigenvalue A_C.toLin' a => rfl
        rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
        simp
        simp [A_C]
        rw [← Matrix.charpoly_map] at a_root
        simpa using a_root

      . apply Polynomial.Monic.map
        apply Matrix.charpoly_monic

    . apply eigen_nonzero
    . simp
      simp [A_C] at char_nonzero
      refine ⟨?_, ?_⟩
      .
        rw [← Matrix.charpoly_map]
        exact char_nonzero
      .
        rw [← Matrix.charpoly_map]
        rw [Polynomial.mem_rootSet] at k_mem_roots
        have foo := k_mem_roots.2
        simp at foo
        simp [A_C] at foo
        exact foo



  let eigen_pow (k: ℂ) (hk: Module.End.HasEigenvalue A_C.toLin' k) := (eigen_root_unity ⟨k, hk⟩).choose
  have eigen_pow_self (k: ℂ) (hk: Module.End.HasEigenvalue A_C.toLin' k): k^(eigen_pow k hk) = 1 := by
    have spec := (eigen_root_unity ⟨k, hk⟩).choose_spec
    obtain ⟨_, pow_eq⟩ := spec
    rw [← pow_eq]
    rfl

  let n_prod := ∏ (k : Module.End.Eigenvalues A_C.toLin'), eigen_pow k.val k.prop
  have n_prod_pos: 0 < n_prod := by
    simp [n_prod]
    intro k
    by_contra!
    simp at this
    have k_pow := eigen_pow_self k.val k.prop
    have pow_nonzero: eigen_pow k.val k.prop ≠ 0 := by
      have spec :=  (eigen_root_unity ⟨k.val, k.prop⟩).choose_spec
      grind [spec.1]

    grind

  have eigen_pow_prod_one: ∀ k:  Module.End.Eigenvalues A_C.toLin', k.val^n_prod = 1 := by
    intro k
    unfold n_prod
    rw [← Finset.mul_prod_erase (f := fun (a: Module.End.Eigenvalues (Matrix.toLin' A_C)) => eigen_pow a.val a.prop) (a := ⟨k.val, k.prop⟩)]
    .
      rw [pow_mul]
      have pow_self := eigen_pow_self (k := k.val) (hk := k.prop)
      simp
      rw [pow_self]
      simp
    . apply Finset.mem_univ

  have pow_eigen: ∀ j: Module.End.Eigenvalues (A_C.toLin'^n_prod), j.val = 1 := by
    intro a
    have a_spec := a.prop
    conv at a_spec =>
      equals Module.End.HasEigenvalue (A_C.toLin' ^ n_prod) (↑a) => rfl
    rw [Module.End.hasEigenvalue_iff_mem_spectrum] at a_spec
    simp_rw [← Matrix.toLin'_pow] at a_spec
    simp [-Matrix.toLin'_pow] at a_spec
    rw [spectrum.map_pow_of_pos _ n_prod_pos] at a_spec
    simp at a_spec
    obtain ⟨k, k_mem, k_pow⟩ := a_spec
    simp [Module.End.UnifEigenvalues.val] at k_pow
    conv at k_pow =>
      rhs
      equals Module.End.Eigenvalues.val _ a => rfl

    rw [← k_pow]
    rw [← Matrix.spectrum_toLin'] at k_mem
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at k_mem
    have k_norm := eigen_one_complex ⟨k, k_mem⟩
    rw [← eigen_pow_prod_one (k := ⟨k, k_mem⟩)]
    . simp

  have char_nonzero: (A_C.toLin' ^ n_prod).charpoly ≠ 0 := by
    by_contra!
    have foo := (A_C.toLin'^n_prod).charpoly_monic
    simp [this] at foo



  have a_f_char_eq: (A_C.toLin'^n_prod).charpoly = (Polynomial.X - (Polynomial.C 1))^d := by
    rw [Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (p := (Polynomial.X - Polynomial.C 1) ^ d) (q :=  (A_C.toLin'^n_prod).charpoly)]
    .
      rw [Polynomial.Monic.def.mp]
      . simp
      . exact LinearMap.charpoly_monic (A_C.toLin' ^ n_prod)
    . simp
      apply Polynomial.Monic.pow
      apply Polynomial.monic_X_sub_C
    .
      have roots_singleton: (A_C.toLin' ^ n_prod).charpoly.roots.toFinset = {1} := by
        ext a
        simp only [Multiset.mem_toFinset]
        rw [Polynomial.mem_roots']
        simp [-Polynomial.IsRoot.def, char_nonzero]
        rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly]
        refine ⟨?_, ?_⟩
        . intro ha
          specialize pow_eigen ⟨_, ha⟩
          simpa using pow_eigen
        . intro ha

          have ne_zero: NeZero d := by
            apply NeZero.mk
            grind


          obtain ⟨k, hk⟩ := Module.End.exists_eigenvalue (A_C.toLin')
          have k_pow_prod: k^n_prod = 1 := by
            rw [← eigen_pow_prod_one (k := ⟨k, hk⟩)]
            simp

          rw [ha, ← k_pow_prod]
          apply Module.End.HasEigenvalue.pow
          exact hk

      rw [← Polynomial.le_rootMultiplicity_iff]

      .
        rw [← Polynomial.count_roots]
        rw [Multiset.toFinset_eq_singleton_iff] at roots_singleton
        rw [roots_singleton.2]
        simp

        rw [← Polynomial.Splits.natDegree_eq_card_roots]
        .
          rw [LinearMap.charpoly_natDegree]
          simp
        .
          apply IsAlgClosed.splits
      . by_contra!
        have monic := (A_C.toLin'^n_prod).charpoly_monic
        simp [this] at monic
    .
      simp only [Polynomial.natDegree_pow]
      rw [Polynomial.natDegree_X_sub_C]
      simp
      rw [LinearMap.charpoly_natDegree]
      simp


  use n_prod
  have eval_zero := (A_C.toLin'^n_prod).aeval_self_charpoly
  simp [a_f_char_eq] at eval_zero
  use d
  refine ⟨n_prod_pos, ?_⟩
  simp [A_C] at eval_zero
  apply_fun (fun f => f.toMatrix') at eval_zero
  simp [-EmbeddingLike.map_eq_zero_iff] at eval_zero
  rw [← Matrix.toLin'_pow] at eval_zero
  rw [LinearMap.toMatrix'_pow] at eval_zero
  rw [sub_eq_add_neg, LinearEquiv.map_add] at eval_zero
  rw [LinearMap.toMatrix'_toLin'] at eval_zero
  simp at eval_zero
  apply_fun (fun m => m.map (Int.castRingHom ℂ))
  . simp [-Int.coe_castRingHom]
    rw [Matrix.map_pow]
    rw [Matrix.map_sub]
    .
      rw [sub_eq_add_neg]
      rw [Matrix.map_pow]
      simp
      exact eval_zero
    . simp
  . intro a b hab
    simp at hab
    apply Matrix.map_injective at hab
    .
      exact hab
    . exact Int.cast_injective


#print axioms int_matrix_unipotent
#print axioms int_matrix_poly_growth_eigenvalue

def homToComplex  {d: ℕ} (g: ((Fin d) → ℤ) ≃+ ((Fin d) → ℤ)) := (g.toAddMonoidHom.toIntLinearMap).toMatrix'.map complexOfIntHom

open scoped Pointwise Finset

-- TODO - this is probably wrong
lemma hom_poly_growth {d: ℕ} [DecidableEq ((AddAut ((Fin d) → ℤ)))] (S: Finset (AddAut ((Fin d) → ℤ))) {p: ℕ}
  (hS: ∃ a, ∀ n ≥ 1, #(n • S) ≤ a * n^p): False := by

  let S' := S.image (fun g => homToComplex g)
  sorry


  -- rw [← ge_iff_le]
  -- grw [(Finset.card_le_card (s := Finset.image (fun (n : Set.Ico ((Nat.ceil (Real.logb ‖k‖ 3))) N) => (A.val^(n.val)).mulVec v) Finset.univ) ?_).ge]
  -- .
  --   simp
  --   rw [Finset.card_image_of_injective]
  --   . simp
  --   have card_le := Finset.card_le_card_of_injective (f := (fun (n : Set.Ico ((Nat.ceil (Real.logb ‖k‖ 3))) N) => (A.val^(n.val)).mulVec v))
  --   sorry
  -- .
  --   intro a ha
  --   simp at ha
  --   simp
  --   obtain ⟨n, hn, other⟩ := ha
  --   use ⟨n, by omega⟩
