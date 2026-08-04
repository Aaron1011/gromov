import Mathlib
import Gromov.MatrixSubsum.Subsums

/-!
# Eigenvalues of integer matrices and unipotence

That an integer matrix whose orbit grows polynomially has all eigenvalues of norm `1`, and is
therefore unipotent after passing to a power.

Root of the `Gromov.MatrixSubsum` hierarchy.
-/

open scoped Finset
open scoped Pointwise

lemma exists_vector_component_nonzero {d: ℕ} (v: (Fin d) → ℂ) (hv: v ≠ 0): ∃ i, v i ≠ 0 := by
  by_contra!
  simp at hv
  rw [funext_iff] at hv
  simp [this] at hv

lemma int_matrix_poly_growth_eigenvalue {d: ℕ} [NeZero d] (A: (Matrix (Fin d) (Fin d) ℤ)ˣ)
  (h_poly: ∀ k: ℂ, 1 < ‖k‖ → ∀ v: (Fin d) → ℤ, ∃ a b N_2: ℕ, (0 < a) ∧ ((Nat.ceil (Real.logb ‖k‖ 3)) < N_2) ∧ (4 * ↑b + Real.log ↑a < (Real.log 2) * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^((1 : ℝ) / 2)) ∧ #((Finset.image (fun a => a.sum (fun b => ((((A.val)^((Nat.ceil (Real.logb ‖k‖ 3)))))^b.val).mulVec (v))) ((Finset.Ico (Nat.ceil (Real.logb ‖k‖ 3)) N_2)).attach.powerset)) ≤ a * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^(2*b)):
  ∀ k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin', ‖k.val‖ = 1 := by


    cases int_matrix_eigenvalue A
    .
      intro k
      rename_i eigen_norm_one
      apply eigen_norm_one k k.property
    .

      rename_i gt_one
      obtain ⟨k, hk, one_lt_k⟩ := gt_one

      have k_eigen := hk
      rw [Module.End.hasEigenvalue_iff_mem_spectrum] at k_eigen
      simp at k_eigen
      rw [spectrum.mem_iff] at k_eigen
      rw [Matrix.isUnit_iff_isUnit_det] at k_eigen
      simp at k_eigen
      rw [← Matrix.exists_vecMul_eq_zero_iff] at k_eigen
      obtain ⟨v, v_nonzero, hv⟩ := k_eigen
      rw [Matrix.vecMul_sub] at hv
      conv at hv =>
        lhs
        lhs
        equals Matrix.vecMul v (Matrix.diagonal (fun _ => k)) =>
          ext a
          simp
          rw [Matrix.algebraMap_eq_diagonal]
          rw [Matrix.vecMul_diagonal]
          simp

      simp at hv
      rw [sub_eq_zero] at hv
      obtain ⟨q, hq⟩ := exists_vector_component_nonzero v v_nonzero

      have mul_dot: (v ⬝ᵥ (A.val.map (Int.castRingHom ℂ)).mulVec q) = (k • v) ⬝ᵥ q  := by
        rw [Matrix.dotProduct_mulVec]
        simp
        rw [← hv]
        simp


      have hN := int_matrix_exponential_growth (d := d)
        (A.val) v (Pi.single q 1) (by
          simp
          conv =>
            arg 1
            lhs
            rhs
            equals Pi.single q 1 =>
              ext a
              simp [Pi.single_apply]
          simp
          exact hq
        ) k (by exact hv.symm)
        one_lt_k


      specialize h_poly k one_lt_k (Pi.single q 1)
      obtain ⟨a, b, N_2, ha, N_2_gt, N_2_diff_gt, card_le⟩ := h_poly
      specialize hN N_2
      simp at hN
      simp at card_le
      grw [card_le] at hN
      rify at hN
      rw [Real.pow_le_iff_le_log] at hN
      rw [Real.log_mul] at hN
      rw [Real.log_pow] at hN
      nth_grw 2 [Real.log_natCast_le_rpow_div (ε := (1/2))] at hN
      simp at hN
      have sub_ne: 0 ≠ (N_2 - ((Nat.ceil (Real.logb ‖k‖ 3)))) := by
        grind
      field_simp at hN
      rw [add_comm] at hN
      rw [← sub_le_iff_le_add] at hN
      rw [← div_le_iff₀] at hN
      rw [sub_div] at hN
      nth_rw 1 [mul_comm] at hN
      rw [mul_div_assoc] at hN
      rw [← Real.rpow_one_sub'] at hN
      have le_n_pow: Real.log ↑a / ↑(N_2 - (Nat.ceil (Real.logb ‖k‖ 3))) ^ ((1: ℝ) / 2) ≤ Real.log a := by
        rw [div_eq_mul_inv]
        apply mul_le_of_le_one_right
        . positivity
        . norm_num
          field_simp
          apply Real.one_le_rpow
          . simp
            grind
          . norm_num


      grw [le_n_pow] at hN
      norm_num at hN
      grw [N_2_diff_gt] at hN
      simp at hN
      rw [Nat.cast_sub] at hN
      grind
      . grind
      . grind
      . grind
      .
        positivity
      . grind
      . simp
        grind
      . norm_num
        grind
      . norm_num
      . apply mul_pos
        . simp
          exact ha
        . apply pow_pos
          rw [Nat.cast_sub]
          . simp
            grind
          . grind


theorem LinearMap.toMatrix'_pow {R : Type*} [CommSemiring R] {m : Type*} [Fintype m] [DecidableEq m] (f : (m → R) →ₗ[R] m → R) (n: ℕ):
    LinearMap.toMatrix' (f^n) = (LinearMap.toMatrix' f)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rw [LinearMap.toMatrix'_mul]
    rw [pow_succ]
    rw [ih]

lemma char_nonzero {d: ℕ} {K: Type*} [Field K] (A: (Matrix (Fin d) (Fin d) K)): A.charpoly ≠ 0 := by
  by_contra!
  have monic := A.charpoly_monic
  simp [this] at monic

lemma eigen_nonzero {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ): ∀ (k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin'), k.val ≠ 0 := by
  intro k
  by_contra!
  have eigen_zero := LinearMap.hasEigenvalue_zero_tfae ((A.val.map (Int.castRingHom ℂ)).toLin')
  have det_zero := (eigen_zero.out 0 3).mp
  have has_k := k.prop
  conv at has_k =>
    lhs
    equals k.val => rfl


  specialize det_zero (by
    simp at this
    simp [this] at has_k
    exact has_k
  )
  have a_det := Matrix.GeneralLinearGroup.det_ne_zero A
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

def KroneckerPow_exists {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (k: Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin') (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1) := Polynomial.pow_eq_one_of_mahlerMeasure_eq_one (by
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
      equals Module.End.HasEigenvalue ((Matrix.toLin' ((A.val).map ⇑(Int.castRingHom ℂ)))) a => rfl
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    simp
    rw [← Matrix.charpoly_map] at a_root
    simpa using a_root

  . apply Polynomial.Monic.map
    apply Matrix.charpoly_monic
) (by
  apply eigen_nonzero
) (by
  simp

  have k_prop := k.property
  conv at k_prop =>
    equals Module.End.HasEigenvalue ((A.val).map ⇑(Int.castRingHom ℂ)).toLin' (↑k) =>
      rfl
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at k_prop

  have k_mem_roots: ↑k.val ∈ ((A.val).map ⇑(Int.castRingHom ℂ)).toLin'.charpoly.rootSet ℂ := by
    simp [Polynomial.mem_rootSet]
    refine ⟨char_nonzero _, ?_⟩
    simp at k_prop
    exact k_prop


  refine ⟨?_, ?_⟩
  .
    rw [← Matrix.charpoly_map]
    apply char_nonzero
  .
    rw [← Matrix.charpoly_map]
    rw [Polynomial.mem_rootSet] at k_mem_roots
    have foo := k_mem_roots.2
    simp at foo
    exact foo
) (z := k) (p := A.val.charpoly)

noncomputable def KroneckerPow_single {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (k: Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin') (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1) :=
  (KroneckerPow_exists A k eigen_one_complex).choose

noncomputable def KroneckerPow {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1) :=
  ∏ (k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ )).toLin'), (KroneckerPow_single A k eigen_one_complex)

lemma KroneckerPow_pos {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1):
    0 < KroneckerPow A eigen_one_complex := by
  simp [KroneckerPow]
  intro k
  by_contra!
  simp at this

  simp [KroneckerPow_single] at this
  grind

lemma int_matrix_unipotent {d: ℕ} (hd: 0 < d) (n: ℕ) (hn: 0 < n) (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1): ∃ m, (A.val^(n * KroneckerPow A eigen_one_complex) - 1)^m = 0 := by
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

  let n_prod := KroneckerPow A eigen_one_complex
  have n_prod_pos: 0 < n_prod := by
    simp [n_prod, KroneckerPow]
    intro k
    by_contra!
    simp at this

    simp [KroneckerPow_single] at this
    grind

  have eigen_pow_prod_one: ∀ k:  Module.End.Eigenvalues A_C.toLin', k.val^(n*n_prod) = 1 := by
    intro k
    unfold n_prod KroneckerPow
    rw [← Finset.mul_prod_erase (f := fun (a: Module.End.Eigenvalues (Matrix.toLin' ((A.val).map ⇑(Int.castRingHom ℂ)))) => KroneckerPow_single A a eigen_one_complex) (a := k)]
    .
      rw [pow_mul]
      have pow_self := eigen_pow_self (k := k.val) (hk := k.prop)
      simp [KroneckerPow_single]
      simp [eigen_pow] at pow_self
      simp_rw [← pow_mul]
      rw [← mul_assoc]
      rw [mul_comm (a := n)]
      rw [mul_assoc]
      rw [pow_mul]
      rw [pow_self]
      simp
    . apply Finset.mem_univ

  have pow_eigen: ∀ j: Module.End.Eigenvalues (A_C.toLin'^(n*n_prod)), j.val = 1 := by
    intro a
    have a_spec := a.prop
    conv at a_spec =>
      equals Module.End.HasEigenvalue (A_C.toLin' ^ (n*n_prod)) (↑a) => rfl
    rw [Module.End.hasEigenvalue_iff_mem_spectrum] at a_spec
    simp_rw [← Matrix.toLin'_pow] at a_spec
    simp [-Matrix.toLin'_pow] at a_spec
    rw [spectrum.map_pow_of_pos _ (by positivity)] at a_spec
    simp at a_spec
    obtain ⟨k, k_mem, k_pow⟩ := a_spec
    simp [Module.End.UnifEigenvalues.val] at k_pow
    conv at k_pow =>
      rhs
      equals Module.End.Eigenvalues.val _ a => rfl

    rw [← k_pow]
    rw [← Matrix.spectrum_toLin'] at k_mem
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at k_mem
    rw [← eigen_pow_prod_one (k := ⟨k, k_mem⟩)]
    . simp

  have char_nonzero: (A_C.toLin' ^ (n*n_prod)).charpoly ≠ 0 := by
    by_contra!
    have foo := (A_C.toLin'^(n*n_prod)).charpoly_monic
    simp [this] at foo


  have a_f_char_eq: (A_C.toLin'^(n*n_prod)).charpoly = (Polynomial.X - (Polynomial.C 1))^d := by
    rw [Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (p := (Polynomial.X - Polynomial.C 1) ^ d) (q :=  (A_C.toLin'^(n*n_prod)).charpoly)]
    .
      rw [Polynomial.Monic.def.mp]
      . simp
      . exact LinearMap.charpoly_monic (A_C.toLin' ^ (n*n_prod))
    . simp
      apply Polynomial.Monic.pow
      apply Polynomial.monic_X_sub_C
    .
      have roots_singleton: (A_C.toLin' ^ (n*n_prod)).charpoly.roots.toFinset = {1} := by
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
          have k_pow_prod: k^(n*n_prod) = 1 := by
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
        have monic := (A_C.toLin'^(n*n_prod)).charpoly_monic
        simp [this] at monic
    .
      simp only [Polynomial.natDegree_pow]
      rw [Polynomial.natDegree_X_sub_C]
      simp
      rw [LinearMap.charpoly_natDegree]
      simp


  have eval_zero := (A_C.toLin'^(n*n_prod)).aeval_self_charpoly
  simp [a_f_char_eq] at eval_zero
  use d
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


open scoped Pointwise Finset
