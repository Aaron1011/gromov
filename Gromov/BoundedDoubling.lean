module

public import Mathlib
public import Gromov.Lemma326

/-!
# A subspace with bounded doubling

`exists_bounded_doubling_subspace`, the main output of the `V_Wrapper` section.
-/

@[expose] public section

set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

set_option maxHeartbeats 2500000 in
lemma exists_bounded_doubling_subspace (data: GoodScalesData b): ∃ U: Submodule ℝ LipschitzH, U ≤ V ∧ dim V ≤ 2 * dim U ∧ ∀ f ∈ U, Q_R (16 * (R_2 data)) f f ≤ Real.exp (2 * (a data.d)) * Q_R ((R_2 data)) f f := by
  classical

  let R := 16 ^ ((GoodScales data).i_2)
  have h_R: R'_ V ≤ ↑R := R'_le_R_2 data

  have q_r_base_pos_def := (Q_R_matrix_pos_def_i₀ b (16 ^ ((GoodScales data).i_2)) (by
    simp [i₀]
    rw [pow_le_pow_iff_right₀]
    . have foo := (GoodScales data).i_2_ge
      simp [i₀] at foo
      exact foo
    . simp
  ))

  have det_succ_pos : 0 < (Q_R_matrix b (16 ^ ((GoodScales data).i_2 + 1))).det :=
    (Q_R_matrix_pos_def b (16 ^ ((GoodScales data).i_2 + 1))
      (le_trans h_R (by simp only [R]; push_cast; exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)))).det_pos

  -- Full (definite) inner product core, registered as a local instance so that
  -- `toNormedAddCommGroup` / `ofCore` pick it up by inference.
  letI Q_R_inner_core: InnerProductSpace.Core ℝ V := {
    inner := fun u v => Q_R R u.val v.val
    conj_inner_symm := by
      simp [Q_R]
      grind
    re_inner_nonneg := by
      simp [Q_R]
      intro a _
      apply Finset.sum_nonneg
      intro x _
      exact mul_self_nonneg _
    add_left := by
      simp
      intro a _ a1 _ a2 _
      simp [Q_R]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
    smul_left := by
      simp
      intro a _ a1 _ r
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    definite := fun x hx => by
      by_contra hne
      exact absurd hx (ne_of_gt (Q_R_pos_on_R' x hne R h_R))
  }

  -- Install the definite Q_R-derived NORM (not just a seminorm) *before* `ofCore`, so the
  -- ambient LipschitzH norm on `↥V` is shadowed and `Q_R_inner` is over this `NormedAddCommGroup`.
  letI Q_R_norm : NormedAddCommGroup ↥V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  -- Also expose the seminorm projection as a *direct* local instance, so it shadows the
  -- ambient `V.seminormedAddCommGroup` (a bare `NormedAddCommGroup` letI does not).
  letI Q_R_seminorm : SeminormedAddCommGroup ↥V := Q_R_norm.toSeminormedAddCommGroup
  letI Q_R_inner : InnerProductSpace ℝ ↥V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ ↥V)

  have norm_eq_q_r : ∀ x : ↥V, ‖x‖ = Real.sqrt (Q_R R x x) := fun _ => rfl
  have norm_sq_eq_q_r : ∀ x : ↥V, ‖x‖^2 = (Q_R R x x) := by
    intro x
    rw [norm_eq_q_r]
    rw [Real.sq_sqrt]
    simp [Q_R]
    simp_rw [← pow_two]
    positivity
  have inner_eq_q_r  : ∀ x y : ↥V, inner ℝ x y = Q_R R x y := fun _ _ => rfl

  obtain ⟨v_orthogonal_orig, v_orthogonal_orig_eval⟩ := LinearMap.BilinForm.exists_orthogonal_basis (Q_R_lin_symm V R)
  let v_orthonormal := v_orthogonal_orig.unitsSMul (fun a => Units.mk0 ‖v_orthogonal_orig a‖⁻¹ (by
    simp
    exact Module.Basis.ne_zero v_orthogonal_orig a
  ))

  let q_r_16_m := (Q_R_lin V (16 * R)).toMatrix₂ v_orthonormal v_orthonormal
  have q_r_16_m_hermitian: q_r_16_m.IsHermitian := Q_R_lin_hermetian v_orthonormal (16 * R)

  let q_r_16_eigen := q_r_16_m_hermitian.eigenvectorBasis.toBasis
  let eigen_basis_V :=  (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ ↥V) → ℝ)).trans v_orthonormal.equivFun.symm
  let remapped_ortho := Module.Basis.map q_r_16_eigen eigen_basis_V

  let Q_R_ortho := (Q_R_lin V R).toMatrix₂ remapped_ortho remapped_ortho
  have Q_R_ortho_m_hermitian: Q_R_ortho.IsHermitian := Q_R_lin_hermetian remapped_ortho R

  have Q_R_pos: ∀ i, 0 ≤ Q_R ↑R ⇑(v_orthogonal_orig i).val ⇑(v_orthogonal_orig i).val :=
    fun i => Q_R_self_nonneg _ _
  have eval_nonzero: ∀ i, (Q_R_lin V ↑R) (v_orthogonal_orig i) (v_orthogonal_orig i) ≠ 0 := by
    intro i
    simp [Q_R_lin]
    apply ne_of_gt
    apply Q_R_pos_on_R'
    . exact Module.Basis.ne_zero v_orthogonal_orig i
    . exact h_R
  have v_orthonormal_isortho : (Q_R_lin V ↑R).IsOrthoᵢ remapped_ortho := by
    simp [remapped_ortho]
    rw [LinearMap.isOrthoᵢ_def]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
    intro x y hxy
    have x_mem := x.prop
    simp [-Subtype.coe_prop] at x_mem
    simp [eigen_basis_V, v_orthonormal]
    simp_rw [Module.Basis.unitsSMul_apply]
    simp_rw [Units.smul_def]
    simp_rw [map_smul]
    simp
    simp_rw [Finset.mul_sum]
    conv =>
      lhs
      arg 2
      intro i
      rw [Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hij
        simp
        right
        right
        right
        right
        -- TODO - why doesn't an 'rw' with this work?
        apply v_orthogonal_orig_eval _ _ hij
      )]

    ring
    simp [norm_eq_q_r]
    conv =>
      lhs
      arg 2
      intro i
      rw [Real.sq_sqrt (by apply Q_R_pos)]
    field_simp
    conv =>
      lhs
      arg 2
      intro i
      rw [mul_div_assoc]
      rhs
      equals ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) / ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) =>
        rfl

    field_simp [eval_nonzero]
    have inner_zero :=  q_r_16_m_hermitian.eigenvectorBasis.inner_eq_zero hxy
    rw [EuclideanSpace.inner_eq_star_dotProduct] at inner_zero
    simp [dotProduct] at inner_zero
    exact inner_zero

  have q_r_lin_remapped_one: ∀ i, ((Q_R_lin V ↑R) (remapped_ortho i)) (remapped_ortho i) = 1 := by
    intro i
    simp [remapped_ortho]
    simp [eigen_basis_V,]
    ring
    field_simp
    simp only [eigen_basis_V, q_r_16_eigen]
    simp
    simp_rw [Finset.mul_sum]
    simp [v_orthonormal]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval

    simp_rw [Module.Basis.unitsSMul_apply]
    simp_rw [Units.smul_def]
    simp_rw [map_smul]
    simp

    conv =>
      lhs
      arg 2
      intro i
      rw [Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hij
        simp
        right
        right
        right
        right
        -- TODO - why doesn't an 'rw' with this work?
        apply v_orthogonal_orig_eval _ _ hij
      )]

    ring
    simp [norm_eq_q_r]
    conv =>
      lhs
      arg 2
      intro i
      rw [Real.sq_sqrt (by apply Q_R_pos)]
    field_simp
    conv =>
      lhs
      arg 2
      intro i
      rw [mul_div_assoc]
      rhs
      equals ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) / ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) =>
        rfl

    field_simp [eval_nonzero]
    have one_eq: (1: ℝ) = 1^2 := by
      simp
    rw [one_eq, ← OrthonormalBasis.norm_eq_one (q_r_16_m_hermitian.eigenvectorBasis) i]
    rw [EuclideanSpace.real_norm_sq_eq]

  let q_r_v_orthonormal := (Q_R_lin V (R)).toMatrix₂ v_orthonormal v_orthonormal

  have Q_R_v_orthonormal_eq_1: q_r_v_orthonormal = 1 := by
    ext i j
    simp [q_r_v_orthonormal, Matrix.one_apply]
    split_ifs
    .
      rename_i i_eq_j
      rw [i_eq_j]
      simp [v_orthonormal]
      simp [Module.Basis.unitsSMul_apply]
      rw [← mul_assoc, ← pow_two]
      simp
      rw [norm_sq_eq_q_r]
      simp [Q_R_lin]
      apply inv_mul_cancel₀
      apply ne_of_gt
      apply Q_R_pos_on_R'
      . apply Module.Basis.ne_zero
      . exact h_R

    .
      rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
      simp [v_orthonormal]
      simp [Module.Basis.unitsSMul_apply]
      right
      right
      apply v_orthogonal_orig_eval
      grind

  -- TODO - an enormous amount of this should get deduplicated with v_orthonormal_isortho
  have Q_R_ortho_eq_1: Q_R_ortho = 1 := by
    ext i j
    simp [Q_R_ortho, Matrix.one_apply]
    split_ifs
    .
      rename_i i_eq_j
      rw [i_eq_j]
      apply q_r_lin_remapped_one
    .
      rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
      apply v_orthonormal_isortho
      grind

  let Q_R_16_new_ortho := (Q_R_lin V (16 *R)).toMatrix₂ remapped_ortho remapped_ortho
  have Q_R_16_new_ortho_hermitian: Q_R_16_new_ortho.IsHermitian := Q_R_lin_hermetian remapped_ortho (16 *R)

  have det_Q_R_one: Q_R_ortho.det = 1 := by
    simp [Q_R_ortho_eq_1]

  have det_Q_R_16_ge: 1 ≤ Q_R_16_new_ortho.det := by
    rw [← det_Q_R_one]
    apply matrix_det_montone
    .
      simp [Q_R_ortho]
      apply Matrix.PosDef.of_dotProduct_mulVec_pos (?_)
      .
        intro x hx
        simp [Q_R_matrix]
        conv =>
          rhs
          lhs
          equals (star x) => simp
        rw [star_dotProduct_toMatrix₂_mulVec]
        apply Q_R_pos_on_R'
        . rw [LinearEquiv.map_ne_zero_iff]
          exact hx
        . exact h_R
      . apply Q_R_ortho_m_hermitian
    .
      simp [Q_R_16_new_ortho, Q_R_ortho]
      rw [← map_sub]
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      apply Q_R_lin_sub_pos_semi_def
      norm_cast
      grind

  have q_r_16_remapped_orthogonal : (Q_R_lin_plain V (16 * R)).IsOrthoᵢ remapped_ortho := by
    simp [remapped_ortho]
    rw [LinearMap.isOrthoᵢ_def]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
    intro x y hxy
    have x_mem := x.prop
    simp [-Subtype.coe_prop] at x_mem
    simp
    rw [apply_eq_dotProduct_toMatrix₂_mulVec (v_orthonormal) (v_orthonormal)]
    simp
    simp [eigen_basis_V]
    have repr_self: ∀ x, (∑ i, fun₀ | i => (q_r_16_eigen x).ofLp i) = (q_r_16_eigen x).ofLp := by
      intro z
      conv =>
        lhs
        arg 2
        intro i
        equals Pi.single i ((q_r_16_eigen z).ofLp i) =>
          simp
          ext a
          rw [Finsupp.single_apply]
          rw [Pi.single_apply]
          have foo := eq_comm (a := i) (b := a)
          simp_rw [foo]

      ext a
      simp

    simp [repr_self]
    unfold q_r_16_eigen
    unfold q_r_16_m
    conv =>
      lhs
      rhs
      lhs
      equals q_r_16_m => rfl

    have tobasis_lp: ∀ x, (q_r_16_m_hermitian.eigenvectorBasis.toBasis x).ofLp = (q_r_16_m_hermitian.eigenvectorBasis x).ofLp := by
      simp
    simp [tobasis_lp]
    rw [Matrix.IsHermitian.mulVec_eigenvectorBasis q_r_16_m_hermitian]
    simp
    right
    conv =>
      lhs
      rhs
      equals star ((q_r_16_m_hermitian.eigenvectorBasis y).ofLp) =>
        simp

    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    apply OrthonormalBasis.inner_eq_zero
    exact hxy.symm

  have new_growth := data.h_growth
  have nonempty_fin: Nonempty (Fin (Module.finrank ℝ ↥V)) := by
    use 0
    apply Module.finrank_pos
  apply growth_bound_basis_change data.d b remapped_ortho at new_growth
  have a_gt := (GoodScales data).second_h_i
  simp [h, f] at a_gt
  rw [Real.log_mul] at a_gt
  .
    have log_pos_first: 0 ≤ Real.log ↑(#(S ^ 16 ^ ((GoodScales data).i_2 + 1))) := by
      apply Real.log_nonneg
      simp
      apply Finset.Nonempty.pow
      simp [S_nonempty]

    have log_second: Real.log ↑(#(S ^ 16 ^ (GoodScales data).i_2)) ≤ Real.log ↑(#(S ^ 16 ^ ((GoodScales data).i_2 + 1))) := by
      apply Real.log_le_log
      . simp
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . simp
        apply Finset.card_le_card
        apply Finset.pow_subset_pow_right
        . simp [one_mem]
        . grind

    --
    have inner_x_self (x: V) (k: ℝ) (hk: ∀ i ∈ (remapped_ortho.repr x).support, (Q_R_lin_plain V (16 * R) (remapped_ortho i) (remapped_ortho i)) ≤ k * (Q_R_lin_plain V (R) (remapped_ortho i) (remapped_ortho i))) : Q_R_lin_plain V (16 * R) x x ≤ k * Q_R_lin_plain V (R) x x := by
      rw [←  Module.Basis.sum_repr remapped_ortho (u := x)]
      have inner_sum_eq: ∀ i, ∑ i_1, inner ℝ ((remapped_ortho.repr x) i_1 • remapped_ortho i_1) ((remapped_ortho.repr x) i • remapped_ortho i) = inner ℝ ((remapped_ortho.repr x) i • remapped_ortho i) ((remapped_ortho.repr x) i • remapped_ortho i) := by
        intro i
        rw [Finset.sum_eq_single i]
        . intro k hk k_neq
          rw [inner_eq_q_r]
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
          specialize v_orthonormal_isortho k i k_neq
          simp [Q_R_lin] at v_orthonormal_isortho
          simp [Q_R]
          simp [Q_R] at v_orthonormal_isortho
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          simp_rw [mul_comm ((remapped_ortho.repr x) i)]
          simp_rw [← mul_assoc]
          rw [← Finset.sum_mul]
          simp [v_orthonormal_isortho]
        .
          intro hi
          simp at hi

      have q_r_16_sum_eq: ∀ i, ∑ i_1, Q_R_lin_plain V (16 * R) ((remapped_ortho.repr x) i_1 • remapped_ortho i_1) ((remapped_ortho.repr x) i • remapped_ortho i) = Q_R_lin_plain V (16 * R) ((remapped_ortho.repr x) i • remapped_ortho i) ((remapped_ortho.repr x) i • remapped_ortho i) := by
        intro i
        rw [Finset.sum_eq_single i]
        . intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at q_r_16_remapped_orthogonal
          specialize q_r_16_remapped_orthogonal k i k_neq
          simp [Q_R_lin_plain] at q_r_16_remapped_orthogonal
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at q_r_16_remapped_orthogonal
          right
          right
          simp [q_r_16_remapped_orthogonal]
        .
          intro hi
          simp at hi

      rw [map_sum]
      simp_rw [map_sum]
      simp [Finset.sum_apply]
      conv =>
        rhs
        rhs
        arg 2
        intro i
        rw [Finset.sum_eq_single i (by
          intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
          right
          specialize v_orthonormal_isortho k i k_neq
          simp [Q_R_lin] at v_orthonormal_isortho
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at v_orthonormal_isortho
          simp [v_orthonormal_isortho]
        ) (by
          intro hi
          simp at hi
        )]
      conv =>
        rhs
        rw [←  Module.Basis.sum_repr remapped_ortho (u := x)]

      simp_rw [map_sum]
      simp
      simp_rw [Finset.mul_sum]
      conv =>
        lhs
        arg 2
        intro i
        rw [Finset.sum_eq_single i (by
          intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at q_r_16_remapped_orthogonal
          specialize q_r_16_remapped_orthogonal k i k_neq
          simp [Q_R_lin_plain] at q_r_16_remapped_orthogonal
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at q_r_16_remapped_orthogonal
          right
          right
          simp [q_r_16_remapped_orthogonal]
        ) (by
          intro hi
          simp at hi
        )]

      apply Finset.sum_le_sum
      intro i hi
      by_cases i_mem_inter: i ∈ (remapped_ortho.repr x).support
      .
        conv =>
          lhs
          equals ((Q_R_lin_plain V (16 * ↑R)) (remapped_ortho i)) (remapped_ortho i)  * (remapped_ortho.repr x) i * (remapped_ortho.repr x) i =>
            ring

        conv =>
          rhs
          equals k * ((Q_R_lin_plain V ↑R) (remapped_ortho i)) (remapped_ortho i) * (remapped_ortho.repr x) i * (remapped_ortho.repr x) i =>
            ring

        rw [mul_assoc]
        nth_rw 2 [mul_assoc]
        specialize hk i i_mem_inter
        grw [hk]
        . ring
          simp
        . rw [← pow_two]
          positivity
      .
        simp at i_mem_inter
        simp [i_mem_inter]
    grw [← log_second] at a_gt
    rw [Real.log_mul] at a_gt
    .
      simp at a_gt
      rw [Real.log_rpow] at a_gt
      rw [Real.log_rpow] at a_gt
      rw [← mul_sub] at a_gt
      rw [← Real.log_div] at a_gt
      .

        simp [Q_R_matrix] at a_gt

        let large_basis: Finset _ := { i: Fin (Module.finrank ℝ ↥V) | (Real.exp (2 * (a data.d))) * Q_R_lin V (R) (remapped_ortho i) (remapped_ortho i) < Q_R_lin V (16 * R) (remapped_ortho i) (remapped_ortho i)}
        let small_basis: Finset _ := { i: Fin (Module.finrank ℝ ↥V) | ¬((Real.exp (2 * (a data.d))) * Q_R_lin V (R) (remapped_ortho i) (remapped_ortho i) < Q_R_lin V (16 * R) (remapped_ortho i) (remapped_ortho i))}
        let large_submodule := Submodule.span ℝ ((Finset.image remapped_ortho large_basis) : Set V)
        by_cases dim_small: 2 * dim large_submodule < dim V
        .
          let small_submodule := Submodule.span ℝ ((Finset.image remapped_ortho Finset.univ ) \ (Finset.image remapped_ortho large_basis) : Set V)
          use Submodule.map V.subtype small_submodule
          refine ⟨?_, ?_, ?_⟩
          . apply Submodule.map_subtype_le
          . simp [dim]
            simp [dim] at dim_small
            have large_small_compl: IsCompl large_submodule small_submodule := by
              simp [large_submodule, small_submodule]
              have diff_eq: Set.range ⇑remapped_ortho \ ⇑remapped_ortho '' ↑large_basis = Set.image remapped_ortho small_basis := by
                ext a
                simp [large_basis, small_basis]
                grind
              rw [diff_eq]
              apply LinearIndependent.isCompl_span_image
              . apply Module.Basis.linearIndependent
              . simp
              . apply IsCompl.of_eq
                . simp
                  ext a
                  simp [large_basis, small_basis]
                . simp
                  ext a
                  simp [large_basis, small_basis]
                  grind

            have dim_sum := Submodule.finrank_add_eq_of_isCompl large_small_compl
            rw [eq_comm, add_comm] at dim_sum

            apply Nat.sub_eq_of_eq_add at dim_sum
            rw [← dim_sum]
            rw [Nat.cast_sub (by apply Submodule.finrank_le)]
            rw [mul_sub]
            simp
            rw [le_sub_iff_add_le']
            grw [dim_small]
            ring
            simp
          .
            have all_le: ∀ f ∈ small_submodule, Q_R_lin V (16 * ↑(R_2 data)) f f ≤ Real.exp (2 * a data.d) * Q_R_lin V ↑(R_2 data) f f := by
              intro f hf
              apply inner_x_self
              intro i hi
              simp only [small_submodule, ← Finset.coe_sdiff] at hf
              rw [Submodule.mem_span_finset] at hf
              obtain ⟨g, g_supp, f_eq_g⟩ := hf
              rw [← f_eq_g] at hi
              rw [Finset.sum_sdiff_eq_sub] at hi
              .
                simp at hi
                rw [Finset.sum_image (by simp; apply Module.Basis.injective)] at hi
                rw [Finset.sum_image (by apply (Module.Basis.injective _).injOn)] at hi
                simp at hi
                have i_not_mem: ¬(i ∈ large_basis) := by
                  by_contra!
                  rw [Finset.sum_eq_single_of_mem i this] at hi
                  .
                    rw [Finset.sum_eq_single_of_mem i (by simp)] at hi
                    . simp at hi
                    . intro k hk i_neq
                      simp
                      right
                      simp [Finsupp.single_apply, i_neq]
                  . intro k hk i_neq
                    simp
                    right
                    simp [Finsupp.single_apply, i_neq]

                simp [large_basis] at i_not_mem
                simp [Q_R_lin_plain]
                simp [Q_R_lin] at i_not_mem
                simpa using i_not_mem

              . apply Finset.image_subset_image
                simp
            intro f hf
            simp at hf
            obtain ⟨f_mem_V, hf⟩ := hf
            specialize all_le ⟨_, f_mem_V⟩ hf
            apply all_le

        simp at dim_small
        have basis_change := Q_R_matrix_det_basis_change v_orthonormal b
        obtain ⟨K, k_pos, hK⟩ := basis_change
        simp [Q_R_matrix] at hK
        simp [hK] at a_gt
        field_simp at a_gt
        unfold Q_R_ortho at det_Q_R_one
        have foo := Q_R_v_orthonormal_eq_1
        unfold q_r_v_orthonormal at Q_R_v_orthonormal_eq_1
        simp [R] at Q_R_v_orthonormal_eq_1
        simp [Q_R_v_orthonormal_eq_1] at a_gt

        have q_r_16_eigen_ge_one: ∀ i, (1: ℝ) ≤ (Q_R_lin V (16 * ↑R)) (remapped_ortho i) (remapped_ortho i) := by
          intro i
          simp [Q_R_lin, Q_R]
          grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := (finite_closed_ball 1 R).toFinset)]
          .
            have foo := q_r_lin_remapped_one
            simp [Q_R_lin, Q_R] at foo
            simp [finite_closed_ball]
            rw [foo]
          .
            simp
            apply Metric.closedBall_subset_closedBall
            norm_cast
            grind
          .
            intro i hi _
            rw [← pow_two]
            positivity

        have key_eq: ∀ i, (Q_R_lin V (16 * ↑R)) (remapped_ortho i) (remapped_ortho i) = q_r_16_m_hermitian.eigenvalues i := by
          intro i
          rw [Matrix.IsHermitian.eigenvalues_eq]
          have app_eq := dotProduct_toMatrix₂_mulVec v_orthonormal v_orthonormal (B := (Q_R_lin V (16 ^ ((GoodScales data).i_2 + 1))))
          conv at app_eq =>
            intro x y
            lhs
            lhs
            equals x =>
              ext j
              simp
          conv at app_eq =>
            intro x y
            lhs
            rhs
            rhs
            equals y =>
              ext j
              simp
          simp [star, R]
          conv =>
            rhs
            rhs
            arg 1
            simp [q_r_16_m]
          simp [R]
          simp_rw [← pow_succ']
          rw [app_eq]
          simp [remapped_ortho, eigen_basis_V, q_r_16_eigen]

        have q_r_16_eigen_ge: ∀ i ∈ large_basis, Real.exp (2 * a data.d) * ((Q_R_lin V ↑R) (remapped_ortho i)) (remapped_ortho i) ≤ q_r_16_m_hermitian.eigenvalues i := by
          intro i hi
          rw [← key_eq i]
          simp only [large_basis, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact le_of_lt hi

        conv at a_gt =>
          lhs
          pattern Matrix.det _
          equals q_r_16_m.det =>
            simp [q_r_16_m, R]
            rw [pow_succ']

        rw [Matrix.IsHermitian.det_eq_prod_eigenvalues q_r_16_m_hermitian] at a_gt
        .
          simp at a_gt
          rw [Real.log_prod] at a_gt
          .
            grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := large_basis) (h := by simp)] at a_gt
            .
              grw [← Finset.card_nsmul_le_sum (n := 2 * (a data.d))] at a_gt
              .
                simp [dim, large_submodule] at dim_small
                rw [finrank_span_finset_eq_card] at dim_small
                . rw [Finset.card_image_iff.mpr] at dim_small
                  .
                    rw [← div_le_iff₀'] at dim_small
                    .
                      norm_cast at dim_small
                      conv at dim_small =>
                        lhs
                        equals ↑(Module.finrank ℝ V / 2) =>
                          rw [Nat.cast_div]
                          . grind
                          . apply Even.two_dvd
                            apply v_wrapper_inst.V_even
                          . simp

                      norm_cast at dim_small
                      grw [← dim_small] at a_gt
                      simp [dim] at a_gt
                      rw [Nat.cast_div] at a_gt
                      .
                        have rank_ne: (↑(Module.finrank ℝ ↥V) : ℝ) ≠ 0 := by
                          apply ne_of_gt
                          simp
                          apply Module.finrank_pos
                        field_simp at a_gt
                        grind
                      . apply Even.two_dvd
                        apply v_wrapper_inst.V_even
                      . simp
                      . simp [a]
                        positivity
                      . simp [dim]
                    . simp
                  . apply (Module.Basis.injective _).injOn
                .
                  rw [Finset.coe_image]
                  apply LinearIndepOn.id_image
                  apply Module.Basis.linearIndepOn
              . simp [dim]
              . intro i hi
                rw [Real.le_log_iff_exp_le]
                .

                  grw [← q_r_16_eigen_ge]
                  .
                    simp [q_r_lin_remapped_one]
                  . exact hi
                .
                  apply Matrix.PosDef.eigenvalues_pos
                  apply Matrix.PosDef.of_dotProduct_mulVec_pos (?_)
                  .
                    intro x hx
                    simp [Q_R_matrix]
                    conv =>
                      rhs
                      lhs
                      equals (star x) => simp
                    rw [star_dotProduct_toMatrix₂_mulVec]
                    apply Q_R_pos_on_R'
                    . rw [LinearEquiv.map_ne_zero_iff]
                      exact hx
                    . grw [h_R]
                      simp [R]
                  . exact q_r_16_m_hermitian
            . simp [dim]
            . intro i hi i_not_mem
              rw [← key_eq i]
              exact Real.log_nonneg (q_r_16_eigen_ge_one i)
          . intro i
            simp
            apply ne_of_gt
            apply Matrix.PosDef.eigenvalues_pos
            apply Matrix.PosDef.of_dotProduct_mulVec_pos (?_)
            . intro x hx
              simp [Q_R_matrix]
              conv =>
                rhs
                lhs
                equals (star x) => simp
              rw [star_dotProduct_toMatrix₂_mulVec]
              apply Q_R_pos_on_R'
              . rw [LinearEquiv.map_ne_zero_iff]
                exact hx
              . grw [h_R]
                simp [R]
            . exact q_r_16_m_hermitian

      . exact det_succ_pos.ne'
      . exact q_r_base_pos_def.det_pos.ne'
      . exact q_r_base_pos_def.det_pos
      . exact det_succ_pos
    . simp
      have foo := S_nonempty
      grind
    . exact (Real.rpow_pos_of_pos q_r_base_pos_def.det_pos _).ne'
  . simp
    have foo := S_nonempty
    grind
  . exact (Real.rpow_pos_of_pos det_succ_pos _).ne'

#print axioms exists_bounded_doubling_subspace

end V_Wrapper_Section

-- Theorem 3.23
-- Todo - is the better way to declare theorem_3_23 so that the constant is not allowed to depend on V?

end GeneratesNS
