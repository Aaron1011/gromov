module

public import Mathlib
public import Gromov.Poincare

/-!
# Lemma 3.26 and basis changes

`lemma_3_26_a` together with the behaviour of `Q_R_matrix` and `growth_bound` under a change of
basis.
-/

public section

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

@[expose]
noncomputable def J (data: GoodScalesData b) := #((X_j_finite data).toFinset)
@[expose]
noncomputable def phi (data: GoodScalesData b): V →ₗ[ℝ] EuclideanSpace ℝ (B_finsets data) := {
  toFun := fun u => WithLp.toLp 2 (fun (j: B_finsets data) => ((#j.val : ℝ)⁻¹) * ∑ x ∈ j.val, u.val x)
  map_add' := by
    intro x y
    simp
    simp_rw [Finset.sum_add_distrib]
    simp_rw [mul_add]
    ext a
    simp
  map_smul' := by
    intro k V
    ext a
    simp
    simp_rw [← Finset.mul_sum]
    ring
}

@[expose] def C: ℝ := 32 * (#S)

set_option maxHeartbeats 2500000 in
lemma lemma_3_26_a (data: GoodScalesData b) (u: V): Q_R (R_2 data) u u ≤ 2 * (#(S^(R_1 data ))) * ‖(phi data u)‖^2 + C * (Real.exp ((2 * a data.d))) * (R_1 data + 1)^2 * (∑ x ∈ B_r (8 * R_2 data), deriv_sq u x)  := by

  rw [Q_R]
  let b_union := ⋃₀ (B data)
  grw [Finset.sum_le_sum_of_subset_of_nonneg (t := (B_finsets data).biUnion id)]
  .
    grw [Finset.sum_biUnion_le (fun x => mul_self_nonneg ((↑u : LipschitzH) x))]
    .
      have u_bound (x: G) (j: B_finsets data): (u.val x)^2 ≤ 2 * ((u.val x - (phi data u).ofLp j)^2 + ((phi data u).ofLp j)^2) := by
        calc
          _ = |u.val x - ((phi data u).ofLp j) + (phi data u).ofLp j|^2 := by
            simp
          _ ≤ (|u.val x - (phi data u).ofLp j| + |(phi data u).ofLp j|)^2 := by
            grw [abs_add_le]
          _ = _ := by
            rw [add_sq]
          _ ≤ _ := by
            grw [two_mul_le_add_sq]
            simp [sq_abs]
            grind

      rw [← Finset.sum_finset_coe]
      simp_rw [← pow_two]
      simp
      grw [Finset.sum_le_sum (g := fun (j: B_finsets data) => ∑ x ∈ j, 2 * ((u.val x - (phi data u).ofLp j)^2 + ((phi data u).ofLp j)^2))]
      .

        simp_rw [← Finset.mul_sum]
        simp_rw [Finset.sum_add_distrib]
        simp
        have card_j_eq (j: B_finsets data): #j.val = #(S^(R_1 data)) := by
          have hj := j.prop
          simp only [B_finsets] at hj
          simp [-SetLike.coe_mem] at hj
          obtain ⟨x, hx, x_eq⟩ := hj
          rw [← x_eq]
          have foo := B_c_r_eq_smul x (R_1 data )
          simp [B_c_r] at foo
          rw [foo]
          simp

          rw [card_B_r_eq]

        simp [card_j_eq]
        simp_rw [← Finset.mul_sum]
        conv =>
          lhs
          rhs
          rhs
          rhs
          rw [← Finset.univ_eq_attach]
          rw [← EuclideanSpace.real_norm_sq_eq]

        have phi_eq (j : B_finsets data) :
            ((phi data) u).ofLp j = (#(j : Finset G) : ℝ)⁻¹ * ∑ x ∈ (j : Finset G), (u : G → ℝ) x :=
          rfl
        simp_rw [phi_eq]
        have attach_eq := Finset.sum_attach (B_finsets data)
          (fun j => ∑ x ∈ j, ((u : G → ℝ) x - (#j : ℝ)⁻¹ * ∑ y ∈ j, (u : G → ℝ) y) ^ 2)
        beta_reduce at attach_eq
        simp only [show (↑u : LipschitzH).toFun = ⇑(↑u : LipschitzH) from rfl, attach_eq]
        simp only [B_finsets]
        rw [Finset.sum_image]
        .
          rw [mul_add]

          rw [add_comm]
          apply add_le_add
          .
            ring
            simp

          .

            conv =>
              lhs
              rhs
              arg 2
              intro x
              equals ∑ x_1 ∈ B_c_r x (R_1 data ), (u.val.toFun x_1 - (f_avg_c x (R_1 data ) u.val.toFun)) ^ 2 =>
                apply Finset.sum_congr
                . simp [B_c_r]
                . intro y hy
                  simp [f_avg_c, B_c_r, -Set.toFinset_card]
                  conv =>
                    lhs
                    lhs
                    pattern #(Metric.closedBall x (↑(R_1 data) )).toFinset
                    equals #(B_c_r x (R_1 data)) =>
                      simp [B_c_r]
                  rw [B_c_r_eq_smul]
                  simp [B_r]

            conv =>
              lhs
              rhs
              arg 2
              intro x
              arg 2
              intro y
              rw [← sq_abs]
            rw [← Finset.sum_finset_coe]
            simp only [SetLike.coe_sort_coe, Finset.univ_eq_attach]
            grw [Finset.sum_le_sum (h := fun (a : {x // x ∈ (X_j_finite data).toFinset}) _ =>
              lemma_3_25_poincare data ⟨a.val, (X_j_finite data).mem_toFinset.mp a.prop⟩
                (f := u.val.toFun))]

            simp_rw [← Finset.mul_sum]
            have sum_swap: ∑ i ∈ (X_j_finite data).toFinset, ∑ x ∈ B_c_r (i) (3 * (↑(R_1 data) + 1)), deriv_sq (u.val).toFun x = ∑ x ∈ B_r (8 * (R_2 data)), #{ i ∈ (X_j_finite data).toFinset | x ∈ B_c_r (↑i) (3 * (↑(R_1 data) + 1))} * deriv_sq (u.val).toFun x := by
              simp_rw [Finset.card_filter]
              simp_rw [Nat.cast_sum]
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr
              . simp
              . intro i hi
                have set_eq: B_r (8 * ↑(R_2 data)) ∩ B_c_r i (3 * (↑(R_1 data) + 1)) = B_c_r i (3 * (↑(R_1 data) + 1)) := by
                  simp
                  intro x hx
                  simp [B_c_r] at hx
                  simp [X_j] at hi
                  apply Metric.maximalSeparatedSet_subset at hi
                  simp [B_r]
                  simp at hi
                  grw [dist_triangle _ i]
                  grw [hx, hi]
                  simp [R_1, R_2]

                  rw [two_mul]
                  have i_1_le:  (GoodScales data).i_1 ≤  (GoodScales data).i_2 := by
                    have foo :=  (GoodScales data).i_diff_mem
                    simp at foo
                    grind
                  grw [i_1_le]
                  ring
                  .
                    rw [← le_sub_iff_add_le]
                    ring
                    have i_2_pos := (GoodScales data).i_2_pos
                    have le_one: 1 ≤  (GoodScales data).i_2 := by grind
                    grw [← le_one]
                    .
                      norm_num
                    . simp
                  . simp
                  . simp
                simp
                rw [set_eq]

            rw [Finset.sum_attach (f := fun (i: G) => ∑ x ∈ B_c_r (i) (3 * (↑(R_1 data) + 1)), deriv_sq (u.val).toFun x)]
            rw [sum_swap]

            have card_inter_le (x: G): #({i ∈ (X_j_finite data).toFinset | x ∈ B_c_r i (3 * (↑(R_1 data + 1)) )}) ≤ Real.exp (a data.d) := by
              have foo := log_pack_center_helper data x
              rw [Nat.cast_add]
              simpa using foo

            simp [C]
            simp_rw [← mul_assoc]
            norm_num
            rw [two_mul, Real.exp_add]
            conv =>
              rhs
              equals (32 * ↑(#S) * (Real.exp (a data.d) * (↑(R_1 data) + 1) ^ 2)) * ((Real.exp (a data.d)) * ∑ x ∈ B_r (8 * ↑(R_2 data)), deriv_sq (⇑u.val) x) =>
                ring
            apply mul_le_mul
            . ring
              simp
            .
              grw [Finset.sum_le_sum (g := fun x => Real.exp (a data.d) *  (deriv_sq (u.val).toFun x))]
              .

                rw [← Finset.mul_sum]
                apply le_refl
              . intro i hi
                norm_cast
                norm_cast at card_inter_le
                grw [card_inter_le]
                simp [deriv_sq, ← pow_two]
                positivity

            . simp [deriv_sq, ← pow_two]
              apply Finset.sum_nonneg
              intro i hi
              norm_cast
              positivity
            . positivity

        .
          simp
          have foo := B_ball_injective_on data (R_1 data ) (by simp [R_1]) (by simp)
          intro a ha b hb hab
          specialize foo ha hb (by
            simp
            simp at hab
            exact hab
          )
          exact foo

      . intro j hj
        apply Finset.sum_le_sum
        intro x hx
        apply u_bound

  .
    have cover := B_covers_R2 data
    simp
    intro a ha
    specialize cover ha
    simp [B_finsets]
    simp [B] at cover

    exact cover
  . intros
    rw [← pow_two]
    positivity

#print axioms lemma_3_26_a

-- Controlled grwoth

-- Lemma 3.27

omit [Nonempty ι] in
/-- The determinant of `Q_R_matrix` at two bases of `V` differs by a positive constant that is
**uniform in the scale `R`**. Hence the determinant *ratio* between two scales — and so the
`h`-difference used to select good scales — is basis-independent. -/
lemma Q_R_matrix_det_basis_change {index : Type*} [Fintype index] [DecidableEq index]
    (b_1 : Module.Basis ι ℝ V) (b_2 : Module.Basis index ℝ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, (Q_R_matrix b_2 R).det = K * (Q_R_matrix b_1 R).det := by
  obtain ⟨K, hK, hB⟩ := LinearMap.toMatrix₂_det_basis_change b_1 b_2
  refine ⟨K, hK, fun R => ?_⟩
  have h2 : Q_R_matrix b_2 R = LinearMap.toMatrix₂ b_2 b_2 (Q_R_lin_plain V R) := by
    simp only [Q_R_matrix]; ext i j; simp [Q_R_lin, Q_R_lin_plain]
  have h1 : Q_R_matrix b_1 R = LinearMap.toMatrix₂ b_1 b_1 (Q_R_lin_plain V R) := by
    simp only [Q_R_matrix]; ext i j; simp [Q_R_lin, Q_R_lin_plain]
  rw [h2, h1, hB]

omit [Nonempty ι] in
lemma growth_bound_basis_change (d: ℕ) {index: Type*} [Fintype index] [DecidableEq index] (b_1: Module.Basis ι ℝ V) (b_2: Module.Basis index ℝ V) (h_growth: growth_bound b_1 d) : growth_bound b_2 d := by
  -- the two bases index the same space, so their index types are canonically equivalent
  let equiv : ι ≃ index := b_1.indexEquiv b_2
  unfold growth_bound my_expr Q_R_matrix
  unfold growth_bound my_expr Q_R_matrix at h_growth
  have conv_plain: ∀ R, (LinearMap.toMatrix₂ b_2 b_2) (Q_R_lin V ↑R) = (LinearMap.toMatrix₂ b_2 b_2) (Q_R_lin_plain V ↑R) := by
    intro R
    ext i j
    simp [Q_R_lin, Q_R_lin_plain]

  have conv_plain_b_1: ∀ R, (LinearMap.toMatrix₂ b_1 b_1) (Q_R_lin V ↑R) = (LinearMap.toMatrix₂ b_1 b_1) (Q_R_lin_plain V ↑R) := by
    intro R
    ext i j
    simp [Q_R_lin, Q_R_lin_plain]

  -- The two change-of-basis determinant factors are transposes of each other, hence equal,
  -- and their common value is nonzero since it is the determinant of an (invertible) basis-change
  -- matrix (`(b_1.reindex equiv).toMatrix b_2`).
  have heq_det : ((b_1.toMatrix ⇑b_2).transpose.submatrix id ⇑equiv.symm).det
               = ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det := by
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have hne_det : ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det ≠ 0 := by
    rw [← Module.Basis.toMatrix_reindex]
    have hmul : ((b_1.reindex equiv).toMatrix ⇑b_2).det
              * (b_2.toMatrix ⇑(b_1.reindex equiv)).det = 1 := by
      rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one hmul

  simp_rw [conv_plain]
  conv =>
    arg 1
    intro R
    rw [← Matrix.det_reindex_self equiv.symm]
    rw [← LinearMap.toMatrix₂_mul_basis_toMatrix (b₁ := b_1.reindex equiv) (b₂ := b_1.reindex equiv)]
    simp [-LinearMap.toMatrix₂_mul_basis_toMatrix]
    rw [mul_assoc]
    rw [mul_comm _ (((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det)]
    rw [← mul_assoc]
    rw [Real.mul_rpow (by rw [heq_det]; exact mul_self_nonneg _) (by
      apply Matrix.PosSemidef.det_nonneg
      conv =>
        arg 1
        equals (LinearMap.toMatrix₂ (b_1.reindex equiv) (b_1.reindex equiv)) (Q_R_lin V ↑R) =>
          ext i j
          simp [Q_R_lin, Q_R_lin_plain]

      -- TODO - make this a standalone lemma
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      rw [LinearMap.isPosSemidef_def]
      refine ⟨?_, ?_⟩
      .
        apply Q_R_lin_symm
      .
        rw [LinearMap.isNonneg_def]
        intro x
        simp [Q_R_lin, Q_R]
        simp_rw [← pow_two]
        positivity

    )]
    rw [← mul_assoc]
    rw [mul_comm ((#(S ^ R)) : ℝ)]
    rw [mul_assoc]
    rw [mul_div_assoc]

  let K := (((b_1.toMatrix ⇑b_2).transpose.submatrix id ⇑equiv.symm).det *
          ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det) ^ (↑(Module.finrank ℝ ↥V) : ℝ)⁻¹
  conv =>
    rhs
    equals (nhdsWithin (K * 0) (Set.Ioi (K * 0))) =>
      simp

  apply Filter.TendstoNhdsWithinIoi.const_mul
  .
    apply Real.rpow_pos_of_pos
    rw [heq_det]
    exact mul_self_pos.mpr hne_det
  .
    simp_rw [LinearMap.toMatrix₂_reindex_det]
    simp_rw [conv_plain_b_1] at h_growth
    simp at h_growth
    apply h_growth

lemma R'_le_R_2 (data: GoodScalesData b) : R'_ V ≤ (↑(R_2 data) : ℝ) := by
  have foo := (GoodScales data).i_2_ge
  simp [i₀] at foo
  have pow_le := Nat.le_pow_clog (b := 16) (x := ⌈R'_ V⌉₊) (by simp)
  have r_ceil := Nat.le_ceil (R')
  unfold R' at r_ceil
  grw [r_ceil]
  grw [pow_le]
  simp [R_2]
  rw [pow_le_pow_iff_right₀]
  . exact foo
  . simp

end V_Wrapper_Section

end GeneratesNS
