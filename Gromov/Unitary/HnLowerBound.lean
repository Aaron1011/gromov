module

public import Mathlib
public import Gromov.Unitary.HnEps

/-!
# A lower bound for powers in `H_n`

The real auxiliary function `f` and the resulting lower bound `H_n_single_pow_lower_bound`.
-/

public section

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]

omit h_n_eps_data in
lemma norm_sub_swap (n: ℕ) (a b: Matrix (Fin n) (Fin n) ℂ): ‖a - b‖ = ‖b - a‖ := by
  rw [← neg_sub]
  rw [norm_neg]


@[expose]
noncomputable def f (a: ℝ) (x: ℝ): ℝ := 1 + (2*x - 1)*a - (1 + a)^x

omit h_n_eps_data in
lemma f_one_eq_zero (a: ℝ): f a 1 = 0 := by
  simp [f]
  ring

omit h_n_eps_data in
lemma f_deriv (a: ℝ) (ha: 0 < 1 + a) (x: ℝ): (deriv (f a)) x = 2*a - (Real.log (1 + a))*(1 + a)^x := by
  unfold f
  simp_rw [← add_sub]
  rw [deriv_const_add]
  rw [← Pi.sub_def]
  rw [deriv_sub]
  · rw [deriv_mul_const]
    · rw [deriv_sub_const, deriv_const_mul]
      · simp
        have deriv_pow := (Real.hasStrictDerivAt_const_rpow (a := 1 + a) ha x).hasDerivAt.deriv
        simp [deriv_pow, mul_comm]
      · simp
    · simp
      apply DifferentiableAt.const_mul
      simp
  · apply DifferentiableAt.mul_const
    simp
    apply DifferentiableAt.const_mul
    simp
  · apply (Real.hasStrictDerivAt_const_rpow _ _).hasDerivAt.differentiableAt
    exact ha


lemma f_deriv_at_one (a: ℝ) (a_pos: 0 < a) (a_lt: a < 1) (ha: 0 < 1 + a): 0 < (deriv (f a) 1) := by
  rw [f_deriv _ ha]
  grw [Real.log_le_sub_one_of_pos]
  · have a_mul_self := mul_lt_of_lt_one_left (a := a) (b := a) (by linarith) (by linarith)
    simp only [add_sub_cancel_left, Real.rpow_one, sub_pos, gt_iff_lt]
    linarith
  simp [ha]


lemma f_deriv_lower (a: ℝ) (ha: 0 < 1 + a) (a_pos: 0 < a) (x: ℝ) (f_zero: (deriv (f a)) x = 0): (Real.log 2) / a ≤ x := by
  have log_plus_le: Real.log (1 + a) ≤ a := by
    grw [Real.log_le_sub_one_of_pos]
    · simp
    · exact ha

  have log_pos : 0 < Real.log (1 + a) := Real.log_pos (by linarith)
  have log_ne : Real.log (1 + a) ≠ 0 := ne_of_gt log_pos

  rw [f_deriv _ ha] at f_zero
  rw [sub_eq_zero] at f_zero
  nth_rw 2 [mul_comm] at f_zero
  replace f_zero := div_eq_of_eq_mul log_ne f_zero
  apply_fun Real.log at f_zero
  rw [Real.log_rpow ha] at f_zero
  replace f_zero := div_eq_of_eq_mul log_ne f_zero
  rw [Real.log_div (mul_ne_zero (by norm_num) a_pos.ne') log_ne,
    Real.log_mul (by norm_num) a_pos.ne'] at f_zero
  rw [← f_zero]

  have log_log_le : Real.log (Real.log (1 + a)) ≤ Real.log a :=
    Real.log_le_log log_pos log_plus_le

  calc Real.log 2 / a
      ≤ Real.log 2 / Real.log (1 + a) :=
        div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) log_pos log_plus_le
    _ ≤ (Real.log 2 + Real.log a - Real.log (Real.log (1 + a))) / Real.log (1 + a) :=
        div_le_div_of_nonneg_right (by linarith) log_pos.le

lemma f_pos_on (a: ℝ) (ha: 0 < 1 + a) (a_pos: 0 < a) (a_lt: a < 1)  (a_lt_log: a < Real.log 2): ∀ x ∈ Set.Ioc 1 (Real.log 2 / a), 0 < f a x := by

  have deriv_nonzero: ∀ x ∈ Set.Ico 1 (Real.log 2 / a), (deriv (f a)) x ≠  0 := by
    intro x hx
    by_contra!
    have x_eq := f_deriv_lower a ha a_pos x this
    have x_lt := hx.right
    linarith

  have one_lt : 1 < Real.log (2) / a := by
    rw [lt_div_iff₀]
    . simp
      exact a_lt_log
    . exact a_pos

  have f_strict := strictMonoOn_of_deriv_pos (f := f a) (D := Set.Icc 1 ((Real.log (2 )) / a)) (by apply convex_Icc) ?_ ?_
  .
    intro x hx
    have f_lt := f_strict.lt_iff_lt (a := 1) (b := x) ?_ ?_
    rw [f_one_eq_zero] at f_lt
    have x_prop := hx.left
    simp [x_prop] at f_lt
    . exact f_lt
    . simp
      linarith
    . simp
      simp at hx
      refine ⟨by linarith, hx.right⟩
  . apply Continuous.continuousOn
    unfold f
    have one_plus: 1 + a ≠ 0 := by linarith
    fun_prop (disch:=assumption)
  .

    intro x hx
    simp at hx

    have deriv_pos: 0 ≤ (deriv (f a)) x := by
      by_contra!
      have foo := ContinuousOn.surjOn_Icc (f := deriv (f a)) (a := x) (b := 1) (s := Set.Ico 1 ((Real.log 2) / a)) ?_ ?_ ?_

      have zero_mem: 0 ∈ (Set.Icc (deriv (f a) x) (deriv (f a) 1)) := by
        simp
        refine ⟨by linarith, ?_⟩
        have my_deriv := f_deriv_at_one a a_pos a_lt ha
        linarith


      unfold Set.SurjOn at foo
      have deriv_zero := foo zero_mem
      rw [Set.mem_image] at deriv_zero
      obtain ⟨y, y_mem, y_deriv⟩ := deriv_zero
      have y_nonzero := deriv_nonzero y y_mem
      . contradiction
      . apply Continuous.continuousOn
        unfold f
        have one_plus: ∀ x: ℝ, 1 + a ≠ 0 := by
          intro x
          linarith
        fun_prop (disch:=assumption)
      . simp
        refine ⟨by linarith, hx.right⟩
      . simp
        exact one_lt

    have not_zero := deriv_nonzero x ?_
    . exact lt_of_le_of_ne deriv_pos (id (Ne.symm not_zero))
    . simp
      refine ⟨by linarith, hx.right⟩

#print axioms f_pos_on


lemma H_n_single_pow_lower_bound {n : ℕ} {m : ℕ} (m_gt: 1 ≤ m) (data : HnData) (m_lt: m < (1/2) / ‖(theorem_3_8_h_n data n).g.val.val - 1‖) : ‖((theorem_3_8_h_n data n).g.val.val^m) - 1‖ ≥ ‖((theorem_3_8_h_n data n).g.val).val - 1‖ := by

  push_cast
  -- TODO: figure out how to get 'SubgroupClass.coe_zpow' to fire for Matrix.unitaryGroup

  conv =>
    lhs
    arg 1
    lhs
    arg 1
    equals (1 + ((theorem_3_8_h_n data n).g.val.val - 1)) =>
      simp

  rw [norm_sub_swap]
  have m_eq: m = (m - 1) + 1 := by
    omega

  rw[add_comm]
  rw [Commute.add_pow (by simp)]
  rw[Finset.sum_range_succ']
  conv =>
    lhs
    arg 1
    rhs
    simp

  nth_rw 1 [m_eq]
  rw [Finset.sum_range_succ']
  simp
  rw [← ge_iff_le]
  rw [← sub_eq_add_neg]
  grw [(norm_sub_norm_le _ _).ge]
  rw [norm_neg]
  --grw [norm_sum_le]


  have nonempty_d: Nonempty (Fin data.d) := by
    have data_pos := data.hd
    exact Fin.pos_iff_nonempty.mp (by linarith)

  have my_pow := Commute.add_pow (y := 1) (x := ‖((theorem_3_8_h_n data n).g.val.val - 1)‖) (n := m - 1 + 1) (by simp)
  rw [Finset.sum_range_succ'] at my_pow
  simp at my_pow
  rw [Finset.sum_range_succ'] at my_pow
  simp at my_pow
  rw [← m_eq] at my_pow
  rw [add_assoc] at my_pow
  apply sub_eq_of_eq_add at my_pow
  norm_cast at my_pow
  rw [← m_eq] at my_pow
  grw [norm_sum_le]

  grw [Finset.sum_le_sum (g := fun i => ‖((theorem_3_8_h_n data n).g.val.val - 1)‖ ^ (i + 1 + 1) * (m.choose (i + 1 + 1)))]
  .
    rw [← my_pow]

    have S_le : (1 + ‖((theorem_3_8_h_n data n).g).val.val - 1‖)^m - ((‖(theorem_3_8_h_n data n).g.val.val - 1‖) * (m : ℝ) + 1) ≤ (m - 1) * ‖(theorem_3_8_h_n data n).g.val.val - 1‖ := by
      by_cases m_eq_one: m = 1
      .
        simp [m_eq_one]
        rw [add_comm]
      .
        have my_bound := f_pos_on ‖((theorem_3_8_h_n data n).g.val.val - 1)‖  ?_ ?_ ?_ ?_ m ?_
        simp [f] at my_bound
        rw [two_mul] at my_bound
        rw [← add_sub] at my_bound
        rw [add_mul] at my_bound
        rw [← add_assoc] at my_bound
        apply sub_left_lt_of_lt_add at my_bound
        rw [← gt_iff_lt] at my_bound
        rw [← ge_iff_le]
        grw [my_bound]
        simp
        ring_nf
        . rfl
        . positivity
        .
          have val_ne := (theorem_3_8_h_n data n).g_dist_nonzero
          positivity
        .
          have val_le := (theorem_3_8_h_n data n).g_dist
          grw [val_le]
          grw [H_n_eps_lt]
          norm_num
        .
          have val_le := (theorem_3_8_h_n data n).g_dist
          grw [val_le]
          grw [H_n_eps_lt]
          norm_num
          linarith [Real.log_two_gt_d9]
        . simp
          refine ⟨by omega, ?_⟩
          grw [← ge_iff_le]
          grw [Real.log_two_gt_d9.gt]
          simp
          grw [m_lt]
          simp
          apply div_le_div₀
          . norm_num
          . norm_num
          . have ne_zero := (theorem_3_8_h_n data n).g_dist_nonzero
            positivity
          . rfl


    rw [add_comm]
    grw [S_le]
    nth_rw 2 [sub_mul]
    rw [mul_comm]
    rw [← mul_comm]
    simp
    have my_smul := norm_smul (m : ℂ) ((theorem_3_8_h_n data n).g.val.val - 1)
    simp at my_smul
    rw [← my_smul]
    conv =>
      rhs
      rhs
      lhs
      arg 1
      equals ((theorem_3_8_h_n data n).g.val.val - 1) * m =>
        rw [Matrix.smul_eq_mul_diagonal]
        rw [← Matrix.diagonal_natCast]

    ring_nf
    rfl

  . intro i hi
    grw [norm_mul_le]
    grw [norm_pow_le]
    nth_rw 2 [Matrix.l2_opNorm_def]
    grw [ContinuousLinearMap.opNorm_le_bound (M := m.choose (i + 1 + 1))]
    . simp
    .
      intro x
      simp
      rw [Matrix.toEuclideanLin_apply]
      simp
      rw [norm_smul]
      simp

  --apply_fun Norm.norm at my_pow

#synth DivisionMonoid (Matrix.unitaryGroup (Fin 2) ℂ)


#synth DivInvMonoid (Matrix (Fin 2) (Fin 2) ℂ)


-- TODO: upstream to mathlib
omit h_n_eps_data in
lemma list_ofFn_drop {M: Type*} (a k: ℕ) (f: Fin (k + a) → M): (List.ofFn f).drop a = List.ofFn (fun (i: Fin k) => f ⟨a + i, by omega⟩) := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    rw [List.ofFn_congr (n := (k + a) + 1) (by linarith)]
    simp
    have list_eq := ih (fun i => f i.succ)
    rw [list_eq]
    simp
    funext b
    group

end HnEpsData
