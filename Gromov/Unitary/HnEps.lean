import Mathlib
import Gromov.Unitary.WeylTrick

/-!
# The sets `H_n` and their upper bounds

The `HnEpsData` bundle of standing hypotheses, the sets `H_n eps`, and upper bounds on products
of their elements.
-/

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative

set_option maxSynthPendingDepth 1

open scoped Pointwise Finset

structure SPolyData {T: Type*} [DecidableEq T] [Group T] (G : Subgroup T) where
  S: Set G
  S_finite: Set.Finite S
  S_one: 1 ∈ S
  S_inv: S = S⁻¹
  S_generates: Subgroup.closure S = ⊤
  S_poly_const: ℕ
  S_poly_const_pos: 0 ≠ S_poly_const
  S_poly_deg: ℕ
  S_poly: ∀ r ≥ 1, #(S_finite.toFinset ^ r) ≤ S_poly_const * (r ^ S_poly_deg)

class HnEpsData where
  degree: ℕ


namespace HnEpsData
variable [h_n_eps_data: HnEpsData]

-- A sufficiently small epsilon to use for the h_n elements in Theorem 3.8 (independent of the choice of n)
noncomputable def H_n_eps {d : ℕ} (hd : 2 ≤ d): ℝ := min (((1 : ℝ) / 60)) (min (((1 : ℝ) / 60) / ((Real.exp (4 + h_n_eps_data.degree * Real.log 2) + 1))) ((small_dist_matrix d hd).choose / 2))

-- H_n_eps is less than 1/2
lemma H_n_eps_lt {d : ℕ} (hd : 2 ≤ d) : H_n_eps hd < ((1 : ℝ) / 4) := by
  simp [H_n_eps]
  left
  norm_num


lemma H_n_eps_pos {d : ℕ} (hd : 2 ≤ d) : 0 < H_n_eps hd := by
  simp [H_n_eps]
  refine ⟨?_, ?_⟩
  . positivity
  .
    have small_pos := (small_dist_matrix d hd).choose_spec
    linarith


open scoped Finset
open scoped Pointwise


structure HnData where
  d : ℕ
  hd : 2 ≤ d
  G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)
  G_central_trivial : ∀ g : G, g ∈ Set.center G → ∃ z : ℂ, g.val.val = z • 1
  S : Set G
  S_generates : Subgroup.closure S = ⊤
  S_finite : S.Finite
  S_one: 1 ∈ S
  S_inv: ∀ s ∈ S, s⁻¹ ∈ S
  S_dist : ∀ s ∈ S, ‖s.val.val - 1‖ ≤ (H_n_eps hd)
  S_poly_const: ℕ
  S_poly_const_pos: 0 ≠ S_poly_const
  S_poly_deg: ℕ
  S_poly: ∀ r ≥ 1, #(S_finite.toFinset ^ r) ≤ S_poly_const * (r ^ S_poly_deg)
  h : S
  h_nontrivial : ¬ ∃(z : ℂ), h.val.val.val = z • 1

structure Theorem3_8_Data (data: HnData) where
  g: data.G
  g_nontrivial : ¬ ∃ z : ℂ, g.val.val = z • 1
  g_dist_nonzero : ‖g.val.val - 1‖ ≠ 0
  g_dist : ‖g.val.val - 1‖ ≤ (H_n_eps data.hd)


-- The element of S in the left-hand side of the commutator in theorem_3_8_h_n
theorem theorem_3_8_h_n_left_S (data: HnData) (prev: Theorem3_8_Data data): ∃ s : data.S, ∀ z : ℂ, ⁅s.val.val, prev.g.val⁆.val ≠ z • 1 := by
  by_contra!
  have comm_eq_id : ∀ s : data.S, ⁅s.val.val, prev.g.val⁆ = 1 := by
    intro s
    obtain ⟨z, comm_eq_z⟩ := this s
    have norm_z : ‖z‖ = 1 := by
      have z_mul_unitary : z • 1 ∈ Matrix.unitaryGroup (Fin data.d) ℂ := by
        rw [← comm_eq_z]
        simp


      have det_unitary := Matrix.det_of_mem_unitary z_mul_unitary
      simp at det_unitary
      apply CStarRing.norm_of_mem_unitary at det_unitary
      simp at det_unitary
      have d_ne_zero : data.d ≠ 0 := by
        have hd := data.hd
        omega
      have z_pow := (pow_eq_one_iff_of_ne_zero (a := ‖z‖) d_ne_zero).mp det_unitary
      have norm_pos : 0 ≤ ‖z‖ := by
        positivity
      have norm_not_neg : ‖z‖ ≠ -1 := by
        linarith

      simp [norm_not_neg] at z_pow
      exact z_pow
    have det_one : ⁅s.val.val, prev.g.val⁆.val.det = 1 := by
      simp [Bracket.bracket]
      rw [Matrix.star_eq_conjTranspose]
      rw [Matrix.star_eq_conjTranspose]
      rw [mul_comm]
      rw [mul_assoc]
      nth_rw 2 [mul_comm]
      rw [mul_assoc]
      rw [← Matrix.det_mul]
      rw [← Matrix.star_eq_conjTranspose]
      rw [← Matrix.star_eq_conjTranspose]
      rw [Matrix.UnitaryGroup.star_mul_self]
      rw [← mul_assoc]
      rw [← Matrix.det_mul]
      rw [Matrix.UnitaryGroup.star_mul_self]
      simp

    have prev_prop := prev.g_dist
    have norm_le := shrinking_conjugators data.d s.val prev.g.val
    grw [data.S_dist s, prev_prop] at norm_le
    · have two_mul_le : 2 * (H_n_eps data.hd) ≤ 1 := by
        grw [H_n_eps_lt data.hd]
        norm_num
      grw [two_mul_le] at norm_le
      · simp at norm_le


        let C := (small_dist_matrix data.d data.hd).choose

        have H_eps_lt_C : H_n_eps data.hd < C := by
          rw [H_n_eps]
          unfold C
          grw [min_le_right]
          simp
          right
          have my_spec := (small_dist_matrix data.d data.hd).choose_spec
          linarith

        unfold C at H_eps_lt_C


        obtain ⟨C_pos, small_eps⟩ := (small_dist_matrix data.d data.hd).choose_spec
        have z_eq_one := small_eps ⁅s.val.val, prev.g.val⁆.val det_one z norm_z (by
          simp [diag_unitary]
          rw [← Matrix.smul_one_eq_diagonal]
          exact comm_eq_z
        ) (by
          grw [norm_le]
          exact H_eps_lt_C
        )
        simp [z_eq_one] at comm_eq_z
        exact comm_eq_z
      · -- TODO - deduplicate this
        have foo := H_n_eps_pos data.hd
        linarith
    · have foo := H_n_eps_pos data.hd
      linarith
    · simp
  · have subgroup_le := Subgroup.closure_le_centralizer_centralizer data.S
    simp [data.S_generates] at subgroup_le
    have prev_mem_centralizer : prev.g ∈ Subgroup.centralizer data.S := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h_comm := comm_eq_id ⟨s, hs⟩
      simp [Bracket.bracket] at h_comm
      rw [mul_assoc] at h_comm
      apply eq_inv_of_mul_eq_one_left at h_comm
      simp at h_comm
      rw [Subtype.ext_iff]
      simp
      exact h_comm

    have prev_central := subgroup_le prev_mem_centralizer
    have prev_trivial := data.G_central_trivial _ prev_central
    have prev_nontrivial := prev.g_nontrivial
    contradiction


-- 'h' is our initial element - we define ε in terms of ‖h - 1‖, so that we can obtain the proper bound
-- for the commutators in the inductive case
set_option maxHeartbeats 500000 in
noncomputable def theorem_3_8_h_n (data : HnData) (n : ℕ): Theorem3_8_Data data := match hn : n with
  | 0 => {
    g := data.h,
    g_nontrivial := data.h_nontrivial,
    g_dist_nonzero := by
      by_contra!
      simp at this
      rw [sub_eq_zero] at this
      have h_nontrivial := data.h_nontrivial
      simp at h_nontrivial
      have h_neq := h_nontrivial 1
      simp at h_neq
      simp at this
      contradiction
    ,
    g_dist := data.S_dist data.h data.h.property
  }
  | k + 1 => by
    -- TODO - why do we get a heartbeat timeout if we inline 'prev'?
    let prev := (theorem_3_8_h_n data k)
    use ⁅(theorem_3_8_h_n_left_S data prev).choose.val, prev.g⁆
    · rw [not_exists]
      exact (theorem_3_8_h_n_left_S data prev).choose_spec
    · by_contra!
      simp at this
      rw [sub_eq_zero] at this
      have my_nontrivial := (theorem_3_8_h_n_left_S data prev).choose_spec 1
      simp at my_nontrivial
      simp at this
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      rw [commutatorElement_eq_one_iff_mul_comm] at my_nontrivial
      rw [Subtype.ext_iff] at this
      simp at this
      contradiction
    · have my_shrink := shrinking_conjugators data.d (theorem_3_8_h_n_left_S data prev).choose prev.g
      conv =>
        lhs
        arg 1
        lhs
        equals ⁅ (theorem_3_8_h_n_left_S data prev).choose.val.val, prev.g.val ⁆.val =>
          rw [commutatorElement_def, commutatorElement_def]
          rfl
      grw [my_shrink]
      have prev_prop := prev.g_dist
      grw [prev_prop]
      have comm_choose_le := data.S_dist (theorem_3_8_h_n_left_S data prev).choose (by simp)
      grw [comm_choose_le]
      have two_mul_le : 2 * (H_n_eps data.hd) ≤ 1 := by
        grw [H_n_eps_lt data.hd]
        norm_num
      grw [two_mul_le]
      · simp
      · linarith [H_n_eps_pos data.hd]
      · linarith [H_n_eps_pos data.hd]


termination_by n
decreasing_by
  simp

#print axioms theorem_3_8_h_n

omit h_n_eps_data in
lemma unitary_shrink {n : ℕ} (a b : Matrix.unitaryGroup (Fin n) ℂ): ‖(a * b).val - 1‖ ≤ ‖a.val - 1‖ + ‖b.val - 1‖ := by
  conv =>
    lhs
    arg 1
    arg 1
    equals (a.val - 1) * b + b =>
      rw [sub_mul]
      simp

  rw [← add_sub]
  grw [norm_add_le]
  rw [CStarRing.norm_mul_coe_unitary]


lemma H_n_upper_bound (data : HnData) (n : ℕ): ‖(theorem_3_8_h_n data (n + 1)).g.val.val - 1‖ ≤ 2 * (H_n_eps data.hd) * ‖(theorem_3_8_h_n data (n)).g.val.val - 1‖ := by
  conv =>
    lhs
    unfold theorem_3_8_h_n
  simp
  have coe_comm_g (a b : data.G): ⁅a.val, b.val⁆ = ⁅a, b⁆.val := by
    rw [commutatorElement_def]
    rw [commutatorElement_def]
    norm_cast

  rw [← coe_comm_g]
  grw [shrinking_conjugators]
  grw [data.S_dist]
  simp

lemma H_n_upper_bound_iter (data : HnData) {a : ℕ} (n : ℕ): ‖(theorem_3_8_h_n data (a + n)).g.val.val - 1‖ ≤ ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ * 2^n * (H_n_eps data.hd)^n  := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [← add_assoc]
    grw [H_n_upper_bound]
    grw [ih]
    abel_nf
    · ring_nf
      rfl
    · simp
      have H_eps_pos := H_n_eps_pos data.hd
      linarith


lemma H_n_single_pow {n : ℕ} {m : ℕ} (data : HnData): ‖((theorem_3_8_h_n data n).g.val^m).val - 1‖ ≤ m * ‖(theorem_3_8_h_n data n).g.val.val - 1‖ := by
  induction m with
  | zero =>
    simp [pow_zero]
  | succ m ih =>
    rw [pow_succ]
    grw [unitary_shrink]
    grw [ih]
    simp
    rw [add_mul]
    simp

lemma H_n_pow_le  {a k : ℕ } {m : ℕ} (a_k_lt : a + k ≤ m)  (pows : Fin m → ℕ) (data : HnData):
  ‖(List.ofFn (fun (i : Fin (k)) => (theorem_3_8_h_n data (a + i)).g^(pows ⟨(a + i), by (have foo := i.isLt; omega)⟩))).prod.val.val - 1‖ ≤ ∑ (i : Fin k), (pows ⟨(a + i), by (have foo := i.isLt; omega)⟩) * ‖(theorem_3_8_h_n data (a + i)).g.val.val - 1‖ := by
  induction k with
  | zero =>
    simp [List.ofFn, List.prod_nil]
  | succ k ih =>
    simp only [ne_eq, List.ofFn_succ']
    simp only [Fin.coe_castSucc, Fin.val_last, List.concat_eq_append, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, Subgroup.val_list_prod,
      List.map_ofFn]

    rw [Subgroup.coe_mul]
    grw [unitary_shrink]
    have prev_le := ih (by linarith)
    grw [prev_le]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_range_succ]
    rw [SubmonoidClass.coe_pow]
    grw [H_n_single_pow]
    simp
    nth_rw 2 [← Finset.sum_attach]


    conv =>
      rhs
      arg 2
      intro x
      equals if h : ↑x < k then ↑(pows ⟨↑(a + x), by omega⟩) * ‖(theorem_3_8_h_n data ↑(a + x)).g.val.val - 1‖ else 0 =>
        have x_lt_m := x.property
        rw [Finset.mem_range] at x_lt_m
        have x_lt_m_succ : x.val < k + 1 := by
          omega
        simp [x_lt_m, Nat.le_of_lt_succ x_lt_m_succ]

    rw [← Finset.sum_attach]


-- Equation 3.16
lemma H_n_prod_le_k {a k : ℕ } {m : ℕ} (a_k_lt : a + k + 1 ≤ m) (c : ℝ) (c_pos : 0 < c) (c_lt : c < 1 / 40) (pows : Fin m → ℕ) (data : HnData)
 (pows_le : ∀ i : Fin m, (pows i) ≤ c * (H_n_eps data.hd)⁻¹) :
  ‖(List.ofFn (fun (i : Fin (k)) => (theorem_3_8_h_n data ((a + 1) + i)).g^(pows ⟨((a + 1) + i), by omega⟩))).prod.val.val - 1‖ ≤ ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ / 10 := by


  grw [H_n_pow_le]
  grw [Finset.sum_le_sum (g := (fun i : Fin (k) => (c * (H_n_eps data.hd)⁻¹) * ‖(theorem_3_8_h_n data ((a + 1) + i)).g.val.val - 1‖))]
  · rw [← Finset.mul_sum]
    grw [Finset.sum_le_sum (g := (fun i : Fin (k) => ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ * 2^(1 + i.val) * (H_n_eps data.hd)^(1 + i.val)))]
    · have eps_nonneg := H_n_eps_pos data.hd
      simp
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      simp_rw [← mul_pow]
      simp_rw [add_comm]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
      rw [Finset.sum_fin_eq_sum_range]
      rw [Finset.sum_congr (s₁ := Finset.range k) (s₂ := Finset.range k) (g := fun i => (2 * H_n_eps data.hd) ^ i)]

      nth_rw 4 [mul_comm]
      rw [Finset.range_eq_Ico, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      grw [geom_sum_Ico_le_of_lt_one]
      simp
      -- TODO - make this a lemma
      have two_mul_le : 2 * (H_n_eps data.hd) < (1 / 2) := by
        have foo := H_n_eps_lt data.hd
        linarith
      nth_grw 2 [two_mul_le]
      field_simp
      norm_num
      have eps_ne_zero : 0 ≠ (H_n_eps data.hd) := by
        linarith


      ring_nf
      field_simp [eps_ne_zero]

      grw [c_lt]
      ring
      rfl
      · positivity
      · grw [H_n_eps_lt data.hd]
        norm_num
      · rfl
      · intro x hx
        simp at hx
        simp [hx]
    · simp [c_pos]
      have pos := H_n_eps_pos data.hd
      linarith
    -- H_n_upper_bound_iter
    · intro i hi
      rw [add_assoc]
      grw [H_n_upper_bound_iter data]
  · intro i hi
    grw [pows_le]
  · omega

#print axioms H_n_prod_le_k

#synth Semiring (Matrix (Fin 2) (Fin 2) ℂ)

end HnEpsData
