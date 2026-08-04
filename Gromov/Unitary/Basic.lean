module

public import Mathlib
public import Gromov.ToMathlib.Analysis.Matrix.Unitary
public import Gromov.ToMathlib.GroupTheory.Closure
public import Gromov.ToMathlib.Analysis.Matrix.Norm

/-!
# Subgroups of the unitary group

Properness and compactness of the unitary group, the transfer of polynomial growth along a
group isomorphism, and the distance estimate `small_dist_matrix`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative

set_option maxSynthPendingDepth 1

-- The `open scoped IsMulCommutative` above activates a low-priority
-- `Group + IsMulCommutative ⇒ CommGroup` instance.  Combined with Mathlib's
-- build-wide `maxSynthPendingDepth 3`, synthesizing the group structure of
-- `↥(Matrix.unitaryGroup (Fin n) ℂ)` blows up the instance search.  Reverting
-- to the historical default depth keeps that synthesis fast.
set_option maxSynthPendingDepth 1

-- Like 'mem_closure_prod_list', but without requring that the generating set be symmetric
lemma weak_mem_closure_prod_list {G: Type*} [Group G] (S: Set G) (x: G) (hx: x ∈ Subgroup.closure S): ∃ l: List (↑(S ∪ S⁻¹)), l.unattach.prod = x := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  specialize foo hx
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold List.unattach
  simp [prod_eq]


-- Proof of proposition 2.18
-- Note - we additionaly assume that the generating set contains 1, as this us use a simpler
-- definition of polynomial growth (since S^n ⊆ S^(n+1))
-- We use this requirement throughout the entire proof, so it's fine
-- At the very start of the proof, we'll use a more general definition of polynomial growth
-- (using the word metric) to drop the assumptions on our generating set,
-- and then reduce the proof to the case of a symmetric generating set containing 1
lemma poly_growth_equiv {G: Type*} [DecidableEq G] [Group G] (a d: ℕ)
  (a_pos: 0 < a)
  (S S': Finset G)
  (S_symm: S = S⁻¹)
  (S_one: 1 ∈ S)
  (S_generates: Subgroup.closure (S : Set G) = ⊤)
  (s_poly: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d):
  ∃ b: ℕ, 1 ≤ b ∧ ∀ n ≥ 1, #(S' ^ n) ≤ b * n^d := by


  by_cases g_nontrivial: Nontrivial G
  .
    let S'_prod := fun (s: S') => (weak_mem_closure_prod_list S s.val (by
      simp [S_generates]
    )).choose

    let all_lists := (Finset.image S'_prod Finset.univ)
    let max_len := all_lists.sup (fun l => l.length)
    by_cases max_len_zero: max_len = 0
    .
      unfold max_len at max_len_zero
      simp at max_len_zero
      simp [all_lists] at max_len_zero


      have S'_one: S' ⊆ {1} := by
        intro s' hs'
        have bad_prod := max_len_zero (S'_prod ⟨s', hs'⟩) s' hs' rfl
        simp [S'_prod] at bad_prod
        have s'_prod := (weak_mem_closure_prod_list S s' (by
          simp [S_generates]
        )).choose_spec
        rw [bad_prod] at s'_prod
        simp at s'_prod
        rw [← s'_prod]
        simp

      have S'_le: #(S') ≤ 1 := by
        grw [Finset.card_le_card (t := {1})]
        simp
        apply S'_one


      use 1
      refine ⟨by simp, ?_⟩
      intro n hn
      simp
      grw [Finset.card_pow_le]
      grw [S'_le]
      simp
      exact Nat.one_le_pow d n hn

    .
      have start_pos_nonzero: 1 ≤ max_len := by omega
      use a * (max_len ^ d)
      refine ⟨?_, ?_⟩
      .
        rw [Nat.one_le_iff_ne_zero]
        apply Nat.mul_ne_zero
        . omega
        .
          rw [← Nat.pos_iff_ne_zero]
          apply Nat.pow_pos
          omega
      intro n hn


      grw [Finset.card_le_card (t := (S ^ max_len) ^ n)]

      .
        rw [← pow_mul]
        grw [s_poly _ (by exact Right.one_le_mul start_pos_nonzero hn)]
        rw [mul_pow]
        rw [← mul_assoc]
      .
        intro s' hs'

        have S'_subset_s_pow: S' ⊆ (S ^ max_len) := by
          intro a a'


          let exists_list := (weak_mem_closure_prod_list S a (by
            simp [S_generates]
          ))
          let l := exists_list.choose
          have l_prop := exists_list.choose_spec

          have len_le_max: l.length ≤ max_len := by
            unfold max_len
            apply le_sup
            simp [all_lists]
            use a
            use a'


          let foo := Fin.append (fun i => l[i].val) (fun (i: Fin (max_len - l.length)) => 1)
          rw [Finset.mem_pow]
          use (fun i => ⟨(foo ⟨i.val, by omega⟩), by (
            unfold foo
            simp
            unfold Fin.append
            unfold Fin.addCases
            simp
            split_ifs
            .
              rename_i i_lt
              have l_i_prop := l[i].property
              nth_rw 2 [S_symm] at l_i_prop
              simp at l_i_prop
              exact l_i_prop
            . apply S_one
          )⟩)
          conv =>
            rhs
            rw [← l_prop]
          unfold foo
          simp
          have add_sub: max_len = l.length + (max_len - l.length)  := by omega
          rw [List.ofFn_congr add_sub]
          simp
          rfl

        have pow_subset := Finset.pow_subset_pow S'_subset_s_pow (m := n) (n := n) (by
          have S_subset: S^1 ⊆ S^max_len := by
            apply Finset.pow_subset_pow
            . simp
            . apply S_one
            . omega

          simp at S_subset
          exact S_subset S_one
        ) (by omega)

        exact pow_subset hs'
  .
    rw [← not_subsingleton_iff_nontrivial] at g_nontrivial
    simp at g_nontrivial
    use 1
    refine ⟨by simp, ?_⟩
    intro n hn
    simp
    grw [Finset.card_pow_le]
    grw [Finset.card_le_one_of_subsingleton]
    simp
    exact Nat.one_le_pow d n hn


#print axioms poly_growth_equiv


-- Lemma 3.29 (Shrinking Conjugators)
lemma shrinking_conjugators (n : ℕ) (g h : Matrix.unitaryGroup (Fin n) ℂ) :
  ‖⁅g, h⁆.val - 1‖ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
  dsimp only [Bracket.bracket]
  calc
    _ = ‖((g* h).val - (h * g).val) * (g⁻¹ * h⁻¹)‖ := by
      rw [sub_mul]
      repeat rw [← Submonoid.coe_mul]
      conv =>
        rhs
        arg 1
        rhs
        arg 1
        equals 1 => group
      repeat rw [← mul_assoc]
      simp
    _ = ‖((g* h).val - (h * g).val)‖ := by
      rw [ ← Submonoid.coe_mul, CStarRing.norm_mul_coe_unitary]
    _ = ‖(g* h).val - g - h + 1 - ((h*g).val - h - g + 1)‖ := by abel_nf
    _ = ‖(g.val - 1)*(h.val - 1) - (h.val - 1)*(g.val - 1)‖ := by
      conv =>
        rhs
        repeat rw [mul_sub]
        repeat rw [sub_mul]
      simp
      abel_nf
    _ ≤ ‖(g.val - 1)*(h.val - 1)‖ + ‖(h.val - 1)*(g.val - 1)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
      linarith [Matrix.l2_opNorm_mul (g.val - 1) (h.val - 1),
                Matrix.l2_opNorm_mul (h.val - 1) (g.val - 1)]

def G' (n : ℕ) (ε : ℝ) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) : Subgroup G :=
  Subgroup.closure (Metric.ball (1 : G) ε)


lemma unitary_preimage (n : ℕ) :
    (fun (m : Matrix (Fin n) (Fin n) ℂ) => m * (star m)) ⁻¹' {1} =
    (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  ext
  simp [Matrix.mem_unitaryGroup_iff]

lemma unitary_closed (n : ℕ) : IsClosed (Matrix.unitaryGroup (Fin n) ℂ).carrier := by
  rw [← unitary_preimage]
  apply IsClosed.preimage
  · fun_prop
  · simp


instance unitary_proper (n : ℕ) : ProperSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  apply ProperSpace.of_isClosed
  apply unitary_closed

#synth Nontrivial (Matrix (Fin 1) (Fin 1) ℂ)


instance compact_unitary (n : ℕ) [Nonempty (Fin n)] :
    CompactSpace ↥(Matrix.unitaryGroup (Fin n) ℂ) := by
  rw [Metric.compactSpace_iff_isBounded_univ, Metric.isBounded_iff]
  use 2
  intro x _ y _
  rw [Subtype.dist_eq]
  grw [dist_le_norm_add_norm]
  rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
  linarith


abbrev diag_unitary (c : ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun _ => c)

lemma small_dist_matrix (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ (∀ h : Matrix (Fin n) (Fin n) ℂ, h.det = 1 → ∀ c : ℂ, ‖c‖ = 1 → h = diag_unitary c n → (‖h - 1‖ < C) → c = 1) := by


  have nezero_n : NeZero n := ⟨by omega⟩
  let dists := (fun (x : ℂ) => (‖x - 1‖ : ℝ)) '' ((Units.val '' (rootsOfUnity n ℂ).carrier \ {1}))

  -- TODO - why can't we combine these into a single line?
  have foo := Set.Finite.exists_minimal (s := dists) ?_ ?_
  obtain ⟨min_dist, ⟨h_min, h_min_prop⟩⟩ := foo
  · refine ⟨min_dist, ?_, ?_⟩
    · simp only [dists, Set.mem_image] at h_min
      obtain ⟨x, x_mem, min_dist_eq⟩ := h_min
      simp at x_mem
      by_contra!
      by_cases min_dist_lt : min_dist < 0
      · rw [← min_dist_eq] at min_dist_lt
        linarith [norm_nonneg (x - 1)]

      simp [show min_dist = 0 by linarith, sub_eq_zero] at min_dist_eq
      have x_neq_one := x_mem.2
      contradiction

    intro h h_det c hc h_mul h_dist

    have c_nonzero : c ≠ 0 := by
      by_contra!
      rw [this] at hc
      simp at hc

    have ne_zero_n : NeZero n := by
      rw [neZero_iff]
      linarith

    let c_unit : Units ℂ := {
        val := c,
        inv := c⁻¹,
        val_inv := by field_simp
        inv_val := by field_simp
      }


    have det_eq_c_n : h.det = c^n := by
      rw [h_mul]
      simp


    rw [h_det] at det_eq_c_n

    rw [h_mul] at h_dist
    simp [diag_unitary] at h_dist

    conv at h_dist =>
      arg 1
      arg 1
      lhs
      equals c • (Matrix.diagonal (fun _ => 1)) =>
        rw [← Matrix.smul_one_eq_diagonal]
        simp

    rw [Matrix.diagonal_one] at h_dist
    conv at h_dist =>
      arg 1
      arg 1
      rhs
      equals (1 : ℂ) • 1 =>
        simp
    rw [← sub_smul] at h_dist
    rw [norm_smul] at h_dist
    conv at h_dist =>
      lhs
      rhs
      equals (1 : ℝ) =>
        bound

    simp at h_dist

    by_contra!


    have c_dist_e : min_dist < ‖ c - 1‖ := by
      have c_dist  := h_min_prop (y := ‖c - 1‖)
      simp [dists] at c_dist
      have dist_ge := c_dist c_unit ?_ ?_ ?_
      · by_contra!
        specialize dist_ge (by linarith)
        linarith
      · simp [c_unit]
        ext
        simp
        rw [det_eq_c_n]
      · simp [c_unit]
        rw [Units.ext_iff]
        simp
        simp [this]
      · simp [c_unit]
    linarith
  · simp [dists]
    apply Set.Finite.image
    apply Set.Finite.diff
    apply Set.Finite.image


    have finite_roots : Finite ↥(rootsOfUnity n ℂ) := by infer_instance
    -- TODO - how is this working???
    exact finite_roots
  · --have n_gt_one : 1 < n := by omega
    simp [dists]
    rw [Set.diff_nonempty]
    simp

    let my_root : Units ℂ := {
      val := Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)),
      inv := (Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)))⁻¹
      val_inv := by simp
      inv_val := by simp
    }
    use my_root
    simp [my_root]
    refine ⟨?_, ?_⟩
    · ext
      simp
      rw [← Complex.exp_nat_mul, mul_comm]
      field_simp
      simp
    · simp [Units.ext_iff, Complex.exp_eq_one_iff]
      intro a
      conv =>
        arg 1
        rhs
        rw [mul_comm]
      field_simp
      by_contra!
      simp at this
      field_simp at this
      have abs_lt_one : ‖((1 : ℂ) / ↑n)‖ < 1 := by
        simp
        have div_le := Nat.cast_inv_le_one (α := ℝ) n
        by_cases inv_eq_one : (n : ℝ)⁻¹ = 1
        · simp at inv_eq_one div_le
          linarith
        · simpa [← ne_iff_lt_iff_le, show n ≠ 1 by omega] using div_le
      by_cases a_eq_zero : a = 0
      · simp [a_eq_zero] at this
        omega
      · simp [this] at abs_lt_one
        norm_cast at abs_lt_one
        linarith [Int.one_le_abs a_eq_zero]

#print axioms small_dist_matrix

-- Lemma 3.31 (Volume Packing)
