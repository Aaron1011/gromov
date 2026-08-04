import Mathlib
import Gromov.HarmonicR2

/-!
# The quadratic form `Q_R` and its determinant bound

The quadratic form `Q_R` on `LipschitzH`, its matrix `Q_R_matrix`, positive-definiteness, and
the determinant bound `det_bound` for a fixed finite-dimensional subspace `V`.
-/

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

noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)

lemma Q_R_self_nonneg (R : ℝ) (v : G → ℝ) : 0 ≤ Q_R R v v := by
  simp [Q_R, ← pow_two]; positivity
noncomputable def Q_R_lin (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R u.val v.val
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}


noncomputable def Q_R_lin_plain (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R u.val v.val
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}

open scoped Topology

-- These definitions go outside, since we need to explicitly vary the V that we pass in for the theorem statement
noncomputable def V_basis (V: Submodule ℝ LipschitzH) := Module.Basis.ofVectorSpace ℝ V
noncomputable def Q_R_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (R: ℝ) := ((Q_R_lin V R).toMatrix₂ b b)
noncomputable def my_expr {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (d: ℝ) (R : ℕ) := #(S ^ R) * ((Q_R_matrix b R).det ^ ((1 : ℝ) / Module.finrank ℝ V)) / (R ^ d)
-- This is a liminf < ∞ in Vikman, but we can actually prove that it goes to 0, which makes things much easier to work with
noncomputable def growth_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (d: ℝ) := Filter.Tendsto (fun (R: ℕ) => my_expr b d R) (Filter.atTop) ((𝓝[>] 0))

lemma Q_R_lin_symm (V: Submodule ℝ LipschitzH) (R: ℝ): (Q_R_lin V R).IsSymm := {
  eq := by
    intro u v
    simp [Q_R_lin, Q_R]
    simp_rw [mul_comm]
}

lemma Q_R_lin_hermetian {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (R: ℝ): (Q_R_matrix b R).IsHermitian := by
  rw [Q_R_matrix, ← LinearMap.isSymm_iff_isHermitian_toMatrix]
  apply Q_R_lin_symm

lemma Q_R_lin_sub_pos_semi_def (V : Submodule ℝ LipschitzH) (R_1 R_2: ℝ) (hr: R_1 ≤ R_2): ((Q_R_lin V R_2) - Q_R_lin V R_1).IsPosSemidef := by
  rw [LinearMap.isPosSemidef_def]
  refine ⟨?_, ?_⟩
  .
    rw [sub_eq_add_neg]
    apply LinearMap.IsSymm.add
    . apply Q_R_lin_symm
    .
      -- TODO - add smul/neg lemmas so that we don't need to inline the proof here
      exact {
        eq := by
          intro u v
          simp [Q_R_lin, Q_R]
          simp_rw [mul_comm]
    }
  .
    rw [LinearMap.isNonneg_def]
    intro x
    simp [Q_R_lin, Q_R]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    .
      simp [Metric.closedBall]
      grind
    . intro a ha a_not
      rw [← pow_two]
      positivity

lemma v_r_all_nonzero (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V]: ∃ R: ℝ, 1 < R ∧ ∀ u ∈ V, u ≠ 0 → ∃ g ∈ Metric.closedBall 1 R, u g ≠ 0 := by
  let zero_ball (n: ℕ): Submodule ℝ V := {
      carrier := {v: V | ∀ g ∈ Metric.closedBall 1 n, v.val g = 0}
      add_mem' := by
        intro a b ha hb
        simp at ha hb
        simp
        grind
      zero_mem' := by
        simp
      smul_mem' := by
        intro c x hx
        simp at hx
        simp
        intro g hg
        grind
  }

  let f: ℕ →o (Submodule ℝ V)ᵒᵈ := {
    toFun := zero_ball
    monotone' := by
      intro a b hab x hx
      simp [zero_ball] at hx
      simp [zero_ball]
      intro g hg
      apply hx g
      grw [hab] at hg
      exact hg
  }
  have artintian: IsArtinian ℝ V := by infer_instance
  rw [← monotone_stabilizes_iff_artinian] at artintian
  specialize artintian f
  obtain ⟨n, hn⟩ := artintian

  have inter_zero: ⨅ n: ℕ, zero_ball n = 0 := by
    ext a
    simp only [Submodule.mem_iInf, Submodule.zero_eq_bot, Submodule.mem_bot]
    refine ⟨?_, ?_⟩
    .
      intro hi
      ext g
      specialize hi (WordNorm g)
      simp [zero_ball] at hi
      specialize hi g
      simp [dist, WordDist_one] at hi
      simp [hi]
    . intro hi
      simp [hi]

  rw [← Antitone.iInf_nat_add (k := n)] at inter_zero
  .
    conv at inter_zero =>
      lhs
      arg 1
      intro k
      equals zero_ball n =>
        specialize hn (k + n) (by simp)
        simp [f] at hn
        exact hn.symm

    simp at inter_zero
    simp [zero_ball] at inter_zero
    use (max 2 n)
    refine ⟨by (grind), ?_⟩
    intro u hu
    rw [Set.ext_iff] at inter_zero
    specialize inter_zero ⟨u, hu⟩
    simp at inter_zero
    intro u_ne_zero
    simp [u_ne_zero] at inter_zero
    simp
    obtain ⟨x, h_x_1, h_x_2⟩ := inter_zero
    use x
    refine ⟨?_, ?_⟩
    . right
      exact h_x_1
    . exact h_x_2
  . intro a b hab
    simp [zero_ball]
    intro u hu hg
    intro g g_dist
    specialize hg g
    grw [hab] at g_dist
    specialize hg g_dist
    exact hg

noncomputable def R'_ (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V] : ℝ := (v_r_all_nonzero V).choose

lemma R'_pos (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V]: 1 < R'_ V := by
  have foo := (v_r_all_nonzero V).choose_spec.1
  exact foo

lemma Q_R_pos_on_R' {V: Submodule ℝ LipschitzH} (v: V) (hv: v ≠ 0) [FiniteDimensional ℝ V] (R: ℝ) (hR: (R'_ V) ≤ R): 0 < Q_R R v v := by
  simp [Q_R]
  rw [Finset.sum_pos_iff_of_nonneg]
  .
    by_contra!
    simp_rw [← pow_two] at this
    simp only [sq_nonpos_iff] at this
    have foo := (v_r_all_nonzero V).choose_spec.2 (v) (by apply Submodule.coe_mem) ?_
    .
      obtain ⟨g, g_mem, x_g_nonzero⟩ := foo
      specialize this g ?_
      .
        simp
        unfold R'_ at hR
        grw [hR] at g_mem
        simpa using g_mem
      .
        simp at x_g_nonzero
        contradiction
    .
      conv =>
        rhs
        equals (0: V) =>
          simp

      rw [ne_eq, ← Subtype.ext_iff]
      rw [← ne_eq]
      exact hv
  . intro y hy
    rw [← pow_two]
    positivity

lemma Q_R_matrix_pos_def {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} [FiniteDimensional ℝ V] (b : Module.Basis ι ℝ ↥V) (R: ℝ) (hR: (R'_ V) ≤ R): (Q_R_matrix b R).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Q_R_lin_hermetian b _)
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
  . exact hR

#print sorries Q_R_matrix_pos_def

-- TODO - generalize and upstream

section V_variable

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

instance nonempty_basis: Nonempty ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V) := Module.Basis.index_nonempty (Module.Basis.ofVectorSpace _ _)

-- TODO - generalize and upstream
omit hGS in
lemma euclidean_of_lp_le {ι : Type*} [Fintype ι] (x: EuclideanSpace ℝ ι) (i: ι):
    |x.ofLp i| ≤ ‖x‖ := by

  rw [EuclideanSpace.norm_eq]
  rw [Real.le_sqrt]
  .
    simp
    apply Finset.single_le_sum (a := i)
    . intro i _
      positivity
    . simp
  . simp
  . positivity

/-- The Lipschitz constant `‖(b i).val‖` of the `i`-th vector of the basis `b` of `V`. -/
noncomputable def v_lipschitz_constant {ι : Type*} (b : Module.Basis ι ℝ ↥V) (i : ι) : ℝ :=
  ‖(b i).val‖

/-- The value at the origin `‖(b i).val 1‖` of the `i`-th vector of the basis `b` of `V`. -/
noncomputable def v_origin_norm {ι : Type*} (b : Module.Basis ι ℝ ↥V) (i : ι) : ℝ :=
  ‖(b i).val 1‖

/-- The maximum, over vectors of the basis `b`, of the Lipschitz constant `v_lipschitz_constant`. -/
noncomputable def max_lipschitz {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  v_lipschitz_constant b (Finite.exists_max (v_lipschitz_constant b)).choose

/-- The maximum, over vectors of the basis `b`, of the value at the origin `v_origin_norm`. -/
noncomputable def max_origin {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  v_origin_norm b (Finite.exists_max (v_origin_norm b)).choose

omit V_finite [Nontrivial ↥V] in
lemma le_max_lipschitz {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (i) : v_lipschitz_constant b i ≤ max_lipschitz b :=
  (Finite.exists_max (v_lipschitz_constant b)).choose_spec i

omit V_finite [Nontrivial ↥V] in
lemma le_max_origin {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (i) : v_origin_norm b i ≤ max_origin b :=
  (Finite.exists_max (v_origin_norm b)).choose_spec i

omit V_finite [Nontrivial ↥V] in
lemma max_lipschitz_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ max_lipschitz b := by
  unfold max_lipschitz v_lipschitz_constant; positivity

omit V_finite [Nontrivial ↥V] in
lemma max_origin_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ max_origin b := by
  unfold max_origin v_origin_norm; positivity

/-- The `R`-independent constant appearing in `det_bound` (the `(1 + R) ^ 2` factor is kept
separate, in the statement of `det_bound`). -/
noncomputable def det_bound_const {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  ((Module.finrank ℝ ↥V) * max_lipschitz b + (Module.finrank ℝ ↥V) * max_origin b) ^ 2

omit V_finite [Nontrivial ↥V] in
lemma det_bound_const_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ det_bound_const b := by
  simp [det_bound_const]
  positivity

lemma det_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (R: ℕ) (hR: (R'_ V) ≤ R):
    ((Q_R_matrix b R).det ^ ((1: ℝ) / Module.finrank ℝ V))
      ≤ det_bound_const b * (1 + R) ^ 2 * #(S ^ R) := by
  classical
  let argmax_eigen := (Finite.exists_max (Q_R_lin_hermetian b R).eigenvalues).choose
  let m :=  (Q_R_lin_hermetian b R).eigenvalues (argmax_eigen)
  let m_vec := (Q_R_lin_hermetian b R).eigenvectorBasis argmax_eigen
  let m_vec_V := b.equivFun.symm (m_vec.ofLp)

  let v_lipschitz_constant := v_lipschitz_constant b
  let v_origin_norm := v_origin_norm b
  let max_lipschitz := max_lipschitz b
  let max_origin := max_origin b
  have h_max_lipschitz : ∀ i, v_lipschitz_constant i ≤ max_lipschitz := le_max_lipschitz b
  have h_max_origin : ∀ i, v_origin_norm i ≤ max_origin := le_max_origin b
  obtain hB := iterated_lipschitz_bound m_vec_V.val

  rw [show det_bound_const b * (1 + R) ^ 2
        = (((Module.finrank ℝ ↥V) * max_lipschitz
            + (Module.finrank ℝ ↥V) * max_origin) * (1 + R)) ^ 2 from by
      simp only [max_lipschitz, max_origin, det_bound_const]; ring]
  rw [(Q_R_lin_hermetian b R).det_eq_prod_eigenvalues]
  grw [Finset.prod_le_prod (g := fun _ => m)]
  .
    simp
    rw [← Module.finrank_eq_card_basis b]
    rw [←  Real.rpow_natCast]
    rw [← Real.rpow_mul]
    .
      have finrank_pos := Module.finrank_pos (R := ℝ) (M := V)
      field_simp [finrank_pos]
      simp
      unfold m
      rw [Matrix.IsHermitian.eigenvalues_eq]
      simp [Q_R_matrix]
      have foo := dotProduct_toMatrix₂_mulVec b b (Q_R_lin V R)
      conv at foo =>
        intro x y
        lhs
        lhs
        equals x =>
          ext a
          simp
      conv at foo =>
        intro x y
        lhs
        rhs
        rhs
        equals y =>
          ext a
          simp
      rw [foo]
      simp only [Q_R_lin, Q_R, LipschitzH_apply,  map_sum,
        map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_sum, LinearMap.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le]
      simp_rw [← pow_two]
      grw [Finset.sum_le_card_nsmul (n := (((((Module.finrank ℝ ↥V)) * max_lipschitz + ((Module.finrank ℝ ↥V) * max_origin)) * (1 + R)) ^ 2))]
      .
        rw [← card_closed_ball_eq]
        simp
        rw [mul_comm]
        field_simp
        simp
      .
        intro x hx
        specialize hB x
        simp
        simp at hB
        rw [← Real.sqrt_sq_eq_abs] at hB
        rw [Real.sqrt_le_iff] at hB
        have foo := hB.2
        .
          simp [dist, WordDist_one] at hx
          grw [hx] at foo
          conv =>
            lhs
            arg 1
            arg 1
            arg 2
            intro x
            arg 1
            arg 1
            arg 1
            equals (Q_R_lin_hermetian b ↑R).eigenvectorBasis =>
              rfl
          conv at foo =>
            lhs
            simp [m_vec_V, m_vec]
          grw [foo]
          rw [mul_pow, mul_pow]
          rw [mul_le_mul_iff_left₀]
          .
            rw [pow_le_pow_iff_left₀]
            . apply add_le_add
              .
                simp [max_lipschitz]
                have foo := (m_vec_V).val.lipschitz.choose_spec
                conv at foo =>
                  arg 2
                  simp [m_vec_V]

                conv =>
                  lhs
                  equals ‖m_vec_V.val‖₊ =>
                    rfl
                simp [m_vec_V]
                --grw [norm_sum_l]
                grw [norm_sum_le]
                grw [Finset.sum_le_card_nsmul (n := ↑max_lipschitz)]
                .
                  simp
                  rw [← Module.finrank_eq_card_basis b]
                .
                  intro i _
                  simp [norm_smul]
                  grw [euclidean_of_lp_le]
                  simp [m_vec]
                  apply h_max_lipschitz
              .
                simp [m_vec_V, m_vec]
                rw [← LipschitzH_apply]
                rw [LipschitzH.finset_sum_apply]
                grw [Finset.abs_sum_le_sum_abs]
                grw [Finset.sum_le_card_nsmul (n := max_origin)]
                . simp
                  rw [← Module.finrank_eq_card_basis b]
                .
                  intro i hi
                  simp
                  grw [euclidean_of_lp_le]
                  simp
                  apply h_max_origin
            . positivity
            . exact add_nonneg (mul_nonneg (by positivity) (max_lipschitz_nonneg b))
                (mul_nonneg (by positivity) (max_origin_nonneg b))
            . simp
          . positivity

    . unfold m
      apply Matrix.PosSemidef.eigenvalues_nonneg
      apply (Q_R_matrix_pos_def b R hR).posSemidef
  .
    apply Finset.prod_nonneg
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def b R hR).posSemidef
  .
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def b R hR).posSemidef
  . intro i _
    unfold m
    have foo := (Finite.exists_max (Q_R_lin_hermetian b R).eigenvalues).choose_spec
    apply foo i

#print axioms det_bound
end V_variable

end GeneratesNS
