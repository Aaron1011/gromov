import Mathlib
import Mathlib.Algebra.Group.Gromov.Defs
import Mathlib.Algebra.Group.Gromov.LipschitzNorm
import Mathlib.Algebra.Group.Gromov.TendstoTactic
import Mathlib.Algebra.Group.Gromov.TendstoNhdsMul

set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false

open scoped Finset
open scoped Pointwise



-- TODO - generalize and upstream
-- Based on https://math.stackexchange.com/questions/1101184/show-that-if-x-succeq-y-then-detx-ge-dety
lemma matrix_psd_det_one {n: Type*} [Fintype n] [DecidableEq n] (A: Matrix n n ℝ) (ha: A.PosSemidef): 1 ≤ (A + 1).det := by
  have foo := ha.isHermitian.spectral_theorem
  have H := ha.isHermitian
  simp at foo
  rw [foo]
  conv =>
    rhs
    arg 1
    equals H.eigenvectorUnitary * ((Matrix.diagonal H.eigenvalues) + 1) * (star H.eigenvectorUnitary) =>
      rw [mul_add, add_mul]
      simp

  rw [Matrix.det_conj_of_mul_eq_one]
  .
    rw [← Matrix.diagonal_one']
    rw [Matrix.diagonal_add]
    simp
    apply Finset.one_le_prod
    intro i _
    have foo := ha.eigenvalues_nonneg
    grind
  . simp
  . simp


open MatrixOrder in
lemma matrix_det_montone {n: Type*} [Fintype n] [DecidableEq n] (A B: Matrix n n ℝ) (hb: B.PosDef) (hab: (A - B).PosSemidef): B.det ≤ A.det := by

  have invert_sqrt: Invertible (CFC.sqrt B) := by
    apply Matrix.invertibleOfIsUnitDet
    rw [Matrix.PosSemidef.det_sqrt hb.posSemidef]
    simp
    rw [← ne_eq, Real.sqrt_ne_zero]
    . grind [hb.det_pos]
    . grind [hb.det_pos]


  have det_prod_eq: A.det = B.det * ((CFC.sqrt B)⁻¹ * (A - B) * (CFC.sqrt B)⁻¹ + 1).det := by
    conv =>
      lhs
      arg 1
      equals (CFC.sqrt B) * (CFC.sqrt B)⁻¹ * A * (CFC.sqrt B)⁻¹ * (CFC.sqrt B) =>
        simp


    rw [mul_assoc, mul_assoc, mul_assoc]
    rw [Matrix.det_mul]
    rw [← mul_assoc, ← mul_assoc]
    rw [Matrix.det_mul]
    ring
    rw [hb.posSemidef.det_sqrt]
    simp only [RCLike.sqrt_real]
    rw [Real.sq_sqrt (by grind [hb.det_pos])]
    rw [mul_sub]
    rw [sub_mul]
    conv =>
      rhs
      rhs
      rhs
      lhs
      rhs
      arg 1
      arg 2
      rw [← CFC.sqrt_mul_sqrt_self (a := B)]

    simp

  rw [det_prod_eq]
  rw [le_mul_iff_one_le_right]
  .
    apply matrix_psd_det_one
    rw [hb.posSemidef.inv_sqrt]
    have foo := (CFC.sqrt_nonneg B⁻¹)
    rw [Matrix.le_iff] at foo
    simp at foo
    nth_rw 2 [← foo.isHermitian.eq]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact hab
  . apply hb.det_pos


namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS


noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)
noncomputable def Q_R_lin (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R (fun g => u.val g) (fun g => v.val g)
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
noncomputable def Q_R_matrix (V: Submodule ℝ LipschitzH) (R: ℝ) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)] := ((Q_R_lin V R).toMatrix₂ (V_basis V) (V_basis V))
noncomputable def my_expr (V: Submodule ℝ LipschitzH) (d: ℝ) (R : ℕ) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)] := #(S ^ R) * ((Q_R_matrix V R).det ^ ((1 : ℝ) / Module.finrank ℝ V)) / (R ^ d)
-- This is a liminf < ∞ in Vikman, but we can actually prove that it goes to 0, which makes things much easier to work with
noncomputable def growth_bound (V: Submodule ℝ LipschitzH) (d: ℝ) [finite_V : FiniteDimensional ℝ V] [decidable_V : DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]  := Filter.Tendsto (fun (R: ℕ) => my_expr V d R) (Filter.atTop) ((𝓝[>] 0))

lemma Q_R_lin_symm (V: Submodule ℝ LipschitzH) (R: ℝ): (Q_R_lin V R).IsSymm := {
  eq := by
    intro u v
    simp [Q_R_lin, Q_R]
    simp_rw [mul_comm]
}

lemma Q_R_lin_hermetian (V: Submodule ℝ LipschitzH) (R: ℝ) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]: (Q_R_matrix V R).IsHermitian := by
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

lemma v_r_all_nonzero (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V]: ∃ R: ℝ, ∀ u ∈ V, u ≠ 0 → ∃ g ∈ Metric.closedBall 1 R, u g ≠ 0 := by
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
    use n
    intro u hu
    rw [Set.ext_iff] at inter_zero
    specialize inter_zero ⟨u, hu⟩
    simp at inter_zero
    intro u_ne_zero
    simp [u_ne_zero] at inter_zero
    simp
    exact inter_zero
  . intro a b hab
    simp [zero_ball]
    intro u hu hg
    intro g g_dist
    specialize hg g
    grw [hab] at g_dist
    specialize hg g_dist
    exact hg



noncomputable def R'_ (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V] : ℝ := (v_r_all_nonzero V).choose


lemma Q_R_matrix_pos_def (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)] (R: ℝ) (hR: (R'_ V) ≤ R): (Q_R_matrix V R).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Q_R_lin_hermetian V _)
  intro x hx
  simp [Q_R_matrix]
  conv =>
    rhs
    lhs
    equals (star x) => simp
  rw [star_dotProduct_toMatrix₂_mulVec]
  simp only [Q_R_lin, Q_R, DFunLike.coe]
  rw [Finset.sum_pos_iff_of_nonneg]
  .
    by_contra!
    simp_rw [← pow_two] at this
    simp only [sq_nonpos_iff] at this

    have foo := (v_r_all_nonzero V).choose_spec ((V_basis V).equivFun.symm x) (by apply Submodule.coe_mem) ?_
    .
      obtain ⟨g, g_mem, x_g_nonzero⟩ := foo
      specialize this g ?_
      .
        simp
        unfold R'_ at hR
        grw [hR] at g_mem
        simpa using g_mem
      . simp at this
        simp at x_g_nonzero
        contradiction
    .
      conv =>
        rhs
        equals (0: V) =>
          simp

      rw [ne_eq, ← Subtype.ext_iff]
      rw [← ne_eq]
      rw [LinearEquiv.map_ne_zero_iff]
      exact hx
  . intro y hy
    rw [← pow_two]
    positivity

#print sorries Q_R_matrix_pos_def

-- TODO - generalize and upstream
theorem LipschitzWith.sum {ι : Type*} {α : Type*} {E : Type*}
    [PseudoEMetricSpace α] [SeminormedAddCommGroup E]
    {s : Finset ι} {f : ι → α → E} {K : ι → NNReal}
    (hf : ∀ i ∈ s, LipschitzWith (K i) (f i)) :
    LipschitzWith (∑ i ∈ s, K i) (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using LipschitzWith.const (α := α) (0 : E)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))



section V_variable

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V] (hV : Even (Module.finrank V))  [V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]

instance nonempty_basis: Nonempty ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V) := Module.Basis.index_nonempty (Module.Basis.ofVectorSpace _ _)

-- TODO - generalize and upstream
lemma euclidean_of_lp_le (x: EuclideanSpace ℝ ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)) (i: ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)):
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


/-- The Lipschitz constant `‖(V_basis i).val‖` of the `i`-th basis vector of `V`. -/
noncomputable def v_lipschitz_constant (i : ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)) : ℝ :=
  ‖(V_basis (V := V) i).val‖

/-- The value at the origin `‖(V_basis i).val 1‖` of the `i`-th basis vector of `V`. -/
noncomputable def v_origin_norm (i : ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)) : ℝ :=
  ‖(V_basis (V := V) i).val 1‖

/-- The maximum, over basis vectors of `V`, of the Lipschitz constant `v_lipschitz_constant`. -/
noncomputable def max_lipschitz : ℝ :=
  v_lipschitz_constant (Finite.exists_max (v_lipschitz_constant (V := V))).choose

/-- The maximum, over basis vectors of `V`, of the value at the origin `v_origin_norm`. -/
noncomputable def max_origin : ℝ :=
  v_origin_norm (Finite.exists_max (v_origin_norm (V := V))).choose

lemma le_max_lipschitz (i) : v_lipschitz_constant (V := V) i ≤ max_lipschitz (V := V) :=
  (Finite.exists_max (v_lipschitz_constant (V := V))).choose_spec i

lemma le_max_origin (i) : v_origin_norm (V := V) i ≤ max_origin (V := V) :=
  (Finite.exists_max (v_origin_norm (V := V))).choose_spec i

lemma max_lipschitz_nonneg : 0 ≤ max_lipschitz (V := V) := by
  unfold max_lipschitz v_lipschitz_constant; positivity

lemma max_origin_nonneg : 0 ≤ max_origin (V := V) := by
  unfold max_origin v_origin_norm; positivity

/-- The `R`-independent constant appearing in `det_bound` (the `(1 + R) ^ 2` factor is kept
separate, in the statement of `det_bound`). -/
noncomputable def det_bound_const : ℝ :=
  ((Module.finrank ℝ ↥V) * max_lipschitz (V := V) + (Module.finrank ℝ ↥V) * max_origin (V := V)) ^ 2

lemma det_bound_const_nonneg: 0 ≤ det_bound_const (V := V) := by
  simp [det_bound_const]
  positivity

lemma det_bound (R: ℕ) (hR: (R'_ V) ≤ R):
    ((Q_R_matrix R (V := V)).det ^ ((1: ℝ) / Module.finrank ℝ V))
      ≤ det_bound_const (V := V) * (1 + R) ^ 2 * #(S ^ R) := by
  classical
  let argmax_eigen := (Finite.exists_max (Q_R_lin_hermetian R (V := V)).eigenvalues).choose
  let m :=  (Q_R_lin_hermetian R (V := V)).eigenvalues (argmax_eigen)
  let m_vec := (Q_R_lin_hermetian R (V := V)).eigenvectorBasis argmax_eigen
  let m_vec_V := V_basis (V := V).equivFun.symm (m_vec.ofLp)

  let v_lipschitz_constant := v_lipschitz_constant (V := V)
  let v_origin_norm := v_origin_norm (V := V)
  let max_lipschitz := max_lipschitz (V := V)
  let max_origin := max_origin (V := V)
  have h_max_lipschitz : ∀ i, v_lipschitz_constant i ≤ max_lipschitz := le_max_lipschitz (V := V)
  have h_max_origin : ∀ i, v_origin_norm i ≤ max_origin := le_max_origin (V := V)
  obtain hB := iterated_lipschitz_bound m_vec_V.val

  -- have B_nonneg: 0 ≤ B := by
  --   specialize hB 1
  --   simp at hB
  --   have foo := abs_nonneg ((m_vec_V).val.toFun 1)
  --   grw [hB] at foo
  --   apply nonneg_of_mul_nonneg_left foo (by grind)
  rw [show det_bound_const (V := V) * (1 + R) ^ 2
        = (((Module.finrank ℝ ↥V) * max_lipschitz
            + (Module.finrank ℝ ↥V) * max_origin) * (1 + R)) ^ 2 from by
      simp only [max_lipschitz, max_origin, det_bound_const]; ring]
  rw [(Q_R_lin_hermetian R (V := V)).det_eq_prod_eigenvalues]
  grw [Finset.prod_le_prod (g := fun _ => m)]
  .
    simp
    rw [← Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℝ V)]
    rw [←  Real.rpow_natCast]
    rw [← Real.rpow_mul]
    .
      have finrank_pos := Module.finrank_pos (R := ℝ) (M := V)
      field_simp [finrank_pos]
      simp
      unfold m
      rw [Matrix.IsHermitian.eigenvalues_eq]
      simp [Q_R_matrix]
      have foo := dotProduct_toMatrix₂_mulVec (V_basis (V := V)) (V_basis (V := V)) (Q_R_lin R (V := V))
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
          simp at foo
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
            equals (Q_R_lin_hermetian V ↑R).eigenvectorBasis =>
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
                  rw [← Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℝ V)]
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
                  rw [← Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℝ V)]
                .
                  intro i hi
                  simp
                  grw [euclidean_of_lp_le]
                  simp
                  apply h_max_origin
            . positivity
            . exact add_nonneg (mul_nonneg (by positivity) (max_lipschitz_nonneg (V := V)))
                (mul_nonneg (by positivity) (max_origin_nonneg (V := V)))
            . simp
          . positivity

    . unfold m
      apply Matrix.PosSemidef.eigenvalues_nonneg
      apply (Q_R_matrix_pos_def V R hR).posSemidef
  .
    apply Finset.prod_nonneg
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def V R hR).posSemidef
  .
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def V R hR).posSemidef
  . intro i _
    unfold m
    have foo := (Finite.exists_max (Q_R_lin_hermetian V R).eigenvalues).choose_spec
    apply foo i

#print axioms det_bound
end V_variable

-- Everything in this section freely references fields from V_Wrapper
section V_Wrapper_Section

class V_Wrapper where
  V: Submodule ℝ LipschitzH
  V_finite: FiniteDimensional ℝ V
  V_nontrivial: Nontrivial V
  V_even: Even (Module.finrank ℝ V)
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ V)

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

local instance v_finite_dim_inst: FiniteDimensional ℝ V := v_wrapper_inst.V_finite
local instance v_nontrivial_inst: Nontrivial V := v_wrapper_inst.V_nontrivial
local instance V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ V) := v_wrapper_inst.V_decidable

private noncomputable def R' := R'_ V


-- Todo - is the better way to declare theorem_3_23 so that the constant is not allowed to depend on V?
-- TODO - can this somehow be merged with V_wrapper?
structure V_Data where
  V: Submodule ℝ LipschitzH
  hV: FiniteDimensional ℝ V
  (V_even : Even (Module.finrank ℝ V))
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)


noncomputable def Q_R_single (R : ℝ) (u: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g)^2

lemma Q_R_single_eq (R: ℝ) (u : G → ℝ): Q_R_single R u = Q_R R u u := by
  unfold Q_R_single Q_R
  simp_rw [pow_two]





-- Finding good scales:

private noncomputable def dim (V: Type*) [AddCommMonoid V] [Module ℝ V] : ℝ := Module.finrank ℝ V

private noncomputable def i₀ : ℕ := Nat.clog 16 ⌈R'⌉₊

lemma Q_R_matrix_pos_def_i₀ (R: ℝ) (hR: 16 ^ (i₀) ≤ R): (Q_R_matrix V R).PosDef := by
  apply Q_R_matrix_pos_def
  simp [i₀] at hR
  have foo := Nat.le_pow_clog (b := 16) (x := ⌈R'_ V⌉₊) (by simp)
  have r_ceil := Nat.le_ceil (R')
  unfold R' at r_ceil
  grw [r_ceil]
  grw [foo]
  simp
  unfold R' at hR
  grw [hR]

private noncomputable def f (R: ℕ): ℝ := #(S ^ R) * (Q_R_matrix V R).det ^ (dim V)⁻¹
private noncomputable def h (i: ℕ): ℝ := Real.log (f (16 ^ i))

-- Matrix.le_iff


lemma f_monotone_on: MonotoneOn f (Set.Ici ⌈R'⌉₊) := by
  intro a ha b hb hab
  unfold f
  grw [Finset.pow_subset_pow_right (n := b)]
  .
    rw [mul_le_mul_iff_right₀]
    .
      rw [Real.rpow_le_rpow_iff]
      .
        apply matrix_det_montone
        .
          apply Q_R_matrix_pos_def V a (by simp [R'] at ha; exact ha)
        .
          unfold Q_R_matrix
          rw [← map_sub]
          rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
          apply Q_R_lin_sub_pos_semi_def
          simpa using hab
      .
        have foo := Q_R_matrix_pos_def V a (by simp [R'] at ha; exact ha)
        grind [foo.det_pos]
      .
        have foo := Q_R_matrix_pos_def V b (by simp [R'] at hb; exact hb)
        grind [foo.det_pos]
      . simp [dim]
        exact Module.finrank_pos
    .
      simp
      apply Finset.Nonempty.pow
      apply S_nonempty

  . apply Real.rpow_nonneg
    have foo := Q_R_matrix_pos_def V a (by simp [R'] at ha; exact ha)
    grind [foo.det_pos]
  . apply hGS.one_mem
  . exact hab

lemma h_montone_on: MonotoneOn h (Set.Ici i₀) := by
  unfold h
  rw [← Function.comp_def]
  apply MonotoneOn.comp
  . apply Real.strictMonoOn_log.monotoneOn
  .
    rw [← Function.comp_def]
    apply MonotoneOn.comp
    . apply f_monotone_on
    .
      conv =>
        arg 1
        equals fun n => 16 ^ n =>
          simp
      apply (pow_right_monotone (by simp)).monotoneOn
    . intro a ha
      simp [i₀] at ha
      simp
      rw [Nat.clog_le_iff_le_pow] at ha
      .
        rify at ha
        grw [Nat.le_ceil (a := R')]
        exact ha
      . simp
  .
    intro a ha
    simp
    simp at ha
    simp [f]
    apply mul_pos
    . simp
      apply Finset.Nonempty.pow
      apply S_nonempty
    .
      apply Real.rpow_pos_of_pos
      apply (Q_R_matrix_pos_def_i₀ _ ?_).det_pos
      rw [pow_le_pow_iff_right₀]
      . exact ha
      . simp



lemma growth_implies_lim_h (d: ℕ) (h_growth: growth_bound V d): Filter.Tendsto (fun (i: ℕ) => (h i - d * i * Real.log 16)) Filter.atTop Filter.atBot := by
  unfold growth_bound my_expr at h_growth
  have pow_tendsto: Filter.Tendsto (fun n => 16 ^ n) Filter.atTop Filter.atTop := by
    apply StrictMono.tendsto_atTop
    apply pow_right_strictMono₀
    simp

  have log_tendsto := Real.tendsto_log_nhdsGT_zero
  -- Real.tendsto_log_nhdsNE_zero
  have comp_pow := Filter.Tendsto.comp h_growth pow_tendsto
  have comp_log := log_tendsto.comp comp_pow
  simp [Function.comp_def] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀] at comp_log
  conv at comp_log =>
    arg 1
    intro x
    rw [Real.log_div (by
      rw [mul_ne_zero_iff]
      refine ⟨?_, ?_⟩
      . simp
        grind [S_nonempty]
      .
        have det_pos := (Q_R_matrix_pos_def_i₀ (16 ^ (x + i₀)) (by
          rw [add_comm]
          rw [pow_add]
          simp
          norm_cast
          apply Nat.one_le_pow
          simp
        )).det_pos

        rw [Real.rpow_ne_zero]
        . grind
        . grind
        .
          norm_cast
          rw [inv_eq_zero]
          norm_cast
          rw [← ne_eq, Nat.ne_zero_iff_zero_lt]
          apply Module.finrank_pos
    ) (by simp)]
    simp
  simp [h, f, dim]
  simp_rw [← mul_assoc] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀]
  simp
  exact comp_log

#print axioms growth_implies_lim_h

noncomputable def a (d: ℕ) := 4 * d * Real.log 16


lemma exists_j_0_for_h (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound V d): ∃ j_0: ℕ, h (i₀ + 3 * w * (j_0 + 1)) - h (i₀ + 3 * w * j_0) < w * (a d) := by
  by_contra!

  have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h (i₀ + 3 * w * n)) (m := 0) (n := N) (by simp)
  simp_rw [eq_comm, sub_eq_iff_eq_add] at h_sum

  have h_gt (N: ℕ): h (i₀ + (3 * w * N)) ≥ 4 * d * w * N * (Real.log 16) + h i₀ := by
    rw [h_sum]
    grw [← Finset.card_nsmul_le_sum (n := w * (a d))]
    .
      simp
      simp [a]
      grind
    . intro n hn
      apply this

  have h_diff_ge (N: ℕ): h (i₀ + (3 * w * N)) - d * (i₀ + 3 * w * N) * Real.log 16 ≥ d * (w * N - i₀) * (Real.log 16) + h i₀ := by
    grw [h_gt]
    simp
    grind

  have rhs_diverges: Filter.Tendsto (fun N => d * (w * N - i₀) * (Real.log 16) + h i₀) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    rw [Filter.tendsto_mul_const_atTop_of_pos (by positivity)]
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    simp_rw [sub_eq_add_neg]
    apply Filter.tendsto_atTop_add_const_right
    conv =>
      arg 1
      equals fun x => w * x =>
        simp
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    apply Filter.tendsto_id

  apply growth_implies_lim_h at h_growth
  rw [Filter.tendsto_atTop_atBot] at h_growth
  rw [Filter.tendsto_atTop_atTop] at rhs_diverges

  obtain ⟨positive_start, h_positive_start⟩ := rhs_diverges 1
  obtain ⟨negative_start, h_negative_start⟩ := h_growth 0

  specialize h_positive_start (max ⌈positive_start⌉₊ negative_start) (by
    apply le_max_of_le_left
    apply Nat.le_ceil
  )
  -- TODO - why can't grind just solve this?
  specialize h_negative_start (i₀ + 3 * w * max ⌈positive_start⌉₊ negative_start) (by
    have le_max: negative_start ≤ max ⌈positive_start⌉₊ negative_start := by
      simp
    conv =>
      lhs
      equals 0 + negative_start => simp
    apply Nat.add_le_add
    . simp
    .
      conv =>
        lhs
        equals 1 * negative_start => simp
      apply Nat.mul_le_mul
      . grind
      . simp
  )

  have h_ge_one := h_diff_ge (max ⌈positive_start⌉₊ negative_start)
  norm_cast at h_ge_one
  norm_cast at h_positive_start
  grw [← h_positive_start] at h_ge_one
  grind




structure Lemma3_24_data (d w: ℕ) where
  i_1 : ℕ
  i_2 : ℕ
  i_1_ge: i₀ ≤ i_1
  i_2_ge: i₀ ≤ i_2
  i_diff_mem: i_2 - i_1 ∈ Set.Ioo w (3 * w)
  h_diff_lt_w: h (i_2 + 1) - h i_1 < w * (a d)
  first_h_i: h (i_1 + 1) - h i_1 < (a d)
  second_h_i : h (i_2 + 1) - h i_2 < (a d)

lemma lemma_3_24 (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound V d): Nonempty (Lemma3_24_data d w) := by
  obtain ⟨j_0, h_j_0⟩ := exists_j_0_for_h w d hw hd h_growth
  let m := i₀ + 3 * w * j_0

  have exists_i1: ∃ i_1: ℕ, i_1 ∈ Set.Ico m (m + w) ∧ h (i_1 + 1) - h i_1 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h (m + n)) (m := 0) (n := w) (by simp)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h (m + w) - h (m) ≤ h (i₀ + 3 * w * (j_0 + 1)) - h (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on
        . simp [m]
        . simp [m]
        . simp [m]


    have h_le_w_a_d : h (m  + w) - h m ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h (m + w) - h m := by
      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
      . intro x hx
        apply this
        simpa using hx
    grind

  -- TODO - can this be deduplicated with exists_i1 ?
  have exists_i2: ∃ i_2: ℕ, i_2 ∈ Set.Ico (m + 2*w) (m + 3 * w) ∧ h (i_2 + 1) - h i_2 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h (m + n)) (m := (2 * w)) (n := (3 * w)) (by grind)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h (m + 3 * w) - h (m + 2 * w) ≤ h (i₀ + 3 * w * (j_0 + 1)) - h (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on
        . simp [m]
        . simp [m]
          grind
        . simp [m]


    have h_le_w_a_d : h (m  + 3 * w) - h (m + 2 * w) ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h (m + 3 * w) - h (m + 2* w) := by

      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
        rw [← Nat.sub_mul]
        simp
      . intro x hx
        apply this
        simp
        simp at hx
        exact hx
    grind

  obtain ⟨i_1, h_i_1⟩ := exists_i1
  obtain ⟨i_2, h_i_2⟩ := exists_i2
  have diff_i_lt: h (i_2 + 1) - h i_1 < w * (a d) := by
    grw [h_montone_on _ _ (b := i₀ + 3 * w * (j_0 + 1))]
    .
      apply LE.le.trans_lt ?_ h_j_0
      apply sub_le_sub_left
      apply h_montone_on
      . simp
      . simp
        grind
      . grind
    . simp at h_i_2
      grind
    . simp
      simp at h_i_2
      grind
    . simp [m]

  apply Nonempty.intro
  exact {
    i_1 := i_1
    i_2 := i_2
    i_1_ge := by grind
    i_2_ge := by grind
    i_diff_mem := by grind
    h_diff_lt_w := diff_i_lt
    first_h_i := h_i_1.2
    second_h_i := h_i_2.2
  }

-- Controlled cover

structure GoodScalesData where
  w: ℕ
  d: ℕ
  hw: 0 < w
  hd: 0 < d
  h_growth: growth_bound V d

noncomputable def GoodScales (data: GoodScalesData) := Classical.choice (lemma_3_24 data.w data.d data.hw data.hd data.h_growth)

noncomputable def R_1 (data: GoodScalesData) := 2 * 16^(GoodScales data).i_1
noncomputable def R_2 (data: GoodScalesData) := 16^(GoodScales data).i_2

-- TODO - does it matter than 'Metric.maximalSeparatedSet' uses 'R_1 < dist' instead of 'R_1 <= dist' ?
def X_j (data: GoodScalesData) := Metric.maximalSeparatedSet (R_1 data) ((Metric.ball (1: G) (R_2 data)))
-- A collection of disjoint balls that cover the ball R_2
def B (data: GoodScalesData) := (fun a => Metric.closedBall a (R_1 data)) '' (X_j data)
def B_half (data: GoodScalesData) := (fun a => Metric.closedBall a (R_1 data / 2)) '' (X_j data)
def B_3 (data: GoodScalesData) := (fun a => Metric.closedBall a (3 * R_1 data)) '' (X_j data)

lemma B_half_injective_on (data: GoodScalesData): Set.InjOn (fun a => Metric.closedBall a (R_1 data / 2)) (X_j data) := by
  intro a ha b hb hab
  by_contra!
  simp at hab
  simp [X_j] at ha hb

  have sep := Metric.isSeparated_maximalSeparatedSet (ε := (R_1 data)) (A := (Metric.ball (1 : G) ↑(R_2 data)))
  specialize sep ha hb this

  have b_mem: b ∈ Metric.closedBall a ((R_1 data / 2)) := by
    rw [hab]
    simp
    grind

  simp at b_mem
  simp [edist, PseudoMetricSpace.edist] at sep
  rw [dist_comm] at b_mem
  simp [dist] at b_mem
  norm_cast at b_mem
  rify at sep
  grw [b_mem] at sep
  grind

lemma B_covers_R2 (data: GoodScalesData): Metric.ball 1 (R_2 data) ⊆ ⋃₀ (B data) := by
  by_contra!
  rw [Set.not_subset] at this
  obtain ⟨x, x_mem, x_not_mem⟩ := this

  -- Metric.maximalSeparatedSet_subset
  have card_le := Metric.encard_le_of_isSeparated (C := (X_j data) ∪ {x}) (ε := (R_1 data)) (A := ( (Metric.ball 1 (R_2 data)))) ?_ ?_ ?_
  .
    simp [X_j] at card_le
    rw [Set.encard_insert_of_notMem] at card_le
    rw [Set.Finite.encard_eq_coe_toFinset_card] at card_le
    . norm_cast at card_le
      grind
    .
      apply Set.Finite.subset (s := Metric.ball 1 (R_2 data))
      . apply finite_ball
      . apply Metric.maximalSeparatedSet_subset
    .
      simp at x_not_mem
      simp only [B, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        not_lt, X_j] at x_not_mem

      by_contra!
      specialize x_not_mem x this
      simp [R_1] at x_not_mem
  .
    apply Set.union_subset
    . simp [X_j]
      grw [Metric.maximalSeparatedSet_subset]
    . simpa using x_mem
  .
    simp
    apply Metric.IsSeparated.insert
    . simp [X_j]
      apply Metric.isSeparated_maximalSeparatedSet
    . intro y hy hxy
      simp [B] at x_not_mem
      specialize x_not_mem y hy
      simp [edist, PseudoMetricSpace.edist]
      simp [dist] at x_not_mem
      exact x_not_mem
  .
    rw [← lt_top_iff_ne_top]
    grw [Metric.packingNumber_le_encard_self]
    simp
    apply finite_ball

lemma B_half_disjoint (data: GoodScalesData): (B_half data).PairwiseDisjoint id := by
  simp [Set.pairwiseDisjoint_iff]
  intro X hX Y hY hXY
  obtain ⟨a, ha⟩ := hXY
  simp [B_half] at hX hY
  obtain ⟨x, x_mem, hx⟩ := hX
  obtain ⟨y, y_mem, hy⟩ := hY

  by_cases x_eq_y : x = y
  .
    rw [x_eq_y] at hx
    rw [← hx, ← hy]


  rw [← hx, ← hy] at ha
  simp at ha
  obtain ⟨a_dist_x, a_dist_y⟩ := ha

  simp [X_j] at x_mem
  have is_sep := Metric.isSeparated_maximalSeparatedSet (ε := ((R_1 data))) (A := Metric.ball (1: G) (R_2 data))

  unfold Metric.IsSeparated Set.Pairwise at is_sep
  have x_sep := is_sep x_mem y_mem x_eq_y
  simp at x_sep


  have x_y_dist_bad := dist_triangle x a y
  rw [dist_comm x a] at x_y_dist_bad
  grw [a_dist_x, a_dist_y] at x_y_dist_bad
  simp at x_y_dist_bad
  -- TODO - we need a lemma that edist = ↑dist
  simp [edist, PseudoMetricSpace.edist] at x_sep
  simp [dist] at x_y_dist_bad
  grind


-- Intersection multiplicity. See https://www.math.ucdavis.edu/~kapovich/EPR/kapovich_drutu.pdf page 24 for the definition
-- (search for 'multiplicity')
noncomputable def InterMult_f  (S: Set (Set G)) := (fun A => (Set.encard A).toNat) '' { A: Set (Set G) | A ⊆ S ∧ ⋂₀ A ≠ ∅ }
noncomputable def InterMult (S: Set (Set G)) := sSup (InterMult_f S)

lemma smul_origin_ball_subset (a: G) (r: ℝ): (MulOpposite.op a) • Metric.closedBall 1 r ⊆ Metric.closedBall a r := by
  intro x hx
  simp
  rw [Set.mem_smul_set] at hx
  obtain ⟨y, hy, x_eq⟩ := hx
  rw [← x_eq]
  simp [dist, WordDist]
  simp at hy
  simp [dist, WordDist] at hy
  exact hy

lemma ball_subset_smul_origin (a: G) (r: ℝ): Metric.closedBall a r ⊆ (MulOpposite.op a) • Metric.closedBall 1 r := by
  intro x hx
  simp at hx
  simpa using hx

lemma ball_smul_eq_origin (a: G) (r: ℝ): Metric.closedBall a r = (MulOpposite.op a) • Metric.closedBall 1 r := by
  ext x
  have foo := smul_origin_ball_subset a r
  have bar := ball_subset_smul_origin a r
  grind

lemma B_finite (data: GoodScalesData): (B data).Finite := by
  simp [B]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_ball

lemma B_3_finite (data: GoodScalesData): (B_3 data).Finite := by
  simp [B_3]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_ball

-- Suprisingly, we can prove an upper bound with 4*R_1, rather than the 8*R_1 from the paper
lemma inter_mult_helper (data: GoodScalesData): InterMult (B_3 data) * #(S ^ ((R_1 data) / 2)) ≤ #(S ^ (4 * (R_1 data))) := by
  classical
  apply Nat.mul_le_of_le_div
  unfold InterMult
  by_cases h_s: InterMult_f (B_3 data) = ∅
  . simp [h_s]
  .
    rw [csSup_le_iff]
    .
      intro n hn
      simp [InterMult_f] at hn
      obtain ⟨X, ⟨X_subset, X_inter⟩, X_card⟩ := hn
      rw [← X_card]
      have X_finite := Set.Finite.subset (B_3_finite data) X_subset
      rw [Set.Finite.encard_eq_coe_toFinset_card X_finite]
      simp
      rw [Nat.le_div_iff_mul_le]
      .
        have X_inner_nonempty: ∀ t ∈ X, ∃ a, a ∈ (X_j data) ∧ Metric.closedBall a (3 * R_1 data) = t := by
          intro t ht
          specialize X_subset ht
          simp [B_3] at X_subset
          exact X_subset

        rw [← closed_ball_eq_S_pow]
        rw [← smul_eq_mul]
        rw [← Finset.sum_const]

        grw [Finset.sum_le_sum (g := fun a => if ha: a ∈ X then #(finite_closed_ball (X_inner_nonempty a ha).choose ((R_1 data) / 2)).toFinset else 0)]
        .
          rw [← closed_ball_eq_S_pow]
          --rw [← Finset.sum_attach]
          rw [Finset.sum_dite]
          rw [← Finset.card_biUnion]
          .
            rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at X_inter
            obtain ⟨base, h_base⟩ := X_inter

            simp only [Finset.sum_const_zero, add_zero]
            nth_rw 2 [← Finset.card_smul_finset (MulOpposite.op base)]
            apply Finset.card_le_card
            rw [← Finset.coe_subset]
            rw [Finset.coe_smul_finset]
            conv =>
              rhs
              arg 2
              simp

            rw [← ball_smul_eq_origin]
            intro a ha
            simp at ha
            simp
            obtain ⟨c, hc, a_dist⟩ := ha
            .
              let q := (X_inner_nonempty c hc).choose
              grw [dist_triangle _ q]
              conv at a_dist =>
                arg 1
                arg 2
                equals q =>
                  simp [q]

              simp
              grw [a_dist]
              simp at h_base
              specialize h_base c hc

              have q_prop := (X_inner_nonempty c hc).choose_spec
              rw [← q_prop.2] at h_base
              simp at h_base
              rw [dist_comm] at h_base
              simp [q]
              grw [h_base]
              grind
          .
            rw [Finset.pairwiseDisjoint_iff]
            intro a _ b _ hab
            rw [Subtype.ext_iff]

            have from_b := B_half_disjoint data
            have a_prop := a.prop
            have b_prop := b.prop
            simp [-SetLike.coe_mem] at a_prop
            simp [-SetLike.coe_mem] at b_prop
            simp [B_half] at from_b

            let a_center := (X_inner_nonempty _ a_prop).choose
            let b_center := (X_inner_nonempty _ b_prop).choose
            obtain ⟨a_center_mem, a_eq⟩ := (X_inner_nonempty _ a_prop).choose_spec
            obtain ⟨b_center_mem, b_eq⟩ := (X_inner_nonempty _ b_prop).choose_spec


            rw [Set.pairwiseDisjoint_iff] at from_b
            simp only [Set.mem_image, id_eq, forall_exists_index, and_imp] at from_b
            simp at hab
            have inter_eq := from_b a_center a_center_mem (i := (Metric.closedBall a_center (↑(R_1 data) / 2) )) (?_) b_center b_center_mem (j := (Metric.closedBall b_center (↑(R_1 data) / 2) )) (?_) ?_
            .

              rw [← a_eq, ← b_eq]
              simp [a_center, b_center] at inter_eq
              apply B_half_injective_on at inter_eq
              .
                simp [inter_eq]
              . grind
              . grind
            . rfl
            . rfl
            . simp [a_center, b_center]
              rw [← Finset.coe_nonempty] at hab
              simp at hab
              exact hab

        . intro y hy
          simp at hy
          simp only [hy, ↓reduceDIte]
          nth_rw 1 [← Finset.card_smul_finset (MulOpposite.op (X_inner_nonempty y hy).choose)]
          apply Finset.card_le_card
          intro a ha
          simp at ha
          simp
          rw [Finset.mem_smul_finset] at ha
          obtain ⟨z, z_mem, z_mul_eq⟩ := ha
          simp at z_mem
          rw [← z_mul_eq]
          simp
          simp [dist, WordDist]
          rw [← word_norm_inv]
          simp [dist, WordDist_one] at z_mem
          norm_cast
          grw [z_mem]
          grw [Nat.cast_div_le]
          simp

      . simp
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    .
      unfold BddAbove
      use (B_3 data).encard.toNat
      rw [mem_upperBounds]
      intro x hx
      simp [InterMult_f] at hx
      obtain ⟨a, b, x_eq⟩ := hx
      rw [← x_eq]
      apply ENat.toNat_le_toNat
      .
        apply Set.encard_le_encard
        grind
      . simp
        apply B_3_finite
    . rw [Set.nonempty_iff_ne_empty]
      grind


lemma log_inter_mult_b3 (data: GoodScalesData): InterMult (B_3 data) ≤ Real.exp (a data.d) := by
  by_cases mult_zero: InterMult (B_3 data) = 0
  . simp [mult_zero]
    positivity

  rw [← Real.log_le_iff_le_exp]
  have foo := inter_mult_helper data
  rw [← Nat.le_div_iff_mul_le] at foo
  grw [foo]
  .
    grw [Nat.cast_div_le]
    .
      rw [Real.log_div]
      .
        have bound := (GoodScales data).first_h_i
        grw [← bound]
        simp [h, f]
        rw [Real.log_mul]
        .
          rw [Real.log_mul]
          .
            ring_nf
            rw [sub_right_comm]
            rw [add_sub_assoc]
            rw [← Real.log_div]
            grw [← Real.log_nonneg (x := _ / _)]
            .
              simp
              rw [← sub_le_iff_le_add]
              apply sub_le_sub
              . apply Real.log_le_log
                . simp
                  apply Finset.Nonempty.pow
                  apply S_nonempty
                . simp
                  apply Finset.card_pow_mono
                  . simp [R_1]
                  .
                    simp [R_1]
                    grind
              . apply Real.log_le_log
                . simp
                  apply Finset.Nonempty.pow
                  simp [S_nonempty]
                . simp [R_1]
            .
              rw [one_le_div₀]
              .
                rw [Real.rpow_le_rpow_iff]
                apply matrix_det_montone
                . apply Q_R_matrix_pos_def_i₀
                  have foo := (GoodScales data).i_1_ge
                  apply pow_le_pow_right₀
                  . simp
                  . exact foo
                . sorry
                .
                  sorry
                . sorry
                . simp [dim]
                  exact Module.finrank_pos
              . sorry
            . sorry
            . sorry
          . simp
            grind [S_nonempty]
          . sorry
        . simp
          grind [S_nonempty]
        . sorry
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    . simp
      refine ⟨?_, ?_⟩
      . apply Finset.Nonempty.pow
        simp [S_nonempty]
      .
        apply Finset.card_pow_mono
        . simp [R_1]
        . grind
  .
    simp
    apply Finset.Nonempty.pow
    simp [S_nonempty]
  . simp
    grind

#print axioms inter_mult_helper

end V_Wrapper_Section

lemma theorem_3_23 (d: ℝ): ∃ C: ℕ, ∀ data: V_Data, (growth_bound data.V d (finite_V := data.hV) (decidable_V := data.V_decidable)) → (Module.finrank ℝ data.V) < C := by
  have C: ℕ := sorry
  use C
  intro data h_growth


  sorry


open scoped Topology

-- TODO - do we really need the double by_contra here?
set_option maxHeartbeats 2500000 in
instance Lipschitz_finite_dimensional: FiniteDimensional ℝ LipschitzH := by
  classical
  by_contra!
  have B := Module.Basis.ofVectorSpace ℝ LipschitzH

  have B_infinite: Infinite ((Module.Basis.ofVectorSpaceIndex ℝ LipschitzH)) := by
    by_contra fin_basis
    simp at fin_basis
    have finite_module := Module.Finite.of_basis B
    have finite_dim: FiniteDimensional ℝ LipschitzH := by
      infer_instance
    contradiction


  obtain ⟨d, hd⟩ := hGS.g_growth
  obtain ⟨C, V_bound⟩ := theorem_3_23 ((d + 3) + (d + 3))

  obtain ⟨fin_basis_idx, card_fin_basis_idx⟩ := B_infinite.exists_subset_card_eq _ (2 + C * 2)
  let fin_basis := Finset.image (B) fin_basis_idx
  let large_v: V_Data := {
    V := Submodule.span ℝ fin_basis
    hV := by infer_instance
    V_even := by
      rw [finrank_span_finset_eq_card]
      .
        simp [fin_basis]
        rw [Finset.card_image_of_injective]
        . grind
        .

          exact Module.Basis.injective B
      .
        simp [fin_basis]
        apply LinearIndepOn.id_image
        exact Module.Basis.linearIndepOn B ↑fin_basis_idx
    V_decidable := by
      infer_instance
  }
  specialize V_bound large_v ?_
  .
    simp [growth_bound, my_expr]
    -- have ne_top_of_zero (a: ENNReal) (ha: a ≤ 0): a ≠ ⊤ := by
    --   simp at ha
    --   simp [ha]
    -- apply ne_top_of_zero
    -- simp
    -- apply Filter.Tendsto.liminf_eq
    -- conv =>
    --   pattern nhds 0
    --   equals nhds ((ENNReal.ofReal (0 * 0))) =>
    --     simp

    -- apply ENNReal.tendsto_ofReal
    norm_cast
    conv =>
      arg 1
      intro a
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [Nat.pow_add]
    push_cast
    conv =>
      arg 1
      intro a
      rw [div_mul_eq_div_mul_one_div]
      rw [mul_comm _ (1 / _)]
      rw [← mul_assoc]

    have nontrivial_v : Nontrivial large_v.V := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      rw [finrank_span_finset_eq_card]
      .
        simp [fin_basis]
        rw [← Finset.card_ne_zero]
        grind
      .
        simp [fin_basis]
        apply LinearIndepOn.id_image
        exact Module.Basis.linearIndepOn B ↑fin_basis_idx


    conv =>
      pattern (𝓝[>] 0)
      equals (𝓝[>] (0 * 0)) => simp

    apply Filter.TendstoNhdsWithinIoi.mul (by simp) (by simp)
    .
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      simp
      -- (R' (V := V))
      let R'' := ⌈R'_ large_v.V⌉₊
      rw [← Filter.tendsto_add_atTop_iff_nat R'']
      --  Filter.tendsto_add_atTop_iff_nat
      apply squeeze_zero_nhdsGT (g := (fun (R: ℕ) => (det_bound_const (V := large_v.V) * (1 + (R + R'')) ^ 2 * ((a * (R + R'')^d : ℝ))) / ((R + R'') ^ (↑d + 3) : ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro R R_pos
        have det_pos := (Q_R_matrix_pos_def (R + R'') (V := large_v.V) (by
          -- TODO - why is this so messy?
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ large_v.V)
          rw [add_comm]
          simp
          grind
        )).det_pos
        norm_cast at det_pos
        positivity
      .
        apply Filter.Eventually.of_forall
        intro R
        have foo := det_bound (V := large_v.V) (R := R + R'') (by
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ (V := large_v.V))
          rw [add_comm]
          simp
          grind
        )
        simp
        simp at foo
        grw [foo]
        by_cases const_zero: det_bound_const (V := large_v.V) = 0
        .
          simp [const_zero]

        field_simp
        rw [mul_div_assoc]
        rw [mul_div_assoc]
        rw [mul_assoc]
        rw [mul_le_mul_iff_right₀]
        .
          by_cases r_zero: (R + R'') = 0
          .
            norm_cast
            simp [r_zero]
          .
            grw [s_growth (R + R'') (by grind)]
            norm_cast
            simp
            rw [mul_div_assoc]
        .
          have nonneg := det_bound_const_nonneg (V := large_v.V)
          grind
      . poly_tendsto
    .
      --apply Asymptotics.IsLittleO.tendsto_div_nhds_zero
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      apply squeeze_zero_nhdsGT (g := (fun (n: ℝ) => (a * n^d : ℝ) / (n ^ (↑d + 3))) ∘ (fun (n: ℕ) => (n: ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro n hn
        have card_nonzero: (0: ℝ) < #(S ^ n) := by
          simp
          apply Finset.Nonempty.pow
          apply S_nonempty

        norm_cast
        positivity
      .
        apply Filter.Eventually.of_forall
        intro n
        by_cases hn: n = 0
        .
          simp [hn]
        .
          grw [s_growth n (by grind)]
          norm_cast
          simp
      . poly_tendsto
  .
    -- TODO - deduplicate
    rw [finrank_span_finset_eq_card] at V_bound
    .
      simp [fin_basis] at V_bound
      rw [Finset.card_image_of_injective] at V_bound
      .
        simp [card_fin_basis_idx] at V_bound
        grind
      . exact Module.Basis.injective B
    .
      simp [fin_basis]
      apply LinearIndepOn.id_image
      exact Module.Basis.linearIndepOn B ↑fin_basis_idx

#synth FiniteDimensional ℝ LipschitzH
