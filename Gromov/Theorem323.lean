import Mathlib
import Mathlib.Algebra.Group.Gromov.Defs

set_option linter.style.cdot false
set_option linter.style.whitespace false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V] (hV : Even (Module.finrank V))  [V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]


noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)

noncomputable def Q_R_lin (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
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

noncomputable def V_basis := Module.Basis.ofVectorSpace ℝ V
noncomputable def Q_R_matrix (R: ℝ) := ((Q_R_lin R (V := V)).toMatrix₂ V_basis V_basis)

omit V_decidable in
noncomputable def my_expr (d: ℝ) (R : ℕ) := #(S ^ R) * ((Q_R_matrix R (V := V)).det ^ ((1 : ℝ) / Module.finrank ℝ V)) / (R ^ d)

omit V_decidable in
noncomputable def growth_bound (d: ℝ) := Filter.liminf (fun (R: ℕ) => ENNReal.ofReal (my_expr (V := V) d R)) (Filter.atTop) ≠ ⊤


-- Todo - is the better way to declare theorem_3_23 so that the constant is not allowed to depend on V?
omit V in
structure V_Data where
  V: Submodule ℝ LipschitzH
  hV: FiniteDimensional ℝ V
  (V_even : Even (Module.finrank ℝ V))
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)


lemma Q_R_lin_symm (R: ℝ): (Q_R_lin R (V := V)).IsSymm := {
  eq := by
    intro u v
    simp [Q_R_lin, Q_R]
    simp_rw [mul_comm]
}
noncomputable def Q_R_single (R : ℝ) (u: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g)^2

lemma Q_R_single_eq (R: ℝ) (u : G → ℝ): Q_R_single R u = Q_R R u u := by
  unfold Q_R_single Q_R
  simp_rw [pow_two]

lemma Q_R_lin_hermetian (R: ℝ): (Q_R_matrix R (V := V)).IsHermitian := by
  rw [Q_R_matrix, ← LinearMap.isSymm_iff_isHermitian_toMatrix]
  apply Q_R_lin_symm


lemma v_r_all_nonzero: ∃ R: ℝ, ∀ u ∈ V, u ≠ 0 → ∃ g ∈ Metric.closedBall 1 R, u g ≠ 0 := by
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

noncomputable def R' : ℝ := (v_r_all_nonzero (V := V)).choose



lemma Q_R_matrix_pos_def (R: ℝ) (hR: (R' (V := V)) ≤ R): (Q_R_matrix R (V := V)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Q_R_lin_hermetian _)
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

    have foo := (v_r_all_nonzero (V := V)).choose_spec (V_basis.equivFun.symm x) (by apply Submodule.coe_mem) ?_
    .
      obtain ⟨g, g_mem, x_g_nonzero⟩ := foo
      specialize this g ?_
      .
        simp
        unfold R' at hR
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



omit V in
lemma theorem_3_23 (d: ℝ): ∃ C: ℕ, ∀ data: V_Data, growth_bound (V := data.V) (V_finite := data.hV) (V_decidable := data.V_decidable) d → (Module.finrank ℝ data.V) < C := by
  have C: ℕ := sorry
  use C
  intro data h_growth

  sorry
