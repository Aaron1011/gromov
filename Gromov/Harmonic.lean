import Mathlib
import Mathlib.Algebra.Group.Gromov.Defs

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS


-- If a harmonic function has a maximum value, then it must be a constant function
-- We state 'f is harmonc' as 'Laplace_b f = 0', as this is the hypothesis we have where we need to call this lemma
-- This is true even if it's a local maximum (considered in terms of the  poitns reached by multiply by S), but
-- we don't need that result yet
lemma harmonic_maximum_implies_const (f: G → ℝ) (hf: Laplace_b  f = 0) (a: G) (h_max: ∀ g: G, f g ≤ f a): f = fun _ => f a := by
  have path_implies_max (l : List S): f (l.unattach.prod * a) = f a := by
    induction l with
    | nil =>
      simp
    | cons s l ih =>
      simp
      simp [Laplace_b, f_conv_mu] at hf
      have f_at_l := congrFun hf (l.unattach.prod * a)
      simp at f_at_l
      rw [sub_eq_zero] at f_at_l
      rw [ih] at f_at_l
      field_simp at f_at_l

      -- TODO - is there a 'Finset.expect' theorem we can use?
     -- rw [← Finset.expect_eq_sum_div_card] at f_at_l
     -- TODO - upstream this to mathlib in some form
      have f_s_eq: ∀ s: S, f a = f (s * (l.unattach.prod * a)) := by
        by_contra!
        simp at this
        obtain ⟨s, s_mem_s, hs⟩ := this
        by_cases val_le_max: f (s * (l.unattach.prod * a)) ≤ f a
        .
          have val_lt_max: f (s * (l.unattach.prod * a)) < f a := by
            exact lt_of_le_of_ne (h_max (↑s * (l.unattach.prod * a))) (id (Ne.symm hs))

          have sum_strict_lt := Finset.sum_lt_sum (f := fun x => f (x * (l.unattach.prod * a))) (g := fun x => f a) (s := S) ?_ ?_
          .
            simp at sum_strict_lt
            rw [mul_comm] at sum_strict_lt
            rw [← div_lt_iff₀] at sum_strict_lt
            .
              apply ne_of_gt at sum_strict_lt
              contradiction
            . simpa using hS
          . intro s hs
            apply h_max
          . use s
        .
          have val_gt := h_max (s * (l.unattach.prod * a))
          simp at val_le_max
          linarith
      specialize f_s_eq s
      rw [f_s_eq]
      rw [mul_assoc]
  ext g

  obtain ⟨l, h_l_prod⟩ := mem_S_prod_list (g * a⁻¹)
  simp [ProdS] at h_l_prod
  specialize path_implies_max l
  rw [h_l_prod] at path_implies_max
  simpa using path_implies_max


variable {V: Submodule ℝ LipschitzH} [Nontrivial V] (V_real: ∀ u ∈ V, ∀ g: G, (u g).im = 0) (hV : Even (Module.finrank V))  [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]


noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)

noncomputable def Q_R_lin (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R (fun g => (u.val g).re) (fun g => (v.val g).re)
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      simp [HSMul.hSMul, SMul.smul]
      simp_rw [← mul_assoc]
      simp_rw [mul_comm]
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
    simp [HSMul.hSMul, SMul.smul]
    simp_rw [← mul_assoc]
}

lemma Q_R_lin_symm (R: ℝ): (Q_R_lin R (V := V)).IsSymm := {
  eq := by
    intro u v
    simp [Q_R_lin, Q_R]
    simp_rw [mul_comm]
}

noncomputable def V_basis := Module.Basis.ofVectorSpace ℝ V

noncomputable def Q_R_matrix (R: ℝ) := ((Q_R_lin R (V := V)).toMatrix₂ V_basis V_basis)

lemma Q_R_lin_hermetian (R: ℝ): (Q_R_matrix R (V := V)).IsHermitian := by
  rw [Q_R_matrix, ← LinearMap.isSymm_iff_isHermitian_toMatrix]
  apply Q_R_lin_symm

lemma Q_lin_pos_semi_def (R: ℝ): (Q_R_matrix R (V := V)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Q_R_lin_hermetian _)
  intro x
  rw [Q_R_matrix]
  rw [star_dotProduct_toMatrix₂_mulVec, Q_R_lin]
  simp only [Q_R, DFunLike.coe]
  apply Finset.sum_nonneg
  intro g _
  rw [← pow_two]
  positivity

lemma v_basis_app_nonzero (k: ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)): ∃ g: G, (V_basis k).val g ≠ 0 := by
  by_contra!
  rw [← funext_iff] at this
  have nonzero := Module.Basis.ne_zero V_basis k
  conv at this =>
    rhs
    equals 0 =>
      ext a
      simp
  simp at nonzero
  have k_zero: V_basis k = 0 := by
    apply_fun Subtype.val
    .
      apply_fun DFunLike.coe
      .
        exact this
      . intro a b hab
        ext g
        rw [funext_iff] at hab
        specialize hab g
        simp at hab
        exact hab
    . simp
  contradiction

lemma v_basis_r: ∃ R: ℝ, ∀ k: ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V), ∃ g ∈ Metric.closedBall 1 R, (V_basis k).val g ≠ 0 := by
  use ((Finset.image ((fun (k: (Module.Basis.ofVectorSpaceIndex ℝ ↥V)) => (WordNorm (v_basis_app_nonzero k).choose : ℝ))) Finset.univ)).max' ?_
  .
    intro k
    use (v_basis_app_nonzero k).choose
    refine ⟨?_, ?_⟩
    .
      simp
      apply Finset.le_max'
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      use k
      simp [dist, WordDist_one]
    . apply (v_basis_app_nonzero k).choose_spec
  .
    simp
    rw [Finset.univ_nonempty_iff]
    have foo := Module.Basis.ofVectorSpace ℝ V
    have bar := Module.Basis.index_nonempty foo
    exact bar


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
        simp [HSMul.hSMul, SMul.smul]
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


include V_real in
lemma Q_R_matrix_pos_def (R: ℝ) (hR: (v_r_all_nonzero (V := V)).choose ≤ R): (Q_R_matrix R (V := V)).PosDef := by
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
        grw [hR] at g_mem
        simpa using g_mem
      . simp at this
        simp at x_g_nonzero
        rw [Complex.ext_iff] at x_g_nonzero
        --simp [DFunLike.coe] at V_real
        conv at x_g_nonzero =>
          arg 1
          rhs
          rw [← LipschitzH_apply]
          rw [V_real _ (by
            apply Submodule.sum_smul_mem
            simp
          )]

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

open scoped Finset
open scoped Pointwise

noncomputable def my_expr (d: ℝ) (R : ℕ) := #(S ^ R) * ((Q_R_matrix R (V := V)).det ^ (1 / Module.finrank ℝ V)) / (R ^ d)

lemma theorem_3_23 (d: ℝ): ∃ C: ℝ, Filter.liminf (fun (R: ℕ) => ENNReal.ofReal (my_expr (V := V) d R)) (Filter.atTop) ≠ ⊤ := by
  sorry
