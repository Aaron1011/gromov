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

variable {V: Submodule ℝ LipschitzH} (hV : Even (Module.finrank V))

noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)

lemma exists_Q_R_positive_definite: ∃ R: ℝ, ∀ u : G → ℝ, HarmonicR u → u ≠ 0 → (Q_R R u u) > 0 := by
  use 1
  intro u u_harmonic u_ne_zero
  by_contra!
  unfold Q_R at this
  have nonneg := Finset.sum_nonneg' (s := (finite_closed_ball 1 1).toFinset) (f := fun g => u g * u g) ?_
  .
    simp at nonneg
    have eq_zero: ∑ g ∈ (Metric.closedBall 1 1).toFinset, u g * u g = 0 := by grind
    rw [Finset.sum_eq_zero_iff_of_nonneg] at eq_zero
    .

    . intro i hi
      rw [← pow_two]
      positivity
  . intro i
    simp
    rw [← pow_two]
    positivity
