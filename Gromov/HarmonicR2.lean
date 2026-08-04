module

public import Mathlib
public import Gromov.CutoffInequality

/-!
# The harmonic `R²` inequality

`harmonic_r2_inequality`, bounding a harmonic function on a ball of radius `R` by its values on
a ball of radius `2R`.
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

set_option maxHeartbeats 9000000 in
lemma harmonic_r2_inequality (f : G → ℝ) (hf : Laplace_b f = 0) (r: ℕ) (hr: r ≠ 0):
    ∑ x ∈ Metric.closedBall 1 (2 * r), deriv_sq f x ≤ ((1: ℝ) / r^2) * #(S) * ∑ x ∈ Metric.closedBall 1 (4 * r), f x ^ 2 := by
  -- `deriv_sq f x = ∑ s, (f (s*x) - f x)^2`; the proof below is written with the
  -- (equal) `(f x - f (s*x))^2` orientation, so rewrite to that first.
  have hrw : ∀ x : G, deriv_sq f x = ∑ s ∈ S, (f x - f (s * x)) ^ 2 := fun x => by
    simp only [deriv_sq]; exact Finset.sum_congr rfl fun s _ => by ring
  simp_rw [hrw]

  -- m * x + b
  -- m * (4*r) + b = 0
  -- b = -4 * r * m

  -- m * (2 *r) - * (4 * r * m) = 1
  -- 2rm - 4rm = 1
  -- m = -1/2
  let φ := fun (x: G) => if WordNorm x ≤ (2 * r) + 1 then 1 else if (WordNorm x ≤ 4 * r) then (-(WordNorm x)/(2 * (r: ℝ))) + 2 else 0
  have phi_support : φ.support ⊆ Metric.ball 1 (4 * r) := by
    intro s hs
    simp at hs
    rw [ite_eq_iff] at hs
    simp at hs
    by_cases s_gt: 2 * r + 1 < (WordNorm s)
    .
      specialize hs s_gt
      simp [dist]
      rw [WordDist_one]
      by_cases eq_four: WordNorm s = 4*r
      .
        simp [eq_four] at hs
        field_simp [hr] at hs
        norm_num at hs
      .
        norm_cast
        grind
    .
      simp at s_gt
      simp [dist, WordDist_one]
      norm_cast
      grind

  have foo := cutoff_inequality f φ hf ?_
  .
    rw [tsum_eq_sum (s := (finite_closed_ball 1 (4 * r)).toFinset)] at foo
    rw [tsum_eq_sum (s := (finite_closed_ball 1 (4 * r)).toFinset)] at foo
    .
      grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := (finite_closed_ball 1 (2 * r)).toFinset)] at foo
      .
        rw [Finset.sum_congr (g := fun x => ∑ s ∈ S, (f x - f (s * x)) ^ 2) (s₂ := (finite_closed_ball 1 (2 * r)).toFinset)] at foo
        .
          simp at foo
          grw [foo]
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro x hx
          conv =>
            rhs
            rw [mul_assoc]
            rhs
            equals ∑ s ∈ S, (f x)^2 =>
              simp
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro s hs
          simp [φ]
          have norm_s_x := word_dist_mul_eq (x := 1) (y := s) (z := x) hs
          simp_rw [WordDist_comm] at norm_s_x
          simp_rw [WordDist_one] at norm_s_x
          rw [← or_assoc] at norm_s_x
          cases norm_s_x
          .
            rename_i norm_s_x_eq
            cases norm_s_x_eq
            .
              rename_i s_lt
              simp [dist] at hx
              norm_cast at hx
              rw [WordDist_one] at hx
              by_cases s_x_le: WordNorm (s * x) ≤ 2 *r + 1
              .
                simp [s_x_le]
                simp [s_lt]
                split_ifs
                . simp
                  positivity
                .
                  have s_x_eq: WordNorm (s * x) = 2 *r + 1 := by grind
                  simp [s_x_eq]
                  field_simp
                  apply mul_le_mul
                  . simp
                  .
                    norm_num
                    ring
                    norm_num
                  . positivity
                  . positivity
                .
                  grind
              .
                have sub_eq: (WordNorm x) - 1 = WordNorm (s * x) := by omega
                have s_x_le_four: WordNorm (s * x) ≤ 4 * r := by
                  simp [s_lt] at hx
                  grind
                simp [s_x_le, s_x_le_four]
                split_ifs
                .
                  grind
                .
                  simp [← sub_eq]
                  rw [← sub_div]
                  simp
                  field_simp
                  push_cast
                  conv =>
                    lhs
                    rhs
                    lhs
                    equals 1 =>
                      rw [sub_eq]
                      rw [s_lt]
                      push_cast
                      ring
                  simp
                  norm_num
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]

                  rw [le_mul_iff_one_le_right]
                  . norm_num
                  . positivity
            .
              rename_i s_lt
              simp [dist] at hx
              norm_cast at hx
              rw [WordDist_one] at hx
              by_cases s_x_le: WordNorm (s * x) ≤ 2*r + 1
              .
                simp [s_x_le]
                split_ifs
                . simp
                  positivity
                .
                  have s_x_eq: WordNorm (s * x) = 2 *r := by grind
                  simp [s_x_eq]
                  rw [mul_comm]
                  apply mul_le_mul
                  .
                    norm_num
                    ring
                    norm_num
                    field_simp
                    rw [mul_sub]
                    rw [← pow_two]
                    rw [sub_mul]
                    conv =>
                      lhs
                      equals (2 * r) * (2 * r) - (WordNorm x) * 2 * r * 2 + (WordNorm x)^2 =>
                        ring
                    rename_i x_gt
                    simp at x_gt
                    omega
                  . simp
                  . positivity
                  . norm_num
              .
                by_cases norm_x_eq: WordNorm x = 4 * r
                .
                  have not_le: ¬(WordNorm (s * x) ≤ (2 *r) + 1) := by grind
                  have not_le_four: ¬(WordNorm (s * x) ≤ (4 *r)) := by grind
                  have x_le: (WordNorm (x) ≤ (4 *r)) := by grind
                  have not_x_le: ¬(WordNorm (x) ≤ (2 *r) + 1) := by grind
                  simp [not_le, not_le_four, x_le, not_x_le]
                  rw [mul_comm]
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]
                  rw [mul_le_mul_iff_left₀]
                  .
                    field_simp
                    grw [x_le]
                    grind
                    simp
                    norm_num
                    simp [norm_x_eq]
                  . positivity

                have sub_eq: (WordNorm x) = WordNorm (s * x) - 1 := by omega
                have s_x_le_four: WordNorm (s * x) ≤ 4 * r := by
                  rw [← s_lt]
                  grind
                simp [s_x_le, s_x_le_four]
                split_ifs
                .
                  field_simp
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]

                  rw [mul_le_mul_iff_right₀]
                  .
                    norm_num
                    field_simp
                    conv =>
                      lhs
                      lhs
                      ring
                    conv =>
                      rhs
                      equals (2^2) =>
                        norm_num

                    have norm_x_eq: WordNorm x = 2 *r + 1 := by grind
                    rw [← s_lt, norm_x_eq]
                    conv =>
                      lhs
                      lhs
                      simp
                      field_simp
                      ring
                    norm_num

                  . positivity
                .
                  simp [← sub_eq]
                  rw [← sub_div]
                  simp
                  field_simp
                  push_cast
                  conv =>
                    lhs
                    rhs
                    lhs
                    equals -1 =>
                      rw [sub_eq]
                      push_cast
                      rw [Nat.cast_sub (by grind)]
                      ring
                  simp
                  norm_num
                  -- TODO - surely this can be simplified
                  by_cases f_x_zero: (f x) ^2 = 0
                  . simp [f_x_zero]

                  rw [le_mul_iff_one_le_right]
                  . norm_num
                  . positivity

          .
            rename_i norm_eq
            simp [← norm_eq]
            positivity
        . rfl
        . intro x hx
          apply Finset.sum_congr
          . rfl
          . intro s hs
            simp [φ]
            simp [dist, WordDist_one] at hx
            norm_cast at hx
            have hx_le : WordNorm x ≤ 2 * r + 1 := by grind
            simp [hx_le]

            have hx_le_sub : WordNorm x ≤ 2 * r := by grind
            have foo := dist_word_le_mul (x := 1) (y := s⁻¹) (z := (s * x)) (by rw [S_eq_Sinv]; simp [hs])
            simp at foo
            simp [WordDist_comm, WordDist_one] at foo

            grw [hx_le_sub] at foo
            simp [foo]
      . simp
        intro a ha
        simp at ha
        simp
        grind
      .
        intro a ha ha2
        positivity
    .
      intro s hs
      simp at hs
      apply Finset.sum_eq_zero
      intro x hx
      have phi_s := Set.notMem_subset phi_support (a := s) ?_
      .
        simp at phi_s
        simp [phi_s]
        have phi_s_x := Set.notMem_subset phi_support (a := x * s)
        .
          simp at phi_s_x
          simp [dist] at hs
          rw [WordDist_comm] at hs
          grw [dist_word_le_mul (y := x)] at hs
          simp at hs
          simp [dist] at phi_s_x
          norm_cast at hs
          norm_cast at phi_s_x
          rw [Nat.lt_add_one_iff] at hs
          rw [WordDist_comm] at hs
          specialize phi_s_x hs
          simp [phi_s_x]
          exact hx
      . simp
        grind
    .
      -- TODO - deduplicate this
      intro s hs
      simp at hs
      apply Finset.sum_eq_zero
      intro x hx
      have phi_s := Set.notMem_subset phi_support (a := s) ?_
      .
        simp at phi_s
        simp [phi_s]
        have phi_s_x := Set.notMem_subset phi_support (a := x * s)
        .
          simp at phi_s_x
          simp [dist] at hs
          rw [WordDist_comm] at hs
          grw [dist_word_le_mul (y := x)] at hs
          simp at hs
          simp [dist] at phi_s_x
          norm_cast at hs
          norm_cast at phi_s_x
          rw [Nat.lt_add_one_iff] at hs
          rw [WordDist_comm] at hs
          specialize phi_s_x hs
          simp [phi_s_x]
          exact hx
      . simp
        grind

  .
    simp [φ]
    apply Set.Finite.subset (s := Metric.ball 1 (4 * r))
    .
      apply finite_ball
    . exact phi_support

#print axioms harmonic_r2_inequality

end GeneratesNS
