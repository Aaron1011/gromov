module

public import Mathlib
public import Gromov.Defs
public import Gromov.LipschitzNorm
public import Gromov.TendstoTactic
public import Gromov.TendstoNhdsMul
public import Gromov.ToMathlib.LinearAlgebra.Matrix.PosDef
public import Gromov.ToMathlib.LinearAlgebra.Matrix.ToMatrix
public import Gromov.ToMathlib.LinearAlgebra.Matrix.Det

/-!
# The cutoff inequality

`cutoff_inequality`, the discrete integration-by-parts estimate underlying Theorem 3.23.
-/

@[expose] public section

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

-- Reverse poincare inequality
-- Lemma 12.2
-- The gradient-squared for the *left* Cayley graph (edges `{x, s * x}`).
-- Note that, as with `Harmonic`, our multiplication order is swapped relative to the paper:
-- `f (s * x)` instead of `f (x * s)`. This is what makes it agree with `MeasureTheory.convolution`
-- (see the note above `Conv` in `Defs.lean`) and with the right-invariant `WordDist`, so that
-- the balls `B_c_r j r = B_r r * j` are right translates and no `MulOpposite` leaks into the
-- convolution terms. `deriv_sq` is invariant under right translation:
-- `deriv_sq (f ∘ (· * j)) x = deriv_sq f (x * j)`, which is what Lemma 3.25 (c) needs.
noncomputable def deriv_sq (f: G → ℝ) (x: G) := ∑ s ∈ S, (f (s * x) - f x)^2

set_option maxHeartbeats 9000000 in
lemma cutoff_inequality (f φ : G → ℝ) (hf: Laplace_b f = 0) (hφ: φ.support.Finite):
    ∑' (x: G), ∑ s ∈ S, ((f x * φ x) - (f (s * x) * φ (s * x)))^2 ≤  ∑' (x: G), ∑ s ∈ S, (f x)^2 * (φ (s * x) - φ x)^2  := by

  conv =>
    lhs
    arg 1
    intro x
    arg 2
    intro s
    rw [pow_two]
  apply le_of_mul_le_mul_left (a := 2⁻¹ * (↑(#S) : ℝ)⁻¹) (a0 := by simp [S_nonempty])
  rw [mul_assoc]
  rw [← tsum_mul_left]
  rw [← laplace_sum_swap_helper]
  .
    conv =>
      lhs
      arg 1
      intro x
      rw [← Pi.mul_def]
      rw [laplace_prod_harmonic (hf := hf)]
      rw [← mul_assoc]
      rw [mul_comm (f x * φ x)]
      rw [mul_assoc, mul_assoc]
      rw [Finset.mul_sum]

    rw [tsum_mul_left]
    simp_rw [Finset.mul_sum]
    simp_rw [mul_comm (f _)]
    rw [Summable.tsum_finsetSum]
    .
      conv =>
        lhs
        rhs
        arg 2
        intro s
        rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
        simp

      nth_rw 2 [S_eq_Sinv]
      simp

      have sum_swap: ∑ x ∈ S, ∑' (c : G), φ (x * c) * ((φ (x * c) - φ c) * f c) * f (x * c) = -∑ x ∈ S, ∑' (c : G), φ (c) * ((φ (x * c) - φ c) * f (x * c)) * f (c) := by
        conv =>
          lhs
          arg 2
          intro s
          rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
          simp
        nth_rw 2 [S_eq_Sinv]
        simp
        rw [← Finset.sum_neg_distrib]
        simp_rw [← tsum_neg]
        ring

      have double {a b: ℝ} (hab: a = b): a = (a + b) / 2 := by
        rw [hab]
        ring

      rw [double sum_swap]
      rw [← sub_eq_add_neg]
      conv =>
        lhs
        rhs
        lhs
        rhs
        arg 2
        intro s
        arg 1
        intro x
        equals (((φ (s * x) - φ x) * f (s * x)) * f x) * (φ x) =>
          ring

      conv =>
        lhs
        rhs
        lhs
        lhs
        arg 2
        intro s
        arg 1
        intro x
        equals (((φ (s * x) - φ x) * f (s * x)) * f (x)) * φ (s * x)  =>
          ring

      rw [← Finset.sum_sub_distrib]
      conv =>
        lhs
        rhs
        arg 1
        arg 2
        intro s
        rw [← Summable.tsum_sub (by
          apply summable_of_hasFiniteSupport
          unfold Function.HasFiniteSupport
          simp
          apply Set.Finite.inter_of_right
          rw [← Function.comp_def]
          rw [Function.support_comp_eq_preimage]
          apply Set.Finite.preimage'
          . apply hφ
          . intro x hx
            simp
        ) (by
          apply summable_of_hasFiniteSupport
          unfold Function.HasFiniteSupport
          simp
          apply Set.Finite.inter_of_right
          apply hφ
        )]
      simp_rw [← mul_sub]
      conv =>
        lhs
        rhs
        lhs
        arg 2
        intro s
        arg 1
        intro x
        equals (f (s * x)) * f x * ((φ (s * x) - φ x))^2 =>
          ring

      have f_prod (x s: G): f (s * x) * (f x) ≤ (f (s * x)^2 + (f x)^2) / 2 := by
        field_simp
        rw [mul_comm]
        rw [← mul_assoc]
        apply two_mul_le_add_sq

      rw [div_eq_inv_mul]
      rw [← mul_assoc]
      nth_rw 2 [mul_comm]
      rw [mul_le_mul_iff_of_pos_left]
      calc
        ∑ s ∈ S, ∑' (x : G), f (s * x) * f x * (φ (s * x) - φ x) ^ 2 ≤ ∑ s ∈ S, ∑' (x : G), (f (s * x)^2 +  (f x)^2) * 2⁻¹ * (φ (s * x) - φ x) ^ 2 := by

          apply Finset.sum_le_sum
          intro s hs
          apply Summable.tsum_le_tsum
          intro x
          grw [f_prod]
          field_simp
          . simp
          .
            apply summable_of_finite_support
            unfold Function.HasFiniteSupport
            simp
            apply Set.Finite.inter_of_right
            apply Set.Finite.subset ?_ (Function.support_sub _ _)
            simp
            refine ⟨?_, hφ⟩
            rw [← Function.comp_def]
            rw [Function.support_comp_eq_preimage]
            apply Set.Finite.preimage'
            . apply hφ
            . intro x hx
              simp
          .
            apply summable_of_finite_support
            unfold Function.HasFiniteSupport
            simp
            apply Set.Finite.inter_of_right
            apply Set.Finite.subset ?_ (Function.support_sub _ _)
            simp
            refine ⟨?_, hφ⟩
            rw [← Function.comp_def]
            rw [Function.support_comp_eq_preimage]
            apply Set.Finite.preimage'
            . apply hφ
            . intro x hx
              simp
        _ ≤ _ := by
          simp_rw [add_mul]
          conv =>
            lhs
            arg 2
            intro s
            rw [Summable.tsum_add (by
              apply summable_of_finite_support
              unfold Function.HasFiniteSupport
              simp
              apply Set.Finite.inter_of_right
              apply Set.Finite.subset ?_ (Function.support_sub _ _)
              simp
              refine ⟨?_, hφ⟩
              rw [← Function.comp_def]
              rw [Function.support_comp_eq_preimage]
              apply Set.Finite.preimage'
              . apply hφ
              . intro x hx
                simp
            ) (by
                apply summable_of_finite_support
                unfold Function.HasFiniteSupport
                simp
                apply Set.Finite.inter_of_right
                apply Set.Finite.subset ?_ (Function.support_sub _ _)
                simp
                refine ⟨?_, hφ⟩
                rw [← Function.comp_def]
                rw [Function.support_comp_eq_preimage]
                apply Set.Finite.preimage'
                . apply hφ
                . intro x hx
                  simp
            )]
          rw [Finset.sum_add_distrib]
          conv =>
            lhs
            lhs
            arg 2
            intro s
            rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
            simp
          nth_rw 1 [S_eq_Sinv]
          simp
          rename_bvar c → b
          simp_rw [sub_sq_comm]
          field_simp
          norm_num
          field_simp
          simp_rw [tsum_div_const]
          rw [← Finset.sum_div]
          field_simp
          rw [← Summable.tsum_finsetSum]
          intro s hs
          apply summable_of_finite_support
          unfold Function.HasFiniteSupport
          simp
          apply Set.Finite.inter_of_right
          apply Set.Finite.subset ?_ (Function.support_sub _ _)
          simp
          refine ⟨hφ, ?_⟩
          rw [← Function.comp_def]
          rw [Function.support_comp_eq_preimage]
          apply Set.Finite.preimage'
          . apply hφ
          . intro x hx
            simp
      . simp [S_nonempty]
    .
      intro s hs
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      apply Set.Finite.inter_of_left
      apply Set.Finite.inter_of_left
      apply hφ
  . left
    simp
    apply Set.Finite.inter_of_right
    apply hφ

#print axioms cutoff_inequality

-- TODO - can we make WordNorm.instSemiNormedGroup and use norm notation

end GeneratesNS
