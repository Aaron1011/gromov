module

public import Mathlib
public import Gromov.Vendor.Carleson
public import Gromov.Defs
public import Gromov.LipschitzNorm
public import Gromov.Theorem323
public import Gromov.TendstoTactic
public import Gromov.TendstoNhdsMul
public import Gromov.Convolution
public import Gromov.Complexification

/-!
# Convolution and the Laplacian

Basic compatibility of the discrete Laplacian with convolution: additivity, scalar
multiplication, and `laplace_conv_eq_laplace_right`.
-/

public section

set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

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
            . simpa using S_nonempty
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


variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]


open scoped Finset
open scoped Pointwise


lemma haar_eq_haar_add : myHaar = myHaarAddOpp := by
  rfl

open scoped Convolution
open MeasureTheory


lemma laplace_b_const (k: ℝ): Laplace_b (fun g => k) = 0 := by
  simp [Laplace_b]
  simp [f_conv_mu]
  ext a
  simp
  norm_cast
  rw [← mul_assoc]

  rw [inv_mul_cancel₀]
  . simp
  . simp
    have foo := S_nonempty
    grind


-- Linearity lemmas for convolution - this is basically just wrapping the MeasureTheory.ConvolutionExists lemmas,
-- specialized for our own Additive/MulOpposite wrappers
lemma conv_add_right {f g h: G → ℝ} (h_fg: ConvExists f g) (h_fh : ConvExists f h):  Conv f (g + h) = Conv f g + Conv f h := by
  unfold Conv
  conv =>
    lhs
    intro x
    arg 2
    equals (fun x => g ((Additive.toMul x))) + (fun x => h ((Additive.toMul x))) =>
      rfl

  rw [MeasureTheory.ConvolutionExists.distrib_add]
  . rfl
  . exact h_fg
  . exact h_fh

lemma conv_add_left {f g h: G → ℝ} (h_fh: ConvExists f h) (h_gh : ConvExists g h):  Conv (f + g) h = Conv f h + Conv g h := by
  unfold Conv
  conv =>
    lhs
    intro x
    arg 1
    equals (fun x => f ((Additive.toMul x))) + (fun x => g ((Additive.toMul x))) =>
      rfl

  rw [MeasureTheory.ConvolutionExists.add_distrib]
  . rfl
  . exact h_fh
  . exact h_gh

lemma conv_smul {f h: G → ℝ} (k: ℝ): Conv (k • f) h = k • Conv f h := by
  funext g
  show MeasureTheory.convolution (G := Additive G) (k • f) h (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
     = k • MeasureTheory.convolution (G := Additive G) f h (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
  simp only [MeasureTheory.convolution_def]
  rw [← MeasureTheory.integral_smul]
  congr 1
  funext t
  simp only [Pi.smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

lemma smul_conv (f h: G → ℝ) (k: ℝ): Conv f (k • h) = k • Conv f h := by
  funext g
  show MeasureTheory.convolution (G := Additive G) f (k • h) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
     = k • MeasureTheory.convolution (G := Additive G) f h (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
  simp only [MeasureTheory.convolution_def]
  rw [← MeasureTheory.integral_smul]
  congr 1
  funext t
  simp only [Pi.smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring


lemma laplace_conv_eq_laplace_right_of_lp2 (f g: G → ℝ) (hfg: ConvExists f g) (hf: MemLp f 2 Measure.count) (hg: MemLp g 2 Measure.count): Laplace_b (Conv f g) = Conv f (Laplace_b g) := by
  simp_rw [Laplace_b]
  rw [conv_assoc_of_lp2]

  nth_rw 2 [sub_eq_add_neg]
  rw [conv_add_right]
  -- TODO - figure out how to do this without a 'conv' block
  conv =>
    rhs
    rhs
    equals Conv f ((-1 : ℝ) • (Conv g (mu ))) =>
      simp
  rw [smul_conv]
  simp
  . rw [← sub_eq_add_neg]
  . exact hfg
  .
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt]
    intro a
    simp_rw [f_conv_mu]
    simp_rw [← mul_assoc, mul_comm, mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    simp_rw [Finset.mul_sum]
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt] at hfg
    specialize hfg (s * a)
    simp_rw [mul_div]
    exact hfg
  . exact hf
  . exact hg
  . apply mu_finsupp


lemma laplace_conv_eq_laplace_right (f g: G → ℝ) (hfg: ConvExists f g) (g_nonneg: ∀ a: G, 0 ≤ g a) (g_finsupp: g.support.Finite): Laplace_b (Conv f g) = Conv f (Laplace_b g) := by
  simp_rw [Laplace_b]
  rw [conv_assoc]

  nth_rw 2 [sub_eq_add_neg]
  rw [conv_add_right]
  -- TODO - figure out how to do this without a 'conv' block
  conv =>
    rhs
    rhs
    equals Conv f ((-1 : ℝ) • (Conv g (mu ))) =>
      simp
  rw [smul_conv]
  simp
  . rw [← sub_eq_add_neg]
  . exact hfg
  .
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt]
    intro a
    simp_rw [f_conv_mu]
    simp_rw [← mul_assoc, mul_comm, mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    simp_rw [Finset.mul_sum]
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt] at hfg
    specialize hfg (s * a)
    simp_rw [mul_div]
    exact hfg
  . exact hfg
  .
    apply conv_exists_fin_supp
    right
    exact mu_finsupp
  . apply g_finsupp
  . exact g_nonneg
  . exact mu_finsupp
  . intro a
    simp [mu]
    positivity

#print axioms laplace_conv_eq_laplace_right


    -- simp_rw [tsum_eq_sum]


lemma f_n_fin_supp (n: ℕ): (f_n  n).support.Finite := by
  unfold f_n
  simp
  apply Set.Finite.inter_of_right
  apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
  refine Set.Finite.biUnion' ?_ ?_
  . exact Set.toFinite (Membership.mem Finset.univ.val)
  . intro m hm
    apply mu_conv_finsupp


-- The expression 'Σ s_1, ..., s_n ∈ S, f(s_1 * ... * s_n)'
-- This is a sum over all n-tuples of elements in S, where each term in is f (s_1 * ... * s_n)
-- TODO - is there aless horrible way to write in in mathlib?
@[expose]
def NTupleSum (n: ℕ) (f: G → ℝ): ℝ := ∑ s : (Fin n → S), f ((List.ofFn s).unattach.prod)


-- Proposition 3.12, item 3, in Vikman
-- The 'm + 1' terms are due to the fact that 'muConv 0' still applies mu once (without any convolution)

end GeneratesNS
