import Mathlib
import Gromov.Defs.LipschitzH

/-!
# Convolution on `G`

The convolution `Conv`, the measure `mu` and its iterates `muConv`, and the `Lp` packaging
`conv_mu_lp2`.
-/

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Convolution
open MeasureTheory

-- TODO - should we define this using 'Lp'?
-- NOTE - the Mathlib convolution uses the opposite order of arguments as in the Vikman paper (g(x - t) instead of g(t - x))
-- I originally used 'MulOpposite' make our usage agree with the paper, but this made it an enormous pain to work with
-- (since while Additive G is defeq to G, MulOpposite G is not defeq to G)
-- Nothing in the paper should actually depend on this (since we take a convolution over a symmetric generating set S)
-- Some of our definitions will have an inverse or order swap compared to the paper, but this is better than
-- fighting with 'MulOpposite' every time we need to prove something about a convolution

-- Note - there's some defeq abuse going on here, as we're passing in 'f' and 'g' directly (they take in G, not 'Additive G')
-- However, this makes it much easier to prove properties about this via the `MeasureTheory.ConvolutionExists` API
noncomputable def Conv (f g: G → ℝ) (x: G) : ℝ :=
  (MeasureTheory.convolution (G := Additive G) f g (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp x)


def ConvExists (f g: G → ℝ) := MeasureTheory.ConvolutionExists (G := Additive G) (fun x => f x.toMul) (fun x => g x.toMul) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp

noncomputable def mu: G → ℝ := ((1 : ℝ) / (#(S) : ℝ)) • ∑ s ∈ S, Pi.single s (1 : ℝ)

-- Definition 3.11 in Vikman - the m-fold convolution of μ with itself
noncomputable def muConv (n: ℕ): G → ℝ := (Nat.iterate (fun f => Conv  f (mu )) n) (mu )


-- TODO - this is left over from when I used MulOpposite
-- we should remove all usages of this
abbrev opAdd (g : G) := Additive.ofMul g


lemma conv_eq_sum {f h: G → ℝ} (hconv: ConvExists f h) (g: G): Conv f h g = ∑' (a : Additive G), f (a) * h (g * (Additive.toMul a)⁻¹) := by
  unfold Conv
  unfold MeasureTheory.convolution
  rw [MeasureTheory.integral_countable']
  .
    simp_rw [MeasureTheory.measureReal_def]
    unfold myHaarAddOpp
    simp_rw [MeasureTheory.Measure.addHaar_singleton]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    simp_rw [← singleton_carrier]
    simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    field_simp

    -- TODO - avoid defeq abuse here
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals h (Additive.ofMul g - a) =>
        rfl

    conv =>
      rhs
      arg 1
      intro a
      rhs
      arg 1
      equals Additive.ofMul g - a =>
        rw [sub_eq_add_neg]
        rfl

  . exact (hconv (opAdd g))


lemma conv_eq_sum'  {f h: G → ℝ} (hconv: ConvExists f h): Conv f h = fun g => ∑' (a : Additive G), f ((Additive.toMul a)) * h (g * (Additive.toMul a)⁻¹) := by
  funext g
  exact conv_eq_sum hconv g


abbrev delta (s: G): G → ℝ := Pi.single s 1


-- A versi on of `conv_exists` where at least one of the functions has finite support
-- This lets us avoid dealing with 'MemLp' in most cases
lemma conv_exists_fin_supp (f g: G → ℝ) (hfg: f.support.Finite ∨ g.support.Finite): ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
  intro x
  apply Continuous.integrable_of_hasCompactSupport
  . exact continuous_of_discreteTopology
  .
    unfold HasCompactSupport
    rw [isCompact_iff_finite]
    dsimp [tsupport]
    rw [closure_discrete]
    simp only [Function.support_mul]
    match hfg with
    | .inl hf =>
      apply Set.Finite.inter_of_left
      apply Set.Finite.subset (s := opAdd '' f.support)
      . unfold opAdd
        exact Set.Finite.image (fun g ↦ Additive.ofMul g) hf
      . intro a ha
        simp at ha
        simp [opAdd]
        exact ha
    | .inr hg =>
      apply Set.Finite.inter_of_right
      let myFun := fun a => -(opAdd a) + x
      have finite_image := Set.finite_image_iff (f := myFun) (s := g.support) ?_
      .
        conv =>
          arg 1
          equals (myFun '' Function.support g) =>
            ext a
            simp
            refine ⟨?_, ?_⟩
            . intro ha
              use (Additive.toMul x) / ((Additive.toMul a))
              refine ⟨ha, ?_⟩
              simp [myFun, opAdd]
            . intro ha
              simp [myFun, opAdd] at ha
              obtain ⟨b, b_zero, a_eq⟩ := ha
              rw [← a_eq]
              simp [b_zero]
        rw [finite_image]
        exact hg
      .
        simp [myFun, opAdd]

-- Proposition 3.12, item 1, in Vikman
lemma f_conv_delta (f: G → ℝ) (g s: G): (Conv  f (delta s)) g = f (s⁻¹ * g) := by
  unfold delta
  rw [conv_eq_sum]
  .
    rw [tsum_eq_sum (s := {opAdd ((s⁻¹ * g))}) ?_]
    .
      simp
      rfl
    .
      intro b hb
      simp only [Finset.mem_singleton] at hb
      simp only [mul_eq_zero]
      right
      apply Pi.single_eq_of_ne
      apply_fun (fun x => s⁻¹ * x)
      simp
      apply_fun (fun x => (x * (Additive.toMul b)) )
      simp
      rw [eq_comm]
      unfold opAdd at hb
      apply_fun Additive.ofMul
      simp
      apply_fun (fun x => x + b)
      rw [add_assoc]
      simp
      exact hb
  .
    apply conv_exists_fin_supp
    right
    simp


lemma mu_finsupp: (mu ).support.Finite := by
  simp [mu]
  rw [Function.support_const_smul_of_ne_zero]
  .
    apply Set.Finite.subset (s := ⋃ i ∈ S, Function.support (Pi.single i (1 : ℝ)))
    .
      simp
      exact Set.toFinite (⋃ i ∈ S, {i})
    .
      conv =>
        lhs
        arg 1
        equals fun (x: G) => ∑ s ∈ S, Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) x =>
          funext a
          simp
      apply Finset.support_sum (s := S) (f := fun i => Pi.single i (1: ℝ))
  . simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

#print axioms mu_finsupp

-- Proposition 3.12, item 2, in Vikman
lemma f_conv_mu (f: G → ℝ): (Conv  f (mu )) = fun g => ((1 : ℝ) / (#(S) : ℝ)) * ∑ s ∈ S, f (s * g) := by
  funext g
  rw [conv_eq_sum]
  .

    dsimp [mu]
    simp_rw [← mul_assoc]
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals (∑ s ∈ S, (Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) ((g * (Additive.toMul a)⁻¹)))) =>
        simp

    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum]
    .
      have delta_conv := f_conv_delta  f g
      conv at delta_conv =>
        intro x
        rw [conv_eq_sum (by
          apply conv_exists_fin_supp
          right
          simp
        )]

      simp_rw [mul_comm, mul_assoc]
      conv =>
        lhs
        rhs
        intro x
        arg 1
        intro b
        rw [mul_comm]
        rw [mul_assoc]
      simp [delta] at delta_conv
      conv at delta_conv =>
        intro x
        lhs
        arg 1
        intro a
        rw [mul_comm]
      conv =>
        lhs
        rhs
        intro x
        rw [Summable.tsum_mul_left (hf := by (
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (   x⁻¹ * g  ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
        ))]
        rw [delta_conv x]

      simp
      rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [mul_comm]
      simp
      left
      conv =>
        lhs
        arg 1
        equals S⁻¹ =>
          exact S_eq_Sinv
      simp
    .
      intro s hs
      by_cases card_zero: #(S) = 0
      .
        simp [card_zero]
      .
        conv =>
          arg 1
          intro a
          rw [mul_assoc, mul_comm, mul_assoc]
        rw [summable_mul_left_iff]
        .
          -- TODO - deduplicate this
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (s⁻¹ * g ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
        .
          simp [card_zero]
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp


noncomputable def conv_mu_lp2 (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := MeasureTheory.MemLp.toLp (Conv f (mu )) (by
  rw [MeasureTheory.MemLp]
  refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [f_conv_mu]
  simp_rw [Finset.mul_sum]
  have other := MeasureTheory.memLp_finset_sum (μ := MeasureTheory.volume (α := G)) (s := S) (p := 2) (f := fun s a => ((1 : ℝ) / (#(S) : ℝ)) * f (s * a)) (by
    intro s hs
    simp
    apply MeasureTheory.MemLp.const_mul
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      simp_rw [my_haar_eq_count]
      rw [MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self s]
      have mem_f := Lp.memLp f
      simp [volume, my_haar_eq_count] at mem_f
      exact mem_f
    . apply AEMeasurable.of_discrete
  )
  have sum_norm := other.2
  simp [eLpNorm, eLpNorm'] at sum_norm
  field_simp at sum_norm
  field_simp
  exact sum_norm
)

-- The Vikman paper defines the Laplace operator as a function ' ∆ : ℓ2(G) → ℓ2(G)'
-- However, we later have '∆ H_n', where H_n is only known to be in L∞
-- We should eventually refactor this, but for we, we just define it twice, once with just plain functions
-- The 'b' is for 'base' (we should come up with a better name)

end GeneratesNS
