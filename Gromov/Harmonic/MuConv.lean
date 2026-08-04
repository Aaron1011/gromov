module

public import Mathlib
public import Gromov.Harmonic.Convolution

/-!
# Iterated convolution with `mu`

`mu_conv_eq_sum` expressing `muConv` as a sum over tuples, its nonnegativity and `L¹` norm, and
the telescoping identity `f_n_sub_conv`.
-/

@[expose] public section

set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

theorem mu_conv_eq_sum (m: ℕ): muConv m = fun g => (((1 : ℝ) / (#(S) : ℝ)) ^ (m + 1)) * (NTupleSum  (m + 1) (delta g))  := by
  induction m with
  | zero =>
    funext g
    simp [muConv, NTupleSum, mu, delta, Pi.single, Function.update]
    by_cases g_in_s: g ∈ S
    .
      simp [g_in_s]
      conv =>
        rhs
        rhs
        rhs
        rhs
        equals {fun (a : Fin 1) => ⟨g, g_in_s⟩} =>
          ext a
          simp
          refine ⟨?_, ?_⟩
          . intro a_zero_eq
            ext x
            simp
            have x_eq_zero: x = 0 := by
              exact Fin.fin_one_eq_zero x
            rw [x_eq_zero]
            exact a_zero_eq
          . intro a_eq
            simp [a_eq]
      simp
    .
      simp [g_in_s]
      right
      by_contra this
      .
        simp at this
        obtain ⟨x, hx⟩ := this
        rw [← hx] at g_in_s
        simp at g_in_s
  | succ n ih =>
    unfold muConv
    rw [Function.iterate_succ_apply']
    nth_rw 3 [mu]
    funext g
    nth_rw 1 [conv_eq_sum]
    simp [-Finset.sum_pi_single]
    simp_rw [mul_comm]
    simp_rw [mul_assoc]
    rw [Summable.tsum_mul_left]
    simp_rw [Finset.sum_mul]
    rw [Summable.tsum_finsetSum]
    .
      conv =>
        lhs
        rhs
        arg 2
        intro x
        equals (Conv (muConv n) (delta x) ) g =>
          rw [conv_eq_sum]
          .
            unfold muConv
            unfold delta
            simp_rw [mul_comm]
          .
            apply conv_exists_fin_supp
            right
            simp [delta]


      simp_rw [f_conv_delta]
      simp_rw [ih]
      rw [← Finset.mul_sum]
      conv =>
        lhs
        rhs
        rhs
        arg 2
        intro s
        simp only [NTupleSum]

      rw [← mul_assoc]
      conv =>
        lhs
        lhs
        simp
        equals (((#S) : ℝ) ^ (n + 1 + 1))⁻¹ =>
          field_simp
          nth_rw 2 [pow_succ]
          simp
          rw [mul_comm]
      simp only [mul_eq_mul_left_iff, inv_eq_zero, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        and_self, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, Finset.card_eq_zero]
      left
      rw [← Finset.sum_attach]
      rw [← Finset.sum_product']
      apply Fintype.sum_bijective (e := fun (x) => (fun (i: Fin (n + 1 + 1)) => if hi: i.val = 0 then x.fst else x.snd ⟨i - 1, by omega⟩))
      .
        refine ⟨?_, ?_⟩
        .
          intro a b hab
          simp at hab
          ext p
          .
            have fst_eq := congrFun hab (⟨0, by omega⟩)
            simp at fst_eq
            rw [fst_eq]

          .
            have p_lt_n_plus := p.prop
            have p_val_neq: p.val ≠ n + 1 := by omega


            have snd_eq := congrFun hab (⟨p + 1, by omega⟩)
            by_cases p_eq_zero: p = 0
            .
              simp [p_eq_zero] at snd_eq
              rw [p_eq_zero]
              rw [snd_eq]
            .
              simp [p_eq_zero] at snd_eq
              rw [snd_eq]
        .
          intro f
          use ((f (⟨0, by omega⟩)), fun i => f (⟨i + 1, by omega⟩))
          funext i
          simp
          by_cases i_eq_zero: i = 0
          . simp [i_eq_zero]
          .
            simp [i_eq_zero]
            have i_val_neq_zero: i.val ≠ 0 := by
              simp [i_eq_zero]
            have one_le_i: 1 ≤ i.val := by omega
            simp [Nat.sub_add_cancel one_le_i]
      .
        intro x
        simp only [delta]
        rw [Pi.single_apply]
        rw [Pi.single_apply]


        split_ifs
        .
          rename _ => hi
          simp [hi]
        .
          rename_i g_eq g_mul_neq
          apply_fun (fun y =>  (x.fst.val) * y ) at g_eq
          rw [← mul_assoc] at g_eq
          simp at g_eq
          rw [← g_eq] at g_mul_neq
          rw [List.ofFn_succ] at g_mul_neq
          norm_cast at g_mul_neq
          conv at g_mul_neq =>
            arg 1
            lhs
            simp


          contradiction
        . rename_i g_mul_neq g_eq

          simp [List.ofFn_succ] at g_eq
          rw [← g_eq] at g_mul_neq
          simp at g_mul_neq
        . rfl
    . intro s hs
      simp [Pi.single_apply]
      rw [← summable_norm_iff]
      apply Summable.of_nonneg_of_le (f := fun a => ‖(fun f ↦ Conv f mu)^[n] mu ((Additive.toMul a))‖)
      .
        intro x
        simp
      . intro x
        split_ifs
        . rfl
        . simp
      .
        rw [summable_norm_iff]
        have conv_finsupp := mu_conv_finsupp  n
        unfold muConv at conv_finsupp

        apply summable_of_hasFiniteSupport
        apply Set.Finite.of_injOn (f := fun a => ( (Additive.toMul a))) (ht := conv_finsupp)
        .
          intro a ha
          exact ha
        . intro a ha b hb
          simp
    -- TODO - deduplicate this with the above goal
    .
      simp [Pi.single_apply]
      rw [← summable_norm_iff]
      apply Summable.of_nonneg_of_le (f := fun a => ‖(fun f ↦ Conv f mu)^[n] mu ((Additive.toMul a))‖)
      .
        intro x
        simp
      . intro x
        split_ifs
        . rfl
        . simp
      .
        rw [summable_norm_iff]
        have conv_finsupp := mu_conv_finsupp  n
        unfold muConv at conv_finsupp

        apply summable_of_hasFiniteSupport
        apply Set.Finite.of_injOn (f := fun a => ( (Additive.toMul a))) (ht := conv_finsupp)
        .
          intro a ha
          exact ha
        . intro a ha b hb
          simp
    .
      apply conv_exists_fin_supp
      right
      simp [delta]
      apply Set.Finite.subset (ht := Function.support_const_smul_subset _ _)
      have supp_sum := Finset.support_sum (s := S) (f := fun s => Pi.single (M := fun _ : G => ℝ) s (1: ℝ))
      conv =>
        arg 1
        arg 1
        equals fun x => ∑ s ∈ S, Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) x =>
          funext a
          simp

      apply Set.Finite.subset (ht := supp_sum)
      simp
      exact Set.toFinite (⋃ i ∈ S, {i})

lemma mu_conv_nonneg (n: ℕ): ∀ g, 0 ≤ muConv  n g := by
  intro g
  induction n with
  | zero =>
    simp [muConv, mu]
    split_ifs
    . simp
    . simp
  | succ n ih =>
    rw [mu_conv_eq_sum]
    apply mul_nonneg
    . simp
    .
      simp [NTupleSum]
      apply Finset.sum_nonneg
      intro i hi
      simp [delta, Pi.single_apply]
      split_ifs
      . simp
      . simp


lemma f_n_nonneg: ∀ n: ℕ, ∀ g: G,  0 ≤ f_n n g := by
  intro n g
  simp [f_n]
  apply mul_nonneg
  . positivity
  . apply Finset.sum_nonneg
    intro i hi
    apply mu_conv_nonneg

lemma conv_laplce_norm (n: ℕ) (H_n: ℕ → G → ℝ): eLpNorm ((Laplace_b ((Conv (H_n n)) (f_n n)))) ⊤ (μ := volume (α := G)) ≤ eLpNorm (H_n n) ⊤ * (eLpNorm (Laplace_b (f_n n)) 1 (μ := volume (α := G))) := by
  rw [laplace_conv_eq_laplace_right]
  .
    unfold Conv
    eta_reduce
    simp only [volume]
    rw [haar_eq_haar_add]

    have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
      (g := Laplace_b (f_n n)) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
      (by simp)
      (by simp)
      (by simp)
      (by simp)
      (by apply AEMeasurable.of_discrete)
      (by apply AEMeasurable.of_discrete)


    refine le_trans my_norm ?_
    have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one]
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    rw [mul_assoc]
    exact le_trans (mul_le_mul_left hmul _) (le_of_eq (one_mul _))
  .
    apply conv_exists_fin_supp
    right
    exact f_n_fin_supp n
  . apply f_n_nonneg
  . exact f_n_fin_supp n


lemma lintegral_g_eq_add (f: G → ENNReal): (∫⁻ (g: G), f g) = (∑' (g : G), f g) := by
  rw [MeasureTheory.lintegral_countable']
  simp [MeasureTheory.volume, my_haar_eq_count]

lemma integral_eq_eq_sum (f: G → ℝ) (hf: Integrable f): (∫ (g: G), f g) = (∑' (g : G), f g) := by
  rw [MeasureTheory.integral_countable]
  .
    simp [MeasureTheory.volume]
    simp_rw [my_haar_eq_count]
    simp
  . apply hf


lemma mu_norm_one (m: ℕ): MeasureTheory.eLpNorm (muConv  m) 1 = 1 := by
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [lintegral_g_eq_add]
  simp [mu_conv_eq_sum]
  rw [ENNReal.tsum_mul_left]
  simp [NTupleSum, delta]
  conv =>
    lhs
    rhs
    equals ENNReal.ofReal (∑' (i : G), (∑ x : (Fin (m + 1) → { x // x ∈ S }), if (List.ofFn x).unattach.prod = i then 1 else 0 )) =>
      conv =>
        lhs
        arg 1
        intro i
        rw [Real.enorm_of_nonneg (by
          apply Finset.sum_nonneg
          intro x hx
          simp [delta, Pi.single_apply]
          split_ifs
          . simp
          . simp
        )]


      rw [← ENNReal.ofReal_tsum_of_nonneg]
      simp [Pi.single_apply]
      . intro g
        apply Finset.sum_nonneg
        intro i
        simp [Pi.single_apply]
        split_ifs
        . simp
        . simp
      .
        apply summable_sum
        intro i hi
        simp only [Pi.single_apply]
        apply summable_of_hasFiniteSupport
        apply Set.Finite.subset (s := {(List.ofFn i).unattach.prod})
        . simp
        . intro a ha
          simp
          simp at ha
          rw [ha]
  rw [Summable.tsum_finsetSum]
  .
    conv =>
      lhs
      rhs
      rhs
      arg 2
      intro i
      simp only [eq_comm]
      rw [tsum_ite_eq]
    simp
    rw [Real.enorm_of_nonneg (by
      simp
    )]
    field_simp
    rw [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_pow]
    rw [← ENNReal.ofReal_mul]
    .
      field_simp
      simp
      exact Finset.nonempty_iff_ne_empty.mp S_nonempty
    . simp
    . simp
  .
    -- TODO - deduplicate this with the above goal
    intro a ha
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (s := {(List.ofFn a).unattach.prod})
    . simp
    . intro a ha
      simp
      simp at ha
      rw [ha]


--set_option pp.analyze true

-- Proposition 3.15.1 from Vikman
theorem f_n_norm_one (n: ℕ): MeasureTheory.eLpNorm (f_n  n) 1 = 1 := by
  unfold f_n
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [lintegral_g_eq_add]
  rw [ENNReal.tsum_mul_left]
  conv =>
    lhs
    arg 2
    arg 1
    intro g
    equals ∑ m: Fin (n + 1), ‖muConv (↑m) g‖ₑ =>
      rw [Real.enorm_of_nonneg (by
        apply Finset.sum_nonneg
        intro i hi
        apply mu_conv_nonneg
      )]
      rw [ENNReal.ofReal_sum_of_nonneg (by
        intro i hi
        apply mu_conv_nonneg
      )]
      conv =>
        lhs
        arg 2
        intro i
        rw [← Real.enorm_of_nonneg (by
          apply mu_conv_nonneg
        )]

  rw [Summable.tsum_finsetSum]
  .
    have mu_norm := mu_norm_one
    simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm'] at mu_norm
    simp_rw [lintegral_g_eq_add] at mu_norm
    simp_rw [mu_norm]
    simp
    norm_cast
    rw [Real.enorm_of_nonneg (by
      simp
      linarith
    )]
    rw [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_mul]
    .
      field_simp
      simp
    . simp
      linarith
  .
    simp


-- Proposition 3.15.2 from Vikman
theorem f_n_sub_conv (n: ℕ): MeasureTheory.eLpNorm ((f_n  n) - (Conv (f_n  n) (mu ))) 1 ≤ ENNReal.ofReal ((2 : ℝ) / ((n + 1) : ℝ)) := by
  unfold f_n
  conv =>
    lhs
    arg 1


  conv =>
    lhs
    arg 1
    arg 1
    equals ((1: ℝ) / (n + 1)) • ∑ m: Fin (n + 1), muConv (↑m) =>
      funext p
      simp
  simp_rw [← smul_eq_mul]
  conv =>
    lhs
    arg 1
    rhs
    arg 1
    rw [← Pi.smul_def]


  rw [conv_smul]
  conv =>
    lhs
    arg 1
    rhs
    equals ((1 : ℝ) / ((n + 1) : ℝ)) • (Conv (∑ m: Fin (n + 1), muConv (m)) (mu )) =>
      funext g
      simp
      left
      conv =>
        lhs
        arg 1
        equals ∑ m: Fin (n + 1), muConv  (m) =>
          funext y
          simp

  rw [conv_sum]
  .
    rw [← smul_sub]
    rw [← Finset.sum_sub_distrib]
    conv =>
      lhs
      arg 1
      rhs
      arg 2
      intro x
      rhs
      equals muConv (↑x + 1) =>
        unfold muConv
        rw [Function.iterate_succ_apply']

    conv =>
      lhs
      arg 1
      rhs
      equals -∑ x: Fin (n + 1), ((muConv  (↑x + 1)) - (muConv  (x.val))) =>
        simp


    conv =>
      lhs
      arg 1
      rhs
      rhs
      equals (muConv (n + 1)) - muConv (0) =>
        induction n with
        | zero =>
          simp

        | succ y iy =>
          rw [Finset.sum_fin_eq_sum_range]
          rw [Finset.sum_range_succ_comm]
          rw [Finset.sum_fin_eq_sum_range] at iy
          simp at iy
          simp
          conv =>
            lhs
            rhs
            rw [Finset.sum_congr (s₂ := Finset.range (y + 1)) rfl (g := fun x => if x < y + 1 then muConv (x + 1) - muConv (x) else 0) (by
              intro x hx
              simp
              simp at hx
              split_ifs
              . simp
              . omega
            )]


          simp [iy]

    simp
    nth_rw 1 [muConv]
    simp
    calc
      _ ≤ ‖((n + 1): ℝ)⁻¹‖ₑ * MeasureTheory.eLpNorm ((mu - muConv (n + 1))) 1 MeasureTheory.volume := by
        apply MeasureTheory.eLpNorm_const_smul_le
      _ ≤ ‖((n + 1): ℝ)⁻¹‖ₑ * (MeasureTheory.eLpNorm ((mu)) 1 MeasureTheory.volume + (MeasureTheory.eLpNorm ((muConv (n + 1))) 1 MeasureTheory.volume)) := by
        have sub_le := MeasureTheory.eLpNorm_sub_le (p := 1) (f := mu ) (g := muConv  (n + 1)) (μ := MeasureTheory.volume) ?_ ?_ (by simp)
        .
          apply mul_le_mul_right sub_le
        . apply MeasureTheory.AEStronglyMeasurable.of_discrete
        . apply MeasureTheory.AEStronglyMeasurable.of_discrete
      _ ≤ ENNReal.ofReal ((2: ℝ) / ((n + 1): ℝ)) := by
        rw [mu_norm_one]
        have mu_single_norm := mu_norm_one  0
        simp [muConv] at mu_single_norm
        rw [mu_single_norm]
        field_simp
        norm_cast
        rw [Real.enorm_of_nonneg (by
          simp
          linarith
        )]
        rw [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul]
        simp
        rw [mul_comm]
        field_simp
        simp
        positivity
  . exact mu_finsupp


#print axioms mu_conv_eq_sum
#print axioms f_n_norm_one
#print axioms f_n_sub_conv

end GeneratesNS
