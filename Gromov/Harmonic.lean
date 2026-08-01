import Mathlib
import Gromov.Vendor.Carleson
import Gromov.Defs
import Gromov.LipschitzNorm
import Gromov.Theorem323
import Gromov.TendstoTactic
import Gromov.TendstoNhdsMul
import Gromov.Convolution

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



-- lemma Q_lin_pos_semi_def (R: ℝ): (Q_R_matrix R (V := V)).PosSemidef := by
--   apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Q_R_lin_hermetian V _)
--   intro x
--   rw [Q_R_matrix]
--   rw [star_dotProduct_toMatrix₂_mulVec, Q_R_lin]
--   simp only [Q_R, DFunLike.coe]
--   apply Finset.sum_nonneg
--   intro g _
--   rw [← pow_two]
--   positivity

lemma v_basis_app_nonzero (k: ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)): ∃ g: G, (V_basis V k).val g ≠ 0 := by
  by_contra!
  rw [← funext_iff] at this
  have nonzero := Module.Basis.ne_zero (V_basis V) k
  conv at this =>
    rhs
    equals 0 =>
      ext a
      simp
  simp at nonzero
  have k_zero: V_basis V k = 0 := by
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

lemma v_basis_r: ∃ R: ℝ, ∀ k: ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V), ∃ g ∈ Metric.closedBall 1 R, (V_basis V k).val g ≠ 0 := by
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



    -- let other := ((fun (x: (Additive G)) ↦ ‖g x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, myHaarAddOpp] fun (x: (Additive G)) ↦ ‖h x‖)
    -- have finsupp_conv := conv_exists_fin_supp (fun (b: G) => ‖f b‖) (fun b => other (Additive.ofMul b)) ?_
    -- . apply finsupp_conv x
    -- . left
    --   simp
    --   rw [← Function.comp_def]
    --   rw [Function.support_comp_eq]
    --   . apply f_finsupp
    --   . simp


-- -- We take advantage of junk values to avoid needing to prove that the convolutions actually exist
-- lemma conv_assoc_le {f g h b: G → ℝ} (x: G) (right_le: ‖Conv f (Conv g h) x‖ ≤ ‖b x‖): ‖Conv (Conv f g) h x‖ ≤ ‖b x‖ := by
--   by_cases f_g_exists: ConvExistsAt f g x
--   .
--     rw [conv_assoc]
--   .
--     conv =>
--       arg 1
--       arg 1
--       arg 1
--       unfold Conv
--     simp [convolution, integral]
--     unfold ConvExistsAt ConvolutionExistsAt at f_g_exists
--     simp [-toMul_sub] at f_g_exists
--     conv at f_g_exists =>
--       arg 1
--       arg 1
--       equals fun t ↦ f (t) * g (((Additive.ofMul x) - (Additive.ofMul t))) =>
--         rfl


--     conv =>
--       lhs
--       arg 1
--       arg 1
--       intro x
--       arg 2
--       intro y
--       rw [dif_neg (by
--         exact f_g_exists
--       )]
--       arg 2
--       equals (fun (hf: Integrable (fun t ↦ f (t) * g (((Additive.ofMul x) - (Additive.ofMul t))))) ↦ L1.integral (Integrable.toL1 (fun t ↦ f (t) * g (((Additive.ofMul x) - (Additive.ofMul t)))) hf)) =>
--         rfl



--     simp
--     simp [f_g_exists]
--     simp

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

    -- simp_rw [conv_eq_sum]
    -- rw [conv_eq_sum]

    -- nth_rw 3 [mu]
    -- apply Finite.support_conv
    -- exact ih


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
def NTupleSum (n: ℕ) (f: G → ℝ): ℝ := ∑ s : (Fin n → S), f ((List.ofFn s).unattach.prod)
--∑ s ∈ (Finset.pi (Finset.range (n + 1))) (fun _ => S), f (List.ofFn (n := n + 1) (fun m => s m.val (by simp))).prod



-- Proposition 3.12, item 3, in Vikman
-- The 'm + 1' terms are due to the fact that 'muConv 0' still applies mu once (without any convolution)
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

            have cast_succ_ne: p.castSucc.val ≠ n + 1 := by
              simp
              omega

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
          --rw [ofFn_fir] at g_mul_neq
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


  --rw [f_conv_mu]
  conv =>
    lhs
    arg 1
    arg 1
    equals ((1: ℝ) / (n + 1)) • ∑ m: Fin (n + 1), muConv (↑m) =>
      funext p
      simp
  simp_rw [← smul_eq_mul]
  --simp_rw [← Finset.smul_sum]
  --simp_rw [← smul_assoc]
  --rw [← Pi.smul_def]
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


  -- rw [conv_const_mul]
#print axioms mu_conv_eq_sum
#print axioms f_n_norm_one
#print axioms f_n_sub_conv

set_option maxHeartbeats 60000 in
noncomputable def nontrivial_harmonic_common (k: ℕ) (seq: ℕ → ℕ) (h_seq: Filter.Tendsto seq Filter.atTop Filter.atTop) (F: G → ℝ) (H_n: ℕ → G → ℝ) (h_conv_lipschitz: ∀ n, LipschitzWith k (Conv (H_n n) (f_n n)))
(tendsto_F: Filter.Tendsto ((fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) Filter.atTop (nhds F))
(H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1): LipschitzH := by

  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n (seq n)) (f_n (seq n)),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  let F_lipschitzh: LipschitzH := {
    toFun := (fun (g: G) => F g),
    lipschitz := by
      use k
      have closed_lipschitz := isClosed_setOf_lipschitzWith (α := G) (β := ℝ) k
      apply IsClosed.isSeqClosed at closed_lipschitz
      simp [IsSeqClosed] at closed_lipschitz
      have F_lipschitz := closed_lipschitz (p := F) (x := (fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) (by
        intro n
        apply h_conv_lipschitz
      ) tendsto_F
      exact F_lipschitz
    harmonic := by
      simp [Harmonic]
      intro g
      rw [tendsto_pi_nhds] at tendsto_F
      have lim_f_sum := tendsto_finset_sum (ι := S) (M := ℝ) (s := Finset.univ) (a := fun s => F (s.val * g)) (f := (fun (s: S) n ↦ Conv (H_n (seq n)) (f_n (seq n)) (s.val *g))) (x := Filter.atTop (α := ℕ)) ?_

      -- TODO - figure out why lean hangs without this
      have my_mul : ContinuousMul ℝ := instIsTopologicalRingReal.toContinuousMul
      have lim_f_mul_sum := Filter.Tendsto.const_mul ((#S) : ℝ)⁻¹ lim_f_sum
      .
        have lim_f_g := tendsto_F g
        have lim_f_g_sub := Filter.Tendsto.sub lim_f_g lim_f_mul_sum

        have laplace_conv_tendsto_zero: Filter.Tendsto (fun n => eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤) Filter.atTop (nhds 0) := by
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => 0) (h := fun (n: ℕ) => ENNReal.ofReal ((2: ℝ) / ((seq n) + 1) : ℝ))
          . simp
          .
            rw [← ENNReal.tendsto_toReal_iff]
            conv =>
              arg 1
              intro n
              rw [ENNReal.toReal_ofReal (by
                norm_cast
                positivity
              )]
            conv =>
              arg 1
              intro n
              rhs
              equals ((((((seq n) + 1): ℕ)) : ℕ ) : ℝ) => simp
            conv =>
              arg 1
              equals (fun (n: ℕ) => (2 : ℝ) / (n) ) ∘ (fun n => (seq n) + 1) =>
                ext n
                simp
            apply Filter.Tendsto.comp
            .
              conv =>
                arg 1
                equals (fun (n: ℕ) => (2 : ℝ) / ((n) : ℕ)) =>
                  ext n
                  simp
              --rw [Filter.tendsto_add_atTop_iff_nat (f := fun n => (2 : ℝ) / (n))]
              apply tendsto_const_div_atTop_nhds_zero_nat
            .
              --apply Filter.tendsto_atTop_add_const_right (f := fun n => eps_seq (seq n))
              apply Filter.Tendsto.comp
              . conv =>
                  arg 1
                  equals fun n => n + 1 =>
                    simp
                apply Filter.tendsto_add_atTop_nat

              . simp
                exact h_seq
            . simp
            . simp
          . rw [Pi.le_def]
            intro x
            simp
          . rw [Pi.le_def]
            intro n
            simp
            have bound_by_norm_one := conv_laplce_norm (seq n)
            have norm_le_two_div := f_n_sub_conv  (seq n)
            nth_rw 1 [eLpNorm] at bound_by_norm_one
            simp at bound_by_norm_one
            grw [bound_by_norm_one]
            have h_norm := H_n_norm (seq n)
            simp [eLpNorm, eLpNorm'] at h_norm
            rw [h_norm]
            simp
            simp_rw [Laplace_b]
            simp [eLpNorm] at norm_le_two_div
            exact norm_le_two_div

        rw [← ENNReal.tendsto_toReal_iff] at laplace_conv_tendsto_zero

        have laplace_real_tendsto_zero: Filter.Tendsto (fun n => |(Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) (g))|) Filter.atTop (nhds 0)  := by
          apply squeeze_zero (g := fun n => (eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤ volume).toReal)
          .
            intro n
            simp
          . intro n
            have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) x‖ₑ) (μ := volume)
            simp [volume] at ae_le
            rw [my_haar_eq_count] at ae_le
            rw [count_ae_everywhere] at ae_le
            specialize ae_le g
            simp [eLpNorm, eLpNorm']
            simp [eLpNormEssSup]
            rw [← ENNReal.toReal_le_toReal] at ae_le
            simp only [toReal_enorm, Real.norm_eq_abs, OrderTop.bddAbove] at ae_le
            simp [volume]
            rw [my_haar_eq_count]
            exact ae_le
            . simp
            .
              -- TODO - deduplicate this
              have bound_by_norm_one := conv_laplce_norm (seq n) H_n
              have norm_le_two_div := f_n_sub_conv (seq n)
              nth_rw 1 [eLpNorm] at bound_by_norm_one
              simp at bound_by_norm_one
              have h_norm := H_n_norm (seq n)
              simp [eLpNorm, eLpNorm'] at h_norm
              rw [h_norm] at bound_by_norm_one
              simp only [eLpNormEssSup] at bound_by_norm_one
              simp [volume] at bound_by_norm_one
              rw [my_haar_eq_count] at bound_by_norm_one
              rw [← lt_top_iff_ne_top]
              grw [bound_by_norm_one]
              simp_rw [Laplace_b]
              simp [volume] at norm_le_two_div
              rw [my_haar_eq_count] at norm_le_two_div
              grw [norm_le_two_div]
              apply ENNReal.ofReal_lt_top
          . apply laplace_conv_tendsto_zero

        simp_rw [Laplace_b] at laplace_real_tendsto_zero
        simp_rw [f_conv_mu] at laplace_real_tendsto_zero
        beta_reduce at laplace_real_tendsto_zero
        conv at laplace_real_tendsto_zero =>
          arg 1
          rw [← Function.comp_def]
        rw [← tendsto_zero_iff_abs_tendsto_zero] at laplace_real_tendsto_zero
        --simp_rw [Function.comp_def] at lim_f_g_sub
        conv at laplace_real_tendsto_zero =>
          arg 1
          intro n
          simp

        conv at lim_f_g_sub =>
          arg 1
          intro n
          rw [← Finset.sum_subtype (s := S) (f := fun s => Conv (H_n (seq n)) (f_n (seq n)) (s * g)) (h := by
            intro s
            simp
          )]
        have lim_eq := tendsto_nhds_unique laplace_real_tendsto_zero lim_f_g_sub
        rw [eq_comm] at lim_eq
        rw [sub_eq_zero] at lim_eq
        rw [lim_eq]
        norm_cast
        rw [← Finset.sum_subtype (s := S) (f := fun i => (F (i * g)))]
        simp
        . intro n
          -- TODO - deduplicate this. I'm sure there's lots of other versions of it scattered around this file
          rw [← lt_top_iff_ne_top]
          grw [conv_laplce_norm]
          rw [H_n_norm]
          simp
          simp_rw [Laplace_b]
          grw [MeasureTheory.eLpNorm_sub_le]
          rw [f_n_norm_one]
          simp_rw [f_conv_mu]
          simp_rw [← smul_eq_mul]
          rw [← Pi.smul_def]
          rw [MeasureTheory.eLpNorm_const_smul]
          conv =>
            lhs
            rhs
            rhs
            arg 1
            equals ∑ x ∈ S, (fun g => f_n (seq n) (x • g)) =>
              funext g
              simp


          grw [MeasureTheory.eLpNorm_sum_le]
          simp_rw [← Function.comp_def]
          conv =>
            lhs
            rhs
            rhs
            arg 2
            intro x
            rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
              apply MeasureTheory.AEStronglyMeasurable.of_discrete
            ) (by
            exact {
              measurable := by
                apply Measurable.of_discrete
              map_eq := by
                simp [MeasureTheory.volume]
            }
          )]
          simp_rw [f_n_norm_one]
          simp
          field_simp
          norm_cast
          rw [Real.enorm_eq_ofReal_abs]
          simp
          norm_cast
          apply ENNReal.mul_lt_top
          . simp
          . simp
          .
            intro s hs
            apply AEStronglyMeasurable.of_discrete
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . simp




        . simp
      . intro s hs
        apply tendsto_F
  }
  exact F_lipschitzh

lemma counting_le_essSup (f: G → ℝ): ∀ g : G, ‖f g‖ₑ ≤ essSup  (fun g => ‖f g‖ₑ) volume := by
  intro g
  have ae_le := ENNReal.ae_le_essSup (fun g => ‖f g‖ₑ) (μ := volume)
  simp [MeasureTheory.volume] at ae_le
  rw [my_haar_eq_count] at ae_le
  rw [count_ae_everywhere] at ae_le
  specialize ae_le g
  simp
  simp [volume]
  rw [my_haar_eq_count]
  exact ae_le

lemma essSup_eq_elpNorm_top (f: G → ℝ): (essSup (fun g => ‖f g‖ₑ) volume) = (eLpNorm f ⊤ volume) := by
  rfl

lemma neg_smul (f: G → ℝ): -f = (-1 : ℝ) • f := by
  simp

-- lemma aeqfun_cast (f: G →ₘ[volume] ℝ):  := by
--   have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
--   rw [ae_eq_everywhere] at eq_fun
--   nth_rw 2 [← eq_fun]
--   rfl


-- TODO - cleanup and upstream to mathlib
lemma nat_mono_le {f: ℕ → ℕ} (hf: StrictMono f) (n: ℕ): n ≤ f n := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have k_le := hf (a := k) (b := k + 1) (by simp)
    have succ_le : k + 1 ≤ (f k) + 1 := by grind

    have succ_le_f: (f k) + 1 ≤ f (k + 1) := by
      have foo := hf.add_le_nat 1 k
      grind
    grind




noncomputable def Laplace_linear: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) →ₗ[ℝ] (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) := {
  toFun := Laplace
  map_add' := by
    intro x y
    simp [Laplace]
    simp [conv_mu_lp2]
    have coe_add := MeasureTheory.Lp.coeFn_add x y
    rw [ae_eq_everywhere] at coe_add
    norm_cast
    simp_rw [coe_add]
    conv =>
      pattern Conv _ _
      rw [conv_add_left (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      ) (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      )]

    rw [MeasureTheory.MemLp.toLp_add]
    . abel
    .
      have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 x)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
    . have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 y)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
  map_smul' := by
    intro c f
    simp [Laplace, conv_mu_lp2]
    have smul_ae := MeasureTheory.Lp.coeFn_smul c f
    rw [ae_eq_everywhere] at smul_ae
    simp_rw [smul_ae]
    simp_rw [conv_smul]
    rw [MeasureTheory.MemLp.toLp_const_smul]
    rw [smul_sub]
}


instance volume_finite_compact: IsFiniteMeasureOnCompacts (volume (α := G)) := by
  simp [volume]
  rw [my_haar_eq_count]
  exact {
    lt_top_of_isCompact := by
      intro k hk
      have finite := IsCompact.finite hk DiscreteTopology.isDiscrete
      exact Measure.count_apply_lt_top.mpr finite
  }



lemma finsupp_lp_top (f: G → ℝ) (hf: f.support.Finite) (p: ENNReal): MeasureTheory.MemLp f p (Measure.count) := by
  rw [← my_haar_eq_count]
  apply Continuous.memLp_of_hasCompactSupport
  . apply continuous_of_discreteTopology
  .
    simp [HasCompactSupport]
    rw [isCompact_iff_finite]
    simp [tsupport]
    exact hf





noncomputable def F_n (n : ℕ) := Real.sqrt ∘ (f_n  n)
noncomputable def F_n_lp2 (n : ℕ) := MeasureTheory.MemLp.toLp (F_n  n) (by
  simp [volume]
  rw [my_haar_eq_count]
  apply finsupp_lp_top
  simp [F_n]
  apply Set.Finite.subset (s := (f_n n).support)
  .
    unfold f_n
    apply f_n_fin_supp
  .
    apply Function.support_comp_subset
    simp
) (μ := volume (α := G)) (p := 2)


instance volume_mul_left_invariant: (volume (α := G)).IsMulLeftInvariant := by
  simp [volume]
  rw [my_haar_eq_count]
  infer_instance

instance volume_mul_right_invariant: (volume (α := G)).IsMulRightInvariant := by
  simp [volume]
  rw [my_haar_eq_count]
  infer_instance



-- TODO - upstream to mathlib
lemma abs_sub_le_abs_add (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): |a - b| ≤ |a + b| := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  .
    rw [le_abs]
    grind
  . rw [le_abs]
    grind

lemma norm_sub_squared_le (a b : ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): (a - b)^2 ≤ |a^2 - b^2| := by
  conv =>
    lhs
    rw [← sq_abs]
    rw [pow_two]

  rw [sq_sub_sq]
  rw [abs_mul]
  nth_rw 2 [mul_comm]
  have foo := abs_sub_le_abs_add a b ha hb
  -- TODO - why doesn't grw work here?
  apply mul_le_mul
  . simp
  . apply abs_sub_le_abs_add a b ha hb
  . simp
  . simp


def f_n_conv_delta_tendsto: Prop :=  ∀ s: S, Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0)



lemma f_conv_delta_helper (f: G → ℝ) (s: G): (Conv  f (delta s)) = fun g => f (s⁻¹ * g) := by
  funext g
  exact f_conv_delta f g s


-- Lemma 3.16 in Vikman

-- The case split statement in Vikman

lemma F_n_conv_mu_lim (f_n_limit: f_n_conv_delta_tendsto):
    Filter.Tendsto (fun n => ‖(F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n)‖ₑ) Filter.atTop (nhds 0) := by

  have f_n_sub_norm: ∀ s ∈ S, ∀ (i : ℕ), ∑' (g : G), ‖f_n i g - f_n i (s * g)‖ₑ ≠ ⊤ := by
    intro s hs n
    have foo := f_n_norm_one n
    rw [← lt_top_iff_ne_top]
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)] at foo
    rw [lintegral_g_eq_add] at foo
    simp at foo
    grw [ENNReal.tsum_le_tsum (g := fun g => ‖f_n n g‖ₑ + ‖(f_n n (s * g))‖ₑ)]
    .
      rw [ENNReal.tsum_add]
      rw [ENNReal.add_lt_top]
      . refine ⟨?_, ?_⟩
        . simp [foo]
        .
          grw [ENNReal.tsum_comp_le_tsum_of_injective (g := fun a =>  ‖f_n n a‖ₑ)]
          .
            simp [foo]
          . intro a b hab
            simpa using hab
    .
      intro a
      grw [enorm_sub_le]

  rw [← ENNReal.tendsto_toReal_iff]
  .
    have S_ne: (#S : ℝ) ≠ 0 := by
      simp
      have foo := hGS.hS
      simp at foo
      grind

    simp_rw [MeasureTheory.Lp.enorm_def]
    simp_rw [conv_mu_lp2, f_conv_mu]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    conv =>
      arg 1
      intro n
      arg 1
      arg 1
      lhs
      equals (1 / (#S : ℝ)) • ∑ s ∈ S, ↑↑(F_n_lp2 n) =>
        simp
        conv =>
          rhs
          equals ((#S : ℝ))⁻¹ • (#S : ℝ) • (F_n_lp2 n).val.cast =>
            norm_cast
            simp
        simp [S_ne]

    conv =>
      arg 1
      intro n
      arg 1
      arg 1
      rhs
      equals (1 / ↑(#S : ℝ)) • ∑ s ∈ S, (fun g => (F_n_lp2 n) (s * g)) =>
        ext a
        simp

    simp_rw [← smul_sub]
    simp_rw [← Finset.sum_sub_distrib]
    rw [ENNReal.toReal_zero]

    have f_n_norm := f_n_sub_conv

    apply squeeze_zero (g := fun n => (1 / ↑(#S : ℝ)) • ∑ x ∈ S, (eLpNorm ((F_n_lp2 n).val.cast - (fun (g: G) => (F_n_lp2 n) (x * g))) 2 volume).toReal)
    . simp
    .
      intro n
      rw [eLpNorm_const_smul]
      grw [eLpNorm_sum_le]
      .
        simp
        rw [ENNReal.toReal_sum]
        intro s hs
        rw [← lt_top_iff_ne_top]
        grw [eLpNorm_sub_le]
        .
          rw [ENNReal.add_lt_top]
          . refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              simp_rw [← Function.comp_def]
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . simp
      .
        apply ENNReal.mul_ne_top (by simp)
        rw [ENNReal.sum_ne_top]
        -- TODO - deduplicate this
        intro s hs
        rw [← lt_top_iff_ne_top]
        grw [eLpNorm_sub_le]
        .
          rw [ENNReal.add_lt_top]
          . refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              simp_rw [← Function.comp_def]
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . simp
      . intro s hs
        apply AEStronglyMeasurable.of_discrete
      . simp
    .
      conv =>
        rhs
        equals nhds ((1 / ↑(#S : ℝ)) • 0) =>
          simp

      apply Filter.Tendsto.const_smul
      conv =>
        rhs
        equals nhds (∑ x_1 ∈ S⁻¹, (0: ℝ)) =>
          simp
      conv =>
        arg 1
        intro x
        arg 1
        equals S⁻¹ =>
          apply S_eq_Sinv
      apply tendsto_finset_sum
      intro s hs
      conv =>
        arg 1
        intro n
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)]
        rw [lintegral_g_eq_add]

      simp
      apply squeeze_zero (g := (fun n ↦ ((∑' (g : G), ‖(f_n n) g - (f_n n) (s * g)‖ₑ) ^ (2 : ℝ)⁻¹).toReal))
      . simp
      .
        intro n
        rw [ENNReal.toReal_le_toReal]
        .
          apply ENNReal.rpow_le_rpow
          .
            apply ENNReal.tsum_le_tsum
            intro g
            rw [Real.enorm_eq_ofReal_abs]
            rw [Real.enorm_eq_ofReal_abs]
            rw [← ENNReal.ofReal_pow]
            .
              apply ENNReal.ofReal_le_ofReal
              simp [F_n_lp2]
              simp [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
              simp [F_n]
              conv =>
                rhs
                arg 1
                equals (Real.sqrt (f_n n g))^2 - (Real.sqrt (f_n n (s * g)))^2 =>
                  rw [Real.sq_sqrt]
                  .
                    rw [Real.sq_sqrt]
                    . apply f_n_nonneg
                  . apply f_n_nonneg

              apply norm_sub_squared_le
              . simp
              . simp
            . simp
          . simp
        .
          rw [← lt_top_iff_ne_top]
          have norm_sub_lt: eLpNorm (((F_n_lp2 n).val.cast) - ((F_n_lp2 n) ∘ fun a ↦ s * a)) 2 volume < ⊤ := by
            grw [eLpNorm_sub_le]
            rw [ENNReal.add_lt_top]
            refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
            . apply AEStronglyMeasurable.of_discrete
            . apply AEStronglyMeasurable.of_discrete
            . simp
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)] at norm_sub_lt
          rw [lintegral_g_eq_add] at norm_sub_lt
          simp at norm_sub_lt
          exact norm_sub_lt
        .
          apply ENNReal.rpow_ne_top_of_nonneg
          . simp
          . apply f_n_sub_norm s (by rw [S_eq_Sinv]; simp [hs])
      .
        unfold f_n_conv_delta_tendsto at f_n_limit
        simp at hs
        specialize f_n_limit ⟨s⁻¹, hs⟩
        conv at f_n_limit =>
          arg 1
          intro n
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)]
          rw [lintegral_g_eq_add]

        simp_rw [f_conv_delta_helper] at f_n_limit
        simp at f_n_limit
        conv =>
          rhs
          equals nhds (0 ^ (2 : ℝ)⁻¹) =>
            simp
        simp_rw [← ENNReal.toReal_rpow]
        apply Filter.Tendsto.rpow_const
        .
          rw [← ENNReal.tendsto_toReal_iff] at f_n_limit
          . exact f_n_limit
          .
            apply f_n_sub_norm s (by rw [S_eq_Sinv]; simp [hs])
          . simp
        . simp
  . intro n
    rw [MeasureTheory.Lp.enorm_def]
    apply MeasureTheory.Lp.eLpNorm_ne_top
  . simp

#print axioms F_n_conv_mu_lim

#synth TopologicalSpace ↥(Lp ℝ 2 volume (α := G))



lemma laplace_smul (k: ℝ) (f: (Lp ℝ 2 volume (α := G))): Laplace (k • f) = k • (Laplace f) := by
  simp [Laplace, conv_mu_lp2]
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
  simp_rw [conv_smul]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [smul_sub]


lemma norm_conv_mu_le  (f: (Lp ℝ 2 volume (α := G))): ‖conv_mu_lp2 f‖ ≤ ‖f‖ := by
  simp [conv_mu_lp2]
  simp [f_conv_mu]
  simp_rw [← smul_eq_mul]
  rw [← Pi.smul_def]
  rw [MeasureTheory.eLpNorm_const_smul]
  -- TODO - deduplicate this with 'laplace_bounded'
  conv =>
    lhs
    rhs
    rhs
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  have card_s_ne: (#S : ℝ) ≠ 0 := by
    simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

  grw [MeasureTheory.eLpNorm_sum_le]
  simp_rw [← Function.comp_def]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
      apply MeasureTheory.AEStronglyMeasurable.of_discrete
    ) (by
    exact {
      measurable := by
        apply Measurable.of_discrete
      map_eq := by
        simp [MeasureTheory.volume]
    }
  )]
  . simp
    field_simp
    rfl
  .
    apply WithTop.mul_ne_top
    .
      rw [Real.enorm_of_nonneg (by simp)]
      apply ENNReal.ofReal_ne_top
    .
      apply ENNReal.sum_ne_top.mpr
      intro s hs
      rw [← Function.comp_def]
      conv =>
        rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
          apply MeasureTheory.AEStronglyMeasurable.of_discrete
        ) (by
        exact {
          measurable := by
            apply Measurable.of_discrete
          map_eq := by
            simp [MeasureTheory.volume]
        }
      )]
      rw [← lt_top_iff_ne_top]
      apply (MeasureTheory.Lp.memLp f).2
  . intro s hs
    apply AEStronglyMeasurable.of_discrete
  .
    simp

open scoped RealInnerProductSpace
lemma inner_laplace_zero (f: (Lp ℝ 2 volume (α := G))) (hf: ⟪Laplace f, f⟫ = 0): Laplace f = 0 := by
  have inner_le := real_inner_le_norm (conv_mu_lp2 f) f

  by_cases norm_f_zero: ‖f‖ = 0
  .
    simp at norm_f_zero
    simp [Laplace, conv_mu_lp2]
    simp [f_conv_mu]
    simp_rw [norm_f_zero]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    simp
    simp_rw [← Pi.zero_def]
    rw [MeasureTheory.MemLp.toLp_zero]

  simp [Laplace] at hf
  rw [inner_sub_left] at hf
  rw [real_inner_self_eq_norm_sq] at hf
  rw [sub_eq_zero] at hf
  rw [eq_comm] at hf
  rw [pow_two] at hf
  --rw [inner_eq_norm_mul_iff_real] at hf
  rw [hf] at inner_le
  nth_rw 2 [mul_comm] at inner_le
  rw [mul_le_mul_iff_of_pos_left] at inner_le
  have conv_le_f := norm_conv_mu_le f
  have f_norm_eq: ‖f‖ = ‖conv_mu_lp2 f‖ := by
    linarith

  have f_sub_norm := norm_sub_sq_real f (conv_mu_lp2 f)
  rw [real_inner_comm] at f_sub_norm
  rw [hf] at f_sub_norm
  rw [← f_norm_eq] at f_sub_norm
  rw [← pow_two] at f_sub_norm
  group at f_sub_norm
  rw [zpow_two] at f_sub_norm
  rw [mul_self_eq_zero] at f_sub_norm
  simp at f_sub_norm
  simpa [Laplace] using f_sub_norm
  simpa using norm_f_zero


lemma F_n_norm_eq_one: ∀ n, MeasureTheory.eLpNorm (F_n n) 2 MeasureTheory.volume (α := G) = 1 := by
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add]
  simp [F_n, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow]

  intro n
  simp [f_n_nonneg]
  have norm_one := f_n_norm_one (n)
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add] at norm_one
  simp_rw [Real.enorm_eq_ofReal_abs] at norm_one
  simp [f_n_nonneg, abs_of_nonneg] at norm_one
  simp [norm_one]



lemma harmonic_abs_max_implies_const (f: G → ℝ) (hf: Laplace_b  f = 0) (a: G) (h_max: ∀ g: G, |f g| ≤ |f a|): f = fun _ => f a := by
  by_cases f_a_pos: 0 ≤ f a
  .
    have lt_f_a: ∀ g: G, f g ≤ f a := by
      intro g
      by_cases f_g_pos: 0 ≤ f g
      . specialize h_max g
        rw [abs_eq_self.mpr ?_] at h_max
        rw [abs_eq_self.mpr f_a_pos] at h_max
        . exact h_max
        . exact f_g_pos
      . linarith
    exact harmonic_maximum_implies_const f hf a lt_f_a
  .
    have f_neg_le: ∀ g, (-f) g ≤ (-f) a := by
      intro g
      simp at f_a_pos
      simp
      specialize h_max g
      rw [abs_of_neg f_a_pos] at h_max
      by_cases f_g_pos: 0 ≤ f g
      . rw [abs_of_nonneg f_g_pos] at h_max
        linarith
      . simp at f_g_pos
        rw [abs_of_neg f_g_pos] at h_max
        linarith
    have neg_const := harmonic_maximum_implies_const (-f) ?_ a f_neg_le
    .
      apply_fun (fun h => -h) at neg_const
      simp at neg_const
      rw [Pi.neg_def] at neg_const
      simpa using neg_const
    .
      simp_rw [Laplace_b]
      simp_rw [Laplace_b] at hf
      conv =>
        lhs
        rhs
        arg 1
        equals (-1 : ℝ) • f =>
          simp
      rw [conv_smul]
      simp
      rw [add_comm]
      rw [← sub_eq_add_neg]
      rw [sub_eq_zero]
      rw [sub_eq_zero] at hf
      exact hf.symm


set_option maxHeartbeats 500000 in
lemma laplace_zero_iff_zero (g: (Lp ℝ 2 volume (α := G))) (eq_zero: Laplace g = 0): g = 0 := by
  by_cases g_has_maximum: ∃ a: G, ∀ b: G, ‖g b‖ ≤ ‖g a‖
  .
    obtain ⟨a, ha⟩ := g_has_maximum
    have laplace_b_zero: Laplace_b  g = 0 := by
      simp [Laplace, conv_mu_lp2, f_conv_mu] at eq_zero
      simp_rw [Laplace_b, f_conv_mu]
      apply_fun (fun f => f.val.cast) at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at eq_zero
      field_simp at eq_zero
      field_simp
      exact eq_zero

    simp [Laplace_b] at laplace_b_zero
    simp [f_conv_mu] at laplace_b_zero
    rw [sub_eq_zero] at laplace_b_zero

    have g_const := harmonic_abs_max_implies_const g (by
      simp [Laplace_b]
      simp [f_conv_mu]
      nth_rw 1 [laplace_b_zero]
      simp
    ) a (by simpa using ha)
    have new_g_const_zero := MeasureTheory.memLp_const_iff_enorm (p := 2) (by simp) (by simp) (c := g a) (μ := volume (α := G)) (by simp)
    rw [← g_const] at new_g_const_zero
    simp [MeasureTheory.Lp.memLp] at new_g_const_zero
    simp [volume, my_haar_eq_count] at new_g_const_zero
    have g_infinity := hGS.g_infinite
    rw [← not_infinite_iff_finite] at new_g_const_zero
    simp [hGS.g_infinite] at new_g_const_zero


    have g_eq_zero: g.val.cast = 0 := by
      rw [g_const]
      rw [new_g_const_zero]
      ext a
      simp

    ext
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    exact g_eq_zero
  . rename _ => g_no_maximum
    simp at g_no_maximum
    have integrable_g := MeasureTheory.MemLp.integrable_sq (MeasureTheory.Lp.memLp g)
    simp [Integrable, HasFiniteIntegral] at integrable_g
    obtain ⟨_, integral_lt⟩ := integrable_g
    rw [lintegral_g_eq_add] at integral_lt
    rw [lt_top_iff_ne_top] at integral_lt
    by_contra g_ne_zero
    simp at g_ne_zero
    have nonzero_val: ∃ a: G, g a ≠ 0 := by
      rw [MeasureTheory.Lp.ext_iff] at g_ne_zero
      rw [ae_eq_everywhere] at g_ne_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at g_ne_zero
      exact Function.ne_iff.mp g_ne_zero

    obtain ⟨a, ha⟩ := nonzero_val
    have finite_gt := ENNReal.finite_const_le_of_tsum_ne_top integral_lt (ε := ‖|g a|‖ₑ ^ 2) (by
      simpa using ha
    )
    have maximal := Set.Finite.exists_maximalFor (f := fun h => |g h|) _ finite_gt (by
      apply Set.nonempty_of_mem (x := a)
      simp
    )
    obtain ⟨m, m_in_g, hm⟩ := maximal
    simp at m_in_g
    -- Obtain an element greater than the maximum
    obtain ⟨p, hp⟩ := g_no_maximum m
    have p_gt := hm (j := p) ?_ ?_
    .
      have not_g_le := not_lt_of_ge p_gt
      contradiction
    .
      simp
      grw [m_in_g]
      rw [← ENNReal.toReal_le_toReal]
      .
        simp
        rw [sq_le_sq]
        linarith
      . simp
      . simp
    linarith


-- Proposition 3.17.1: "∆ is bounded" from Vikman
-- The paper also proves that the Laplace operator is self-adjoint as part of this step,
-- but we split it out
lemma laplace_bounded (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ₑ ≤ 2 * ‖f‖ₑ := by
  unfold Laplace
  unfold conv_mu_lp2
  simp_rw [f_conv_mu]
  grw [enorm_sub_le]
  --grw [norm_sub_le]
  --grw [norm_add_le]
  --grw [MeasureTheory.eLpNorm_sub_le]
  simp_rw [← smul_eq_mul]
  simp_rw [← Pi.smul_def]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [enorm_smul]
  --rw [MeasureTheory.eLpNorm_const_smul]
  conv =>
    lhs
    rhs
    rhs
    arg 1
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  rw [MeasureTheory.Lp.enorm_toLp]
  grw [MeasureTheory.eLpNorm_sum_le]
  simp_rw [← Function.comp_def]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
      apply MeasureTheory.AEStronglyMeasurable.of_discrete
    ) (by
    exact {
      measurable := by
        apply Measurable.of_discrete
      map_eq := by
        simp [MeasureTheory.volume]
    }
  )]
  simp
  rw [Real.enorm_of_nonneg (by simp)]
  rw [← mul_assoc]
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul]
  field_simp
  rw [div_self (by
    have foo := hS
    simp at foo
    simp
    exact Finset.nonempty_iff_ne_empty.mp foo
  )]
  simp
  rw [two_mul]
  . rw [← MeasureTheory.Lp.enorm_def]
  -- TODO - inline these in the right places
  . simp
  .
    intro i hs
    apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . norm_num
  .
    apply MeasureTheory.memLp_finsetSum
    intro s hs
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      apply MeasureTheory.Lp.memLp f
    . apply AEMeasurable.of_discrete



lemma laplace_bounded' (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ ≤ 2 * ‖f‖ := by
  have bounded := laplace_bounded f
  rw [← ofReal_norm_eq_enorm] at bounded
  rw [← ofReal_norm_eq_enorm] at bounded
  simp_rw [← ENNReal.ofReal_ofNat] at bounded
  rw [← ENNReal.ofReal_mul] at bounded
  .
    rw [ENNReal.ofReal_le_ofReal_iff] at bounded
    . exact bounded
    . simp
  . simp

lemma laplace_spectrum_contains_zero (f_n_limit: f_n_conv_delta_tendsto): 0 ∈ spectrum ℝ (Laplace_linear ) := by
  rw [spectrum.zero_mem_iff]
  by_contra this
  obtain ⟨f, hf⟩ := this
  -- Copied from https://github.com/leanprover-community/mathlib4/blob/60041760fb96850991084120a9a9b217890cf1f1/Mathlib/Topology/Algebra/Module/Equiv.lean#L760
  let laplace_equiv: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) ≃ₗ[ℝ] (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) := {
      toFun := f.val
      map_add' := by simp
      map_smul' := by simp
      invFun := f.inv
      left_inv := fun x =>
        show (f.inv * f.val) x = x by
          rw [f.inv_val]
          simp
      right_inv := fun x =>
        show (f.val * f.inv) x = x by
          rw [f.val_inv]
          simp
      }
  have laplace_cont := continuous_of_linear_of_bound (C := 2) (𝕜 := ℝ ) (f := f.val) ?_ ?_ ?_
  let cont_equiv :=  LinearEquiv.toContinuousLinearEquivOfContinuous laplace_equiv laplace_cont

  have inv_bounded := ContinuousLinearMap.isBoundedLinearMap (𝕜 := ℝ) (cont_equiv.symm.toContinuousLinearMap)

  have nontrival_lp : Nontrivial ↥(Lp ℝ 2 (volume (α := G))) := by
    rw [nontrivial_iff]
    use 0
    use MemLp.toLp (Pi.single 1 1) (by
      apply Continuous.memLp_of_hasCompactSupport
      . apply continuous_of_discreteTopology
      . simp [HasCompactSupport, tsupport]
    )
    simp
    rw [MeasureTheory.Lp.ext_iff]
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    conv =>
      arg 1
      lhs
      equals 0 =>
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    by_contra!
    apply_fun (fun f => f 1) at this
    simp at this


  have norm_mul_bound := ContinuousLinearEquiv.one_le_norm_mul_norm_symm cont_equiv



  have inv_norm_ge (n: ℕ) : (1 : ENNReal) / (eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G))) ≤ ENNReal.ofReal ‖cont_equiv.symm.toContinuousLinearMap‖ := by

    calc
    _ = (eLpNorm (F_n n) 2 (μ := volume (α := G))) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      rw [F_n_norm_eq_one]
    _ = (eLpNorm (cont_equiv.symm.toFun (cont_equiv.toFun (F_n_lp2 n))) 2) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      simp [F_n_lp2]
      rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    _ ≤ ENNReal.ofReal ‖cont_equiv.symm.toContinuousLinearMap‖ := by
      have other := ContinuousLinearMap.ratio_le_opNorm (f := cont_equiv.symm.toContinuousLinearMap) (x := (((F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n))))
      conv at other =>
        lhs
        rw [Lp.norm_def]
        --rw [ContinuousLinearMap.map_sub]
        --rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]



      conv =>
        lhs
        arg 1
        arg 1
        rhs
        rhs
        rhs
        simp [cont_equiv, laplace_equiv]
        simp [hf, Laplace_linear]
      simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, Laplace]
      apply_fun ENNReal.ofReal at other
      -- TODO - consider removing @[simp] from 'AddSubgroupClass.coe_sub'
      simp only [ContinuousLinearEquiv.coe_coe, map_sub, ofReal_norm] at other
      simp only [F_n_lp2, Laplace_b, conv_mu_lp2]
      simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
      by_cases norm_f_eq_zero: ‖F_n_lp2 n - conv_mu_lp2 (F_n_lp2 n)‖ = 0
      . rw [norm_eq_zero] at norm_f_eq_zero
        have foo := laplace_zero_iff_zero (F_n_lp2 n) (by
          simp [Laplace]
          exact norm_f_eq_zero
        )
        simp [F_n_lp2] at foo
        apply_fun (fun f => (f: (G → ℝ))) at foo
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at foo
        conv at foo =>
          rhs
          equals 0 =>
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
        simp [foo]
        unfold Conv
        conv =>
          lhs
          pattern MemLp.toLp _ _
          equals 0 =>
            conv =>
              arg 1
              arg 1
              equals 0 =>
                exact MeasureTheory.zero_convolution (G := Additive G)
            simp
        simp
        conv =>
          arg 1
          arg 1
          arg 1
          equals 0 =>
            rw [ae_eq_everywhere.mp (MeasureTheory.AEEqFun.coeFn_zero)]
        simp
      rw [ENNReal.ofReal_div_of_pos] at other
      .
        simp only [ofReal_norm, Lp.enorm_def] at other
        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
        simp only [F_n_lp2, conv_mu_lp2] at other
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
        rw [ENNReal.ofReal_toReal] at other
        .
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
          simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
          exact other
        .
          rw [← ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          apply MeasureTheory.Lp.eLpNorm_ne_top
      . simpa using norm_f_eq_zero
      . exact ENNReal.ofReal_mono
  .
    rw [isBoundedLinearMap_iff] at inv_bounded
    obtain ⟨M, M_pos, le_M⟩ := inv_bounded.2

    have foo := F_n_conv_mu_lim f_n_limit
    rw [ENNReal.tendsto_atTop_zero] at foo
    obtain ⟨n, hn⟩ := foo  ((1: ENNReal) /(2 * ‖cont_equiv.symm.toContinuousLinearMap‖ₑ)) (by
      simp
      rw [ENNReal.mul_eq_top]
      simp
    )
    specialize hn n (by simp)

    rw [Lp.enorm_def] at hn
    specialize inv_norm_ge n
    simp [Laplace_b] at inv_norm_ge
    rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at hn
    simp only [F_n_lp2, conv_mu_lp2] at hn
    simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at hn
    grw [hn] at inv_norm_ge
    simp at inv_norm_ge

    have norm_nonzero :‖cont_equiv.symm.toContinuousLinearMap‖ ≠ 0 := by
      by_contra!
      simp [this] at norm_mul_bound
      norm_num at norm_mul_bound

    simp [enorm] at inv_norm_ge
    norm_cast at inv_norm_ge
    rw [two_mul] at inv_norm_ge
    simp at inv_norm_ge
    apply_fun norm at inv_norm_ge
    rw [inv_norm_ge] at norm_nonzero
    simp at norm_nonzero
  . simp
  . simp
  . intro x
    rw [hf]
    apply laplace_bounded'




lemma laplace_g_n (n: ℕ) (hn: 0 < n): ∃ g: (Lp ℝ 2 volume (α := G)), ‖Laplace g‖ ≤ (1 : ℝ) / n ∧ ⟪Laplace g, g⟫ = 1 := by

  let eps := (1: ℝ) / n
  -- selfAdjoint.mem_spectrum_eq_re

  let P: Polynomial ℝ := (Polynomial.X^2 - eps • Polynomial.X)

  have spec_inter: spectrum ℝ (Polynomial.aeval Laplace_linear P) ∩ Set.Ioo 0 eps ≠ ∅ := by
    by_contra!
    have zero_isolated: spectrum ℝ (Polynomial.aeval Laplace_linear P) ∩ (Set.Ico 0 eps) = {0} := by
      ext a
      simp
      refine ⟨?_, ?_⟩
      . sorry
      .
        intro ha
        sorry
    sorry


  have mem_spec: eps ∈ spectrum ℝ (Polynomial.aeval Laplace_linear P) := by
    apply spectrum.subset_polynomial_aeval
    simp
    simp_rw [spectrum.mem_iff]
    sorry



  sorry
  -- This whole proof is completely wrong - it needs to use the spectral theorem

  -- have ball_open: IsOpen (Metric.ball (0 : Lp ℝ 2 volume (α := G)) (1 / n)) := by
  --   exact Metric.isOpen_ball


  -- have punctured_ball_open: IsOpen ((Metric.ball (0 : Lp ℝ 2 volume (α := G)) (1 / n)) \ {0})  := by
  --   apply IsOpen.sdiff
  --   . exact ball_open
  --   .
  --     rw [← Metric.closedBall_zero]
  --     apply Metric.isClosed_closedBall

  -- have dense := laplace_range_dense
  -- rw [dense_iff_inter_open] at dense

  -- let lp_point: (Lp ℝ 2 volume (α := G)) := MemLp.toLp (fun (g: G) => if g = 1 then (1 : ℝ) / ((n + 1)^2) else 0) (by
  --   simp [MemLp]
  --   refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
  --   simp [eLpNorm, eLpNorm']
  --   rw [lintegral_g_eq_add]
  --   rw [tsum_eq_sum (s := {1})]
  --   . simp
  --     rw [Real.enorm_eq_ofReal_abs]
  --     norm_cast
  --     simp
  --     apply ENNReal.rpow_lt_top_of_nonneg
  --     . simp
  --     .
  --       apply ENNReal.pow_ne_top
  --       apply ENNReal.ofReal_ne_top
  --   . intro b hb
  --     simp at hb
  --     simp [hb]
  -- )

  -- have lp_point_norm: ‖lp_point‖ < (n: ℝ)⁻¹ := by
  --   simp [lp_point, eLpNorm, eLpNorm']
  --   rw [lintegral_g_eq_add]
  --   simp_rw [Real.enorm_eq_ofReal_abs]
  --   conv =>
  --     lhs
  --     arg 1
  --     lhs
  --     arg 1
  --     intro g
  --     rw [← ENNReal.ofReal_pow (by simp)]
  --   rw [tsum_eq_sum (s := {1})]
  --   .
  --     simp
  --     rw [ENNReal.ofReal_rpow_of_nonneg]
  --     rw [ENNReal.toReal_ofReal]
  --     .
  --       rw [← Real.rpow_neg_one]
  --       rw [← Real.rpow_mul]
  --       rw [← Real.rpow_natCast]
  --       rw [← Real.rpow_mul]
  --       rw [← Real.rpow_natCast]
  --       rw [← Real.rpow_mul]
  --       field_simp
  --       simp
  --       rw [Real.rpow_neg]
  --       rw [mul_inv_lt_iff₀']
  --       field_simp
  --       norm_cast
  --       rw [pow_two]
  --       ring
  --       norm_cast
  --       rw [mul_two]
  --       . omega
  --       .
  --         norm_cast
  --         positivity
  --       . norm_cast
  --         omega
  --       . norm_cast
  --         linarith
  --       . norm_cast
  --         positivity
  --       . norm_cast
  --         positivity
  --     . positivity
  --     . positivity
  --     . simp
  --   . intro b hb
  --     simp at hb
  --     simp [hb]

  -- use (Real.sqrt ⟪Laplace lp_point, lp_point⟫)⁻¹ • lp_point
  -- refine ⟨?_, ?_⟩
  -- .
  --   rw [laplace_smul]
  --   rw [norm_smul]
  --   simp only [norm_inv, Real.norm_eq_abs, one_div]
  --   grw [laplace_bounded']
  --   grw [lp_point_norm]
  --   rw [inv_mul_le_iff₀]
  --   .
  --     rw [← Real.norm_eq_abs]
  --     rw [Real.norm_of_nonneg (by apply Real.sqrt_nonneg)]
  --     simp_rw [Laplace]
  --     simp_rw [inner_sub_left, conv_mu_lp2]
  --     simp_rw [f_conv_mu]
  --     s orry
  --     --grw [real_inner_le_norm]
  --   . s orry


  -- -- Show that the punctured open ball is nonempty, so a dense set has a nonempty intersection with it
  -- have mem_ball := dense _ punctured_ball_open (by
  --   simp
  --   use lp_point
  --   simp
  --   refine ⟨?_, ?_⟩
  --   . simp [lp_point, eLpNorm, eLpNorm']
  --     rw [lintegral_g_eq_add]
  --     simp_rw [Real.enorm_eq_ofReal_abs]
  --     conv =>
  --       lhs
  --       arg 1
  --       lhs
  --       arg 1
  --       intro g
  --       rw [← ENNReal.ofReal_pow (by simp)]
  --     rw [tsum_eq_sum (s := {1})]
  --     .
  --       simp
  --       rw [ENNReal.ofReal_rpow_of_nonneg]
  --       rw [ENNReal.toReal_ofReal]
  --       .
  --         rw [← Real.rpow_neg_one]
  --         rw [← Real.rpow_mul]
  --         rw [← Real.rpow_natCast]
  --         rw [← Real.rpow_mul]
  --         rw [← Real.rpow_natCast]
  --         rw [← Real.rpow_mul]
  --         field_simp
  --         simp
  --         rw [Real.rpow_neg]
  --         rw [mul_inv_lt_iff₀']
  --         norm_num
  --         norm_cast
  --         rw [pow_two]
  --         ring
  --         norm_cast
  --         rw [mul_two]
  --         . omega
  --         .
  --           norm_cast
  --           positivity
  --         . norm_cast
  --           simp
  --         . norm_cast
  --           linarith
  --         . norm_cast
  --           positivity
  --         . norm_cast
  --           positivity
  --       . positivity
  --       . positivity
  --       . simp
  --     . intro b hb
  --       simp at hb
  --       simp [hb]
  --   . by_contra!
  --     rw [MeasureTheory.Lp.ext_iff] at this
  --     rw [ae_eq_everywhere] at this
  --     have eval_one := congrFun this (1 : G)
  --     rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at eval_one
  --     rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at eval_one
  --     simp at eval_one
  --     linarith
  -- )
  -- simp only [Set.Nonempty] at mem_ball
  -- obtain ⟨g, gh⟩ := mem_ball
  -- simp at gh
  -- have g_norm := gh.1
  -- have g_range := gh.2
  -- simp only [laplace_range] at g_range
  -- simp only [LinearMap.mem_range] at g_range
  -- obtain ⟨a, ha⟩ := g_range
  -- s orry

  -- by_cases inner_laplace_nonneg: 0 ≤ ⟪Laplace a, a⟫
  -- .
  --   --use (Real.sqrt ⟪Laplace a, a⟫)⁻¹ • a
  --   --simp [Laplace_linear] at ha
  --   field_simp at g_norm
  --   refine ⟨?_, ?_⟩
  --   .
  --     rw [laplace_smul]
  --     rw [norm_smul]
  --     simp
  --     rw [norm_eq_sqrt_real_inner]
  --     rw [ha]
  --     rw [← norm_eq_sqrt_real_inner]

  --     simp
  --     rw [inner_smul_left]
  --     rw [inner_smul_right]
  --     field_simp
  --     simp [Laplace]
  --   .
  --     rw [laplace_smul]
  --     rw [inner_smul_left]
  --     rw [inner_smul_right]
  --     field_simp
  --     apply div_self
  --     rw [Real.sqrt_ne_zero]
  --     . by_contra!
  --       apply inner_laplace_zero at this
  --       rw [this] at ha
  --       have g_nonzero := g_norm.2
  --       rw [eq_comm] at ha
  --       contradiction
  --     . exact inner_laplace_nonneg
  -- . s orry


#print axioms laplace_g_n




lemma measure_preserving_inv: MeasurePreserving Inv.inv ((MeasureTheory.volume (α := G))) (MeasureTheory.volume (α := G)) := {
  measurable := by
    exact measurable_inv
  map_eq := by
    simp [volume]
    simp [my_haar_eq_count]
}


lemma measure_preserving_unop_tomul: MeasurePreserving (fun (x: Additive (G)) ↦ (Additive.toMul x)) myHaarAddOpp volume := by
  apply MeasureTheory.MeasurePreserving.id

lemma measure_preserving_op_add: MeasurePreserving (fun (x: G) ↦ Additive.ofMul (x)) volume myHaarAddOpp := by
  apply MeasureTheory.MeasurePreserving.id





noncomputable def G_n (n: ℕ) (hn: 0 < n) := Classical.choose (laplace_g_n n hn )


lemma lp_summable {p: ℕ} (hp: 0 < p) (f: (Lp ℝ p volume (α := G))): Summable (fun g: G => |(f g)|^p) := by
  have f_norm := (MeasureTheory.Lp.memLp f).2
  simp [eLpNorm, eLpNorm'] at f_norm
  have not_le: ¬(p = 0) := by linarith
  simp [not_le] at f_norm
  rw [lintegral_g_eq_add] at f_norm
  rw [lt_top_iff_ne_top] at f_norm
  rw [Ne] at f_norm
  rw [ENNReal.rpow_eq_top_iff] at f_norm
  simp at f_norm
  have not_ofreal: ¬((ENNReal.ofReal p).toReal ≤ 0) := by
    simp
    linarith
  simp [not_le] at f_norm
  simp_rw [Real.enorm_eq_ofReal_abs] at f_norm
  conv at f_norm =>
    arg 1
    lhs
    arg 1
    intro g
    rw [← ENNReal.ofReal_pow (by simp)]
  apply ENNReal.summable_toReal at f_norm
  conv at f_norm =>
    arg 1
    intro x
    rw [ENNReal.toReal_ofReal (by
      simp
    )]
  exact f_norm

lemma lp2_summable (f: (Lp ℝ 2 volume (α := G))): Summable (fun g: G => (f g)^2) := by
  conv =>
    arg 1
    intro g
    rw [← sq_abs]
  apply lp_summable (p := 2) (by simp) f


lemma summable_f_mul_translate (f: (Lp ℝ 2 volume (α := G))) (i: G): Summable (fun x => (f x) * (f (i * x))) := by
  have lp_mul := (MeasureTheory.MemLp.mul (φ := f) (f := fun x => f (i * x)) (p := 2) (q := 2) (r := 1) (μ := volume) ?_ ?_).2
  .
    simp [MemLp, eLpNorm, eLpNorm'] at lp_mul
    rw [lintegral_g_eq_add] at lp_mul
    simp [Real.enorm_eq_ofReal_abs] at lp_mul
    simp [← ENNReal.ofReal_mul] at lp_mul
    rw [lt_top_iff_ne_top] at lp_mul
    apply ENNReal.summable_toReal at lp_mul
    conv at lp_mul =>
      arg 1
      intro x
      rw [ENNReal.toReal_ofReal (by
        apply mul_nonneg
        . simp
        . simp
      )]
    apply Summable.of_abs
    simp_rw [abs_mul]
    exact lp_mul
  .
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume i
  . apply Lp.memLp f


-- Note - this is stated incorrectly in Vikman
-- The RHS should have a squared norm
set_option maxRecDepth 40000 in
lemma proposition_3_18 (f: (Lp ℝ 2 volume (α := G))): (∑' g: G, (f g) * (Laplace f) g) = ((2) * (#(S) : ℝ))⁻¹ * ∑ s ∈ S, ‖(f - (conv_finsupp_lp2 f (delta s) (by simp [delta])))‖^2 := by
  simp_rw [Laplace]
  simp_rw [conv_mu_lp2]
  simp_rw [f_conv_mu]
  conv =>
    enter [1, 1, g, 2, 1, 1, 2, 1, g, 2, 2, s]
    rw[ ← inv_inv s]
    rw [← f_conv_delta (s := s⁻¹) (f := f.val.cast)]

  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
  simp only [Pi.sub_apply]
  conv =>
    lhs
    arg 1
    intro g
    lhs
    rw [← inv_mul_cancel_left₀ (a := 2) (by simp) (f g)]



  simp_rw [mul_assoc]
  rw [Summable.tsum_mul_left]
  simp_rw [← mul_assoc]

  conv =>
    lhs
    rhs
    arg 1
    intro g
    rw [mul_sub]
  rw [Summable.tsum_sub]
  have sum_f: ∀ c: ℝ, c = (#(S) : ℝ)⁻¹ * ∑ s ∈ S, c := by
    intro g
    simp
    have card_nonneg: #(S) ≠ 0 := by
      exact Finset.card_ne_zero.mpr S_nonempty
    field_simp
  conv =>
    lhs
    rhs
    lhs
    arg 1
    intro g
    rw [mul_assoc]
    rw [← pow_two]
    rw [sum_f (c := (f g)^2)]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_mul_left]
  have f_norm := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := 2) (by simp) (by simp) (f := f.val.cast) (μ := volume (α := G))
  simp_rw [lintegral_g_eq_add] at f_norm
  simp [enorm] at f_norm
  apply_fun ENNReal.toReal at f_norm
  norm_cast at f_norm
  rw [← ENNReal.toReal_rpow] at f_norm
  rw [ENNReal.tsum_toReal_eq] at f_norm
  simp at f_norm
  apply_fun (fun x => x^2) at f_norm
  nth_rw 2 [← Real.rpow_natCast] at f_norm
  rw [← Real.rpow_mul] at f_norm
  simp at f_norm
  have f_summable := lp_summable (p := 2) (by simp) f
  conv =>
    lhs
    rhs
    lhs
    rhs
    rhs
    rw [Summable.tsum_finsetSum (by
      intro i hi
      apply lp2_summable
    )]
    rw [← f_norm]

  conv =>
    lhs
    rhs
    rhs
    arg 1
    intro b
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    rw [← mul_assoc]
    rw [mul_comm (2 * _)]
    rw [mul_assoc]
    rw [mul_assoc]
    rw [Finset.mul_sum]
    rw [← mul_assoc]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_finsetSum (by
    intro i hi
    simp [f_conv_delta]
    apply summable_f_mul_translate
  )]
  simp_rw [f_conv_delta]
  simp only [inv_inv]
  let f_conv := fun (s: G) => conv_finsupp_lp2 f (delta s) (by
    simp [delta]
  )
  have real_inner : ∀ a b : ℝ, ⟪a, b⟫ = a * b := fun a b => by rw [show (⟪a, b⟫ : ℝ) = b * a from rfl, mul_comm]
  have inner_f_conv := fun (s: G) => MeasureTheory.L2.inner_def (𝕜 := ℝ) (f := f) (g := f_conv s)
  simp [f_conv, conv_finsupp_lp2] at inner_f_conv
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at inner_f_conv
  conv at inner_f_conv =>
    intro a
    rhs
    -- TODO  - deduplicate this with the 'have lp_mul' block above
    rw [MeasureTheory.integral_countable (by
      simp [f_conv_delta]
      simp [Integrable]
      refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
      simp [HasFiniteIntegral]
      simp [Real.enorm_eq_ofReal_abs]
      rw [lintegral_g_eq_add]
      rw [lt_top_iff_ne_top]
      simp_rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul]
      rw [← ENNReal.ofReal_tsum_of_nonneg]
      . apply ENNReal.ofReal_ne_top
      . intro n
        positivity
      .
        apply Summable.abs
        simp_rw [mul_comm]
        apply summable_f_mul_translate
    )]
  simp [volume, my_haar_eq_count, f_conv_delta] at inner_f_conv
  conv =>
    lhs
    rhs
    rhs
    rhs
    arg 1
    rw [S_eq_Sinv ]

  simp only [Finset.sum_inv_index]

  simp_rw [mul_comm] at inner_f_conv
  simp_rw [← inner_f_conv]
  -- Split '2 * ‖f‖^2 into two copies of ‖f‖^2, and convert one into ‖Conv f delta‖^2
  rw [two_mul]
  conv =>
    lhs
    rhs
    lhs
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.eLpNorm_comp_measurePreserving (f := fun x => s⁻¹ * x) (ν := volume) (by apply AEStronglyMeasurable.of_discrete) (by apply measurePreserving_mul_left)]
    -- TODO - why does doing this result in a weird metavariable outside of conv?
    --pattern _ ∘ _
    --equals fun g => f (s⁻¹ * g) =>
    --  funext a
    --  simp



  simp_rw [Function.comp_def]
  simp_rw [← f_conv_delta]
  have card_s_ne: #(S) ≠ 0 := by
    simp
    exact Finset.nonempty_iff_ne_empty.mp S_nonempty
  simp_rw [norm_sub_sq_real]
  simp only [MeasureTheory.Lp.norm_def]
  simp_rw [conv_finsupp_lp2]
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  eta_reduce
  ring
  . apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    apply summable_f_mul_translate
  .
    apply tsum_nonneg
    intro g
    apply sq_nonneg
  . simp
  . apply summable_sum
    intro s hs
    apply lp2_summable
  .
    apply Summable.mul_left
    apply summable_sum
    intro s hs
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    simp_rw [← pow_two]
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [← mul_assoc]
    simp_rw [Finset.mul_sum]
    apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    simp_rw [mul_comm]
    simp_rw [mul_assoc]
    apply Summable.mul_left
    apply summable_f_mul_translate
  .
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [mul_sub]
    apply Summable.sub
    . simp_rw [← pow_two]
      apply lp2_summable
    .
      simp_rw [← mul_assoc]
      simp_rw [Finset.mul_sum]
      apply summable_sum
      intro s hs
      simp_rw [f_conv_delta]
      simp_rw [mul_comm]
      simp_rw [mul_assoc]
      apply Summable.mul_left
      apply summable_f_mul_translate

lemma g_n_laplace_enorm_le (n: ℕ) (hn: 0 < n): ‖Laplace (G_n n hn)‖ₑ ≤ 1/n := by
  have g_n_prop := (laplace_g_n n hn).choose_spec
  sorry

lemma g_n_laplace_norm_le (n: ℕ) (hn: 0 < n): ‖Laplace (G_n n hn)‖ ≤ 1/n := by
  have g_n_prop := (laplace_g_n n hn).choose_spec
  exact g_n_prop.1

open scoped RealInnerProductSpace in
lemma g_n_conv_norm (n: ℕ) (hn: 0 < n): ⟪Laplace (G_n n hn), (G_n n hn)⟫ = 1 := by
  have g_n_prop := (laplace_g_n n hn).choose_spec
  exact g_n_prop.2

lemma g_n_ne_zero (n: ℕ) (hn: 0 < n): G_n n hn ≠ 0 := by
  simp
  by_contra!
  have g_n_prop := (laplace_g_n n hn).choose_spec
  simp [G_n] at this
  simp [this] at g_n_prop



noncomputable def laplace_range := LinearMap.range (Laplace_linear )



-- The only measure-zero sets are empty sets, so we can evaluate a MemLp function by evaluating any function
-- from the equivalence class
lemma tolp_apply (f: G → ℝ) {p: ENNReal}  (hf: MeasureTheory.MemLp f p) (g: G): (MeasureTheory.MemLp.toLp f hf) g = f g := by
  have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
  rw [ae_eq_everywhere] at eq_fun
  nth_rw 2 [← eq_fun]
  rfl

lemma tolp_val_apply (f: G → ℝ) {p: ENNReal}  (hf: MeasureTheory.MemLp f p) (g: G): (MeasureTheory.MemLp.toLp f hf).val g = f g := by
  have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
  rw [ae_eq_everywhere] at eq_fun
  nth_rw 2 [← eq_fun]
  rfl

--lemma lp_apply (f: Lp ℝ 2 (μ := volume (α := G)):


-- Note - this might only true because our measure is equivalen to the counting measure,
-- so a.e. is the same thing as everywhere.
lemma lp_finset_sum {R: Finset G} (f: G → (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))) (g: G): (∑ s ∈ R, (f s) g) = ((∑ s ∈ R, f s) : (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))) g := by
  -- have foo := Finset.sum_induction (p := fun (m: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))) => m g = (∑ s ∈ S, f s g)) (s := S)
  rw [eq_comm]
  refine Finset.induction_on R ?_ ?_
  .
    simp only [Finset.sum_empty]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    simp
  .
    intro a s ha sum_eq
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    rw [← sum_eq]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_add _ _)]
    simp



open scoped RealInnerProductSpace
lemma laplace_self_adjoint (f h: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): ⟪f, (Laplace  h)⟫ = ⟪(Laplace  f), h⟫ := by

  simp [MeasureTheory.L2.inner_def]

  have my_eq := ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub h (conv_mu_lp2 h))

  --simp only [AddSubgroupClass.coe_sub, ae_eq_everywhere] at my_eq

  -- MeasureTheory.Lp.coeFn_smul

  conv =>
    lhs
    arg 2
    intro g
    rw [mul_comm]
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    simp
    rw [mul_sub]
    rhs
    equals (f g • (conv_mu_lp2 h)) g =>
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
      simp

  conv =>
    lhs
    arg 2
    intro g
    rhs
    unfold conv_mu_lp2
    rw [← MeasureTheory.MemLp.toLp_const_smul]

  simp_rw [f_conv_mu]
  simp_rw [Pi.smul_def]
  simp
  simp_rw [← mul_assoc]
  simp_rw [mul_comm]
  simp_rw [mul_assoc]
  simp_rw [Finset.mul_sum]


  --simp_rw [← smul_eq_mul]

  conv =>
    lhs
    arg 2
    intro g
    rhs
    arg 1
    rhs
    arg 1
    intro i
    --rw [← Finset.mul_sum]


  simp_rw [tolp_apply]
  rw [integral_sub]
  rw [MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.integral_mul_left_eq_self (g := s⁻¹)]
    simp
  rw [← MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro g
    rw [← Finset.mul_sum]
    rw [Finset.sum_bijective (s := S) (t := S) (e := fun s => s⁻¹) (g := fun i => (f (i * g) * (h g))) (by
      refine ⟨?_, ?_⟩
      . exact inv_injective
      . exact inv_surjective
    ) (by
      intro a
      refine ⟨?_, ?_⟩
      . apply hGS.has_inv a
      . simpa using (hGS.has_inv a⁻¹)
    ) (by
      simp
    )]

  simp_rw [Finset.mul_sum]
  rw [← integral_sub]
  simp_rw [← mul_assoc]
  simp_rw [← Finset.sum_mul]
  simp_rw [mul_comm]
  conv =>
    lhs
    arg 2
    intro a
    rw [mul_comm]
    rw [← mul_sub]



  conv =>
    rhs
    arg 2
    intro g
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    unfold conv_mu_lp2
    simp [f_conv_mu]
    rw [tolp_apply]
    --rw [← MeasureTheory.MemLp.toLp_const_smul]


  simp_rw [Finset.mul_sum]
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s⁻¹ * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s⁻¹
    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
    -- rw [mul_sub]
    -- rhs
    -- equals (f g • (conv_mu_lp2 h)) g =>
    --   rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
    --   sim




lemma laplace_range_dense: Dense (X := ↥(Lp ℝ 2 volume (α := G))) (laplace_range ) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [Submodule.topologicalClosure_eq_top_iff]
  simp_rw [laplace_range]
  ext g
  rw [Submodule.mem_bot]
  refine ⟨?_, ?_⟩
  .
    intro hg
    rw [Submodule.mem_orthogonal] at hg
    have inner_laplace_zero: ∀ u: (Lp ℝ 2 volume), ⟪Laplace_linear u, g⟫ = 0 := by
      intro u
      specialize hg (Laplace_linear u)
      simpa using hg

    simp only [Laplace_linear, LinearMap.coe_mk, AddHom.coe_mk] at inner_laplace_zero
    simp_rw [← laplace_self_adjoint] at inner_laplace_zero
    simp at inner_laplace_zero

    have eq_zero:= Dense.eq_zero_of_inner_right (E := (Lp ℝ 2 (volume (α := G)))) (𝕜 := ℝ) (by apply dense_univ) (x := (Laplace g))
    simp at eq_zero
    specialize eq_zero inner_laplace_zero
    apply laplace_zero_iff_zero _ eq_zero
  . intro hg
    rw [hg]
    simp








#print sorries proposition_3_18
#print axioms proposition_3_18
#print axioms laplace_range_dense



lemma g_sub_norm_gt (n: ℕ): ∃ s ∈ S, ‖(G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))‖^2 > 1 := by
  by_contra!
  have card_le := Finset.sum_le_card_nsmul S _ (1 : ℝ) this
  have sum_norm := (proposition_3_18 (G_n (n + 1) (by simp)) )
  have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace (G_n (n + 1) (by simp))) (G_n (n + 1) (by simp)) (𝕜 := ℝ) (α := G)
  have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp))).2
  have real_inner : ∀ a b : ℝ, ⟪a, b⟫ = b * a := fun a b => rfl
  rw [integral_eq_eq_sum] at g_inner_laplace
  .
    simp_rw [real_inner] at g_inner_laplace
    simp_rw [← g_inner_laplace] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    rw [g_n_prop] at sum_norm
    rw [eq_inv_mul_iff_mul_eq₀] at sum_norm
    simp at sum_norm
    rw [← sum_norm] at card_le
    simp at card_le
    rw [mul_le_iff_le_one_left] at card_le
    . norm_num at card_le
    . simp
      have foo := S_nonempty
      grind
    .
      simp
      have foo := S_nonempty
      grind

  .
    rw [MeasureTheory.L2.inner_def] at g_n_prop
    apply MeasureTheory.integrable_of_integral_eq_one at g_n_prop
    exact g_n_prop


lemma g_sub_norm_single_s: ∃ s ∈ S, { n: ℕ | ‖(G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))‖^2 > 1 }.Infinite := by

  have frequent := Filter.Frequently.of_forall (f := Filter.atTop) g_sub_norm_gt
  simp at frequent
  obtain ⟨s, s_mem, s_frequently⟩ := frequent
  rw [Nat.frequently_atTop_iff_infinite] at s_frequently
  use s
  refine ⟨s_mem, ?_⟩
  simpa using s_frequently


lemma lipschitzWith_mul_prod  {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C)
  (g: G) (s: List S): dist (f (s.unattach.prod * g)) (f g) ≤ C * s.length := by

  induction s with
  | nil =>
    simp
  | cons head tail ih =>
    simp
    have triangle := dist_triangle (f (head * tail.unattach.prod * g)) (f (tail.unattach.prod * g)) (f g)
    grw [triangle]
    grw [ih]
    rw [mul_assoc]
    grw [hf _ _ (by simp)]
    grind


lemma lipschitzWith_discrete {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C):
    LipschitzWith C f := by

  apply LipschitzWith.of_dist_le_mul
  intro x y

  have prod_eq := word_norm_prod (y * x⁻¹) (WordNorm (y * x⁻¹)) rfl
  obtain ⟨l, l_prod, l_len⟩ := prod_eq
  simp [ProdS] at l_prod

  have mul_prod := lipschitzWith_mul_prod f hf x l
  simp [l_prod] at mul_prod
  rw [dist_comm]
  grw [mul_prod]
  simp [dist, WordDist, l_len]



lemma f_mul_mu_summable (f: G → ℝ) (g: G) (s: G):
  Summable fun a ↦
    (f ((Additive.toMul a))) * (if s = ((((Additive.toMul a))⁻¹ * g)) then 1 else 0) := by
  apply summable_of_hasFiniteSupport
  change (Function.support _).Finite
  simp only [one_div, Function.support_mul, Function.support_inv]
  apply Set.Finite.inter_of_right
  apply Set.Finite.subset (s := {(opAdd (g * s⁻¹))})
  . simp
  . intro a ha
    simp at ha
    simp [opAdd]
    rw [ha]
    simp



-- Proposition 1.5
lemma laplace_sum_swap (f g: G → ℝ) (hfg: f.support.Finite ∨ g.support.Finite): ∑' (x: G), (f x) * (Laplace_b g) x = ∑' (x: G), ((Laplace_b f ) x) * (g x) := by
  rw [laplace_sum_swap_helper hfg]
  simp_rw [mul_comm _ ( g _)]
  rw [laplace_sum_swap_helper hfg.symm]
  simp_rw [mul_comm]

#print axioms laplace_sum_swap


lemma conv_neg_left (f g: G → ℝ): Conv (-f) g = -(Conv f g) := by
  conv =>
    pattern -f
    equals (-1 : ℝ) • f => simp

  rw [conv_smul]
  simp

lemma laplace_b_sub (f g: G → ℝ): Laplace_b (f - g) = Laplace_b f - Laplace_b g := by
  simp [Laplace_b]
  nth_rw 3 [sub_eq_add_neg]
  rw [conv_add_left]
  .
    rw [conv_neg_left]
    ring_nf
  .
    apply conv_exists_fin_supp
    right
    apply mu_finsupp
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp


-- DO NOT REMOVE `f_n_limit` - this will be needed by the spectral theorem part of the proof
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma nontrivial_harmonic_case_one (f_n_limit: ∀ s: S, (Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by



  let H_n (n: ℕ) (s: G): (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) :=
    (1 / (‖(((G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))))‖)) •
      MeasureTheory.Lp.compMeasurePreserving (Inv.inv) (measure_preserving_inv) (((G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))))

  obtain ⟨s, s_mem_S, s_infinite⟩ := g_sub_norm_single_s
  let seq := Nat.nth ({n | ‖(G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp))‖ ^ 2 > 1})
  have seq_mono : StrictMono seq := Nat.nth_strictMono s_infinite


  have H_n_norm (n: ℕ): ‖H_n (seq n) s‖ₑ = 1 := by
    conv =>
      rhs
      equals ‖(1: ℝ)‖ₑ => simp
    rw [enorm_eq_iff_norm_eq]
    unfold H_n
    have norm_gt := Nat.nth_mem_of_infinite s_infinite n
    rw [norm_smul]
    rw [MeasureTheory.Lp.norm_compMeasurePreserving]
    field_simp
    simp
    rw [mul_inv_cancel₀]
    simp [seq]
    simp at norm_gt
    by_contra!
    simp only [Set.ofPred] at this
    simp [this] at norm_gt
    norm_num at norm_gt

  have seq_add_pos: ∀ {n}, 0 < (seq (n + 1)) := by
    intro n
    have prev_lt := (seq_mono.lt_iff_lt (a := n) (b := n + 1)).mpr (by simp)
    grind

  have h_n_f_lipschitz: ∀ n: ℕ, LipschitzWith ((2 * #(S))^((2 : ℝ)⁻¹)) (Conv (H_n (seq (n)) s) (G_n ((seq n) + 1) (by simp))) := by
    intro n
    let G'_n := (G_n ((seq n) + 1) (by simp))
    apply lipschitzWith_discrete
    intro g y hy
    rw [Real.dist_eq]
    rw [← Real.norm_eq_abs]
    rw [norm_sub_rev]
    have y_eq_inv_inv: y = y⁻¹⁻¹ := by simp
    rw [y_eq_inv_inv]
    rw [← f_conv_delta (f := Conv (↑↑(H_n (seq (n)) s)) (G_n ((seq n) + 1) (by simp)))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [neg_smul]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        rw [← ENNReal.ofReal_le_ofReal_iff]
        .
          rw [ofReal_norm_eq_enorm]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [my_haar_eq_count]
          rw [← my_haar_eq_count]
          conv =>
            lhs
            arg 1
            arg 0
            unfold Conv
          eta_reduce
          simp_rw [my_haar_eq_count]
          conv =>
            arg 1
            arg 3
            equals myHaarAddOpp =>
              exact my_add_haar_eq_count.symm

          refine le_trans (ENNReal.eLpNorm_top_convolution_le (μ := myHaarAddOpp) (c := 1) (p := 2) (q := 2) (hpq := inferInstance) (by apply AEMeasurable.of_discrete) (by apply AEMeasurable.of_discrete) (by intro a b; simp)) ?_
          .
            simp [norm, volume] at H_n_norm
            rw [my_add_haar_eq_count]
            simp [H_n_norm]

            have sum_norm := proposition_3_18 G'_n
            have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace G'_n) G'_n (𝕜 := ℝ) (α := G)
            have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp))).2
            rw [integral_eq_eq_sum] at g_inner_laplace
            replace g_inner_laplace := g_inner_laplace.trans sum_norm
            rw [g_n_conv_norm] at g_inner_laplace
            rw [inv_mul_eq_div] at g_inner_laplace
            rw [eq_div_iff_mul_eq] at g_inner_laplace

            --simp at g_inner_laplace
            --simp_rw [mul_comm] at g_inner_laplace
            .
              simp [eLpNorm, eLpNorm']
              simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, MeasureTheory.Lp.norm_def, eLpNorm, eLpNorm', conv_finsupp_lp2] at g_inner_laplace
              rw [← ENNReal.ofReal_rpow_of_pos]
              .
                have hkey : (∫⁻ (a : Additive G), ‖(H_n (seq n) s : Additive G → ℝ) a‖ₑ ^ 2 ∂Measure.count) ^ (2 : ℝ)⁻¹ = 1 := by
                  have h := H_n_norm n
                  show (∫⁻ (a : G), ‖(H_n (seq n) s : G → ℝ) a‖ₑ ^ 2 ∂Measure.count) ^ (2 : ℝ)⁻¹ = 1
                  simpa [MeasureTheory.Lp.enorm_def, eLpNorm, eLpNorm', one_div, volume,
                    my_haar_eq_count] using h
                rw [hkey, one_mul]
                apply ENNReal.rpow_le_rpow
                .
                  generalize_proofs p_1 p_2 p_3
                  -- TODO - make this less horrible
                  grw [Finset.single_le_sum (f := (fun g => ∫⁻ (a : Additive G), ‖(G_n ((seq n) + 1) (by simp)) a + Conv (-↑↑(G_n ((seq n) + 1) (by simp))) (delta g) a‖ₑ ^ 2 ∂Measure.count)) (s := S) (hf := by simp) (h := (by rw [S_eq_Sinv]; simp [hy]))]



                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.toReal_pow] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_mul] at g_inner_laplace
                  simp  [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_inner_laplace
                  simp at g_inner_laplace
                  rw [neg_smul]
                  simp_rw [conv_smul]
                  simp
                  simp_rw [← sub_eq_add_neg]
                  simp [G'_n] at g_inner_laplace
                  apply_fun ENNReal.ofReal at g_inner_laplace
                  simp at g_inner_laplace
                  rw [g_inner_laplace]
                  norm_cast
                  rw [ENNReal.ofReal_sum_of_nonneg]
                  .
                    conv =>
                      rhs
                      arg 2
                      intro i
                      rw [ENNReal.ofReal_toReal (by
                        simp [f_conv_delta_helper]
                        have g_norm := MeasureTheory.Lp.eLpNorm_lt_top ((G_n ((seq n) + 1) (by simp)) - (Lp.compMeasurePreserving (fun x => i⁻¹ * x) (by
                          apply measurePreserving_mul_left
                        ) (G_n ((seq n) + 1) (by simp))))
                        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at g_norm
                        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)] at g_norm
                        simp [eLpNorm, eLpNorm', Lp.compMeasurePreserving] at g_norm
                        rw [ENNReal.rpow_lt_top_iff_of_pos (by simp)] at g_norm
                        grind
                      )]
                    simp [volume]
                    simp_rw [my_haar_eq_count]
                    apply le_refl
                  . simp
                . simp
              .
                simpa using S_nonempty

              -- Finset.single_le_sum
            . simp
              grind
            .
              apply MeasureTheory.Integrable.of_integral_ne_zero
              rw [← g_inner_laplace]
              simp [G'_n]
              have foo := g_n_conv_norm (seq (n) + 1) (by simp)
              grind
        .
          exact NNReal.coe_nonneg _
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
        .
          refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
          rw [← my_add_haar_eq_count]
          rw [neg_smul]
          rw [conv_smul]
          simp
          rw [← Pi.neg_def]
          simp [Conv]
          rw [← Function.comp_def (β := Additive G)]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := Measure.count)]
          .
            conv =>
              arg 1
              arg 1
              arg 1
              equals ↑↑(G_n ((seq (n)) + 1) (by simp)) ∘ Additive.toMul =>
                rfl

            conv =>
              arg 1
              arg 1
              arg 2
              equals (delta y⁻¹) ∘ Additive.toMul =>
                rfl

            rw [← my_add_haar_eq_count]
            grw [ENNReal.eLpNorm_convolution_le_enorm_mul (p := 2) (q := 1)]
            .
              refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ?_) ?_
              · exact MeasureTheory.MemLp.eLpNorm_lt_top (MeasureTheory.MemLp.comp_measurePreserving (ν := volume) (Lp.memLp _) measure_preserving_unop_tomul)
              · refine MeasureTheory.MemLp.eLpNorm_lt_top (MeasureTheory.MemLp.comp_measurePreserving (ν := volume) ?_ measure_preserving_unop_tomul)
                apply Continuous.memLp_of_hasCompactSupport
                · fun_prop
                · simp [HasCompactSupport, tsupport]
            . simp
            . simp
            . simp
            . simp
            . apply AEMeasurable.of_discrete
            . apply AEMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [my_add_haar_eq_count]
            apply MeasurePreserving.id
    . rw [← my_haar_eq_count]
      apply Lp.memLp
    . rw [← my_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp

  -- Now rename Hn ∗Gn such that we have added a constant so that Hn ∗Gn(e) = 0
  let new_seq: ℕ → ℕ := seq
  let H_G_conv_zero (n: ℕ) (g: G) := ((Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp))) g) - (Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp)) 1)


  -- TODO - can the lipschitz constant can be improved?
  have H_G_conv_zero_lipschitz: ∀ n: ℕ, LipschitzWith ((((2 * #(S))^((2 : ℝ)⁻¹))) + 0) (H_G_conv_zero n) := by
    intro n
    simp only [H_G_conv_zero]
    simp only [new_seq]
    apply LipschitzWith.sub
    .
      apply h_n_f_lipschitz
    . apply LipschitzWith.const


  have H_n_conv_zero_eq: ∀ n: ℕ, (H_G_conv_zero (n) 1) - (H_G_conv_zero (n) s⁻¹) = ‖(G_n ((new_seq n) + 1) (by simp)) - (conv_finsupp_lp2 (((G_n ((new_seq n) + 1) (by simp)))) (delta s) (by simp [delta]))‖ := by
    intro n
    simp [H_G_conv_zero]
    have s_inv_eq: s⁻¹ = s⁻¹ * 1 := by
      simp
    rw [s_inv_eq]
    rw [← f_conv_delta  (f := Conv ((H_n ((new_seq n)) s)) ((G_n ((new_seq n) + 1) (by simp))))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [neg_smul]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        simp [H_n, conv_finsupp_lp2]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
        rw [conv_smul]
        conv =>
          lhs
          lhs
          arg 0
          unfold Conv

        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        simp only [convolution,
          ContinuousLinearMap.coe_sub', ContinuousLinearMap.mul_apply', Pi.smul_apply, smul_eq_mul]
        simp
        have t_fake_inv: ∀ (t: G), (t: (Additive G))⁻¹ = -(Additive.ofMul t) := by
          intro t
          rfl

        simp [t_fake_inv, Additive.ofMul]
        have one_g_eq: (1 : G) = (0 : (Additive G)) := rfl
        simp_rw [one_g_eq]
        simp_rw [zero_sub]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rhs
          rhs
          equals (conv_finsupp_lp2 (-(G_n (new_seq n + 1) (by simp))) (delta s) (by simp [delta])) (-t) =>
            simp [conv_finsupp_lp2]
            simp_rw [tolp_apply]
            norm_cast
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]

        simp [conv_finsupp_lp2]
        norm_cast
        simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [neg_smul]
        simp_rw [conv_smul]
        simp
        rw [MeasureTheory.MemLp.toLp_neg (by
          rw [f_conv_delta_helper]
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
          . apply MeasureTheory.Lp.memLp
          .
            exact measurePreserving_mul_left volume s⁻¹
        )]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [← Pi.sub_apply]
        have real_inner: ∀ a b : ℝ, ⟪a, b⟫ = a * b := fun a b => by
          rw [show (⟪a, b⟫ : ℝ) = b * a from rfl, mul_comm]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rw [← Pi.add_apply]
          rw [← Pi.mul_apply]


        rw [MeasureTheory.integral_neg_eq_self]
        simp_rw [Pi.mul_apply]
        simp_rw [← real_inner]
        conv =>
          lhs
          rhs
          equals ‖(G_n (new_seq n + 1) (by simp)) - (MemLp.toLp (Conv ((G_n ((new_seq n) + 1) (by simp))) (delta s)) (by
              rw [f_conv_delta_helper]
              rw [← Function.comp_def]
              apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
              . apply MeasureTheory.Lp.memLp
              .
                exact measurePreserving_mul_left volume s⁻¹
            ))‖^2 =>
            rw [← real_inner_self_eq_norm_sq]
            rw [MeasureTheory.L2.inner_def]
            simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
            rfl

        rw [pow_two]
        rw [real_inner]
        have key : ∀ a : ℝ, a⁻¹ * (a * a) = a := by
          intro a
          rcases eq_or_ne a 0 with h | h
          · simp [h]
          · field_simp
        exact key _
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
      .
        -- TODO - deduplicate this
        simp [f_conv_delta_helper]
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.neg
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          .
            simp [volume]
            rw [my_haar_eq_count]
            refine MeasurePreserving.mul_left Measure.count s⁻¹ ?_
            apply MeasureTheory.MeasurePreserving.id
    . rw [← my_haar_eq_count]
      apply Lp.memLp
    . rw [← my_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp [delta]



  --let F := fun (n : ℕ) (g: G) => (Conv (H_n (seq n) s) (f_n (seq n)))
  --have F_tendsto: Filter.Tendsto F Filter.atTop

  have compact_with_fixed_g (g: G): IsCompact (closure ( (Set.range (fun n => H_G_conv_zero n g)))) := by

    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]


    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have new_compact_closure: IsCompact (closure (Set.range (fun n => H_G_conv_zero n))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]

    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have arzela_tendsto := IsCompact.tendsto_subseq new_compact_closure (x := fun n => (
    H_G_conv_zero n
  )) (by
    intro n
    apply _root_.subset_closure
    simp
  )
  obtain ⟨arzela_lim, arzela_lim_mem, arzela_seq, arzela_seq_mono, tendsto_arzela_lim⟩ := arzela_tendsto
  rw [tendsto_pi_nhds] at tendsto_arzela_lim

  have tendsto_one := tendsto_arzela_lim 1
  have tendsto_s_inv := tendsto_arzela_lim s⁻¹
  simp at tendsto_one
  simp at tendsto_s_inv

  have abs_tendsto : ∀ z: ℝ, Filter.Tendsto (fun x => |x|) (nhds z) (nhds |z|)  := by
    intro z
    apply Continuous.tendsto
    fun_prop

  have tendsto_sub := tendsto_one.sub tendsto_s_inv
  use {
    toFun := fun g => arzela_lim g
    lipschitz := by
      use ⟨(((↑(#S) * 2) ^ (2 : ℝ)⁻¹)), by positivity⟩
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq]

      have new_tendsto_sub := (abs_tendsto _).comp ((tendsto_arzela_lim x).sub (tendsto_arzela_lim y))
      have sub_le := le_of_tendsto new_tendsto_sub (b := ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist x y)) ?_
      . norm_cast
        norm_cast at sub_le
      . apply Filter.Eventually.of_forall
        intro n
        have foo := (H_G_conv_zero_lipschitz (arzela_seq n)).dist_le_mul x y
        rw [Real.dist_eq] at foo
        simp
        norm_cast
        simp at foo
        norm_cast at foo
        ring_nf at foo
        ring_nf
        exact foo

    harmonic := by
      simp [Harmonic]
      intro x
      rw [← sub_eq_zero]

      have sum_lim := tendsto_finset_sum (s := S) (fun s hs => tendsto_arzela_lim (s * x))
      have tendsto_sub := (tendsto_arzela_lim x).sub (sum_lim.const_mul ((#S : ℝ))⁻¹)
      norm_cast

      have lim_zero := squeeze_zero (t₀ := Filter.atTop)
        (f := (fun x_1 ↦ |((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 x - (↑(#S))⁻¹ * ∑ c ∈ S, ((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 (c * x)|))
        (g := fun n => (1 / (n + 1)))
        ?_ ?_ ?_
      .
        have target_eq_zero := tendsto_nhds_unique ((abs_tendsto _).comp tendsto_sub) (lim_zero)
        rw [abs_eq_zero] at target_eq_zero
        rw [sub_eq_zero] at target_eq_zero
        simp [target_eq_zero]
      . simp
      . intro n
        simp
        conv =>
          lhs
          arg 1
          equals Laplace_b (H_G_conv_zero (arzela_seq n)) x =>
            simp [Laplace_b]
            simp [f_conv_mu]


        have ae_le := ENNReal.ae_le_essSup (fun x ↦ ENNReal.ofReal |Laplace_b (H_G_conv_zero (arzela_seq n)) x|) (μ := volume)
        simp [volume] at ae_le
        rw [my_haar_eq_count] at ae_le
        rw [count_ae_everywhere] at ae_le
        specialize ae_le x
        rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
        grw [ae_le]

        simp [H_G_conv_zero]
        intro i
        rw [← Pi.sub_def]
        rw [laplace_b_sub]
        simp
        rw [sub_eq_add_neg]
        grw [abs_add_le]
        simp
        rw [laplace_conv_eq_laplace_right_of_lp2]
        .
          simp [Conv]
          grw [ENNReal.ofReal_add_le]
          rw [← Real.enorm_eq_ofReal_abs]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [haar_eq_haar_add]
          conv =>
            lhs
            arg 1
            arg 1
            arg 2
            equals (Laplace_b (G_n ((new_seq (arzela_seq n)) + 1) (by simp))) ∘ Additive.toMul =>
              rfl

          conv =>
            lhs
            arg 1
            arg 1
            arg 1
            equals (H_n (new_seq (arzela_seq n)) s) ∘ Additive.toMul =>
              rfl

          refine le_trans (add_le_add_left (ENNReal.eLpNorm_convolution_le_enorm_mul (G := Additive G) (L := ContinuousLinearMap.mul ℝ ℝ) (p := 2) (q := 2) (r := ⊤) (μ := myHaarAddOpp) ?_ ?_ ?_ ?_ ?_ ?_) _) ?_
          · simp
          · simp
          · simp
          · rw [ENNReal.inv_top, zero_add]; exact ENNReal.inv_two_add_inv_two
          · apply AEMeasurable.of_discrete
          · apply AEMeasurable.of_discrete
          .
            conv =>
              lhs
              arg 1
              arg 1
              arg 2
              arg 1
              equals ↑↑(H_n (seq (arzela_seq n)) s) => rfl


            rw [show eLpNorm (↑↑(H_n (seq (arzela_seq n)) s)) 2 myHaarAddOpp = 1 from by
                  have h := H_n_norm (arzela_seq n)
                  rw [MeasureTheory.Lp.enorm_def] at h
                  rw [my_add_haar_eq_count,
                      show (Measure.count : Measure (Additive G)) = myHaar from my_haar_eq_count.symm]
                  exact h]
            simp [enorm]
            have g_norm := g_n_laplace_enorm_le (seq (arzela_seq n) + 1) (by simp)
            rw [MeasureTheory.Lp.enorm_def] at g_norm
            simp only [Laplace] at g_norm
            rw [laplace_b_const]
            simp [Laplace_b]
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_norm
            simp only [conv_mu_lp2] at g_norm
            rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_norm
            refine le_trans (le_of_eq (eLpNorm_comp_measurePreserving (by apply AEStronglyMeasurable.of_discrete) measure_preserving_unop_tomul)) ?_
            grw [g_norm]
            norm_cast
            simp
            norm_cast
            rw [ENNReal.ofReal_inv_of_pos (by positivity)]
            simp
            norm_cast
            have seq_le_n : n ≤ seq (arzela_seq n) := by
              have n_arzela : n ≤ arzela_seq n := by
                apply nat_mono_le arzela_seq_mono
              apply LE.le.trans n_arzela

              apply nat_mono_le seq_mono

            omega

        .
          -- TODO - deduplicate this
          simp [ConvExists]
          rw [my_add_haar_eq_count]
          apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
          . infer_instance
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [← Function.comp_def]
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
          .
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
        . rw [← my_haar_eq_count]
          apply Lp.memLp
        . rw [← my_haar_eq_count]
          apply Lp.memLp
      .
        simp
        simp_rw [inv_eq_one_div]
        apply tendsto_one_div_add_atTop_nhds_zero_nat
  }
  intro z
  by_contra!
  have lim_ge := ge_of_tendsto tendsto_sub (b := 1) (by
    apply Filter.Eventually.of_forall
    intro n
    rw [H_n_conv_zero_eq]
    simp [new_seq, seq]
    have norm_gt := Nat.nth_mem_of_infinite s_infinite ((arzela_seq n))
    simp at norm_gt
    apply le_of_lt
    exact norm_gt
  )

  apply_fun (fun f => f 1 - f s⁻¹) at this
  simp [ConstLipschitzH] at this
  norm_cast at this
  grind



-- Case two of Theorem 3.6
set_option maxHeartbeats 2000000 in
lemma nontrivial_harmonic_case_two (f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by
  obtain ⟨s, hs⟩ := f_n_limit
  let H_n := fun n g => if  ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) ≠ 0 then ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) / |((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)| else 1

  -- TODO - why can't we write '∞' here
  have H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1 := by
    intro n
    simp [H_n]
    simp [MeasureTheory.eLpNormEssSup]
    --rw [essSup_eq_sInf]
    simp [MeasureTheory.volume]
    rw [my_haar_eq_count]
    simp
    have h_norm_one: ∀ x, ‖H_n n x‖ₑ = 1 := by
      simp [H_n]
      intro g
      split_ifs
      . simp
      .

        rename_i foo
        by_cases val_pos: 0 ≤ ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)
        .
          rw [abs_of_nonneg val_pos]
          rw [div_self]
          . simp
          . exact foo
        .
          rw [abs_of_neg]
          .
            rw [div_neg_self]
            .
              simp
            . exact foo
          . linarith

    unfold H_n at h_norm_one
    simp at h_norm_one
    simp_rw [h_norm_one]
    simp

  have H_n_diff_pos: ∀ n: ℕ,  ∀ (i : G), 0 ≤ H_n n i⁻¹ * f_n n i - H_n n i⁻¹ * f_n n ((↑s)⁻¹ * i) := by
    intro n g
    simp [H_n]
    simp [f_conv_delta]
    split_ifs
    . linarith
    .
      rename_i diff_zero
      by_cases val_pos: 0 ≤ f_n n g - f_n n ((↑s)⁻¹ * g)
      .
        rw [abs_of_nonneg val_pos]
        rw [div_self]
        . linarith
        . assumption
      .
        rw [abs_of_neg]
        . rw [div_neg_self]
          . linarith
          . assumption
        .
          simpa using val_pos

  have fn_sub_norm: ∀ n: ℕ, eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 = ENNReal.ofReal |((Conv (H_n n) (f_n n)) 1) - ((Conv (H_n n) (f_n n)) s⁻¹)| := by
    intro n
    simp [eLpNorm, eLpNorm']
    rw [lintegral_g_eq_add]
    conv =>
      lhs
      arg 1
      intro g
      rw [Real.enorm_eq_ofReal_abs]
      arg 1
      equals (H_n n g⁻¹) * (f_n n g - (Conv (f_n n) (delta s.val)) g) =>
        simp [H_n]
        split_ifs
        .
          rename_i diff_eq_zero
          simp [diff_eq_zero]
        .
          rename_i diff_ne_zero
          by_cases val_pos: 0 ≤ ((f_n n g) - (Conv (f_n n) (delta s.val)) g)
          .
            rw [abs_of_nonneg]
            .
             rw [div_self]
             simp
             apply diff_ne_zero
            . exact val_pos
          .
            rw [abs_of_neg]
            .
              rw [div_neg_self]
              simp
              exact diff_ne_zero
            .
              simpa using val_pos

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]


    conv =>
      rhs
      arg 1
      arg 1
      rw [← Summable.tsum_sub (by
        apply summable_of_hasFiniteSupport
        change (Function.support _).Finite
        simp only [Function.support_mul]
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => ((Additive.toMul a))⁻¹) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      ) (by
        apply summable_of_hasFiniteSupport
        change (Function.support _).Finite
        simp only [Function.support_mul]
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * ((Additive.toMul a))⁻¹ ) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      )]
    simp_rw [mul_sub]
    simp_rw [f_conv_delta]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    rw [ENNReal.ofReal_eq_ofReal_iff]
    rw [← Function.Injective.tsum_eq (γ := G) (β := Additive (G)) (g := fun a => Additive.ofMul (a⁻¹))]
    simp
    rw [abs_of_nonneg]
    rfl
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    .
      simp
      apply Function.Injective.comp
      . exact neg_injective
      . exact fun ⦃a₁ a₂⦄ a ↦ a
    .
      simp
      intro g hg
      use g⁻¹
      simp
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    . simp
    . apply H_n_diff_pos n
    .
      simp_rw [← mul_sub]
      apply summable_of_hasFiniteSupport
      change (Function.support _).Finite
      simp only [Function.support_mul]
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Function.support_sub _ _)
      simp
      refine ⟨?_, ?_⟩
      . apply f_n_fin_supp
      .
        apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * a) (ht := f_n_fin_supp n)
        . intro a ha
          simpa using ha
        . simp


  have haar_eq_haar_add : myHaar = myHaarAddOpp := by
    rfl

  have h_conv_f_bounded (n: ℕ): eLpNorm (Conv (H_n n) (f_n n)) ⊤ ≤ 1 := by
    unfold Conv
    eta_reduce
    simp only [volume]
    rw [haar_eq_haar_add]
    have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
      (g := f_n n) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
      (by simp) (by simp) (by simp) (by simp)
      (by apply AEMeasurable.of_discrete)
      (by apply AEMeasurable.of_discrete)
    refine le_trans my_norm ?_
    have norm_one := f_n_norm_one (n )
    simp [volume] at norm_one
    rw [haar_eq_haar_add] at norm_one
    simp only  [volume] at H_n_norm
    rw [haar_eq_haar_add] at H_n_norm
    refine le_trans (mul_le_mul' (mul_le_mul' (show ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 by simp [enorm]) (le_of_eq (H_n_norm n))) (le_of_eq norm_one)) ?_
    simp

  have conv_laplce_norm (n: ℕ): eLpNorm ((Laplace_b ((Conv (H_n n)) (f_n n)))) ⊤ (μ := volume (α := G)) ≤ eLpNorm (H_n n) ⊤ * (eLpNorm (Laplace_b (f_n n)) 1 (μ := volume (α := G))) := by
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
      have h1 : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by simp [enorm]
      calc ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp
          ≤ 1 * eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp := by gcongr
        _ = eLpNorm (H_n n) ⊤ myHaarAddOpp * eLpNorm (Laplace_b (f_n n)) 1 myHaarAddOpp := by rw [one_mul]
    .
      apply conv_exists_fin_supp
      right
      exact f_n_fin_supp n
    . apply f_n_nonneg
    . exact f_n_fin_supp n


  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n n) (f_n n),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  have abs_conv_le_one: ∀ g: G, ∀ n: ℕ,  |Conv (H_n n) (f_n n) g| ≤ 1 := by
    intro g n
    have norm_bound := h_conv_f_bounded n
    simp [eLpNorm, eLpNormEssSup] at norm_bound
    have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Conv (H_n n) (f_n n) x‖ₑ) (μ := volume)
    simp [volume] at ae_le
    rw [my_haar_eq_count] at ae_le
    rw [count_ae_everywhere] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at norm_bound
    norm_cast at ae_le
    simp [volume] at norm_bound
    rw [my_haar_eq_count] at norm_bound
    specialize ae_le g
    have ennreal_bound := le_trans ae_le norm_bound
    norm_cast at ennreal_bound

  have conv_h_n_lipschitz (n: ℕ): LipschitzWith 2 (conv_h_n_cont n) := by
    unfold conv_h_n_cont
    simp [LipschitzWith]
    intro x y
    by_cases x_eq_y: x = y
    . simp [x_eq_y]
    .
      norm_cast
      rw [edist_dist]
      rw [Real.dist_eq]
      rw [edist_dist]
      conv =>
        rhs
        equals ENNReal.ofReal (2 * (dist x y)) =>
          rw [ENNReal.ofReal_mul]
          . simp
          . linarith
      rw [ENNReal.ofReal_le_ofReal_iff]
      .
        grw [abs_sub]
        grw [abs_conv_le_one x]
        grw [abs_conv_le_one y]
        rw [one_add_one_eq_two]
        simp
        simp [dist]
        have dist_ne_zero: dist x y ≠ 0 := by
          exact dist_ne_zero.mpr x_eq_y
        simp [dist] at dist_ne_zero
        omega
      . simp [dist]




  have compact_closure_f: IsCompact (closure ( (Set.range (fun n => (Conv (H_n n) (f_n n)))))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2
    intro x hx y hy
    simp at hx
    simp at hy
    obtain ⟨n, h_x_n⟩ := hx
    obtain ⟨m, h_y_m⟩ := hy
    rw [Real.dist_eq]
    grw [abs_sub]
    rw [← h_x_n, ← h_y_m]
    grw [abs_conv_le_one]
    grw [abs_conv_le_one]
    linarith


  rw [Filter.not_tendsto_iff_exists_frequently_notMem] at hs
  obtain ⟨eps, h_eps, frequently_gt_eps⟩ := hs
    -- We obtain a subsequence where all of the points satisfy the 'norm > ε' condition
  obtain ⟨eps_seq, mono_eps_seq, eps_seq_gt_x⟩ := Filter.extraction_of_frequently_atTop frequently_gt_eps

  -- Along this sequence, the evauation of 'Conv H_n f_n' at is leq to 1,
  -- so it's in a compact set
  have locally_bounded_at_g: ∀ g: G, ∀ n, Conv (H_n (eps_seq n)) (f_n (eps_seq n)) g ∈ Metric.closedBall 0 1 := by
    intro g n
    simp
    apply abs_conv_le_one


  have h_n_pointwise_converge := IsCompact.tendsto_subseq compact_closure_f (x := fun n => (Conv (H_n (eps_seq n)) (f_n (eps_seq n)))) (by
    intro n
    apply Set.mem_of_subset_of_mem (_root_.subset_closure)
    simp
  )
  -- We now have a sequence of functions which converges pointwise, where all of the
  -- elements of the sequence satisfy the 'norm > ε' condition
  obtain ⟨F, F_mem, seq, seq_mono, tendsto_F⟩ := h_n_pointwise_converge
  let F_lipschitzh := nontrivial_harmonic_common 2 (eps_seq ∘ seq) (by
    apply Filter.Tendsto.comp (x := Filter.atTop) (y := Filter.atTop)
    . exact StrictMono.tendsto_atTop mono_eps_seq
    . exact StrictMono.tendsto_atTop seq_mono
  ) F H_n conv_h_n_lipschitz tendsto_F H_n_norm
  use F_lipschitzh
  --use F_lipschitzh
  intro z
  have not_conv_tendsto_zero: ¬Filter.Tendsto (fun n => ENNReal.ofReal |Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) 1 - Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) (↑s)⁻¹|) Filter.atTop (nhds 0) := by
    rw [Filter.not_tendsto_iff_exists_frequently_notMem]
    use eps
    refine ⟨h_eps, ?_⟩
    simp_rw [← fn_sub_norm]
    apply Filter.Frequently.of_forall
    intro n
    exact eps_seq_gt_x (seq n)

  have F_non_const: F 1 ≠ F s⁻¹ := by
    by_contra!
    rw [← sub_eq_zero] at this
    rw [tendsto_pi_nhds] at tendsto_F
    have lim_f_sub := Filter.Tendsto.sub (tendsto_F 1) (tendsto_F s⁻¹)
    rw [this] at lim_f_sub
    simp_rw [Function.comp_def] at lim_f_sub
    rw [tendsto_zero_iff_abs_tendsto_zero] at lim_f_sub
    rw [Function.comp_def] at lim_f_sub
    have f_sub_ennreal := ENNReal.tendsto_ofReal lim_f_sub
    simp only [ENNReal.ofReal_zero] at f_sub_ennreal
    contradiction

  by_contra!
  -- TODO - there must be a cleaner way
  have app_one_eq: F_lipschitzh 1 = ConstLipschitzH z (1: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_one_eq
  simp [DFunLike.coe] at app_one_eq

  have app_s_inv_eq: F_lipschitzh s⁻¹ = ConstLipschitzH z (s⁻¹: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_s_inv_eq
  simp [DFunLike.coe] at app_s_inv_eq
  rw [← app_one_eq] at app_s_inv_eq
  norm_cast at app_s_inv_eq
  rw [eq_comm] at app_s_inv_eq
  simp [nontrivial_harmonic_common] at app_s_inv_eq
  contradiction

--#print sorries nontrivial_harmonic_case_one
--#print sorries nontrivial_harmonic_case_two

#synth OrderTopology ENNReal

-- Theorem 3.6 - a non-constant harmonic function exists on G
theorem exists_nontrivial_harmonic: ∃ F: LipschitzH , ∀ z: ℝ, F ≠ ConstLipschitzH z := by
  by_cases f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))
  . exact nontrivial_harmonic_case_two f_n_limit
  .
    simp at f_n_limit
    exact nontrivial_harmonic_case_one (by
      intro s
      exact f_n_limit s.val s.property
    )


instance new_nonempty_basis: Nonempty ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V) := Module.Basis.index_nonempty (Module.Basis.ofVectorSpace _ _)


-- lemma hermitian_det_pow_le (R: ℝ) (hR: (v_r_all_nonzero V).choose ≤ R): (Q_R_matrix R (V := V)).det ^ ((1: ℝ) / Module.finrank ℝ V) ≤ (Q_R_matrix R (V := V)).trace := by
--   rw [(Q_R_lin_hermetian V R).det_eq_prod_eigenvalues, (Q_R_lin_hermetian V R).trace_eq_sum_eigenvalues]
--   have am_gm :=  Real.geom_mean_le_arith_mean (ι := ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)) (s := Finset.univ)
--     (w := fun i => 1)
--     (z := fun i => (Q_R_lin_hermetian V R).eigenvalues i)
--     (by intro i hi; positivity)
--     (by
--       simp
--       rw [← Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℝ V)]
--       rw [Module.finrank_pos_iff_of_free]
--       infer_instance
--     )
--     (by
--       intro i _
--       apply (Q_R_matrix_pos_def V R hR).posSemidef.eigenvalues_nonneg
--     )
--   simp at am_gm
--   simp
--   rw [← Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℝ V)] at am_gm
--   grw [am_gm]
--   apply div_le_self
--   .
--     apply Finset.sum_nonneg
--     intro i _
--     apply (Q_R_matrix_pos_def V R hR).posSemidef.eigenvalues_nonneg
--   . simp
--     apply Submodule.nontrivial_iff_ne_bot.mp
--     infer_instance
