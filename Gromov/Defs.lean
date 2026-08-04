module

public import Mathlib
public import Gromov.Defs.Convolution

/-!
# The discrete Laplacian and the `G`-action

The Laplacian `Laplace_b` / `Laplace`, the constant functions `ConstF`, the quotient `W`, the
`G`-action `gAct`, and the closed-ball counting lemmas.

Root of the `Gromov.Defs` hierarchy: importing it pulls in the word metric, the measure
structure, `LipschitzH` and the convolution API.
-/

@[expose] public section

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

noncomputable def Laplace_b (f: G → ℝ): G → ℝ := f - (Conv f (mu ))
noncomputable def Laplace (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := f - (conv_mu_lp2 f)


-- TODO - make this Finite to avoid a non-compuatable Fintype instance
noncomputable instance fintype_closedBall (x: G) (r: ℝ): Fintype ↑(Metric.closedBall x r) := Set.Finite.fintype (finite_closed_ball _ _)


-- Graphs and Discrete Direchlet Spaces
-- https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-GraphTh/Keller/KellerLenzWojciechowski_GraphsAndDiscreteDirichletSpaces_wu_version.pdf


def ConstF: Submodule ℝ (LipschitzH) := {
  carrier := Set.range ConstLipschitzH
  add_mem' := by
    intro a b ha hb
    simp at ha
    simp at hb
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    simp
    use (x + y)
    ext g
    simp [ConstLipschitzH]
    rw [← hx, ← hy]
    dsimp [ConstLipschitzH]
  zero_mem' := by
    use (0 : ℝ)
    simp [ConstLipschitzH]
    ext g
    simp
  smul_mem' := by
    intro c f hf
    simp at hf
    simp
    obtain ⟨x, hx⟩ := hf
    use (c * x)
    ext g
    simp [ConstLipschitzH]
    left
    rw [← hx]
    simp [ConstLipschitzH]
}

instance isometricGMul: IsIsometricSMul (MulOpposite G) (G) where
  isometry_smul := by
    intro g
    simp [Isometry]
    intro a b
    simp [edist]
    simp [PseudoMetricSpace.edist]
    simp [WordDist]


def gAct (g: G) (v: LipschitzH ): LipschitzH  := {
  toFun := fun x => v (x * g)
  lipschitz := by
    obtain ⟨C, hC⟩ := v.lipschitz
    use C
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [lipschitzWith_iff_dist_le_mul] at hC
    specialize hC (x * g) (y * g)
    simp [DFunLike.coe]
    grw [hC]
    simp [dist, WordDist]
  harmonic := by
    unfold Harmonic
    intro x
    simp
    have v_harmonic := v.harmonic
    simp [Harmonic] at v_harmonic
    specialize v_harmonic (x * g)
    rw [v_harmonic]
    simp_rw [← mul_assoc]
}

lemma gAct_mul (g h : G) (f: LipschitzH ): gAct (g * h) f = gAct g (gAct h f) := by
  unfold gAct
  ext x
  simp [DFunLike.coe]
  rw [← mul_assoc]


def gAct_const (g: G) (z: ℝ): gAct g (ConstLipschitzH z) = ConstLipschitzH z := by
  unfold gAct
  unfold ConstLipschitzH
  ext x
  simp [DFunLike.coe]

#synth Module ℝ (LipschitzH)
#synth AddCommGroup (LipschitzH)

abbrev W := (LipschitzH) ⧸ ConstF

#synth Module ℝ (W)

noncomputable def f_n (n: ℕ) (g: G): ℝ := ((1: ℝ) / ((n + 1): ℝ)) * ∑ m: Fin (n + 1), muConv  (m.val) g

lemma closed_ball_eq_S_pow (R: ℕ): (finite_closed_ball 1 R).toFinset = S ^ R := by
  ext a
  refine ⟨?_, ?_⟩
  . intro ha
    simp [dist, WordDist_one] at ha
    rw [Finset.mem_pow]
    obtain ⟨l, l_prod, l_len⟩ := word_norm_prod_self a
    let padded := l ++ List.replicate (R - WordNorm a) ⟨1, one_mem⟩
    simp_rw [← Function.comp_def]
    simp_rw [← List.map_ofFn]
    conv =>
      arg 1
      intro f
      lhs
      arg 1
      equals (List.ofFn f).unattach =>
        rfl

    have padded_len: padded.length = R := by
      unfold padded
      simp [l_len]
      grind
    use fun n => padded.get ⟨n, by (
      grind
    )⟩
    rw [List.ofFn_congr padded_len.symm]
    simp
    unfold padded
    simp
    simp [ProdS] at l_prod
    rw [← l_prod]
  . intro hb
    rw [Finset.mem_pow] at hb
    simp [dist, WordDist_one]
    obtain ⟨f, hf⟩ := hb
    conv at hf =>
      lhs
      arg 1
      equals (List.ofFn f).unattach =>
        simp_rw [← Function.comp_def]
        simp_rw [← List.map_ofFn]
        rfl

    have r_eq: R = (List.ofFn f).length := by
      simp
    rw [r_eq]
    apply word_norm_le
    simp [ProdS, hf]

lemma card_closed_ball_eq (R: ℕ): #((finite_closed_ball 1 R).toFinset) = #(S ^ R) := by
  rw [closed_ball_eq_S_pow]


-- Proposition 1.5 helper (moved from Harmonic.lean)
lemma laplace_sum_swap_helper {f g: G → ℝ} (hgf: f.support.Finite ∨ g.support.Finite): ∑' (x: G), (f x) * (Laplace_b g) x = 2⁻¹ * ∑' (x: G), ((#(S) : ℝ)⁻¹) * ∑ s ∈ S, (((f x) - (f (s * x))) * ((g x) - (g (s * x)))) := by
  simp_rw [sub_mul]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [Laplace_b, f_conv_mu]
  simp
  simp_rw [← Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib]
  simp
  have foo := S_card_ne_zero_re
  conv =>
    rhs
    rhs
    arg 1
    intro x
    rw [mul_sub (#S : ℝ)⁻¹]
    lhs
    rw [← mul_assoc]
    rw [mul_sub]
    ring_nf
    rw [mul_inv_cancel₀ (by apply S_card_ne_zero_re)]


  simp
  rw [Summable.tsum_sub]

  conv =>
    rhs
    rhs
    rhs
    arg 1
    intro x
    rw [Finset.mul_sum]
  rename_bvar b → x
  rw [Summable.tsum_finsetSum]
  .
    conv =>
      rhs
      rhs
      rhs
      arg 2
      intro s
      rw [← Equiv.tsum_eq (Equiv.mulLeft s⁻¹)]
      simp


    rw [← Summable.tsum_finsetSum]
    .
      simp_rw [← mul_assoc]
      simp_rw [mul_sub ((#S : ℝ)⁻¹ * _)]
      simp_rw [Finset.sum_sub_distrib]
      simp
      simp_rw [← mul_assoc]
      rw [mul_inv_cancel₀ (by apply S_card_ne_zero_re)]
      simp
      rename_bvar b → x
      conv =>
        rhs
        rhs
        rhs
        arg 1
        intro x
        rw [← neg_sub]
        rw [← Finset.mul_sum]
        rw [Finset.sum_equiv (Equiv.inv _) (s := S) (t := S) (g := fun s => g (s * x)) (by
          intro s
          simp
          nth_rw 2 [S_eq_Sinv]
          simp
        ) (by
          intro s
          simp
        )]


      rw [tsum_neg]
      simp
      rename_bvar b → x
      rw [← mul_two]
      simp_rw [mul_comm _ (f _), mul_assoc]
      simp_rw [← mul_sub]
      ring
    .
      intro s hs
      apply Summable.mul_left
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      clear foo
      wlog hg: g.support.Finite
      .
        apply Set.Finite.inter_of_left
        have hf := hgf
        simp [hg] at hf
        exact hf
      .
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset ?_ (Function.support_sub _ _)
        simp
        refine ⟨?_, hg⟩
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp
  .
  -- TODO - deduplicate this
      intro s hs
      apply Summable.mul_left
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      wlog hg: g.support.Finite
      .
        apply Set.Finite.inter_of_left
        have hf := hgf
        simp [hg] at hf
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hf
        . intro x hx
          simp
      .
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset ?_ (Function.support_sub _ _)
        simp
        refine ⟨hg, ?_⟩
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp
  .
    apply Summable.sub
    apply summable_of_finite_support
    .
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . apply Set.Finite.inter_of_left
        grind
      . apply Set.Finite.inter_of_right
        grind
    .
      simp_rw [mul_assoc]
      apply Summable.mul_left
      simp_rw [Finset.mul_sum]
      apply summable_sum
      intro s hs
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . rename_i hf
        apply Set.Finite.inter_of_left
        apply hf
      .
        rename_i hg
        apply Set.Finite.inter_of_right
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp
  .
    apply Summable.mul_left
    apply summable_sum
    intro s hs
    simp_rw [mul_sub]
    apply Summable.sub
    .
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . rename_i hf
        apply Set.Finite.inter_of_left
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hf
        . intro x hx
          simp
      . rename_i hg
        apply Set.Finite.inter_of_right
        apply hg
    .
      apply summable_of_finite_support
      unfold Function.HasFiniteSupport
      simp
      cases hgf
      . rename_i hf
        apply Set.Finite.inter_of_left
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hf
        . intro x hx
          simp
      . rename_i hg
        apply Set.Finite.inter_of_right
        rw [← Function.comp_def]
        rw [Function.support_comp_eq_preimage]
        apply Set.Finite.preimage'
        . apply hg
        . intro x hx
          simp


lemma laplace_prod_harmonic (f φ : G → ℝ)  (hf: Laplace_b  f = 0) (x: G): Laplace_b (f * φ) x = ((1 : ℝ) / (#(S) : ℝ)) * ∑ s ∈ S, f (s * x) * ((φ (x) - φ (s * x))) := by
  simp_rw [Laplace_b]
  simp_rw [f_conv_mu]
  simp
  simp_rw [Laplace_b] at hf
  conv =>
    rhs
    simp [mul_sub]
    simp [← Finset.sum_mul]

  simp_rw [f_conv_mu] at hf
  apply_fun (fun f => f x) at hf
  simp at hf
  rw [← mul_assoc]
  rw [sub_eq_zero] at hf
  rw [← hf]


end GeneratesNS

lemma group_fg_map {G G': Type*} [Group G] [Group G'] (H: Subgroup G) (h_fg: H.FG) (f: G →* G'): (Subgroup.map f H).FG := by
  obtain ⟨s, hs⟩ := h_fg
  classical
  rw [Subgroup.fg_iff]
  use s.image f
  refine ⟨?_, ?_⟩
  .
    rw [Finset.coe_image]
    rw [← MonoidHom.map_closure]
    rw [hs]
  . simp
    exact Set.toFinite (⇑f '' ↑s)
