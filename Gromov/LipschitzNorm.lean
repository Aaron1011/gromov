/-
Copyright (c) 2024 Aaron Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill
-/
module

public import Mathlib
public import Gromov.Defs

/-!
# The Lipschitz seminorm on `LipschitzH`

This file collects the Lipschitz seminorm `LipschitzSemiNorm` on functions `G → ℝ`, the basic
lemmas about it, and the resulting `SeminormedAddCommGroup` / `NormedSpace` instances on
`LipschitzH`. These instances are public so that they are available to downstream files.

Note that we only implement `SeminormedAddCommGroup` for `LipschitzH`, so this is only really a
seminormed space. The quotient space `W := LipschitzH ⧸ ConstF` is an actual normed space.
-/

public section

set_option linter.style.cdot false
set_option linter.style.whitespace false

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

@[expose]
noncomputable def LipschitzSemiNorm (f: G → ℝ): NNReal := sInf { k: NNReal | LipschitzWith k f }

lemma lipschiz_norm_zero: LipschitzSemiNorm  (0) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (0 : LipschitzH) } := by
    simp
  have sinf_le: sInf { k: NNReal | LipschitzWith k (0 : LipschitzH) } ≤ 0 := by
    exact csInf_le' zero_mem
  exact nonpos_iff_eq_zero.mp sinf_le


#synth IsStrictOrderedRing NNReal

-- TODO - upstream to mathlib
lemma lipschitz_attains_norm (f: G → ℝ) (hf: IsLipschitz f): LipschitzWith (LipschitzSemiNorm f) f := by
  by_contra!
  simp [LipschitzWith] at this
  obtain ⟨x, y, hdist⟩ := this
  have edist_ne_zero: edist x y ≠ 0 := by
    by_contra!
    rw [this] at hdist
    simp at this
    rw [this] at hdist
    simp at hdist

  have edist_not_top: edist x y ≠ ⊤ := by
    rw [edist_nndist]
    exact ENNReal.coe_ne_top

  rw [← ENNReal.lt_div_iff_mul_lt (by simp) (Or.inl edist_not_top)] at hdist
  simp [LipschitzSemiNorm] at hdist
  have isglb_sinf := isGLB_csInf (s := { k: NNReal | LipschitzWith k f }) (by
    obtain ⟨K, hK⟩ := hf
    use K
    simp
    exact hK
  ) (by simp)


  have between := IsGLB.exists_between (b := (edist (f x) (f y) / edist x y).toNNReal) isglb_sinf (by
    rw [edist_nndist]
    rw [edist_nndist]
    conv =>
      rhs
      equals (nndist (f x) (f y)) / (nndist x y) =>
        rw [← ENNReal.coe_div]
        simp
        exact ENNReal.coe_ne_zero.mp edist_ne_zero

    rw [edist_nndist] at hdist
    rw [edist_nndist] at hdist
    have edist_gt_zero: edist x y > 0 := by
      exact pos_of_ne_zero edist_ne_zero

    have x_ne_y := edist_pos.mp edist_gt_zero

    conv at hdist =>
      rhs
      equals ENNReal.ofNNReal ((nndist (f x) (f y)) / (nndist x y)) =>
        rw [ENNReal.coe_div]
        simp [x_ne_y]


    norm_cast at hdist
  )
  obtain ⟨D, lipschitz_d, sinf_le_d, d_lt_slope⟩ := between
  simp [LipschitzWith] at lipschitz_d
  specialize lipschitz_d x y
  rw [mul_comm] at lipschitz_d
  apply ENNReal.div_le_of_le_mul' at lipschitz_d
  repeat rw [edist_nndist] at lipschitz_d
  repeat rw [edist_nndist] at d_lt_slope
  rw [← ENNReal.coe_div] at lipschitz_d
  .
    norm_cast at lipschitz_d
    rw [← ENNReal.coe_div] at d_lt_slope
    .
      norm_cast at d_lt_slope
      apply not_lt_of_ge at lipschitz_d
      contradiction
    . rw [edist_nndist] at edist_ne_zero
      exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)
  . rw [edist_nndist] at edist_ne_zero
    exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)


lemma lipschitz_norm_triangle (x y z: G → ℝ) (hx: IsLipschitz x) (hy: IsLipschitz y) (hz: IsLipschitz z): LipschitzSemiNorm (x - z) ≤ LipschitzSemiNorm (x - y) + LipschitzSemiNorm (y - z) := by
  simp [LipschitzSemiNorm]
  conv =>
    pattern x - z
    equals (x - y) + (y - z) =>
      simp


  have sum_norm_mem: (LipschitzSemiNorm (x - y)) + (LipschitzSemiNorm (y - z)) ∈ { k: NNReal | LipschitzWith k ((x - y) + (y - z)) } := by
    simp only [LipschitzSemiNorm]
    apply LipschitzWith.add
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hx
      simp [IsLipschitz] at hy
      obtain ⟨X, hX⟩ := hx
      obtain ⟨Y, hY⟩ := hy
      use X + Y
      apply LipschitzWith.sub hX hY
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hy
      simp [IsLipschitz] at hz
      obtain ⟨Y, hY⟩ := hy
      obtain ⟨Z, hZ⟩ := hz
      use Y + Z
      apply LipschitzWith.sub hY hZ

  have sinf_le_sum := csInf_le (by simp) sum_norm_mem
  simp [LipschitzSemiNorm] at sinf_le_sum
  conv at sinf_le_sum =>
    pattern x - z
    equals (x - y) + (y - z) =>
      simp
  exact sinf_le_sum


lemma lipschitzH_norm_triangle (x y z: LipschitzH): LipschitzSemiNorm (x - z) ≤ LipschitzSemiNorm (x - y) + LipschitzSemiNorm (y - z) := by
  apply lipschitz_norm_triangle x y z x.lipschitz y.lipschitz z.lipschitz

lemma lipschitzWith_neg_iff {f : G → ℝ} {K : NNReal} : LipschitzWith K (-f) ↔ LipschitzWith K f :=
  ⟨fun h => by simpa using h.neg, LipschitzWith.neg⟩

lemma lipschitzSemiNorm_neg (f : G → ℝ) : LipschitzSemiNorm (-f) = LipschitzSemiNorm f := by
  unfold LipschitzSemiNorm
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, lipschitzWith_neg_iff]


set_option maxHeartbeats 1000000 in
noncomputable instance LipschitzH_seminorm: SeminormedAddCommGroup (LipschitzH) where
  norm := fun v => LipschitzSemiNorm v
  dist_self := by
    intro v
    simp [LipschitzSemiNorm]
    exact lipschiz_norm_zero
  dist_comm := by
    intro x y
    have key : LipschitzSemiNorm (⇑(-x + y)) = LipschitzSemiNorm (⇑(-y + x)) := by
      rw [← lipschitzSemiNorm_neg (⇑(-y + x))]
      congr 1
      ext a
      simp only [lipschitz_neg_tofun, lipschitz_add_tofun, LipschitzH_apply, Pi.add_apply,
        Pi.neg_apply]
      ring
    simpa using key
  dist_triangle := by
    intro x y z
    have key : LipschitzSemiNorm (⇑(-x + z)) ≤
        LipschitzSemiNorm (⇑(-x + y)) + LipschitzSemiNorm (⇑(-y + z)) := by
      have h := lipschitzH_norm_triangle z y x
      have e1 : (⇑(-x + z) : G → ℝ) = ⇑(z - x) := by
        ext a
        simp only [lipschitz_neg_tofun, lipschitz_add_tofun, lipschitz_sub_tofun, LipschitzH_apply,
          Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
      have e2 : (⇑(-x + y) : G → ℝ) = ⇑(y - x) := by
        ext a
        simp only [lipschitz_neg_tofun, lipschitz_add_tofun, lipschitz_sub_tofun, LipschitzH_apply,
          Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
      have e3 : (⇑(-y + z) : G → ℝ) = ⇑(z - y) := by
        ext a
        simp only [lipschitz_neg_tofun, lipschitz_add_tofun, lipschitz_sub_tofun, LipschitzH_apply,
          Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
      rw [e1, e2, e3, add_comm]
      exact h
    exact_mod_cast key

-- Note that we only implement SeminormedAddCommGroup for LipschitzH, so this is only
-- really a seminormed space. The quotient space W := LipschitzH ⧸ ConstF
-- is an actual normed space.
noncomputable instance LipschitzH_normed: NormedSpace ℝ (LipschitzH) where
  norm_smul_le := by
    intro c f
    simp [HSMul.hSMul, SMul.smul]
    simp [norm]
    conv =>
      lhs
      simp [LipschitzSemiNorm]
    norm_cast
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    )
    simp
    let K := LipschitzSemiNorm f
    have hK := lipschitz_attains_norm f (f.lipschitz)
    use ‖ (c * K) ‖₊
    simp
    have comp_mul_const := LipschitzWith.comp (Kf := ‖c‖₊) (Kg := K) (f := fun x => c • x) (g := f.toFun) (by apply lipschitzWith_smul) hK
    simp at comp_mul_const
    conv =>
      lhs
      arg 2
      simp [DFunLike.coe]
      equals (fun x ↦ c • x) ∘ f.toFun => rfl


    refine ⟨comp_mul_const, ?_⟩
    left
    simp [K]

lemma iterated_lipschitz_bound (f: LipschitzH): ∀ g: G, ‖f g‖ ≤ (LipschitzSemiNorm f + ‖f 1‖) * (1 + WordNorm g) := by
  intro g
  induction hg: WordNorm g using Nat.strong_induction_on generalizing g with
  | h n ih =>
    obtain ⟨l, l_prod, l_len⟩ := word_norm_prod _ _ hg
    simp [ProdS] at l_prod
    by_cases n_eq: n = 0
    .
      simp [n_eq]
      simp [n_eq] at l_len
      simp [l_len] at l_prod
      simp [← l_prod]
    .
      obtain ⟨head, tail, l_eq⟩ := List.exists_cons_of_length_pos (l := l) (by grind)
      have tail_norm := word_norm_le tail.unattach.prod tail (by simp [ProdS])
      specialize ih (WordNorm tail.unattach.prod) (by grind) tail.unattach.prod rfl
      rw [← l_prod, l_eq]
      simp
      have foo := lipschitz_attains_norm f.toFun f.lipschitz
      unfold LipschitzWith at foo
      have s_dist := foo (head * tail.unattach.prod) tail.unattach.prod
      rw [edist_dist] at s_dist
      conv at s_dist =>
        rhs
        equals ENNReal.ofReal (LipschitzSemiNorm f *  (dist (↑head * tail.unattach.prod) tail.unattach.prod)) =>
          rw [ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
          rw [edist_dist]
          .
            rfl
          . simp
      rw [ENNReal.ofReal_le_ofReal_iff] at s_dist
      .
        apply norm_le_norm_add_const_of_dist_le at s_dist
        simp only [Real.norm_eq_abs] at s_dist
        grw [s_dist]
        simp [DFunLike.coe] at ih
        grw [ih]
        rw [dist_comm]
        grw [dist_word_mul_le]
        .
          simp [dist, WordDist, word_norm_one]
          grw [tail_norm]
          have tail_len_le: tail.length ≤ n - 1 := by
            grind
          grw [tail_len_le]
          norm_cast
          rw [Nat.add_sub_of_le (by grind)]
          simp [DFunLike.coe]
          ring
          norm_cast
          conv =>
            lhs
            lhs
            arg 1
            equals (LipschitzSemiNorm f.toFun) * (n + 1) =>
              ring
          nth_rw 2 [add_comm]
          simp
          norm_cast
          simp
          rw [mul_add]
          simp
        . simp
      . positivity
        
end GeneratesNS
