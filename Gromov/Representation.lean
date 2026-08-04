module

public import Mathlib
public import Gromov.ToMathlib.GroupTheory.CosetCover
public import Gromov.Complexification
public import Gromov.Defs
public import Gromov.Harmonic
public import Gromov.UnitaryGromov
public import Gromov.UnipotentGromov
public import Gromov.NilpotentFinite
public import Gromov.ToMathlib.GroupTheory.Closure
public import Gromov.ToMathlib.Data.ENNReal.Basic
public import Gromov.ToMathlib.Data.List.Finite
public import Gromov.ToMathlib.Algebra.Group.Pointwise.Finset
public import Gromov.Laplace

/-!
# The representation of `G` on `W`

The space `W = LipschitzH ⧸ ConstF`, the representation `GRep` / `GRepW` of `G` on it, and the
fact that it preserves the quotient norm.
-/

public section

set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

-- `LipschitzH_seminorm` and `LipschitzH_normed` are public instances in
-- `Gromov.LipschitzNorm`, so they are already available here.

-- The lift of LipschitzSemiNorm to W, using a proof that LipschitzSemiNorm doesn't depend on the choice representative
-- (adding a constant to a Lipschitz function doesn't change its Lipschitz constant)


lemma lipschitz_norm_const (z: ℝ): LipschitzSemiNorm (ConstLipschitzH z) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (ConstLipschitzH z).toFun } := by
    simp [ConstLipschitzH]
  have my_le := csInf_le (by simp) zero_mem
  exact nonpos_iff_eq_zero.mp my_le


lemma constf_eq_null: (ConstF : Set (LipschitzH)) = nullAddSubgroup (LipschitzH) := by
  unfold ConstF
  unfold nullAddSubgroup
  ext f
  simp
  refine ⟨?_, ?_⟩
  .
    intro hf
    obtain ⟨z, hz⟩ := hf
    rw [← hz]
    simp [norm]
    apply lipschitz_norm_const
  .
    intro hf
    simp [norm, LipschitzSemiNorm] at hf
    have lipschitz_zero := lipschitz_attains_norm f (f.lipschitz)
    simp [LipschitzSemiNorm] at lipschitz_zero
    rw [hf] at lipschitz_zero
    simp [LipschitzWith] at lipschitz_zero
    use (f.toFun 1)
    simp [ConstLipschitzH]
    ext a
    simp
    apply lipschitz_zero

@[expose]
instance const_isClosed: IsClosed (ConstF : Set (LipschitzH)) := by
  rw [constf_eq_null]
  exact isClosed_nullAddSubgroup


#synth NormedSpace ℝ (W )
#synth NormedAddCommGroup (W )

#synth TopologicalSpace (W)


set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 9000000

-- The space 'GL(W)' of invertible continuous linear functions from W to W
abbrev GL_W := (W →L[ℝ] W)ˣ

-- The space 'GL(W)' of invertible continuous linear functions from W to W


#synth NormedRing (((W →L[ℝ] W)))

#synth NormedAddCommGroup (((W →L[ℝ] W)))


#synth FiniteDimensional ℝ (((W →L[ℝ] W)))

-- Homeomorph.isCompact_preimage

@[expose]
instance proper_linear_w: ProperSpace (((W →L[ℝ] W))) := FiniteDimensional.proper_rclike ℝ (((W →L[ℝ] W)))


#synth FiniteDimensional ℝ (LipschitzH)
#synth TopologicalSpace (LipschitzH)
#synth BorelSpace (((W →L[ℝ] W)))

#synth ProperSpace (((W →L[ℝ] W)))


@[expose]
def GRep: Representation ℝ G (LipschitzH)  := {
  toFun := fun g => {
    toFun := gAct g
    map_add' := by
      intro f h
      ext a
      simp [gAct]
    map_smul' := by
      intro c f
      ext a
      simp [gAct]
  }
  map_one' := by
    ext f a
    simp [gAct]
  map_mul' := by
    intro g h
    ext f a
    simp [gAct]
    simp [mul_assoc]
}


--attribute [-instance] QuotientModule.Quotient.topologicalSpace

-- We start with a map from G into the space of (not necessarily invertible) linear maps from W to W
@[expose]
def GRepW_non_invertible: Representation ℝ G (W) := Representation.quotient (GRep) ConstF (by
  intro g
  intro f hf
  simp
  simp [ConstF]
  simp [ConstF] at hf
  obtain ⟨K, hK⟩ := hf
  use K
  ext a
  simp [GRep]
  rw [← hK]
  rw [gAct_const]
)

-- We then build a map from G into the group of invertible linear maps from W to W
@[expose]
noncomputable def GRepW_base := Representation.asGroupHom GRepW_non_invertible


-- GRep just translates functions by g⁻¹, so it preserves the Lipschitz operator norm
lemma GRep_preserves_norm (g: G) (f: LipschitzH): ‖(GRep g) f‖ = ‖f‖ := by
  simp [GRep]
  simp [norm]
  nth_rw 1 [LipschitzSemiNorm]
  rw [gAct]
  simp [DFunLike.coe]
  conv =>
    lhs
    arg 1
    arg 1
    intro k
    equals (LipschitzWith k (f.toFun ∘ (fun y => (y * g)))) =>
      rfl

  have comp := LipschitzWith.comp (f := f.toFun) (g := fun y => (y * g)) (Kf := (LipschitzSemiNorm ⇑f)) (Kg := 1) ?_ ?_
  rotate_left 1
  . apply lipschitz_attains_norm
    exact f.lipschitz
  .
    simp [LipschitzWith]

  have norm_mem: (LipschitzSemiNorm f) ∈ { k: NNReal | LipschitzWith k (f.toFun ∘ (fun y => (y * g))) } := by
    simp
    simp at comp
    exact comp


  apply le_antisymm
  .
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    ) norm_mem
  .
    apply le_csInf
    .
      apply Set.nonempty_of_mem (x := (LipschitzSemiNorm ⇑f)) norm_mem
    . intro b hb
      simp at hb
      simp [LipschitzSemiNorm]
      apply csInf_le
      .
        simp [BddBelow]
        apply Set.nonempty_of_mem (x := 0)
        rw [mem_lowerBounds]
        simp
      . simp
        simp [LipschitzWith] at hb
        simp [LipschitzWith]
        intro x y
        specialize hb (x * g⁻¹) (y * g⁻¹)
        simp at hb
        grw [hb]


-- Takes in an invertible linear map from W to W, and produces a *continuous* linear map from W to W
@[expose]
noncomputable def GRepW: (W →ₗ[ℝ] W)ˣ →* (W →L[ℝ] W)ˣ := {
  toFun := fun f => {
    val := LinearMap.toContinuousLinearMap f.val
    inv := LinearMap.toContinuousLinearMap f.inv
    val_inv := by
      have old_inv := f.val_inv
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
    inv_val := by
      have old_inv := f.inv_val
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
  }
  map_one' := by
    ext a
    simp
  map_mul' := by
    intro f g
    ext a
    simp
}


#synth Group (GL_W)

lemma quotient_norm_eq_norm (f: LipschitzH): ‖(Submodule.Quotient.mk f : W)‖ = ‖f‖ := by
  conv =>
    lhs
    equals ‖(QuotientAddGroup.mk f : (LipschitzH ⧸ ConstF.toAddSubgroup))‖ =>
      rfl
  rw [QuotientAddGroup.norm_mk]
  simp [Metric.infDist]
  have hzero : (0 : LipschitzH) ∈ (↑ConstF : Set LipschitzH) :=
    SetLike.mem_coe.mpr (Submodule.zero_mem ConstF)
  have hconst : ∀ y ∈ (↑ConstF : Set LipschitzH), edist f y = (‖f‖₊ : ENNReal) := by
    intro y hy
    simp [ConstF] at hy
    obtain ⟨a, ha⟩ := hy
    simp [edist, PseudoMetricSpace.edist]
    simp [LipschitzSemiNorm]
    simp [LipschitzWith]
    simp_rw [← ha]
    simp [ConstLipschitzH]
    rfl
  have hinf : Metric.infEDist f (↑ConstF : Set LipschitzH) = (‖f‖₊ : ENNReal) := by
    apply le_antisymm
    · calc Metric.infEDist f (↑ConstF : Set LipschitzH) ≤ edist f 0 :=
            Metric.infEDist_le_edist_of_mem hzero
        _ = (‖f‖₊ : ENNReal) := hconst 0 hzero
    · rw [Metric.le_infEDist]
      exact fun y hy => (hconst y hy).ge
  rw [hinf]
  simp

#synth NormedRing (W →L[ℝ] W)
#synth TopologicalSpace (W →L[ℝ] W)ˣ


lemma GLW_preseves_norm (g: G) (w: W): ‖(GRepW (GRepW_base g)).val w‖ = ‖w‖ := by
  have exists_v: ∃ v, Submodule.Quotient.mk v = w := by
    apply Quotient.exists_rep
  obtain ⟨v, hv⟩ := exists_v
  simp [GRepW, GRepW_base, GRepW_non_invertible]
  nth_rw 1 [← hv]
  rw [Representation.asGroupHom_apply]
  simp only [Representation.quotient_apply, Submodule.mapQ_apply]
  rw [quotient_norm_eq_norm]
  rw [GRep_preserves_norm]
  rw [← hv]
  rw [quotient_norm_eq_norm]


lemma GRepW_norm_le (g: G): ‖(GRepW (GRepW_base g)).val‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff]
  . simp [GLW_preseves_norm]
  . simp


set_option synthInstance.maxHeartbeats 500000


@[expose]
noncomputable def rho_g := (GRepW_base).range


@[expose]
def isembedding_units_val := Units.isEmbedding_val_mk' (M := (W →L[ℝ] W)) (f := ContinuousLinearMap.inverse) (by
  intro x hx
  have foo := ContDiffAt.continuousAt (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (e := x) (n := 0) (by
    simp at hx
    obtain ⟨u, hu⟩ := hx
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := u.inv)
    .
      simp
      have mul_inv := u.val_inv
      dsimp [HMul.hMul, Mul.mul] at mul_inv
      rw [hu] at mul_inv
      exact mul_inv
    . simp
      have inv_val := u.inv_val
      dsimp [HMul.hMul, Mul.mul] at inv_val
      rw [hu] at inv_val
      exact inv_val
  ))
  apply ContinuousAt.continuousWithinAt
  exact foo
  -- ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
) (by
  intro u
  have mul_inv := u.val_inv
  dsimp [HMul.hMul, Mul.mul] at mul_inv
  apply ContinuousLinearMap.inverse_eq
  . exact u.val_inv
  . exact u.inv_val
)

#synth NormedSpace ℝ (W →L[ℝ] W)
#synth MetricSpace (W →L[ℝ] W)


-- All norms are equivalent on finite-dimensional spaces:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/FiniteDimension.html

-- Section 3.3 in Vikmanm, "Construction of a representation"
-- This is a combination of Cartan's Theorem and Theorem 3.6, giving us the conclusion that
-- ρ(G) contains an abelian subgroup of finite index


--borelize (W →L[ℝ] W)ˣ


-- (dropped a `#synth ContinuousMul (W →L[ℝ] W)` diagnostic here: it only resolves at a
-- raised `maxSynthPendingDepth`. The instance itself *is* needed -- see
-- `rho_g_contains_abelian`, which raises the depth for exactly this reason -- but a bare
-- `#synth` is not worth carrying a build-wide option for.)


#synth NormedAddCommGroup (W)

#synth FiniteDimensional ℝ (W)


-- WRONG?: We want the topology to come from our metric space 'GL_W_psuedoMetric', not from the units

-- We actualy want the topology to be the induced topology from the space of (not necessarily invertible) linear maps from W to W
--attribute [-instance] Units.instTopologicalSpaceUnits


#synth TopologicalSpace (W)


--attribute [-instance] QuotientModule.Quotient.topologicalSpace
@[expose]
def FreshTopology (V: Type*) := V
instance (V: Type*) [base_group: Group V]: Group (FreshTopology V) := base_group
instance (V: Type*) [base_comm: AddCommGroup V]: AddCommGroup (FreshTopology V) := base_comm
instance (V: Type*) [AddCommGroup V] [base_module: Module ℝ V]: Module ℝ (FreshTopology V) := base_module
@[expose]
instance (V: Type*) [AddCommGroup V] [Module ℝ V]  [base_finite: FiniteDimensional ℝ V]: FiniteDimensional ℝ (FreshTopology V) := base_finite


#synth CStarAlgebra ((ℂ →L[ℂ] ℂ))

#synth AddCommMonoid (W)

@[expose]
instance T2_W: T2Space (W) := TopologicalSpace.t2Space_of_metrizableSpace

#synth T2Space (W)


#synth TopologicalSpace (W →L[ℝ] W)
#synth FiniteDimensional ℝ (W →L[ℝ] W)

@[expose]
noncomputable def G_SPolyData {d: ℕ} (h_poly: HasPolynomialGrowthD hGS.S d): SPolyData (T := G) ⊤ := {
  S := Subgroup.topEquiv.symm.toMonoidHom '' hGS.S
  S_finite := by
    apply Set.Finite.image
    simp
  S_one := by
    simp
    apply hGS.one_mem
  S_inv := by
    rw [← Set.image_inv]
    nth_rw 1 [S_eq_Sinv]
    simp
  S_generates := by
    rw [← MonoidHom.map_closure]
    have foo := hGS.generates
    simp at foo
    simp [foo]

  S_poly_const := h_poly.choose
  S_poly_const_pos := by
    by_contra!
    have foo := h_poly.choose_spec
    simp [← this] at foo
    specialize foo 1 (by simp)
    simp at foo
    have S_nonempty := hGS.hS
    simp at S_nonempty
    grind
  S_poly_deg := d
  S_poly := by
    have foo := h_poly.choose_spec
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      specialize foo r hr
      simpa using foo
    . simp
}


-- Theorem 3.8 in Vikman

end GeneratesNS
