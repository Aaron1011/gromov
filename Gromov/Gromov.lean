import Mathlib
import Gromov.ToMathlib.GroupTheory.CosetCover
import Gromov.ToMathlib.GroupTheory.FiniteAbelian.Basic
import Gromov.Complexification
import Gromov.Defs
import Gromov.Harmonic
import Gromov.UnitaryGromov
import Gromov.UnipotentGromov
import Gromov.NilpotentFinite

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

-- `LipschitzH_seminorm` and `LipschitzH_normed` are public instances in
-- `Mathlib.Algebra.Group.Gromov.LipschitzNorm`, so they are already available here.

-- The lift of LipschitzSemiNorm to W, using a proof that LipschitzSemiNorm doesn't depend on the choice representative
-- (adding a constant to a Lipschitz function doesn't change its Lipschitz constant)
noncomputable def LipschitzSemiNorm_w (w: W) := Quotient.lift ((fun f => LipschitzSemiNorm f.toFun)) (by
  intro f g hfg
  replace hfg := ConstF.quotientRel_def.mp hfg
  simp [ConstF] at hfg
  obtain ⟨k, hk⟩ := hfg
  have f_eq_g_k: f = g + (ConstLipschitzH k) := by
    exact Eq.symm (add_eq_of_eq_sub' hk)
  rw [f_eq_g_k]
  simp [LipschitzSemiNorm]
  simp [LipschitzWith]
  simp_rw [edist_eq_enorm_sub]
  simp [ConstLipschitzH]
) w



--#synth TopologicalSpace (LipschitzH)
--def myInst := Submodule.Quotient.normedAddCommGroup (S := ConstF)

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

--#synth LieGroup (modelWithCornersSelf ℂ ((W →L[ℝ] W))) 1 (GL_W)
--#synth TopologicalSpace ((W →L[ℝ] W))
--#synth TopologicalSpace ((W →L[ℝ] W))ˣ


#synth NormedRing (((W →L[ℝ] W)))

#synth NormedAddCommGroup (((W →L[ℝ] W)))

lemma opnorm_continuous: Continuous fun (f: (W →L[ℝ] W)) => ‖f‖ := by
  apply continuous_norm

#synth FiniteDimensional ℝ (((W →L[ℝ] W)))

-- Homeomorph.isCompact_preimage

instance proper_linear_w: ProperSpace (((W →L[ℝ] W))) := FiniteDimensional.proper_rclike ℝ (((W →L[ℝ] W)))


--#synth NormedSpace ℂ (GL_W)
--#synth MetricSpace (GL_W)


#synth FiniteDimensional ℝ (LipschitzH)
#synth TopologicalSpace (LipschitzH)
#synth BorelSpace (((W →L[ℝ] W)))

#synth ProperSpace (((W →L[ℝ] W)))



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
set_option trace.profiler true in
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

-- noncomputable def GRepW_Multiplicative: (W →ₗ[ℝ] W) →* (Multiplicative (GL_W)) := {
--   toFun := fun f => Multiplicative.ofAdd (GRepW f)
--   map_one' := by
--     simp
--   map_mul' := by
--     intro f g
--     ext
--     simp [DFunLike.coe]
--     simp [ContinuousLinearMap.toFun_eq_coe]
--     simp [ContinuousLinearMap.mul_apply]
-- }

#synth Group (GL_W)

lemma quotient_norm_eq_norm (f: LipschitzH): ‖(Submodule.Quotient.mk f : W)‖ = ‖f‖ := by
  have foo := QuotientAddGroup.norm_mk (S := ConstF.toAddSubgroup) f
  conv =>
    lhs
    equals ‖(QuotientAddGroup.mk f : (LipschitzH ⧸ ConstF.toAddSubgroup))‖ =>
      rfl
  rw [QuotientAddGroup.norm_mk]
  simp [Metric.infDist]
  -- goal: (Metric.infEDist f ↑ConstF).toReal = ‖f‖
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
  --rw [Submodule.mapQ_apply]
  rw [quotient_norm_eq_norm]
  rw [GRep_preserves_norm]
  rw [← hv]
  rw [quotient_norm_eq_norm]


lemma GRepW_norm_le (g: G): ‖(GRepW (GRepW_base g)).val‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff]
  . simp [GLW_preseves_norm]
  . simp
  -- apply ContinuousLinearMap.opNorm_eq_of_bounds (by simp)
  -- . simp [GLW_preseves_norm]
  -- . intro n hn
  --   simp [GLW_preseves_norm]
  --   intro x

  --   by_contra!
  --   unfold W at x
  --   specialize x (Submodule.Quotient.mk (ConstLipschitzH 1))
  --   simp at hn
  --   by_cases n_eq_zero: n = 0
  --   .
  --     simp [n_eq_zero] at x

  --   have mul_lt := mul_lt_of_lt_one_left (a := ‖((Submodule.Quotient.mk (ConstLipschitzH 1)) : W)‖) (b := n) (by linarith)
  -- rw [ContinuousLinearMap.norm_def]
  -- simp [GLW_preseves_norm]


--#synth CompleteSpace (W)

    --infer_instance

lemma continuous_GRepW : Continuous (fun g => GRepW (GRepW_base g)) := by
  fun_prop

set_option synthInstance.maxHeartbeats 500000

lemma continous_of_map (v: W): Continuous (fun (r: (W →L[ℝ] W)ˣ) => r.val v) := by
  apply Continuous.comp (g := (fun r => r v)) (f := (fun (r : (W →L[ℝ] W)ˣ) => r.val))
  -- TODO - how does this work???
  . exact Continuous.clm_apply continuous_id' continuous_const
  . apply Units.continuous_val




-- The image of G under our representation: ρ(G) in the Vikman paper
--noncomputable def rho_g := ((GRepW).restrict ((GRepW_base).range)).range

noncomputable def rho_g := (GRepW_base).range

--noncomputable instance GL_W_TopologicalSpace: TopologicalSpace (GL_W) := TopologicalSpace.induced Units.val (by infer_instance)
--noncomputable instance GL_W_PseudoMetricSpace: PseudoMetricSpace (GL_W) := Topology.IsInducing.comapPseudoMetricSpace (f := Units.val) (by apply Topology.IsInducing.induced)


--def rho_g_closure := _root_.closure (rho_g).carrier

-- instance GL_W_proper: ProperSpace (GL_W) := by
--   unfold GL_W
--   apply FiniteDimensional.proper

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

--#synth MeasurableSpace (W →L[ℝ] W)ˣ
--#synth TopologicalSpace (W →L[ℝ] W)ˣ
--#synth BorelSpace (W →L[ℝ] W)




--borelize (W →L[ℝ] W)ˣ

--#synth BorelSpace (Units.val '' (rho_g).carrier)

#synth ContinuousMul (W →L[ℝ] W)


#synth NormedAddCommGroup (W)

#synth FiniteDimensional ℝ (W)

--#synth CompleteSpace (W)

--#synth IsBoundedSMul ℂ (LipschitzH)



--end lipschitz_norm



-- WRONG?: We want the topology to come from our metric space 'GL_W_psuedoMetric', not from the units

-- We actualy want the topology to be the induced topology from the space of (not necessarily invertible) linear maps from W to W
--attribute [-instance] Units.instTopologicalSpaceUnits

--instance Units_subtype_Topology {T: Type*} [Monoid T] [TopologicalSpace T]: TopologicalSpace (T)ˣ := TopologicalSpace.induced Units.val (by infer_instance)


#synth TopologicalSpace (W)


--attribute [-instance] QuotientModule.Quotient.topologicalSpace
def FreshTopology (V: Type*) := V
instance (V: Type*) [base_group: Group V]: Group (FreshTopology V) := base_group
instance (V: Type*) [base_comm: AddCommGroup V]: AddCommGroup (FreshTopology V) := base_comm
instance (V: Type*) [AddCommGroup V] [base_module: Module ℝ V]: Module ℝ (FreshTopology V) := base_module
instance (V: Type*) [AddCommGroup V] [Module ℝ V]  [base_finite: FiniteDimensional ℝ V]: FiniteDimensional ℝ (FreshTopology V) := base_finite
-- instance (V: Type*) [base_topology: TopologicalSpace V]: TopologicalSpace (FreshTopology V) := base_topology
-- instance (V: Type*) [TopologicalSpace V] [AddCommGroup V] [base_add: IsTopologicalAddGroup V]: IsTopologicalAddGroup (FreshTopology V) := base_add
-- #synth Group (FreshTopology (W →L[ℝ] W)ˣ)

--instance proper_fresh_topology [TopologicalSpace (FreshTopology (W))]: ProperSpace ((((FreshTopology (W)) →L[ℂ] (FreshTopology (W))))) := FiniteDimensional.proper_rclike ℝ (((W →L[ℝ] W)))

#synth CStarAlgebra ((ℂ →L[ℂ] ℂ))

#synth AddCommMonoid (W)

instance T2_W: T2Space (W) := TopologicalSpace.t2Space_of_metrizableSpace

#synth T2Space (W)


#synth TopologicalSpace (W →L[ℝ] W)
#synth FiniteDimensional ℝ (W →L[ℝ] W)

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
set_option maxHeartbeats 500000 in
lemma theorem_3_8 {V: Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (H: Subgroup (V →L[ℂ] V)ˣ) [DecidableEq H] (h_compact: CompactSpace H) (G: Subgroup H) (G_fg: G.FG) (S_data: SPolyData G): ∃ A: Subgroup G, IsMulCommutative A ∧ A.FiniteIndex := by
  obtain ⟨H', ⟨H_equiv_H'⟩⟩ := new_weyl_unitarian_trick (V := V) (H := H)
  --let first := Subgroup.map H'.subtype.restrict_range (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  let G' := Subgroup.map H'.subtype (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  let my_hom := MonoidHom.ofInjective (f := H'.subtype) (by exact subtype_injective H')
  let other := Subgroup.map my_hom.toMonoidHom (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  --let other' := other.toMonoidHom.restrict

  let reverse := Subgroup.comap H'.subtype


  let G'_to_G: G' →* G := {
    toFun := fun g => (by
      use ⟨H_equiv_H' (my_hom.symm ⟨g, by (
        have g_prop := g.property
        simp only [G'] at g_prop
        rw [Subgroup.mem_map] at g_prop
        obtain ⟨x, x_mem, g_eq⟩ := g_prop
        rw [← g_eq]
        simp
      )⟩), by (
        simp [my_hom]
      )⟩
      simp [my_hom]
      have g_prop := g.property
      simp only [G'] at g_prop
      rw [Subgroup.mem_map] at g_prop
      obtain ⟨x, x_mem, g_eq⟩ := g_prop
      simp_rw [← g_eq]
      rw [Subgroup.mem_map] at x_mem
      obtain ⟨y, y_mem, x_eq⟩ := x_mem
      simp_rw [← x_eq]
      simp [MonoidHom.ofInjective, MulEquiv.ofBijective, Equiv.ofBijective, Function.surjInv]
      exact y_mem
    )
    map_one' := by simp
    map_mul' := by
      intro a b
      conv =>
        enter [1, 1, 1, 1, 2, 2]
        equals ⟨a.val, (by
          have a_prop := a.property
          simp only [G'] at a_prop
          rw [Subgroup.mem_map] at a_prop
          obtain ⟨x, x_mem, a_eq⟩ := a_prop
          rw [← a_eq]
          simp
        )⟩ * ⟨b.val, (by
          have b_prop := b.property
          simp only [G'] at b_prop
          rw [Subgroup.mem_map] at b_prop
          obtain ⟨y, y_mem, b_eq⟩ := b_prop
          rw [← b_eq]
          simp
        )⟩ =>
          rfl

      simp_rw [MulEquiv.map_mul]
      rfl
  }

  have G'_fg: G'.FG := by
    simp [G']
    apply group_fg_map
    apply group_fg_map
    exact G_fg

  by_cases dim_le_one: Module.finrank ℂ (V) ≤ 1
  .
    use ⊤
    refine ⟨?_, ?_⟩
    .

      have map_dim := Module.finrank_linearMap ℂ ℂ V V
      -- TODO - is there an easier way to prove this?
      have map_dim_le_one: Module.finrank ℂ (V →ₗ[ℂ] V) ≤ 1 := by
        rw [map_dim]
        by_cases dim_eq_zero: Module.finrank ℂ (V) = 0
        . simp [dim_eq_zero]
        . simp at dim_eq_zero
          have dim_eq_one: Module.finrank ℂ (V) = 1 := by omega
          simp [dim_eq_one]

      rw [finrank_le_one_iff] at map_dim_le_one
      obtain ⟨v, v_span⟩ := map_dim_le_one
      refine { is_comm := ?_ }
      refine { comm := ?_ }
      intro x y
      ext a
      simp
      obtain ⟨p, hx⟩ := v_span x.val.val.val
      obtain ⟨q, hy⟩ := v_span y.val.val.val

      -- TODO - upstream to mathlib
      have clm_apply (f: V →L[ℂ] V) (v: V): f v = f.toLinearMap v := rfl
      rw [clm_apply]
      rw [clm_apply]
      rw [clm_apply]
      rw [clm_apply]

      rw [← hx, ← hy]
      simp
      rw [smul_comm]
    . infer_instance
  .
    have dim_ge_two: 2 ≤ Module.finrank ℂ (V) := by omega

    let new_S_data := map_S_data G (f := H'.subtype.comp (H_equiv_H'.symm.toMonoidHom)) S_data
    obtain ⟨N, N_comm, N_finite_index⟩ := compact_lie_virtually_abelian (Module.finrank ℂ V) (by omega) G' G'_fg (by
      unfold G'
      rw [Subgroup.map_map]
      exact new_S_data
    )

    let new_N := N
    simp [G'] at new_N
    --let new_N' := H'.subtype


    let new_N' := Subgroup.map G'.subtype N

    let new_N' := Subgroup.map G'_to_G N
    use new_N'
    refine ⟨?_, ?_⟩
    .
      simp [new_N']
      apply Subgroup.map_isMulCommutative
    .
      simp [new_N']
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map_of_injective]
      . simp
        refine ⟨?_, ?_⟩
        . exact N_finite_index.index_ne_zero
        . conv =>
            arg 1
            arg 1
            arg 1
            equals ⊤ =>
              rw [MonoidHom.range_eq_top]
              simp [G'_to_G]
              intro a
              simp
              use H'.subtype (H_equiv_H'.symm a)
              simp [my_hom]
              use ?_
              . simp [MonoidHom.ofInjective, MulEquiv.ofBijective, Equiv.ofBijective, Function.surjInv]
              . simp [G']
                use a.val
                use ?_
                . simp
                . simp

          simp
      .
        simp [G'_to_G]
        intro a b hab
        simpa using hab

instance rho_g_FG: Group.FG (rho_g) := by
  have fg_grep: Group.FG ↥(GRepW_base).range := by
    apply Group.fg_range
  unfold rho_g
  apply Group.fg_range

-- TODO - deduplicate with 'map_S_Data'
def map_range_S_data {G H: Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H] {f: G →* H} (S_data: SPolyData (T := G) ⊤): SPolyData f.range := {
  S := (f.rangeRestrict.comp (Subgroup.topEquiv.toMonoidHom)) '' S_data.S
  S_finite := by
    apply Set.Finite.image
    apply S_data.S_finite
  S_one := by
    simp only [Set.mem_image]
    use 1
    simp
    apply S_data.S_one
  S_inv := by
    rw [← Set.image_inv]
    rw [← S_data.S_inv]
  S_generates := by
    rw [← MonoidHom.map_closure]
    rw [S_data.S_generates]
    rw [Subgroup.map_top_of_surjective]
    simp
    apply MonoidHom.rangeRestrict_surjective
  S_poly_const := S_data.S_poly_const
  S_poly_const_pos := S_data.S_poly_const_pos
  S_poly_deg := S_data.S_poly_deg
  S_poly := by
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      apply S_data.S_poly r hr
    . exact S_data.S_finite
}

def map_equiv_S_data {A B: Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B] {G: Subgroup A} {H: Subgroup B} (f: G ≃* H) (S_data: SPolyData G): SPolyData H := {
  S := f.toMonoidHom '' S_data.S
  S_finite := by
    apply Set.Finite.image
    apply S_data.S_finite
  S_one := by
    simp only [Set.mem_image]
    use 1
    simp
    apply S_data.S_one
  S_inv := by
    rw [← Set.image_inv]
    rw [← S_data.S_inv]
  S_generates := by
    rw [← MonoidHom.map_closure]
    rw [S_data.S_generates]
    rw [Subgroup.map_top_of_surjective]
    simp
    exact MulEquiv.surjective f
  S_poly_const := S_data.S_poly_const
  S_poly_const_pos := S_data.S_poly_const_pos
  S_poly_deg := S_data.S_poly_deg
  S_poly := by
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      apply S_data.S_poly r hr
    . exact S_data.S_finite
}


--#synth NormedAddCommGroup (W)

/-- The real-inner-product-space version of `theorem_3_8`: a finitely generated, polynomial-growth
subgroup of the units of a compact linear group over `ℝ` is virtually abelian.  We reduce to the
complex `theorem_3_8` by complexifying (`Cx.unitsMapHom`) just before the unitary machinery. -/
lemma theorem_3_8_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (H : Subgroup (V →L[ℝ] V)ˣ) [DecidableEq H]
    (h_compact : CompactSpace H) (G : Subgroup H) (G_fg : G.FG) (S_data : SPolyData G) :
    ∃ A : Subgroup G, IsMulCommutative A ∧ A.FiniteIndex := by
  classical
  have φ_inj : Function.Injective (Cx.unitsMapHom (V := V)) := Cx.unitsMapHom_injective
  have φ_cont : Continuous (Cx.unitsMapHom (V := V)) := Cx.unitsMapHom_continuous
  let Hc : Subgroup ((Cx V →L[ℂ] Cx V)ˣ) := Subgroup.map Cx.unitsMapHom H
  let e : H ≃* Hc := Subgroup.equivMapOfInjective H Cx.unitsMapHom φ_inj
  let Gc : Subgroup Hc := Subgroup.map e.toMonoidHom G
  let eG : G ≃* Gc := MulEquiv.subgroupMap e G
  have Gc_fg : Gc.FG := group_fg_map G G_fg e.toMonoidHom
  have Sc : SPolyData Gc := map_equiv_S_data eG S_data
  have hc : CompactSpace Hc := by
    have hH : IsCompact ((H : Set (V →L[ℝ] V)ˣ)) := by
      have h1 := (isCompact_univ (X := ↥H)).image continuous_subtype_val
      rwa [Set.image_univ, Subtype.range_coe] at h1
    have h2 : IsCompact ((Hc : Set (Cx V →L[ℂ] Cx V)ˣ)) := by
      have := hH.image φ_cont
      rwa [← Subgroup.coe_map] at this
    exact isCompact_iff_compactSpace.mp h2
  obtain ⟨A, A_comm, A_fi⟩ := theorem_3_8 (V := Cx V) Hc hc Gc Gc_fg Sc
  refine ⟨Subgroup.map eG.symm.toMonoidHom A, ?_, ?_⟩
  · exact Subgroup.map_isMulCommutative A eG.symm.toMonoidHom
  · rw [Subgroup.finiteIndex_iff, Subgroup.index_map_of_injective A eG.symm.injective,
      eG.symm.toMonoidHom.range_eq_top.mpr eG.symm.surjective, Subgroup.index_top, mul_one]
    exact A_fi.index_ne_zero

open scoped RealInnerProductSpace in
attribute [-simp] Subgroup.map_toSubmonoid in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 600000 in
--set_option trace.Meta.synthInstance true in
lemma rho_g_contains_abelian {d: ℕ} (hd: HasPolynomialGrowthD S d) : ∃ M: Subgroup ((rho_g)), IsMulCommutative M ∧ M.FiniteIndex := by
  classical
  let my_map := Subgroup.subtype (rho_g)
  have W_equiv: (W) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin <| Module.finrank ℝ W) := LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin.symm



  unfold GL_W at my_map
  -- TODO - is there a simpler way to get an arbitrary inner product space?
  let inner_prod_core: InnerProductSpace.Core ℝ (FreshTopology (W)) := {
    inner := fun v w => ⟪W_equiv v, W_equiv w⟫,
    conj_inner_symm := by intro x y; simp [real_inner_comm],
    re_inner_nonneg := by
      exact fun x ↦ inner_self_nonneg
    add_left := by
      intro x y z
      have key : ∀ a b : FreshTopology (W), W_equiv (a + b) = W_equiv a + W_equiv b :=
        fun a b => map_add W_equiv a b
      rw [key, inner_add_left]
    smul_left := by
      intro x y r
      have key : ∀ (c : ℝ) (a : FreshTopology (W)), W_equiv (c • a) = c • W_equiv a :=
        fun c a => map_smul W_equiv c a
      rw [key, inner_smul_left]
    definite := by
      intro x hx
      simpa using hx
  }

  let temp_inner := InnerProductSpace.ofCore inner_prod_core.toCore
  let add_comm := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := (FreshTopology (W)))

  let normed_space := InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ) (F := (FreshTopology (W)))

  have proper_space: ProperSpace (FreshTopology (W)) := FiniteDimensional.proper_rclike ℝ _

  have fresh_t2: T2Space (FreshTopology (W)) := TopologicalSpace.t2Space_of_metrizableSpace


  let plain_linear_to_clm: (((W)) →ₗ[ℝ] ((W)))ˣ →* (((W)) →L[ℝ] ((W)))ˣ := {
    toFun := fun f => {
      val := LinearMap.toContinuousLinearMap f.val
      inv := LinearMap.toContinuousLinearMap f.inv
      val_inv := by
        have old_inv := f.val_inv
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
      inv_val := by
        have old_inv := f.inv_val
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
    }
    -- TODO - why is a normal `simp` so slow here?
    map_one' := by
      ext a
      simp only []
      rfl
    map_mul' := by
      intro f g
      ext a
      simp only []
      rfl
  }

  let linear_to_clm: ((FreshTopology (W)) →ₗ[ℝ] (FreshTopology (W)))ˣ →* ((FreshTopology (W)) →L[ℝ] (FreshTopology (W)))ˣ := {
    toFun := fun f => {
      val := LinearMap.toContinuousLinearMap f.val
      inv := LinearMap.toContinuousLinearMap f.inv
      val_inv := by
        have old_inv := f.val_inv
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
      inv_val := by
        have old_inv := f.inv_val
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
    }
    -- TODO - why is a normal `simp` so slow here?
    map_one' := by
      ext a
      simp only []
      rfl
    map_mul' := by
      intro f g
      ext a
      simp only []
      rfl
  }


  have plain_linear_to_clm_preserves_norm (g: G) (w: (W)): ‖(plain_linear_to_clm (GRepW_base g)).val w‖ = ‖w‖ := by
    simp [plain_linear_to_clm]
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


  let my_range := (linear_to_clm.comp GRepW_base).range

  have fresh_complete: CompleteSpace (FreshTopology (W)) := by apply complete_of_proper (α := FreshTopology (W))

  have locally_compact_map: LocallyCompactSpace ((FreshTopology (W)) →L[ℝ] (FreshTopology (W))) := locallyCompact_of_proper
  have units_locally:  LocallyCompactSpace ((FreshTopology (W)) →L[ℝ] (FreshTopology (W)))ˣ := by
    exact Units.isOpenEmbedding_val.locallyCompactSpace



  -- TODO - generalize to LinearMap/ContinuousLinearMap
  have units_val_embedding: Topology.IsEmbedding (Units.val (α := ((FreshTopology (W)) →L[ℝ] (FreshTopology (W))))) := by
    apply Units.isEmbedding_val_mk' (f := fun g => g.inverse)
    . intro a ha
      apply (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := 1) ?_).continuousAt.continuousWithinAt
      simp at ha
      obtain ⟨b, hb⟩ := ha
      use ContinuousLinearEquiv.ofUnit b
      rw [← hb]
      rfl
    . intro u
      have u_unit: IsUnit u.val := by
        use u
      apply ContinuousLinearMap.inverse_eq
      .
        have u_val_inv := u.val_inv
        rw [ContinuousLinearMap.mul_def] at u_val_inv
        -- TODO - avoid the unfold somehow
        unfold Inv.inv
        unfold Units.instInv
        simp only []
        rw [u_val_inv]
        rfl
      .
        unfold Inv.inv
        unfold Units.instInv
        simp only []
        have u_inv_val := u.inv_val
        rw [ContinuousLinearMap.mul_def] at u_inv_val
        rw [u_inv_val]
        rfl


  let my_new_range := ((GRepW).comp GRepW_base).range
  unfold rho_g


  have continuous_mul: ContinuousMul ((W) →L[ℝ] (W)) := by
    infer_instance

  have is_topological: IsTopologicalGroup ((W) →L[ℝ] (W))ˣ := by
    infer_instance

  let plain_units_metric: MetricSpace (((W)) →L[ℝ] ((W)))ˣ := by
    apply Topology.IsEmbedding.comapMetricSpace (f := Units.val)
    exact isembedding_units_val

  let units_metric: MetricSpace ((FreshTopology (W)) →L[ℝ] (FreshTopology (W)))ˣ := by
    apply Topology.IsEmbedding.comapMetricSpace (f := Units.val)
    apply units_val_embedding



  have fresh_equiv: W ≃L[ℝ] FreshTopology (W) := ContinuousLinearEquiv.ofFinrankEq (rfl)

  let to_fresh (f: (W) ≃ₗ[ℝ] (W)): (FreshTopology (W)) ≃ₗ[ℝ] (FreshTopology (W)) := f
  let new_map_entry (f: (W →L[ℝ] W)ˣ): ((FreshTopology W) →L[ℝ] (FreshTopology W))ˣ := {
    val := ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv f.val,
    inv := ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv f.inv
    val_inv := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv ((f.val * f.inv) (fresh_equiv.symm a))) =>
          rfl
      simp
    inv_val := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv ((f.inv * f.val) (fresh_equiv.symm a))) =>
          rfl
      simp
  }

  let new_map_entry_inv (f: ((FreshTopology W) →L[ℝ] (FreshTopology W))ˣ ): (W →L[ℝ] W)ˣ  := {
    val := (ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv).symm f.val,
    inv := (ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv).symm f.inv
    val_inv := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv.symm ((f.val * f.inv) (fresh_equiv a))) =>
          rfl
      simp
    inv_val := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv.symm ((f.inv * f.val) (fresh_equiv a))) =>
          rfl
      simp
  }

  let to_continuous_hom: (FreshTopology (W) →ₗ[ℝ] FreshTopology (W)) →* (FreshTopology (W) →L[ℝ] FreshTopology (W)) := {
    toFun := fun f => f.toContinuousLinearMap,
    map_one' := by
      ext a
      simp
    map_mul' := by
      intro a b
      rfl
    }

  let new_map_hom: (W →L[ℝ] W)ˣ ≃* ((FreshTopology W) →L[ℝ] (FreshTopology W))ˣ := {
    toFun := new_map_entry,
    invFun := new_map_entry_inv,
    left_inv := by
      simp [Function.LeftInverse]
      intro x
      ext a
      simp [new_map_entry, new_map_entry_inv]
    right_inv := by
      simp [Function.RightInverse]
      intro x
      ext a
      simp [new_map_entry, new_map_entry_inv]
    map_mul' := by
      intro f g
      simp [new_map_entry]
      ext a
      simp
  }


  let mapped_group := Subgroup.map new_map_hom.toMonoidHom my_new_range.topologicalClosure

  have my_new_range_compact: CompactSpace my_new_range.topologicalClosure := by
    refine { isCompact_univ := ?_ }
    rw [Subtype.isCompact_iff]
    rw [Topology.IsEmbedding.isCompact_iff (f := Units.val) ?_]
    . rw [Metric.isCompact_iff_isClosed_bounded]
      refine ⟨?_, ?_⟩
      . apply IsSeqClosed.isClosed
        by_contra!
        simp [IsSeqClosed] at this
        obtain ⟨seq, seq_in, ⟨lim_seq, seq_tendsto_lim_seq, lim_seq_not_mem⟩⟩ := this

        by_cases lim_seq_invertible: IsUnit lim_seq.toLinearMap
        .
          -- If the limit (in the space of linear maps) is invertible, then the limit will also exist in the space
          -- of units, which will then imply that the limit exists in the space of linear maps.
          -- TODO - this probably can be a direct proof, rather than by contradiction
          obtain ⟨u, hu⟩ := lim_seq_invertible
          have closure_closed := Subgroup.isClosed_topologicalClosure my_new_range
          apply IsClosed.isSeqClosed at closure_closed
          dsimp [IsSeqClosed] at closure_closed

          have seq_units: ∀ n: ℕ, IsUnit (seq n) := by
            intro n
            obtain ⟨x, x_mem, seq_eq_x⟩ := (seq_in n)
            rw [← seq_eq_x]
            apply Units.isUnit

          have lim_units := closure_closed (x := fun n => (seq_units n).unit) (p := plain_linear_to_clm u) ?_ ?_
          .
            specialize lim_seq_not_mem (plain_linear_to_clm u) lim_units
            conv at lim_seq_not_mem =>
              arg 1
              lhs
              equals u.val.toContinuousLinearMap =>
                rfl
            rw [hu] at lim_seq_not_mem
            conv at lim_seq_not_mem =>
              arg 1
              lhs
              equals lim_seq =>
                rfl
            simp at lim_seq_not_mem
          . intro n
            simp
            have seq_n := seq_in n
            obtain ⟨x, x_mem, seq_eq_x⟩ := seq_n
            simp_rw [← seq_eq_x]
            simpa using x_mem
          .
            rw [Topology.IsEmbedding.tendsto_nhds_iff (g := Units.val)]
            .
              conv =>
                arg 1
                equals seq =>
                  rfl

              have to_clm_u: plain_linear_to_clm u = u.val.toContinuousLinearMap := by
                rfl

              have u_val_eq_lim: u.val.toContinuousLinearMap = lim_seq := by
                rw [hu]
                rfl

              rw [to_clm_u, u_val_eq_lim]
              exact seq_tendsto_lim_seq
            .
              exact isembedding_units_val


        -- If the limit (in the space of linear maps) is not invertible, then it has a non-trivial kernel.
        rw [LinearMap.isUnit_iff_ker_eq_bot] at lim_seq_invertible
        apply Submodule.exists_mem_ne_zero_of_ne_bot at lim_seq_invertible
        obtain ⟨v, v_in_ker, v_ne_zero⟩ := lim_seq_invertible
        simp at v_in_ker


        have eval_at := Filter.Tendsto.eval_const seq_tendsto_lim_seq v
        have norm_tendsto := Continuous.tendsto (f := fun (x: W) => ‖x‖) (by fun_prop) (lim_seq v)
        have norm_seq_lim := Filter.Tendsto.comp norm_tendsto eval_at
        rw [v_in_ker] at norm_seq_lim
        rw [norm_zero] at norm_seq_lim
        conv at norm_seq_lim =>
          arg 1
          -- Use the fact that the action preserves the euclidian norm (maybe just up to a constant),
          -- so the sequence is actually constant
          equals fun x => ‖v‖ =>
            funext n
            simp
            have seq_mem := seq_in n
            obtain ⟨x, x_mem, seq_eq_x⟩ := seq_mem
            rw [← seq_eq_x]
            apply ContinuousWithinAt.eq_const_of_mem_closure (f := fun (x: ((W) →L[ℝ] (W))ˣ) => ‖x.val v‖) (c := ‖v‖) (x := x) (s := my_new_range)
            . apply Continuous.continuousWithinAt
              fun_prop
            . exact x_mem
            . intro y hy
              simp [my_range] at hy
              obtain ⟨g, rep_g_eq_y⟩ := hy
              rw [← rep_g_eq_y]
              apply plain_linear_to_clm_preserves_norm

        -- TODO - why do we need this?
        have r_t2: T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace

        have tendsto_norm_v := tendsto_const_nhds (α := ℕ) (f := Filter.atTop) (x := ‖v‖)
        have norm_v_zero := tendsto_nhds_unique tendsto_norm_v norm_seq_lim
        simp at norm_v_zero
        contradiction
      .
        simp
        apply LipschitzWith.isBounded_image (f := Units.val) (K := 1)
        . rw [lipschitzWith_iff_dist_le_mul]
          intro a b
          simp
          rfl
        .
          apply Bornology.IsBounded.closure
          rw [Metric.isBounded_iff_subset_ball 1]
          use 3
          intro a ha
          simp [my_new_range] at ha
          obtain ⟨g, rep_g_eq_a⟩ := ha
          simp
          conv =>
            lhs
            equals dist (a.val) (ContinuousLinearMap.id _ _) =>
              rfl
          grw [dist_le_norm_add_norm]
          grw [ContinuousLinearMap.norm_id_le]
          rw [← rep_g_eq_a]
          grw [GRepW_norm_le]
          norm_num
        -- Bornology.isBounded_image_subtype_val
    . exact isembedding_units_val




  have continuous_new_map_entry: Continuous new_map_entry := by
    simp [new_map_entry]
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    . fun_prop
    . fun_prop

  --have compact_map := IsCompact.image my_range_compact.isCompact_univ (f := new_map_hom)

  have compact_mapped_group: CompactSpace mapped_group := by
    have h1 : IsCompact (my_new_range.topologicalClosure : Set (W →L[ℝ] W)ˣ) :=
      isCompact_iff_compactSpace.mpr my_new_range_compact
    have hcont : Continuous (⇑new_map_hom.toMonoidHom) := by
      simp [new_map_hom]
      apply continuous_new_map_entry
    have h2 := h1.image hcont
    rw [← Subgroup.coe_map] at h2
    exact isCompact_iff_compactSpace.mp h2

  let map_sub_equiv := (Subgroup.subgroupOfEquivOfLe (H := map new_map_hom.toMonoidHom my_new_range) (K := mapped_group) (by
    unfold mapped_group
    simp
    rw [Subgroup.map_le_map_iff]
    apply le_sup_of_le_left
    exact le_topologicalClosure my_new_range
  )).symm

  have S_data_range := map_range_S_data (f := (GRepW.comp GRepW_base)) (G_SPolyData hd)
  have mapped_S_data := map_S_data (f := new_map_hom.toMonoidHom) _ S_data_range
  have final_data := map_equiv_S_data map_sub_equiv mapped_S_data


  let data := theorem_3_8_real (H := mapped_group) compact_mapped_group ((Subgroup.map new_map_hom.toMonoidHom my_new_range).subgroupOf mapped_group) ?_ (final_data)
  obtain ⟨B, B_abelian, B_finite_index⟩ := data

  let reverse_hom: ((map new_map_hom.toMonoidHom my_new_range).subgroupOf mapped_group) →* (GRepW_base).range := {
    toFun := fun g => (
      ((⟨Units.map (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom) (new_map_hom.symm g.val), by (
        simp
        have g_prop := g.property
        rw [Subgroup.mem_subgroupOf] at g_prop
        rw [Subgroup.mem_map] at g_prop
        obtain ⟨x, x_mem, g_eq⟩ := g_prop
        simp [my_new_range] at x_mem
        obtain ⟨a, ha⟩ := x_mem
        use a
        ext f
        simp
        apply_fun (fun h => Units.map (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom) h) at ha
        simp [GRepW] at ha
        rw [ha]
        simp [new_map_hom, new_map_entry_inv]
        rw [← g_eq]
        simp [new_map_hom, new_map_entry]
      )⟩) : GRepW_base.range)
    ),
    map_one' := by
      simp [map_one]
    map_mul' := by
      intro a b
      apply Subtype.ext
      show (Units.map _) (new_map_hom.symm ↑↑(a * b)) =
        (Units.map _) (new_map_hom.symm ↑↑a) * (Units.map _) (new_map_hom.symm ↑↑b)
      rw [← map_mul (Units.map _), ← map_mul new_map_hom.symm]
      norm_cast
  }

  have reverse_hom_ker_bot: reverse_hom.ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    intro a b hab
    simp only [reverse_hom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq] at hab
    apply Units.map_injective at hab
    .
      replace hab := new_map_hom.symm.injective hab
      exact Subtype.ext (Subtype.ext hab)
    .
      intro a b hab
      simpa using hab

  have reverse_hom_range_top: reverse_hom.range = ⊤ := by
    simp [reverse_hom]
    rw [Subgroup.eq_top_iff']
    intro x
    simp
    use new_map_entry (plain_linear_to_clm x.val)
    use ?_
    .
      use ?_
      . have hrt : ∀ y, new_map_hom.symm (new_map_entry y) = y := new_map_hom.left_inv
        refine Subtype.ext ?_
        change (Units.map (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ) (M₁ := W)).toMonoidHom)
            (new_map_hom.symm (new_map_entry (plain_linear_to_clm ↑x))) = x.val
        rw [hrt]
        ext f
        rfl
      .
        rw [Subgroup.mem_subgroupOf]
        . simp [my_new_range]
          have x_prop := x.property
          rw [MonoidHom.mem_range] at x_prop
          obtain ⟨g, hg⟩ := x_prop
          use g
          simp [new_map_hom, new_map_entry]
          ext f
          rw [← hg]
          rfl
    .
      simp [mapped_group, my_new_range]
      have x_prop := x.property
      rw [MonoidHom.mem_range] at x_prop
      obtain ⟨g, hg⟩ := x_prop
      use (plain_linear_to_clm x.val)
      refine ⟨?_, ?_⟩
      .
        have mem_range: plain_linear_to_clm ↑x ∈ (GRepW.comp GRepW_base).range := by
          simp
          use g
          rw [← hg]
          rfl
        apply Subgroup.le_topologicalClosure (GRepW.comp (GRepW_base)).range mem_range
      . rfl



  let B' := Subgroup.map reverse_hom B
  use B'
  refine ⟨?_, ?_⟩
  . simp only [B']
    apply Subgroup.map_isMulCommutative
  . simp only [B']
    rw [Subgroup.finiteIndex_iff]
    rw [Subgroup.index_map]
    rw [reverse_hom_ker_bot, reverse_hom_range_top, sup_bot_eq, Subgroup.index_top, mul_one]
    exact B_finite_index.index_ne_zero
  .
    have base_fg: (map new_map_hom.toMonoidHom my_new_range).FG := by
      apply group_fg_map
      simp [my_new_range]
      have group_fg: Group.FG (GRepW.comp (GRepW_base)).range := by
        apply Group.fg_range
      exact (Group.fg_iff_subgroup_fg (GRepW.comp GRepW_base).range).mp group_fg

    have base_le: (map new_map_hom.toMonoidHom my_new_range) ≤ mapped_group := by
      intro a ha
      simp at ha
      simp [mapped_group]
      obtain ⟨g, g_mem, g_eq_a⟩ := ha
      use g
      refine ⟨?_, g_eq_a⟩
      apply Subgroup.le_topologicalClosure my_new_range g_mem



    rw [Subgroup.fg_iff]
    rw [Subgroup.fg_iff] at base_fg
    obtain ⟨S, S_eq, S_finite⟩ := base_fg

    have S_in_map: ∀ s ∈ S, s ∈ (map new_map_hom.toMonoidHom my_new_range) := by
      rw [Subgroup.ext_iff] at S_eq
      intro s hs
      apply (S_eq s).mp ?_
      exact Subgroup.mem_closure.mpr fun K a ↦ a hs

    let S' := Set.range (fun (s: S) => (⟨s.val, base_le (S_in_map s s.property)⟩ : mapped_group))
    use S'
    -- TODO - this is a huge mess. This can be a general proof about the closure of Subgroup.subgroupOf
    refine ⟨?_, ?_⟩
    .
      simp only [S']
      rw [← S_eq]
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        rw [Subgroup.mem_subgroupOf]
        simp at ha
        induction ha using Subgroup.closure_induction_left with
        | one => simp
        | mul_left y hy z hz h_other_z =>
          simp
          apply Subgroup.mul_mem
          . simp at hy
            obtain ⟨p, p_mem, p_eq_y⟩ := hy
            rw [← p_eq_y]
            simp
            apply Subgroup.mem_closure_of_mem p_mem
          . exact h_other_z
        | inv_mul_cancel y hy z hz h_other_z =>
          simp
          apply Subgroup.mul_mem
          . simp
            simp at hy
            obtain ⟨p, p_mem, p_eq_y⟩ := hy
            rw [← p_eq_y]
            simp
            apply Subgroup.mem_closure_of_mem p_mem
          . exact h_other_z
      . intro ha
        rw [Subgroup.mem_subgroupOf] at ha
        rw [Subgroup.mem_closure]
        intro K hK
        rw [Subgroup.mem_closure] at ha
        have a_mem := ha (Subgroup.map mapped_group.subtype K) ?_
        . simpa using a_mem
        . simp
          intro s hs
          rw [Set.range_subset_iff] at hK
          have s_mem := hK ⟨s, hs⟩
          simp
          simp at s_mem
          use ?_
          apply base_le (S_in_map s hs)
    .
      simp [S']
      rw [← Set.finite_coe_iff] at S_finite
      apply Set.finite_range

-- We need this to work with Finset
noncomputable instance GL_W_DecidableEq: DecidableEq (GL_W) := by
  apply Classical.typeDecidableEq

noncomputable instance w_map_DecidableEq: DecidableEq (W →ₗ[ℝ] W) := by
  apply Classical.typeDecidableEq



-- The input data and proofs for Theorem 3.1 in Vikman
omit hGS in
structure Theorem3_1_Input (G: Type*) [Group G] where
  -- A finite index subgroup G' of G
  G': Subgroup G
  finite_index: G'.FiniteIndex
  -- G' can be mapped homomorphically onto ℤ
  φ: (Additive G') →+ ℤ
  hφ: Function.Surjective φ





#synth Group.FG (rho_g)




lemma g_hom_abelian {T: Type*} [Group T] (A: Subgroup G) (A_finite_index: A.FiniteIndex) (hom: A →* T) (hom_surjective: Function.Surjective hom) (H: Subgroup T) (H_infinite: Infinite H) (H_abeliean: IsMulCommutative H) (H_finite_index: H.FiniteIndex) (H_FG: Group.FG H): Nonempty (Theorem3_1_Input G) := by
  -- TODO - generalize this to a lemma: finite-index subgroup of an infinite group is infinite
  -- and upstream to mathlib


  --have h_commgroup: CommGroup H := by
  --  apply CommGroup.ofIsMulCommutative

  --have h_fg: Group.FG H := by
  --  apply

    --infer_instance
  --have h_fg_comm: @Group.FG ↥H CommGroup.toGroup := by
  --  dsimp [CommGroup.toGroup]
  --  exact h_fg




  -- TODO - figure out how to make instance inference work here
  obtain ⟨i, j, i_fin, j_fin, p, p_prime, e, exists_iso⟩ := @CommGroup.equiv_free_prod_directSum_zmod H (haveI := H_abeliean; { (inferInstance : Group H) with mul_comm := mul_comm' }) (H_FG)
  have iso := Classical.choice exists_iso

  have j_nonempty: Nonempty j := by
    by_contra!
    simp [this] at iso
    have H_finite : Finite H := by
      rw [Equiv.finite_iff iso.toEquiv]
      have finite_i: Finite i := by
        infer_instance
      have finite_mul: ∀ f: i, Finite (Multiplicative (ZMod (p f ^ e f))) := by
        intro f
        simp [Multiplicative]
        have pow_ne_zero: NeZero (p f ^ e f) := by
          exact {
            out := by
              simp
              have first_ne_zero := Nat.Prime.ne_zero (p_prime f)
              simp [first_ne_zero]
          }
        apply Finite.of_fintype
      apply Finite.instProd
    have no_finite := H_infinite.not_finite
    contradiction

  -- TODO - can we get the comp '∘' syntax to give us a monoid hom, instead of a plain function?
  let h_to_z := (Pi.evalMonoidHom _ (Classical.choice (by
    exact j_nonempty
  ))).comp ((MonoidHom.fst _ _).comp iso.toMonoidHom)

  have h_to_z_surjective: Function.Surjective h_to_z := by
    unfold h_to_z
    simp
    apply Function.Surjective.comp
    .
      intro x
      simp
      use fun _ => x
    . apply Function.Surjective.comp
      . exact Prod.fst_surjective
      . exact iso.surjective



  -- Interpret H as a subgroup of GL_W
  --let H_as_GL_W := Subgroup.map (Subgroup.subtype (hom.range)) H
  let G' := Subgroup.comap hom H
  have H_index_ne_zero := H_finite_index.index_ne_zero

  -- TODO - generalize this and PR to mathlib
  have rangerestrict_range: hom.rangeRestrict.range = ⊤ := by
    ext a
    simp
    have a_prop := a.property
    rw [MonoidHom.mem_range] at a_prop
    obtain ⟨x, hx⟩ := a_prop
    use x
    use x.property
    rw [Subtype.ext_iff]
    simp
    exact hx



  have G'_finite_index: G'.FiniteIndex := by
    unfold G'
    exact {
      index_ne_zero := by
        simp
        rw [Subgroup.index_comap]
        -- apply somehow found this - how does it work???
        exact Subgroup.FiniteIndex.index_ne_zero
    }



  -- TODO - there must be an easier way to do this
  let g'_to_h: (map A.subtype G') →* H := {
    toFun := fun g => ⟨hom ⟨g.val, by (
      -- TODO - clean this up
      have foo := g.property
      rw [Subgroup.mem_map] at foo
      obtain ⟨x, hx, a_subtype⟩ := foo
      rw [← a_subtype]
      simp
    )⟩, by (
      have g_prop := g.property
      simp only [G', Subgroup.mem_comap] at g_prop
      rw [Subgroup.mem_map] at g_prop
      obtain ⟨x, hx, a_subtype⟩ := g_prop
      simp_rw [← a_subtype]
      simp
      simp at hx
      exact hx
    )⟩
    map_one' := by
      simp
      conv =>
        lhs
        arg 2
        equals 1 => simp
      simp

    map_mul' := by
      simp
      intro a ha a_mem b hb b_mem

      conv =>
        lhs
        arg 2
        equals ⟨a, ha⟩ * ⟨b, hb⟩ => simp
      rw [MonoidHom.map_mul]
  }

  let additive_g'_to_h := g'_to_h.toAdditive
  let additive_h_to_z := h_to_z.toAdditive

  let g_to_additive_z := additive_h_to_z.comp additive_g'_to_h
  let g_to_z := (AddEquiv.additiveMultiplicative ℤ).toAddMonoidHom.comp g_to_additive_z


  apply Nonempty.intro
  exact {
    G' := Subgroup.map A.subtype G',
    finite_index := by
      rw [Subgroup.finiteIndex_iff]
      simp [Subgroup.index_map_subtype]
      refine ⟨?_, ?_⟩
      . rw [← ne_eq]
        rw [← Subgroup.finiteIndex_iff]
        exact G'_finite_index
      . exact A_finite_index.index_ne_zero
      -- G'_finite_index
    φ := g_to_z,
    hφ := by
      simp [g_to_z, g_to_additive_z]
      apply Function.Surjective.comp
      . simp [additive_h_to_z]
        exact h_to_z_surjective
      .
        simp [additive_g'_to_h, g'_to_h]
        intro h
        obtain ⟨a, hom_a⟩ := hom_surjective h
        simp
        use a
        simp
        simp [G', hom_a]
  }

#print axioms g_hom_abelian

-- Case 1 in Section 3.3 of Vikman, where the representation ρ(G) is infinite
lemma rho_g_case_infinite {d: ℕ} (hd: HasPolynomialGrowthD S d) (hr: Infinite (↥(rho_g))): Nonempty (Theorem3_1_Input G) := by
  obtain ⟨H, H_abelian, H_finite_index⟩ := rho_g_contains_abelian hd


  have h_fg: Group.FG H := by
    apply Subgroup.fg_of_index_ne_zero

  let top_equiv := Subgroup.topEquiv (G := G)
  let top_comp := (GRepW_base).comp top_equiv.toMonoidHom
  let g_rho := (GRepW_base).rangeRestrict.comp top_equiv.toMonoidHom



  --let H' := top_equiv.toMonoidHom
  --let other_H' := H'.range

  have target := g_hom_abelian ⊤ (by infer_instance) (g_rho) ?_ (H) ?_ ?_ ?_ ?_
  . exact target
  .
    simp [g_rho]
    exact MonoidHom.rangeRestrict_surjective GRepW_base
  .
    dsimp [MonoidHom.range]
    unfold rho_g at hr
    have card_mul := Subgroup.card_mul_index H
    unfold rho_g at card_mul
    nth_rw 2 [Nat.card_eq_zero_of_infinite] at card_mul
    rw [Nat.mul_eq_zero] at card_mul
    replace card_mul := card_mul.resolve_right H_finite_index.index_ne_zero
    rw [Nat.card_eq_zero] at card_mul
    simp at card_mul
    exact card_mul
  . exact H_abelian
  . exact H_finite_index
  . exact h_fg

#print axioms rho_g_case_infinite


instance G_Add_MeasureableSingleton: MeasurableSingletonClass (Additive G) := {
  measurableSet_singleton := by
    intro x
    apply IsOpen.measurableSet
    simp
}

instance G_MeasureableSingleton: MeasurableSingletonClass (G) := {
  measurableSet_singleton := by
    intro x
    apply IsOpen.measurableSet
    simp
}


-- lemma conv_lp2 (f g: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): MemLp (Conv f g) 2 := by
--   unfold Conv
--   have foo := ENNReal.eLpNorm_top_convolution_le
--     (L := (ContinuousLinearMap.mul ℝ ℝ))
--     (f := fun (x: Additive (MulOpposite G)) => f x.toMul.unop)
--     (g := fun (x: Additive (MulOpposite G)) => g x.toMul.unop)
--     (p := 2) (q := 2)
--     (μ := myHaarAddOpp)
--     (by
--       simp [ENNReal.HolderConjugate]
--       exact {
--         inv_add_inv_eq_inv := by field_simp
--       }
--     )
--     (by apply AEMeasurable.of_discrete)
--     (by apply AEMeasurable.of_discrete) 1
--     (by simp)
--   simp at foo





lemma lt_top_mul {a b c : ENNReal} (hab: a ≤ b * c) (hb: b < ⊤) (hc: c < ⊤) : a < ⊤ := by
  have b_c_not_top: b * c < ⊤ := by
    apply WithTop.mul_lt_top (hb) (hc)
  grw [hab]
  exact b_c_not_top


-- lemma conv_exists_lp1 (f g: G → ℝ)
--   (hf: MeasureTheory.MemLp ((fun x => f x.toMul)) 1 myHaarAddOpp)
--   (hg: ∀ y: G, MeasureTheory.MemLp ((fun x => g x.toMul)) 1 myHaarAddOpp)
--   : ConvExists f g := by

--   apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 1) (q := 1) (μ := myHaarAddOpp) (by
--     simp [ENNReal.HolderConjugate]
--     exact {
--       inv_add_inv_eq_inv := by field_simp
--     }
--   )
--     -- (f := fun a => f (MulOpposite.unop (Additive.toMul a)))
--     -- (g := fun a => g ((MulOpposite.unop (Additive.toMul a))))
--     -- (hf := AEMeasurable.of_discrete)
--     -- (hg := AEMeasurable.of_discrete)
--     -- (by simp [ENNReal.HolderConjugate])
--     -- (by simp [ENNReal.HolderConjugate])

--   have young_bound := ENNReal.eLpNorm_convolution_le_enorm_mul
--     (f := fun a => f (MulOpposite.unop (Additive.toMul a)))
--     (g := fun a => g ((MulOpposite.unop (Additive.toMul a))))
--     (L := (ContinuousLinearMap.mul ℝ ℝ))
--     (r := 1)
--     (p := 1)
--     (q := 1)
--     (μ := myHaarAddOpp)
--     (by simp)
--     (by simp)
--     (by simp)
--     (by simp)
--     (by apply AEMeasurable.of_discrete)
--     (by apply AEMeasurable.of_discrete)

--   have young_lt_top := lt_top_mul young_bound ?_ ?_
--   .
--     simp [eLpNorm, eLpNorm'] at young_lt_top
--     --

--     unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
--     intro z
--     refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
--     unfold MeasureTheory.HasFiniteIntegral
--     simp [MeasureTheory.convolution] at young_lt_top
--     simp

--     rw [WithTop.lt_top_iff_ne_top] at young_lt_top
--     apply MeasureTheory.measure_eq_top_of_lintegral_ne_top _ at young_lt_top
--     rw [my_add_haar_eq_count] at young_lt_top
--     rw [MeasureTheory.Measure.count_eq_zero_iff] at young_lt_top
--     simp only [enorm_ne_top] at young_lt_top




--   unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
--   intro g
--   refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
--   unfold MeasureTheory.HasFiniteIntegral
--   simp [eLpNorm, eLpNorm'] at young_bound
--   --simp [MeasureTheory.convolution] at young_bound
--   grw [young_bound]



--   unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
--   intro x
--   simp only [toMul_sub, MulOpposite.unop_div, ContinuousLinearMap.mul_apply']
--   refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
--   unfold MeasureTheory.HasFiniteIntegral
--   grw [ENNReal.eLpNorm_convolution_le_enorm_mul]


lemma conv_exists (p q : ℝ) (hp: 0 < p) (hq: 0 < q) (hpq: p.HolderConjugate q) (f g: G → ℝ)
  (hf: MeasureTheory.MemLp ((fun x => f x.toMul)) (ENNReal.ofReal p) myHaarAddOpp)
  (hg: ∀ y: G, MeasureTheory.MemLp ((fun x => g (y / x.toMul))) (ENNReal.ofReal q) myHaarAddOpp)
  : ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
  intro x
  simp only [toMul_sub, MulOpposite.unop_div, ContinuousLinearMap.mul_apply']
  refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
  unfold MeasureTheory.HasFiniteIntegral
  simp
  have holder_bound := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.Measure.count) (hpq)
    (AEMeasurable.of_discrete) (AEMeasurable.of_discrete)
    (f := fun a => ‖f ( (Additive.toMul a))‖ₑ)
    (g := fun a => ‖g ((Additive.toMul x) / ((Additive.toMul a)))‖ₑ)
  simp at holder_bound
  rw [my_add_haar_eq_count]

  have p_ne_zero: ENNReal.ofReal p ≠ 0 := by
    simp [hp]


  have p_ge_zero: 0 ≤ p := by
    linarith

  have q_ge_zero: 0 ≤ q := by
    linarith

  have q_ne_zero: ENNReal.ofReal q ≠ 0 := by
    simp
    linarith

  have integral_lt_top := ne_top_of_le_ne_top (?_) holder_bound
  . exact Ne.lt_top' (id (Ne.symm integral_lt_top))
  . apply WithTop.mul_ne_top
    .
      have foo := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top p_ne_zero (by simp) (MeasureTheory.MemLp.eLpNorm_lt_top hf)
      rw [my_add_haar_eq_count] at foo
      rw [ENNReal.toReal_ofReal p_ge_zero] at foo
      apply ENNReal.rpow_ne_top_of_nonneg (?_) ?_
      . simp only [inv_nonneg]
        linarith
      . exact LT.lt.ne_top foo
    .

      have foo := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top q_ne_zero (by simp) (MeasureTheory.MemLp.eLpNorm_lt_top (hg x.toMul))
      rw [my_add_haar_eq_count] at foo
      rw [ENNReal.toReal_ofReal q_ge_zero] at foo
      apply ENNReal.rpow_ne_top_of_nonneg (?_) ?_
      . simp only [inv_nonneg]
        linarith
      .
        exact LT.lt.ne_top foo





open MeasureTheory

-- TODO - figure out why we need these
instance Real.t2Space: T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
instance Real.firstCountable: FirstCountableTopology ℝ := TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology


-- Old stuff for two LP_2 function - might be useful later
    -- unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
    -- have my_exists := conv_exists  (p := 2) (q := 2) (by simp) (by simp) (by exact Real.HolderConjugate.two_two) f (delta s) hf ?_
    -- .
    --   intro x
    --   exact MeasureTheory.ConvolutionExistsAt.integrable (my_exists x)
    -- .
    --   intro x
    --   unfold delta
    --   apply Continuous.memLp_of_hasCompactSupport
    --   . exact continuous_of_discreteTopology
    --   .
    --     unfold HasCompactSupport
    --     rw [isCompact_iff_finite]
    --     dsimp [tsupport]
    --     rw [closure_discrete]

    --     apply Set.Finite.subset (s := {opAdd (x * s⁻¹)}) (by simp)
    --     intro a ha
    --     dsimp [Pi.single, Function.update] at ha
    --     simp at ha
    --     simp [opAdd]
    --     rw [← ha]
    --     simp





-- Copied from https://github.com/leanprover/lean4/blob/6741444a63eec253a7eae7a83f1beb3de015023d/src/Init/Data/List/OfFn.lean#L81
theorem ofFn_succ_last (α: Type*) {n} {f : Fin (n + 1) → α} :
    List.ofFn f = (List.ofFn fun i => f i.castSucc) ++ [f (Fin.last n)] := by
  induction n with
  | zero => simp [List.ofFn_succ]
  | succ n ih =>
    rw [List.ofFn_succ]
    conv => rhs; rw [List.ofFn_succ]
    rw [ih]
    simp


lemma list_prod_eq {T : Type*} [Mul T] [One T] (f g: List T) (hfg: f = g): f.prod = g.prod := by
  rw [hfg]

lemma list_unattach_eq {T : Type*}  {p : T → Prop} (f g : List { x : T // p x }) (h: f = g): f.unattach = g.unattach := by
  rw [h]






lemma finsupp_lp_top (f: G → ℝ) (hf: f.support.Finite) (p: ENNReal): MeasureTheory.MemLp f p (Measure.count) := by
  rw [← my_haar_eq_count]
  apply Continuous.memLp_of_hasCompactSupport
  . apply continuous_of_discreteTopology
  .
    simp [HasCompactSupport]
    rw [isCompact_iff_finite]
    simp [tsupport]
    exact hf





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
  . simp
  -- TODO - inline these in the right places
  .
    intro i hs
    apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . simp
  .
    apply MeasureTheory.memLp_finset_sum
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



open scoped RealInnerProductSpace
-- Proposition 3.17.2: "∆ is positive semidefinite" from Vikman
set_option maxHeartbeats 200000 in
lemma laplace_positive_semidefinite (f: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): 0 ≤ ⟪f, (Laplace  f)⟫ := by
  unfold Laplace
  rw [inner_sub_right]
  rw [real_inner_self_eq_norm_sq]
  rw [conv_mu_lp2]
  rw [MeasureTheory.L2.inner_def]
  simp_rw [tolp_apply]
  simp_rw [f_conv_mu]
  simp_rw [← smul_eq_mul]
  simp_rw [inner_smul_right]
  simp_rw [inner_sum]
  rw [integral_const_mul]
  rw [MeasureTheory.integral_finset_sum]

  -- I couldn't figure how to to handle 'toLp (∑ x ∈ S), so I ended up manipulating the integral to avoid dealing with it
  have comp_smul_left (i: G) := MeasureTheory.Lp.coeFn_compMeasurePreserving (g := f) (f := fun a => i * a) (μ := volume) (by
    exact measurePreserving_mul_left volume i
  )
  simp_rw [ae_eq_everywhere] at comp_smul_left
  have congr_comp (i: G) (x: G) := congrFun (comp_smul_left i) x
  simp only [Function.comp_apply] at congr_comp
  simp_rw [smul_eq_mul]
  simp_rw [← congr_comp]
  simp_rw [← MeasureTheory.L2.inner_def]

  let f_eq_coe: f = f := by rfl
  nth_rw 1 [← MeasureTheory.Lp.toLp_coeFn (f := f) (hf := Lp.memLp f)] at f_eq_coe


  conv =>
    rhs
    rhs
    rhs
    arg 2
    intro x
    rw [← f_eq_coe]
    rw [MeasureTheory.Lp.toLp_compMeasurePreserving]
    simp



    --rw [MeasureTheory.Lp.toLp_compMeasurePreserving]

  -- We've now packed everything back up in an inner product -
  -- we no longer need to deal with commuting toLp and Finset.sum


  --simp [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]

  --rw [← MeasureTheory.L2.inner_def]


  -- have comp_mul_mem_lp (i: G) (f: MeasureTheory.Lp ℝ 2 (μ := volume)): MemLp (f ∘ (fun x => i * x)) 2 (μ := volume) := by
  --   apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
  --   . apply MeasureTheory.Lp.memLp f
  --   . exact measurePreserving_mul_left volume i


  -- conv =>
  --   rhs
  --   rhs
  --   rhs
  --   arg 2
  --   equals ∑ x ∈ S, MemLp.toLp (fun i => f (i • x)) (by
  --     apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
  --     . apply MeasureTheory.Lp.memLp f
  --     . exact measurePreserving_mul_right volume x
  --   ) =>

  --     apply Lp.ext
  --     rw [ae_eq_everywhere]
  --     funext a
  --     --simp
  --     rw [tolp_apply]
  --     conv =>
  --       rhs
  --     rw [Finsupp.sum_apply'']

  --     rw [eq_comm]
  --     refine Finset.induction_on S ?_ ?_
  --     .
  --       simp only [Finset.sum_empty]
  --       rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
  --       simp
  --     .
  --       intro a s ha sum_eq
  --       rw [Finset.sum_insert ha]
  --       rw [Finset.sum_insert ha]
  --       rw [← sum_eq]
  --       rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_add _ _)]
  --       simp





  --rw [inner_smul_right]
  --rw [inner_sum]

  let conv_f_delta_lp (i: G) :=  MemLp.toLp (Conv (f) (delta i⁻¹)) (μ := volume) (p := 2) (by
    simp_rw [f_conv_delta_helper]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume _
  )


  -- conv =>
  --   rhs
  --   rhs
  --   rhs
  --   arg 2
  --   intro i
  --   rhs
  --   equals conv_f_delta_lp i =>
  --     unfold conv_f_delta_lp
  --     simp_rw [f_conv_delta_helper]
  --     simp
    -- arg 1
    -- intro i
    -- rhs
    -- equals fun x => (fun i => (MemLp.toLp _  (comp_mul_mem_lp i f)) x) i =>
    --   funext x
    --   simp
    --   rw [tolp_apply]
    --   simp

  have sum_le := Finset.sum_le_sum (g := fun i => ‖f‖ * ‖conv_f_delta_lp i‖) (f := fun i => ⟪f, conv_f_delta_lp i⟫) (s := S) (by
    intro s hs
    simp
    have foo := norm_inner_le_norm (x := f) (y := conv_f_delta_lp s) (𝕜 := ℝ)
    rw [Real.norm_eq_abs] at foo
    exact real_inner_le_norm f (conv_f_delta_lp s)
  )
  rw [← ge_iff_le]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rhs
    equals conv_f_delta_lp x =>
      apply Lp.ext
      rw [ae_eq_everywhere]
      funext g
      rw [tolp_apply]
      simp [conv_f_delta_lp]
      rw [tolp_apply]
      rw [f_conv_delta]
      simp


  calc
    _ ≥ ‖f‖ ^ 2 - 1 / ↑(#S) * ∑ i ∈ S, ‖f‖ * ‖conv_f_delta_lp i‖ := by

      apply sub_le_sub_left
      simp
      gcongr
    _ ≥ 0 := by
      unfold conv_f_delta_lp
      simp_rw [f_conv_delta_helper]
      conv =>
        lhs
        rhs
        rhs
        arg 2
        intro x
        rhs
        equals ‖f‖ =>
          simp
          rw [← Function.comp_def]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := volume)]
          . simp [norm]
          . apply MeasureTheory.AEStronglyMeasurable.of_discrete
          . exact measurePreserving_mul_left volume x
      simp
      have s_card_ne_zero: (#S : ℝ) ≠ 0 := by
        simp
        have foo := hS
        simp at foo
        exact Finset.nonempty_iff_ne_empty.mp foo

      rw [← mul_assoc]
      simp [s_card_ne_zero]
      rw [pow_two]
  .
    intro s hs
    simp

    have mem_lp_h_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp f) mem_lp_h_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1



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


-- Lemma 3.16 in Vikman

-- The case split statement in Vikman
def f_n_conv_delta_tendsto: Prop :=  ∀ s: S, Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0)

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

lemma ennreal_ofReal_toReal_eq (a: ENNReal): ENNReal.ofReal a.toReal = a ∨ ENNReal.ofReal a.toReal = 0 := by
  match a with
  | none =>
    simp
  | some val =>
    simp

-- lemma ennreal_div_le_of_zero (a b c: ENNReal) (ha: (((ENNReal.ofReal a.toReal) / b) ≤ c)): a / b ≤ c  := by
--   by_cases a_eq_top: a = ⊤
--   .
--     rw [a_eq_top] at ha
--   cases ha
--   . rename_i a_top
--     simp [a_top]
--   . rename_i div_le
--     grw [ENNReal.ofReal_toReal_le]
--     exact div_le

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


#print axioms laplace_bounded
#print axioms laplace_self_adjoint
#print axioms laplace_positive_semidefinite





#synth Module ℝ (Lp ℝ 2 (μ := MeasureTheory.volume (α := G)))

lemma abs_sub_sq_eq (a b : ℝ): (a - b)^2 = |a - b|^2 := by
  nth_rw 2 [pow_two]
  rw [abs_sub_sq]
  rw [sub_sq]
  group

lemma sub_sq_le_abs (a b : ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): (a - b)^2 ≤ |a^2 - b^2| := by
  rw [sq_sub_sq]
  rw [abs_mul]
  have sub_le_add: |a - b| ≤ |a + b| := by
    have sum_pos: 0 ≤ a + b := by linarith
    rw [abs_of_nonneg sum_pos]
    rw [abs_le]
    refine ⟨?_, ?_⟩
    . linarith
    . linarith
  rw [abs_sub_sq_eq]
  grw [← sub_le_add]
  rw [pow_two]

lemma card_s_ne: #(S) ≠ 0 := by
  simp
  have foo := S_nonempty
  simp at foo
  exact Finset.nonempty_iff_ne_empty.mp foo

lemma bounded_from_elpnorm_bound (f: G → ℝ) (p: ℕ) (hp: p ≠ 0) (C: ℝ) (hC: 0 ≤ C) (hf: eLpNorm f p (volume) ≤ (ENNReal.ofReal C)): ∀ g: G, |f g| ≤ C := by
  simp [eLpNorm, eLpNorm', hp] at hf
  simp_rw [lintegral_g_eq_add] at hf
  by_contra!
  obtain ⟨g, hg⟩ := this
  have norm_le := ENNReal.le_tsum (f := fun a => ‖f a‖ₑ ^ p) g
  rw [ENNReal.rpow_inv_le_iff] at hf
  .
    rw [Real.enorm_eq_ofReal_abs] at norm_le
    grw [hf] at norm_le
    norm_cast at norm_le
    rw [← ENNReal.ofReal_pow (by simp)] at norm_le
    rw [← ENNReal.ofReal_pow hC] at norm_le
    rw [ENNReal.ofReal_le_ofReal_iff (by simp [hC])] at norm_le
    rw [pow_le_pow_iff_left₀ (by simp) hC (by omega)] at norm_le
    linarith
  . simp only [Nat.cast_pos]
    omega


lemma rangeRestrict_range {A B: Type*} [Group A] [Group B] (f: A →* B): f.rangeRestrict.range = ⊤ := by
  ext a
  have a_prop := a.property
  simp only [mem_top, iff_true]
  rw [MonoidHom.mem_range] at a_prop
  rw [MonoidHom.mem_range]
  obtain ⟨x, hx⟩ := a_prop
  use x
  ext
  simp [hx]


lemma rho_g_case_finite (hr: Finite (↥(rho_g))): Nonempty (Theorem3_1_Input G) := by
  have quotient_iso := QuotientGroup.quotientKerEquivRange (GRepW_base)
  unfold rho_g at hr

  have ker_finite_index := Subgroup.finiteIndex_ker (GRepW_base)
  let G' := (GRepW_base).ker

  let G'_action := (GRepW_base).restrict G'

  have act_ker (g: G) := MonoidHom.mem_ker (f := (GRepW_base)) (x := g)

  have act_v (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): Submodule.Quotient.mk (GRep  g f) = (Submodule.Quotient.mk (f) : W) := by
    simp [GRep]
    have apply_g := (act_ker g).mp hg
    simp [GRepW_base, GRepW_non_invertible, GRep] at apply_g
    apply_fun Units.val at apply_g
    rw [Representation.asGroupHom_apply] at apply_g
    rw [Representation.quotient_apply] at apply_g
    apply_fun (fun y => y (Submodule.Quotient.mk f)) at apply_g
    simp at apply_g
    exact apply_g

  let extract_const (f: LipschitzH) (hf: f ∈ ConstF ) := f 1

  simp_rw [Submodule.Quotient.eq] at act_v

  -- As proved in 'act_v', we have  '(GRep g f) - f' is a constant function. We can therefore evaluate
  -- it any poitn in G (here, 1) to get the constant
  let lambda_g := fun (g: G') (f: LipschitzH ) => ((GRep g.val) f - f) 1
  let lambda_g_dual (g: G'): Module.Dual ℝ (LipschitzH) := {
    toFun := fun w => lambda_g g w
    map_add' := by
      intro x y
      simp [lambda_g]
      abel
    map_smul' := by
      intro c x
      simp [lambda_g]
      rw [mul_sub]
  }

  -- TODO - this could be much cleaner
  have act_eq_lambda (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): (gAct g f) = f + ConstLipschitzH (lambda_g ⟨g, hg⟩ f) := by
    have act := act_v g hg f
    simp [GRep, gAct, ConstF] at act
    simp [gAct]
    obtain ⟨y, hy⟩ := act
    simp [lambda_g, GRep, gAct]
    ext a
    simp
    apply_fun (fun l => l.toFun) at hy
    have app_a := congrFun hy a
    simp [lipschitz_sub_tofun] at app_a
    rw [eq_comm] at app_a
    apply eq_add_of_sub_eq at app_a
    rw [app_a]
    rw [add_comm]
    simp [LipschitzH_apply]
    simp [LipschitzH_apply] at hy
    have other_app := congrFun hy 1
    simp at other_app
    rw [← other_app]
    simp [ConstLipschitzH]

  have lambda_const (g: (GRepW_base).ker) (f: LipschitzH ) (k: ℝ): (lambda_g g (f + (ConstLipschitzH k))) = (lambda_g g f) := by
    simp [lambda_g, GRep, gAct]
    simp [ConstLipschitzH]


  let lambda_g_hom: G' →* Multiplicative (Module.Dual ℝ (LipschitzH)) := {
    toFun := fun g => Multiplicative.ofAdd (lambda_g_dual g)
    map_one' := by
      simp [lambda_g_dual]
      simp [lambda_g]
      ext f
      simp
    map_mul' := by
      intro g h
      ext f
      simp [lambda_g_dual]
      conv =>
        lhs
        dsimp [lambda_g]
      simp [GRep]
      rw [gAct_mul]
      rw [act_eq_lambda h.val h.property]
      rw [act_eq_lambda g.val g.property]
      rw [lambda_const]
      simp [ConstLipschitzH]
      group
  }

  by_cases lambda_g_infinite: Infinite (lambda_g_hom.range)
  .

    apply g_hom_abelian G' ?_ lambda_g_hom.rangeRestrict ?_ lambda_g_hom.rangeRestrict.range ?_ ?_ ?_ ?_
    . simp [G']
      exact ker_finite_index
    . exact MonoidHom.rangeRestrict_surjective lambda_g_hom
    . rw [rangeRestrict_range]
      simp
      -- TODO: PR this to mathlib
      apply (Equiv.infinite_iff (α := lambda_g_hom.range) _).mp
      . exact lambda_g_infinite
      . exact {
          toFun := fun g => ⟨g, trivial⟩
          invFun := fun g => g.val
          left_inv := by simp [Function.LeftInverse]
          right_inv := by simp [Function.RightInverse, Function.LeftInverse]
        }
    . exact {
        is_comm := {
          comm := by
            intro a b
            ext
            simp
            rw [add_comm]
        }
      }
    . rw [Subgroup.finiteIndex_iff]
      rw [rangeRestrict_range]
      simp
    . rw [rangeRestrict_range]
      simp
      exact Group.FG.out
  .
    simp only [not_infinite_iff_finite] at lambda_g_infinite
    let G'' := lambda_g_hom.ker
    have G''_finite_index := Subgroup.finiteIndex_ker lambda_g_hom

  -- TODO - this could be a lot cleaner
    have G''_act_v (g: lambda_g_hom.ker) (x: G) (f: LipschitzH ): f (x * g) = f x := by
      specialize act_v g
      simp at act_v
      have g_prop := g.property
      rw [MonoidHom.mem_ker] at g_prop
      simp [lambda_g_hom, lambda_g_dual, lambda_g, GRep] at g_prop
      apply_fun (fun p => p f) at g_prop
      simp at g_prop
      rw [sub_eq_zero] at g_prop
      simp [gAct] at g_prop
      specialize act_v f
      simp [GRep, gAct, ConstF] at act_v
      obtain ⟨y, hy⟩ := act_v
      simp [ConstLipschitzH] at hy
      apply_fun (fun l => l.toFun) at hy
      simp at hy
      rw [Pi.sub_def] at hy
      have eval_one := hy
      apply_fun (fun f => f 1) at eval_one
      apply_fun (fun f => f x) at hy
      simp at hy
      simp at eval_one
      rw [← g_prop] at eval_one
      simp at eval_one
      rw [eq_comm] at hy
      apply eq_add_of_sub_eq' at hy
      simp
      rw [hy]
      simp
      exact eval_one


    -- View G'' as a subgroup of G
    let G''_subgroup_G := (Subgroup.map G'.subtype lambda_g_hom.ker)

    -- TODO - clean up this proof
    have G''_subgroup_finite_index: G''_subgroup_G.FiniteIndex := by
      unfold G''_subgroup_G
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map]
      simp
      unfold G'
      rw [Subgroup.finiteIndex_iff] at ker_finite_index
      refine ⟨?_, ker_finite_index⟩
      rw [Subgroup.finiteIndex_iff] at G''_finite_index
      exact G''_finite_index


    have finite_quotient := Subgroup.finite_quotient_of_finiteIndex (H := G''_subgroup_G)

    have coset_union := QuotientGroup.univ_eq_iUnion_smul G''_subgroup_G
    have f_range_eq (f: LipschitzH ): Set.range f = Set.range ((fun (x: G ⧸ G''_subgroup_G) => f (x.out))) := by
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        simp at ha
        obtain ⟨y, hy⟩ := ha
        have y_mem: y ∈ Set.univ := by simp
        rw [coset_union] at y_mem
        simp at y_mem
        obtain ⟨i, hi⟩ := y_mem
        rw [Set.mem_smul_set] at hi
        obtain ⟨x, x_mem, y_eq⟩ := hi
        rw [← y_eq] at hy

        unfold G''_subgroup_G at x_mem
        simp at x_mem
        obtain ⟨x_mem_g', hx'⟩ := x_mem

        have x_mem_ker: ⟨x, x_mem_g'⟩ ∈ lambda_g_hom.ker := by
          simp
          exact hx'

        let x_ker: lambda_g_hom.ker := ⟨⟨x, x_mem_g'⟩, x_mem_ker⟩
        have f_translate := G''_act_v x_ker i.out f

        simp only [Set.mem_range]
        use i
        rw [← f_translate]
        exact hy
      . intro ha
        simp only [Set.mem_range] at ha
        obtain ⟨y, hy⟩ := ha
        simp
        simp at hy
        use y.out


    have all_f_const (f: LipschitzH ): ∃ z: ℝ, f = ConstLipschitzH z := by
      have f_max := Set.Finite.exists_maximalFor (fun y => ‖y‖) (Set.range f) ?_ ?_
      obtain ⟨z, z_mem, hz⟩ := f_max

      have z_max: ∀ p ∈ Set.range f, ‖p‖ ≤ ‖z‖ := by
        intro p hp
        simp at hp
        obtain ⟨y, hy⟩ := hp
        by_cases p_le_z: ‖p‖ ≤ ‖z‖
        . exact p_le_z
        . simp at p_le_z

          have f_le := hz (j := f.toFun y) ?_ ?_
          .
            simp at f_le
            rw [← hy]
            exact f_le
          . simp
          . simp
            rw [← hy] at p_le_z
            linarith

      simp at z_mem
      obtain ⟨g_max, f_g_max_eq⟩ := z_mem

      have f_const_fn := harmonic_abs_max_implies_const  f.toFun (by
        have f_harmonic := f.harmonic
        simp [Harmonic] at f_harmonic
        simp [Laplace_b, f_conv_mu]
        ext x
        simp
        have f_harmonic_real := f_harmonic x
        rw [sub_eq_zero]
        exact f_harmonic_real
      ) g_max (by
        intro a
        specialize z_max ((f.toFun a)) (by (
          simp
        ))
        rw [← f_g_max_eq] at z_max
        simpa using z_max
      )

      use (f g_max)
      ext a
      have app := congrFun f_const_fn a
      rw [app]
      simp [ConstLipschitzH]
      .
        rw [f_range_eq]
        apply Set.finite_range
      . apply Set.range_nonempty

    obtain ⟨f, nontrivial_f⟩ := exists_nontrivial_harmonic
    obtain ⟨z, f_eq_const⟩ := all_f_const f
    specialize nontrivial_f z
    contradiction


-- TODO - upstream to mathlib
lemma s_pow_inv (n: ℕ): (S^n)⁻¹ = (S⁻¹)^n := by
  induction n with
  | zero =>
    simp only [pow_zero, inv_one]
  | succ n ih =>
    simp only [inv_pow]

-- TODO - upstream to mathlib
lemma mem_closure_iff_mem_pow (g: G): g ∈ Subgroup.closure S ↔ ∃ n, g ∈ S^n := by
  refine ⟨?_, ?_⟩
  .
    intro hg
    induction hg using Subgroup.closure_induction with
    | one =>
      use 1
      simp
      exact hGS.one_mem
    | inv a ha a_mem =>
      obtain ⟨n, hn⟩ := a_mem
      use n
      rw [← Finset.mem_inv']
      rw [s_pow_inv]
      rw [← S_eq_Sinv]
      exact hn
    | mem s hs =>
      use 1
      simp
      exact hs
    | mul a b ha hb iha ihb =>
      obtain ⟨p, hp⟩ := iha
      obtain ⟨q, hq⟩ := ihb
      use (p + q)
      rw [pow_add]
      rw [Finset.mem_mul]
      refine ⟨a, hp, b, hq, rfl⟩
  .
    intro _
    apply mem_closure g

-- TODO - get rid of the duplicate 'hGS'
lemma exists_theorem_3_1_input [hGS: Generates ] {d: ℕ} (hd: HasPolynomialGrowthD S d): Nonempty (Theorem3_1_Input G) := by
  by_cases rho_g_infinite: Infinite (↥(rho_g))
  . exact rho_g_case_infinite hd rho_g_infinite
  . exact rho_g_case_finite (by simpa using rho_g_infinite)




structure PreservesProd (T: Type*) (l h: List G) (γ: G) where
  prod_eq: l.prod = h.prod
  same_sum: (l.map (fun s => if s = γ then 1 else 0)).sum = (h.map (fun s => if s = γ then 1 else 0)).sum


abbrev countElemOrInv {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (γ: T): ℤ := (l.map (fun (s: E) => if s = γ then 1 else if s = γ⁻¹ then -1 else 0)).sum
abbrev isElemOrInv {T: Type*} [ht: Group T] [heq: DecidableEq T] (g: T): T → Bool := fun a => decide (a = g ∨ a = g⁻¹)
lemma take_count_sum_eq_exp {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (g: T) (hg: g ≠ g⁻¹) (hl: ∀ val ∈ l, val = g ∨ val = g⁻¹): l.unattach.prod = g^(countElemOrInv l g) := by
  induction l with
  | nil =>
    simp [countElemOrInv]
  | cons h t ih =>
    simp [countElemOrInv]
    by_cases h_eq_g: h = g
    .
      simp [h_eq_g]
      rw [ih]
      . rw [← zpow_one_add]
      . simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right
    .
      have h_eq_inv: h = g⁻¹ := by
        specialize hl h
        simp at hl
        simp  [h_eq_g] at hl
        exact hl
      simp [h_eq_g, h_eq_inv]
      rw [ih]
      .
        rw [← zpow_neg_one]
        rw [← zpow_add]
        simp [hg.symm]
      .
        simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right

open Additive


lemma list_filter_one {T: Type*} [DecidableEq T] [Group T] (l: List T): (l.filter (fun s => !decide (s = 1))).prod = l.prod := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    simp
    by_cases h_eq_one: h = 1
    .
      simp [h_eq_one]
      exact ih
    .
      rw [List.filter_cons]
      simp [h_eq_one]
      exact ih

def e_i_regular_helper {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (s: S): G := (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))

def E_helper (φ: (Additive G) →+ ℤ) (γ: G) := {γ, γ⁻¹} ∪ Set.range (ι := S) (e_i_regular_helper φ γ)

lemma take_drop_len {T: Type*} {l: List T} {p: T → Bool}: (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  suffices h: l.takeWhile p ++ l.dropWhile p = l by
    nth_rw 3 [← h]
    rw [List.length_append]
  exact List.takeWhile_append_dropWhile

def gamma_m_helper {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (m: ℤ) (s: S): G := γ^m * (e_i_regular_helper φ γ s) * γ^(-m)

lemma gamma_m_eq_mulAt (φ: (Additive G) →+ ℤ) (γ: G) (m: ℤ) (s: S): gamma_m_helper φ γ m s = (MulAut.conj ((γ^m))) (e_i_regular_helper φ γ s) := by
  dsimp [gamma_m_helper]
  simp


-- The set {γ_m_i}_{m ≤ n}
omit hGS in
noncomputable def three_two_S_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (Function.uncurry (gamma_m_helper φ γ)) ((Finset.Icc (-n : ℤ) n).product S.attach)
-- The set of words of at length at most n generated by {γ_m_i}_{m ≤ n}
-- Note - This is based on https://terrytao.wordpress.com/2010/02/18/a-proof-of-gromovs-theorem/, which uses
-- "length at most n"
-- The Vikman paper says "words of length n", which seems incorrect



omit hGS in
lemma gamma_helper_subset_S_n {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Set.range (gamma_m_helper (S := S) φ γ n) ⊆ three_two_S_n S  φ γ n := by
  intro val hval
  simp [three_two_S_n]
  use n
  refine ⟨by omega, ?_⟩
  simp at hval
  exact hval

omit hGS in
instance simple_finite_list {G: Type*} (P: Finset G) (n: ℕ): Finite { l: List P | l.length ≤ n } := by
  apply List.finite_length_le


omit hGS in
noncomputable def list_len_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset (List ((three_two_S_n S φ γ n ))) := @Set.toFinset _ { l: List ((three_two_S_n S φ γ n )) | l.length ≤ n } (@Fintype.ofFinite _ _)

omit hGS in
noncomputable def three_two_B_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (fun l => l.unattach.prod) (list_len_n S φ γ n )

--noncomputable def three_two_B_n_single_s (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ) (s: G): Finset G := Finset.image (fun l => l.unattach.prod) (list_len_n φ γ n (S := {s}))



--set_option maxHeartbeats 600000

-- If G has polynomial growth, than we can find an N such that S_n ⊆ B_n * B_n⁻¹
set_option maxHeartbeats 2000000 in
lemma new_three_two_poly_growth (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (γ: G) (φ: (Additive G) →+ ℤ)  (s: G) (s_mem: s ∈ S): ∃ n, three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)  := by
  by_contra!
  simp [HasPolynomialGrowthD] at hG
  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop d (b := Real.log 2) (Real.log_pos (by simp))
  simp at little_o_poly
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly
  apply Asymptotics.IsLittleO.eventuallyLE at little_o_poly
  apply Filter.Eventually.natCast_atTop at little_o_poly
  simp at little_o_poly

  -- Find an N' such that N^D < 2^N
  obtain ⟨N', hN⟩ := little_o_poly

  -- Write γ as a product of elements in S
  obtain ⟨gamma_list, gamma_list_prod⟩ := mem_S_prod_list γ
  simp [ProdS] at gamma_list_prod

  have gamma_list_inv: ((gamma_list.unattach).map (fun x => x⁻¹)).reverse.prod = γ⁻¹ := by
    rw [← List.prod_inv_reverse]
    rw [gamma_list_prod]

  have gamma_list_comm_inv: ((gamma_list.unattach).map (fun x => x⁻¹)) = (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).unattach := by
    clear gamma_list_prod gamma_list_inv
    induction gamma_list with
    | nil =>
      simp
    | cons a b ih =>
      simp
      exact ih

  rw [gamma_list_comm_inv] at gamma_list_inv



  -- Choose our N large enough that we can apply all of the above conditions
  let N := max N' (max gamma_list.length (max (φ (ofMul s)).natAbs 2))
  -- specialize hN N (by simp [N])
  -- specialize this N
  -- rw [Finset.not_subset] at this
  -- obtain ⟨p, ⟨p_mem, p_not_prod⟩⟩ := this
  -- rw [Finset.mem_mul.not] at p_not_prod
  -- push_neg at p_not_prod


  have disjoint_smul (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)) (p_not_prod: p ∉ three_two_B_n (S := {s}) φ γ M * (three_two_B_n (S := {s}) φ γ M)⁻¹): (p • three_two_B_n (S := {s}) φ γ M) ∩ (three_two_B_n (S := {s}) φ γ M) = ∅ := by
    rw [Finset.mem_mul.not] at p_not_prod
    push_neg at p_not_prod

    ext a
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro ha
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨b, b_mem, s_b_eq⟩ := ha
    apply_fun (fun g => g * b⁻¹ ) at s_b_eq
    simp at s_b_eq
    apply Finset.inv_mem_inv at b_mem
    by_contra!
    specialize p_not_prod a this b⁻¹ b_mem
    rw [ne_comm] at p_not_prod
    contradiction


  have s_n_subset: ∀ M, N ≤ M → three_two_S_n (S := {s}) φ γ M ⊆ three_two_S_n (S := {s}) φ γ (M + 1) := by
    intro m hM a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩

  have s_n_subset_all (x y: ℕ) (hxy: x ≤ y): three_two_S_n (S := {s}) φ γ x ⊆ three_two_S_n (S := {s}) φ γ (y) := by
    intro a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩


  have b_n_subset_b_n_succ: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro M hM a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    obtain ⟨l, l_len, l_prod⟩ := ha
    simp [list_len_n]
    use l.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)
    simp
    simp [list_len_n] at l_len
    refine ⟨by omega, ?_⟩
    conv =>
      lhs
      arg 1
      equals l.unattach =>
        simp [List.unattach, -List.map_subtype]
    exact l_prod

  have smul_subset (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)): p • three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨list_prod, ⟨list, list_mem, list_prod_eq⟩, p_mul_eq⟩ := ha
    --have new_p_mem := (s_n_subset_all (N + 1) (M + 1) (by omega)) p_mem
    --have p_mem_M := s_n_subset M hM p_mem
    use (⟨p, p_mem⟩ :: (list.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)))
    refine ⟨?_, ?_⟩
    .
      simp [list_len_n, list_mem]
      simp [list_len_n] at list_mem
      exact list_mem

    .
      simp
      conv =>
        lhs
        arg 2
        arg 1
        equals list.unattach =>
          simp [List.unattach, -List.map_subtype]
      rw [list_prod_eq, p_mul_eq]


  have s_n_bound: ∀ M: ℕ, N ≤ M → ∀ a ∈ three_two_S_n (S := {s}) φ γ M, ∃ l: List S, l.unattach.prod = a ∧ l.length ≤ 4*M^2 := by
    intro M hM a ha
    simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at ha
    obtain ⟨m, m_bound, s_m_eq⟩ := ha
    let gamma_inv_list: List S := (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).reverse

    -- Depending on whether these values are positive or negative, we either need to repeat γ or γ⁻¹ in the first list
    let m_list_choice := if 0 < m then gamma_list else gamma_inv_list
    let phi_list_choice := if 0 < (-φ (ofMul s)) then gamma_list else gamma_inv_list

    let m_list_choice_inv := if 0 < m then gamma_inv_list else gamma_list

      --
    --have phi_natabs: (φ (ofMul s)).natAbs = -φ (ofMul s) := by omega
    use (List.replicate m.natAbs m_list_choice).flatten ++ [⟨s, s_mem⟩] ++ (List.replicate (-(φ (ofMul s))).natAbs phi_list_choice).flatten ++ (List.replicate m.natAbs m_list_choice_inv).flatten
    refine ⟨?_, ?_⟩
    .
      simp [phi_list_choice]
      --rw [gamma_list_prod]
      norm_cast
      rw [← s_m_eq]
      rw [← zpow_natCast]
      conv =>
        rhs
        arg 1
        arg 2
        -- TODO - is there a tactic that can normalize the 'ofMul' stuff for us?
        equals s * γ^(-(φ (ofMul s))) =>
          rw [← ofMul_zpow]
          rw [← sub_eq_add_neg]
          rw [← ofMul_div]
          rw [div_eq_mul_inv]
          rw [← inv_zpow]
          rw [inv_zpow']
          rfl


      --rw [← zpow_natCast, phi_natabs]
      simp
      simp_rw [m_list_choice, m_list_choice_inv]
      by_cases m_pos: 0 < m
      .
        simp_rw [m_pos]
        simp
        have m_eq_abs : |m| = m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        rw [m_eq_abs]
        group
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [m_eq_abs]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [m_eq_abs]
          group
      .
        simp_rw [m_pos]
        simp
        have neg_abs_m : |m| = - m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        group
        rw [neg_abs_m]
        group
        -- TODO - this can be deduplicated
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [neg_abs_m]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [neg_abs_m]
          group
    .

      simp [m_list_choice, m_list_choice_inv]
      simp_rw [apply_ite]
      have m_natabs_le: m.natAbs ≤ M := by omega
      have gamma_list_len_le: gamma_list.length ≤ N := by omega
      have inv_list_len_eq: gamma_inv_list.length = gamma_list.length := by
        simp [gamma_inv_list]
      simp [inv_list_len_eq]
      have n_squared_pos: 1 ≤ N * N := by
        simp [N]
      have m_squared_pos: 1 ≤ M * M := by
        nlinarith
      have phi_choice_len: phi_list_choice.length = gamma_list.length := by
        simp [phi_list_choice]
        simp_rw [apply_ite]
        simp [inv_list_len_eq]
      rw [phi_choice_len]
      have phi_s_le_: (φ (ofMul s)).natAbs ≤ M := by omega
      calc
        _ ≤ M * M + ((φ (ofMul s)).natAbs * gamma_list.length + M * M + 1) := by
          nlinarith
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + 1 := by
          nlinarith
        -- Extremely crude upper bound, but we only need to show a polynomial bound,
        -- so it's fine to use '1 <= N * N'
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + M*M := by
          nlinarith
        _ ≤ 3 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * M) := by
          nlinarith
        _ = 4 * M * M := by
          nlinarith
        _ = 4 * M^2 := by nlinarith


  have b_n_subset_s_n_squared: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ S ^ (M * (4 * M^2)) := by
    intro M hM a ha
    have orig_ha := ha
    rw [Finset.mem_pow]
    simp [three_two_B_n] at ha
    obtain ⟨l, l_len, l_prod⟩ := ha
    let nested_list := l.map (fun s => ((s_n_bound M hM s.val s.property).choose))
    have flat_list_prod: nested_list.flatten.unattach.prod = a := by
      simp [nested_list]
      rw [← l_prod]
      conv =>
        lhs
        arg 1
        equals l.unattach =>
          clear l_len l_prod nested_list
          induction l with
          | nil =>
            simp
          | cons h t ih =>
            simp
            rw [ih]
            simp [List.unattach, -List.map_subtype]
            simp at ih
            have my_spec := Exists.choose_spec ((s_n_bound M hM h h.property))
            have first_prop := my_spec.1
            -- wtf
            nth_rw 8 [← first_prop]
            simp



    have flat_list_len: nested_list.flatten.length ≤ nested_list.length • (4 * M^2) := by
      simp
      have foo := List.sum_le_card_nsmul (l := (List.map List.length nested_list)) (4 * M^2) ?_
      --simp only [List.length_map, smul_eq_mul, nested_list] at foo
      .
        conv at foo =>
          rhs
          simp
        exact foo
      .
        intro q hq
        simp at hq
        obtain ⟨s_list, h_s_prod, s_len⟩ := hq
        simp [nested_list] at h_s_prod
        obtain ⟨gamma_n, gamma_n_mem, gamma_n_mem_l, s_prod_eq⟩ := h_s_prod
        have s_prod_prop: s_list.unattach.prod = gamma_n ∧ s_list.length ≤ 4*M^2 := by
          have my_spec := Exists.choose_spec ((s_n_bound M hM gamma_n gamma_n_mem))
          rw [s_prod_eq] at my_spec
          exact my_spec
        rw [← s_len]
        exact s_prod_prop.2

    have nested_len_eq: nested_list.length = l.length := by
      simp [nested_list]

    rw [nested_len_eq] at flat_list_len
    simp [list_len_n] at l_len
    simp only [smul_eq_mul] at flat_list_len
    have nested_list_le_n_squared: nested_list.flatten.length ≤ M * (4 * M^2) := by
      apply le_mul_of_le_mul_right (b := l.length)
      . omega
      . omega


    let filled_list := nested_list.flatten ++ (List.replicate ((M * (4 * M^2)) - nested_list.flatten.length) ⟨1, hGS.one_mem⟩)

    have filled_list_prod: filled_list.unattach.prod = nested_list.flatten.unattach.prod := by
      simp [filled_list]


    have len_eq: filled_list.length = M * (4 * M^2) := by
      simp [filled_list]
      apply Nat.add_sub_of_le
      simp at nested_list_le_n_squared
      exact nested_list_le_n_squared

    rw [← len_eq]
    use filled_list.get
    conv =>
      lhs
      equals (List.ofFn (filled_list.get)).unattach.prod =>
        simp

    simp
    rw [filled_list_prod]
    exact flat_list_prod

  conv at b_n_subset_s_n_squared =>
    intro M hM
    rhs
    rhs
    equals 4 * M^3 => ring


  -- #(B_n) grows exponentially, at least from N onword
  have b_n_card_exp: ∀ M: ℕ, N ≤ M → 2^(M - N) ≤ #(three_two_B_n (S := {s}) φ γ M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      simp [three_two_B_n, list_len_n]
      use [⟨(gamma_m_helper φ γ 0 ⟨s, s_mem⟩), ?_⟩]
      . simp [N]
      .
        simp [three_two_S_n]
        use 0
        refine ⟨by omega, ?_⟩
        simp [gamma_m_helper, e_i_regular_helper]

    | succ k hk ih =>
      rw [← tsub_add_eq_add_tsub hk]
      rw [pow_succ]

      --specialize hN N (by simp [N])
      specialize this k
      rw [Finset.not_subset] at this
      obtain ⟨p, ⟨p_mem, p_not_prod⟩⟩ := this
      --rw [Finset.mem_mul.not] at p_not_prod
      --push_neg at p_not_prod

      have union_subset_n_succ: three_two_B_n (S := {s}) φ γ k ∪ (p • three_two_B_n (S := {s}) φ γ k) ⊆ three_two_B_n (S := {s}) φ γ (k + 1) := by
        apply Finset.union_subset
        . exact b_n_subset_b_n_succ k hk
        . exact smul_subset k hk p p_mem


      have card_le := Finset.card_le_card (union_subset_n_succ)
      rw [Finset.card_union_of_disjoint ?_] at card_le
      .
        simp at card_le
        ring_nf at card_le
        rw [add_comm] at card_le
        omega
        --have b_n_subset_n := Finset.card_le_card (b_n_subset_s_n_squared N (by simp))
        --have b_n_succ_subset := Finset.card_le_card (b_n_subset_s_n_squared (N + 1) (by simp))
        --simp at b_n_succ_subset
      .
        specialize disjoint_smul  k hk p p_mem p_not_prod
        rw [Finset.inter_comm] at disjoint_smul
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact disjoint_smul


  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop (3 * d) (b := (Real.log 2)) (by
    --simp
    apply Real.log_pos
    simp
  )
  simp at little_o_poly
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly


  obtain ⟨a, hG⟩ := hG

  have a_ne_zero: a ≠ 0 := by
    by_contra!
    rw [this] at hG
    have hg_one := hG 1 (by omega)
    simp at hg_one
    have one_mem := hGS.one_mem
    rw [hg_one] at one_mem
    simp at one_mem

  have mul_four := Asymptotics.IsLittleO.const_mul_left little_o_poly (a * 4^d)
  rw [← Asymptotics.isLittleO_const_mul_right_iff (c := 2^(-N : ℤ)) (hc := (by simp))] at mul_four
  --have mul_four := little_o_poly


  --rw [Asymptotics.IsLittleO.tendsto_zero_of_tendsto] at little_o_poly
  apply Asymptotics.IsLittleO.def (c := (1 : ℝ)  / 2) (hc := by simp) at mul_four
  apply Filter.Eventually.natCast_atTop at mul_four
  simp at mul_four
  obtain ⟨M', hM⟩ := mul_four
  let M: ℕ := max N M'





  have m_le_n: N ≤ M := by omega


  specialize b_n_card_exp M m_le_n
  specialize b_n_subset_s_n_squared
  have b_n_subset_n := Finset.card_le_card (b_n_subset_s_n_squared M (m_le_n))

  have m_ge_one: 1 ≤ M := by
    omega

  have m_cubed: 1 ≤ M^3 := by
    apply Nat.one_le_pow
    omega


  have other_poly := hG (4 * M ^ 3) (by
    omega
  )

  have m_pow_lt := hM (M) (by omega)
  rw [pow_mul] at m_pow_lt

  -- apply_fun (fun (g: ℝ) => 2 * g) at m_pow_lt
  -- .
  --   simp at m_pow_lt

  -- .
  --   apply Monotone.const_mul
  --   exact fun ⦃a b⦄ a ↦ a
  --   simp


  have helper_lemma (a b c : ℝ) (ha: 0 < a) (hb: 0 < b) (hc: 0 < c) (habc: a ≤ b * c) (hb: b < 1): a < c := by
    nlinarith

  have strict_lt: a * 4 ^ d * (↑M ^ 3) ^ d < (((2 : ℝ) ^ N)⁻¹ * 2 ^ M) := by
    apply helper_lemma (b := 2⁻¹)
    .
      field_simp
      positivity
    . simp
    . simp
    . exact m_pow_lt
    . norm_num



    -- apply lt_or_eq_of_le at m_pow_lt
    -- match m_pow_lt with
    -- | .inl strict =>
    --   omega
    -- | .inr eq =>
    --   rw [eq]
    --   rw [mul_comm]l
    --   apply mul_lt_of_lt_one_right'
    --   apply lt_mul_of_one_lt_right'
    --   apply mul_lt_of_lt_of_le_one


  conv at strict_lt =>
    rhs
    equals 2^(M - N) =>
      have m_minu_n_pos: N ≤ M := by omega
      field_simp
      rw [← pow_add]
      simp
      omega


  norm_cast at strict_lt
  rw [mul_assoc, ← mul_pow] at strict_lt

  have eventually_lt_double: a * (4 * M ^ 3) ^ d < 2 ^ (M - N) := by
    exact strict_lt

  omega



set_option maxHeartbeats 300000 in
lemma closure_iterate_mulact {T: Type*} [Group T] [DecidableEq T] (a b: T) (n: ℤ)
  (conj_in: (a^n * b * a^(-n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs))))
  (conj_inv_in: (a^(-n) * b * a^(n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs)))) :
 (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) = (Subgroup.closure (G := T) (Set.range (fun (m : ℤ) => a^m * b * a^(-m)))) := by
  ext x
  refine ⟨?_, ?_⟩
  .
    intro hx
    apply Subgroup.closure_mono (h := (fun (m: ℤ) ↦ a ^ m * b * a ^ (-m)) '' Set.Ioo (-n.natAbs) n.natAbs)
    .
      intro y hy
      simp at hy
      simp
      obtain ⟨m, hm, y_eq⟩ := hy
      use m
    . exact hx
  .
    intro hx
    have closed_under_conj: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a * y * a⁻¹ ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: m < (n.natAbs : ℤ) - 1
        . apply Subgroup.subset_closure
          simp
          use (m + 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            . omega
            .
              apply_fun (fun (z: ℤ) => z + 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                exact m_lt_n_sub
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) 1
          .
            rw [← mul_self_zpow]
            simp
            repeat rw [← mul_assoc]
        .
          have n_minus_eq: n - 1 + 1 = n := by
            omega
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (|n|) - 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← inv_zpow']
          rw [mul_assoc]
          rw [← zpow_add_one]
          simp
          simp at conj_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_inv_in
            exact conj_inv_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        simp at mul_mem
        simp
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem

    -- TODO - deduplicate this
    have closed_under_conj_inv: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a⁻¹ * y * a ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: (-n.natAbs : ℤ) < m - 1
        . apply Subgroup.subset_closure
          simp
          use (m - 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            .
              simp at m_lt_n_sub
              have ⟨m_gt, other⟩ := hm
              omega

            .
              apply_fun (fun (z: ℤ) => z - 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                omega
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-1)
          .
            repeat rw [← mul_assoc]
            nth_rw 2 [← zpow_neg_one]
            rw [← zpow_add]
            rw [add_comm, ← sub_eq_add_neg]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← inv_zpow]
              rw [inv_zpow']
              rw [mul_zpow_self]
              rw [add_comm]
            simp
            rw [← inv_zpow]
            simp
            rw [sub_eq_add_neg]

        .
          have n_minus_eq: n - 1 + 1 = n := by
            omega
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (-|n|) + 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [← mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← zpow_neg_one]
          rw [mul_assoc]
          rw [mul_assoc]
          rw [mul_assoc]
          simp
          repeat rw [← mul_assoc]
          simp at conj_inv_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_inv_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_in
            exact conj_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        repeat rw [← mul_assoc] at mul_mem
        simp at mul_mem
        simp
        repeat rw [← mul_assoc]
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem



    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp at hy
      obtain ⟨m, hm, y_eq⟩ := hy
      by_cases m_in_range: m ∈ Set.Ioo (-n.natAbs : ℤ) n.natAbs
      .
        apply Subgroup.subset_closure
        simp
        use m
        simp at m_in_range
        refine ⟨by omega, by simp⟩
      .
        simp only [Set.mem_Ioo] at m_in_range
        rw [not_and_or] at m_in_range
        simp at m_in_range
        by_cases m_pos: 0 < m
        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            rw [← m_eq_abs] at this
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              exact conj_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              simp at conj_inv_in
              rw [n_eq_neg_abs] at conj_inv_in
              simp at conj_inv_in
              rw [n_eq_neg_abs]
              simp
              exact conj_inv_in
          | succ p hsucc ih =>
            specialize closed_under_conj _ ih
            norm_cast
            rw [pow_succ']
            repeat rw [← mul_assoc] at closed_under_conj
            simp at closed_under_conj
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj

        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = -m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              simp at conj_inv_in
              exact conj_inv_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              rw [n_eq_neg_abs] at conj_in
              simp at conj_in
              rw [n_eq_neg_abs]
              simp
              exact conj_in
          | succ p hsucc ih =>
            --rw [← Subgroup.inv_mem_iff]
            --simp
            specialize closed_under_conj_inv _ ih
            simp at ih
            norm_cast
            rw [zpow_negSucc]
            rw [pow_succ]
            --rw [zpow_add]
            repeat rw [← mul_assoc] at closed_under_conj_inv
            simp at closed_under_conj_inv
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj_inv


    | one => apply Subgroup.one_mem
    | mul y z hy hz y_mem z_mem =>
      apply Subgroup.mul_mem
      . exact y_mem
      . exact z_mem
    | inv y hy y_mem =>
      apply Subgroup.inv_mem _ y_mem

#print axioms closure_iterate_mulact

--- Consequence of `three_two_poly_growth` - the set of all 'γ^n *e_i γ^(-n)' is contained the closure of S_n
lemma three_poly_poly_growth_all_s_n (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (γ: G) (φ: (Additive G) →+ ℤ) (hγ: φ γ = 1)
  : ∃ n, ∀ m, (Finset.image (gamma_m_helper (S := S) φ γ m) Finset.univ).toSet ⊆ Subgroup.closure (three_two_S_n S  φ γ (n)).toSet := by

  -- by_cases S_empty: S = ∅
  -- .
  --   simp [S_empty, gamma_m_helper, three_two_S_n]
  --   use 1
  --   intro m
  --   intro a ha
  --   simp at ha
  --   obtain ⟨s, hs, a_eq⟩ := ha
  --   grind


  let r: ℕ := Finset.max' (Finset.image (fun s => (by
    exact sInf { n: ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹) }
    --exact {Classical.choose (new_three_two_poly_growth  d hd hG γ φ hφ hγ s)}
  )) S) (by
    simp
    exact S_nonempty
  )
  use r
  intro m
  intro x hx
  simp [gamma_m_helper] at hx
  simp [three_two_S_n, gamma_m_helper]
  obtain ⟨s, hs, x_eq_conj⟩ := hx

  let all_n_vals := { n : ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)}
  let n := sInf all_n_vals
  have set_nonempty: all_n_vals.Nonempty := by
    exact new_three_two_poly_growth  d hd hG γ φ s hs
  have temp_s_n_subset := Nat.sInf_mem set_nonempty
  have s_n_subset: n ∈ all_n_vals := by
    exact temp_s_n_subset
  simp [all_n_vals] at s_n_subset
  --obtain ⟨n, s_n_subset⟩ := new_three_two_poly_growth  d hd hG γ φ hφ hγ s
  have n_le_r: n ≤ r := by
    simp [r]
    apply Finset.le_max'
    simp
    use s


  have my_iter := closure_iterate_mulact γ (e_i_regular_helper φ γ ⟨s, hs⟩) (n + 1)
  simp [three_two_S_n, gamma_m_helper] at s_n_subset
  have closure_eq := my_iter ?_ ?_
  .
    have x_mem_closure_range: x ∈ Subgroup.closure (Set.range fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) := by
      by_cases m_pos: 0 < m
      .
        have m_eq_natabs: m = m.natAbs := by
          omega
        apply Subgroup.subset_closure
        simp
        use m.natAbs
        rw [m_eq_natabs] at x_eq_conj
        rw [← x_eq_conj]
      .
        --rw [← Subgroup.closure_inv]
        --rw [← Subgroup.inv_mem_iff]
        have m_eq_neg_natabs: m = -m.natAbs := by
          omega
        apply Subgroup.subset_closure
        simp
        --simp only [zpow_neg, zpow_natCast, Set.mem_range]
        use m

    rw [← closure_eq] at x_mem_closure_range
    apply Subgroup.closure_mono (h := ((fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) '' (Set.Ioo (-(r + 1) : ℤ) (r + 1 : ℤ))))
    .
      intro p hp
      simp at hp
      simp
      obtain ⟨q, hp, p_eq⟩ := hp
      use q
      refine ⟨by omega, ?_⟩
      use s
      use hs
    .
      apply (Subgroup.closure_mono _) x_mem_closure_range
      intro z hz
      simp at hz
      simp
      obtain ⟨a, ⟨a_gt, a_lt⟩, z_eq⟩ := hz
      use a
      refine ⟨⟨?_, ?_⟩, z_eq⟩
      .
        --have neg_n_gt_r: (-r : ℤ) ≤ (-n : ℤ) := by omega
        norm_cast at a_gt
        omega
      .
        norm_cast at a_lt
        omega
  .
    specialize s_n_subset (n + 1) (by omega) (by omega) s rfl
    --specialize s_n_subset ⟨s, hs⟩
    simp [three_two_B_n] at s_n_subset
    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
  .
    -- TODO - 99% of this can be deduplicated
    specialize s_n_subset (-(n + 1)) (by omega) (by omega) s rfl
    -- Deduplicate verything after here
    simp [three_two_B_n] at s_n_subset

    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]

def e_i_with_gamma (φ: (Additive G) →+ ℤ) (γ : G) (s: S): Additive G := (ofMul s.val) + ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))


-- The 'e_i' terms from Vikman 3.2, together with γ, generate the original group G
lemma e_i_and_gamma_generates_G (φ: (Additive G) →+ ℤ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure ({1, γ, γ⁻¹} ∪ ((e_i_with_gamma φ γ) '' Set.univ)) = (Subgroup.closure S) := by

  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ

  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))

  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))
  have e_i_zero: ∀ s: S, φ (e_i s) = 0 := by
    intro s
    unfold e_i
    simp
    simp [phi_ofmul]

  have e_i_regular_zero: ∀ s: S, φ (ofMul (e_i_regular s)) = 0 := by
    dsimp [ofMul]
    intro s
    unfold e_i_regular
    simp
    simp [phi_ofmul]

  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp

  conv =>
    arg 1
    arg 1
    arg 2
    arg 1
    equals e_i_regular =>
      rfl
  rw [closure_enlarge]
  apply Subgroup.closure_eq_of_le
  .
    rw [hGS.generates]
    exact fun ⦃a⦄ a ↦ trivial
  .
    simp
    intro s hs
    simp
    rw [← mem_toSubmonoid]
    rw [Subgroup.closure_toSubmonoid]
    dsimp [Membership.mem]
    rw [Submonoid.closure_eq_image_prod]
    -- TODO - why do we need any of this?
    show s ∈ List.prod '' _
    rw [Set.mem_image]


    have foo := Submonoid.exists_list_of_mem_closure (s := ((S ∪ S⁻¹) : Set G)) (x := s)
    rw [← Subgroup.closure_toSubmonoid _] at foo
    simp only [mem_toSubmonoid, Finset.mem_coe] at foo
    have generates := hGS.generates
    have x_in_top: s ∈ (⊤: Set G) := by
      simp

    rw [← generates] at x_in_top
    specialize foo x_in_top
    obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
    norm_cast at l_mem_s
    rw [s_union_sinv] at l_mem_s

    let l_attach := l.attach
    let list_with_mem: List S := (l_attach).map (fun a => ⟨a.val, l_mem_s a.val a.prop⟩)
    let new_list := list_with_mem.map (fun s => (e_i s) + ofMul (γ^(((φ (ofMul s.val))))))

    have cancel_add_minus: max_phi - 1 + 1 = max_phi := by
      omega

    use new_list
    refine ⟨?_, ?_⟩
    .
      simp
      intro x hx
      unfold new_list list_with_mem l_attach at hx
      simp at hx
      obtain ⟨⟨a, ha⟩, _, x_eq_sum⟩ := List.mem_map.mp hx
      simp only [Function.comp_apply] at x_eq_sum
      left

      have gamma_phi_in_minus_plus: γ^(φ a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1  +1) := by
        by_cases val_pos: 0 < φ a
        .
          have eq_self: Int.natAbs (φ a) = φ a := by
            simp [val_pos]
            linarith
          conv =>
            arg 2
            equals γ ^ (Int.natAbs (φ a)) =>
              nth_rw 1 [← eq_self]
              norm_cast
          apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
          . simp
          .
            rw [cancel_add_minus]
            unfold max_phi
            simp
            right
            apply Finset.le_max'
            simp
            use a
            refine ⟨l_mem_s a ha, ?_⟩
            conv =>
              pattern ofMul a
              equals a => rfl
          .
            apply Set.pow_mem_pow
            simp
        .
          have eq_neg_abs: (φ a) = -(φ a).natAbs := by
            rw [← Int.abs_eq_natAbs]
            simp at val_pos
            rw [← abs_eq_neg_self] at val_pos
            omega
          rw [eq_neg_abs]
          conv =>
            arg 2
            equals (γ⁻¹) ^ (↑(φ a).natAbs) =>
              simp
              rw [Int.abs_eq_natAbs]
              norm_cast
          -- TOOD - deduplicate this with the positive case
          apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
          . simp
          .
            rw [cancel_add_minus]
            unfold max_phi
            simp
            right
            apply Finset.le_max'
            simp
            use a
            refine ⟨l_mem_s a ha, ?_⟩
            conv =>
              pattern ofMul a
              equals a => rfl
          .
            apply Set.pow_mem_pow
            simp
      have a_mem_s: a ∈ S := by exact l_mem_s a ha
      have prod_mem_power: e_i_regular ⟨a, a_mem_s⟩ * γ ^ φ (ofMul a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1 + 1 + 1) := by
        rw [pow_succ']
        rw [Set.mem_mul]
        use e_i_regular ⟨a, a_mem_s⟩
        refine ⟨by simp, ?_⟩
        use γ ^ φ (ofMul a)
        refine ⟨gamma_phi_in_minus_plus, ?_⟩
        simp

      have prod_eq_sum: e_i ⟨a, l_mem_s a ha⟩ + φ (ofMul a) • ofMul γ = (e_i_regular ⟨a, a_mem_s⟩) * (γ ^ φ (ofMul a)) := by
        simp [e_i, e_i_regular, cancel_add_minus]


        conv =>
          rhs
          arg 1
          equals ofMul (a* γ^(-(φ (ofMul a)))) =>
            simp

        apply_fun (fun x => x * (γ ^ (- φ (ofMul a))))
        .
          simp only
          simp
          conv =>
            lhs
            equals a * (γ ^ φ (ofMul a))⁻¹ =>
              simp
              rfl
          conv =>
            rhs
            rhs
            equals ofMul (γ ^ (- φ (ofMul a))) =>
              simp

          rw [← ofMul_mul]
          conv =>
            rhs
            equals (a * γ ^ (-φ (ofMul a))) =>
              rfl
          simp
        .
          exact mul_left_injective (γ ^ (-φ (ofMul a)))






      rw [← x_eq_sum]
      rw [prod_eq_sum]
      rw [cancel_add_minus] at prod_mem_power
      apply prod_mem_power








    unfold new_list list_with_mem l_attach
    simp
    conv =>
      arg 1
      arg 1
      arg 1
      arg 1
      intro z
      unfold e_i
      simp
    simp
    conv =>
      arg 1
      arg 1
      arg 1
      equals id =>
        rfl
    convert l_prod using 2
    exact List.map_id l


#print axioms e_i_and_gamma_generates_G

-- The kernel of `φ` is generated by {γ_m_i}
set_option maxHeartbeats 1000000
lemma three_two_gamma_m_generates (φ: (Additive G) →+ ℤ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S)  φ γ))) = AddSubgroup.toSubgroup φ.ker := by
  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ
  --
  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))



  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))
  have e_i_zero: ∀ s: S, φ (e_i s) = 0 := by
    intro s
    unfold e_i
    simp
    simp [phi_ofmul]

  have e_i_regular_zero: ∀ s: S, φ (ofMul (e_i_regular s)) = 0 := by
    dsimp [ofMul]
    intro s
    unfold e_i_regular
    simp
    simp [phi_ofmul]

  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp


  have new_closure_e_i := e_i_and_gamma_generates_G φ γ hγ
  let gamma_m := fun (m: ℤ) (s: S) => γ^m * (e_i s).toMul * γ^(-m)
  have gamma_m_ker_phi: (Subgroup.closure (Set.range (Function.uncurry gamma_m))) = φ.ker.toSubgroup := by
    ext z
    refine ⟨?_, ?_⟩
    . intro hz
      have foo := Submonoid.exists_list_of_mem_closure (s := Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) (x := z)
      rw [← Subgroup.closure_toSubmonoid _] at foo
      specialize foo hz
      obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
      rw [← l_prod]
      rw [← MonoidHom.coe_toMultiplicative_ker]
      show (AddMonoidHom.toMultiplicative φ) (List.prod (l : List (Multiplicative (Additive G)))) = 1
      rw [map_list_prod]
      apply List.prod_eq_one
      intro x hx
      simp at hx
      obtain ⟨a, a_mem_l, phi_a⟩ := hx
      specialize l_mem_s a a_mem_l
      unfold gamma_m at l_mem_s
      simp at l_mem_s
      rw [← phi_a]
      match l_mem_s with
      | .inl a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
      | .inr a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        apply_fun Inv.inv at prod_eq_a
        simp at prod_eq_a
        -- TODO - deduplicate this with the branch above
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
    .
      intro hz

      -- We need to write 'γ^a (f⁻¹ )' as an element of e_i

      -- γ^(φ(f_1)) (f_1⁻¹ ) = f_2 γ^(-φ(f_2))

      have foo := Submonoid.exists_list_of_mem_closure (s := ({1, γ, γ⁻¹} ∪ e_i '' Set.univ) ∪ ({1, γ, γ⁻¹} ∪ e_i '' Set.univ)⁻¹) (x := z)
      apply_fun Subgroup.toSubmonoid at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i

      have e_i_eq: e_i = e_i_with_gamma φ γ := rfl
      rw [← e_i_eq] at new_closure_e_i
      rw [new_closure_e_i] at foo
      rw [← Subgroup.closure_toSubmonoid _] at foo
      simp only [mem_toSubmonoid, Finset.mem_coe] at foo

      conv at foo =>
        intro hz
        arg 1
        intro l
        lhs
        intro y
        intro hy
        rw [Set.union_comm {1, γ, γ⁻¹} (e_i '' Set.univ)]
        rw [Set.union_assoc]
        arg 1
        rhs
        rw [Set.union_comm]
        rw [Set.union_inv]
        rw [Set.union_assoc]
        rhs
        simp

      have generates := hGS.generates
      have z_in_top: z ∈ (⊤: Set G) := by
        simp

      rw [← generates] at z_in_top
      have z_eq_prod := foo z_in_top
      clear foo

      let E: Set G := {γ, γ⁻¹} ∪ Set.range e_i_regular ∪ (Set.range e_i_regular)⁻¹

      let rec rewrite_list (list: List (E)) (hlist: φ (ofMul list.unattach.prod) = 0): { t: List (((Set.range (Function.uncurry gamma_m) : (Set G)) ∪ (Set.range (Function.uncurry gamma_m))⁻¹ : (Set G))) // list.unattach.prod = t.unattach.prod } := by
        let is_gamma: E → Bool := fun (k: E) => k = γ ∨ k = γ⁻¹
        let is_gamma_prop: E → Prop := fun (k: E) => k = γ ∨ k = γ⁻¹
        have eq_split: list = list.takeWhile is_gamma ++ list.dropWhile is_gamma := by
          exact Eq.symm List.takeWhile_append_dropWhile
        by_cases header_eq_full: list.takeWhile is_gamma = list
        .
          have list_eq_gamma_m: ∃ m: ℤ, list.unattach.prod = γ ^ m := by
            unfold is_gamma at header_eq_full
            clear eq_split is_gamma is_gamma_prop hlist

            induction list with
            | nil =>
              use 0
              simp
            | cons h t ih =>
              have h_gamma: h = γ ∨ h = γ⁻¹ := by
                simp at header_eq_full
                exact header_eq_full.1
              rw [List.takeWhile_cons_of_pos] at header_eq_full
              .
                rw [List.cons_eq_cons] at header_eq_full
                specialize ih header_eq_full.2
                obtain ⟨m, hm⟩ := ih
                by_cases h_eq_gamma: h = γ
                .
                  use (m + 1)
                  simp [h_eq_gamma, hm]
                  exact mul_self_zpow γ m
                . use (-1 + m)
                  simp [h_eq_gamma] at h_gamma
                  simp [h_gamma, hm]
                  rw [← zpow_neg_one]
                  rw [zpow_add]
              . simp [h_gamma]


          have empty_prod_eq: list.unattach.prod = ([] : List E).unattach.prod := by
            obtain ⟨m, hm⟩ := list_eq_gamma_m
            rw [hm]
            simp
            rw [hm] at hlist
            simp at hlist
            simp [phi_ofmul] at hlist
            simp [hlist]

          exact ⟨[], empty_prod_eq⟩
        .

          have tail_nonempty: list.dropWhile is_gamma ≠ [] := by
            rw [not_iff_not.mpr List.takeWhile_eq_self_iff] at header_eq_full
            rw [← not_iff_not.mpr List.dropWhile_eq_nil_iff] at header_eq_full
            exact header_eq_full

          have dropwhile_len_gt: 0 < (list.dropWhile is_gamma).length := by
            exact List.length_pos_iff.mpr tail_nonempty

          have not_is_gamma := List.dropWhile_get_zero_not is_gamma list dropwhile_len_gt
          simp at not_is_gamma

          have not_is_gamma_prop: ¬ is_gamma_prop (List.dropWhile is_gamma list)[0] := by
            dsimp [is_gamma_prop]
            dsimp [is_gamma] at not_is_gamma
            exact of_decide_eq_false not_is_gamma

          simp [is_gamma_prop] at not_is_gamma_prop
          have drop_head_in_e_i: (List.dropWhile is_gamma list)[0].val ∈ (Set.range e_i_regular) ∪ (Set.range e_i_regular)⁻¹ := by
            have drop_in_E: (List.dropWhile is_gamma list)[0].val ∈ E := by
              simp [E]
            simp only [E] at drop_in_E
            simp_rw [Set.union_assoc] at drop_in_E
            rw [Set.mem_union] at drop_in_E
            have not_in_left: (List.dropWhile is_gamma list)[0].val ∉ ({γ, γ⁻¹} : Set G) := by
              simp [not_is_gamma_prop]

            -- TODO - why can't simp handle this?
            have in_right := Or.resolve_left drop_in_E not_in_left
            exact in_right


          let m := ((list.takeWhile is_gamma).map (fun (k : E) => if k = γ then 1 else if k = γ⁻¹ then -1 else 0)).sum

          have in_range: γ ^ m * ↑(List.dropWhile is_gamma list)[0] * γ ^ (-m) ∈ (Set.range (Function.uncurry gamma_m)) ∪ ((Set.range (Function.uncurry gamma_m)))⁻¹ := by
            simp [gamma_m]
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              left
              use m
              use s
              use s_in_S
              simp
              rw [← eq_e_i]
              rfl
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              right
              use m
              use s
              use s_in_S
              conv =>
                rhs
                rw [← mul_assoc]
              simp
              rw [← eq_e_i]
              rfl

          have phi_ofmul_gamma: φ (ofMul γ) = 1 := by
            exact hγ

          have gamma_ne_inv: γ ≠ γ⁻¹ := by
            by_contra this
            apply_fun ofMul at this
            apply_fun φ at this
            rw [phi_ofmul_gamma] at this
            rw [ofMul_inv] at this
            rw [AddMonoidHom.map_neg] at this
            rw [phi_ofmul_gamma] at this
            omega

          let gamma_copy: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ⁻¹, by simp [E]⟩
          let gamma_copy_inv: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ⁻¹, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ, by simp [E]⟩

          have gamma_copy_prod: gamma_copy.unattach.prod = γ^m := by
            simp [gamma_copy]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have gamma_copy_inv_prod: gamma_copy_inv.unattach.prod = γ^(-m) := by
            simp [gamma_copy_inv]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have E_inhabited: Inhabited E := by
            use γ
            simp [E]

          have header_prod: (List.takeWhile is_gamma list).unattach.prod = γ^m := by
            have my_lemma := take_count_sum_eq_exp (List.takeWhile is_gamma list) γ gamma_ne_inv ?_
            .
              rw [my_lemma]
            .
              have foo (x: E) := List.mem_takeWhile_imp (p := fun (val: E) => (val = γ ∨ val = γ⁻¹)) (l := list) (x := x)
              conv at foo =>
                intro x hx
                equals ↑x = γ ∨ ↑x = γ⁻¹ =>
                  simp
              exact foo

          -- 'γ^n * a * γ^(_n) * γn * tail', as a list of elements in E
          let mega_list := (gamma_copy ++ [(List.dropWhile is_gamma list)[0]] ++ gamma_copy_inv) ++ (gamma_copy ++ (list.dropWhile is_gamma).tail)
          have mega_list_prod: mega_list.unattach.prod = list.unattach.prod := by
            simp [mega_list]
            simp [gamma_copy_prod, gamma_copy_inv_prod]
            conv =>
              rhs
              rw [eq_split]
              rw [List.unattach_append]
              simp
            have dropwhile_not_nul : (List.dropWhile is_gamma list) ≠ [] := by
              exact tail_nonempty
            apply_fun (fun x => x * (List.dropWhile is_gamma list).unattach.prod⁻¹)
            .
              simp
              conv =>
                pattern _[0]
                equals (List.dropWhile is_gamma list).headI =>
                  rw [← List.head_eq_getElem_zero dropwhile_not_nul]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.head_eq_getElem_zero]
                  exact
                    Eq.symm
                      (List.getI_eq_getElem (List.dropWhile is_gamma list)
                        (List.length_pos_iff.mpr dropwhile_not_nul))

              have unattach_len_pos: 0 < (List.dropWhile is_gamma list).unattach.length := by
                rw [List.length_unattach]
                exact List.length_pos_iff.mpr dropwhile_not_nul

              -- TODO - this is gross, and should be removed
              letI : Inhabited G := {
                default := 1
              }

              conv =>
                lhs
                lhs
                rhs
                equals (List.dropWhile is_gamma list).unattach.headI * (List.dropWhile is_gamma list).unattach.tail.prod =>
                  rw [← List.getI_zero_eq_headI]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.getI_eq_getElem _ (List.length_pos_iff.mpr dropwhile_not_nul)]
                  rw [List.getI_eq_getElem _ unattach_len_pos]
                  simp [List.getElem_unattach _ unattach_len_pos]
                  rw [list_tail_unattach]

              rw [List.headI_mul_tail_prod_of_ne_nil]
              .
                simp
                simp [header_prod]
              .
                by_contra this
                rw [List.eq_nil_iff_length_eq_zero] at this
                rw [List.length_unattach] at this
                rw [← List.eq_nil_iff_length_eq_zero] at this
                contradiction


            . exact mul_left_injective (List.dropWhile is_gamma list).unattach.prod⁻¹

          have sublist_phi_zero: φ (gamma_copy ++ (List.dropWhile is_gamma list).tail).unattach.prod = 0 := by
            rw [← mega_list_prod] at hlist
            unfold mega_list at hlist
            simp at hlist
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [inv_eq_iff_eq_inv.symm] at eq_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist

          have count_head_lt: (List.map (fun (k: E) ↦ if ↑k = γ then (1 : ℤ) else if ↑k = γ⁻¹ then -1 else 0)
          (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list)).sum.natAbs ≤ (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list).length := by
            induction (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list) with
            | nil =>
              simp
            | cons h t ih =>
              simp
              split_ifs
              . omega
              . omega
              . omega

          let rewritten_sub_list := (rewrite_list (gamma_copy ++ (list.dropWhile is_gamma).tail) sublist_phi_zero)
          let return_list := (⟨γ^m * (List.dropWhile is_gamma list)[0] * γ^(-m), in_range⟩) :: rewritten_sub_list.val

          -- Show that the list (rewritten in terms of `γ^m * e_i * γ^(-m)` terms) is in the kernel of φ


          have mega_list_prod_preserve: mega_list.unattach.prod = return_list.unattach.prod := by
            unfold mega_list return_list
            simp
            rw [gamma_copy_prod]
            rw [gamma_copy_inv_prod]
            simp
            rw [← rewritten_sub_list.property]
            simp
            rw [gamma_copy_prod]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← mul_assoc]
              simp
            rw [mul_assoc]

          have return_list_prod: list.unattach.prod = return_list.unattach.prod := by
            rw [← mega_list_prod_preserve]
            exact mega_list_prod.symm


          exact ⟨return_list, return_list_prod⟩
      termination_by list.length
      decreasing_by {
        simp
        have inhabited_g : Inhabited G := by
          use 1
        split_ifs
        .
          simp
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
        .
          simp-- [count_gamma_copy]
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
      }

      obtain ⟨z_list, h_z_list⟩ := z_eq_prod
      rw [← list_filter_one] at h_z_list
      have z_filter_mem_e: ∀ p ∈ (List.filter (fun s ↦ !decide (s = 1)) z_list), p ∈ E := by
        intro p hp
        dsimp [E]
        simp at hp
        obtain ⟨h_z_list_in, _⟩ := h_z_list
        specialize h_z_list_in p hp.1
        rw [Set.mem_union] at h_z_list_in
        rw [Set.mem_union] at h_z_list_in
        match h_z_list_in with
        | .inl h_z_list_in =>
          simp at h_z_list_in
          obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
          apply Set.mem_union_left
          apply Set.mem_union_right
          simp
          use a
          use a_mem_s
        | .inr h_z_list_in =>
          simp at h_z_list_in
          match h_z_list_in with
          | .inl h_z_list_in =>
            obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
            apply Set.mem_union_right
            simp
            use a
            use a_mem_s
          | .inr h_z_list_in =>
            simp [hp.2] at h_z_list_in
            apply Set.mem_union_left
            apply Set.mem_union_left
            simp
            exact h_z_list_in.symm

      let my_res := rewrite_list ((z_list.filter (fun s ↦ !decide (s = 1))).attach.map (fun (g) => ⟨g.val, z_filter_mem_e g.val g.property⟩)) (by
        simp
        -- TODO - there has to be a less awful way of doing this
        conv =>
          arg 1
          arg 2
          arg 1
          arg 2
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            clear h_z_list

            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        rw [← ofMul_list_prod]
        rw [h_z_list.2]
        exact hz
      )
      have my_res_prop := my_res.property
      rw [← Subgroup.mem_toSubmonoid]
      rw [Subgroup.closure_toSubmonoid _]
      conv =>
        equals z ∈ (Submonoid.closure (Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) : Set _) =>
          rfl
      rw [Submonoid.closure_eq_image_prod]
      rw [Set.mem_image]
      use my_res.val.unattach
      refine ⟨?_, ?_⟩
      . simp only [Set.mem_setOf_eq]
        intro x hx
        rw [List.mem_unattach] at hx
        obtain ⟨x_prop, _⟩ := hx
        exact x_prop
      .
        rw [← my_res_prop]
        conv =>
          pattern List.unattach _
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        exact h_z_list.2
  exact gamma_m_ker_phi

noncomputable def phi_generating (n: ℕ) (φ: (Additive G) →+ ℤ) (γ: G) := Finset.preimage (three_two_S_n S  φ γ (n)) Multiplicative.ofAdd (by
    apply Set.injOn_of_injective
    exact fun ⦃a₁ a₂⦄ a ↦ a
  )

omit hGS in
lemma three_two_S_n_subset_ker {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (phi_gamma: φ γ = 1) (n: ℕ):
   ↑(three_two_S_n S φ γ n) ⊆ Additive.toMul '' φ.ker.carrier := by

  intro x hx
  simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at hx
  obtain ⟨m, m_in_range, s, s_mem_s, prod_eq_x⟩ := hx
  apply_fun ofMul at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  apply_fun φ at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  simp at prod_eq_x
  conv at prod_eq_x =>
    arg 1
    arg 2
    equals (ofMul s + -(φ (ofMul s) • ofMul γ)) => rfl

  simp at prod_eq_x
  conv at prod_eq_x =>
    pattern φ (ofMul γ)
    equals φ γ => rfl

  simp [phi_gamma] at prod_eq_x
  simp
  exact id (Eq.symm prod_eq_x)

lemma three_two_S_n_generates  (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ : Additive G) (phi_gamma: φ γ = 1): ∃ n, AddSubgroup.closure (Additive.ofMul '' (three_two_S_n S φ γ (n))) = φ.ker := by
  --obtain ⟨n, hn⟩ := three_two_poly_growth d hd hG γ φ hφ phi_gamma
  obtain ⟨n, hn⟩ := three_poly_poly_growth_all_s_n d hd hG γ φ phi_gamma
  use n
  ext z
  refine ⟨?_, ?_⟩
  . intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      have helper := three_two_S_n_subset_ker S φ γ phi_gamma n
      have x_mem: x ∈ three_two_S_n S φ γ n := by
        simp at hx
        exact hx

      have helper := (three_two_S_n_subset_ker S φ γ phi_gamma n) x_mem
      simpa using helper
    | zero =>
      simp
    | add y z y_mem z_mem hy hz =>
      exact (AddSubgroup.add_mem_cancel_right φ.ker hz).mpr hy
    | neg x x_mem hx =>
      exact AddSubgroup.neg_mem φ.ker hx
  . intro hz
    have generates_ker := three_two_gamma_m_generates φ γ phi_gamma
    --obtain ⟨γ, hγ, generates_ker⟩ := three_two_gamma_m_generates φ hφ

    have hz' : z ∈ Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S) φ γ))) := by
      rw [generates_ker]; exact hz

    --have exists_prod_list := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
    have hz'' : z ∈ (Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S) φ γ)))).toSubmonoid := hz'
    rw [Subgroup.closure_toSubmonoid] at hz''
    have exists_prod := Submonoid.exists_list_of_mem_closure (M := Multiplicative (Additive G)) hz''
    obtain ⟨l, l_mem, z_eq_prod⟩ := exists_prod
    rw [← z_eq_prod]
    conv =>
      arg 2
      equals ofMul l.prod => rfl
    apply AddSubgroup.list_sum_mem
    simp only [Additive.forall]
    intro a ha
    specialize l_mem (ofMul a) ha
    --simp [three_two_S_n]
    rcases (Set.mem_union _ _ _).mp l_mem with l_mem | l_mem
    · obtain ⟨⟨p, s, s_mem⟩, helper_eq_a⟩ := Set.mem_range.mp l_mem
      simp only [Function.uncurry_apply_pair] at helper_eq_a
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      apply (AddSubgroup.mem_toSubgroup' _ (gamma_m_helper φ γ p ⟨s, s_mem⟩)).mp
      rw [AddSubgroup.toSubgroup'_closure]
      simp
      exact hn
    · rw [← AddSubgroup.neg_mem_iff]
      obtain ⟨⟨p, s, s_mem⟩, helper_eq_a⟩ := Set.mem_range.mp (Set.mem_inv.mp l_mem)
      simp only [Function.uncurry_apply_pair] at helper_eq_a
      conv at helper_eq_a =>
        rhs
        equals -ofMul a => rfl
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      apply (AddSubgroup.mem_toSubgroup' _ (gamma_m_helper φ γ p ⟨s, s_mem⟩)).mp
      rw [AddSubgroup.toSubgroup'_closure]
      simp
      exact hn

lemma three_two_ker_fg  (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ): φ.ker.FG := by
  rw [AddSubgroup.fg_iff]
  obtain ⟨γ, hγ⟩ := hφ 1
  obtain ⟨n, hn⟩ := three_two_S_n_generates d hd hG φ γ hγ
  use ofMul '' ↑(three_two_S_n S φ γ n)
  refine ⟨hn, ?_⟩
  rw [Set.finite_image_iff]
  .
    simp
  . intro a b hab
    simpa using hab


-- Extract a generatating set for the kernel of φ
noncomputable def phi_S (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ): Finset (φ.ker) := by
  have fg := three_two_ker_fg d hd hG φ hφ
  rw [AddSubgroup.fg_iff] at fg
  let S := Classical.choose fg
  have s_generates := (Classical.choose_spec fg).1
  have s_finite := (Classical.choose_spec fg).2
  have fintype : Fintype S := by
    exact s_finite.fintype

  let s_fin: Finset φ.ker := S.toFinset.attach.image (fun a => ⟨a.val, (by
    rw [← s_generates]
    apply AddSubgroup.mem_closure_of_mem
    have a_prop := a.property
    rw [Set.mem_toFinset] at a_prop
    exact a_prop
  )⟩)
  exact s_fin



omit hGS in
noncomputable def S_n_ker_phi  {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1) (n: ℕ)  : Finset φ.ker := (three_two_S_n S φ γ n).attach.image (fun x => ⟨x.val, (by
have foo := (three_two_S_n_subset_ker S φ γ hγ n) x.property
simpa using foo
)⟩) ∪ {0}

omit hGS in
lemma finite_virtually_nilpotent {G: Type*} [Group G] [Finite G]: Group.IsVirtuallyNilpotent G := by
  rw [Group.IsVirtuallyNilpotent]
  use ⊥
  refine ⟨?_, ?_⟩
  . exact Group.isNilpotent_of_subsingleton
    -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
  . infer_instance


omit hGS in
structure GeneratesWithParam (G: Type*) [Group G] [DecidableEq G] where
  S: Finset G
  hS: Nonempty S
  generates : ((closure (S : Set G) : Set G) = ⊤)
  -- This should be fine, since the growth rate doesn't depend on the generating set
  one_mem: (1 : G) ∈ S
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S
  g_infinite: Infinite G

lemma one_mem_S  {G: Type*} [Group G] [DecidableEq G] {n: ℕ} (data: Theorem3_1_Input G) (hGS: GeneratesWithParam data.G') (γ: Additive data.G') (hγ: data.φ γ = 1): 0 ∈ S_n_ker_phi hGS.S data.φ γ hγ n := by
  simp [S_n_ker_phi]

-- TODO - generalize from InvolutiveInv and upstream to mathlib
omit hGS in
lemma finset_union_inv {α : Type*}  [DecidableEq α] [InvolutiveInv α] {s t : Finset α}: (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := by
  ext a
  simp

omit hGS in
lemma finset_union_neg {α : Type*}  [DecidableEq α] [InvolutiveNeg α] {s t : Finset α}: -(s ∪ t) = -s ∪ -t := by
  ext a
  simp



-- The generating set of `ker φ` used below, shared between the `new_g_growth`
-- hypothesis and the `S` field so that `g_growth := new_g_growth` is definitionally
-- trivial (avoids an expensive `whnf` on the two separately-elaborated `Finset`s).
omit hGS in
noncomputable def ker_S {G: Type*} [Group G] [DecidableEq G] (data: Theorem3_1_Input G)
    (hGS: GeneratesWithParam data.G') (γ: data.G') (hγ: data.φ γ = 1) (n: ℕ) :
    Finset (Multiplicative data.φ.ker) :=
  (Finset.image Additive.toMul (S_n_ker_phi hGS.S data.φ γ hγ n)) ∪
    (Finset.image Additive.toMul ((S_n_ker_phi hGS.S data.φ γ hγ n)))⁻¹

-- TODO - figure out how to make this a 'let' without adding it to typeclass search
omit hGS in
noncomputable def ker_generates {d: ℕ} {n: ℕ} (hd: 1 ≤ d){G: Type*} [Group G] [DecidableEq G] (data: Theorem3_1_Input G) (hGS: GeneratesWithParam data.G') (γ: data.G') (hγ: data.φ γ = 1)
  (ker_infinite: Infinite (Multiplicative data.φ.ker))
  (ker_generates: AddSubgroup.closure (Additive.ofMul '' (three_two_S_n hGS.S data.φ γ (n))) = data.φ.ker)
  --(g_growth: HasPolynomialGrowth (Finset.image Additive.toMul (S_n_ker_phi hGS.S data.φ γ hγ n)) ∪ (Finset.image Additive.toMul ((S_n_ker_phi hGS.S data.φ γ hγ n)))⁻¹)
  ( new_g_growth: HasPolynomialGrowth (ker_S data hGS γ hγ n))
  : Generates := {
  G := (Multiplicative data.φ.ker)
  g_group := by infer_instance
  g_eq := by infer_instance
  S := ker_S data hGS γ hγ n
  hS := by
    use 1
    simp only [ker_S]
    simp
    exact one_mem_S data hGS γ hγ
  generates := by
    simp only [ker_S]
    simp
    rw [Subgroup.closure_union]
    conv =>
      arg 1
      arg 1
      equals ⊤ =>

        let f := (AddSubgroup.subtype data.φ.ker).toMultiplicative
        -- have foo := Subgroup.map_eq_map_iff (G) (f := Subgroup.subtype (G := Multiplicative (data.φ.ker))) (H := ⊤) (K := ⊤)
        -- let b := Subgroup.map a
        -- apply_fun (fun f => Subgroup.map (Subgroup.subtype (G := Multiplicative (data.φ.ker))) f)
        ext a
        simp
        rw [AddSubgroup.ext_iff] at ker_generates
        specialize ker_generates a.val
        have foo := ker_generates.mpr a.prop
        simp at foo
        conv at foo =>
          arg 2
          equals Additive.ofMul a.val => rfl

        apply (AddSubgroup.mem_toSubgroup' _ _).mpr at foo
        rw [AddSubgroup.toSubgroup'_closure] at foo
        simp at foo
        unfold S_n_ker_phi
        simp
        simp only [Finset.insert_eq, Set.image_union]
        simp
        first
          | erw [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
          | rw [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
          | simp only [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
        rw [← Subgroup.mem_map_iff_mem (f := f)]
        .
          simp only [f, Subgroup.subtype_apply]
          rw [MonoidHom.map_closure]
          simp
          conv =>
            arg 2
            equals a.val => rfl
          conv =>
            arg 1
            arg 1
            equals (three_two_S_n hGS.S data.φ γ n).toSet =>
              ext b
              constructor
              · intro hb
                obtain ⟨c, hc, rfl⟩ := hb
                obtain ⟨d, hd, rfl⟩ := hc
                obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hd
                exact y.2
              · intro hb
                have hbk : b ∈ three_two_S_n hGS.S data.φ γ n := by simpa using hb
                exact Set.mem_image_of_mem _ (Set.mem_image_of_mem _
                  (SetLike.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨b, hbk⟩))))
          exact foo
        . simp [f]
          intro x y hxy
          simpa using hxy
    simp
  one_mem := by
    apply Finset.mem_union_left
    rw [Finset.mem_image]
    use 0
    simp
    -- TODO - figure out wht 'apply one_mem_S' is slow
    exact one_mem_S data hGS γ hγ

  has_inv := by
    intro g hg
    simp only [ker_S] at hg ⊢
    simp at hg
    simp
    rw [or_comm]
    exact hg
  g_infinite := by
    exact ker_infinite
  g_growth := by convert new_g_growth using 2
}

omit hGS in
lemma poly_growth_equiv_generates (hG: Generates) (S': Finset hG.G) {d: ℕ} (h_poly: HasPolynomialGrowthD hG.S d): HasPolynomialGrowthD S' d := by
  unfold HasPolynomialGrowthD at h_poly
  obtain ⟨a, ha⟩ := h_poly
  have a_ne_zero: a ≠ 0 := by
    by_contra a_eq_zero
    simp [a_eq_zero] at ha
    specialize ha 1 (by simp)
    simp at ha
    have s_nonempty := hG.one_mem
    grind
  have poly := poly_growth_equiv a d (by omega) hG.S S' (S_eq_Sinv) (hG.one_mem) (by simpa using hG.generates) ha
  obtain ⟨b, b_ge, hb⟩ := poly
  use b


lemma three_two_kernel_poly_growth  (d: ℕ) (hd: d >= 1) (n: ℕ) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1)
 : HasPolynomialGrowthD (G := Multiplicative φ.ker) (d - 1) (S := (S_n_ker_phi S φ γ hγ n) ∪ (S_n_ker_phi S φ γ hγ n)⁻¹) := by

  -- The set S_n, viewed a subset of ker φ



  obtain ⟨a, ha⟩ := hG

  by_cases a_eq_zero: a = 0
  .
    simp [a_eq_zero] at ha
    specialize ha 1 (by simp)
    simp at ha
    have s_nonempty := hGS.one_mem
    grind



  unfold HasPolynomialGrowthD




  have S_n_poly := poly_growth_equiv a d (by omega) S ((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1}) S_eq_Sinv hGS.one_mem (by simpa using hGS.generates) ha
  obtain ⟨b, hb, ker_poly⟩ := S_n_poly



  use b * (2 ^ d)

  intro r hr
  specialize ker_poly (2 * r) (by omega)

  -- -- The kernel is an additive group, so we use hsmul instead of hpow for repeatedly adding elements in the group
  -- have poly_r: ∀ r: ℕ, r * #(r • S_n_ker_phi) ≤ #((three_two_S_n S φ γ n)) := by
  --   intro r

  --   by_cases r_zero: r = 0
  --   . simp [r_zero]

  let mul_by_i := fun (g: G) (i: Fin r) => g * (γ ^ i.val)
  have new_phi_gamma: φ (Additive.ofMul γ) = 1 := hγ
  have card_mul_range (g: G): #(Finset.image (mul_by_i g) Finset.univ) = r := by
    rw [Finset.card_image_of_injOn]
    . simp
    .

      intro j _ k _ mul_eq
      simp [mul_by_i] at mul_eq
      apply_fun φ ∘ (Additive.ofMul) at mul_eq
      simp [new_phi_gamma] at mul_eq
      rw [Fin.ext_iff]
      exact mul_eq

  have card_union: #((((((S_n_ker_phi S φ γ hγ n) ∪ (-(S_n_ker_phi S φ γ hγ n))).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) = r * #(r • ((S_n_ker_phi S φ γ hγ n) ∪ -((S_n_ker_phi S φ γ hγ n)))) := by
    rw [Finset.card_biUnion]
    .
      simp_rw [card_mul_range]
      simp
      rw [mul_comm]
      conv =>
        lhs
        arg 2
        arg 1
        equals r • ((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)) =>
          ext a
          rw [Finset.mem_image]
          simp_rw [Finset.mem_pow]
          refine Iff.trans ?_ Finset.mem_nsmul.symm
          refine ⟨?_, ?_⟩
          . intro h
            obtain ⟨b, ⟨f, hf⟩, b_eq_a⟩ := h
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image] at f_prop
              obtain ⟨g, g_mem, hg⟩ := f_prop
              rw [← hg]
              exact g_mem
            )⟩)
            rw [← b_eq_a]
            rw [← hf]
            rfl
          . intro h
            obtain ⟨f, hf⟩ := h
            use a
            refine ⟨?_, rfl⟩
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image]
              use (f i).val
              refine ⟨f_prop, ?_⟩
              rfl
            )⟩)
            rw [← hf]
            rfl
      rfl



    .
      intro a ha b hb hab x h_first h_second
      simp at h_first
      simp at h_second
      simp

      by_contra!
      obtain ⟨p, hp⟩ := this
      have orig_h_first := h_first hp
      have orig_h_second := h_second hp
      specialize h_first hp
      specialize h_second hp

      simp at h_first
      simp at h_second

      obtain ⟨y, hy⟩ := h_first
      obtain ⟨z, hz⟩ := h_second

      have orig_hy := hy
      have orig_hz := hz

      rw [← hz] at hy
      simp [mul_by_i] at hy
      apply_fun φ ∘ (Additive.ofMul) at hy
      simp [new_phi_gamma] at hy

      have a_ker: a.val ∈ φ.ker := by
        simp

      have b_ker: b.val ∈ φ.ker := by
        simp

      rw [AddMonoidHom.mem_ker] at a_ker
      rw [AddMonoidHom.mem_ker] at b_ker
      simp [ofMul] at hy
      simp [a_ker, b_ker] at hy

      rw [← Fin.ext_iff] at hy
      rw [hy] at orig_hy
      rw [← orig_hy] at orig_hz
      simp [mul_by_i] at orig_hz
      rw [eq_comm] at orig_hz
      contradiction



  have card_union_le: #((((((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) ≤ #(((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1}) ^ (2 * r)) := by
    grw [Finset.card_le_card]
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨s, s_mem, a_mem⟩ := ha
    rw [Finset.mem_image] at a_mem
    obtain ⟨k, _, hk⟩ := a_mem
    simp [mul_by_i] at hk
    rw [← hk]
    rw [two_mul]
    rw [pow_add]
    apply Finset.mul_mem_mul
    .
      unfold S_n_ker_phi at s_mem

      rw [Finset.mem_image] at s_mem
      obtain ⟨z, z_mem, hz⟩ := s_mem
      rw [← hz]

      rw [Finset.mem_pow] at z_mem
      obtain ⟨f, hf⟩ := z_mem
      rw [Finset.mem_pow]
      use (fun i => ⟨(f i).val.val, (by
        have f_prop := (f i).property
        rw [Finset.mem_image] at f_prop
        obtain ⟨g, g_mem, hg⟩ := f_prop
        rw [← hg]
        simp at g_mem
        cases g_mem
        .
          rename_i g_eq_zero
          apply Finset.mem_union_right
          rw [Finset.mem_singleton, g_eq_zero]
          first | rfl | simp
        . rename_i g_eq_nonzero
          cases g_eq_nonzero
          . rename_i left
            obtain ⟨z, z_mem, hz⟩ := left
            rw [← hz]
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            exact z_mem
          .
            rename_i right
            obtain ⟨z, z_mem, hz⟩ := right
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_right
            simp
            conv =>
              arg 2
              equals (-g).val =>
                rfl
            rw [← hz]
            exact z_mem
      )⟩)
      rw [← hf, ofMul_list_prod, List.map_ofFn]
      first
        | (erw [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
        | (rw [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
        | (simp only [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
    .
      have gamma_pow_subset: {γ}^r ⊆ (three_two_S_n S φ γ n ∪ {γ})^r := by
        apply Finset.pow_subset_pow_left
        simp



      have gamma_r_subset: ({γ, 1} : Finset G)^r ⊆ ((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1})^r := by
        apply Finset.pow_subset_pow
        . grind
        . grind
        . simp

      have gamma_subset: ({γ, 1} : Finset G)^k.val ⊆ ({γ, 1} : Finset G)^r := by
        apply Finset.pow_subset_pow
        . simp
        . simp
        . simp


      have gamma_mem_self: γ^k.val ∈ ({γ, 1} : Finset G)^k.val := by
        apply Finset.pow_mem_pow
        simp

      grind




  rw [card_union] at card_union_le
  grw [ker_poly] at card_union_le
  rw [mul_pow] at card_union_le
  rw [← mul_assoc] at card_union_le
  rw [mul_comm] at card_union_le
  rw [← Nat.le_div_iff_mul_le] at card_union_le
  .
    rw [Nat.mul_div_assoc] at card_union_le
    .
      nth_rw 3 [← pow_one (a := r)] at card_union_le
      rw [Nat.pow_div] at card_union_le
      .
        -- TODO - get rid of this obnoxious  Additive/Multiplicative defeq abuse
        conv =>
          lhs
          arg 1
          equals r • ((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)) =>
            ext a
            rw [Finset.mem_pow]
            -- TODO - why do we need explicit args here
            refine Iff.trans ?_ Finset.mem_nsmul.symm
            refine ⟨?_, ?_⟩
            .
              intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
            . intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
        exact card_union_le
      . omega
      . omega

    .
      nth_rw 1 [← pow_one (a := r)]
      apply Nat.pow_dvd_pow
      omega
  . omega

#print axioms three_two_kernel_poly_growth

lemma iterate_one {G: Type*} [Monoid G] {n: ℕ}: Nat.iterate (fun (g: G) => (1 : G)) n = (fun g => if n = 0 then g else 1) := by
  induction n with
  | zero =>
    simp
    ext a
    simp
  | succ n ih =>
    simp
    simp [ih]
    ext a
    simp


def iteratedCommutator {T: Type*} [Group T] {M: Subgroup T} (base right: M) (n: ℕ) := Nat.iterate (fun x => ⁅base, x⁆) n right

-- structure G''CommData {T: Type*} [Group T] (M: Subgroup T) where
--   -- Our 'γ^α' element
--   gamma_alpha: M
--   -- The result of repeatedly applying commutators
--   cur: M

--   -- When we take a commutator, we increment the second component if we take a commutator with 'right',
--   -- and reset it to zero and increment the first component if we take a commutator with anything else
--   -- As a result, 'pos' strictly increases at each step
--   pos: Lex (ℕ × ℕ)
--   -- The first component of our position is our index in the lower central series of M
--   pos_first: cur ∈ (lowerCentralSeries M pos.1)
--   -- The second component is the number of copies of 'right' that occur in successive adjacent commutators
--   pos_second: pos.2 ≠ 0 → ∃ b: M, cur = iteratedCommutator b gamma_alpha pos.2

-- set_option trace.profiler true in
-- set_option trace.Elab.command true in
-- set_option tactic.simp.trace true in
-- open Classical in
-- noncomputable def G''_comm {T: Type*} [Group T] {N: Subgroup T} (N_normal: N.Normal) {M: Subgroup T} (gamma_alpha base next: M) (gamma_N: gamma_alpha.val ∈ N) (n: ℕ): G''CommData M := match n with
-- | 0 => {
--   gamma_alpha := gamma_alpha
--   cur := base
--   pos := (0, 0)
--   pos_first := by
--     simp [lowerCentralSeries]
--   pos_second := by
--     simp
-- }
-- | n + 1 => {
--   gamma_alpha := gamma_alpha
--   cur := ⁅(G''_comm N_normal gamma_alpha base next gamma_N n).cur, next⁆
--   pos := if (next = gamma_alpha) then ((G''_comm N_normal gamma_alpha base next gamma_N n).pos.1, (G''_comm N_normal gamma_alpha base next gamma_N n).pos.2 + 1)
--          else ((G''_comm N_normal gamma_alpha base next gamma_N n).pos.1 + 1, 0)
--   pos_first := by
--     split_ifs
--     .
--       rename_i next_eq_gamma
--       simp [next_eq_gamma]
--       s orry
--     . s orry
--   pos_second := by
--     split_ifs
--     . rename_i next_eq_gamma
--       intro _
--       have prev := (G''_comm N_normal gamma_alpha base next gamma_N n).pos_second
--       by_cases prev_zero: (G''_comm N_normal gamma_alpha base next gamma_N n).pos.2 = 0
--       . use (G''_comm N_normal gamma_alpha base next gamma_N n).cur
--         simp [prev_zero]
--         simp [prev_zero, next_eq_gamma, iteratedCommutator]
--       . have prev_eq := prev prev_zero
--         obtain ⟨b, b_eq⟩ := prev_eq
--         use b
--         simp [next_eq_gamma, iteratedCommutator]
--         s orry
--     .
--       rename_i next_ne_gamma
--       simp
-- }
-- termination_by n
-- decreasing_by
--   all_goals { s orry }
-- StrictMono.not_bddAbove_range_of_wellFoundedLT


-- TODO - replace this with Subgroup.coe_mul_of_left_le_normalizer_right
lemma subgroup_coe_sup_invariant {G: Type*} [Group G] {A B: Subgroup G} (hab: ∀ b ∈ B, ∀ a ∈ A, (b * a * b⁻¹) ∈ A): ↑((A ⊔ B) : Subgroup G) = (A: Set G) * (B: Set G) := by
  ext a
  simp
  refine ⟨?_, ?_⟩
  .
    intro ha
    rw [Subgroup.sup_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      cases hx
      . rename_i x_mem_a
        conv =>
          arg 2
          equals x * 1 => simp
        apply Set.mul_mem_mul
        . exact x_mem_a
        . simp
      .
        rename_i x_mem_b
        conv =>
          arg 2
          equals 1 * x => simp
        apply Set.mul_mem_mul
        . simp
        . simpa using x_mem_b
    | one =>
      conv =>
        arg 2
        equals 1 * 1 => simp
      apply Set.mul_mem_mul
      . simp
      . simp
    | mul x y hx hy x_mem y_mem =>
      rw [Set.mem_mul] at x_mem y_mem
      obtain ⟨b, b_mem, c, c_mem, x_eq⟩ := x_mem
      obtain ⟨d, d_mem, e, e_mem, y_eq⟩ := y_mem

      rw [← x_eq, ← y_eq]
      rw [mul_assoc]
      nth_rw 2 [← mul_assoc]
      conv =>
        arg 2
        equals (b * (c * d * c⁻¹)) * (c * e) =>
          group

      apply Set.mul_mem_mul
      . simp
        apply Subgroup.mul_mem
        . simpa using b_mem
        .
          apply hab
          . simpa using c_mem
          . simpa using d_mem
      .
        simp
        apply Subgroup.mul_mem
        . simpa using c_mem
        . simpa using e_mem
    | inv x hx other =>
      rw [← Set.mem_inv]
      simp [-Set.mem_inv]
      rw [Set.mem_mul] at other
      obtain ⟨a, ha, b, hb, x_eq⟩ := other
      rw [← x_eq]
      conv =>
        arg 2
        equals b * (b⁻¹ * a * b) =>
          group

      apply Set.mul_mem_mul
      . exact hb
      .
        have foo := hab b⁻¹ (by simpa using hb) a ha
        simpa using foo
  . intro ha
    rw [Set.mem_mul] at ha
    obtain ⟨x, hx, y, hy, hxy⟩ := ha
    rw [Subgroup.sup_eq_closure]
    rw [Subgroup.closure_union]
    rw [← hxy]
    apply Subgroup.mul_mem_sup
    . apply Subgroup.mem_closure_of_mem
      exact hx
    . apply Subgroup.mem_closure_of_mem
      exact hy

-- TODO - generalize and upstream to mathlib
lemma set_smul_eq_mul {G: Type*} [Group G] (g: G) (A: Set G): g • A = {g} * A := by
  ext a
  rw [Set.mem_smul_set]
  rw [Set.mem_mul]
  simp


-- TODO - add an explicit top-level universe parameter to avoid this 'omit hGS' hack
set_option maxHeartbeats 2500000 in
omit hGS in
lemma theorem_3_1.{u} [hGS: Generates.{u}] (data: Theorem3_1_Input G) (d: ℕ) (hd: 1 ≤ d) (h_growth: HasPolynomialGrowthD S d)
(inductive_gromov: ∀ (Q_generates: Generates.{u}),(Q_growth : (HasPolynomialGrowthD (Q_generates.S)) (d - 1)) → Group.IsVirtuallyNilpotent Q_generates.G)
: Group.IsVirtuallyNilpotent G := by

  have G'_finite_index := data.finite_index
  have G'_fg: Group.FG data.G' := by
    apply Subgroup.fg_of_index_ne_zero

  -- A symmetric generating set for G'
  let S_G' := G'_fg.out.choose ∪  G'_fg.out.choose⁻¹ ∪ {1}

  -- TODO - factor out this proof that a subgroup has polynomial growth
  have G'_poly: HasPolynomialGrowthD (G := data.G') S_G' d := by
    unfold HasPolynomialGrowthD
    obtain ⟨a, ha⟩ := h_growth

    have a_pos: 0 < a := by
      by_contra!
      simp at this
      simp [this] at ha
      specialize ha 1 (by simp)
      simp at ha
      have s_one := hGS.one_mem
      grind

    have my_equiv := poly_growth_equiv a d a_pos S (Finset.image Subtype.val S_G')
      S_eq_Sinv hGS.one_mem (by simpa using hGS.generates) ha

    obtain ⟨b, hb, poly_growth_G'⟩ := my_equiv

    use b
    intro n hn
    rw [← Finset.card_image_of_injective (f := data.G'.subtype)]
    .
      rw [Finset.image_pow]
      exact poly_growth_G' n hn
    . simp

  have inhabited_G': Inhabited data.G' := by
    use 1
    simp

  have inhabited_G: Inhabited G := by
    use 1

  -- TODO - figure out how to avoid registering this instance
  let new_generates: Generates := {
    G := data.G'
    g_group := by infer_instance
    g_eq := by infer_instance
    S := S_G'
    hS := by
      simp [S_G']
    generates := by
      simp [S_G']
      rw [Subgroup.closure_union]
      rw [G'_fg.out.choose_spec]
      simp
    one_mem := by
      simp [S_G']
    has_inv := by
      intro g hg
      unfold S_G'
      unfold S_G' at hg
      rw [← Finset.mem_inv']
      simp
      simp at hg
      grind
    g_infinite := by
      have index_ne := G'_finite_index.index_ne_zero
      simp [Subgroup.index] at index_ne
      -- TODO - generalize and upstream this to mathlib
      by_contra!
      have finite_iff := Subgroup.finite_iff_finite_and_finiteIndex data.G'
      simp [this, G'_finite_index] at finite_iff
      have G_infinite := hGS.g_infinite
      rw [← not_finite_iff_infinite] at G_infinite
      contradiction
    g_growth := by
      use d
  }


  obtain ⟨γ, hγ⟩ := data.hφ 1
  let bad_instance: Generates := {
    G := data.G'
    S := S_G'
    g_group := by infer_instance
    g_eq := inferInstance
    hS := by
      use 1
      unfold S_G'
      simp
    generates := by
      unfold S_G'
      simp
      rw [Subgroup.closure_union]
      have foo := G'_fg.out.choose_spec
      simp [foo]
    one_mem := by
      simp [S_G']
    has_inv := by
      unfold S_G'
      intro g
      rw [← Finset.mem_inv']
      simp
      nth_rw 2 [or_comm]
      simp
    g_infinite := by
      have foo := Infinite.of_surjective _ data.hφ
      exact foo
    g_growth := by
      use d
  }
  -- TODO - why can't this be an inline instance for hGS
  obtain ⟨n, generates_with_n⟩ := three_two_S_n_generates  (hGS := bad_instance) d hd G'_poly data.φ γ hγ
  have kernel_poly := three_two_kernel_poly_growth (hGS := new_generates) d hd n G'_poly data.φ γ hγ
  have kernel_fg := three_two_ker_fg d hd G'_poly data.φ data.hφ
  --have kernel_poly_fg_out := poly_growth_equiv_generates new_generates kernel_fg.choose (d := 2)




  rw [← AddGroup.fg_iff_addSubgroup_fg] at kernel_fg
  rw [AddGroup.fg_iff_mul_fg] at kernel_fg




  let orig_ker_phi := (S_n_ker_phi S data.φ γ hγ 1)

  let new_generate_data: GeneratesWithParam data.G' := {
    S := new_generates.S
    hS := new_generates.hS
    generates := new_generates.generates
    one_mem := new_generates.one_mem
    has_inv := new_generates.has_inv
    g_infinite := new_generates.g_infinite
  }

  have kernel_virtually_nilpotent: Group.IsVirtuallyNilpotent (Multiplicative data.φ.ker) := by
    by_cases kernel_finite: Finite (Multiplicative data.φ.ker)
    .
      rw [Group.IsVirtuallyNilpotent]
      use ⊥
      refine ⟨?_, ?_⟩
      . exact Group.isNilpotent_of_subsingleton
        -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
      . infer_instance
    .
      rw [not_finite_iff_infinite] at kernel_finite

      have new_kernel_poly := kernel_poly
      -- TODO - get rid of defeq abuse
      conv at new_kernel_poly =>
        arg 1
        equals (((Finset.image Additive.toMul (S_n_ker_phi S data.φ γ hγ n)) ∪ (Inv.inv (α := Finset (Multiplicative _))) (Finset.image Additive.toMul ((S_n_ker_phi S data.φ γ hγ n))))) =>
          ext a
          refine ⟨?_, ?_⟩
          . intro ha
            rw [Finset.mem_union]
            rw [Finset.mem_image]
            simp at ha
            cases ha
            . rename_i left
              left
              use a
              refine ⟨left, rfl⟩
            . rename_i right
              right
              rw [Finset.mem_inv']
              rw [Finset.mem_image]
              use Additive.ofMul a⁻¹
              refine ⟨right, rfl⟩
          .
            intro ha
            rw [Finset.mem_union] at ha
            rw [Finset.mem_union]
            cases ha
            . rename_i left
              simp at left
              left
              exact left
            . rename_i right
              rw [Finset.mem_inv'] at right
              rw [Finset.mem_image] at right
              obtain ⟨b, hb, a_eq⟩ := right
              right
              rw [Finset.mem_inv']
              rw [← a_eq]
              exact hb


      let foo := ker_generates hd data new_generate_data γ hγ kernel_finite (by
        exact generates_with_n
      ) (by
        use (d - 1)
        simp only [ker_S]
        exact new_kernel_poly
      )
      let bar := inductive_gromov foo new_kernel_poly
      apply inductive_gromov foo
      exact new_kernel_poly
  .
    obtain ⟨pre_N, pre_N_nilpotent, pre_N_finiteindex⟩ := kernel_virtually_nilpotent
    let N := pre_N.normalCore
    have N_normal: N.Normal := Subgroup.normalCore_normal pre_N
    have N_finite_index: N.FiniteIndex := Subgroup.finiteIndex_normalCore pre_N
    have N_nilpotent: Group.IsNilpotent N := by
      have normalCore_iso := Subgroup.subgroupOfEquivOfLe (Subgroup.normalCore_le pre_N)
      unfold N
      rw [← Group.isNilpotent_congr normalCore_iso]
      apply Subgroup.isNilpotent

    have N_fg: Subgroup.FG N := by
      sorry

    rw [Subgroup.finiteIndex_iff] at N_finite_index
    let N' := Subgroup.closure (Set.range (fun (a: Multiplicative data.φ.ker) => a ^ N.index))



    -- Page 24 of Vikman, "G′′ is virtually nilpotent:"
    have alpha_unipotent: ∃ α: ℕ, ∃ m: ℕ, ∀ g ∈ N', Nat.iterate (fun x => ⁅x, γ.toMul^α⁆) m g.val = 1 := by
      sorry

    obtain ⟨α, m, alpha_is_unipotent⟩ := alpha_unipotent

    -- This will probably come from the proof of 'alpha_unipotent'
    have alpha_nonzero: α ≠ 0 := by
      sorry


    let new_N'_map : _ →* _ := {
      toFun := fun (g: (Multiplicative ↥data.φ.ker)) => Additive.toMul (data.φ.ker.subtype g)
      map_one' := rfl
      map_mul' := by
        intro x y
        rfl
    }


    let new_N': Subgroup (data.G') := Subgroup.map new_N'_map N'

    have N'_le_N: N' ≤ N := by
      unfold N'
      simp
      intro n hn
      rw [Set.mem_range] at hn
      obtain ⟨a, ha⟩ := hn
      rw [← ha]
      apply Subgroup.pow_index_mem

    have N'_nilpotent: Group.IsNilpotent N' := by
      rw [← Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe N'_le_N)]
      -- TODO - why isn't 'N_nilpotent' found by typeclass synthesis?
      apply isNilpotent (N'.subgroupOf N) (hG := N_nilpotent)



    have N'_char: Subgroup.Characteristic N' := by
      rw [Subgroup.characteristic_iff_map_eq]
      intro f
      unfold N'
      simp
      rw [MonoidHom.map_closure]
      simp
      congr
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        rw [Set.mem_image] at ha
        obtain ⟨b, hb, ab_eq⟩ := ha
        rw [Set.mem_range] at hb
        obtain ⟨c, hc⟩ := hb
        rw [← hc] at ab_eq
        simp at ab_eq
        grind
      . intro ha
        rw [Set.mem_range] at ha
        obtain ⟨b, hb⟩ := ha
        rw [← hb]
        rw [Set.mem_image]
        use f⁻¹ (b ^ N.index)
        refine ⟨?_, by simp⟩
        simp

    have N'_normal: N'.Normal := by
      infer_instance


    have N'_index: N'.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff]
      rw [← Subgroup.relIndex_mul_index N'_le_N]
      simp
      refine ⟨?_, ?_⟩
      .
        unfold Subgroup.relIndex
        rw [← ne_eq, ← Subgroup.finiteIndex_iff]
        rw [Subgroup.finiteIndex_iff_finite_quotient]
        -- TODO - why do we need this explicit instance?
        have foo : Group.IsNilpotent (↥N ⧸ N'.subgroupOf N) := by
          infer_instance
        apply finite_of_nilpotent_fg_order
        intro n
        rw [isOfFinOrder_iff_pow_eq_one]
        use N.index
        refine ⟨by omega, ?_⟩
        -- TODO - there should be a much simpler proof
        let a := n.out
        rw [← QuotientGroup.out_eq' (a := n)]
        conv =>
          lhs
          arg 1
          equals QuotientGroup.mk' _ (n).out =>
            rfl

        rw [← MonoidHom.map_pow]
        simp only [QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq_one_iff]
        rw [Subgroup.mem_subgroupOf]
        unfold N'
        apply Subgroup.mem_closure_of_mem
        rw [Set.mem_range]
        use n.out
        simp
      .
        exact N_finite_index
      -- simp

      -- unfold N'


    have N'_fg: Subgroup.FG N' := by
      rw [← Group.fg_iff_subgroup_fg]
      apply Subgroup.fg_of_index_ne_zero




    --have new_alpha := center_unipotent N'_fg γ.toMul

    -- TODO - generalize and upstream to mathlib
    have phi_ker_normal: (AddSubgroup.toSubgroup' data.φ.ker).Normal := by
      have phi_normal: data.φ.ker.Normal := by
        infer_instance
      --exact phi_normal
      exact {
        conj_mem := by
          intro a ha g
          have foo := phi_normal.conj_mem a ha g
          exact foo
      }

    -- have N'_nilpotent: Group.IsNilpotent ↥N' := by
    --   exact N'_nilpotent

    haveI : Subgroup.Characteristic N' := N'_char
    have alpha_nilpotent := unipotent_commutator_trivial (G := data.G') (H := data.φ.ker.toSubgroup') (N' := N') (N'_char := N'_char) (N'_nilpotent := by
      exact N'_nilpotent
    ) (γ.toMul^α) (by
      simp
      intro hx
      by_contra!

      have gamma_alpha_mem_ker: (γ.toMul^α) ∈ data.φ.ker := by
        -- This is *not* called 'extract_proofs'
        generalize_proofs at this
        rename_i mem_ker
        exact mem_ker

      simp at gamma_alpha_mem_ker
      clear * - hγ α gamma_alpha_mem_ker alpha_nonzero
      have gak : data.φ (α • γ) = 0 := gamma_alpha_mem_ker
      rw [AddMonoidHom.map_nsmul, hγ] at gak
      simp at gak
      exact alpha_nonzero gak
    ) m alpha_is_unipotent

    have map_N'_invariant_gamma {n: ℕ}: ∀ b ∈ Subgroup.closure {γ.toMul^n}, ∀ a ∈ map new_N'_map N', b * a * b⁻¹ ∈ map new_N'_map N'  := by
      intro gamma_pow h_gamma_pow n hn
      let conj_aut := MulAut.conjNormal gamma_pow (H := data.φ.ker.toSubgroup')
      have conj_map := N'_char.fixed conj_aut
      rw [Subgroup.ext_iff] at conj_map
      rw [Subgroup.mem_map]

      have conj_mem_ker: gamma_pow * n * gamma_pow⁻¹ ∈ data.φ.ker := by
        rw [Subgroup.mem_map] at hn
        obtain ⟨y, hy, n_eq⟩ := hn
        have hn0 : data.φ (Additive.ofMul n) = 0 := by
          rw [← n_eq]
          exact y.2
        show data.φ (Additive.ofMul gamma_pow + Additive.ofMul n + (-(Additive.ofMul gamma_pow))) = 0
        rw [map_add, map_add, map_neg, hn0]
        abel

      use ⟨gamma_pow * n * gamma_pow⁻¹, conj_mem_ker⟩
      .
        refine ⟨?_, ?_⟩
        .

          rw [Subgroup.mem_map] at hn
          obtain ⟨y, hy, n_eq⟩ := hn
          conv =>
            arg 2
            equals conj_aut y =>
              rw [Subtype.ext_iff]
              simp [conj_aut]
              simp [← n_eq, new_N'_map]
              rfl
          specialize conj_map y
          simp [hy] at conj_map
          exact conj_map
        .
          rfl

    have map_N'_invariant_gamma_one := map_N'_invariant_gamma (n := 1)
    simp only [pow_one] at map_N'_invariant_gamma_one

    rw [Group.IsVirtuallyNilpotent]
    rw [Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ (Subgroup.subtype _) (by simp))] at alpha_nilpotent
    -- TODO - this is wrong. We need to use {toMul γ} so that we can prove that it has finite index (G'' is defined using
    -- just gamma, not gamma^alpha)
    use (map data.G'.subtype (Subgroup.closure (↑(map (AddSubgroup.toSubgroup' data.φ.ker).subtype N') ∪ {toMul γ ^ α})))
    refine ⟨?_, ?_⟩
    . exact alpha_nilpotent
    .
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map]
      simp
      refine ⟨?_, ?_⟩
      .

        simp_rw [Set.insert_eq]

        have gamma_alpha_le_gamma: (Subgroup.closure ({toMul γ ^ α} ∪ (new_N'_map '' N')) ≤ (Subgroup.closure ({toMul γ} ∪ (new_N'_map '' N')))) := by
          simp
          intro g hg
          rw [Set.insert_eq]
          cases hg
          . rename_i g_eq_gamma
            rw [Subgroup.closure_union]
            apply Subgroup.mem_sup_left
            rw [Subgroup.mem_closure_singleton]
            use α
            rw [g_eq_gamma]
            simp
          . rename_i g_mem_map
            rw [Subgroup.closure_union]
            apply Subgroup.mem_sup_right
            apply Subgroup.mem_closure_of_mem
            exact g_mem_map

        conv =>
          arg 1
          arg 1
          arg 1
          arg 1
          arg 2
          equals (new_N'_map '' N') => rfl
        rw [← Subgroup.relIndex_mul_index gamma_alpha_le_gamma]
        simp
        refine ⟨?_, ?_⟩
        .
          unfold Subgroup.relIndex
          rw [← ne_eq]
          rw [← Subgroup.finiteIndex_iff]
          apply Subgroup.finiteIndex_of_rightCoset_cover_const (s := Finset.Ioo (-α : ℤ) (α)) (g := fun a => ⟨a • γ, (by
            rw [Set.insert_eq, Subgroup.closure_union]
            apply Subgroup.mem_sup_left
            rw [Subgroup.mem_closure_singleton]
            use a
            rfl
          )⟩)
          ext g
          simp
          have g_prop := g.property
          simp_rw [Set.insert_eq, Subgroup.closure_union] at g_prop
          rw [← MonoidHom.map_closure] at g_prop
          simp at g_prop
          rw [← SetLike.mem_coe] at g_prop
          rw [sup_comm] at g_prop


          rw [subgroup_coe_sup_invariant map_N'_invariant_gamma_one] at g_prop
          rw [Set.mem_mul] at g_prop
          obtain ⟨b, hb, a, ha, g_eq⟩ := g_prop
          simp at ha
          rw [Subgroup.mem_closure_singleton] at ha
          obtain ⟨z, hz⟩ := ha
          use z % α
          refine ⟨?_, ?_⟩
          .
            have foo := Int.emod_lt_abs z (b := α) (by grind)
            rw [lt_abs] at foo
            refine ⟨?_, ?_⟩
            .
              have bar := Int.emod_nonneg z (b := α) (by simpa using alpha_nonzero)
              grind
            . grind
          .
            rw [Set.mem_smul_set]
            use ⟨(Additive.ofMul b) + (((α : ℤ) * (z / (α : ℤ))) • γ), ?_⟩
            .
              refine ⟨?_, ?_⟩
              .
                simp
                rw [Subgroup.mem_subgroupOf]
                simp_rw [Set.insert_eq, Subgroup.closure_union]
                rw [← SetLike.mem_coe]
                rw [sup_comm]
                rw [subgroup_coe_sup_invariant (by
                  simp_rw [← MonoidHom.map_closure, Subgroup.closure_eq]
                  apply map_N'_invariant_gamma
                )]
                apply Set.mul_mem_mul
                .
                  simp
                  apply Subgroup.mem_closure_of_mem
                  exact hb
                .
                  simp
                  rw [Subgroup.mem_closure_singleton]
                  use (z / (α : ℤ))
                  conv =>
                    lhs
                    arg 1
                    equals toMul γ ^ (α : ℤ) =>
                      simp

                  rw [← zpow_mul]
              .
                simp
                rw [Subtype.ext_iff]
                simp
                rw [← g_eq, ←hz]
                nth_rw 3 [← Int.mul_ediv_add_emod (a := z) (b := α)]
                rw [← toMul_zsmul]
                conv =>
                  lhs
                  equals (ofMul b) + ((↑α * (z / ↑α)) • γ) + ((z % ↑α) • γ) =>
                    rfl



                rw [add_zsmul]
                rw [add_assoc]
                rfl
            .
              simp_rw [Set.insert_eq, Subgroup.closure_union]
              rw [sup_comm]
              rw [← SetLike.mem_coe]

              rw [subgroup_coe_sup_invariant (by
                simp_rw [← MonoidHom.map_closure, Subgroup.closure_eq]
                apply map_N'_invariant_gamma_one
              )]
              apply Set.mul_mem_mul
              .
                simp
                apply Subgroup.mem_closure_of_mem
                exact hb
              .
                simp [Subgroup.mem_closure_singleton]
        .
          obtain ⟨s, s_compl, s_cosets⟩ := Subgroup.exists_leftTransversal_of_FiniteIndex (D := N') (H := ⊤) (by simp)
          simp at s_cosets

          rw [← ne_eq]
          rw [← Subgroup.finiteIndex_iff]
          apply Subgroup.finiteIndex_of_leftCoset_cover_const (s := s) (g := fun g => g.val.val.toMul)
          simp_rw [Set.insert_eq, Subgroup.closure_union]
          rename_bvar i → g

          -- let N'_normal: N'.Normal := by
          --   infer_instance

          -- rw [← Set.iUnion_smul]
          -- rw [Subgroup.coe_sup]
          -- let A: Subgroup data.G' := ⊤
          --have bar := Subgroup.coe_pointwise_smul (1 : A) A
          conv =>
            arg 1
            arg 1
            intro i
            arg 1
            intro hi
            rw [sup_comm]
            rw [subgroup_coe_sup_invariant (by
              intro gamma_pow h_gamma_pow n hn
              conv at hn =>
                arg 1
                equals ((Subgroup.closure (new_N'_map '' ↑N'))) =>
                  rfl
              simp_rw [← MonoidHom.map_closure] at hn
              simp only [closure_eq] at hn
              conv =>
                arg 1
                equals ((Subgroup.closure (new_N'_map '' ↑N'))) =>
                  rfl
              simp_rw [← MonoidHom.map_closure]
              simp only [closure_eq]
              apply map_N'_invariant_gamma_one _ h_gamma_pow _ hn
            )]
            rw [set_smul_eq_mul]
            rw [← mul_assoc]
            rw [← set_smul_eq_mul]


          simp_rw [← Set.iUnion_mul]
          conv =>
            arg 1
            arg 1
            equals Additive.toMul '' data.φ.ker =>
              apply_fun (fun s => Additive.toMul '' (Subtype.val '' s)) at s_cosets
              conv at s_cosets =>
                rhs
                equals Additive.toMul '' data.φ.ker =>
                  ext a
                  simp
                  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Set.mem_univ _⟩⟩
              rw [← s_cosets]
              conv =>
                arg 1
                arg 1
                intro i
                arg 1
                intro hi
                arg 2
                equals ↑((Subgroup.closure (new_N'_map '' ↑N'))) =>
                  rfl

              simp_rw [← MonoidHom.map_closure]

              simp only [Set.image_image]
              first
                | erw [Set.image_iUnion₂]
                | rw [Set.image_iUnion₂]
                | simp only [Set.image_iUnion]
              apply Set.iUnion_congr
              intro i
              apply Set.iUnion_congr
              intro hi
              ext z
              simp only [closure_eq, coe_map]
              rw [Set.mem_smul_set]
              rw [Set.mem_image]
              refine ⟨?_, ?_⟩
              .
                intro hy
                obtain ⟨a, ha⟩ := hy
                have foo := ha.1
                rw [Set.mem_image] at foo
                obtain ⟨b, b_mem, a_eq_b⟩ := foo
                refine ⟨(↑i : Multiplicative ↥data.φ.ker) • b, Set.smul_mem_smul_set b_mem, ?_⟩
                rw [← ha.2, ← a_eq_b]
                rfl
              .
                intro hx
                obtain ⟨x, hx, x_eq⟩ := hx
                erw [Set.mem_smul_set] at hx
                obtain ⟨n, hn, x_eq_n⟩ := hx
                refine ⟨new_N'_map n, ?_, ?_⟩
                .
                  rw [Set.mem_image]
                  exact ⟨n, hn, rfl⟩
                . rw [← x_eq, ← x_eq_n]
                  rfl



          conv =>
            arg 1
            lhs
            equals ↑data.φ.ker.toSubgroup' =>
              ext a
              simp

          rw [← subgroup_coe_sup_invariant]
          .
            simp
            rw [eq_top_iff]
            have ker_gen := e_i_and_gamma_generates_G data.φ γ hγ
            have foo := new_generates.generates
            simp at foo
            rw [← foo, ← ker_gen]
            simp_rw [Subgroup.closure_union]
            conv =>
              lhs
              arg 1
              equals Subgroup.closure {γ.toMul} =>
                simp [Subgroup.closure_union]
                conv =>
                  lhs
                  arg 1
                  equals {γ.toMul, γ.toMul⁻¹} => rfl
                rw [Set.insert_eq]
                rw [Subgroup.closure_union]
                simp

            simp_rw [← Subgroup.closure_union]
            rw [Subgroup.closure_le]
            rw [Set.union_subset_iff]
            refine ⟨?_, ?_⟩
            .
              intro a ha
              simp at ha
              simp
              apply Subgroup.mem_sup_right
              simp [ha]
            .
              intro a ha
              apply Subgroup.mem_sup_left
              simp
              simp at ha
              obtain ⟨p, hp, a_eq⟩ := ha
              simp [e_i_with_gamma] at a_eq
              rw [← a_eq]
              conv =>
                arg 1
                arg 2
                equals (ofMul p) + -((data.φ (ofMul p)) • γ) =>
                  rfl


              simp [hγ]
              group
          .
            intro b hb a ha
            rw [Subgroup.mem_closure_singleton] at hb
            obtain ⟨n, b_eq⟩ := hb
            simp [← b_eq]
            simp at ha
            exact ha
      . have foo := data.finite_index
        rw [Subgroup.finiteIndex_iff] at foo
        exact foo



-- Decompose list of {e_k, γ}:

-- The starting list must have the powers of γ sum to zero (since it's in the kernel of φ)


-- Map the list in a way that maintains the invariant that the powers of γ sum to zero:
-- If the head is e_i, then map it to γ_0,i = e_i
-- Otherwise, collect gamma terms:
-- If we get γ^a e_i * γ^b, then
-- * If the head is γ^n e_i for some n (collecting up adjacent γ), then choose γ_n,i = γ^n * e_i * γ^(-n)
-- * If the remaining list is just γ^n, then n must be 0 (since we maintained the invariant)

#print axioms three_two_gamma_m_generates
#print axioms three_two_ker_fg

-- NOTE: from https://www.numdam.org/item/PMIHES_1981__53__53_0.pdf
-- it looks like our definition of 'polynomial growth' should use `S ∪ S⁻¹`
lemma main_gromov_theorem (n: ℕ) (h: HasPolynomialGrowthD S n): Group.IsVirtuallyNilpotent G := by
  induction hn: n generalizing hGS n with
  | zero =>
    simp [HasPolynomialGrowthD] at h
    obtain ⟨a, ha⟩ := h
    simp [hn] at ha

    have S_closure := hGS.generates

    let pow_cards := Set.range (fun (n: ℕ) => #(S ^ n))
    -- TODO - this can probably be much simpler
    have pow_cards_bounded: ∃ y, ∀ n ∈ pow_cards, n ≤ y := by
      use a
      intro n hn
      simp [pow_cards] at hn
      obtain ⟨y, hy⟩ := hn
      rw [← hy]

      by_cases y_eq_zero: y = 0
      . simp [y_eq_zero]

        -- TODO - deduplicate this
        have a_ne_zero: a ≠ 0 := by
          by_contra!
          rw [this] at ha
          have hg_one := ha 1 (by omega)
          simp at hg_one
          have one_mem := hGS.one_mem
          rw [hg_one] at one_mem
          simp at one_mem

        omega
      . by_cases y_eq_one: y = 1
        .
          simp [y_eq_one]
          have card_mono := Finset.card_pow_mono (s := S) (m := 1) (n := 2) (by simp) (by simp)
          have card_two_le := ha 2 (by simp)
          simp at card_mono
          linarith
        .
          exact ha y (by omega)



    classical
    have max_card_mem := Nat.sSup_mem (s := pow_cards) ?_ ?_
    . simp [pow_cards] at max_card_mem
      obtain ⟨y, hy⟩ := max_card_mem



      have all_closure_mem: ∀ s ∈ (Subgroup.closure S), s ∈ (S ^ y) := by
        intro s hs
        induction hs using Subgroup.closure_induction with
        | one =>
          apply Finset.one_mem_pow
          exact Generates.one_mem
        | mem x hx =>
          by_cases y_eq_zero: y = 0
          .
            rw [y_eq_zero]
            rw [y_eq_zero] at hy
            simp at hy
            simp
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have S_one_le := find_le #(S) ?_
            .
              simp [pow_cards] at S_one_le
              rw [← hy] at S_one_le
              rw [Finset.card_le_one] at S_one_le
              have one_mem: 1 ∈ S := by exact Generates.one_mem
              have x_eq := S_one_le 1 one_mem x hx
              apply x_eq.symm
            . simp [pow_cards]
              use 1
              simp
          .
            have pow_mono := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (n := y) (m := 1) (by omega)
            simp at pow_mono
            apply pow_mono hx
        | mul a b a_mem_closure b_mem_closure a_mem_pow b_mem_pow =>
          by_cases y_eq_zero: y = 0
          .
            simp [y_eq_zero]
            simp [y_eq_zero] at a_mem_pow b_mem_pow
            simp [a_mem_pow, b_mem_pow]
          .
            by_contra!
            have a_b_mem_two: a * b ∈ (S ^ (y * 2)) := by
              have mem_mul := Finset.mul_mem_mul a_mem_pow b_mem_pow
              rw [← pow_two] at mem_mul
              rw [← pow_mul] at mem_mul
              exact mem_mul

            have card_le := Finset.card_pow_mono (s := S) (m := y) (n := (y * 2))  (by omega) (by omega)
            have subset := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (m := y) (n := (y * 2)) (by omega)

            have strict_subset : (S ^ y) ⊂ (S ^ (y * 2)) := by
              rw [Finset.ssubset_iff_of_subset subset]
              use (a * b)

            have card_lt: #(S ^ y) < #(S ^ (y * 2)) := by
              exact Finset.card_lt_card strict_subset


            rw [hy] at card_lt
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have reverse_le := find_le #(S ^ (y * 2)) ?_
            .
              simp [pow_cards] at reverse_le
              linarith
            . simp [pow_cards]
        | inv a ha a_mem_pow =>
          rw [← Finset.mem_inv']
          rw [← inv_pow]
          rw [← S_eq_Sinv]
          exact a_mem_pow

      have G_finite: Finite G := by
        rw [← Set.finite_univ_iff]
        have univ_eq: (Set.univ : Set G) = (S ^ y) := by
          simp at S_closure

          apply_fun (fun y => y.carrier) at S_closure
          conv at S_closure =>
            rhs
            equals Set.univ =>
              exact rfl

          rw [← S_closure]
          ext a
          refine ⟨?_, ?_⟩
          . intro ha
            simp at ha
            rw [← Finset.coe_pow]
            exact all_closure_mem a ha
          . intro ha
            simp
            exact mem_closure a

        rw [univ_eq]
        rw [← Finset.coe_pow]
        exact Finset.finite_toSet (S ^ y)

      rw [Group.IsVirtuallyNilpotent]
      use ⊥
      refine ⟨?_, ?_⟩
      . exact Group.isNilpotent_of_subsingleton
        -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
      . infer_instance
    .
      simp [pow_cards]
      apply Set.range_nonempty
    .
      rw [bddAbove_def]
      exact pow_cards_bounded
  | succ k ih =>
    obtain ⟨data⟩ := exists_theorem_3_1_input h
    -- Consider changing 'theorem_3_1' to make 'inductive_gromov' take in 'Generates',
    -- to avoid fiddling with 'FG.out' (which might not be symmetric)
    apply theorem_3_1 data n (by omega) h
    intro Q_generates Q_poly

    by_cases Q_finite: Finite Q_generates.G
    .
      rw [Group.IsVirtuallyNilpotent]
      use ⊥
      refine ⟨?_, ?_⟩
      . exact Group.isNilpotent_of_subsingleton
        -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
      . infer_instance
    .
      -- let generates: Generates := {
      --   G := Q,
      --   g_group := Q_group
      --   g_eq := Q_dec_eq
      --   S := Q_FG.out.choose ∪ Q_FG.out.choose⁻¹ ∪ {1}
      --   hS := by simp
      --   generates := by
      --     simp
      --     rw [Subgroup.closure_union]
      --     rw [Q_FG.out.choose_spec]
      --     simp
      --   one_mem := by
      --     simp
      --   has_inv := by
      --     intro g hg
      --     simp at hg
      --     simp
      --     grind
      --   g_infinite := by
      --     simpa using Q_finite
      -- }
      have prev := @ih Q_generates (n - 1) Q_poly (by omega)
      exact prev
