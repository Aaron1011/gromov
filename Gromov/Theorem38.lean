module

public import Mathlib
public import Gromov.Representation

/-!
# Theorem 3.8

`theorem_3_8` and its real form: a group of polynomial growth admits a nontrivial
finite-dimensional representation.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.cdot false
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

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

omit hGS in
set_option maxHeartbeats 500000 in
lemma theorem_3_8 {V: Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (H: Subgroup (V →L[ℂ] V)ˣ) [DecidableEq H] (h_compact: CompactSpace H) (G: Subgroup H) (G_fg: G.FG) (S_data: SPolyData G): ∃ A: Subgroup G, IsMulCommutative A ∧ A.FiniteIndex := by
  obtain ⟨H', ⟨H_equiv_H'⟩⟩ := new_weyl_unitarian_trick (V := V) (H := H)
  let G' := Subgroup.map H'.subtype (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  let my_hom := MonoidHom.ofInjective (f := H'.subtype) (by exact subtype_injective H')
  let other := Subgroup.map my_hom.toMonoidHom (Subgroup.map H_equiv_H'.symm.toMonoidHom G)

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
      have key : (MonoidHom.ofInjective (subtype_injective H')).symm
          ⟨H'.subtype (H_equiv_H'.symm.toMonoidHom y), ⟨_, rfl⟩⟩
            = H_equiv_H'.symm.toMonoidHom y :=
        subtype_injective H' (MonoidHom.apply_ofInjective_symm _ _)
      rw [key]
      simpa using y_mem
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
        . have dim_eq_one: Module.finrank ℂ (V) = 1 := by omega
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

    let new_S_data := map_S_data G (f := H'.subtype.comp (H_equiv_H'.symm.toMonoidHom)) S_data
    obtain ⟨N, N_comm, N_finite_index⟩ := compact_lie_virtually_abelian (Module.finrank ℂ V) (by omega) G' G'_fg (by
      unfold G'
      rw [Subgroup.map_map]
      exact new_S_data
    )

    let new_N := N
    simp [G'] at new_N


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
              . have key : (MonoidHom.ofInjective (subtype_injective H')).symm
                    ⟨↑(H_equiv_H'.symm (↑a : ↥H)), ⟨H_equiv_H'.symm (↑a : ↥H), rfl⟩⟩
                      = H_equiv_H'.symm (↑a : ↥H) :=
                  subtype_injective H' (MonoidHom.apply_ofInjective_symm _ _)
                exact Subtype.ext ((congrArg H_equiv_H' key).trans
                  (H_equiv_H'.apply_symm_apply _))
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

end GeneratesNS
