module

public import Mathlib
public import Gromov.Unitary.Packing

/-!
# The unitarian trick

`new_weyl_unitarian_trick`: a bounded subgroup of `GL` is conjugate into the unitary group.
-/

public section

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative

set_option maxSynthPendingDepth 1

attribute [local implicit_reducible] FreshInnerProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
lemma new_weyl_unitarian_trick {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]  (H : Subgroup (V →L[ℂ] V)ˣ)   [LocallyCompactSpace H] [CompactSpace H]: ∃ S : Subgroup ↥(Matrix.unitaryGroup (Fin (Module.finrank ℂ V)) ℂ), Nonempty (S ≃* H) := by
  let integrand := fun (v w : FreshInnerProduct V) (h : H) => ⟪(h.val.val v), (h.val.val w)⟫
  have continuous_integrand : ∀ v w : FreshInnerProduct V, Continuous fun h : H => integrand v w h := by
    intro v w
    simp only [integrand]
    fun_prop

  borelize (V →L[ℂ] V)ˣ

  --

  have finite_dimensional_fresh : FiniteDimensional ℂ (FreshInnerProduct V) := inferInstanceAs (FiniteDimensional ℂ V)

  have integrable_on : ∀ v w : V, MeasureTheory.Integrable (integrand v w) (MeasureTheory.Measure.haar.inv (G := H)) := by
    intro v w
    rw [← MeasureTheory.integrableOn_univ]
    apply ContinuousOn.integrableOn_compact
    · exact CompactSpace.isCompact_univ
    · apply (continuous_integrand v w).continuousOn


  let inner_product_core : InnerProductSpace.Core ℂ (FreshInnerProduct V) := {
    inner := fun v w => MeasureTheory.integral (MeasureTheory.Measure.haar.inv) (integrand v w)
    conj_inner_symm := by
      intro x y
      simp only [integrand]
      simp_rw [show ∀ h : ↥H, (⟪(h.val.val x : V), (h.val.val y : V)⟫ : ℂ)
          = (starRingEnd ℂ) ⟪(h.val.val y : V), (h.val.val x : V)⟫
        from fun h => (inner_conj_symm _ _).symm]
      exact integral_conj.symm
    re_inner_nonneg := by
      intro x
      simp [integrand]
      conv =>
        rhs
        arg 1
        arg 2
        intro h
        equals ⟪h.val.val x, h.val.val x⟫ =>
          simp
      conv =>
        rhs
        arg 1
        arg 2
        intro h
        rw [← inner_self_ofReal_re]
      simp
      rw [integral_complex_ofReal]
      apply MeasureTheory.integral_nonneg
      rw [Pi.le_def]
      intro y
      simp
      rw [← RCLike.re_to_complex]
      simp
      rw [Complex.re_nonneg_iff_nonneg]
      .
        norm_cast
        positivity
      . rw [isSelfAdjoint_iff]
        simp
    add_left := by
      intro a b c
      have hpt : (integrand (a + b) c) = (fun h => integrand a c h + integrand b c h) := by
        funext h
        simp only [integrand]
        rw [show (h.val.val (a + b) : V) = h.val.val a + h.val.val b from map_add _ _ _,
          inner_add_left]
      rw [hpt]
      exact MeasureTheory.integral_add (integrable_on a c) (integrable_on b c)
    smul_left := by
      intro x y z
      have hpt : (integrand (z • x) y) = (fun h => (starRingEnd ℂ) z * integrand x y h) := by
        funext h
        simp only [integrand]
        rw [show (h.val.val (z • x) : V) = z • h.val.val x from map_smul _ _ _, inner_smul_left]
      rw [hpt]
      exact MeasureTheory.integral_const_mul _ _
    definite := by
      intro x hx
      simp only [integrand] at hx
      conv at hx =>
        lhs
        arg 2
        intro h
        rw [← inner_self_ofReal_re]

      simp at hx
      rw [integral_complex_ofReal] at hx
      norm_cast at hx
      rw [MeasureTheory.integral_eq_zero_iff_of_nonneg ?_] at hx
      · dsimp only [Filter.EventuallyEq] at hx
        conv at hx =>
          pattern MeasureTheory.Measure.haar.inv
          rw [← MeasureTheory.Measure.restrict_univ (μ := MeasureTheory.Measure.haar.inv)]


        obtain ⟨q, _, inner_q_zero⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae ?_ hx
        conv at inner_q_zero =>
          equals ⟪(q.val.val x), (q.val.val x)⟫ = 0 =>
            rw [← inner_self_ofReal_re]
            simp
            norm_cast
            simp


        simp at inner_q_zero
        have map_iff_zero := LinearMap.map_eq_zero_iff (f := q.val.val.toLinearMap) (x := x) ?_
        · exact map_iff_zero.mp inner_q_zero
        · -- TODO - find a better way of doing this
          let my_map := (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := V)).toMonoidHom
          let f_map := (Units.map my_map) q.val
          let f_as_equiv := fun f => (LinearMap.GeneralLinearGroup.toLinearEquiv (R := ℂ) (M := V) f)
          simp [LinearMap.GeneralLinearGroup] at f_as_equiv
          have injective_f := (f_as_equiv f_map).injective
          simp [f_as_equiv, f_map] at injective_f
          exact injective_f
      · have foo := integrable_on x x
        simp [integrand] at foo
        norm_cast
        norm_cast at foo
        apply MeasureTheory.Integrable.re at foo
        norm_cast at foo
      · rw [Pi.le_def]
        intro y
        simpa using inner_self_nonneg (𝕜 := ℂ) (x := (y.val.val x))
  }
  · exact Ne.symm (NeZero.ne' (MeasureTheory.Measure.haar.inv Set.univ))

  let new_inner := InnerProductSpace.ofCore inner_product_core.toCore
  let normed_add := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := (FreshInnerProduct V))


  have proper_fresh : ProperSpace (FreshInnerProduct V) := by
    apply FiniteDimensional.proper_rclike ℂ _


  let apply_rep (h : H) (v : FreshInnerProduct V): FreshInnerProduct V := h.val.val v

  have v_preserves_inner : ∀ h : H, ∀ v w : FreshInnerProduct V, ⟪(apply_rep h v), (apply_rep h w)⟫ = ⟪v, w⟫ := by
    intro h v w
    show MeasureTheory.integral (MeasureTheory.Measure.haar.inv (G := H)) (integrand (apply_rep h v) (apply_rep h w))
       = MeasureTheory.integral (MeasureTheory.Measure.haar.inv (G := H)) (integrand v w)
    have hpt : integrand (apply_rep h v) (apply_rep h w) = (fun g : H => integrand v w (g * h)) := by
      funext g
      simp only [integrand, apply_rep, Subgroup.coe_mul, Units.val_mul]
      rfl
    rw [hpt]
    exact MeasureTheory.integral_mul_right_eq_self (integrand v w) h
  · -- finDimVectorspaceEquiv
    have rank_eq := Module.finrank_eq_rank' ℂ (FreshInnerProduct V)
    have V_equiv := (finDimVectorspaceEquiv (Module.finrank ℂ (FreshInnerProduct V)) rank_eq.symm).toContinuousLinearEquiv
    let V_equiv_fresh : V ≃L[ℂ] (FreshInnerProduct V) := ContinuousLinearEquiv.ofFinrankEq ?_
    let V_fresh_arrow := ContinuousLinearEquiv.arrowCongr V_equiv_fresh V_equiv_fresh

    let new_H_matrix := ContinuousLinearMap.toLinearMap '' (Units.val '' H.carrier)
    -- Deliberate defeq abuse, so that things line up with our integral (which is over plain V)
    let new_H_coe : Set ((FreshInnerProduct V) →ₗ[ℂ] (FreshInnerProduct V)) := new_H_matrix



    have V_basis := stdOrthonormalBasis ℂ (FreshInnerProduct V)

    let H_matrix := (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) '' new_H_coe


    have H_mem_unitary : ∀ h ∈ H_matrix, h ∈ Matrix.unitaryGroup (Fin (Module.finrank ℂ (FreshInnerProduct V))) ℂ := by
      intro h h_mem
      simp [H_matrix, new_H_coe, new_H_matrix] at h_mem
      obtain ⟨u, u_mem, hu⟩ := h_mem
      let a : FreshInnerProduct V →ₗ[ℂ] FreshInnerProduct V := (↑↑u : V →ₗ[ℂ] V)
      have ha : (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) a = h := hu
      rw [← ha, Matrix.mem_unitaryGroup_iff']
      -- `a` is the linear map underlying an element of `H`, so it preserves the new inner product.
      have preserves_inner : ∀ (x y : FreshInnerProduct V), ⟪a x, a y⟫ = ⟪x, y⟫ := by
        intro x y
        exact v_preserves_inner ⟨u, u_mem⟩ x y
      -- Preservation of the inner product means `adjoint a ∘ a = id`.
      have adj : a.adjoint ∘ₗ a = LinearMap.id := by
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, LinearMap.id_apply]
        apply ext_inner_right ℂ
        intro y
        rw [LinearMap.adjoint_inner_left]
        exact preserves_inner x y
      have hmat : star (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis a) *
          (LinearMap.toMatrix V_basis.toBasis V_basis.toBasis a) = 1 := by
        rw [Matrix.star_eq_conjTranspose, ← LinearMap.toMatrix_adjoint, ← LinearMap.toMatrix_comp,
          adj, LinearMap.toMatrix_id]
      exact hmat


    let H_matrix_subgroup : Subgroup (Matrix.unitaryGroup (Fin (Module.finrank ℂ V)) ℂ) := {
      carrier := Set.range (fun (h : H_matrix) => ⟨h.val, H_mem_unitary h (by simp)⟩),
      mul_mem' := by
        intro X Y hx hy
        simp
        use (X * Y).val
        simp
        simp at hx
        simp at hy
        simp [H_matrix]
        simp [H_matrix] at hx
        simp [H_matrix] at hy
        obtain ⟨a, ⟨p, p_mem, p_eq_a⟩, a_eq_x⟩ := hx
        obtain ⟨b, ⟨q, q_mem, q_eq_b⟩, b_eq_y⟩ := hy
        simp [new_H_coe, new_H_matrix] at q_mem
        simp [new_H_coe, new_H_matrix] at p_mem
        obtain ⟨y, y_mem, y_eq_q⟩ := q_mem
        obtain ⟨x, x_mem, x_eq_p⟩ := p_mem
        simp [new_H_coe, new_H_matrix]
        refine ⟨?_, rfl⟩
        have hX : X.val = a := by rw [← a_eq_x]
        have hY : Y.val = b := by rw [← b_eq_y]
        refine ⟨x * y, H.mul_mem x_mem y_mem, ?_⟩
        rw [hX, hY, ← p_eq_a, ← q_eq_b, ← LinearMap.toMatrix_mul, ← x_eq_p, ← y_eq_q]
        rfl
      one_mem' := by
        simp [H_matrix, new_H_coe, new_H_matrix]
        refine ⟨1, H.one_mem, ?_⟩
        exact LinearMap.toMatrix_one _
      inv_mem' := by
        simp
        intro a ha b hb a_eq_b
        refine ⟨a⁻¹, ?_, ?_⟩
        · simp [H_matrix, new_H_coe, new_H_matrix] at ⊢ hb
          obtain ⟨u, u_mem, hz₀⟩ := hb
          refine ⟨u⁻¹, H.inv_mem u_mem, ?_⟩
          rw [← a_eq_b, ← hz₀]
          refine (Matrix.inv_eq_left_inv ?_).symm
          rw [← LinearMap.toMatrix_mul]
          convert LinearMap.toMatrix_one (R := ℂ) V_basis.toBasis using 2
          ext v
          change (↑(u⁻¹) : V →L[ℂ] V) ((↑u : V →L[ℂ] V) v) = v
          rw [← mul_apply_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            one_apply_eq_self]
        · rw [Matrix.mem_unitaryGroup_iff] at ha
          apply Matrix.inv_eq_right_inv at ha
          rw [Subtype.ext_iff]
          show a⁻¹ = star a
          exact ha
    }

    let remove_fresh (h : FreshInnerProduct V →ₗ[ℂ] FreshInnerProduct V): (V →ₗ[ℂ] V) := h

    · use H_matrix_subgroup
      apply Nonempty.intro
      exact {
        toFun := fun h => ⟨{
          val := ((remove_fresh (h.val.val.toLin V_basis.toBasis V_basis.toBasis)).toContinuousLinearMap),
          inv := ((remove_fresh (h.val.val⁻¹.toLin V_basis.toBasis V_basis.toBasis)).toContinuousLinearMap),
          val_inv := by
            simp [remove_fresh]
            ext a
            simp
            conv =>
              lhs
              equals Matrix.toLin V_basis.toBasis V_basis.toBasis (h.val.val * h.val.val⁻¹) a =>
                rw [eq_comm]
                exact Matrix.toLin_mul_apply (v₁ := V_basis.toBasis) (v₂ := V_basis.toBasis) (v₃ := V_basis.toBasis) _ _ _
            rw [Matrix.mul_nonsing_inv]
            · exact LinearMap.congr_fun (Matrix.toLin_one (v₁ := V_basis.toBasis)) a
            · apply Matrix.UnitaryGroup.det_isUnit
          inv_val := by
            simp [remove_fresh]
            ext a
            simp
            conv =>
              lhs
              equals Matrix.toLin V_basis.toBasis V_basis.toBasis (h.val.val⁻¹ * h.val.val) a =>
                rw [eq_comm]
                exact Matrix.toLin_mul_apply (v₁ := V_basis.toBasis) (v₂ := V_basis.toBasis) (v₃ := V_basis.toBasis) _ _ _
            rw [Matrix.nonsing_inv_mul]
            · exact LinearMap.congr_fun (Matrix.toLin_one (v₁ := V_basis.toBasis)) a
            · apply Matrix.UnitaryGroup.det_isUnit
        }, by (
          simp [remove_fresh]
          have h_prop := h.property
          simp only [H_matrix_subgroup] at h_prop
          rw [← Subgroup.mem_carrier] at h_prop
          simp only [] at h_prop
          rw [Set.mem_range] at h_prop
          obtain ⟨a, ha⟩ := h_prop
          have a_prop := a.property
          simp only [H_matrix, new_H_coe, new_H_matrix] at a_prop
          rw [Set.mem_image] at a_prop
          obtain ⟨b, b_mem, b_eq_a⟩ := a_prop
          obtain ⟨c, ⟨d, d_mem, d_eq_c⟩, c_eq_b⟩ := b_mem
          simp_rw [← ha, ← b_eq_a]
          simp
          simp_rw [← c_eq_b, ← d_eq_c]
          conv =>
            arg 2
            arg 1
            equals d.val =>
              rfl

          simp
          rw [Subgroup.mem_carrier] at d_mem
          exact d_mem
        )⟩
        invFun := fun h => ⟨⟨(LinearMap.toMatrix V_basis.toBasis V_basis.toBasis) h.val.val.toLinearMap, by (
          apply H_mem_unitary
          exact ⟨h.val.val.toLinearMap, ⟨h.val.val, ⟨h.val, h.property, rfl⟩, rfl⟩, rfl⟩
        )⟩, by (
          refine ⟨⟨_, ⟨h.val.val.toLinearMap, ⟨h.val.val, ⟨h.val, h.property, rfl⟩, rfl⟩, rfl⟩⟩, rfl⟩
        )⟩,
        left_inv := by
          intro h
          simp
          rw [Subtype.ext_iff]
          simp [remove_fresh]
        right_inv := by
          intro h
          simp
          simp [remove_fresh]
          ext a
          simp
        map_mul' := by
          intro x y
          simp [remove_fresh]
          ext a
          simp
          exact Matrix.toLin_mul_apply (v₁ := V_basis.toBasis) (v₂ := V_basis.toBasis)
            (v₃ := V_basis.toBasis) _ _ _
      }
    · rfl


#print axioms new_weyl_unitarian_trick

-- A product of k unitary groups U(n_1) × U(n_2) × ... × U(n_k), where n_i < n for each n_i


#check Pi.commSemigroup
