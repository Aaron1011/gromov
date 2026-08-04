module

public import Mathlib
public import Gromov.Theorem38

/-!
# `rho_g` contains a finite-index abelian subgroup

`rho_g_contains_abelian`, the bundled input `Theorem3_1_Input`, and the infinite-image case.
-/

public section

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
      exact W_equiv.map_eq_zero_iff.mp (by simpa using hx)
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
    rw [Subgroup.eq_top_iff']
    intro x
    have x_prop := x.property
    rw [MonoidHom.mem_range] at x_prop
    obtain ⟨g, hg⟩ := x_prop
    have mem_range: plain_linear_to_clm ↑x ∈ my_new_range := by
      refine MonoidHom.mem_range.mpr ⟨g, ?_⟩
      rw [← hg]
      rfl
    have mem_closure: plain_linear_to_clm ↑x ∈ my_new_range.topologicalClosure :=
      Subgroup.le_topologicalClosure my_new_range mem_range
    refine MonoidHom.mem_range.mpr
      ⟨⟨⟨new_map_entry (plain_linear_to_clm ↑x),
          Subgroup.mem_map_of_mem new_map_hom.toMonoidHom mem_closure⟩, ?_⟩, ?_⟩
    .
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem new_map_hom.toMonoidHom mem_range
    .
      have hrt : ∀ y, new_map_hom.symm (new_map_entry y) = y := new_map_hom.left_inv
      refine Subtype.ext ?_
      change (Units.map (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ) (M₁ := W)).toMonoidHom)
          (new_map_hom.symm (new_map_entry (plain_linear_to_clm ↑x))) = x.val
      rw [hrt]
      ext f
      rfl


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


  -- TODO - figure out how to make instance inference work here
  obtain ⟨i, j, i_fin, j_fin, p, p_prime, e, exists_iso⟩ := @CommGroup.equiv_free_prod_prod_multiplicative_zmod H (haveI := H_abeliean; { (inferInstance : Group H) with mul_comm := mul_comm' }) (H_FG)
  have iso := Classical.choice exists_iso

  have j_nonempty: Nonempty j := by
    by_contra!
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


  let G' := Subgroup.comap hom H

  -- TODO - generalize this and PR to mathlib


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


  have target := g_hom_abelian ⊤ (by infer_instance) (g_rho) ?_ (H) ?_ ?_ ?_ ?_
  . exact target
  .
    simp [g_rho]
    exact MonoidHom.rangeRestrict_surjective GRepW_base
  .
    unfold rho_g at hr
    have card_mul := Subgroup.card_mul_index H
    unfold rho_g at card_mul
    nth_rw 2 [Nat.card_eq_zero_of_infinite] at card_mul
    rw [Nat.mul_eq_zero] at card_mul
    replace card_mul := card_mul.resolve_right H_finite_index.index_ne_zero
    rw [Nat.card_eq_zero] at card_mul
    exact card_mul.resolve_left (fun h => h.false ⟨1, H.one_mem⟩)
  . exact H_abelian
  . exact H_finite_index
  . exact h_fg

#print axioms rho_g_case_infinite

end GeneratesNS
