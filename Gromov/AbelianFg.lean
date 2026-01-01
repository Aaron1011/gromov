import Mathlib

lemma addgroup_fg_map {G G': Type*} [AddGroup G] [AddGroup G'] (H: AddSubgroup G) (h_fg: H.FG) (f: G →+ G'): (AddSubgroup.map f H).FG := by
  obtain ⟨s, hs⟩ := h_fg
  classical
  rw [AddSubgroup.fg_iff]
  use s.image f
  refine ⟨?_, ?_⟩
  .
    rw [Finset.coe_image]
    rw [← AddMonoidHom.map_closure]
    rw [hs]
  . simp
    exact Set.toFinite (⇑f '' ↑s)

lemma addsubgroup_z_map (n: ℕ) (H: AddSubgroup (Fin n → ℤ)): H.FG :=
  (H.toIntSubmodule.fg_iff_addSubgroup_fg).mp (IsNoetherian.noetherian _)

lemma fg_subgroup_of_abelian {G : Type*} [AddCommGroup G] (hG : AddGroup.FG G) (H : AddSubgroup G): H.FG := by
  have fg_top: (⊤ : AddSubgroup G).FG := by
    rw [← AddGroup.fg_def]
    infer_instance

  rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at fg_top
  obtain ⟨n, f, hf⟩ := fg_top

  let H' := AddSubgroup.comap f H

  have H'_fg: H'.FG := by
   apply addsubgroup_z_map


  let new_H := AddSubgroup.map f (AddSubgroup.comap f H)

  have H_eq := AddSubgroup.map_comap_eq f H
  simp [hf] at H_eq
  rw [← H_eq]
  apply addgroup_fg_map
  apply H'_fg

open scoped Finset Pointwise

-- Each element of G can be written as a product of elements of S in at least one way
lemma mem_S_prod_list_of_gen {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (hS: Subgroup.closure (G := G) S = ⊤) (x: G): ∃ l: List (((S ∪ S⁻¹) : Finset G)), l.unattach.prod = x := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo

  have x_mem: x ∈ Subgroup.closure (G := G) S := by
    rw [hS]
    simp

  --simp only [mem_toSubmonoid, Finset.mem_coe] at foo
  specialize foo x_mem
  norm_cast at foo
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  rw [← prod_eq]
  unfold List.unattach
  simp

lemma fg_of_quot {G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) [DecidableEq (G ⧸ H)]  [H.Normal] (fg_H: Subgroup.FG H) [fg_quot: Group.FG (G ⧸ H)]: Group.FG G := by
  rw [Group.fg_iff]
  have foo := Subgroup.groupEquivQuotientProdSubgroup (s := H)
  have h_group_fg: Group.FG H := by
    rw [Group.fg_iff_subgroup_fg]
    apply fg_H
  -- have fg_prod: Group.FG ((G ⧸ H) × ↥H) := by apply Prod.instGroupFG

  -- use (Finset.image foo.symm fg_prod.out.choose)
  -- refine ⟨?_, by apply Finset.finite_toSet⟩
  -- simp
  -- have choose_fg := fg_prod.out.choose_spec
  -- ext a
  -- simp

  -- have a_mem_top: (foo a) ∈ (⊤ : Subgroup ((G ⧸ H) × ↥H)) := by simp
  -- rw [← choose_fg] at a_mem_top
  -- have bar := mem_S_prod_list_of_gen _ choose_fg (foo a)
  -- obtain ⟨l, hl⟩ := bar
  -- rw [← hl] at a_mem_top


  -- apply_fun foo.symm at hl
  -- simp at hl
  -- rw [← hl]




  -- rw [Subgroup.mem_closure_iff_of_fintype]

  obtain ⟨S_H, S_H_closure⟩ := fg_H
  use S_H ∪ ((Finset.image (fun a => a.out) fg_quot.out.choose) ∪ ((Finset.image (fun a => a⁻¹.out) fg_quot.out.choose)))
  rw [← Finset.coe_union]
  rw [← Finset.coe_union]
  refine ⟨?_, ?_⟩
  .
    ext a
    simp

    have quot_gen := fg_quot.out.choose_spec
    simp at quot_gen

    have a_mem: QuotientGroup.mk' H a ∈ (⊤ : (Subgroup (G ⧸ H))) := by simp
    rw [← quot_gen] at a_mem

    have foo := mem_S_prod_list_of_gen _ quot_gen (QuotientGroup.mk' H a)
    obtain ⟨l, hl⟩ := foo
    simp at hl
    conv at hl =>
      lhs
      equals QuotientGroup.mk' H (l.unattach.map (fun a => a.out)).prod =>
        rw [map_list_prod]
        simp
        unfold List.unattach
        rw [List.map_map]
        simp



    unfold List.unattach at hl
    simp at hl
    rw [QuotientGroup.eq] at hl

    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul H a
    rw [Subgroup.closure_union]
    apply mul_inv_eq_of_eq_mul at hb
    --rw [← hb]
    rw [sup_comm]

    have a_eq: a = ((List.map (fun a ↦ Quotient.out a) l.unattach).prod) * ((List.map (fun a ↦ Quotient.out a) l.unattach).prod⁻¹ * a) := by
      simp

    rw [a_eq]



    --simp at a_mem

    apply Subgroup.mul_mem_sup
    .
      apply Subgroup.list_prod_mem
      intro x hx
      simp at hx
      obtain ⟨a, ⟨a_mem, a_mem_l⟩, x_eq⟩ := hx
      apply Subgroup.mem_closure_of_mem
      simp
      cases a_mem
      . rename_i a_mem_first
        left
        grind
      .
        rename_i a_mem_inv
        right
        use a⁻¹
        refine ⟨a_mem_inv, ?_⟩
        rw [← x_eq]
        simp
    .
      rw [S_H_closure]
      exact hl
  .
    apply Finset.finite_toSet

lemma subgroup_fg_of_nilpotent_fg {G: Type*} [Group G] [Group.IsNilpotent G] [Group.FG G] (H: Subgroup G): Group.FG H:= by
  apply nilpotent_center_quotient_ind (P := fun A _ _ => Group.FG A)
  .
    intro A _ hA
    infer_instance
  . intro A _ _ h_quot

    have foo := Module.Finite.of_submodule_quotient ((Subgroup.toAddSubgroup A).toIntSubmodule) (M := Additive A)
    sorry

  rw [Subgroup.fg_iff_add_fg]
  apply induction_nilp
  --have : Module.Finite ℤ (Subgroup.toAddSubgroup H).toIntSubmodule := by inferInstance
