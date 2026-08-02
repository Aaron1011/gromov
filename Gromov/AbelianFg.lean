import Mathlib

open scoped commutatorElement

lemma new_group_fg_map {G G': Type*} [Group G] [Group G'] (H: Subgroup G) (h_fg: H.FG) (f: G →* G'): (Subgroup.map f H).FG := by
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

  specialize foo x_mem
  norm_cast at foo
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  rw [← prod_eq]
  unfold List.unattach
  simp

-- TODO - simplify and pr to mathlib
lemma fg_of_quot {G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) [DecidableEq (G ⧸ H)]  [H.Normal] (fg_H: Subgroup.FG H) [fg_quot: Group.FG (G ⧸ H)]: Group.FG G := by
  rw [Group.fg_iff]
  have foo := Subgroup.groupEquivQuotientProdSubgroup (s := H)
  have h_group_fg: Group.FG H := by
    rw [Group.fg_iff_subgroup_fg]
    apply fg_H

  obtain ⟨S_H, S_H_closure⟩ := fg_H
  have fg_quot_out : ∃ S : Finset (G ⧸ H), Subgroup.closure (S : Set (G ⧸ H)) = ⊤ := fg_quot.out
  use S_H ∪ ((Finset.image (fun a => a.out) fg_quot_out.choose) ∪ ((Finset.image (fun a => a⁻¹.out) fg_quot_out.choose)))
  rw [← Finset.coe_union]
  rw [← Finset.coe_union]
  refine ⟨?_, ?_⟩
  .
    ext a
    simp

    have quot_gen := fg_quot_out.choose_spec

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
    rw [sup_comm]

    have a_eq: a = ((List.map (fun a ↦ Quotient.out a) l.unattach).prod) * ((List.map (fun a ↦ Quotient.out a) l.unattach).prod⁻¹ * a) := by
      simp

    rw [a_eq]

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

-- Helper: subgroups of FG commutative groups are FG
lemma fg_subgroup_of_comm_group {G : Type*} [CommGroup G] [hG: Group.FG G]
    (H : Subgroup G): H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  have hG' : AddGroup.FG (Additive G) := GroupFG.iff_add_fg.mp hG
  have hG'' : (⊤ : AddSubgroup (Additive G)).FG := by
    rw [← AddGroup.fg_def]; exact hG'
  rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hG''
  obtain ⟨n, f, hf⟩ := hG''
  let K := AddSubgroup.comap f (H.toAddSubgroup)
  have hK : K.FG := (K.toIntSubmodule.fg_iff_addSubgroup_fg).mp (IsNoetherian.noetherian _)
  have h_img : AddSubgroup.map f K = H.toAddSubgroup := by
    rw [AddSubgroup.map_comap_eq f (H.toAddSubgroup)]; simp [hf]
  rw [← h_img]
  apply addgroup_fg_map K hK f

-- Helper: When ⁅H, ⊤⁆ is central in G, it's FG if H and G are FG
-- This is because the commutator map H × G → [H, G] is biadditive when [H, G] is abelian
lemma commutator_fg_of_fg_central {G : Type*} [Group G] [Group.FG G]
    (H : Subgroup G) (hH : H.FG) (hC : ⁅H, ⊤⁆ ≤ Subgroup.center G) :
    (⁅H, ⊤⁆ : Subgroup G).FG := by
  classical
  -- Get generators for H
  obtain ⟨T, hT⟩ := hH
  -- Get generators for G
  have hGfg := (Subgroup.fg_iff _).mp (Group.fg_def.mp ‹Group.FG G›)
  obtain ⟨S, hS_cl, hS_fin⟩ := hGfg

  -- The finite generating set - commutators of generators
  let gen : Set G := Set.image2 (fun t s => ⁅t, s⁆) (↑T : Set G) S
  have hgen_finite : gen.Finite := Set.Finite.image2 _ T.finite_toSet hS_fin

  -- When ⁅H, ⊤⁆ is central, commutator is biadditive:
  -- [xy, z] = [x, z][y, z] and [x, yz] = [x, y][x, z]
  -- So ⁅H, ⊤⁆ is generated by {[t, s] : t ∈ T, s ∈ S}
  rw [Subgroup.fg_iff]
  use hgen_finite.toFinset
  constructor
  · -- Show closure(gen) = ⁅H, ⊤⁆
    apply le_antisymm
    · -- closure(gen) ⊆ ⁅H, ⊤⁆
      rw [Subgroup.closure_le, Set.Finite.coe_toFinset]
      intro x hx
      obtain ⟨t, ht, s, hs, hx⟩ := Set.mem_image2.mp hx
      rw [← hx]
      apply Subgroup.commutator_mem_commutator
      · rw [← hT]; exact Subgroup.subset_closure ht
      · simp
    · -- ⁅H, ⊤⁆ ⊆ closure(gen)
      -- When ⁅H, ⊤⁆ is central, the commutator map is biadditive.
      -- So ⁅H, ⊤⁆ is generated by {[t, s] : t ∈ T, s ∈ S} = gen
      rw [Subgroup.commutator_def, Subgroup.closure_le, Set.Finite.coe_toFinset]
      intro x hx
      obtain ⟨h, hh, g, _, rfl⟩ := hx
      rw [← hT] at hh
      -- Need to show ⁅h, g⁆ ∈ closure gen for h ∈ closure T, g ∈ G = closure S
      -- Use double induction with biadditive structure

      -- Helper: biadditive formulas when commutators are central
      have mul_left : ∀ (a b c : G), a ∈ H → b ∈ H →
          ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := fun a b c ha hb => by
        have hbc_central := hC (Subgroup.commutator_mem_commutator hb (Subgroup.mem_top c))
        have hac_central := hC (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top c))
        have hbc_comm : ∀ g, g * ⁅b, c⁆ = ⁅b, c⁆ * g := Subgroup.mem_center_iff.mp hbc_central
        have hac_comm : ∀ g, g * ⁅a, c⁆ = ⁅a, c⁆ * g := Subgroup.mem_center_iff.mp hac_central
        have h1 : b * c * b⁻¹ = ⁅b, c⁆ * c := by simp only [commutatorElement_def]; group
        simp only [commutatorElement_def]
        calc a * b * c * (a * b)⁻¹ * c⁻¹ = a * (b * c * b⁻¹) * a⁻¹ * c⁻¹ := by group
          _ = a * (⁅b, c⁆ * c) * a⁻¹ * c⁻¹ := by rw [h1]
          _ = a * ⁅b, c⁆ * c * a⁻¹ * c⁻¹ := by group
          _ = ⁅b, c⁆ * a * c * a⁻¹ * c⁻¹ := by rw [hbc_comm a]
          _ = ⁅b, c⁆ * (a * c * a⁻¹ * c⁻¹) := by group
          _ = (a * c * a⁻¹ * c⁻¹) * ⁅b, c⁆ := (hbc_comm _).symm

      have inv_left : ∀ (a b : G), a ∈ H → ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := fun a b ha => by
        have ha_inv := Subgroup.inv_mem H ha
        have h_prod : ⁅a⁻¹ * a, b⁆ = 1 := by simp [commutatorElement_one_left]
        rw [mul_left a⁻¹ a b ha_inv ha] at h_prod
        exact mul_eq_one_iff_eq_inv.mp h_prod

      have mul_right : ∀ (a b c : G), a ∈ H →
          ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := fun a b c ha => by
        have hab_central := hC (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
        have hac_central := hC (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top c))
        have hac_comm : ∀ g, g * ⁅a, c⁆ = ⁅a, c⁆ * g := Subgroup.mem_center_iff.mp hac_central
        have h1 : b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ := by rw [hac_comm b, mul_inv_cancel_right]
        simp only [commutatorElement_def]
        calc a * (b * c) * a⁻¹ * (b * c)⁻¹
            = (a * b * a⁻¹) * (a * c * a⁻¹ * c⁻¹) * b⁻¹ := by group
          _ = (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by group
          _ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by rw [commutatorElement_def] at h1; rw [h1]

      have inv_right : ∀ (a b : G), a ∈ H → ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := fun a b ha => by
        have h_prod : ⁅a, b⁻¹ * b⁆ = 1 := by simp [commutatorElement_one_right]
        rw [mul_right a b⁻¹ b ha] at h_prod
        exact mul_eq_one_iff_eq_inv.mp h_prod

      -- Double induction: first on h ∈ closure T, then on g ∈ closure S
      -- Since g ∈ ⊤ = closure S, and H = closure T, we need to show ⁅h, g⁆ ∈ closure gen
      have hg_mem : g ∈ Subgroup.closure S := by rw [hS_cl]; trivial
      refine Subgroup.closure_induction (p := fun h' _ => ⁅h', g⁆ ∈ Subgroup.closure gen)
        ?mem ?one ?mul ?inv hh
      case mem =>
        -- For t ∈ T, show ⁅t, g⁆ ∈ closure gen by induction on g ∈ closure S
        intro t ht
        have ht_mem : t ∈ H := by rw [← hT]; exact Subgroup.subset_closure ht
        refine Subgroup.closure_induction (p := fun g' _ => ⁅t, g'⁆ ∈ Subgroup.closure gen)
            ?_ ?_ ?_ ?_ hg_mem
        · intro s hs; exact Subgroup.subset_closure (Set.mem_image2_of_mem ht hs)
        · simp only [commutatorElement_one_right]; exact Subgroup.one_mem _
        · intro g₁ g₂ _ _ hg₁ hg₂
          rw [mul_right t g₁ g₂ ht_mem]; exact Subgroup.mul_mem _ hg₁ hg₂
        · intro g' _ hg'; rw [inv_right t g' ht_mem]; exact Subgroup.inv_mem _ hg'
      case one =>
        simp only [commutatorElement_one_left]; exact Subgroup.one_mem _
      case mul =>
        intro h₁ h₂ hh₁ hh₂ ih₁ ih₂
        have h₁_mem : h₁ ∈ H := hT ▸ hh₁
        have h₂_mem : h₂ ∈ H := hT ▸ hh₂
        rw [mul_left h₁ h₂ g h₁_mem h₂_mem]; exact Subgroup.mul_mem _ ih₁ ih₂
      case inv =>
        intro h' hh' ih
        have h'_mem : h' ∈ H := hT ▸ hh'
        rw [inv_left h' g h'_mem]; exact Subgroup.inv_mem _ ih
  · exact Set.toFinite _

