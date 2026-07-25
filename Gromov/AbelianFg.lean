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



-- lemma group_fg_comap {G G': Type*} [Group G] [Group G'] (H: Subgroup G') (h_fg: H.FG) (f: G →* G'): (Subgroup.comap f H).FG := by
--   obtain ⟨s, hs⟩ := h_fg
--   classical
--   rw [Subgroup.fg_iff]
--   use Set.preimage f s
--   refine ⟨?_, ?_⟩
--   .
--     apply_fun (Subgroup.map f)
--     . sorry
--     .
--       apply Subgroup.map_injective

--     simp
--     rw [Finset.coe_image]
--     rw [← MonoidHom.map_closure]
--     rw [hs]
--   .

--     exact Set.toFinite (⇑f '' ↑s)

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

-- -- Helper: For FG nilpotent groups, all terms of the lower central series are FG
-- -- Proof: Show quotients γ_k/γ_{k+1} are FG by upward induction, then use extensions.
-- lemma lowerCentralSeries_fg {G : Type*} [Group G] [Group.IsNilpotent G] [Group.FG G] :
--     ∀ k, (lowerCentralSeries G k).FG := by
--   classical
--
--   -- Phase 1: Show γ_k/γ_{k+1} is FG for all k by upward induction
--   -- We show the image of γ_k in G/γ_{k+1} is FG
--   have h_quot_fg : ∀ k, ((lowerCentralSeries G k).map
--       (QuotientGroup.mk' (lowerCentralSeries G (k + 1)))).FG := by
--     intro k
--     induction k with
--     | zero =>
--       -- γ_0/γ_1 = G/[G,G] is FG (quotient of FG group)
--       simp only [lowerCentralSeries_zero]
--       rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
--       rw [← Group.fg_def]
--       exact QuotientGroup.fg (lowerCentralSeries G 1)
--     | succ k ih =>
--       -- γ_{k+1}/γ_{k+2} is generated by commutators [a,s] for a ∈ γ_k, s ∈ S
--       -- By IH, γ_k/γ_{k+1} is FG, and G is FG
--       -- The commutators of generators generate γ_{k+1}/γ_{k+2}
--
--       -- If γ_{k+1} = ⊥, then γ_{k+2} = ⊥, so image is trivial
--       by_cases hk1_bot : lowerCentralSeries G (k + 1) = ⊥
--       · rw [hk1_bot, Subgroup.map_bot]
--         exact Subgroup.FG.bot
--
--       -- γ_{k+1}/γ_{k+2} is generated by commutators of:
--       -- - generators for γ_k modulo γ_{k+1} (from IH)
--       -- - generators for G
--       -- The biadditive structure works because γ_{k+1}/γ_{k+2} is central in G/γ_{k+2}
--
--       -- Get generators for γ_k/γ_{k+1} from IH
--       obtain ⟨T', hT'⟩ := ih
--       -- Get generators for G
--       have hGfg := (Subgroup.fg_iff _).mp (Group.fg_def.mp ‹Group.FG G›)
--       obtain ⟨S, hS_cl, hS_fin⟩ := hGfg
--
--       -- The finite generating set for γ_{k+1}/γ_{k+2}:
--       -- commutators [t', s] where t' ∈ T' (lifted to γ_k) and s ∈ S
--       let π := QuotientGroup.mk' (lowerCentralSeries G (k + 1 + 1))
--       let π' := QuotientGroup.mk' (lowerCentralSeries G (k + 1))
--
--       -- T' contains elements of G/γ_{k+1} that generate the image of γ_k
--       -- We lift by taking Quotient.out (representative of the coset)
--       -- The representative lies in γ_k because T' ⊆ γ_k/γ_{k+1}
--       let T : Finset G := T'.image (fun q => Quotient.out q)
--       have hT_mem : ∀ t ∈ T, t ∈ lowerCentralSeries G k := by
--         intro t ht
--         simp only [T, Finset.mem_image] at ht
--         obtain ⟨q, hq, rfl⟩ := ht
--         -- q ∈ T' means q is in the closure of T', which equals the image of γ_k
--         -- So q = π'(g) for some g ∈ γ_k
--         have hmem : q ∈ Subgroup.map π' (lowerCentralSeries G k) := by
--           rw [← hT']; exact Subgroup.subset_closure hq
--         simp only [Subgroup.mem_map] at hmem
--         obtain ⟨g, hg_mem, hg_eq⟩ := hmem
--         -- Quotient.out q and g differ by an element of γ_{k+1}
--         have hout : π' (Quotient.out q) = q := Quotient.out_eq q
--         -- Since q = π' g, we have π' (Quotient.out q) = π' g
--         have hout' : π' (Quotient.out q) = π' g := by rw [hout, ← hg_eq]; rfl
--         have hdiff := QuotientGroup.eq.mp hout'.symm
--         -- g⁻¹ * Quotient.out q ∈ γ_{k+1} ⊆ γ_k, and g ∈ γ_k, so Quotient.out q ∈ γ_k
--         have hle : lowerCentralSeries G (k + 1) ≤ lowerCentralSeries G k :=
--           lowerCentralSeries_antitone (by omega : k ≤ k + 1)
--         have : Quotient.out q = g * (g⁻¹ * Quotient.out q) := by group
--         rw [this]
--         exact Subgroup.mul_mem _ hg_mem (hle hdiff)
--
--       -- The generating set: commutators [t, s]
--       let gen : Set (G ⧸ lowerCentralSeries G (k + 1 + 1)) :=
--         Set.image2 (fun t s => π ⁅t, s⁆) (↑T : Set G) S
--
--       have hgen_finite : gen.Finite := Set.Finite.image2 _ T.finite_toSet hS_fin
--
--       rw [Subgroup.fg_iff]
--       use hgen_finite.toFinset
--       constructor
--       · -- Show closure(gen) = γ_{k+1}/γ_{k+2}
--         apply le_antisymm
--         · -- closure(gen) ⊆ γ_{k+1}/γ_{k+2}
--           rw [Subgroup.closure_le, Set.Finite.coe_toFinset]
--           intro x hx
--           obtain ⟨t, ht, s, hs, hx⟩ := Set.mem_image2.mp hx
--           rw [← hx]
--           -- [t, s] ∈ γ_{k+1} = [γ_k, G], so π([t, s]) ∈ γ_{k+1}/γ_{k+2}
--           apply Subgroup.mem_map_of_mem
--           apply Subgroup.commutator_mem_commutator (hT_mem t ht) (by simp)
--         · -- γ_{k+1}/γ_{k+2} ⊆ closure(gen)
--           -- This uses the biadditive structure when γ_{k+1}/γ_{k+2} is central
--           -- Since [γ_{k+1}, G] = γ_{k+2}, γ_{k+1}/γ_{k+2} is central in G/γ_{k+2}
--           -- The proof follows the same pattern as commutator_fg_of_fg_central
--
--           -- For all a ∈ γ_{k+1}, π a ∈ closure gen
--           intro x hx
--           obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
--           simp only [Set.Finite.coe_toFinset]
--
--           -- γ_{k+1}/γ_{k+2} is central in G/γ_{k+2}
--           have hcentral : ∀ c ∈ lowerCentralSeries G (k + 1), ∀ g : G,
--               π c * π g = π g * π c := fun c hc g => by
--             have h : ⁅c, g⁆ ∈ lowerCentralSeries G (k + 1 + 1) :=
--               Subgroup.commutator_mem_commutator hc (by simp)
--             have h1 : π ⁅c, g⁆ = 1 := QuotientGroup.eq_one_iff.mpr h
--             simp only [commutatorElement_def, map_mul, map_inv] at h1
--             -- π c * π g * (π c)⁻¹ * (π g)⁻¹ = 1
--             have h2 : π c * π g * (π c)⁻¹ * (π g)⁻¹ = 1 := h1
--             calc π c * π g = π c * π g * (π c)⁻¹ * (π g)⁻¹ * (π g * π c) := by group
--               _ = 1 * (π g * π c) := by rw [h2]
--               _ = π g * π c := by group
--
--           -- Biadditive formulas (in the quotient)
--           have mul_left : ∀ (a b c : G), a ∈ lowerCentralSeries G k → b ∈ lowerCentralSeries G k →
--               π ⁅a * b, c⁆ = π ⁅a, c⁆ * π ⁅b, c⁆ := fun a b c ha hb => by
--             have hbc := Subgroup.commutator_mem_commutator hb (Subgroup.mem_top c)
--             have hbc_comm : ∀ x, π ⁅b, c⁆ * x = x * π ⁅b, c⁆ := fun x =>
--               (hcentral _ hbc _).symm.trans (hcentral _ hbc _)
--             have h1 : b * c * b⁻¹ = ⁅b, c⁆ * c := by simp only [commutatorElement_def]; group
--             simp only [commutatorElement_def, map_mul, map_inv]
--             -- Goal: π a * π b * π c * (π a * π b)⁻¹ * (π c)⁻¹ = (π a * π c * (π a)⁻¹ * (π c)⁻¹) * (π b * π c * (π b)⁻¹ * (π c)⁻¹)
--             have h2 : π b * π c * (π b)⁻¹ = π ⁅b, c⁆ * π c := by
--               simp only [commutatorElement_def, map_mul, map_inv]; group
--             calc π a * π b * π c * (π a * π b)⁻¹ * (π c)⁻¹
--                 = π a * (π b * π c * (π b)⁻¹) * (π a)⁻¹ * (π c)⁻¹ := by group
--               _ = π a * (π ⁅b, c⁆ * π c) * (π a)⁻¹ * (π c)⁻¹ := by rw [h2]
--               _ = π a * π ⁅b, c⁆ * π c * (π a)⁻¹ * (π c)⁻¹ := by group
--               _ = π ⁅b, c⁆ * π a * π c * (π a)⁻¹ * (π c)⁻¹ := by rw [hbc_comm (π a)]
--               _ = π ⁅b, c⁆ * (π a * π c * (π a)⁻¹ * (π c)⁻¹) := by group
--               _ = (π a * π c * (π a)⁻¹ * (π c)⁻¹) * π ⁅b, c⁆ := by rw [hbc_comm]
--               _ = (π a * π c * (π a)⁻¹ * (π c)⁻¹) * (π b * π c * (π b)⁻¹ * (π c)⁻¹) := by
--                   simp only [commutatorElement_def, map_mul, map_inv]
--
--           have inv_left : ∀ (a b : G), a ∈ lowerCentralSeries G k →
--               π ⁅a⁻¹, b⁆ = (π ⁅a, b⁆)⁻¹ := fun a b ha => by
--             have ha_inv := Subgroup.inv_mem _ ha
--             have h_prod : π ⁅a⁻¹ * a, b⁆ = 1 := by
--               simp only [inv_mul_cancel, commutatorElement_one_left, map_one]
--             rw [mul_left a⁻¹ a b ha_inv ha, mul_eq_one_iff_eq_inv] at h_prod
--             exact h_prod
--
--           have mul_right : ∀ (a b c : G), a ∈ lowerCentralSeries G k →
--               π ⁅a, b * c⁆ = π ⁅a, b⁆ * π ⁅a, c⁆ := fun a b c ha => by
--             have hac := Subgroup.commutator_mem_commutator ha (Subgroup.mem_top c)
--             have hac_comm : ∀ x, π ⁅a, c⁆ * x = x * π ⁅a, c⁆ := fun x =>
--               (hcentral _ hac _).symm.trans (hcentral _ hac _)
--             have h1 : π b * π ⁅a, c⁆ * (π b)⁻¹ = π ⁅a, c⁆ := by rw [hac_comm]; group
--             simp only [commutatorElement_def, map_mul, map_inv]
--             have h2 : π b * (π a * π c * (π a)⁻¹ * (π c)⁻¹) * (π b)⁻¹
--                     = π a * π c * (π a)⁻¹ * (π c)⁻¹ := by
--               simp only [commutatorElement_def, map_mul, map_inv] at h1
--               calc π b * (π a * π c * (π a)⁻¹ * (π c)⁻¹) * (π b)⁻¹
--                   = π b * (π a * π c * (π a)⁻¹ * (π c)⁻¹) * (π b)⁻¹ := rfl
--                 _ = (π a * π c * (π a)⁻¹ * (π c)⁻¹) := by rw [hac_comm]; group
--             calc π a * (π b * π c) * (π a)⁻¹ * (π b * π c)⁻¹
--                 = (π a * π b * (π a)⁻¹) * (π a * π c * (π a)⁻¹ * (π c)⁻¹) * (π b)⁻¹ := by group
--               _ = (π a * π b * (π a)⁻¹ * (π b)⁻¹) *
--                   (π b * (π a * π c * (π a)⁻¹ * (π c)⁻¹) * (π b)⁻¹) := by group
--               _ = (π a * π b * (π a)⁻¹ * (π b)⁻¹) * (π a * π c * (π a)⁻¹ * (π c)⁻¹) := by rw [h2]
--
--           have inv_right : ∀ (a b : G), a ∈ lowerCentralSeries G k →
--               π ⁅a, b⁻¹⁆ = (π ⁅a, b⁆)⁻¹ := fun a b ha => by
--             have h_prod : π ⁅a, b⁻¹ * b⁆ = 1 := by
--               simp only [inv_mul_cancel, commutatorElement_one_right, map_one]
--             rw [mul_right a b⁻¹ b ha, mul_eq_one_iff_eq_inv] at h_prod
--             exact h_prod
--
--           -- γ_{k+1} = [γ_k, G], so a ∈ γ_{k+1} is in closure of commutators [a', g'] for a' ∈ γ_k
--           have h_lcs : lowerCentralSeries G (k + 1) = ⁅lowerCentralSeries G k, ⊤⁆ := rfl
--           rw [h_lcs] at ha
--
--           -- The argument: a ∈ γ_k means π' a ∈ γ_k/γ_{k+1} = closure T'
--           -- Induction on ha : a ∈ [γ_k, G]
--           refine Subgroup.closure_induction (p := fun a _ => π a ∈ Subgroup.closure gen) ?_ ?_ ?_ ?_ ha
--           · -- Base: a = ⁅a', g'⁆ for a' ∈ γ_k, g' ∈ G
--             intro x hx
--             obtain ⟨a', ha', g', _, rfl⟩ := hx
--             -- π' a' ∈ γ_k/γ_{k+1} = closure T'
--             have ha'_quot : π' a' ∈ Subgroup.map π' (lowerCentralSeries G k) :=
--               Subgroup.mem_map_of_mem π' ha'
--             rw [← hT'] at ha'_quot
--             have hg'_mem : g' ∈ Subgroup.closure S := by rw [hS_cl]; trivial
--
--             -- Base: for t ∈ T, π[t, g'] ∈ closure gen
--             have base : ∀ t ∈ T, ∀ g'' ∈ Subgroup.closure S, π ⁅t, g''⁆ ∈ Subgroup.closure gen := by
--               intro t ht g'' hg''
--               have ht_mem := hT_mem t ht
--               refine Subgroup.closure_induction (p := fun g _ => π ⁅t, g⁆ ∈ Subgroup.closure gen)
--                   ?_ ?_ ?_ ?_ hg''
--               · intro s hs; exact Subgroup.subset_closure (Set.mem_image2_of_mem ht hs)
--               · simp only [commutatorElement_one_right, map_one]; exact Subgroup.one_mem _
--               · intro g₁ g₂ _ _ h1 h2; rw [mul_right t g₁ g₂ ht_mem]; exact Subgroup.mul_mem _ h1 h2
--               · intro g _ h; rw [inv_right t g ht_mem]; exact Subgroup.inv_mem _ h
--
--             -- Induction on π' a' ∈ closure T'
--             refine Subgroup.closure_induction (s := ↑T')
--                 (p := fun q _ => ∀ a'' : G, π' a'' = q → a'' ∈ lowerCentralSeries G k →
--                   ∀ g'' ∈ Subgroup.closure S, π ⁅a'', g''⁆ ∈ Subgroup.closure gen) ?_ ?_ ?_ ?_ ha'_quot
--             · intro q hq a'' ha''_eq ha''_mem g'' hg''
--               have ht : Quotient.out q ∈ T := by simp only [T, Finset.mem_image]; exact ⟨q, hq, rfl⟩
--               have hinv_diff : Quotient.out q⁻¹ * a'' ∈ lowerCentralSeries G (k + 1) := by
--                 have hdiff : a''⁻¹ * Quotient.out q ∈ lowerCentralSeries G (k + 1) := by
--                   have hout : π' (Quotient.out q) = q := Quotient.out_eq q
--                   exact QuotientGroup.eq.mp (ha''_eq.symm.trans hout)
--                 have := Subgroup.inv_mem _ hdiff
--                 simp only [mul_inv_rev, inv_inv] at this; convert this using 1; group
--               have h_triv : π ⁅Quotient.out q⁻¹ * a'', g''⁆ = 1 :=
--                 QuotientGroup.eq_one_iff.mpr (Subgroup.commutator_mem_commutator hinv_diff (by simp))
--               have ha''_eq2 : a'' = Quotient.out q * (Quotient.out q⁻¹ * a'') := by group
--               rw [ha''_eq2, mul_right _ _ _ (hT_mem _ ht), h_triv, mul_one]
--               exact base (Quotient.out q) ht g'' hg''
--             · intro a'' ha''_eq _ g'' _
--               have h := QuotientGroup.eq_one_iff.mp ha''_eq
--               have hcomm := Subgroup.commutator_mem_commutator h (Subgroup.mem_top g'')
--               rw [QuotientGroup.eq_one_iff.mpr hcomm]; exact Subgroup.one_mem _
--             · intro q₁ q₂ hq₁ hq₂ ih₁ ih₂ a'' ha''_eq ha''_mem g'' hg''
--               obtain ⟨a₁, ha₁_mem, ha₁_eq⟩ := Subgroup.mem_map.mp
--                 (hT' ▸ Subgroup.closure_mono (Set.subset_univ _) hq₁)
--               obtain ⟨a₂, ha₂_mem, ha₂_eq⟩ := Subgroup.mem_map.mp
--                 (hT' ▸ Subgroup.closure_mono (Set.subset_univ _) hq₂)
--               have hinv_diff : (a₁ * a₂)⁻¹ * a'' ∈ lowerCentralSeries G (k + 1) := by
--                 have ha12_eq : π' (a₁ * a₂) = q₁ * q₂ := by rw [map_mul, ha₁_eq, ha₂_eq]
--                 have := Subgroup.inv_mem _ (QuotientGroup.eq.mp (ha''_eq.symm.trans ha12_eq))
--                 simp only [mul_inv_rev, inv_inv] at this; convert this using 1; group
--               have h_triv : π ⁅(a₁ * a₂)⁻¹ * a'', g''⁆ = 1 :=
--                 QuotientGroup.eq_one_iff.mpr (Subgroup.commutator_mem_commutator hinv_diff (by simp))
--               have ha''_eq2 : a'' = (a₁ * a₂) * ((a₁ * a₂)⁻¹ * a'') := by group
--               rw [ha''_eq2, mul_right _ _ _ (Subgroup.mul_mem _ ha₁_mem ha₂_mem), h_triv, mul_one]
--               rw [mul_left a₁ a₂ g'' ha₁_mem ha₂_mem]
--               exact Subgroup.mul_mem _ (ih₁ a₁ ha₁_eq ha₁_mem g'' hg'') (ih₂ a₂ ha₂_eq ha₂_mem g'' hg'')
--             · intro q' hq' ih a'' ha''_eq ha''_mem g'' hg''
--               obtain ⟨a''', ha'''_mem, ha'''_eq⟩ := Subgroup.mem_map.mp
--                 (hT' ▸ Subgroup.closure_mono (Set.subset_univ _) hq')
--               have hinv_diff : a''' * a'' ∈ lowerCentralSeries G (k + 1) := by
--                 have hainv_eq : π' (a'''⁻¹) = q'⁻¹ := by rw [map_inv, ha'''_eq]
--                 have := Subgroup.inv_mem _ (QuotientGroup.eq.mp (ha''_eq.symm.trans hainv_eq))
--                 simp only [mul_inv_rev, inv_inv] at this; convert this using 1; group
--               have h_triv : π ⁅a''' * a'', g''⁆ = 1 :=
--                 QuotientGroup.eq_one_iff.mpr (Subgroup.commutator_mem_commutator hinv_diff (by simp))
--               have ha''_eq2 : a'' = a'''⁻¹ * (a''' * a'') := by group
--               rw [ha''_eq2, mul_right _ _ _ (Subgroup.inv_mem _ ha'''_mem), h_triv, mul_one]
--               rw [inv_left a''' g'' ha'''_mem]
--               exact Subgroup.inv_mem _ (ih a''' ha'''_eq ha'''_mem g'' hg'')
--             · exact a'; · rfl; · exact ha'; · exact hg'_mem
--           · simp only [map_one]; exact Subgroup.one_mem _
--           · intro x y _ _ hx hy; rw [map_mul]; exact Subgroup.mul_mem _ hx hy
--           · intro x _ hx; rw [map_inv]; exact Subgroup.inv_mem _ hx
--       · exact Set.toFinite _
--
--   -- Phase 2: Show γ_k is FG by downward induction from γ_c = ⊥
--   intro k
--   by_cases hk : Group.nilpotencyClass G ≤ k
--   · -- γ_k = ⊥ for k ≥ class
--     rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hk]
--     exact Subgroup.FG.bot
--   · -- For k < class, use downward induction
--     push_neg at hk
--     -- Strong induction on (class - k)
--     -- We prove: ∀ d, ∀ k, k + d = nilpotencyClass → γ_k FG
--     suffices ∀ d k, k + d = Group.nilpotencyClass G → (lowerCentralSeries G k).FG by
--       exact this (Group.nilpotencyClass G - k) k (by omega)
--     intro d
--     induction d with
--     | zero =>
--       intro k hkd
--       -- k = nilpotencyClass, so γ_k = ⊥
--       rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (by omega : Group.nilpotencyClass G ≤ k)]
--       exact Subgroup.FG.bot
--     | succ d ihd =>
--       intro k hkd
--       -- k + (d+1) = hc, so k + 1 + d = hc
--       have h_next_fg : (lowerCentralSeries G (k + 1)).FG := ihd (k + 1) (by omega)
--       -- γ_k/γ_{k+1} is FG by Phase 1
--       have h_quot : ((lowerCentralSeries G k).map (QuotientGroup.mk' (lowerCentralSeries G (k + 1)))).FG :=
--         h_quot_fg k
--
--       -- Now use fg_of_quot to conclude γ_k is FG
--       have h_le : lowerCentralSeries G (k + 1) ≤ lowerCentralSeries G k :=
--         lowerCentralSeries_antitone (by omega : k ≤ k + 1)
--
--       -- The kernel of γ_k → image is γ_{k+1} ∩ γ_k = γ_{k+1}
--       have h_ker_fg : ((lowerCentralSeries G (k + 1)).subgroupOf (lowerCentralSeries G k)).FG := by
--         let e : (lowerCentralSeries G (k + 1)) ≃* ((lowerCentralSeries G (k + 1)).subgroupOf (lowerCentralSeries G k)) := {
--           toFun := fun ⟨x, hx⟩ => ⟨⟨x, h_le hx⟩, by simp [Subgroup.mem_subgroupOf]; exact hx⟩
--           invFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, by simpa [Subgroup.mem_subgroupOf] using hx⟩
--           left_inv := fun _ => rfl
--           right_inv := fun _ => rfl
--           map_mul' := fun _ _ => rfl
--         }
--         have hfg : Group.FG (lowerCentralSeries G (k + 1)) := (Group.fg_iff_subgroup_fg _).mpr h_next_fg
--         exact (Group.fg_iff_subgroup_fg _).mp (Group.fg_of_surjective (f := e.toMonoidHom) e.surjective)
--
--       -- The quotient γ_k / (γ_{k+1} ∩ γ_k) is isomorphic to image, which is FG
--       haveI h_quot_group_fg : Group.FG ((lowerCentralSeries G k) ⧸
--           (lowerCentralSeries G (k + 1)).subgroupOf (lowerCentralSeries G k)) := by
--         let ψ : (lowerCentralSeries G k) →* (G ⧸ lowerCentralSeries G (k + 1)) :=
--           (QuotientGroup.mk' (lowerCentralSeries G (k + 1))).comp (lowerCentralSeries G k).subtype
--         have h_range : ψ.range = (lowerCentralSeries G k).map (QuotientGroup.mk' (lowerCentralSeries G (k + 1))) := by
--           ext x; constructor
--           · intro ⟨y, hy⟩; exact ⟨y.val, y.property, hy⟩
--           · intro ⟨y, hy, hyx⟩; exact ⟨⟨y, hy⟩, hyx⟩
--         have h_ker : ψ.ker = (lowerCentralSeries G (k + 1)).subgroupOf (lowerCentralSeries G k) := by
--           ext ⟨x, hx⟩
--           simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
--           constructor
--           · intro h; exact (QuotientGroup.eq_one_iff _).mp h
--           · intro h; exact (QuotientGroup.eq_one_iff _).mpr h
--         have h_range_fg : Group.FG ψ.range := by
--           rw [h_range]; exact (Group.fg_iff_subgroup_fg _).mpr h_quot
--         have h_equiv : (lowerCentralSeries G k) ⧸ ψ.ker ≃* ψ.range := QuotientGroup.quotientKerEquivRange ψ
--         have hfg_ker : Group.FG ((lowerCentralSeries G k) ⧸ ψ.ker) :=
--           Group.fg_of_surjective (f := h_equiv.symm.toMonoidHom) h_equiv.symm.surjective
--         -- Transport via isomorphism from equal kernels
--         have h_quot_equiv : ((lowerCentralSeries G k) ⧸ ψ.ker) ≃*
--             ((lowerCentralSeries G k) ⧸ (lowerCentralSeries G (k + 1)).subgroupOf (lowerCentralSeries G k)) :=
--           QuotientGroup.quotientMulEquivOfEq h_ker
--         exact Group.fg_of_surjective (f := h_quot_equiv.toMonoidHom) h_quot_equiv.surjective
--
--       exact (Group.fg_iff_subgroup_fg _).mp (@fg_of_quot (lowerCentralSeries G k) _ _
--         ((lowerCentralSeries G (k + 1)).subgroupOf (lowerCentralSeries G k)) _ _ h_ker_fg _)
--
-- -- Helper: For FG nilpotent groups, the commutator subgroup is FG
-- lemma commutator_fg {G : Type*} [Group G] [Group.IsNilpotent G] [Group.FG G] :
--     (commutator G).FG := by
--   rw [← lowerCentralSeries_one]
--   exact lowerCentralSeries_fg 1
--
-- lemma subgroup_fg_of_nilpotent_fg {G : Type*} [Group G] [hG : Group.IsNilpotent G] [Group.FG G] :
--     ∀ (H : Subgroup G), H.FG := by
--   -- Use strong induction on nilpotencyClass
--   suffices h : ∀ (c : ℕ), Group.nilpotencyClass G ≤ c → ∀ (H : Subgroup G), H.FG by
--     exact h (Group.nilpotencyClass G) (le_refl _)
--   intro c
--   induction c generalizing G with
--   | zero =>
--     intro hc H
--     have : Group.nilpotencyClass G = 0 := Nat.eq_zero_of_le_zero hc
--     rw [nilpotencyClass_zero_iff_subsingleton] at this
--     haveI : Subsingleton G := this
--     rw [← Group.fg_iff_subgroup_fg]
--     infer_instance
--   | succ n ih =>
--     intro hc H
--     classical
--     -- Handle case where class is actually ≤ n (use IH directly)
--     by_cases hc_eq : Group.nilpotencyClass G ≤ n
--     · exact ih hc_eq H
--     · -- Class is exactly n+1
--       have hc_exact : Group.nilpotencyClass G = n + 1 := by omega
--
--       -- G/Z(G) has nilpotencyClass n
--       have hclass : Group.nilpotencyClass (G ⧸ Subgroup.center G) = n := by
--         rw [nilpotencyClass_quotient_center, hc_exact]; omega
--
--       -- G/Z(G) is FG
--       haveI : Group.FG (G ⧸ Subgroup.center G) := QuotientGroup.fg (Subgroup.center G)
--
--       -- Image of H in G/Z(G) is FG by IH (class ≤ n)
--       let H' := Subgroup.map (QuotientGroup.mk' (Subgroup.center G)) H
--       have hH'_fg : H'.FG := @ih (G ⧸ Subgroup.center G) _ _ _ (le_of_eq hclass) H'
--
--       -- Key: Z(G) is FG
--       -- Strategy: Use exact sequence Z(G) ∩ [G,G] → Z(G) → image in G/[G,G]
--       have hZ_fg : (Subgroup.center G).FG := by
--         let D := commutator G  -- [G,G]
--
--         -- [G,G] has nilpotency class ≤ n
--         have hD_class : Group.nilpotencyClass D ≤ n := by
--           rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
--           have hG_class : lowerCentralSeries G (n + 1) = ⊥ := by
--             rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, hc_exact]
--           -- lowerCentralSeries D k ≤ lowerCentralSeries G (k+1) via subtype
--           have hD_eq : (D : Set G) = (lowerCentralSeries G 1 : Set G) := by
--             simp only [SetLike.coe_set_eq]
--             exact lowerCentralSeries_one.symm
--           -- The key: Show lowerCentralSeries D n = ⊥
--           -- D.subtype maps lowerCentralSeries D k into lowerCentralSeries G (k+1)
--           have h_incl : ∀ k, (lowerCentralSeries D k).map D.subtype ≤ lowerCentralSeries G (k + 1) := by
--             intro k
--             induction k with
--             | zero =>
--               simp only [lowerCentralSeries_zero, ← MonoidHom.range_eq_map, Subgroup.subtype_range]
--               exact lowerCentralSeries_one.symm.le
--             | succ k ihk =>
--               -- lowerCentralSeries D (k+1) = [lowerCentralSeries D k, ⊤]
--               -- map to G: [lowerCentralSeries D k, D] ≤ [lowerCentralSeries G (k+1), G]
--               have step1 : (lowerCentralSeries D (k + 1)).map D.subtype =
--                   ⁅(lowerCentralSeries D k).map D.subtype, (⊤ : Subgroup D).map D.subtype⁆ := by
--                 show Subgroup.map D.subtype (⁅lowerCentralSeries D k, ⊤⁆) = _
--                 exact Subgroup.map_commutator _ _ _
--               have step2 : (⊤ : Subgroup D).map D.subtype = D := by
--                 rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]
--               rw [step1, step2]
--               calc ⁅(lowerCentralSeries D k).map D.subtype, D⁆
--                   ≤ ⁅lowerCentralSeries G (k + 1), D⁆ :=
--                     Subgroup.commutator_mono ihk le_rfl
--                 _ ≤ ⁅lowerCentralSeries G (k + 1), lowerCentralSeries G 1⁆ :=
--                     Subgroup.commutator_mono le_rfl lowerCentralSeries_one.symm.le
--                 _ ≤ ⁅lowerCentralSeries G (k + 1), ⊤⁆ :=
--                     Subgroup.commutator_mono le_rfl le_top
--                 _ = lowerCentralSeries G (k + 2) := rfl
--           -- Since lowerCentralSeries G (n+1) = ⊥, we have
--           -- (lowerCentralSeries D n).map D.subtype ≤ ⊥
--           have h_bot : (lowerCentralSeries D n).map D.subtype ≤ ⊥ := by
--             calc (lowerCentralSeries D n).map D.subtype ≤ lowerCentralSeries G (n + 1) := h_incl n
--               _ = ⊥ := hG_class
--           -- This means lowerCentralSeries D n = ⊥
--           ext ⟨x, hx⟩
--           simp only [Subgroup.mem_bot]
--           constructor
--           · intro hxmem
--             have : D.subtype ⟨x, hx⟩ ∈ (lowerCentralSeries D n).map D.subtype := by
--               exact Subgroup.mem_map_of_mem D.subtype hxmem
--             have := h_bot this
--             simp only [Subgroup.mem_bot] at this
--             ext; exact this
--           · intro h; rw [h]; exact Subgroup.one_mem _
--
--         -- D is FG nilpotent with class ≤ n, so by IH all subgroups of D are FG
--         haveI : Group.IsNilpotent D := Subgroup.isNilpotent D
--
--         -- Map Z(G) → G/D (abelianization)
--         let π : G →* G ⧸ D := QuotientGroup.mk' D
--         -- G/D is commutative (D = [G,G] = commutator G)
--         -- Use the default quotient group structure
--         haveI hGD_fg : Group.FG (G ⧸ D) := QuotientGroup.fg D
--
--         -- Image of Z(G) in G/D is FG (subgroup of abelian FG)
--         have h_img_fg : (Subgroup.center G).map π |>.FG := by
--           -- G/D is FG abelian (since D = [G,G]), so all subgroups are FG
--           -- Use the fact that G/D = G^ab is FG abelian
--           -- The image is a subgroup of an FG abelian group, hence FG
--           -- Since D = commutator G and the quotient types are the same,
--           -- we can transfer the result
--           have h := @fg_subgroup_of_comm_group (G ⧸ commutator G) (Abelianization.commGroup G)
--             (QuotientGroup.fg (commutator G)) ((Subgroup.center G).map (QuotientGroup.mk' (commutator G)))
--           convert h using 1
--
--         -- D = [G,G] is FG by the commutator_fg lemma
--         haveI hD_fg : Group.FG D := by
--           rw [Group.fg_iff_subgroup_fg]
--           exact commutator_fg
--
--         -- Kernel: Z(G) ∩ D is FG (subgroup of D which has class ≤ n)
--         have h_ker_fg : (Subgroup.center G ⊓ D).FG := by
--           -- View Z(G) ∩ D as a subgroup of D
--           let K := (Subgroup.center G).comap D.subtype
--           have hK_map : K.map D.subtype = Subgroup.center G ⊓ D := by
--             rw [Subgroup.map_comap_eq, Subgroup.subtype_range, inf_comm]
--           rw [← hK_map]
--           -- K is a subgroup of D, and D has class ≤ n
--           -- D is FG nilpotent, so by IH, K is FG
--           exact new_group_fg_map K (@ih D _ _ hD_fg hD_class K) D.subtype
--
--         -- Apply fg_of_quot: Z(G) with kernel Z(G) ∩ D and image in G/D
--         let φ : (Subgroup.center G) →* (G ⧸ D) := π.comp (Subgroup.center G).subtype
--
--         have h_ker_eq : φ.ker = (Subgroup.center G ⊓ D).subgroupOf (Subgroup.center G) := by
--           ext ⟨x, hx⟩
--           simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
--           constructor
--           · intro h
--             refine ⟨hx, ?_⟩
--             -- h : φ ⟨x, hx⟩ = 1, i.e., π x = 1
--             exact (QuotientGroup.eq_one_iff (N := D) x).mp h
--           · intro ⟨_, hD⟩
--             exact (QuotientGroup.eq_one_iff (N := D) x).mpr hD
--
--         -- Transfer FG from (Z(G) ∩ D) to φ.ker
--         have h_ker_fg' : φ.ker.FG := by
--           rw [h_ker_eq]
--           let K' := Subgroup.center G ⊓ D
--           have hK'H : K' ≤ Subgroup.center G := inf_le_left
--           let e : K' ≃* (K'.subgroupOf (Subgroup.center G)) := {
--             toFun := fun ⟨x, hx⟩ => ⟨⟨x, hK'H hx⟩, by simp only [Subgroup.mem_subgroupOf]; exact hx⟩
--             invFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, by simpa only [Subgroup.mem_subgroupOf] using hx⟩
--             left_inv := fun _ => rfl
--             right_inv := fun _ => rfl
--             map_mul' := fun _ _ => rfl
--           }
--           have hKfg : Group.FG K' := (Group.fg_iff_subgroup_fg K').mpr h_ker_fg
--           have hKsubfg : Group.FG (K'.subgroupOf (Subgroup.center G)) :=
--             Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
--           exact (Group.fg_iff_subgroup_fg _).mp hKsubfg
--
--         -- φ.range is FG
--         have h_range_fg : φ.range.FG := by
--           have h_eq : φ.range = (Subgroup.center G).map π := by
--             ext x
--             constructor
--             · intro ⟨y, hy⟩
--               exact ⟨y.val, y.property, hy⟩
--             · intro ⟨y, hy, hyx⟩
--               exact ⟨⟨y, hy⟩, hyx⟩
--           rw [h_eq]; exact h_img_fg
--
--         -- Quotient Z(G) / φ.ker ≃ φ.range is FG
--         haveI : Group.FG ((Subgroup.center G) ⧸ φ.ker) := by
--           have h_equiv := QuotientGroup.quotientKerEquivRange φ
--           have hrangefg : Group.FG φ.range := (Group.fg_iff_subgroup_fg φ.range).mpr h_range_fg
--           exact Group.fg_of_surjective (f := h_equiv.symm.toMonoidHom) (MulEquiv.surjective _)
--
--         -- Apply fg_of_quot
--         exact (Group.fg_iff_subgroup_fg _).mp
--           (@fg_of_quot (Subgroup.center G) _ _ φ.ker _ _ h_ker_fg' _)
--
--       -- H ∩ Z(G) is a subgroup of Z(G), which is abelian and FG
--       -- Therefore H ∩ Z(G) is FG
--       have h_inter_fg : (H ⊓ Subgroup.center G).FG := by
--         -- H ∩ Z(G) is the image of a subgroup of Z(G)
--         haveI : Group.FG (Subgroup.center G) := by
--           rw [Group.fg_iff_subgroup_fg]; exact hZ_fg
--         -- Let K be H ∩ Z(G) viewed inside Z(G)
--         let K := H.comap (Subgroup.center G).subtype
--         have hK_fg : K.FG := fg_subgroup_of_comm_group K
--         -- K maps to H ∩ Z(G) under subtype
--         have h_map : Subgroup.map (Subgroup.center G).subtype K = H ⊓ Subgroup.center G := by
--           ext x
--           simp only [Subgroup.mem_map, Subgroup.mem_inf]
--           constructor
--           · intro ⟨y, hy, hyx⟩
--             rw [← hyx]
--             exact ⟨hy, y.property⟩
--           · intro ⟨hx1, hx2⟩
--             exact ⟨⟨x, hx2⟩, hx1, rfl⟩
--         rw [← h_map]
--         exact new_group_fg_map K hK_fg (Subgroup.center G).subtype
--
--       -- H fits into exact sequence: 1 → (H ∩ Z(G)) → H → H' → 1
--       -- Use fg_of_quot on H with kernel (H ∩ Z(G))
--
--       -- The kernel of H → G/Z(G) restricted to H is H ∩ Z(G)
--       let ψ : H →* (G ⧸ Subgroup.center G) := (QuotientGroup.mk' (Subgroup.center G)).comp H.subtype
--
--       -- Show range of ψ equals H'
--       have h_range : ψ.range = H' := by
--         ext x
--         constructor
--         · intro ⟨y, hy⟩
--           exact ⟨y.val, y.property, hy⟩
--         · intro ⟨y, hy, hyx⟩
--           exact ⟨⟨y, hy⟩, hyx⟩
--
--       -- The kernel ψ.ker is FG (isomorphic to H ∩ Z(G))
--       have h_ker_fg'' : ψ.ker.FG := by
--         -- ψ.ker = (H ⊓ Z(G)).subgroupOf H
--         have h_ker_eq : ψ.ker = (H ⊓ Subgroup.center G).subgroupOf H := by
--           ext ⟨x, hx⟩
--           simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
--           constructor
--           · intro h
--             refine ⟨hx, ?_⟩
--             exact (QuotientGroup.eq_one_iff _).mp h
--           · intro ⟨_, h⟩
--             exact (QuotientGroup.eq_one_iff _).mpr h
--         rw [h_ker_eq]
--         -- Transfer FG from (H ⊓ Z(G)) to its subgroupOf via isomorphism
--         let K := H ⊓ Subgroup.center G
--         have hKH : K ≤ H := inf_le_left
--         let e : K ≃* (K.subgroupOf H) := {
--           toFun := fun ⟨x, hx⟩ => ⟨⟨x, hKH hx⟩, by simp only [Subgroup.mem_subgroupOf]; exact hx⟩
--           invFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, by simpa only [Subgroup.mem_subgroupOf] using hx⟩
--           left_inv := fun _ => rfl
--           right_inv := fun _ => rfl
--           map_mul' := fun _ _ => rfl
--         }
--         have hKfg : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr h_inter_fg
--         have hKsubfg : Group.FG (K.subgroupOf H) := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
--         exact (Group.fg_iff_subgroup_fg _).mp hKsubfg
--
--       -- The quotient H / ψ.ker is FG (isomorphic to H' which is FG)
--       haveI : Group.FG (H ⧸ ψ.ker) := by
--         have h_equiv : (H ⧸ ψ.ker) ≃* ψ.range := QuotientGroup.quotientKerEquivRange ψ
--         rw [h_range] at h_equiv
--         -- H' is FG as a subgroup, so as a group it's FG
--         haveI : Group.FG H' := (Group.fg_iff_subgroup_fg H').mpr hH'_fg
--         exact Group.fg_of_surjective (f := h_equiv.symm.toMonoidHom) (MulEquiv.surjective _)
--
--       -- Apply fg_of_quot to conclude H is FG
--       rw [← Group.fg_iff_subgroup_fg]
--       exact @fg_of_quot H _ _ ψ.ker _ _ h_ker_fg'' _

-- lemma new_subgroup_fg_of_nilpotent_fg {G: Type*} [Group G] [hG: Group.IsNilpotent G] [Group.FG G] (H: Subgroup G): H.FG:= by
--   induction hn: Group.nilpotencyClass H generalizing H G with
--   | zero =>
--     rw [nilpotencyClass_zero_iff_subsingleton] at hn
--     rw [← Group.fg_iff_subgroup_fg]
--     infer_instance
--   | succ n ih =>
--     have center_class: Group.nilpotencyClass (Subgroup.center H) ≤ 1 := by
--       apply CommGroup.nilpotencyClass_le_one

--     have quot_center := nilpotencyClass_quotient_center (G := H)
--     rw [hn] at quot_center
--     simp at quot_center





--     have prev := ih (G := (H ⧸ (Subgroup.center H))) ⊤



--lemma subgroup_fg_of_nilpotent_fg {G: Type*} [Group G] [hG: Group.IsNilpotent G] [Group.FG G]: ∀ (H: Subgroup G), H.FG:= by

  -- apply nilpotent_center_quotient_ind (P := fun A _ _ => ∀ (B: Subgroup A), B.FG)
  -- .
  --   intro A _ hA
  --   intro BAll
  --   rw [← Group.fg_iff_subgroup_fg]
  --   infer_instance
  -- . intro A _ _ h_quot
  --   classical

  --   intro B

  --   let B' := Subgroup.map (QuotientGroup.mk' (Subgroup.center A)) B
  --   have B'_fg := h_quot B'

  --   let A' := Subgroup.map (QuotientGroup.mk' (Subgroup.center A)) (Subgroup.center A)
  --   have A'_fg := h_quot A'

  --   have foo := comap_upperCentralSeries_quotient_center (G := A) 2
  --   apply_fun (Subgroup.map (QuotientGroup.mk' (Subgroup.center A))) at foo
  --   rw [Subgroup.map_comap_eq_self] at foo
  --   .
  --     have bar := new_group_fg_map (upperCentralSeries A (Nat.succ 2)) (by sorry) (QuotientGroup.mk' (Subgroup.center A))
  --     rw [← foo] at bar
  --     sorry
  --   . simp

  --   have a_fg := h_quot ⊤
  --   rw [← Group.fg_def] at a_fg




  --   sorry
  --   apply fg_of_quot (H := (Subgroup.center A))
  --   sorry
