import Mathlib

@[simp]
lemma mulequiv_ker_eq_bot {G H: Type*} [Group G] [Group H] (f: G ≃* H): (f: G →* H).ker = ⊥ := by
  have foo := MonoidHom.ker_eq_bot_iff f.toMonoidHom
  rw [← MulEquiv.toMonoidHom_eq_coe]
  rw [foo.mpr]
  simp
  exact MulEquiv.injective f

lemma lowerCentralSeries_congr {G H: Type*} [Group G] [Group H] [Group.IsNilpotent G] [Group.IsNilpotent H] (f: G ≃* H): Group.nilpotencyClass G = Group.nilpotencyClass H := by
  have first  := nilpotencyClass_le_of_surjective f.toMonoidHom (by simp; exact MulEquiv.surjective f)
  have second := nilpotencyClass_le_of_surjective f.symm.toMonoidHom (by simp; exact MulEquiv.surjective f.symm)
  linarith

-- lemma lowerCentralSeries_lowerCentralSeries {G: Type*} [Group G] [Group.IsNilpotent G] {a b: ℕ}:
--     Subgroup.map (Subgroup.subtype _) (lowerCentralSeries (lowerCentralSeries G a) b) = lowerCentralSeries G (a + b) := by

--   induction b with
--   | zero =>
--     simp
--     rw [le_antisymm_iff]
--     refine ⟨?_, ?_⟩
--     .
--       intro x hx
--       simp at hx
--       simpa using hx
--     .
--       induction a with
--       | zero =>
--         simp
--         ext a
--         simp
--       | succ n ih =>
--         rw [lowerCentralSeries_succ]
--         simp
--         -- intro x hx
--         -- simp at hx
--         -- simp
--         -- obtain ⟨p, hp, q, hq⟩ := hx
--         -- rw [mem_lowerCentralSeries_succ_iff]
--         -- apply Subgroup.mem_closure_of_mem
--         -- simp
--         -- use p
--         -- refine ⟨?_, ?_⟩
--         -- .
--         --   specialize ih hp
--         --   simpa using ih
--         -- .
--         --   use q
--         --   rw [← hq]
--         --   rfl
--   | succ n ih =>
--     rw [le_antisymm_iff]
--     refine ⟨?_, ?_⟩
--     .
--       rw [lowerCentralSeries_succ]
--       rw [← add_assoc]
--       rw [lowerCentralSeries_succ]
--       rw [Subgroup.map_le_iff_le_comap]
--       rw [Subgroup.closure_le]
--       intro x hx
--       simp
--       rw [Subgroup.mem_subgroupOf]
--       rw [← ih]
--       apply Subgroup.mem_closure_of_mem
--       simp
--       simp only [Set.mem_setOf_eq] at hx
--       obtain ⟨p, hp, q, hq, hx⟩ := hx
--       use p
--       use ?_
--       .
--         use q
--         simp [← hx]
--       . use ?_
--         simp
--     .
--       rw [← add_assoc]
--       rw [lowerCentralSeries_succ]
--       rw [Subgroup.closure_le]
--       rw [← ih]
--       intro x hx

--       rw [lowerCentralSeries_succ]
--       simp only [Set.mem_setOf_eq] at hx
--       simp only [
--         Subgroup.coe_map, Subgroup.subtype_apply, Set.mem_image, SetLike.mem_coe, exists_and_right,
--         ]
--       use ⟨x, ?_⟩
--       . refine ⟨?_, ?_⟩
--         .
--           apply Subgroup.mem_closure_of_mem
--           simp only [Set.mem_setOf_eq]
--           obtain ⟨p, hp, q, hq, hx⟩ := hx
--           simp at hp
--           obtain ⟨p_mem, p_mem_nested⟩ := hp
--           use ⟨p, p_mem⟩
--           use ?_
--           .

--             use q
--             simp [← hx]
--           . use ?_
--             simp

--       use x
--     ext x
--     refine ⟨?_, ?_⟩
--     .
--       intro hx
--       simp at hx
--       obtain ⟨x_mem, x_mem_nested⟩ := hx
--       rw [← add_assoc]
--       -- rw [mem_lowerCentralSeries_succ_iff]
--       -- apply Subgroup.mem_closure_of_mem
--       -- simp
--       --rw [← ih]

--       rw [mem_lowerCentralSeries_succ_iff] at x_mem_nested
--       rw [mem_lowerCentralSeries_succ_iff]
--       rw [← Subgroup.mem_map_iff_mem (f := Subgroup.subtype _)] at x_mem_nested
--       .
--         simp only [Subgroup.subtype_apply] at x_mem_nested
--         rw [← ih]



--         rw [Subgroup.mem_map] at x_mem_nested
--         grw [lowerCentralSeries_map_subtype_le] at x_mem_nested



--       . simp
--       apply_fun (Subgroup.subtype _) at x_mem_nested
--     . sorry




-- lemma new_lowerCentralSeries_nilpotencyClass_succ {G: Type*} [Group G] [Group.IsNilpotent G] [Nontrivial G] :
--   (Group.nilpotencyClass (lowerCentralSeries G 1)) = (Group.nilpotencyClass G) - 1 := by

--   generalize hn : Group.nilpotencyClass G = n
--   rcases n with (rfl | n)
--   · simp only [nilpotencyClass_zero_iff_subsingleton, zero_tsub] at *
--     exact instSubsingletonSubtype_mathlib fun x ↦ x ∈ lowerCentralSeries G 1
--   ·
--     simp
--     apply le_antisymm
--     ·

--       rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
--       apply le_of_eq at hn
--       rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le] at hn
--       apply_fun (Subgroup.map (Subgroup.subtype _))
--       .
--         simp [← hn]
--         ext a
--         refine ⟨?_, ?_⟩
--         .
--           intro ha
--           simp at ha
--           rw [mem_lowerCentralSeries_succ_iff]
--           obtain ⟨ha, a_mem_lower⟩ := ha
--           apply Subgroup.mem_closure_of_mem
--           simp

--           sorry
--         .
--           intro ha
--           simp
--           sorry
--       . apply Subgroup.map_injective
--         exact Subgroup.subtype_injective (commutator G)
--       apply comap_injective (f := (mk' (center G))) Quot.mk_surjective
--       rw [comap_upperCentralSeries_quotient_center, comap_top, Nat.succ_eq_add_one, ← hn]
--       exact upperCentralSeries_nilpotencyClass
--     ·

--       apply le_of_add_le_add_right (a := 1)
--       rw [← hn]
--       rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]


--       apply nilpotencyClass_le_of_ker_le_center



--       calc
--         n + 1 = Group.nilpotencyClass G := hn.symm
--         _ ≤ Group.nilpotencyClass (G) + 1 :=
--           nilpotencyClass_le_of_ker_le_center _ (le_of_eq (ker_mk' _)) _

lemma lowerCentralSeries_nilpotencyClass_succ {G: Type*} [Group G] [Group.IsNilpotent G] [Nontrivial G] :
    (Group.nilpotencyClass G) - 1 = (Group.nilpotencyClass (lowerCentralSeries G 1)) := by

  induction hn: Group.nilpotencyClass G generalizing G with
  | zero =>
    simp
    rw [nilpotencyClass_zero_iff_subsingleton] at hn
    rw [eq_comm, nilpotencyClass_zero_iff_subsingleton]
    infer_instance
  | succ k ih =>
    simp
    simp at ih




    -- rw [nilpotencyClass_eq_quotient_center_plus_one] at hn
    -- simp at hn
    -- by_cases quot_nontrivial:  Nontrivial (G ⧸ Subgroup.center G)
    -- .
    --   have foo := ih hn
    --   rw [nilpotencyClass_quotient_center] at foo

    -- .
    --   rw [not_nontrivial_iff_subsingleton] at quot_nontrivial
    --   rw [← nilpotencyClass_zero_iff_subsingleton] at quot_nontrivial
    --   rw [quot_nontrivial] at hn
    --   simp [← hn]
    --   sorry
    -- rw [← hn]
    -- rw [nilpotencyClass_eq_quotient_center_plus_one]

    have foo := le_of_eq hn
    have bar := lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr foo
    rw [le_antisymm_iff]
    refine ⟨?_, ?_⟩
    .

      sorry
    .


      rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
      rw [lowerCentralSeries_succ] at bar
      simp at bar




      sorry


      -- clear hn
      -- induction n with
      -- | zero =>
      --   simp
      --   rw [nilpotencyClass_zero_iff_subsingleton]
      --   simp at foo
      --   rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le] at foo
      --   simp at foo
      --   simp [foo]
      --   exact Unique.instSubsingleton
      -- | succ n ih =>
      --   simp
      --   rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
      --   rw [lowerCentralSeries_succ]
      --   rw [← le_bot_iff]
      --   rw [Subgroup.closure_le]
      --   intro x hx
      --   simp
      --   simp only [Set.mem_setOf_eq] at hx
      --   obtain ⟨p, hp, q, _, hx⟩ := hx
      --   rw [← hx]
      --   rw [mul_eq_one_iff_inv_eq']
      --   simp

      --   have char: (commutator G).Characteristic := by infer_instance
      --   rw [Subgroup.characteristic_iff_map_eq] at char
      --   specialize char (MulAut.conj p)
      --   simp at char

      --   apply Subgroup.Normal.conj
      --   rw [← mul_inv_eq_iff_eq_mul₀]
      --   rw [← SetLike.coe_set_eq]
      --   rw [Subgroup.coe_bot]

      --   simp?




    -- rw [nilpotencyClass_eq_quotient_center_plus_one]


    -- rw [← nilpotencyClass_quotient_center]
    -- rw [lowerCentralSeries_succ] at bar
    -- rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    -- match n with
    -- | 0 =>
    --   simp
    --   simp at hn
    --   apply Subgroup.eq_bot_of_subsingleton
    -- | k + 1 =>
    --   rw [lowerCentralSeries_succ]
    --   simp

lemma lowerCentralSeries_nilpotency_sub {G: Type*} [Group G] [Group.IsNilpotent G] (n: ℕ):
  (Group.nilpotencyClass G) = (Group.nilpotencyClass (lowerCentralSeries G n)) + n := by

  induction n with
  | zero =>
      simp
      rw [lowerCentralSeries_congr (Subgroup.topEquiv)]
  | succ n ih =>
    rw [ih]
    have succ_le: lowerCentralSeries G (n + 1) ≤ lowerCentralSeries G n := by
      apply lowerCentralSeries_antitone
      simp


    rw [lowerCentralSeries_succ]



    have first := nilpotencyClass_le_of_ker_le_center (Subgroup.inclusion succ_le) (by
      intro x hx
      simp at hx
      simp [hx]
    ) (by infer_instance)


    sorry


lemma nilpotent_subgroup_fg {G: Type*} [Group G] [Group.FG G] [Group.IsNilpotent G]: ∀ H: Subgroup G, H.FG := by
  induction hn: Group.nilpotencyClass G generalizing G with
  | zero =>
    rw [nilpotencyClass_zero_iff_subsingleton] at hn
    let unique: Unique (Subgroup G) := by infer_instance
    intro H
    rw [unique.uniq (a := H)]
    rw [← unique.uniq (a := ⊤)]
    exact Group.FG.out
  | succ n ih =>
    intro H


    sorry
