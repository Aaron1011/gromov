import Mathlib

@[simp]
lemma mulequiv_ker_eq_bot {G H: Type*} [Group G] [Group H] (f: G ≃* H): (f: G →* H).ker = ⊥ := by
  have foo := MonoidHom.ker_eq_bot_iff f.toMonoidHom
  rw [← MulEquiv.toMonoidHom_eq_coe]
  rw [foo.mpr]
  simp
  exact MulEquiv.injective f

lemma lowerCentralSeries_congr {G H: Type*} [Group G] [Group H] [Group.IsNilpotent G] [Group.IsNilpotent H] (f: G ≃* H) (n: ℕ): Group.nilpotencyClass G = Group.nilpotencyClass H := by
  have first  := nilpotencyClass_le_of_surjective f.toMonoidHom (by simp; exact MulEquiv.surjective f)
  have second := nilpotencyClass_le_of_surjective f.symm.toMonoidHom (by simp; exact MulEquiv.surjective f.symm)
  linarith

lemma lowerCentralSeries_lowerCentralSeries {G: Type*} [Group G] [Group.IsNilpotent G] {a b: ℕ}:
    Subgroup.map (Subgroup.subtype _) (lowerCentralSeries (lowerCentralSeries G a) b) = lowerCentralSeries G (a + b) := by

  induction a with
  | zero =>
    simp
    rw [le_antisymm_iff]
    refine ⟨?_, ?_⟩
    . grw [lowerCentralSeries_map_subtype_le]
    .
      induction b with
      | zero =>
        simp
        ext a
        simp
      | succ n ih =>
        rw [lowerCentralSeries_succ]
        simp
        intro x hx
        simp at hx
        simp
        obtain ⟨p, hp, q, hq⟩ := hx
        rw [mem_lowerCentralSeries_succ_iff]
        apply Subgroup.mem_closure_of_mem
        simp
        use p
        refine ⟨?_, ?_⟩
        .
          specialize ih hp
          simpa using ih
        .
          use q
          rw [← hq]
          rfl
  | succ n ih =>
    ext a
    refine ⟨?_, ?_⟩
    .
      intro ha
      simp at ha
      obtain ⟨a_mem, a_mem_nested⟩ := ha
      rw [add_comm, ← add_assoc]
      rw [mem_lowerCentralSeries_succ_iff]
      apply Subgroup.mem_closure_of_mem
      simp
      




lemma lowerCentralSeries_nilpotencyClass_succ {G: Type*} [Group G] [Group.IsNilpotent G] [Nontrivial G]  :
    (Group.nilpotencyClass G) - 1 = (Group.nilpotencyClass (lowerCentralSeries G 1)) := by

  induction hn: Group.nilpotencyClass G generalizing G with
  | zero =>
    simp
    rw [nilpotencyClass_zero_iff_subsingleton] at hn
    rw [eq_comm, nilpotencyClass_zero_iff_subsingleton]
    infer_instance
  | succ k ih =>
    have foo := le_of_eq hn
    have bar := lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr foo
    simp only [add_tsub_cancel_right]
    rw [le_antisymm_iff]
    refine ⟨?_, ?_⟩
    .

      sorry
    .
      rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]

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
      rw [lowerCentralSeries_congr (Subgroup.topEquiv) 0]
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
