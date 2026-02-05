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

lemma lowerCentralSeries_nilpotencyClass_succ {G: Type*} [Group G] [Group.IsNilpotent G] (n: ℕ):
    Group.nilpotencyClass (lowerCentralSeries G (Group.nilpotencyClass (G))) ≤ (Group.nilpotencyClass G) - 1 := by

  induction hn: Group.nilpotencyClass G generalizing G with
  | zero =>
    simp
    rw [nilpotencyClass_zero_iff_subsingleton] at hn
    rw [nilpotencyClass_zero_iff_subsingleton]
    infer_instance

    -- let unique: Unique (Subgroup G) := by infer_instance
    -- simp [commutator]
    -- have subgroup_sub: Subsingleton (Subgroup G) := by infer_instance
    -- rw [← subsingleton_iff_bot_eq_top] at subgroup_sub

    -- rw [unique.uniq (a := commutator G)]
    -- rw [← unique.uniq (a := ⊤)]
    -- exact Group.FG.out
  | succ k ih =>
    have foo := le_of_eq hn
    have bar := lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr foo
    rw [bar]
    simp
    rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    match k with
    | 0 =>
      simp
      exact Subgroup.eq_bot_of_subsingleton ⊤
    | k + 1 =>
      rw [lowerCentralSeries_succ]
      simp

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
