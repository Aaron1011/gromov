import Mathlib

def iteratedCommutator {T: Type*} [Group T] (base right: T) (n: ℕ) := Nat.iterate (fun x => ⁅x, right⁆) n base

structure G''CommData {T: Type*} [Group T] (N: Subgroup T) (gamma_alpha: T) where
  -- The result of repeatedly applying commutators
  cur: T

  -- When we take a commutator, we increment the second component if we take a commutator with 'right',
  -- and reset it to zero and increment the first component if we take a commutator with anything else
  -- As a result, 'pos' strictly increases at each step
  pos: Lex (ℕ × ℕ)
  -- The first component of our position is our index in the lower central series of M
  pos_first: cur ∈ Subgroup.map N.subtype (lowerCentralSeries N pos.1)
  -- The second component is the number of copies of 'right' that occur in successive adjacent commutators
  pos_second: pos.2 ≠ 0 → ∃ b: T, cur = iteratedCommutator b gamma_alpha pos.2


set_option trace.profiler true

set_option Elab.async false
--set_option trace.Meta.Tactic.simp true in
--set_option trace.Meta.Tactic.simp.numSteps true in
--set_option trace.Elab.command true in
--open Classical in

-- TODO - upstream to mathlib
instance lower_central_characteristic {G: Type*} [Group G] (n: ℕ): (lowerCentralSeries G n).Characteristic := by
  induction n with
  | zero =>
    simp
    infer_instance
  | succ n ih =>
    unfold lowerCentralSeries
    infer_instance

open Classical in
noncomputable def G''_comm {T: Type*} [Group T] {N: Subgroup T} (N_normal: N.Normal) (gamma_alpha cur: T) (h_cur: cur ≠ gamma_alpha → cur ∈ N) (prev: G''CommData N gamma_alpha): G''CommData N gamma_alpha := {
  cur := ⁅prev.cur, cur⁆
  pos := (if (cur = gamma_alpha) then (prev.pos.1, prev.pos.2 + 1)
        else (prev.pos.1 + 1, 0))
  pos_first := by
    split_ifs
    .
      rename_i next_eq_gamma
      have prev_mem: prev.cur ∈ N := by
        have foo := prev.pos_first
        simp at foo
        obtain ⟨a, a_eq⟩ := foo
        use a

      dsimp [Bracket.bracket]

      have conj_mem: cur * prev.cur⁻¹ * cur⁻¹ ∈ N := by
        apply N_normal.conj_mem
        exact (Subgroup.inv_mem_iff N).mpr prev_mem


      have prod_mem: prev.cur * (cur * prev.cur⁻¹ * cur⁻¹) ∈ N := by
        apply N.mul_mem
        exact prev_mem
        exact conj_mem


      rw [← mul_assoc] at prod_mem
      rw [← mul_assoc] at prod_mem
      simp
      use prod_mem
      have prev_cur_mem := prev.pos_first

      have lower_normal: (lowerCentralSeries (↥N) prev.pos.1).Normal := by
        infer_instance

      have map_normal: (Subgroup.map N.subtype (lowerCentralSeries (↥N) prev.pos.1)).Normal := by
        infer_instance

      have map_conj := map_normal.conj_mem prev.cur⁻¹ (by exact
        (Subgroup.inv_mem_iff (Subgroup.map N.subtype (lowerCentralSeries (↥N) prev.pos.1))).mpr prev_cur_mem) gamma_alpha
      simp_rw [next_eq_gamma]


      have new_prod_mem: prev.cur * (gamma_alpha * prev.cur⁻¹ * gamma_alpha⁻¹) ∈ Subgroup.map N.subtype (lowerCentralSeries (↥N) prev.pos.1) := by
        apply Subgroup.mul_mem
        exact prev_cur_mem
        exact map_conj

      rw [← mul_assoc] at new_prod_mem
      rw [← mul_assoc] at new_prod_mem
      simp at new_prod_mem
      obtain ⟨a, ha⟩ := new_prod_mem
      exact ha
    .
      rename_i cur_neq
      specialize h_cur cur_neq

      simp
      have prev_mem := prev.pos_first
      simp at prev_mem
      obtain ⟨prev_cur_mem_N, prev_cur_mem_lower⟩ := prev_mem
      use ?_
      .
        dsimp [Bracket.bracket]
        have lower_normal : (lowerCentralSeries N prev.pos.1).Normal := by infer_instance
        have conj_mem := lower_normal.conj_mem ⟨prev.cur⁻¹, by exact (Subgroup.inv_mem_iff N).mpr prev_cur_mem_N⟩ (by
          rw [← Subgroup.mem_map_iff_mem (f := Subgroup.subtype N)]
          rw [Subgroup.subtype_apply]
          simp
          use ?_
          . exact prev_cur_mem_N
          . exact Subgroup.subtype_injective N
        ) ⟨cur, h_cur⟩
        rw [← Subgroup.mem_map_iff_mem (f := Subgroup.subtype N)]
        rw [Subgroup.subtype_apply]
        simp only []
        simp
        use ?_
        .
          rw [mem_lowerCentralSeries_succ_iff]
          apply Subgroup.mem_closure_of_mem
          simp
          use prev.cur
          use prev_cur_mem_N
          refine ⟨prev_cur_mem_lower, ?_⟩
          use cur
          use h_cur
          rfl

        . apply Subgroup.mul_mem
          . apply Subgroup.mul_mem
            . apply Subgroup.mul_mem
              . exact prev_cur_mem_N
              . exact h_cur
            . exact (Subgroup.inv_mem_iff N).mpr prev_cur_mem_N
          . exact (Subgroup.inv_mem_iff N).mpr h_cur
        exact Subgroup.subtype_injective N
      .
        dsimp [Bracket.bracket]
        apply Subgroup.mul_mem
        . apply Subgroup.mul_mem
          . apply Subgroup.mul_mem
            . exact prev_cur_mem_N
            . exact h_cur
          . exact (Subgroup.inv_mem_iff N).mpr prev_cur_mem_N
        . exact (Subgroup.inv_mem_iff N).mpr h_cur
  pos_second := by
    split_ifs
    . rename_i cur_eq
      intro _
      unfold iteratedCommutator
      have prev_val := prev.pos_second
      match h_pos: prev.pos.2 with
      | 0 =>
        use prev.cur
        simp [cur_eq]
      | k + 1 =>
        specialize prev_val (by omega)
        obtain ⟨b, b_eq⟩ := prev_val
        unfold iteratedCommutator at b_eq
        simp at h_pos
        rw [h_pos] at b_eq
        rw [Function.iterate_succ'] at b_eq
        simp at b_eq
        use b
        rw [Function.iterate_succ']
        rw [Function.comp_def]
        beta_reduce
        rw [b_eq]
        rw [cur_eq]
        rw [Function.iterate_succ']
        simp
    . rename_i cur_neq
      simp
}

-- | 0 => {
--   cur := cur
--   pos := (0, 0)
--   pos_first := by
--     simp [lowerCentralSeries]
--   pos_second := by
--     simp
-- }
-- | n + 1 => {
--   cur := ⁅(G''_comm N_normal gamma_alpha base next gamma_N n).cur, next⁆
--   pos := (if (next = gamma_alpha) then ((G''_comm N_normal gamma_alpha base next gamma_N n).pos.1, (G''_comm N_normal gamma_alpha base next gamma_N n).pos.2 + 1)
--          else ((G''_comm N_normal gamma_alpha base next gamma_N n).pos.1 + 1, 0))
--   pos_first := by
--     split_ifs
--     .
--       rename_i next_eq_gamma
--       simp [next_eq_gamma]
--       sorry
--     . sorry
--   pos_second := by
--     split_ifs

--     . rename_i next_eq_gamma
--       intro _
--       have prev := (G''_comm N_normal gamma_alpha base next gamma_N n).pos_second
--       by_cases prev_zero: (G''_comm N_normal gamma_alpha base next gamma_N n).pos.2 = 0
--       . use (G''_comm N_normal gamma_alpha base next gamma_N n).cur
--         simp [prev_zero]
--         simp [prev_zero, next_eq_gamma, iteratedCommutator]
--       .
--         have prev_eq := prev prev_zero
--         obtain ⟨b, b_eq⟩ := prev_eq
--         use b
--         simp
--         unfold iteratedCommutator
--         simp
--         simp [iteratedCommutator] at b_eq
--         simp [b_eq, next_eq_gamma]
--         rfl
--         rw [Function.iterate_succ']
--         simp? [next_eq_gamma, iteratedCommutator]
--         simp [next_eq_gamma, iteratedCommutator] at b_eq
--         simp [b_eq]
--     . sorry
--     --   rename_i next_ne_gamma
--     --   simp
-- }
-- termination_by n
-- decreasing_by
--  all_goals { sorry }
