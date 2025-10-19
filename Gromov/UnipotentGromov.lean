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

-- TODO - generalize and upstream to mathlib
lemma prod_lex_has_unbounded {f: ℕ → Lex (ℕ × ℕ)} (hf: StrictMono f):
  ¬BddAbove (Set.range (Prod.fst ∘ f)) ∨ ¬BddAbove (Set.range (Prod.snd ∘ f)) := by
  by_contra!
  obtain ⟨fst_bounded, snd_bounded⟩ := this
  have fst_max := Nat.sSup_mem (s := Set.range (Prod.fst ∘ f)) (by apply Set.range_nonempty) fst_bounded
  simp at fst_max
  obtain ⟨fst_max, h_fst_max⟩ := fst_max
  -- have snd_max := Nat.sSup_mem (s := Set.range (Prod.snd ∘ f)) (by apply Set.range_nonempty) snd_bounded
  -- simp at snd_max
  -- obtain ⟨snd_max, h_snd_max⟩ := snd_max

  have f_gt := hf (a := fst_max) (b := 1 + fst_max) (by omega)

  rw [Prod.Lex.lt_iff] at f_gt
  cases f_gt
  .
    rename_i f_gt_max
    conv at f_gt_max =>
      lhs
      equals (f fst_max).1 => rfl
    conv at f_gt_max =>
      rhs
      equals (f (1 + fst_max)).1 => rfl

    rw [h_fst_max] at f_gt_max


    have f_succ_le := le_csSup fst_bounded (a := (f (1 + fst_max)).1) (by simp)
    linarith
  .
    rename_i h
    obtain ⟨fst_eq, snd_lt⟩ := h

    have bdd_above_subset: BddAbove { a: ℕ | ∃ n: ℕ, (f n).1 = (f fst_max).1 ∧ (f n).2 = a } := by
      apply BddAbove.mono (t := Set.range (Prod.snd ∘ f))
      . grind
      . apply snd_bounded

    have snd_max := Nat.sSup_mem (by
      use (f fst_max).2
      simp
      use fst_max
    ) bdd_above_subset
    obtain ⟨snd_max, f_snd_max_eq, h_snd_max⟩ := snd_max
    have f_gt_snd := hf (a := snd_max) (b := 1 + snd_max) (by omega)
    rw [Prod.Lex.lt_iff] at f_gt_snd
    cases f_gt_snd
    .
      rename_i fst_component_gt

      conv at fst_component_gt =>
        lhs
        equals (f snd_max).1 => rfl
      conv at fst_component_gt =>
        rhs
        equals (f (1 + snd_max)).1 => rfl

      have f_succ_le := le_csSup fst_bounded (a := (f (1 + snd_max)).1) (by simp)
      rw [← h_fst_max] at f_succ_le
      linarith
    . rename_i fst_eq_snd_lt
      obtain ⟨new_fst_eq, new_snd_lt⟩ := fst_eq_snd_lt
      conv at new_fst_eq =>
        lhs
        equals (f snd_max).1 => rfl
      conv at new_snd_lt =>
        rhs
        equals (f (1 + snd_max)).2 => rfl


      have f_succ_le := le_csSup bdd_above_subset (a := (f (1 + snd_max)).2) (by
        simp
        use 1 + snd_max
        refine ⟨?_, rfl⟩
        rw [← f_snd_max_eq]
        rw [new_fst_eq]
        rfl
      )
      rw [← h_snd_max] at f_succ_le
      conv at new_snd_lt =>
        lhs
        equals (f snd_max).2 => rfl
      linarith




-- TODO - h_cur is wrong, we can have things like 'gamma_alpha * a'
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
      have h_cur_neq := h_cur cur_neq

      -- by_cases prev_pos_eq_zero: prev.pos.1 = 0
      -- . simp [prev_pos_eq_zero]
      --   have conj_mem := N_normal.conj_mem cur (h_cur_neq) prev.cur
      --   use ?_
      --   .

      --     -- by_cases prev_eq_gamma: prev.cur = gamma_alpha
      --     -- .
      --     --   simp_rw [prev_eq_gamma]
      --     simp [commutator]
      --     simp [Bracket.bracket]
      --     apply Subgroup.mem_closure_of_mem

      --     sorry
      --   . simp [Bracket.bracket]
      --     apply Subgroup.mul_mem
      --     . exact conj_mem
      --     . exact (Subgroup.inv_mem_iff N).mpr h_cur_neq

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
        ) ⟨cur, h_cur_neq⟩
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
          use h_cur_neq
          rfl

        . apply Subgroup.mul_mem
          . apply Subgroup.mul_mem
            . apply Subgroup.mul_mem
              . exact prev_cur_mem_N
              . exact h_cur_neq
            . exact (Subgroup.inv_mem_iff N).mpr prev_cur_mem_N
          . exact (Subgroup.inv_mem_iff N).mpr h_cur_neq
        exact Subgroup.subtype_injective N
      .
        dsimp [Bracket.bracket]
        apply Subgroup.mul_mem
        . apply Subgroup.mul_mem
          . apply Subgroup.mul_mem
            . exact prev_cur_mem_N
            . exact h_cur_neq
          . exact (Subgroup.inv_mem_iff N).mpr prev_cur_mem_N
        . exact (Subgroup.inv_mem_iff N).mpr h_cur_neq
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

-- TODO ' add simp lemma to avoid the need for all of the 'conv' steps, and upstream to mathlib
lemma G''_comm_strict_mono {T: Type*} [Group T] {N: Subgroup T} (N_normal: N.Normal) (gamma_alpha cur: T) (h_cur: cur ≠ gamma_alpha → cur ∈ N) (prev: G''CommData N gamma_alpha):
  prev.pos < (G''_comm N_normal gamma_alpha cur h_cur prev).pos := by

  simp [G''_comm]
  split_ifs
  .
    rw [Prod.Lex.lt_iff]
    right
    refine ⟨?_, ?_⟩
    .
      conv =>
        lhs
        equals prev.pos.1 => rfl
      conv =>
        rhs
        equals (prev.pos.1) => rfl
    . conv =>
        lhs
        equals (prev.pos.2) => rfl
      conv =>
        rhs
        equals (prev.pos.2 + 1) => rfl
      omega
  . rw [Prod.Lex.lt_iff]
    left
    conv =>
      lhs
      equals prev.pos.1 => rfl
    conv =>
      rhs
      equals (prev.pos.1 + 1) => rfl
    omega
#print axioms G''_comm

-- noncomputable instance inf_lex: InfSet (Lex (ℕ × ℕ)) := {
--   sInf := fun s => (sInf (Prod.fst '' s), sInf (Prod.snd '' s))
-- }

-- instance lattice_lex: ConditionallyCompleteLattice  (Lex (ℕ × ℕ)) := {
--   sSup :=  fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))
--   le_csSup := by
--     intro s a hs ha
--     unfold BddAbove at hs
--     obtain ⟨upper, h_upper⟩ := hs
--     simp [upperBounds] at h_upper
--     specialize h_upper a.fst a.snd ha
--     rw [Prod.Lex.le_iff]
--     by_cases fst_eq: a.fst = (sSup (Prod.fst '' s))
--     .
--       right
--       refine ⟨?_, ?_⟩
--       . exact fst_eq
--       .
--         conv =>
--           lhs
--           equals a.snd => rfl
--         conv =>
--           rhs
--           equals (sSup (Prod.snd '' s)) => rfl

--         apply le_csSup
--         . sorry
--         .
--           simp
--           use a.1
--           exact ha

--     --rw [Prod.Lex.le_iff] at h_upper
--     cases h_upper
--     . rename_i fst_lt
--       rw [Prod.Lex.le_iff]
--       left
--       conv =>
--         equals a.1 < (sSup (Prod.fst '' s)) => rfl

--       conv at fst_lt =>
--         lhs
--         equals a.1 => rfl


--       rw [lt_csSup_iff]
--       .
--     . rename_i fst_eq
--       sorry
--   csSup_le := _
--   csInf_le := _
--   le_csInf := _
-- }

open Classical in
def RepeatComm {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (hN: ∀ {g : G}, g ≠ gamma_alpha → g ∈ N) (n: ℕ): Set (G''CommData N gamma_alpha) :=
match n with
| 0 => Set.range (fun (g: N) =>{
    cur := g
    pos := (0, 0)
    pos_first := by
      simp
    pos_second := by
      simp
  })
| n + 1 => Set.sUnion (Set.image (fun prev => (
  Set.range (fun (g: G) => G''_comm N_normal gamma_alpha g hN prev)
)) (RepeatComm N_normal gamma_alpha hN n))

lemma RepeatComm_wf {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (hN: ∀ {g : G}, g ≠ gamma_alpha → g ∈ N) (n: ℕ):
  ((fun a => a.pos) '' (RepeatComm N_normal gamma_alpha hN n)).IsWF := by
  apply Set.IsWF.of_wellFoundedLT

lemma RepeatComm_nonempty {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (hN: ∀ {g : G}, g ≠ gamma_alpha → g ∈ N) (n: ℕ):
  (RepeatComm N_normal gamma_alpha hN n).Nonempty := by
  rw [RepeatComm.eq_def]
  split
  . apply Set.range_nonempty
  .
    rename_i j k
    simp
    obtain ⟨a, ha⟩ := RepeatComm_nonempty N_normal gamma_alpha hN k
    use a
    refine ⟨ha, ?_⟩
    apply Set.range_nonempty


-- TODO - golf and upstream to mathlib
theorem Set.IsWF.lt_min_iff {α: Type*} [LinearOrder α] {s: Set α} {a : α} (hs : s.IsWF) (hn : s.Nonempty) : a < hs.min hn ↔ ∀ b, b ∈ s → a < b := by
  by_cases a_eq: a = hs.min hn
  .
    simp [a_eq]
    use hs.min hn
    refine ⟨?_, ?_⟩
    . exact Set.IsWF.min_mem hs hn
    . simp
  .
    rw [lt_iff_le_and_ne]
    simp [a_eq]
    refine ⟨?_, ?_⟩
    .
      intro ha
      rw [le_iff_eq_or_lt] at ha
      simp [a_eq] at ha
      intro b hb
      have min_le := Set.IsWF.min_le hs (by exact hn) hb
      exact Std.lt_of_lt_of_le ha min_le
    . intro ha
      have a_le: ∀ b ∈ s, a ≤ b := by
        exact fun b a_1 ↦ Std.le_of_lt (ha b a_1)
      rw [le_iff_eq_or_lt]
      simp [a_eq]

      have min_mem := Set.IsWF.min_mem hs hn
      specialize ha _ min_mem
      exact ha


noncomputable def RepeatComm_min {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (hN: ∀ {g : G}, g ≠ gamma_alpha → g ∈ N) (n: ℕ) :=
  (RepeatComm_wf N_normal gamma_alpha hN n).min (by
    simp
    apply RepeatComm_nonempty
  )

lemma RepeatComm_min_strict_mono' {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (hN: ∀ {g : G}, g ≠ gamma_alpha → g ∈ N) (n: ℕ):
  (RepeatComm_min N_normal gamma_alpha hN n) < RepeatComm_min N_normal gamma_alpha hN (n + 1)  := by
  simp [RepeatComm_min]
  rw [Set.IsWF.lt_min_iff]
  intro a ha
  simp at ha
  obtain ⟨data, data_in, ha_eq⟩ := ha
  simp [RepeatComm] at data_in
  obtain ⟨prev, prev_in, h_prev⟩ := data_in
  obtain ⟨g, hg⟩ := h_prev
  rw [← ha_eq]
  rw [← hg]
  by_cases min_eq_prev: prev.pos = (RepeatComm_min N_normal gamma_alpha hN n)
  .
    have min_mem := Set.IsWF.min_mem (RepeatComm_wf N_normal gamma_alpha hN n) (by
      simp
      apply RepeatComm_nonempty
    )
    simp at min_mem
    obtain ⟨x, x_mem, x_pos_eq⟩ := min_mem
    rw [← x_pos_eq]
    simp [RepeatComm_min] at min_eq_prev
    rw [← min_eq_prev] at x_pos_eq
    rw [x_pos_eq]
    apply G''_comm_strict_mono
  .
    simp [RepeatComm_min] at min_eq_prev
    have prev_not_lt := Set.IsWF.not_lt_min (RepeatComm_wf N_normal gamma_alpha hN n) (by
      simp
      apply RepeatComm_nonempty
    ) (a := prev.pos) (by
      simp
      use prev
    )
    rw [lt_iff_le_and_ne] at prev_not_lt
    simp [min_eq_prev] at prev_not_lt


    have prev_mono := G''_comm_strict_mono N_normal gamma_alpha g hN prev
    exact gt_trans prev_mono prev_not_lt

lemma RepeatComm_min_strict_mono {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (hN: ∀ {g : G}, g ≠ gamma_alpha → g ∈ N):
  StrictMono (fun n => RepeatComm_min N_normal gamma_alpha hN n) := by
  intro a b ab
  simp
  apply strictMono_of_lt_succ
  .
    intro a _
    apply RepeatComm_min_strict_mono'
  . exact ab


lemma RepeatComm_eventually_le {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (hN: ∀ {g : G}, g ≠ gamma_alpha → g ∈ N) (a b: ℕ):
  ∃ n: ℕ, a ≤ (RepeatComm_min N_normal gamma_alpha hN n).fst ∨ b ≤ (RepeatComm_min N_normal gamma_alpha hN n).snd := by

  have unbounded := prod_lex_has_unbounded (RepeatComm_min_strict_mono N_normal gamma_alpha hN)
  -- TODO - deduplicate most of these cases
  cases unbounded
  .
    rename_i fst_unbounded
    rw [not_bddAbove_iff] at fst_unbounded
    specialize fst_unbounded a
    obtain ⟨n, hn⟩ := fst_unbounded
    simp at hn
    obtain ⟨⟨c, c_eq⟩, a_lt_n⟩ := hn
    use c
    left
    rw [c_eq]
    exact Nat.le_of_succ_le a_lt_n
  .
    rename_i snd_unbounded
    rw [not_bddAbove_iff] at snd_unbounded
    specialize snd_unbounded b
    obtain ⟨n, hn⟩ := snd_unbounded
    simp at hn
    obtain ⟨⟨c, c_eq⟩, b_lt_n⟩ := hn
    use c
    right
    rw [c_eq]
    exact Nat.le_of_succ_le b_lt_n






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
