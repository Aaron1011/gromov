import Mathlib

def iteratedCommutator {T: Type*} [Group T] (base right: T) (n: ℕ) := Nat.iterate (fun x => ⁅x, right⁆) n base


def iterate_comm_set {G: Type*} [Group G] (S: Set G) (n: ℕ): Set G :=
  match n with
  | 0 => S
  | n + 1 => Set.iUnion (fun (s: S) => Set.image (fun g => ⁅g, s⁆) (iterate_comm_set S n))

-- lemma iterate_comm_mem_inv {G: Type*} [Group G] (S: Set G) (n: ℕ): iterate_comm_set (S ∪ S⁻¹) n = (iterate_comm_set (S ∪ S⁻¹) n)⁻¹ := by
--   induction n with
--   | zero =>
--     simp [iterate_comm_set]
--     grind
--   | succ n ih =>
--     simp [iterate_comm_set]
--     ext a
--     simp
--     refine ⟨?_, ?_⟩
--     . intro ha
--       obtain ⟨b, b_mem, ⟨c, c_mem, a_eq⟩⟩ := ha
--       use b⁻¹
--       refine ⟨?_, ?_⟩
--       . simp
--         grind
--       .
--         use c⁻¹
--         refine ⟨?_, ?_⟩
--         . sorry
--         .
--           rw [← inv_eq_iff_eq_inv]
--           simp

--     . sorry
-- Lemma 13.30 (4) in https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdfw

lemma comm_prod {G: Type*} [Group G] (x y z: G): ⁅x * y, z⁆ = ⁅x, ⁅y, z⁆⁆ * ⁅y, z⁆ * ⁅x, z⁆ := by
  simp [Bracket.bracket]
  group


-- Lemma 13.30 (3)
lemma comm_prod_right {G: Type*} [Group G] (x y z: G): ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅y, ⁅x, z⁆⁆ * ⁅x, z⁆ := by
  simp [Bracket.bracket]
  group


lemma comm_first_inv {G: Type*} [Group G] (x y: G): ⁅x⁻¹, y⁆ = ⁅x⁻¹, ⁅y, x⁆⁆ * ⁅y, x⁆ := by
  simp [Bracket.bracket]
  group

-- Each element of G can be written as a product of elements of S in at least one way
lemma new_mem_S_prod_list {G: Type*} [Group G] {S: Set G} {x: G} (hx: x ∈ Subgroup.closure S): ∃ l: List ↑(S ∪ S⁻¹), l.unattach.prod = x:= by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  simp at foo
  specialize foo hx
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold List.unattach
  simp [prod_eq]




lemma closure_set_union_normal {G: Type*} [Group G] (S: Set G) (N: Subgroup G) (hN: N.Normal) {x: G} (hx: x ∈ Subgroup.closure (S ∪ N)):
  ∃ a: N, ∃ l: List ↑(S ∪ S⁻¹), x = l.unattach.prod * a := by

  induction hx using Subgroup.closure_induction with
  | one =>
    use 1
    use []
    simp
  | mem y hy =>
    simp at hy
    cases hy
    .
      rename_i y_mem_S
      use 1
      use [⟨y, by simp [y_mem_S]⟩]
      simp
    . rename_i y_mem_N
      use ⟨y, y_mem_N⟩
      use []
      simp
  | mul y z hy hz y_eq z_eq =>
    obtain ⟨a, l, y_eq⟩ := y_eq
    obtain ⟨b, m, z_eq⟩ := z_eq
    simp [y_eq, z_eq]
    group
    use ((m.unattach.prod⁻¹) * a * (m.unattach.prod)⁻¹⁻¹ * b)
    refine ⟨(by
      apply Subgroup.mul_mem
      . apply hN.conj_mem a (by simp)
      . simp
    ), ?_⟩
    use (l ++ m)
    simp
    group
  | inv y hy a_eq =>
    obtain ⟨a, l, y_eq⟩ := a_eq
    use ⟨_, hN.conj_mem a⁻¹ (by simp) l.unattach.prod⟩
    simp
    use (l.map (fun x => ⟨x⁻¹, (by
      simp
      have x_prop := x.prop
      simp [-Subtype.coe_prop] at x_prop
      grind
    )⟩)).reverse
    nth_rw 1 [y_eq]
    simp
    conv =>
      arg 2
      arg 1
      equals l.unattach.prod⁻¹ =>
        rw [List.prod_inv_reverse]
        congr
        ext i g
        simp
    group

#print axioms closure_set_union_normal

-- Lemma 13.44. in https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
-- Note - the book seems to implicitly assume that the generating set is symmetric

set_option maxHeartbeats 400000 in
lemma lower_central_generates_succ {G: Type*} [Group G] (S: Set G) (hS: Subgroup.closure S = ⊤) (n: ℕ):
  lowerCentralSeries G n = Subgroup.closure ((iterate_comm_set (S ∪ S⁻¹) n) ∪ ↑(lowerCentralSeries G (n + 1))) := by
    induction n with
    | zero =>
      simp [iterate_comm_set]
      rw [Subgroup.closure_union]
      rw [Subgroup.closure_union]
      simp [hS]
    | succ n ih =>
      ext a
      refine ⟨?_, ?_⟩
      .
        intro ha
        rw [mem_lowerCentralSeries_succ_iff] at ha
        apply (Subgroup.closure_le _).mp ?_ ha
        simp
        intro p hp
        simp at hp
        obtain ⟨c, c_mem, ⟨g, p_eq_comm⟩⟩ := hp
        rw [← p_eq_comm]
        rw [← commutatorElement_def]
        rw [ih] at c_mem

        have h_c_prod := closure_set_union_normal (S := iterate_comm_set (S ∪ S⁻¹) n) (N := lowerCentralSeries G (n + 1)) (by
          infer_instance
        ) c_mem
        obtain ⟨x, l, c_prod⟩ := h_c_prod
        rw [c_prod]
        rw [comm_prod]

        have x_comm_mem: ⁅x.val, g⁆ ∈ lowerCentralSeries G (n + 1 + 1) := by
          rw [mem_lowerCentralSeries_succ_iff]
          apply Subgroup.mem_closure_of_mem
          simp
          use x
          simp
          use g
          simp [Bracket.bracket]


        apply Subgroup.mul_mem
        . apply Subgroup.mul_mem
          .

            conv =>
              arg 2
              equals l.unattach.prod * ⁅x.val, g⁆ * l.unattach.prod⁻¹ * ⁅x.val, g⁆⁻¹ =>
                simp [Bracket.bracket]


            apply Subgroup.mul_mem
            .
              apply Subgroup.mem_closure_of_mem
              apply Set.mem_union_right
              simp
              apply Subgroup.Normal.conj_mem
              . infer_instance
              . exact x_comm_mem
            .
              apply Subgroup.mem_closure_of_mem
              apply Set.mem_union_right
              simp only [SetLike.mem_coe]
              rw [Subgroup.inv_mem_iff]
              apply x_comm_mem
          .
            apply Subgroup.mem_closure_of_mem
            apply Set.mem_union_right
            simp only [SetLike.mem_coe]
            apply x_comm_mem
        .
          obtain ⟨g_list, g_prod⟩ := new_mem_S_prod_list (S := S) (x := g) (by simp [hS])
          --clear ha a p_eq_comm p c_prod c_mem c x_comm_mem
          rw [← g_prod]
          --clear g_prod g

          by_cases l_len_ne_zero: l.unattach.length = 0
          . have l_empty: l.unattach = [] := by
              exact List.eq_nil_iff_length_eq_zero.mpr l_len_ne_zero
            simp [l_empty]

          by_cases g_len_ne_zero: g_list.unattach.length = 0
          . have g_empty: g_list.unattach = [] := by
              exact List.eq_nil_iff_length_eq_zero.mpr g_len_ne_zero
            simp [g_empty]


          by_cases both_eq_one: g_list.length = 1 ∧ l.unattach.length = 1
          .
            obtain ⟨g_len_one, l_len_one⟩ := both_eq_one
            obtain ⟨g', h_g'⟩ := List.length_eq_one_iff.mp g_len_one
            obtain ⟨l', h_l'⟩ := List.length_eq_one_iff.mp l_len_one

            simp [h_g', h_l']

            conv =>
              arg 2
              arg 1
              equals l'⁻¹⁻¹ => simp

            rw [comm_first_inv]
            simp



            have double_comm_mem {l': G} (l'_mem: l' ∈ ↑(iterate_comm_set (S ∪ S⁻¹) n ∪ (iterate_comm_set (S ∪ S⁻¹) n)⁻¹)): ⁅l'⁻¹, ⁅g'.val, l'⁆⁆ ∈ Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) (n + 1) ∪ ↑(lowerCentralSeries G (n + 1 + 1))) := by
              rw [← Subgroup.inv_mem_iff]
              simp
              apply Subgroup.mem_closure_of_mem
              apply Set.mem_union_right
              simp [mem_lowerCentralSeries_succ_iff]
              apply Subgroup.mem_closure_of_mem
              simp
              use ⁅g'.val, l'⁆
              refine ⟨?_, ?_⟩
              .

                simp
                rw [← Subgroup.inv_mem_iff]
                simp
                apply Subgroup.mem_closure_of_mem
                simp
                use l'
                refine ⟨?_, ?_⟩
                . rw [ih]
                  cases l'_mem
                  .
                    rename_i l'_mem_forward
                    apply Subgroup.mem_closure_of_mem
                    apply Set.mem_union_left
                    exact l'_mem_forward
                  . rename_i l'_mem_inv
                    rw [← Subgroup.closure_inv]
                    apply Subgroup.mem_closure_of_mem
                    simp
                    left
                    exact l'_mem_inv
                .
                  use g'
                  simp [Bracket.bracket]
              .
                use l'⁻¹
                simp [Bracket.bracket]


            have triple_comm_mem {l': G} (l'_mem_comm: l' ∈ iterate_comm_set (S ∪ S⁻¹) n ∨ l'⁻¹ ∈ iterate_comm_set (S ∪ S⁻¹) n):  ⁅l'⁻¹, ⁅g'.val, l'⁆⁆ * ⁅g'.val, l'⁆ ∈  Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) (n + 1) ∪ ↑(lowerCentralSeries G (n + 1 + 1))) := by
              -- have l'_mem: l' ∈ l.unattach := by
              --   simp [h_l']

              -- rw [List.mem_unattach] at l'_mem
              -- obtain ⟨l'_mem_comm, l'_subtype_mem⟩ := l'_mem
              --simp at l'_mem_comm

              have g'_prop := g'.prop
              rw [Set.mem_union] at g'_prop





              cases l'_mem_comm
              .
                rw [← Subgroup.inv_mem_iff]
                simp
                rename_i l'_mem
                . apply Subgroup.mul_mem
                  .
                    apply Subgroup.mem_closure_of_mem
                    apply Set.mem_union_left
                    simp [iterate_comm_set]
                    use g'
                    simp
                    refine ⟨g'_prop, ?_⟩
                    use l'
                  .
                    rw [← Subgroup.inv_mem_iff]
                    simp
                    apply double_comm_mem (by simp [l'_mem])
              .

                rename_i l'_inv_mem
                . apply Subgroup.mul_mem
                  .
                    apply double_comm_mem
                    simp [l'_inv_mem]

                    -- rw [← Set.mem_inv] at l'_inv_mem
                    -- rw [← Subgroup.closure_inv]
                    -- apply Subgroup.mem_closure_of_mem
                    -- rw [Set.union_inv]
                    -- apply Set.mem_union_left
                    -- simp [-Set.mem_inv, iterate_comm_set]
                    -- use g'
                    -- simp [-Set.mem_inv]
                    -- refine ⟨g'_prop, ?_⟩
                    -- use l'
                    -- simp

                  .
                    rw [← Subgroup.inv_mem_iff]
                    simp
                    conv =>
                      arg 2
                      arg 1
                      equals l'⁻¹⁻¹ => simp

                    rw [comm_first_inv]
                    simp
                    apply Subgroup.mul_mem
                    .
                      have foo := double_comm_mem (l' := l'⁻¹ ) (by
                        simp
                        left
                        exact l'_inv_mem
                      )
                      simp at foo
                      exact foo
                    .
                      rw [← Subgroup.inv_mem_iff]
                      simp
                      apply Subgroup.mem_closure_of_mem
                      apply Set.mem_union_left
                      simp [iterate_comm_set]
                      use g'
                      simp at g'_prop
                      simp [g'_prop]
                      use l'⁻¹

            .

              have l'_mem: l' ∈ l.unattach := by
                simp [h_l']

              rw [List.mem_unattach] at l'_mem
              obtain ⟨l'_mem_comm, l'_subtype_mem⟩ := l'_mem
              simp at l'_mem_comm

              have foo := triple_comm_mem (l' := l'⁻¹) (by
                simp
                grind
              )
              simp at foo
              exact foo


          rw [not_and_or] at both_eq_one

          cases both_eq_one
          .
            rename_i g_len_ne
            rw [List.length_unattach] at g_len_ne_zero

            -- have le_g_len: 2 ≤ g_list.unattach.length := by
            --   simp
            --   omega


            clear p_eq_comm x_comm_mem g_prod g g_len_ne g_len_ne_zero

            -- TODO - figure out how to get Nat.le_induction working
            induction h_len: g_list.unattach.length + l.unattach.length using Nat.case_strong_induction_on generalizing g_list with
            | hz =>
              simp at h_len
              obtain ⟨g_list_eq, l_eq⟩ := h_len
              simp [g_list_eq, l_eq]
            | hi k hk =>


              by_cases g_list_zero: g_list.length = 0
              . simp at g_list_zero
                simp [g_list_zero]
              .
                simp at g_list_zero


              -- by_cases l_len_eq: k + 1 ≤ l.unattach.length
              -- .
              --   have prev := hk (l.unattach.length) (by
              --     simp
              --     simp at l_len_eq
              --     omega
              --   )
              --   simp [l_len_eq] at h_len

              --   sorry
              -- .
                simp at h_len
                have g_len_pos: 0 < g_list.length := by
                  by_contra!
                  simp at this
                  contradiction

                rw [← List.take_append_getLast (l := g_list) g_list_zero]
                rw [List.unattach_append]
                simp
                rw [comm_prod_right]
                . apply Subgroup.mul_mem
                  . apply Subgroup.mul_mem
                    .


                      sorry
                    .


                      rw [← Subgroup.inv_mem_iff]
                      simp
                      apply Subgroup.mem_closure_of_mem
                      apply Set.mem_union_right
                      simp
                      rw [mem_lowerCentralSeries_succ_iff]
                      apply Subgroup.mem_closure_of_mem
                      simp
                      use ⁅l.unattach.prod, (g_list.getLast g_list_zero).val⁆
                      refine ⟨?_, ?_⟩
                      .

                        simp [mem_lowerCentralSeries_succ_iff]
                        apply Subgroup.mem_closure_of_mem
                        simp
                        use l.unattach.prod
                        refine ⟨?_, ?_⟩
                        .
                          rw [ih]
                          apply Subgroup.list_prod_mem
                          intro x hx
                          simp at hx
                          obtain ⟨x_mem, x_subtype_mem⟩ := hx
                          cases x_mem
                          . rename_i x_mem_forward
                            apply Subgroup.mem_closure_of_mem
                            grind
                          . rename_i x_mem_inv
                            rw [← Subgroup.closure_inv]
                            apply Subgroup.mem_closure_of_mem
                            simp
                            left
                            exact x_mem_inv
                        .
                          use (g_list.getLast g_list_zero)
                          simp [Bracket.bracket]
                      .
                        use (List.take (g_list.length - 1) g_list).unattach.prod
                        simp [Bracket.bracket]
                  .

                    sorry

                    -- apply Subgroup.mem_closure_of_mem
                    -- apply Set.mem_union_right
                    -- simp
                    -- rw [mem_lowerCentralSeries_succ_iff]
                    -- apply Subgroup.mem_closure_of_mem
                    -- simp
                    -- use l.unattach.prod
                    -- refine ⟨?_, ?_⟩
                    -- .
                    --   apply Subgroup.mem_closure_of_mem
                    --   simp
                    --   rw [ih]

                    --   sorry
                    -- .
                    --  use (g_list.getLast g_len_ne_zero)
                    --  simp [Bracket.bracket]




                    -- apply Subgroup.mem_closure_of_mem
                    -- apply Set.mem_union_right
                    -- simp
                    -- simp [mem_lowerCentralSeries_succ_iff]
                    -- apply Subgroup.mem_closure_of_mem
                    -- simp
                    -- use l.unattach.prod
                    -- refine ⟨?_, ?_⟩
                    -- .
                    --   apply Subgroup.list_prod_mem
                    --   intro x hx
                    --   simp at hx
                    --   apply Subgroup.mem_closure_of_mem
                    --   simp
                    --   rw [ih]

                    -- have prev := hk (l.unattach.length + 1) (by


                    --   rw [Nat.add_one_le_iff]
                    --   have g_len_ne: g_list.length ≠ 0 := by
                    --     simp
                    --     exact g_list_zero

                    --   omega


                    --   linarith
                    -- ) [g_list.getLast g_list_zero] (by simp; linarith)
                    -- simpa using prev
          .
            rename_i l_len
            sorry

      intro ha
      rw [mem_lowerCentralSeries_succ_iff]
      sorry
      --apply Subgroup.mem_closure_of_mem
      --simp

      --sorry


          -- induction h_len: l.unattach.length generalizing l with
          -- | zero =>
          --   simp
          --   conv =>
          --     arg 2
          --     arg 1
          --     equals l.unattach.prod⁻¹⁻¹ => simp


          --   rw [comm_first_inv]
          --   simp

          --   apply Subgroup.mul_mem
          --   . sorry
          --   .
          --     rw [← Subgroup.inv_mem_iff]
          --     simp
          --     apply Subgroup.mem_closure_of_mem
          --     apply Set.mem_union_left
          --     simp [iterate_comm_set]
          --     sorry

          -- | succ n _ => sorry


          -- | nil =>
          --   simp
          -- | cons l_head l_tail l_ih =>
          --   induction g_list.unattach with
          --   | nil =>
          --     simp
          --   | cons g_head g_tail g_ih =>
          --     rw [← List.take_append_getLast (l := l_head :: l_tail) (by simp)]
          --     simp
          --     -- conv =>
          --     --   pattern (l_head :: l_tail).prod
          --     --   equals (l_head :: l_tail.tak)
          --     -- rw [List.prod_append]
          --     -- simp
          --     rw [comm_prod]
          --     apply Subgroup.mul_mem
          --     . apply Subgroup.mul_mem
          --       . sorry
          --       .
          --         sorry
          --     . sorry



      -- .
      --   intro ha
      --   apply (Subgroup.closure_le _).mp ?_ ha
      --   simp
      --   refine ⟨?_, ?_⟩
      --   .
      --     intro b hb
      --     simp [iterate_comm_set] at hb
      --     obtain ⟨s, s_mem, ⟨c, c_mem, c_comm⟩⟩ := hb

      --     have c_mem_lower: c ∈ (lowerCentralSeries G n) := by
      --       rw [ih]
      --       apply Subgroup.mem_closure_of_mem
      --       apply Set.mem_union_left
      --       exact c_mem


      --     apply Subgroup.mem_closure_of_mem
      --     simp
      --     use c
      --     refine ⟨c_mem_lower, ?_⟩
      --     use s
      --   .
      --     intro b hb
      --     have succ_le: lowerCentralSeries G (n + 1 + 1) ≤ lowerCentralSeries G (n + 1) := by
      --       simp [lowerCentralSeries]
      --       apply Subgroup.commutator_le_left


      --     apply succ_le
      --     exact hb


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

lemma normal_comm_mem {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (a b: G) (ha: a ∈ N) :
  ⁅a, b⁆ ∈ N := by

  dsimp [Bracket.bracket]
  have conj_mem := N_normal.conj_mem a⁻¹ (by simp [ha]) b
  conv =>
    arg 2
    equals a * (b * a⁻¹ * b⁻¹) => group

  apply Subgroup.mul_mem
  . exact ha
  . exact conj_mem

open Classical in
def RepeatComm {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (n: ℕ): Set (G''CommData N gamma_alpha) :=
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
  Set.range (fun (g: ↑((N.carrier) ∪ {gamma_alpha})) => G''_comm N_normal gamma_alpha ⁅prev.cur, g⁆ (by

    have g_prop := g.prop
    intro hg
    simp [hg] at g_prop
    have prev_mem := prev.pos_first
    simp at prev_mem
    obtain ⟨prev_cur_mem_N, prev_cur_mem_lower⟩ := prev_mem
    cases g_prop
    .
      rename_i g_eq_gamma
      apply normal_comm_mem N_normal prev.cur
      apply prev_cur_mem_N
    .
      rename_i g_in_N
      simp [Bracket.bracket]
      apply Subgroup.mul_mem
      . apply Subgroup.mul_mem
        . apply Subgroup.mul_mem
          . exact prev_cur_mem_N
          . exact g_in_N
        . simp [prev_cur_mem_N]
      . simp [g_in_N]
  ) prev)
)) (RepeatComm N_normal gamma_alpha n))

lemma RepeatComm_wf {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (n: ℕ):
  ((fun a => a.pos) '' (RepeatComm N_normal gamma_alpha n)).IsWF := by
  apply Set.IsWF.of_wellFoundedLT

lemma RepeatComm_nonempty {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (n: ℕ):
  (RepeatComm N_normal gamma_alpha n).Nonempty := by
  rw [RepeatComm.eq_def]
  split
  . apply Set.range_nonempty
  .
    rename_i j k
    simp
    obtain ⟨a, ha⟩ := RepeatComm_nonempty N_normal gamma_alpha k
    use a
    refine ⟨ha, ?_⟩
    have nonempty_union: Nonempty ↑(N.carrier ∪ {gamma_alpha}) := by
      simp
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


noncomputable def RepeatComm_min {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (n: ℕ) :=
  (RepeatComm_wf N_normal gamma_alpha n).min (by
    simp
    apply RepeatComm_nonempty
  )

lemma RepeatComm_min_strict_mono' {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (n: ℕ):
  (RepeatComm_min N_normal gamma_alpha n) < RepeatComm_min N_normal gamma_alpha (n + 1)  := by
  simp [RepeatComm_min]
  rw [Set.IsWF.lt_min_iff]
  intro a ha
  simp at ha
  obtain ⟨data, data_in, ha_eq⟩ := ha
  simp [RepeatComm] at data_in
  obtain ⟨prev, prev_in, h_prev⟩ := data_in
  obtain ⟨g, ⟨h_eq, prev_eq_data⟩⟩ := h_prev
  rw [← ha_eq]
  rw [← prev_eq_data]
  by_cases min_eq_prev: prev.pos = (RepeatComm_min N_normal gamma_alpha n)
  .
    have min_mem := Set.IsWF.min_mem (RepeatComm_wf N_normal gamma_alpha n) (by
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
    have prev_not_lt := Set.IsWF.not_lt_min (RepeatComm_wf N_normal gamma_alpha n) (by
      simp
      apply RepeatComm_nonempty
    ) (a := prev.pos) (by
      simp
      use prev
    )
    rw [lt_iff_le_and_ne] at prev_not_lt
    simp [min_eq_prev] at prev_not_lt


    have prev_mono := G''_comm_strict_mono N_normal gamma_alpha ⁅prev.cur, g⁆ (by
      intro hg
      apply normal_comm_mem N_normal
      have prev_cur_mem_N := prev.pos_first
      simp at prev_cur_mem_N
      obtain ⟨prev_cur_mem, _⟩ := prev_cur_mem_N
      exact prev_cur_mem
    ) prev
    exact gt_trans prev_mono prev_not_lt

lemma RepeatComm_min_strict_mono {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) :
  StrictMono (fun n => RepeatComm_min N_normal gamma_alpha n) := by
  intro a b ab
  simp
  apply strictMono_of_lt_succ
  .
    intro a _
    apply RepeatComm_min_strict_mono'
  . exact ab



-- lemma iterated_comm_nilpotent {G: Type*} [Group G] (S: Set G) (n: ℕ) (hS: Subgroup.closure (iterate_comm_set S n) = ⊥):
--   lowerCentralSeries (Subgroup.closure S) (n) = ⊥ := by
--   induction n with
--   | zero =>
--     simp [iterate_comm_set] at hS
--     simp

--     by_cases s_empty: S = ∅
--     .
--       have closure_eq: Subgroup.closure S = ⊥ := by
--         simp [s_empty]

--       ext a
--       simp
--       have a_mem := a.property
--       simp [closure_eq] at a_mem
--       exact a_mem
--     .
--       ext a
--       simp
--       have S_eq: S = {1} := by
--         ext a
--         simp
--         grind

--       have a_prop := a.property
--       simp [S_eq] at a_prop
--       rw [Subgroup.closure_singleton_one] at a_prop
--       simp at a_prop
--       exact a_prop
--   | succ n ih =>
--     simp [lowerCentralSeries]
--     simp [iterate_comm_set] at hS
--     ext a
--     simp
--     refine ⟨?_, ?_⟩
--     .
--       intro ha
--       simp at ha
--       rw [Subgroup.commutator_def] at ha

--     . intro ha
--       simp [ha]

-- lemma iterated_comm_generates_lower {G: Type*} [Group G] (S: Set G) (n: ℕ):
--   Subgroup.map (Subgroup.subtype _) (lowerCentralSeries (Subgroup.closure S) n) =  (Subgroup.closure (iterate_comm_set S n)) := by
--   induction n with
--   | zero =>
--     simp [iterate_comm_set]
--     ext a
--     simp
--   | succ n ih =>
--     simp only [lowerCentralSeries]
--     apply_fun (Subgroup.comap (Subgroup.closure S).subtype) at ih
--     rw [Subgroup.comap_map_eq_self_of_injective] at ih
--     .
--       rw [ih]
--       ext a
--       simp
--       refine ⟨?_, ?_⟩
--       . intro ha
--         obtain ⟨a_mem, other⟩ := ha
--         dsimp [Subgroup.commutator] at other
--         have foo := Subgroup.mem_map_of_mem (Subgroup.subtype _) other
--         rw [Subgroup.subtype_apply] at foo
--         simp only [] at foo
--         rw [MonoidHom.map_closure] at foo
--         induction foo using Subgroup.closure_induction with
--         | mem p hp =>
--           simp at hp
--           obtain ⟨p_mem_closure, b, ⟨b_mem, ⟨b_mem_closure, ⟨c, c_mem, comm_eq⟩⟩⟩⟩ := hp

--           simp
--         | one => sorry
--         | mul x y hx hy _ _ => sorry
--         | inv x hx _ => sorry
--     . exact Subgroup.subtype_injective (Subgroup.closure S)
--     simp [lowerCentralSeries, iterate_comm_set]
--     ext a
--     simp
--     refine ⟨?_, ?_⟩
--     .
--       intro hx
--       -- rw [Subgroup.closure_iUnion]
--       obtain ⟨a_mem_closure, a_mem_lower⟩ := hx
--       dsimp [Bracket.bracket] at a_mem_lower
--       have foo := Subgroup.mem_map_of_mem (Subgroup.subtype _) a_mem_lower
--       rw [Subgroup.subtype_apply] at foo
--       simp only [] at foo
--       rw [MonoidHom.map_closure] at foo
--       apply Subgroup.closure_induction (p := fun g hg => g ∈ Subgroup.closure (⋃ i ∈ S, (fun a ↦ ⁅a, i⁆) '' iterate_comm_set S n)) (hx := foo)
--       .
--         intro g hg
--         simp at hg
--         obtain ⟨g_mem_closure, a, ⟨a_mem_closure, a_mem_lower, ⟨b, b_mem_closure, g_eq_comm⟩⟩⟩ := hg
--         apply Subgroup.mem_closure_of_mem
--         simp

--     . sorry


lemma nilpotent_of_comm_trivial {G: Type*} [Group G] (S: Set G) (n: ℕ) (hS: iterate_comm_set S n = {1}):
  ∃ k: ℕ, lowerCentralSeries (Subgroup.closure S) k = ⊥ := by
  induction n with
  | zero =>
    use 0
    simp
    simp [iterate_comm_set] at hS
    ext a
    simp
    have closure_eq: Subgroup.closure S = Subgroup.closure {1} := by
      rw [hS]

    simp at closure_eq
    rw [Subgroup.closure_singleton_one] at closure_eq
    have a_mem := a.property
    simp_rw [closure_eq] at a_mem
    simp at a_mem
    exact a_mem
  | succ n ih =>
    simp [iterate_comm_set] at hS

    sorry

lemma RepeatComm_eventually_le {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (a b: ℕ):
  ∃ n: ℕ, a ≤ (RepeatComm_min N_normal gamma_alpha n).fst ∨ b ≤ (RepeatComm_min N_normal gamma_alpha n).snd := by

  have unbounded := prod_lex_has_unbounded (RepeatComm_min_strict_mono N_normal gamma_alpha)
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


-- This probably needs the semidirect productff
lemma closure_mem_repeatComm {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (n: ℕ):
  ∀ g ∈ { x | ∃ p ∈ lowerCentralSeries (Subgroup.closure ↑(N.carrier ∪ {gamma_alpha})) (n), ∃ q, x = ⁅p.val, q⁆ }, ∃ data ∈ RepeatComm N_normal gamma_alpha (n + 1), g = data.cur := by

    intro g g_mem
    induction n with
    | zero =>
      simp at g_mem
      obtain ⟨p, p_in, q, g_eq⟩ := g_mem
      simp [RepeatComm]

      use {
        cur := p
        pos := (0, 0)
        pos_first := by
          simp [lowerCentralSeries]
        pos_second := by
          simp
      }
      have g_prop := g.property
      apply Subgroup.closure_induction (p := fun g hg => ∃ data ∈ RepeatComm N_normal gamma_alpha (0 + 1), g = data.cur) (k := N.carrier ∪ {gamma_alpha}) g_mem
      .
        rw [RepeatComm]
        use {
          cur := 1
          pos := (1, 0)
          pos_first := by
            simp [lowerCentralSeries]
          pos_second := by
            simp
        }
        rw [Set.mem_sUnion]
        refine ⟨?_, by simp⟩
        simp
        use {
          cur := 1
          pos := (0, 0)
          pos_first := by
            simp [lowerCentralSeries]
          pos_second := by
            simp
        }
        simp [RepeatComm]
        use 1
        use (by simp)
        simp [G''_comm]
        -- TODO - take this as a hypothesis
        have gamma_alpha_ne_one: 1 ≠ gamma_alpha := by
          sorry
        simp [gamma_alpha_ne_one]
      .
        intro x y hx hy x_cur y_cur
        rw [RepeatComm] at x_cur
        rw [RepeatComm] at y_cur
        obtain ⟨x_data, x_data_in, x_eq⟩ := x_cur
        obtain ⟨y_data, y_data_in, y_eq⟩ := y_cur

        simp [RepeatComm]


      simp at g_mem
      simp [RepeatComm]
      use {
        cur := g
        pos := (0, 0)
        pos_first := by
          simp [lowerCentralSeries]
        pos_second := by
          simp
      }


    | succ k ih =>
      sorry



-- OLD

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
