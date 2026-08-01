import Mathlib
import Gromov.ToMathlib.GroupTheory.FiniteAbelian.Basic
import Gromov.MatrixSubsum
import Gromov.AbelianFg
import Gromov.ToMathlib.GroupTheory.Closure
import Gromov.ToMathlib.GroupTheory.Nilpotent
import Gromov.ToMathlib.Data.List.Infix
import Gromov.ToMathlib.Order.Prod.Lex

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise


def iteratedCommutator {T: Type*} [Group T] (base right: T) (n: ℕ) := Nat.iterate (fun x => ⁅x, right⁆) n base


def iterate_comm_set {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (n: ℕ): Finset G :=
  match n with
  | 0 => S
  | n + 1 => Finset.biUnion S (fun s => Finset.image (fun g => ⁅g, s⁆) (iterate_comm_set S n))


lemma iterate_comm_set_eq_fold {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (n: ℕ):
    iterate_comm_set S n = { g | ∃ s: S, ∃ l: List S, l.length = n ∧ (l.unattach.foldr (fun acc s => ⁅s, acc⁆) s.val) = g } := by

  induction n with
  | zero =>
    simp [iterate_comm_set]
  | succ n ih =>
    simp [iterate_comm_set]
    ext g
    simp
    refine ⟨?_, ?_⟩
    .
      intro h
      obtain ⟨s, s_mem, ⟨x, x_mem, comm_eq⟩⟩ := h
      rw [← Finset.mem_coe] at x_mem
      rw [ih] at x_mem
      simp at x_mem
      obtain ⟨t, t_mem, l, l_len, l_fold_eq⟩ := x_mem
      use t
      refine ⟨t_mem, ?_⟩
      use (⟨s, s_mem⟩ :: l)
      refine ⟨?_, ?_⟩
      . grind
      .
        simp
        rw [← comm_eq]
        rw [← l_fold_eq]
    .
      intro h
      obtain ⟨t, t_mem, l, l_len, l_fold_eq⟩ := h
      have l_len_eq := l_len
      apply List.exists_cons_of_length_eq_add_one at l_len

      obtain ⟨head, tail, l_eq⟩ := l_len
      rw [l_eq] at l_fold_eq
      simp at l_fold_eq

      use head
      refine ⟨by simp, ?_⟩
      simp at ih



      have tail_len_eq: tail.length = n := by
        rw [l_eq] at l_len_eq
        simp at l_len_eq
        exact l_len_eq


      use List.foldr (fun x b ↦ ⁅b, x⁆) t tail.unattach
      refine ⟨?_, ?_⟩
      .
        rw [← Finset.mem_coe]
        rw [ih]
        simp
        use t
        refine ⟨t_mem, ?_⟩
        use tail
      . exact l_fold_eq

#print axioms iterate_comm_set_eq_fold

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




lemma double_comm_mem {G: Type*}  [DecidableEq G] [Group G] (S: Finset G) {l': G} (n: ℕ) (ih: (⊤ : Subgroup G).lowerCentralSeries n = Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) n ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1)))) (g': ↑(S ∪ S⁻¹))  (l'_mem: l' ∈ ↑(iterate_comm_set (S ∪ S⁻¹) n ∪ (iterate_comm_set (S ∪ S⁻¹) n)⁻¹)): ⁅l'⁻¹, ⁅g'.val, l'⁆⁆ ∈ Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) (n + 1) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1))) := by
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

    rw [← Subgroup.inv_mem_iff]
    simp
    apply Subgroup.mem_closure_of_mem
    simp
    use l'
    refine ⟨?_, ?_⟩
    . rw [ih]
      simp at l'_mem
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
  .
    use l'⁻¹



set_option maxHeartbeats 400000 in
lemma triple_comm_mem {G: Type*} [Group G] [DecidableEq G] (S: Finset G) {l': G} (n: ℕ) (ih: (⊤ : Subgroup G).lowerCentralSeries n = Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) n ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1)))) (g': ↑(S ∪ S⁻¹))   (l'_mem_comm: l' ∈ iterate_comm_set (S ∪ S⁻¹) n ∨ l'⁻¹ ∈ iterate_comm_set (S ∪ S⁻¹) n):  ⁅l'⁻¹, ⁅g'.val, l'⁆⁆ * ⁅g'.val, l'⁆ ∈  Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) (n + 1) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1))) := by
  -- have l'_mem: l' ∈ l.unattach := by
  --   simp [h_l']

  -- rw [List.mem_unattach] at l'_mem
  -- obtain ⟨l'_mem_comm, l'_subtype_mem⟩ := l'_mem
  --simp at l'_mem_comm

  have g'_prop := g'.prop
  rw [Finset.mem_union] at g'_prop





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
        refine ⟨by simpa using g'_prop, ?_⟩
        use l'
      .
        rw [← Subgroup.inv_mem_iff]
        simp
        apply double_comm_mem
        . exact ih
        . simp [l'_mem]

  .

    rename_i l'_inv_mem
    . apply Subgroup.mul_mem
      .
        apply double_comm_mem
        exact ih
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
          have foo := double_comm_mem (l' := l'⁻¹ ) _ _ ih g' (by
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


#print axioms triple_comm_mem
-- Lemma 13.44. in https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
-- Note - the book seems to implicitly assume that the generating set is symmetric

set_option maxHeartbeats 400000 in
lemma lower_central_generates_succ {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ):
  (⊤ : Subgroup G).lowerCentralSeries n = Subgroup.closure ((iterate_comm_set (S ∪ S⁻¹) n) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1))) := by
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
        rw [ih] at c_mem

        have h_c_prod := closure_set_union_normal (S := iterate_comm_set (S ∪ S⁻¹) n) (N := (⊤ : Subgroup G).lowerCentralSeries (n + 1)) (by
          infer_instance
        ) c_mem
        obtain ⟨x, l, c_prod⟩ := h_c_prod
        rw [c_prod]
        rw [comm_prod]

        have x_comm_mem: ⁅x.val, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1) := by
          rw [mem_lowerCentralSeries_succ_iff]
          apply Subgroup.mem_closure_of_mem
          simp
          use x
          exact ⟨x.2, g, rfl⟩


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
          clear g_prod c_prod


          -- TODO - figure out how to get Nat.le_induction working
          induction h_len: g_list.unattach.length + l.unattach.length using Nat.case_strong_induction_on generalizing g_list l with
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


              by_cases l_len_ne_zero: l.unattach.length = 0
              . have l_empty: l.unattach = [] := by
                  exact List.eq_nil_iff_length_eq_zero.mpr l_len_ne_zero
                simp [l_empty]


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


                have l'_mem: l' ∈ l.unattach := by
                  simp [h_l']

                rw [List.mem_unattach] at l'_mem
                obtain ⟨l'_mem_comm, l'_subtype_mem⟩ := l'_mem
                simp at l'_mem_comm

                rw [comm_first_inv]
                simp
                have foo := triple_comm_mem (l' := l'⁻¹) _ _ ih ⟨g', by (
                  have foo := g'.prop
                  simp [-Subtype.coe_prop] at foo
                  simp
                  exact foo
                )⟩  (by
                  simp
                  grind
                )
                simp at foo
                exact foo


              rw [not_and_or] at both_eq_one
              cases both_eq_one
              . rename_i g_len_ne_one

                have g_len_ne_zero: g_list.length ≠ 0 := by
                  simp
                  exact g_list_zero
                have two_le_g_len: 2 ≤ g_list.length := by
                  omega

                clear g_len_ne_one g_len_ne_zero
                simp at h_len



                rw [← List.take_append_getLast (l := g_list) (g_list_zero)]
                rw [List.unattach_append]
                simp
                rw [comm_prod_right]
                . apply Subgroup.mul_mem
                  . apply Subgroup.mul_mem
                    .

                      have prev := hk k (by simp) l (List.take (g_list.length - 1) g_list) (by
                        simp
                        omega
                      )
                      exact prev
                    .


                      rw [← Subgroup.inv_mem_iff]
                      simp
                      apply Subgroup.mem_closure_of_mem
                      apply Set.mem_union_right
                      simp only [SetLike.mem_coe]
                      have l_prod_mem : l.unattach.prod ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
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
                      exact Subgroup.commutator_mem_commutator
                        (Subgroup.commutator_mem_commutator l_prod_mem (Subgroup.mem_top _))
                        (Subgroup.mem_top _)
                  .

                    have prev := hk (l.length + 1) (by omega) l [(g_list.getLast g_list_zero)] (by
                      simp
                      omega
                    )
                    simp at prev
                    exact prev

              .
                rename_i l_len_ne_one
                simp at l_len_ne_one
                have l_ne_zero: l.length ≠ 0 := by
                  rw [List.length_unattach] at l_len_ne_zero
                  exact l_len_ne_zero

                simp [-List.length_eq_zero_iff] at l_ne_zero
                have two_le_l_len: 2 ≤ l.length := by
                  omega

                rw [← List.take_append_getLast (l := l) (by simpa using l_ne_zero)]
                rw [List.unattach_append]
                simp
                rw [comm_prod]
                simp at h_len
                apply Subgroup.mul_mem
                . apply Subgroup.mul_mem
                  .
                    rw [← Subgroup.inv_mem_iff]
                    simp
                    apply Subgroup.mem_closure_of_mem
                    apply Set.mem_union_right
                    simp only [SetLike.mem_coe]
                    have last_mem : (l.getLast (by simpa using l_ne_zero)).val ∈
                        (⊤ : Subgroup G).lowerCentralSeries n := by
                      rw [ih]
                      have l_prop := (l.getLast (by simpa using l_ne_zero)).prop
                      rw [Set.mem_union] at l_prop
                      cases l_prop
                      . rename_i l_prop_forward
                        apply Subgroup.mem_closure_of_mem
                        grind
                      . rename_i l_prop_inv
                        rw [← Subgroup.closure_inv]
                        simp
                        apply Subgroup.mem_closure_of_mem
                        grind
                    exact Subgroup.commutator_mem_commutator
                      (Subgroup.commutator_mem_commutator last_mem (Subgroup.mem_top _))
                      (Subgroup.mem_top _)
                  .

                    have foo := hk (g_list.length + 1) (by omega) [l.getLast (by simpa using l_ne_zero)] g_list (by simp)
                    simp at foo
                    exact foo
                .
                  have foo := hk k (by simp) (List.take (l.length - 1) l) g_list (by
                    simp
                    omega
                  )
                  exact foo

      intro ha
      rw [mem_lowerCentralSeries_succ_iff]


      have closure_le: (Subgroup.closure ((iterate_comm_set (S ∪ S⁻¹) (n + 1)) ∪ ↑((⊤ : Subgroup G).lowerCentralSeries (n + 1 + 1)))) ≤ (Subgroup.closure {x | ∃ p ∈ (⊤ : Subgroup G).lowerCentralSeries n, ∃ q ∈ (⊤ : Subgroup G), ⁅p, q⁆ = x}) := by
        rw [Subgroup.closure_le]
        intro x hx
        simp at hx
        cases hx
        .
          rename_i x_mem_comm
          apply Subgroup.mem_closure_of_mem
          simp
          rw [ih]
          simp [iterate_comm_set] at x_mem_comm
          obtain ⟨s, s_mem, ⟨c, c_mem, c_comm⟩⟩ := x_mem_comm
          use c
          refine ⟨?_, ?_⟩
          . apply Subgroup.mem_closure_of_mem
            grind
          . use s
        .
          rename_i x_mem_lower_two
          have x_mem_lower_succ: x ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1) :=
            Subgroup.commutator_le_left _ _ x_mem_lower_two


          rw [mem_lowerCentralSeries_succ_iff] at x_mem_lower_succ
          simpa using x_mem_lower_succ



      apply closure_le ha

#print axioms lower_central_generates_succ

-- Corollary 13.45
-- TODO - we might not actually need this from Gromov. Also, it's unclear whether 'k' is fixed, or if we need to take a union over all k ≥ n
lemma nilpotent_comm_generates {G: Type*} [Group G] [DecidableEq G] [Group.IsNilpotent G] (S: Finset G) (hS: Subgroup.closure (S: Set G) = ⊤) (n k: ℕ) (hn: n ≤ k):
  (⊤ : Subgroup G).lowerCentralSeries k = Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) k) := by

  by_cases class_zero: Group.nilpotencyClass G = 0
  .
    rw [nilpotencyClass_zero_iff_subsingleton] at class_zero

    have unique_subgroup: Unique (Subgroup G) := by infer_instance

    -- TODO - what's the right way to apply Unique?
    rw [unique_subgroup.eq_default ((⊤ : Subgroup G).lowerCentralSeries k)]
    rw [unique_subgroup.eq_default (Subgroup.closure (iterate_comm_set (S ∪ S⁻¹) k))]
  .




    by_cases class_sub_le: (Group.nilpotencyClass G) - 1 ≤ k
    .
      induction k, class_sub_le using Nat.le_induction generalizing n with
      | base =>
        have succ_add_eq: Group.nilpotencyClass G = (Group.nilpotencyClass G) - 1 + 1 := by
          omega

        rw [lower_central_generates_succ S hS]
        rw [← succ_add_eq]
        simp
      | succ m hmn ih =>
        apply Nat.le_add_of_sub_le at hmn
        rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le] at hmn
        rw [hmn]

        have foo := lower_central_generates_succ S hS (m + 1)
        rw [hmn] at foo

        rw [eq_comm]
        rw [← le_bot_iff]
        rw [foo]
        simp
        intro a ha
        apply Subgroup.mem_closure_of_mem
        grind
    .
      simp at class_sub_le
      rw [Nat.add_lt_iff_lt_sub_right] at class_sub_le
      apply Nat.le_of_lt at class_sub_le
      induction class_sub_le using Nat.decreasingInduction generalizing n with
      | of_succ k h ih =>
        rw [lower_central_generates_succ S hS]
        rw [ih (k + 1) (by simp)]
        rw [Subgroup.closure_union]
        rw [Subgroup.closure_eq]
        simp
        intro a ha
        simp [iterate_comm_set] at ha
        obtain ⟨s, s_mem, ⟨c, c_mem, c_comm⟩⟩ := ha
        sorry


      --   rw [← ih (k + 1) (by simp)]

      --   have le_nilotency: k + 1 ≤ Group.nilpotencyClass G := by
      --     omega

      --   rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le] at le_nilotency



      --   sorry
      | self =>
        -- TODO - deduplicate this
        have succ_add_eq: Group.nilpotencyClass G = (Group.nilpotencyClass G) - 1 + 1 := by
          omega

        rw [lower_central_generates_succ S hS]
        rw [← succ_add_eq]
        simp


  --   by_cases k_succ_eq_class: k + 1 = Group.nilpotencyClass G
  --   .
  --     rw [lower_central_generates_succ S hS]
  --     rw [k_succ_eq_class]
  --     simp
  --   .
  --     by_cases k_ge: Group.nilpotencyClass G < k + 1


  -- match k with
  -- | 0 =>
  --   simp [iterate_comm_set]
  --   rw [Subgroup.closure_union]
  --   simp [hS]
  -- | m + 1 =>
  --   by_cases m_eq: m = Group.nilpotencyClass G
  --   .
  --     simp [lowerCentralSeries]
  --     rw [m_eq]
  --     simp

  --   by_cases class_le_k: Group.nilpotencyClass G ≤ (m + 1)
  --   .

  --     simp [lowerCentralSeries]
  --     rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le] at class_le_k
  --     rw [lower_central_generates_succ S hS] at class_le_k
  --     simp [class_le_k]

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)


-- https://math.stackexchange.com/questions/4995327/group-in-the-lower-central-series-is-generated-by-conjugates-of-comutators-of-ge
lemma iterate_comm_generates (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ):
  (Subgroup.normalClosure (iterate_comm_set (S) n)) = (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    simp [iterate_comm_set]

    have closure_le: ⊤ ≤ Subgroup.closure (S : Set G) := by
      simp [hS]


    rw [eq_top_iff]
    grw [closure_le]
    apply Subgroup.closure_le_normalClosure
  | succ n ih =>
    simp [lowerCentralSeries]
    rw [le_antisymm_iff]
    refine ⟨?_, ?_⟩
    .
      simp [Subgroup.normalClosure]
      intro y hy
      simp [Group.conjugatesOfSet, iterate_comm_set] at hy
      obtain ⟨s, s_mem, ⟨c, c_mem, c_comm⟩⟩ := hy
      simp [conjugatesOf] at c_comm
      obtain ⟨x, x_mem⟩ := c_comm
      rw [← x_mem]
      apply Subgroup.Normal.conj_mem
      . infer_instance
      .
        apply Subgroup.commutator_mem_commutator
        .
          rw [← ih]
          apply Subgroup.mem_closure_of_mem
          simp [Group.conjugatesOfSet]
          use c
          refine ⟨c_mem, ?_⟩
          simp [conjugatesOf]
          use 1
          simp
        . simp
    .

      have image_commute: ∀ s ∈ S, ∀ g ∈ (iterate_comm_set (S) n), QuotientGroup.mk' (((Subgroup.normalClosure (iterate_comm_set (S) (n + 1))))) (s * g) = QuotientGroup.mk' (((Subgroup.normalClosure (iterate_comm_set (S) (n + 1))))) (g * s) := by
        intro s hs g hg
        simp
        rw [← QuotientGroup.mk_mul]
        rw [← QuotientGroup.mk_mul]
        rw [QuotientGroup.eq]
        simp [Subgroup.normalClosure]
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← Subgroup.closure_inv]
        apply Subgroup.mem_closure_of_mem
        simp [-Set.mem_inv, Group.conjugatesOfSet]
        simp only [conjugatesOf]
        use g * s * g⁻¹ * s⁻¹
        refine ⟨?_, ?_⟩
        . simp [iterate_comm_set]
          use s
          refine ⟨by simp [hs], ?_⟩
          use g
          refine ⟨hg, ?_⟩
          simp [Bracket.bracket]
        .
          simp
          use s⁻¹ * g⁻¹
          group

      have comm_subset_center: (QuotientGroup.mk' _) '' (iterate_comm_set (S) n) ⊆ ((Subgroup.center (G ⧸ ((Subgroup.normalClosure (iterate_comm_set (S) (n + 1)))))).carrier) := by
        intro x hx
        simp at hx
        obtain ⟨a, a_mem, hx⟩ := hx
        rw [Subgroup.mem_carrier]
        rw [Subgroup.mem_center_iff]
        intro b
        rw [← QuotientGroup.out_eq' (a := b)]
        rw [← hx]
        rw [← QuotientGroup.mk_mul]
        rw [← QuotientGroup.mk_mul]
        rw [QuotientGroup.eq]
        simp


        have b_mem_top: Quotient.out b ∈ (⊤ : (Subgroup G)) := by
          simp

        rw [← hS] at b_mem_top

        -- TODO - figure out how to get the 'induction' tactic working here
        apply Subgroup.closure_induction (p := fun y hy => a⁻¹ * y⁻¹ * (a * y) ∈ Subgroup.normalClosure (iterate_comm_set (S) (n + 1))) (hx := b_mem_top)
        .
          intro s hs
          have comm := image_commute s hs a a_mem
          simp at comm
          rw [← QuotientGroup.mk_mul] at comm
          rw [← QuotientGroup.mk_mul] at comm
          rw [QuotientGroup.eq] at comm
          simp at comm
          exact comm
        . simp
        . intro y hy z hz y_mem z_mem
          simp
          conv =>
            arg 2
            equals (a⁻¹ * hy⁻¹ * a * hy) * (hy⁻¹ * a⁻¹ * y⁻¹ * a * y * hy) =>
              group
          apply Subgroup.mul_mem
          . group
            group at z_mem
            exact z_mem
          .
            have foo := (Subgroup.normalClosure_normal).conj_mem _ y_mem hy⁻¹
            simp at foo
            group at foo
            group
            exact foo
        .
          intro y hy y_mem
          rw [← Subgroup.inv_mem_iff]
          simp
          have foo := (Subgroup.normalClosure_normal).conj_mem _ y_mem y
          group at foo
          group
          exact foo


      simp [Bracket.bracket]
      intro g hg
      simp at hg
      obtain ⟨a, a_mem, b, g_eq⟩ := hg
      have normal_le_center := Subgroup.normalClosure_le_normal comm_subset_center
      rw [← Subgroup.map_normalClosure] at normal_le_center
      rw [ih] at normal_le_center
      simp
      have a_mem_center := @normal_le_center a⁻¹ ?_
      .
        rw [Subgroup.mem_center_iff] at a_mem_center
        specialize a_mem_center (QuotientGroup.mk b⁻¹)
        rw [← QuotientGroup.mk_inv] at a_mem_center
        rw [← QuotientGroup.mk_mul] at a_mem_center
        rw [← QuotientGroup.mk_mul] at a_mem_center
        rw [QuotientGroup.eq] at a_mem_center
        simp at a_mem_center
        rw [← g_eq]
        group at a_mem_center
        group
        exact a_mem_center
      . simp
        use a



      simp
      exact QuotientGroup.mk_surjective

#print axioms iterate_comm_generates

-- Lemma 13.55 from https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
lemma comm_trivial_implies_nilpotent {G: Type*} [DecidableEq G] [Group G] (S: Finset G) (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ) (h_comm: iterate_comm_set (S) (n) = {1}):
    (⊤ : Subgroup G).lowerCentralSeries n = ⊥ := by

  rw [← iterate_comm_generates S hS n]
  rw [h_comm]
  simp [Subgroup.normalClosure]
  intro g hg
  simp [Group.conjugatesOfSet, conjugatesOf] at hg
  exact hg


structure G''CommData {T: Type*} [Group T] (N: Subgroup T) (gamma_alpha: T) where
  -- The result of repeatedly applying commutators
  cur: T

  -- When we take a commutator, we increment the second component if we take a commutator with 'right',
  -- and reset it to zero and increment the first component if we take a commutator with anything else
  -- As a result, 'pos' strictly increases at each step
  pos: Lex (ℕ × ℕ)
  -- The first component of our position is our index in the lower central series of M
  pos_first: cur ∈ Subgroup.lowerCentralSeries N pos.1
  -- The second component is the number of copies of 'right' that occur in successive adjacent commutators
  pos_second: pos.2 ≠ 0 → ∃ b: T, cur = iteratedCommutator b gamma_alpha pos.2


--set_option trace.profiler true

--set_option Elab.async false
--set_option trace.Meta.Tactic.simp true in
--set_option trace.Meta.Tactic.simp.numSteps true in
--set_option trace.Elab.command true in
--open Classical in

-- TODO - upstream to mathlib
instance lower_central_characteristic {G: Type*} [Group G] (n: ℕ): ((⊤ : Subgroup G).lowerCentralSeries n).Characteristic := by
  induction n with
  | zero =>
    simp
    infer_instance
  | succ n ih =>
    infer_instance





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
      simp only [next_eq_gamma, if_true]
      have prev_cur_mem := prev.pos_first

      have map_normal: (Subgroup.lowerCentralSeries N prev.pos.1).Normal := by
        infer_instance

      have map_conj := map_normal.conj_mem prev.cur⁻¹ (by exact
        (Subgroup.inv_mem_iff (Subgroup.lowerCentralSeries N prev.pos.1)).mpr prev_cur_mem)
        gamma_alpha

      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact Subgroup.mul_mem _ prev_cur_mem (by rwa [← mul_assoc])
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

      simp only [cur_neq, if_false]
      exact Subgroup.commutator_mem_commutator prev.pos_first h_cur_neq
  pos_second := by
    split_ifs
    . rename_i cur_eq
      simp only [cur_eq, if_true]
      show prev.pos.2 + 1 ≠ 0 → ∃ b : T,
        ⁅prev.cur, gamma_alpha⁆ = iteratedCommutator b gamma_alpha (prev.pos.2 + 1)
      intro _
      unfold iteratedCommutator
      have prev_val := prev.pos_second
      match h_pos: prev.pos.2 with
      | 0 =>
        use prev.cur
        simp
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
        rw [Function.iterate_succ']
        simp
    . rename_i cur_neq
      simp only [cur_neq, if_false]
      simp
}

-- TODO ' add simp lemma to avoid the need for all of the 'conv' steps, and upstream to mathlib
lemma G''_comm_strict_mono {T: Type*} [Group T] {N: Subgroup T} (N_normal: N.Normal) (gamma_alpha cur: T) (h_cur: cur ≠ gamma_alpha → cur ∈ N) (prev: G''CommData N gamma_alpha):
  prev.pos < (G''_comm N_normal gamma_alpha cur h_cur prev).pos := by

  by_cases h : cur = gamma_alpha
  . have hpos : (G''_comm N_normal gamma_alpha cur h_cur prev).pos
        = toLex (prev.pos.1, prev.pos.2 + 1) := if_pos h
    rw [hpos, Prod.Lex.lt_iff]
    exact Or.inr ⟨rfl, Nat.lt_succ_self _⟩
  . have hpos : (G''_comm N_normal gamma_alpha cur h_cur prev).pos
        = toLex (prev.pos.1 + 1, 0) := if_neg h
    rw [hpos, Prod.Lex.lt_iff]
    exact Or.inl (Nat.lt_succ_self _)
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

-- lemma mulequiv_pow {G: Type*} [CommGroup G] (f: G ≃* G) (a: G) (n: ℕ) (hn: 0 ≠ n): (f^n).toMonoidHom a = (f.toMonoidHom a)^n := by
--   induction n with
--   | zero =>
--     simp at hn
--   | succ n ih =>
--     simp
--     rw [pow_succ']
--     simp
--     rw [pow_succ']
--     rw [pow_succ]

--     conv =>
--       lhs
--       lhs
--       equals (f.toMonoidHom) ^n =>
--         rfl

-- FALSE - counterexample is Z × (ℤ mod 2)
-- https://gemini.google.com/app/e28d0a7ce053d1e0
-- def mulaut_prod_torsionfree {A B: Type*} [Group A] [Group B] (ha: IsMulTorsionFree A): MulAut (A × B) ≃ MulAut A × MulAut B := {
--   toFun := fun a => (
--     {
--       toFun := fun g => (a (g, 1)).fst
--       invFun := fun g => (a.symm (g, 1)).fst
--       map_mul' := by
--         intro x y

--         have maps_one: ∀ x : A, a (x, 1) = ((a (x, 1)).1, 1) := by
--           intro z
--           by_cases z_eq: z = 1
--           .
--             simp [z_eq_one]
--             conv =>
--               rhs
--               arg 1
--               arg 1
--               arg 2
--               equals 1 => simp
--             simp
--             conv =>
--               lhs
--               arg 2
--               equals 1 => simp
--             simp
--             rfl
--           .
--             have order_eq := MulEquiv.orderOf_eq a (z, 1)
--             nth_rw 2 [Prod.orderOf] at order_eq
--             conv at order_eq =>
--               arg 2
--               arg 1
--               equals 0 =>
--                 simp
--                 apply not_isOfFinOrder_of_isMulTorsionFree z_eq
--             simp only [-MulEquiv.orderOf_eq, orderOf_one, Nat.lcm_one_right] at order_eq

--         simp [-MulEquiv.orderOf_eq] at order_eq
--       left_inv := sorry
--       right_inv := sorry
--     },
--     {
--       toFun := fun g => sorry
--       invFun := fun g => sorry
--       map_mul' := sorry
--       left_inv := sorry
--       right_inv := sorry
--     }
--   )
--   invFun := fun a => {
--     toFun := fun g => (a.1 g.1, a.2 g.2)
--     invFun := fun g => (a.1.symm g.1, a.2.symm g.2)
--     map_mul' := by
--       intro x y
--       simp
--     left_inv := by
--       intro a
--       simp
--     right_inv := by
--       intro b
--       simp
--   }
-- }

-- TODO - cleanup and upstream to mathlib
instance torsion_characteristic {G: Type*} [CommGroup G]: (CommGroup.torsion G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_map]
  intro f g hg
  simp
  rw [CommGroup.mem_torsion] at hg
  use (f.symm.toMonoidHom g)
  refine ⟨?_, by simp⟩
  rw [CommGroup.mem_torsion]
  apply MonoidHom.isOfFinOrder
  exact hg

-- TODO - generalize and upstream to mathlib
lemma eigen_one_unipotent {A: Type*}  [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A] (f: Module.End ℂ A) (hf: ∀ k : Module.End.Eigenvalues f, k.val = 1): ∃ n, (f - 1)^n = 0 := by

  have charpoly_mono: ∀ x ∈ f.charpoly.roots, x = 1 := by
    intro x hx
    have x_root: f.charpoly.IsRoot x := by
      exact Polynomial.isRoot_of_mem_roots hx

    apply hasEigenvalue_of_isRoot_charpoly at x_root
    specialize hf ⟨x, x_root⟩
    simp [Module.End.Eigenvalues.val, Module.End.UnifEigenvalues.val] at hf
    exact hf

  have charpoly_roots: f.charpoly.roots = Multiset.replicate f.charpoly.natDegree 1 := by
    rw [Multiset.ext]
    intro x
    rw [Multiset.count_replicate]
    by_cases x_eq_one: 1 = x
    .
      simp [-Polynomial.count_roots, x_eq_one]
      conv =>
        arg 1
        equals f.charpoly.roots.card =>
          rw [Multiset.count_eq_card]
          simp_rw [← x_eq_one, eq_comm]
          exact charpoly_mono

      exact IsAlgClosed.card_roots_eq_natDegree
    .
      simp only [x_eq_one]
      simp only [↓reduceIte]
      simp
      intro hx
      rw [← Polynomial.IsRoot.def] at hx
      rw [← Polynomial.mem_roots] at hx
      .
        specialize charpoly_mono _ hx
        grind
      .
        by_contra!
        have foo := LinearMap.charpoly_natDegree f
        have monic := LinearMap.charpoly_monic f
        simp [this] at monic






  have monic: f.charpoly.Monic := by exact LinearMap.charpoly_monic f
  have foo := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq monic (by exact
    IsAlgClosed.card_roots_eq_natDegree)

  rw [charpoly_roots] at foo
  simp at foo

  have f_eval := LinearMap.aeval_self_charpoly f
  rw [← foo] at f_eval
  simp at f_eval
  use f.charpoly.natDegree



def iteratedCommutatorNormal {T: Type*} [Group T] {N: Subgroup T} [hN: N.Normal] (base: N) (right: T) (n: ℕ) := Nat.iterate (fun x => ⟨⁅x.val, right⁆, (by
  apply normal_comm_mem hN
  simp
)⟩) n base

lemma iterated_comm_normal_eq_iterated {T: Type*} [Group T] {N: Subgroup T} [hN: N.Normal] (base: N) (right: T) (n: ℕ):
    (iteratedCommutatorNormal base right n).val = iteratedCommutator base.val right n := by

  induction n with
  | zero =>
    simp [iteratedCommutatorNormal, iteratedCommutator]
  | succ n ih =>
    simp only [iteratedCommutatorNormal, iteratedCommutator]
    simp only [iteratedCommutatorNormal, iteratedCommutator] at ih
    rw [Function.iterate_succ']
    rw [Function.iterate_succ']
    simp
    rw [ih]


-- TODO - upstream to mathlib
instance subgroup_map_finite {A B: Type*} [Group A] [Group B] (f: A →* B) (G: Subgroup A) [Finite G]: Finite (Subgroup.map f G) := by
  have foo: (Subgroup.map f G) ≃ (Set.image f G.carrier) := {
    toFun := fun a => a
    invFun := fun a => a
  }
  rw [Equiv.finite_iff foo]
  rw [Set.finite_coe_iff]
  apply Finite.Set.finite_image

-- TODO - generalize and pr to mathlib
lemma matrix_map_pow  {n : Type*} {α : Type*} {β : Type*} [CommSemiring α] [Fintype n] [DecidableEq n] {L : Matrix n n α} [CommSemiring β] {f : α →+* β} (k: ℕ):
  (L.map f)^k = (L^k).map f := by

  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ]
    rw [pow_succ]
    simp
    rw [ih]

-- A subgroup of an FG commutative group is again FG
lemma fg_of_subgroup_fg_comm {A : Type*} [CommGroup A] [Group.FG A] (H : Subgroup A) : H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  have : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h := IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)
  rw [Submodule.fg_iff_addSubgroup_fg] at h
  simpa using h

lemma fg_extension {A: Type*} [Group A] (N: Subgroup A) [N.Normal] (hN: N.FG) (hQ: Group.FG (A ⧸ N)): Group.FG A := by
  obtain ⟨S_Q, hS_Q⟩ := hQ
  obtain ⟨S_N, hS_N⟩ := hN


  sorry

set_option maxHeartbeats 5000000 in
lemma fg_of_subgroup_fg_nilpotent {A: Type*} [DecidableEq A] [Group A] [Group.IsNilpotent A] (A_fg: Group.FG A) (H: Subgroup A): H.FG := by
  classical
  revert H
  induction hn: Group.nilpotencyClass A using Nat.strong_induction_on generalizing A with
  -- | zero =>
  --   rw [Group.nilpotencyClass_zero_iff_subsingleton] at hn
  --   intro H
  --   have H_eq: H = ⊥ := by
  --     ext a
  --     simp
  --     simp [Subsingleton.eq_one a]
  --   simp [H_eq]
  --   exact fg_of_subgroup_fg_comm ⊥
  | h n ih =>
  match n with
  | 0 =>
    rw [Group.nilpotencyClass_zero_iff_subsingleton] at hn
    intro H
    have H_eq: H = ⊥ := by
      ext a
      simp
      simp [Subsingleton.eq_one a]
    simp [H_eq]
    exact fg_of_subgroup_fg_comm ⊥
  | n + 1 =>
    have comm_eq := Subgroup.lowerCentralSeries_succ (⊤ : Subgroup A) n
    rw [← hn] at comm_eq
    rw [Subgroup.lowerCentralSeries_nilpotencyClass] at comm_eq
    conv at comm_eq =>
      rhs
      simp
    rw [eq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at comm_eq
    simp [Subgroup.centralizer_univ] at comm_eq
    have n_fg: (Subgroup.lowerCentralSeries (⊤ : Subgroup A) n).FG := by
      obtain ⟨S, hS⟩ := A_fg
      rw [lower_central_generates_succ (G := A) S hS]
      rw [← hn]
      simp
      rw [← Group.fg_iff_subgroup_fg]
      apply Group.closure_finset_fg

    specialize ih (A := A ⧸  (Subgroup.lowerCentralSeries (⊤ : Subgroup A) n)) (Group.nilpotencyClass (A ⧸ (⊤ : Subgroup A).lowerCentralSeries n)) (by
      -- The `n`-th term of the lower central series of `A ⧸ Cⁿ A` is the image of `Cⁿ A`, i.e. `⊥`.
      -- Hence that quotient has class `≤ n < n + 1 = nilpotencyClass A`.
      have key : (⊤ : Subgroup (A ⧸ (⊤ : Subgroup A).lowerCentralSeries n)).lowerCentralSeries n
          = ⊥ := by
        have hmap : Subgroup.map
            (QuotientGroup.mk' ((⊤ : Subgroup A).lowerCentralSeries n)) (⊤ : Subgroup A) = ⊤ :=
          Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
        rw [← hmap, ← Subgroup.map_lowerCentralSeries, Subgroup.map_eq_bot_iff,
          QuotientGroup.ker_mk']
      have h_le := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp key
      omega
    ) (by infer_instance) rfl

    intro H
    have h_inf_fg: ((H ⊓ (⊤ : Subgroup A).lowerCentralSeries n).subgroupOf ((⊤ : Subgroup A).lowerCentralSeries n)).FG := by
      --let c_comm: CommGroup ((⊤ : Subgroup A).lowerCentralSeries n) := by
      --  sorry
      let c_comm := Group.commGroupOfCenterEqTop (G := ((⊤ : Subgroup A).lowerCentralSeries n)) (by
        rw [Subgroup.eq_top_iff']
        intro x
        rw [Subgroup.mem_center_iff]
        intro y
        have foo := comm_eq x.prop
        rw [Subgroup.mem_center_iff] at foo
        specialize foo y.val
        ext
        simpa using foo
      )
      rw [← Group.fg_iff_subgroup_fg] at n_fg
      apply fg_of_subgroup_fg_comm

    have h_quot_fg := ih (Subgroup.map (QuotientGroup.mk' _) H)
    have h_equiv :=  QuotientGroup.quotientInfEquivProdNormalQuotient H ((⊤ : Subgroup A).lowerCentralSeries n)
    sorry

lemma iterate_const (A: Type*) (k: A) (n: ℕ): (fun _ => k)^[n] k = k := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp [ih]



-- Note: `⇑(f ^ n)`, not `f ^ n`: the latter elaborates at type `G → G` and picks up
-- `Pi.instPow`, i.e. the pointwise power `fun a => (f a) ^ n`, not composition.
lemma mul_aut_iterate {G: Type*} [Group G] (f: MulAut G) (n: ℕ): f^[n] = ⇑(f ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext a
    rw [Function.iterate_succ_apply, pow_succ, MulAut.mul_apply, ← ih]

-- lemma iterate_mul_aut_mul_eq_one {G: Type*} [Group G] (f : MulAut G) (n m k: ℕ) (g: G) (h: (fun x ↦ x * (f)^[n] x⁻¹)^[k] g = 1):
--     (fun x ↦ x * (f)^[n*m] x⁻¹)^[k] g = 1 := by

--   induction k generalizing g with
--   | zero =>
--     simpa using h
--   | succ k ih =>
--     rw [Function.iterate_succ']
--     simp
--     simp at ih
--     rw [ih]
--     . sorry
--     .
--       rw [Function.iterate_succ'] at h
--       simp at h
--       rw [← h]
--       simp
--       group
--       sorry


lemma toIntLinearMap_pow_coe {M : Type*}  [AddCommGroup M]  (f : M →+ M) (n: ℕ): ↑((f.toIntLinearMap)^(n)) = (f^[n]) := by
  induction n with
  | zero =>
    ext g
    simp
  | succ n ih =>
    ext g
    rw [pow_succ]
    rw [Function.iterate_succ]
    simp
    rw [ih]


lemma toIntLinearMap_pow_apply {M : Type*}  [AddCommGroup M]  (f : M →+ M) (g: M) (n: ℕ): ((f.toIntLinearMap)^(n)) g = (f^[n]) g := by
  induction n generalizing g with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ]
    rw [Function.iterate_succ]
    simp
    rw [ih]

lemma toIntLinearMap_comp_mul {M : Type*}  [AddCommGroup M] (f g : M →+ M): ((f.comp g).toIntLinearMap) = f.toIntLinearMap * g.toIntLinearMap := by
  ext a
  simp

lemma toIntLinearMap_neg {M_1 M_2 : Type*}  [AddCommGroup M_1] [AddCommGroup M_2]  (f : M_1 →+ M_2): (-f).toIntLinearMap = -(f.toIntLinearMap) := by
  ext a
  simp

@[simp]
lemma toIntLinearMap_id {M : Type*}  [AddCommGroup M]: (AddMonoidHom.id M).toIntLinearMap = LinearMap.id := by
  ext a
  simp

/-- Isolates `K` on the right of the `h_poly` inequality of
`int_matrix_poly_growth_eigenvalue`: to prove
`X < Real.log 2 * (K - N_1) ^ (1/2)` it suffices to prove `N_1 + (X / Real.log 2) ^ 2 < K`.

No hypothesis relating `N_1` and `K` is needed, and none on the sign of `X`: the conclusion
is *reduced* rather than rewritten to an iff, and `N_1 < K` already follows from the
premise since `(X / Real.log 2) ^ 2 ≥ 0`. -/
theorem lt_log_two_mul_rpow_half (N_1 K : ℕ) (X : ℝ)
    (h : (N_1 : ℝ) + (X / Real.log 2) ^ 2 < (K : ℝ)) :
    X < Real.log 2 * ((K : ℝ) - (N_1 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Real.sqrt_eq_rpow, mul_comm, ← div_lt_iff₀ hc]
  calc X / Real.log 2 ≤ |X / Real.log 2| := le_abs_self _
    _ = Real.sqrt ((X / Real.log 2) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ < Real.sqrt ((K : ℝ) - (N_1 : ℝ)) := Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 40000 in
--  {G: Type*} [Group G] [DecidableEq G] (H: Subgroup G)
lemma exists_gamma_n_unipotent_center_N' {H: Type*} [DecidableEq H] [Group H] {N': Subgroup H} [N'_normal: N'.Normal] (N'_nilpotent: Group.IsNilpotent N') (hN': Subgroup.FG N') (gamma: MulAut N'):
    ∃ a n, a ≠ 0 ∧ ∀ g ∈ Subgroup.center N', Nat.iterate (fun x => x * ((gamma^[a]) x⁻¹)) n g = 1 := by

  classical


  have gamma_conj_card: ∃ p q : ℕ, ∀ a b : ℕ, ∀ g, ∀ s: Finset (Finset.Ico a b), (List.map (fun k => gamma^[k] g) s.toList).prod = 1 := by
    sorry

  let torsion := CommGroup.torsion (Subgroup.center N')
  have center_fg: Group.FG (Subgroup.center N') := by
    rw [Group.fg_iff_subgroup_fg]

    apply fg_of_subgroup_fg_nilpotent
    rw [Group.fg_iff_subgroup_fg]
    apply hN'
  have torsion_fg : Group.FG torsion := by
    simp
    rw [Subgroup.fg_iff_add_fg]
    have : Module.Finite ℤ (Additive (Subgroup.center N')) := Module.Finite.iff_addGroup_fg.mpr (by
      apply AddGroup.fg_of_group_fg
    )
    let foo: IsNoetherian ℤ (AddSubgroup.toIntSubmodule torsion.toAddSubgroup) := by
      infer_instance
    have h := IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule torsion.toAddSubgroup)
    rw [Submodule.fg_iff_addSubgroup_fg] at h
    simpa using h

  have fg_top: (⊤ : Subgroup (Subgroup.center N')).FG := by
    rw [← Group.fg_def]
    apply center_fg

    -- Submodule.FG.of_le
  have T_finite := CommGroup.finite_of_fg_isMulTorsion torsion (by
    simp [torsion]
    rw [IsMulTorsion]
    intro g
    have foo := g.prop
    rw [CommGroup.mem_torsion] at foo
    rw [isOfFinOrder_iff_pow_eq_one]
    rw [isOfFinOrder_iff_pow_eq_one] at foo
    obtain ⟨n, n_pos, hg⟩ := foo
    use n
    refine ⟨n_pos, ?_⟩
    rw [Subtype.ext_iff]
    exact hg
  )

  -- let pre_gamma_center := MonoidHom.domRestrict gamma.toMonoidHom (Subgroup.center N')
  -- let gamma_center := MonoidHom.codRestrict pre_gamma_center (Subgroup.center N') (by
  --   intro x
  --   simp [pre_gamma_center]
  --   have char := Subgroup.centerCharacteristic (G := N')
  --   rw [Subgroup.characteristic_iff_comap_eq] at char
  --   have foo := char gamma
  --   rw [Subgroup.ext_iff] at foo
  --   specialize foo x
  --   simp at foo
  --   exact foo
  -- )
  let gamma_center := MulAut.characteristic (Subgroup.center N') gamma
  have t_char: torsion.Characteristic := torsion_characteristic
  let torsion_N := Subgroup.map (Subgroup.subtype _) torsion
  let gamma_torsion := MonoidHom.domRestrict gamma.toMonoidHom torsion_N
  let new_gamma_torsion_hom := MonoidHom.codRestrict gamma_torsion torsion_N (by
    rw [Subgroup.characteristic_iff_map_le] at t_char
    specialize t_char
    intro x
    simp [torsion_N]
    use ?_
    .
      rw [CommGroup.mem_torsion]
      simp [gamma_torsion]
      rw [isOfFinOrder_iff_pow_eq_one]
      simp
      rw [← isOfFinOrder_iff_pow_eq_one]
      conv =>
        arg 1
        equals gamma.toMonoidHom x =>
          simp
      apply MonoidHom.isOfFinOrder
      have x_prop := x.prop
      unfold torsion_N at x_prop
      simp [-SetLike.coe_mem] at x_prop
      obtain ⟨x_mem, x_mem_torsion⟩ := x_prop
      rw [CommGroup.mem_torsion] at x_mem_torsion
      rw [isOfFinOrder_iff_pow_eq_one] at x_mem_torsion
      simp at x_mem_torsion
      rw [← isOfFinOrder_iff_pow_eq_one] at x_mem_torsion
      simpa using x_mem_torsion
    .
      simp [gamma_torsion]
      have char_center := Subgroup.centerCharacteristic (G := N')
      rw [Subgroup.characteristic_iff_map_eq] at char_center
      specialize char_center gamma
      rw [← char_center]
      simp
      have x_prop := x.prop
      unfold torsion_N at x_prop
      simp [-SetLike.coe_mem] at x_prop
      obtain ⟨x_center, hx⟩ := x_prop
      exact x_center
  )

  let new_gamma_torsion := MulAut.characteristic torsion_N gamma

  -- let new_gamma_torsion: MulAut (torsion_N) := MulEquiv.ofBijective new_gamma_torsion_hom (by
  --   unfold Function.Bijective
  --   refine ⟨?_, ?_⟩
  --   .
  --     intro a b hab
  --     simp [new_gamma_torsion_hom, gamma_torsion] at hab
  --     exact hab
  --   .
  --     intro p
  --     use ⟨gamma.symm p, (by

  --       sorry
  --     )⟩
  --     simp [new_gamma_torsion_hom, gamma_torsion]
  -- )

  have finite_aut: Finite (MulAut (torsion_N)) := by infer_instance
  have fin_order_new_gamma := isOfFinOrder_of_finite new_gamma_torsion

  have order_pos: 0 < orderOf new_gamma_torsion := by
    rw [← Nat.ne_zero_iff_zero_lt]
    rw [orderOf_ne_zero_iff]
    apply fin_order_new_gamma

  have iter_gamma_coe: ∀ n, ∀ g, (⇑new_gamma_torsion)^[n] g = gamma^[n] g := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ]
      simp
      rw [ih]
      simp [new_gamma_torsion, new_gamma_torsion_hom, gamma_torsion]



  let gamma_lift := QuotientGroup.congr (torsion) torsion gamma_center (by
    rw [Subgroup.characteristic_iff_map_eq] at t_char
    specialize t_char gamma_center
    exact t_char
  )

  have unipotent_on_quot: ∃ a, ∃ n, 0 < a ∧  ∀ g : (Subgroup.center ↥N') ⧸ torsion, Nat.iterate (fun x => x * ((gamma_lift^[a] x⁻¹))) n g = 1 := by
    wlog nontrivial_quot: Nontrivial ((Subgroup.center ↥N') ⧸ torsion)
    .
      clear this
      simp at nontrivial_quot
      use 1
      use 1
      simp
      intro g
      have quot_subsingelton: Subsingleton ((Subgroup.center ↥N') ⧸ torsion) := by
        rw [QuotientGroup.subsingleton_iff]
        exact nontrivial_quot

      have g_eq := Subsingleton.eq_one g
      simp [g_eq]




    let foo: CommGroup (Subgroup.center N') := by infer_instance
    -- if the additive picture is wanted, this is *definitionally* the same type:
    have add_torsion_free: IsAddTorsionFree
        (Additive ↥(Subgroup.center ↥N') ⧸ AddCommGroup.torsion (Additive ↥(Subgroup.center ↥N'))) := by
      infer_instance

    let add_quot := (Additive ↥(Subgroup.center ↥N') ⧸ AddCommGroup.torsion (Additive ↥(Subgroup.center ↥N')))
    have module_torsion_free: Module.IsTorsionFree ℤ add_quot := by
      infer_instance


    let fin_dim: Module.Finite ℤ add_quot := by infer_instance

    let gamma_add := gamma_lift.toAdditive.toAddMonoidHom.toIntLinearMap
    let B := (Module.finBasis ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion)))
    let gamma_matrix := gamma_add.toMatrix B B
    have quot_fg: AddGroup.FG (Additive (↥(Subgroup.center ↥N') ⧸ torsion)) := by
      infer_instance
    have invertible_gamma: Invertible gamma_matrix := {
      invOf := ((gamma_lift.toAdditive).symm.toAddMonoidHom).toIntLinearMap.toMatrix B B
      invOf_mul_self := by
        simp [gamma_matrix, gamma_add]
        rw [← LinearMap.toMatrix_mul]
        rw [← toIntLinearMap_comp_mul]
        simp
      mul_invOf_self := by
        simp [gamma_matrix, gamma_add]
        rw [← LinearMap.toMatrix_mul]
        rw [← toIntLinearMap_comp_mul]
        simp
    }

    let dim := Module.finrank ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion))
    let equiv (v: Fin _ → ℤ) := (Finsupp.linearEquivFunOnFinite ℤ _ (Fin dim)).symm v
    let remap (v: Fin _ → ℤ) := Finsupp.linearCombination _ B (equiv v)

    have gamma_matrix_mulVec: ∀ v: (Fin dim) → ℤ , remap ((gamma_matrix).mulVec (equiv v)) = Additive.ofMul (gamma_lift (Additive.toMul (remap v))) := by
      intro v
      unfold gamma_matrix
      rw [← Module.Basis.repr_linearCombination (v := (equiv v)) (b := B)]
      rw [LinearMap.toMatrix_mulVec_repr]
      simp [remap, gamma_add, equiv]


    have gamma_matrix_mulVec_pow: ∀ n: ℕ, ∀ v: (Fin dim) → ℤ , remap ((gamma_matrix^n).mulVec (equiv v)) = Additive.ofMul (gamma_lift^[n] (Additive.toMul (remap v))) := by
      intro n
      induction n with
      | zero =>
        intro v
        simp [remap, equiv]
      | succ n ih =>
        intro v
        rw [Function.iterate_succ_apply', pow_succ', ← Matrix.mulVec_mulVec]
        rw [show ((gamma_matrix ^ n).mulVec ⇑(equiv v))
              = ⇑(equiv ((gamma_matrix ^ n).mulVec ⇑(equiv v))) from rfl]
        rw [gamma_matrix_mulVec, ih]
        rfl
    -- have gamma_matrix_map_mulVec: ∀ v, B.repr.symm (Finsupp.equivFunOnFinite.symm ((gamma_matrix).mulVec v)) ∈ (Finset.image (fun (i: Fin dim) => (v i • (B i))) Finset.univ)  := by
    --   intro v
    --   simp [gamma_matrix]
    --   rw [← B.repr_sum_self (c := v)]
    --   rw [LinearMap.toMatrix_mulVec_repr]
    --   rw [map_sum]
    --   simp_rw [map_smul]
    --   simp
    --   sorry

    --have gamma_lift_pow_mem: ∀ k: ℕ, Finset.sum (gamma_lift^{})

    have rank_nonzero: NeZero (Module.finrank ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion))) := by
      apply NeZero.of_pos
      apply Module.finrank_pos

    have gamma_conj: ∀ k: ℕ, (0 < k) →  ∃ q: ℕ, ∀ g, ∀ b: ℕ, 0 < b → ∃ p: ℕ, 0 < p ∧ ∀ a: ℕ, (0 < a) → (a < b) → (Finset.image (fun x ↦ (List.map (fun i ↦ (gamma)^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * (b - a)^q := by
      sorry


    have gamma_lift_conj: ∀ k: ℕ, (0 < k) →  ∃ q: ℕ, ∀ g, ∀ b: ℕ, 0 < b → ∃ p: ℕ, 0 < p ∧ ∀ a: ℕ, (0 < a) → (a < b) → (Finset.image (fun x ↦ (List.map (fun (i:  ↥(Finset.Ico a b)) ↦ (gamma_lift)^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * (b - a)^q := by


      sorry

    have unipotent_gamma_matrix := int_matrix_unipotent (by
      apply Module.finrank_pos
    ) (unitOfInvertible gamma_matrix) (by
      apply int_matrix_poly_growth_eigenvalue
      .
        intro k hk v
        -- name the (fixed) group element the iterates are applied to
        set g : ↥(Subgroup.center ↥N') ⧸ torsion :=
          Additive.toMul ((Finsupp.linearCombination ℤ ⇑B)
            ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin dim)).symm v)) with hg


        obtain ⟨q, hq⟩ := gamma_lift_conj ⌈Real.logb ‖k‖ 3⌉₊ (by simp; sorry)
        --have K: ℕ := ⌈Real.logb ‖k‖ 3⌉₊ + ⌈((4 * ↑q + Real.log ↑p) / Real.log 2) ^ 2⌉₊ + 1

        have K : ℕ := sorry
        use K

        obtain ⟨p, p_pos, hpq⟩ := hq g K sorry
        specialize hpq ⌈Real.logb ‖k‖ 3⌉₊ sorry sorry
        refine ⟨by sorry, ?_⟩
        use p
        use q
        refine ⟨?_, ?_, ?_⟩
        . exact p_pos
        .
          apply lt_log_two_mul_rpow_half
          sorry
        .
          rw [← (Finset.card_image_iff (f := fun a => remap (Finsupp.equivFunOnFinite.symm a))).mpr]
          .
            rw [Finset.image_image]
            simp [remap, equiv]
            rw [Function.comp_def]
            simp_rw [map_sum]
            simp [remap, equiv] at gamma_matrix_mulVec_pow
            simp_rw [← pow_mul]
            simp_rw [gamma_matrix_mulVec_pow]
            -- Turn each subsum into `Additive.ofMul` of a product in the group, keeping the
            -- index set as the subtype `↥(Finset.Ico N_1 N_2)`.
            simp_rw [← ofMul_prod]
            -- `Additive.ofMul` is a bijection, so it does not affect the cardinality: pull it
            -- out of the image and discard it.
            rw [← Function.comp_def Additive.ofMul, ← Finset.image_image,
              Finset.card_image_of_injective _ (Equiv.injective _)]


            simp_rw [← Finset.prod_map_toList]

            grw [hpq]
            -- TODO - we might be able to make the goal stronger, if we don't actually need the factor of 2 in it
            rw [pow_mul']
            apply mul_le_mul
            . simp
            . apply Nat.le_pow
              simp
            . simp
            . simp
          . apply Function.Injective.injOn
            intro a b hab
            simp [remap, equiv] at hab
            rw [Function.Injective.eq_iff (linearIndependent_iff_injective_finsuppLinearCombination.mp ?_)] at hab
            . simpa using hab
            . apply Module.Basis.linearIndependent

        --rw [← (Finset.card_image_iff (f := fun (a: Fin (Module.finrank ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion))) → ℂ) => ((Module.finBasis ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion)))).repr.symm a)).mpr]
        --simp_rw [← pow_mul]
    )
    obtain ⟨a, n, a_pos, hm⟩ := unipotent_gamma_matrix
    use a
    use n
    refine ⟨a_pos, ?_⟩
    intro g
    apply_fun (fun f => f.toLin (Module.finBasis _ _) (Module.finBasis _ _)) at hm
    rw [LinearMap.ext_iff] at hm
    specialize hm g
    simp [gamma_matrix] at hm
    simp [gamma_add] at hm
    conv at hm =>
      rhs
      equals 0 => rfl



    apply_fun (fun f => (f).toMul) at hm
    conv at hm =>
      rhs
      equals 1 => rfl

    rw [← neg_sub] at hm
    rw [neg_pow] at hm
    simp at hm
    rw [Module.End.mul_eq_comp] at hm
    simp at hm
    simp [Function.comp_def] at hm
    apply (LinearMap.ker_eq_bot'.mp (by
      ext a
      clear hm
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        simp
        simp at ih
        exact ih
    )) at hm
    rw [← toMul_eq_one] at hm
    rw [← hm]
    clear hm

    have x_mul_gamma_eq: (fun x => x * (⇑gamma_lift)^[a] x⁻¹) = Additive.toMul ∘ (-((MonoidHom.toAdditive gamma_lift.toMonoidHom).toIntLinearMap ^ (a) - LinearMap.id)).toFun ∘ (Additive.ofMul) := by
      ext x
      conv =>
        rhs
        equals Additive.toMul ((-((MonoidHom.toAdditive gamma_lift.toMonoidHom).toIntLinearMap ^ (a) - LinearMap.id)).toFun (Additive.ofMul x)) =>
          rfl
      simp
      rw [toIntLinearMap_pow_apply]
      simp
      rw [Function.comp_def]
      rw [div_eq_mul_inv]
      simp
      rfl

    rw [x_mul_gamma_eq]
    simp
    rw [Module.End.coe_pow]
    --rfl
    sorry

    -- induction n with
    -- | zero =>
    --   simp
    --   rfl
    -- | succ n ih =>
    --   rw [Function.iterate_succ']
    --   simp
    --   rw [ih]
    --   rw [pow_succ]
    --   rw [Module.End.mul_eq_comp]
    --   simp
    --   rw [Function.comp_def]
    --   simp
    --   conv =>
    --     rhs
    --     pattern g
    --     equals (Additive.ofMul g) =>
    --       rfl

    --   rw [LinearMap.sub_apply]
    --   simp [-map_sub]
    --   conv =>
    --     rhs
    --     rhs
    --   simp_rw [toIntLinearMap_pow_apply]
    --   sorry







  obtain ⟨quot_pow, quot_n, quot_pow_pos, h_quot_n⟩ := unipotent_on_quot
  use (quot_pow * orderOf new_gamma_torsion)
  use quot_n + 1



  have new_gamma_pow: new_gamma_torsion^[quot_pow * (orderOf new_gamma_torsion)] = id := by
    rw [mul_comm, Function.iterate_mul]
    rw [mul_aut_iterate]
    simp

  have orig_new_gamma_pow := new_gamma_pow

  refine ⟨by positivity, ?_⟩
  intro g hg

  have gamma_mem_center:  ∀ g: Subgroup.center N', gamma g ∈ Subgroup.center N' := by
    intro g
    have center_char: (Subgroup.center N').Characteristic := by
      infer_instance
    rw [Subgroup.characteristic_iff_le_comap] at center_char
    specialize center_char (gamma) g.prop
    simp at center_char
    exact center_char

  have gamma_iter_mem_center: ∀ n, ∀ g: Subgroup.center N', gamma^[n] g ∈ Subgroup.center N' := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ]
      simp
      apply ih ⟨_, gamma_mem_center g⟩


  specialize h_quot_n (QuotientGroup.mk ⟨g, hg⟩)

  have swap_gamma_lift: ∀ g: Subgroup.center N', gamma_lift ↑g = ↑(⟨((gamma) g), by apply gamma_mem_center⟩ : Subgroup.center N') := by
    intro g
    simp [gamma_lift, gamma_center]
    rfl

  have swap_gamma_lift_iter: ∀ n, ∀ g: Subgroup.center N', gamma_lift^[n] ↑g = ↑(⟨((gamma^[n]) g), by apply gamma_iter_mem_center⟩ : Subgroup.center N') := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ']
      simp only [Function.comp_apply]
      rw [ih]
      rw [swap_gamma_lift]
      simp_rw [Function.iterate_succ']
      simp


  have swap_iter: ∀ n, ∀ g: Subgroup.center N', (fun x ↦ x * (gamma_lift^[quot_pow]) x⁻¹)^[n] g = QuotientGroup.mk ⟨((fun x ↦ x * (gamma^[quot_pow]) x⁻¹)^[n] g), (by
    rw [mul_aut_iterate]
    simp
    induction n generalizing g with
    | zero =>
      simp
    | succ n ih =>
      simp
      have mul_mem_center: (↑g * ((gamma ^ (quot_pow )) ↑g)⁻¹) ∈ Subgroup.center N' := by
        apply Subgroup.mul_mem
        . simp
        .
          simp
          have center_char: (Subgroup.center N').Characteristic := by
            infer_instance
          rw [Subgroup.characteristic_iff_le_comap] at center_char
          specialize center_char (gamma ^ (quot_pow)) g.prop
          simpa using center_char
      conv =>
        pattern (↑g * ((gamma ^ (quot_pow)) ↑g)⁻¹)
        equals ↑(⟨_, mul_mem_center⟩ : Subgroup.center N') =>
          rfl
      apply ih

  )⟩ := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ']
      rw [Function.comp_def]
      beta_reduce
      rw [ih]
      simp_rw [Function.iterate_succ']
      simp
      rw [swap_gamma_lift_iter]
      rfl

  rw [swap_iter] at h_quot_n
  rw [QuotientGroup.eq_one_iff] at h_quot_n
  rw [Function.iterate_succ']
  simp


  rw [funext_iff] at new_gamma_pow
  apply Subgroup.mem_map_of_mem (Subgroup.center ↥N').subtype at h_quot_n
  specialize new_gamma_pow ⟨_, h_quot_n⟩
  simp at new_gamma_pow




  rw [Subtype.ext_iff] at new_gamma_pow
  rw [iter_gamma_coe] at new_gamma_pow
  simp at new_gamma_pow
  sorry
  --simp_rw [new_gamma_pow]
  --simp

  -- OLD CODE


  -- conv =>
  --   lhs

  -- rw [funext_iff] at orig_new_gamma_pow
  -- --simp_rw [Subtype.ext_iff] at orig_new_gamma_pow
  -- conv at orig_new_gamma_pow =>
  --   intro x
  --   arg 1
  --   arg 1
  --   simp [new_gamma_torsion]


  -- simp_rw [Subtype.ext_iff] at orig_new_gamma_pow
  -- conv at orig_new_gamma_pow =>
  --   intro x
  --   rw [iter_gamma_coe]
  --   simp

  -- have orig_gamma_for_n: ∀ x: N', (⇑gamma)^[orderOf new_gamma_torsion] x = x := by
  --   sorry
  -- simp at orig_new_gamma_pow
  -- simp_rw [orig_gamma_for_n]
  -- simp
  -- have quot_n_eq: quot_n - 1 + 1 = quot_n := by grind
  -- rw [← quot_n_eq]
  -- rw [Function.iterate_succ]
  -- simp
  -- rw [iterate_const]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 160000 in
/--{G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) [H.Normal]--/
lemma exists_gamma_n_unipotent_N' {H: Type*} [Group H] {N': Subgroup H} [N'_normal: N'.Normal] (N'_nilpotent: Group.IsNilpotent N') (hN': Subgroup.FG N') (gamma: MulAut N'):
    ∃ a n, a ≠ 0 ∧ ∀ g : N', Nat.iterate (fun x => x * ((gamma^[a]) x⁻¹)) n g = 1 := by


  -- induction ↥N' using Group.nilpotent_center_quotient_ind (P := P) with
  classical
  by_cases N'_subsingle: Subsingleton N'
  .
    use 1
    use 1
    simp
    intro a ha
    have order := Subsingleton.orderOf_eq (⟨_, ha⟩ : N')
    simp at order
    simp [order, iteratedCommutator]

-- lemma quot_mk_one (H: Type*) [Group H] (P: Subgroup H) [P.Normal] (a: H) (ha: QuotientGroup.mk a = (QuotientGroup.mk' P 1)): a ∈ P := by
--   simp? at ha


  induction hn: Group.nilpotencyClass N' using Nat.strong_induction_on generalizing H N' with
  -- | zero =>
  --   rw [Group.nilpotencyClass_zero_iff_subsingleton] at hn
  --   use 1
  --   use 1
  --   simp
  --   intro a ha a_mem
  --   have order := Subsingleton.orderOf_eq (⟨_, a_mem⟩ : N')
  --   simp at order
  --   simp [order, iteratedCommutator]
  | h n ih =>

    let new_N' := (⊤ : Subgroup (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N')))
    let first_map := (MulAut.congr (Subgroup.topEquiv (G := ↥N' ⧸ Subgroup.center ↥N'))).symm
    let aut_transfer := first_map
    let gamma_quot := QuotientGroup.congr (Subgroup.center N') (Subgroup.center N') gamma (by
      conv =>
        lhs
        arg 1
        equals gamma.toMonoidHom =>
          simp
      rw [Subgroup.characteristic_iff_map_eq.mp]
      exact Subgroup.centerCharacteristic
    )
    let final_gamma := aut_transfer gamma_quot

    by_cases top_subsingle: Subsingleton (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N'))
    .
      obtain ⟨z_a, z_n, h_z_a, h_z_unipotent⟩ := exists_gamma_n_unipotent_center_N' (N' := N') (N'_nilpotent) (hN') gamma

      use z_a
      use z_n
      refine ⟨h_z_a, ?_⟩
      intro g
      have foo := top_subsingle.allEq
      simp at foo
      have center_top: Subgroup.center N' = ⊤ := by
        rw [← QuotientGroup.subsingleton_iff]
        exact {
          allEq := foo
        }

      apply h_z_unipotent
      simp [center_top]

    have foo := ih (Group.nilpotencyClass (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N'))) (by
      grw [Subgroup.nilpotencyClass_le]
      simp [nilpotencyClass_quotient_center]
      rw [← hn]
      simp
      by_contra!
      simp at this
      rw [nilpotencyClass_zero_iff_subsingleton] at this
      contradiction
    ) (H := N' ⧸ Subgroup.center N') (N' := ⊤) (by simp; apply Group.nilpotent_quotient_of_nilpotent) (by
      have fg_quot: Group.FG (↥N' ⧸ Subgroup.center ↥N') := by
        rw [← Group.fg_iff_subgroup_fg] at hN'
        apply QuotientGroup.fg
      have base_fg: Group.FG (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N')) := by
        apply Subgroup.fg_of_index_ne_zero

      rw [← Group.fg_iff_subgroup_fg]
      apply Subgroup.fg_of_index_ne_zero
    ) final_gamma top_subsingle rfl

    clear ih
    obtain ⟨a, n, ha, h_prev⟩ := foo

    obtain ⟨z_a, z_n, h_z_a, h_z_unipotent⟩ := exists_gamma_n_unipotent_center_N' (N' := N') (N'_nilpotent) (hN') (gamma^a)

    use a * z_a
    use z_n + n
    refine ⟨by positivity, ?_⟩
    intro g
    let g_h_prev: (⊤ : Subgroup (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N'))) := ⟨⟨g, by simp⟩, by simp⟩
    specialize h_prev g_h_prev
    rw [Function.iterate_add_apply]
    --rw [← QuotientGroup.out_eq' (a := iteratedCommutator _ _ _)] at h_prev
    --rw [QuotientGroup.eq_one_iff] at h_prev

    --let foo :=  iteratedCommutatorNormal (H.subtype g) (gamma ^ z_a) (n)
    specialize h_z_unipotent ((fun x ↦ x * ((gamma^[a*z_a]) (x⁻¹)))^[n] g) ?_
    -- specialize h_z_unipotent ⟨⟨((fun x ↦ x * ((gamma^[a*z_a]) (x⁻¹)))^[n] g), (by
    --   clear h_prev
    --   induction n with
    --   | zero =>
    --     simp
    --   | succ n n_ind =>
    --     rw [Function.iterate_succ']
    --     simp
    --     apply Subgroup.mul_mem
    --     .
    --       simp only [iterate_map_inv] at n_ind
    --       exact n_ind
    --     . simp
    --     -- rw [mul_assoc]
    --     -- rw [mul_assoc]
    --     -- apply Subgroup.mul_mem
    --     -- . exact n_ind
    --     -- .
    --     --   rw [← mul_assoc]
    --     --   apply Subgroup.Normal.conj_mem
    --     --   . infer_instance
    --     --   . simpa using n_ind
    -- )⟩, by (
    --   sorry
    -- )⟩ ?_
    .

      have swap_gamma_base: ∀ x, (gamma) x = ((final_gamma) ⟨x, by simp⟩).val := by
        intro x
        simp [final_gamma, aut_transfer, first_map]
        rfl

      have swap_gamma: ∀ x, ∀ m: ℕ, (gamma^[m]) x = ((final_gamma^[m]) ⟨x, by simp⟩).val := by
        intro x m
        induction m generalizing x with
        | zero =>
          simp
        | succ m ih_m =>
          rw [Function.iterate_succ]
          simp
          rw [ih_m]
          rw [swap_gamma_base]


      have coe_iter: ∀ m: ℕ, ((fun x ↦ x * (final_gamma^[m]) x⁻¹)^[n] g_h_prev).val = (fun x ↦ x * (gamma^[m]) x⁻¹)^[n] g := by
        clear h_prev
        intro m
        induction n with
        | zero =>
          simp
          simp [g_h_prev]
        | succ n ind_n =>
          simp_rw [Function.iterate_succ']
          simp
          simp at ind_n
          simp [ind_n]
          rw [swap_gamma]
          simp
          rw [← ind_n]

      --simp [-iterate_map_inv]
      rw [← QuotientGroup.eq_one_iff]
      rw [← coe_iter]
      sorry
      --exact h_prev
      --simpa using h_prev

      -- a ((conj b) a⁻¹

      --(a ((conj b) a⁻¹) (conj b) (a ((conj b) a⁻¹)⁻¹

      -- a b a⁻¹ b⁻¹
      -- (a b a⁻¹ b⁻¹) b (a b a⁻¹ b⁻¹)⁻¹ b⁻¹
      -- (a b a⁻¹) b (a b⁻¹ a⁻¹ b⁻¹)

    .
      simp_rw [mul_aut_iterate] at h_z_unipotent
      rw [mul_aut_iterate]
      simp_rw [← pow_mul] at h_z_unipotent
      exact h_z_unipotent


-- lemma old_unipotent_stuff {G: Type*} [Group G] (H: Subgroup G) [H.Normal] {N: Subgroup H} [N'_normal: N.Normal] (N'_nilpotent: Group.IsNilpotent N) (hN': Subgroup.FG N) (gamma: MulAut N):
--     ∃ a n, a ≠ 0 ∧ ∀ g : N, Nat.iterate (fun x => x * ((gamma^a) x)) n g = 1 := by


--   -- Use the fact that this is a subgroup of a finitely-generated nilpotent group
--   have center_fg: Group.FG (Subgroup.center N) := by
--     sorry
--   have center_iso := CommGroup.equiv_free_prod_directSum_zmod (Subgroup.center N)
--   obtain ⟨I, J, fin_I, fin_J, I_pow, I_pow_prime, K_map, ⟨center_iso⟩⟩ := center_iso


--   --have center_normal_in_G := ConjAct.normal_of_characteristic_of_normal (K := Subgroup.center N)

--   let new_conj := MulAut.conjNormal (H := (Subgroup.map N.subtype (Subgroup.center ↥N))) gamma

--   -- have subtype_center_iso := Subgroup.equivMapOfInjective (Subgroup.center N) N.subtype (by apply Subgroup.subtype_injective)
--   -- have aut_congr := MulAut.congr subtype_center_iso
--   -- let gamma_conj := aut_congr.symm.toMonoidHom new_conj
--   -- let mulaut_fg_abelian := MulAut.congr center_iso


--   -- TODO - bad K?
--   --let K := Nat.card (((i : I) → Multiplicative (ZMod (I_pow i ^ K_map i))))

--   let center_fst := (MonoidHom.fst _ _).comp center_iso.toMonoidHom
--   let aut_congr := MulAut.congr center_iso

--   let gamma_pow_conj (n: ℕ): MulAut ↥(Subgroup.center ↥N) := {
--     toFun := fun a => ⟨⟨gamma^n * a * (gamma^n)⁻¹, by
--       apply N_normal.conj_mem
--       simp
--     ⟩, by
--       have map_normal: (Subgroup.map (Subgroup.subtype _) (Subgroup.center N)).Normal := by
--         infer_instance
--       have foo := map_normal.conj_mem a (by simp) (gamma^n)
--       simp at foo
--       obtain ⟨a_mem, other_mem⟩ := foo
--       exact other_mem
--     ⟩
--     invFun := fun a =>  ⟨⟨(gamma^n)⁻¹ * a * (gamma^n), by
--       apply N_normal.conj_mem'
--       simp
--     ⟩, by (
--       have map_normal: (Subgroup.map (Subgroup.subtype _) (Subgroup.center N)).Normal := by
--         infer_instance
--       have foo := map_normal.conj_mem' a (by simp) (gamma^n)
--       simp at foo
--       obtain ⟨a_mem, other_mem⟩ := foo
--       exact other_mem
--     )⟩
--     left_inv := by
--       intro a
--       group
--     right_inv := by
--       intro a
--       group
--     map_mul' := by
--       simp
--   }



--   let gamma_conj := gamma_pow_conj 1

--   have torsion_free: IsMulTorsionFree ((Subgroup.center N) ⧸ (CommGroup.torsion (Subgroup.center N))) := by
--     apply QuotientGroup.instIsMulTorsionFree

--   have center_quot_equiv := finDimVectorspaceEquiv (R := ℤ) (n := Module.finrank ℤ (Additive (((Subgroup.center N) ⧸ (CommGroup.torsion (Subgroup.center N)))))) (hn := by simp) (M := Additive (((Subgroup.center N) ⧸ (CommGroup.torsion (Subgroup.center N)))))

--   let gamma_quot := QuotientGroup.congr (CommGroup.torsion (Subgroup.center N)) (CommGroup.torsion (Subgroup.center N)) gamma_conj (by
--     conv =>
--       arg 1
--       arg 1
--       equals gamma_conj.toMonoidHom => rfl
--     apply Subgroup.characteristic_iff_map_eq (H := (CommGroup.torsion (Subgroup.center N))).mp
--     apply torsion_characteristic
--   )

--   let add_gamma_conj := gamma_quot.toAdditive.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance)
--   let gamma_int := LinearEquiv.conj center_quot_equiv (add_gamma_conj)
--   let gamma_matrix := gamma_int.toMatrix'.map (complexOfIntHom)

--   -- TODO - deduplicate the val_inv and inv_val code
--   have gamma_eigenvalues := int_matrix_poly_growth_eigenvalue {
--     val := gamma_int.toMatrix'
--     inv := (LinearEquiv.conj center_quot_equiv (add_gamma_conj.symm)).toMatrix'
--     val_inv := by
--       unfold gamma_int
--       rw [← LinearMap.toMatrix'_mul]
--       apply_fun (fun f => Matrix.toLin' f)
--       .
--         simp
--         conv =>
--           lhs
--           equals (center_quot_equiv.conj add_gamma_conj).comp (center_quot_equiv.conj (add_gamma_conj.symm)) =>
--             rfl

--         rw [← LinearEquiv.conj_comp]
--         simp
--       .
--         intro a b hab
--         simpa using hab
--     inv_val := by
--       unfold gamma_int
--       rw [← LinearMap.toMatrix'_mul]
--       apply_fun (fun f => Matrix.toLin' f)
--       .
--         simp
--         conv =>
--           lhs
--           equals (center_quot_equiv.conj add_gamma_conj.symm).comp (center_quot_equiv.conj (add_gamma_conj)) =>
--             rfl

--         rw [← LinearEquiv.conj_comp]
--         simp
--       .
--         intro a b hab
--         simpa using hab

--   } (p := sorry) sorry sorry
--   simp only [] at gamma_eigenvalues

--   -- use pow_eq_one_of_norm_le_one (Kronecker's Theorem) once mathlib is bumped

--   have gamma_eigen_unity: ∀ k : Module.End.Eigenvalues gamma_matrix.toLin', ∃ n, 0 < n ∧ k.val^n = 1 := by
--     sorry

--   choose k_root h_k_root using gamma_eigen_unity
--   let n_prod := ∏ n ∈ (Finset.image k_root Finset.univ), n


--   let K := Nat.card (MulAut ↥(Subgroup.map (N.subtype.comp (Subgroup.center ↥N).subtype) (CommGroup.torsion ↥(Subgroup.center ↥N))))


--   have n_prod_ne: n_prod ≠ 0 := by
--     unfold n_prod
--     rw [Finset.prod_ne_zero_iff]
--     intro k hk
--     simp at hk
--     obtain ⟨a, ha⟩ := hk
--     have gamma_pow := (h_k_root a).1
--     rw [ha] at gamma_pow
--     grind

--   have K_ne_zero: K ≠ 0 := by
--     unfold K
--     rw [Nat.card_ne_zero]
--     refine ⟨by infer_instance, ?_⟩
--     unfold MulAut

--     have torsion_fg: Group.FG ↥(CommGroup.torsion ↥(Subgroup.center ↥N)) := by
--       simp
--       rw [Subgroup.fg_iff_add_fg]
--       apply fg_subgroup_of_abelian
--       apply AddGroup.fg_of_group_fg

--     have torsion_finite : Finite (CommGroup.torsion ↥(Subgroup.center ↥N)) := by
--       apply CommGroup.finite_of_fg_torsion
--       -- TODO - extract this and pr to mathlib
--       intro g
--       have foo := g.property
--       rw [CommGroup.mem_torsion] at foo
--       rw [isOfFinOrder_iff_pow_eq_one] at foo
--       rw [isOfFinOrder_iff_pow_eq_one]
--       simp_rw [Subtype.ext_iff]
--       simp_rw [Subtype.ext_iff] at foo
--       simpa using foo

--     apply MulEquiv.finite_left

--   have n_prod_mul_ne: (n_prod * K : ℕ) ≠ (0 : ℂ) := by
--     simp
--     refine ⟨n_prod_ne, ?_⟩
--     apply K_ne_zero

--   have n_prod_pow: ∀ k: Module.End.Eigenvalues gamma_matrix.toLin', k.val^(n_prod * K) = 1 := by
--     intro k
--     rw [pow_mul]
--     unfold n_prod
--     rw [← Finset.prod_erase_mul (a := k_root k)]
--     .
--       rw [pow_mul']
--       simp [h_k_root]
--     . simp



--   -- TODO - generalize and pr to mathlib
--   have gamma_pow_eigen: ∀ k: Module.End.Eigenvalues ((gamma_matrix.toLin')^(n_prod * K)), k.val = 1 := by
--     intro k
--     have k_prop := k.property
--     have has_eigen: Module.End.HasEigenvalue (Matrix.toLin' gamma_matrix ^ (n_prod * K)) k := by
--       exact k.property
--     rw [Module.End.hasEigenvalue_iff_mem_spectrum] at has_eigen
--     rw [← AlgEquiv.spectrum_eq (f := Module.End.toContinuousLinearMap _)] at has_eigen
--     simp at has_eigen
--     rw [spectrum.map_pow_of_pos] at has_eigen
--     .
--       rw [AlgEquiv.spectrum_eq] at has_eigen
--       simp at has_eigen
--       obtain ⟨c, c_mem, c_pow_eq⟩ := has_eigen
--       simp [Module.End.Eigenvalues.val, Module.End.UnifEigenvalues.val]
--       simp [Module.End.Eigenvalues.val, Module.End.UnifEigenvalues.val] at c_pow_eq
--       rw [← c_pow_eq]
--       rw [← Matrix.spectrum_toLin'] at c_mem
--       rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at c_mem
--       specialize n_prod_pow ⟨_, c_mem⟩
--       simp [Module.End.Eigenvalues.val, Module.End.UnifEigenvalues.val] at n_prod_pow
--       exact n_prod_pow
--     .
--       simp at n_prod_mul_ne
--       simp
--       omega



--   -- have torsion_ne_top: CommGroup.torsion ↥(Subgroup.center ↥N) ≠ ⊤ := by

--   --   sorry


--   -- have quot_nontrivial : Nontrivial ((Subgroup.center ↥N) ⧸ CommGroup.torsion ↥(Subgroup.center ↥N)) := by
--   --   -- TODO - use QuotientGroup.nontrivial_iff
--   --   sorry

--   -- Module.free_of_finite_type_torsion_free'
--   -- QuotientGroup.instIsMulTorsionFree

--   -- have rank_ne_zero: NeZero (Module.finrank ℤ (Additive (↥(Subgroup.center ↥N) ⧸ CommGroup.torsion ↥(Subgroup.center ↥N)))) := by
--   --   rw [neZero_iff]
--   --   rw [Nat.ne_zero_iff_zero_lt]

--   --   -- QuotientGroup.nontrivial_iff
--   --   apply Module.finrank_pos

--   obtain ⟨m, hm⟩ := eigen_one_unipotent _ gamma_pow_eigen

--   -- have m_ne_zero: m ≠ 0 := by
--   --   by_contra!
--   --   simp [this] at hm
--   --   rw [eq_comm] at hm
--   --   rw [LinearMap.ext_iff] at hm
--   --   specialize hm 1
--   --   rw [LinearMap.zero_apply] at hm
--   --   rw [Module.End.one_apply] at hm
--   --   rw [funext_iff] at hm
--   --   specialize hm ⟨0, ?_⟩
--   --   .
--   --     apply Module.finrank_pos
--   --   .
--   --     simp at hm


--   -- have quotient_comm_trivial: ∀ z : (↥(Subgroup.center ↥N) ⧸ CommGroup.torsion ↥(Subgroup.center ↥N)), iteratedCommutator z.out.val.val ((gamma) ^ (n_prod)) m ∈ Subgroup.map (Subgroup.subtype _) (Subgroup.center N) := by
--   --   clear * - gamma_conj
--   --   intro z

--   --   have comm_eq: ∀ n: ℕ, iteratedCommutator z.out.val.val ((gamma) ^ (n_prod)) 1 = (center_quot_equiv.symm ((-((gamma_int ^ n_prod) - 1)) ((center_quot_equiv z)))).out.val.val := by

--   --     intro n
--   --     simp [iteratedCommutator, Bracket.bracket]
--   --     conv =>
--   --       lhs
--   --       equals z.out.val.val * ((gamma_pow_conj n_prod) z.out⁻¹) =>
--   --         simp [gamma_pow_conj]
--   --         group

--   --     rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
--   --     rw [← Subtype.ext_iff, ← Subtype.ext_iff]
--   --     simp


--   --     sorry

--   --   sorry




--   use (n_prod * K)
--   -- Using 'm + 2' avoids an issue with the quotient group being trivial
--   use (m + 1)
--   refine ⟨?_, ?_⟩
--   .
--     simp [K]
--     refine ⟨n_prod_ne, ?_⟩
--     apply K_ne_zero

--   intro g hg
--   unfold iteratedCommutator
--   rw [Function.iterate_succ']
--   simp

--   have comm_torsion_trivial: ∀ h ∈ (CommGroup.torsion ↥(Subgroup.center ↥N)), ⁅h.val.val, gamma ^ (n_prod * K)⁆ = 1 := by
--     intro h h_mem
--     rw [commutatorElement_def]



--     -- TODO - this can probably be generalized into a lemma about characteristic subgroups, and pr'd to mathlib
--     have normal_center_map: (Subgroup.map (N.subtype.comp (Subgroup.center ↥N).subtype) (CommGroup.torsion ↥(Subgroup.center ↥N))).Normal := {
--       conj_mem := by
--         intro f hf k
--         simp at hf
--         obtain ⟨f_mem_N, f_mem_center, f_mem_torsion⟩ := hf
--         simp
--         use ?_
--         . use ?_
--           .
--             rw [CommGroup.mem_torsion]
--             conv =>
--               arg 1
--               arg 1
--               arg 1
--               equals (MulAut.conj k) f =>
--                 rfl

--             rw [isOfFinOrder_iff_pow_eq_one]
--             simp_rw [Subtype.ext_iff]
--             simp
--             rw [← isOfFinOrder_iff_pow_eq_one]
--             rw [CommGroup.mem_torsion] at f_mem_torsion
--             rw [isOfFinOrder_iff_pow_eq_one] at f_mem_torsion
--             simp_rw [Subtype.ext_iff] at f_mem_torsion
--             simp at f_mem_torsion
--             rw [← isOfFinOrder_iff_pow_eq_one] at f_mem_torsion
--             exact f_mem_torsion
--           .
--             have first := ConjAct.normal_of_characteristic_of_normal (H := N) (K := Subgroup.center ↥N)
--             have foo := first.conj_mem f (by simp; use f_mem_N) k
--             simp at foo
--             obtain ⟨mem_n, mem_center⟩ := foo
--             exact mem_center
--         .
--           apply N_normal.conj_mem
--           exact f_mem_N
--     }

--     have conj_trivial: MulAut.conjNormal (H := Subgroup.map ((Subgroup.subtype _).comp (Subgroup.subtype _)) ((CommGroup.torsion ↥(Subgroup.center ↥N)))) (gamma ^ (n_prod * K)) = 1 := by
--       rw [MonoidHom.map_pow]
--       rw [pow_mul']
--       unfold K
--       simp

--     apply_fun (fun f => f ⟨h⁻¹, by simpa using h_mem⟩) at conj_trivial
--     rw [Subtype.ext_iff] at conj_trivial
--     rw [MulAut.conjNormal_apply] at conj_trivial
--     simp at conj_trivial
--     conv =>
--       lhs
--       equals h.val.val * (gamma ^ (n_prod * K) * (↑↑h)⁻¹ * (gamma ^ (n_prod * K))⁻¹) =>
--         group
--     simp [conj_trivial]


--   have comm_mem_N: ∀ n, ∀ m, ∀ g: N, (fun x ↦ ⁅x, gamma ^ (n)⁆)^[m] ↑g ∈ N := by
--     intro n m g
--     have foo := iterated_comm_normal_eq_iterated g (gamma ^ (n)) (m)
--     unfold iteratedCommutator at foo
--     rw [← foo]
--     simp

--   have mem_center:  ∀ n, ∀ m, ⟨_, (comm_mem_N n m g)⟩ ∈ Subgroup.center N := by
--     intro n m
--     have foo := iterated_comm_normal_eq_iterated (N := Subgroup.map (Subgroup.subtype _) (Subgroup.center N)) ⟨g, by simpa using hg⟩ (gamma ^ (n)) (m)
--     unfold iteratedCommutator at foo
--     simp only [] at foo
--     simp_rw [← foo]
--     rw [← Subgroup.mem_map_iff_mem (f := Subgroup.subtype _)]
--     . simp
--     . exact Subgroup.subtype_injective N

--   have mem_torsion: ⟨_, (mem_center (n_prod * K) m)⟩ ∈ CommGroup.torsion ↥(Subgroup.center ↥N) := by
--     rw [← QuotientGroup.eq_one_iff]
--     apply_fun center_quot_equiv ∘ Additive.ofMul
--     .
--       conv =>
--         lhs
--         equals (-1)^(m) * ((((gamma_int ^ (n_prod * K)) - 1)^(m)) (center_quot_equiv (Additive.ofMul (QuotientGroup.mk (⟨_, hg⟩))))) =>

--           apply_fun center_quot_equiv.symm
--           .
--             simp
--             clear hm
--             induction m with
--             | zero =>
--               simp [Bracket.bracket]
--               -- apply_fun center_quot_equiv ∘ (Additive.ofMul)
--               -- .
--               --   simp [-EmbeddingLike.apply_eq_iff_eq]
--               --   conv =>
--               --     lhs
--               --     arg 2
--               --     arg 2
--               --     arg 1
--               --     equals ⟨g, hg⟩ * ⟨⟨gamma ^ (n_prod * K) * (↑g)⁻¹ * (gamma ^ (n_prod * K))⁻¹, (by
--               --       have foo := N_normal.conj_mem g⁻¹ (by simp) (gamma ^ (n_prod * K))
--               --       exact foo
--               --     )⟩, (by
--               --       let map_normal: (Subgroup.map (Subgroup.subtype _) (Subgroup.center N)).Normal := by
--               --         infer_instance

--               --       have foo := map_normal.conj_mem g⁻¹ (by simp [hg]) (gamma ^ (n_prod * K))
--               --       simp at foo
--               --       obtain ⟨mem_N, mem_center⟩ := foo
--               --       exact mem_center
--               --     )⟩ =>
--               --       simp
--               --       rw [Subtype.ext_iff]
--               --       simp
--               --       group
--               --   rw [QuotientGroup.mk_mul]
--               --   rw [ofMul_mul]
--               --   rw [LinearEquiv.map_add]
--               --   conv =>
--               --     rhs
--               --     arg 2
--               --     arg 1
--               --     unfold Additive.ofMul
--               --   simp
--               --   rw [sub_eq_add_neg]
--               --   simp
--               --   unfold gamma_int
--               --   conv =>
--               --     rhs
--               --     arg 1
--               --     arg 1
--               --     -- TODO - extract this to a lemma and upstream to mathlib
--               --     equals center_quot_equiv.conj (add_gamma_conj ^ (n_prod * K)) =>
--               --       induction (n_prod * K) with
--               --       | zero =>
--               --         simp
--               --         conv =>
--               --           rhs
--               --           arg 2
--               --           equals LinearMap.id => rfl
--               --         simp
--               --         rfl
--               --       | succ k ih =>
--               --         rw [pow_succ']
--               --         rw [ih]
--               --         rw [pow_succ']
--               --         conv =>
--               --           rhs
--               --           pattern _ * _
--               --           equals add_gamma_conj.toLinearMap ∘ₗ (add_gamma_conj.toLinearMap ^ k) =>
--               --             rfl
--               --         rw [LinearEquiv.conj_comp]
--               --         rfl
--               --   rw [LinearEquiv.conj_apply_apply]
--               --   nth_rw 1 [← neg_one_smul (R := ℤ)]
--               --   rw [← LinearEquiv.map_smul]
--               --   rw [neg_one_smul]
--               --   congr
--               --   simp
--               --   -- TODO - investigate why this needed to be explicitly factored out and generalized over 'n'
--               --   -- for the induction proof below to work
--               --   have pow_mem_N: ∀ n, gamma ^ (n) * ↑g * gamma⁻¹ ^ (n) ∈ N := by
--               --     simp
--               --     intro n
--               --     apply N_normal.conj_mem
--               --     simp
--               --   conv =>
--               --     rhs
--               --     arg 1
--               --     arg 2
--               --     equals Additive.ofMul (QuotientGroup.mk' (CommGroup.torsion ↥(Subgroup.center ↥N)) (⟨⟨(gamma^(n_prod * K)) * g * gamma⁻¹^((n_prod * K)), (pow_mem_N _)⟩, (by
--               --       simp
--               --       norm_cast
--               --       -- TODO - deduplicate this
--               --       let map_normal: (Subgroup.map (Subgroup.subtype _) (Subgroup.center N)).Normal := by
--               --         infer_instance


--               --       have foo := map_normal.conj_mem g (by simp [hg]) (gamma ^ (n_prod * K))
--               --       simp at foo
--               --       obtain ⟨mem_N, mem_center⟩ := foo
--               --       exact mem_center
--               --     )⟩)) =>
--               --       clear * -
--               --       simp
--               --       norm_cast
--               --       -- rw[← QuotientGroup.out_eq' (a := Additive.toMul _)]
--               --       -- rw [QuotientGroup.eq]

--               --       -- congr
--               --       -- rw [Subtype.ext_iff]
--               --       -- simp
--               --       -- rw [Subtype.ext_iff]
--               --       -- simp
--               --       induction (n_prod * K) with
--               --       | zero =>
--               --         simp
--               --       | succ q ih =>
--               --         nth_rw 1 [pow_succ']
--               --         conv =>
--               --           lhs
--               --           equals (add_gamma_conj.toLinearMap) ((add_gamma_conj.toLinearMap ^ (q)) (Additive.ofMul (QuotientGroup.mk ⟨g, hg⟩))) =>
--               --             simp
--               --         rw [ih]
--               --         simp [add_gamma_conj, gamma_quot, gamma_conj, gamma_pow_conj]
--               --         group

--               --   simp
--               --   rw [← QuotientGroup.mk_inv]
--               --   congr
--               --   simp
--               --   group
--               -- .
--               --   intro a b hab
--               --   simpa using hab
--             | succ j ih =>
--               simp_rw [Function.iterate_succ']
--               simp
--               conv =>
--                 lhs
--                 equals (Additive.ofMul (QuotientGroup.mk ⟨⟨(fun x ↦ ⁅x, gamma ^ (n_prod * K)⁆)^[j] ↑g, by apply comm_mem_N⟩, by apply mem_center⟩))
--                   + (Additive.ofMul (gamma_quot ((QuotientGroup.mk ⟨⟨(fun x ↦ ⁅x, gamma ^ (n_prod * K)⁆)^[j] ↑g, by apply comm_mem_N⟩, by apply mem_center⟩)))) =>

--                   sorry

--               rw [ih]
--               apply_fun center_quot_equiv
--               .
--                 simp
--                 sorry
--               . sorry
--               -- simp [gamma_quot]
--               -- sorry
--               -- simp [Bracket.bracket]
--               -- simp [Bracket.bracket] at ih
--               -- set gamma_a := gamma ^ (n_prod * K)
--               -- sorry
--           . exact LinearEquiv.injective center_quot_equiv.symm

--       -- v * (B * v)⁻¹

--       -- v * (B * v)⁻¹ * (B * (v * (B * v)⁻¹))⁻¹
--       --

--       -- conv =>
--       --   lhs
--       --   arg 2
--       --   arg 1
--       --   arg 1
--       --   arg 1
--       --   equals ((g.val * ((gamma_pow_conj (n_prod * K)) ⟨g⁻¹, by simpa using hg⟩))^(((-1 : ℤ)^(m + 1))))^((m + 1)) =>
--       --     clear * -
--       --     -- TODO - extract this to a lemma
--       --     induction m with
--       --     | zero =>
--       --       simp [Bracket.bracket, gamma_pow_conj]
--       --       group
--       --     | succ n ih =>
--       --       rw [Function.iterate_succ']
--       --       simp only [Function.comp_apply]
--       --       simp_rw [ih]
--       --       simp [gamma_pow_conj]
--       --       simp [Bracket.bracket]
--       --       set q := (gamma ^ (n_prod * K))
--       --       set f := ((↑g * (q * (↑g)⁻¹ * q⁻¹)))
--       --       nth_rw 6 [pow_succ]
--       --       rw [pow_succ (n := n + 1)]
--       --       simp
--       --       rw [← mul_inv_rev]
--       --       rw [← pow_succ']
--       --       simp
--       --       rw [← inv_zpow]
--       --       simp
--       --       simp [gamma_pow_conj]
--       --       nth_rw 3 [pow_succ]
--       --       rw [pow_succ (a := (-1 : ℤ))]
--       --       simp
--       --       nth_rw 2 [← inv_pow]
--       --       nth_rw 4 [← inv_pow]

--       --       rw [← inv_zpow]
--       --       simp

--       --       simp
--       --       nth_rw 1 [← inv_pow]
--       --       simp
--       --       group
--       --       sorry

--       rw [← Matrix.toLin'_pow] at hm
--       conv at hm =>
--         lhs
--         arg 1
--         rhs
--         equals Matrix.toLin' 1 =>
--           simp
--           ext a
--           simp

--       rw [sub_eq_add_neg] at hm
--       conv at hm =>
--         lhs
--         arg 1
--         rhs
--         equals Matrix.toLin' (-1) =>
--           simp

--       rw [← LinearEquiv.map_add] at hm
--       rw [← Matrix.toLin'_pow] at hm
--       apply_fun (fun f => LinearMap.toMatrix' f) at hm
--       rw [LinearMap.toMatrix'_toLin'] at hm
--       simp at hm
--       unfold gamma_matrix at hm
--       conv at hm =>
--         lhs
--         equals ((gamma_int.toMatrix'^(n_prod * K) - 1)^m).map complexOfIntHom =>
--           rw [Matrix.ext_iff_mulVec]
--           intro v
--           rw [matrix_map_pow]
--           conv =>
--             pattern -1
--             equals (-1 : Matrix _ _ ℤ).map complexOfIntHom =>
--               ext i j
--               simp
--               simp [Matrix.one_apply]

--           rw [← Matrix.map_add]
--           .
--             rw [matrix_map_pow]
--             rfl
--           .
--             intro x y
--             simp




--       have gamma_int_app_zero: (LinearMap.toMatrix' gamma_int ^ (n_prod * K) - 1)^(m ) = 0 := by
--         ext i j
--         simp
--         rw [← Matrix.ext_iff] at hm
--         specialize hm i j
--         simp at hm
--         norm_cast at hm


--       have gamma_int_app_succ_zero: (LinearMap.toMatrix' gamma_int ^ (n_prod * K) - 1)^(m + 1) = 0 := by
--         rw [pow_succ]
--         simp [gamma_int_app_zero]

--       conv =>
--         lhs
--         arg 2
--         arg 1
--         equals 0 =>
--           apply_fun (fun f => LinearMap.toMatrix' f)
--           .
--             simp only [map_zero]
--             rw [← gamma_int_app_succ_zero]
--             ext i j
--             simp
--             rw [← LinearMap.toMatrix_eq_toMatrix']
--             rw [LinearMap.toMatrix_pow]
--             rw [LinearMap.toMatrix_eq_toMatrix']
--             conv =>
--               rhs
--               arg 1
--               equals LinearMap.toMatrix' ((gamma_int^(n_prod * K)) - 1) =>
--                 ext i j
--                 simp [Matrix.one_apply, Pi.single_apply]

--             rw [← LinearMap.toMatrix_eq_toMatrix']
--             rw [LinearMap.toMatrix_pow]
--             rw [LinearMap.toMatrix_eq_toMatrix']
--             simp
--             sorry
--           .
--             intro a b hab
--             simpa using hab


--       simp
--       -- conv =>
--       --   rhs
--       --   equals center_quot_equiv ((0 : Additive _)) => rfl
--       -- simp
--     . exact LinearEquiv.injective center_quot_equiv

--   specialize comm_torsion_trivial _ mem_torsion
--   simpa using comm_torsion_trivial






--   -- let induced_gamma_aut := aut_congr gamma_conj


--   -- have induced_trivial: ∀ g: Subgroup.center N, ((induced_gamma_aut^K) (center_iso g)).snd = 1 := by
--   --   intro g
--   --   simp [induced_gamma_aut, aut_congr]
--   --   --rw [← MonoidHom.map_pow]

--   --   simp [K]
--   --   sorry

--   -- -- let induced_snd_aut: MulAut (((i : I) → Multiplicative (ZMod (I_pow i ^ K_map i)))) := {
--   -- --   toFun := fun a => aut_congr gamma_conj
--   -- -- }

--   -- --let center_aut_fst := (MonoidHom.fst _ _).comp aut_congr.toMonoidHom

--   -- have gamma_snd_trivial: ∀ g: Subgroup.center N, (center_iso g^K).snd = 1 := by
--   --   intro g
--   --   simp [K]



--   -- have map_pow_hom: ∀ p, (((MulAut.congr center_iso).toMonoidHom (aut_congr.symm.toMonoidHom ((new_conj)^(ord_fin)))).toMonoidHom p).fst = p.fst := by
--   --   intro p
--   --   rw [MonoidHom.map_pow]
--   --   rw [MonoidHom.map_pow]
--   --   have my_prod := MonoidHom.prod_unique (f := (MulEquiv.toMonoidHom ((MulAut.congr center_iso).toMonoidHom (aut_congr.symm.toMonoidHom new_conj) ^ ord_fin)))
--   --   have my_coprod := MonoidHom.coprod_unique (f := (MulEquiv.toMonoidHom ((MulAut.congr center_iso).toMonoidHom (aut_congr.symm.toMonoidHom new_conj) ^ ord_fin)))
--   --   rw [← my_coprod]
--   --   rw [MonoidHom.coprod_apply]
--   --   simp
--   --   -- rw [MonoidHom.prod_apply]
--   --   -- -- rw [MonoidHom.comp_apply]
--   --   -- -- rw [MonoidHom.comp_apply]
--   --   -- -- simp only [MonoidHom.inr_apply, MonoidHom.inl_apply]
--   --   -- rw [← my_prod]
--   --   -- rw [MonoidHom.prod_apply]
--   --   -- rw [MonoidHom.comp_apply]
--   --   -- rw [MonoidHom.comp_apply]
--   --   -- simp
--   --   -- unfold MulAut

--   --   -- rw [MulEquiv.toMonoidHom_eq_coe]
--   --   -- rw [MonoidHom.coe_coe]

--   --   -- rw [MonoidHom.pow_map]

--   --   -- simp
--   --   -- dsimp only [ord_fin]



--   --   sorry






--   -- have map_pow : ∃ F: ((i : I) → Multiplicative (ZMod (I_pow i ^ K_map i))), (MulAut.congr center_iso).toMonoidHom (aut_congr.symm.toMonoidHom ((new_conj)^(42))) = MonoidHom.toMulEquiv
--   --   ((MonoidHom.coprod (MonoidHom.prod sorry sorry) (MonoidHom.prod sorry (MonoidHom.id _))))
--   --   ((MonoidHom.coprod (MonoidHom.prod sorry sorry) (MonoidHom.prod sorry (MonoidHom.id _)))) sorry sorry := by

--   --   use sorry
--   --   simp

--   --   -- conv =>
--   --   --   arg 1
--   --   --   arg 2
--   --   --   equals (center_iso.toMonoidHom ((aut_congr.symm new_conj ^ ord_fin).toMonoidHom (center_iso.symm a))).1 b =>
--   --   --     simp


--   --   --simp
--   --   -- rw [MonoidHom.pow_apply]
--   --   -- rw [MonoidHom.map_pow]
--   --   -- rw [MonoidHom.map_pow]
--   --   -- ext x y
--   --   -- simp
--   --   -- have f_eq := MonoidHom.coprod_unique (f := (MulAut.congr center_iso).toMonoidHom (aut_congr.symm.toMonoidHom new_conj))




--   --   sorry



--   -- let target_aut := mulaut_fg_abelian gamma_conj
--   -- let target_hom := MonoidHom.comp (MonoidHom.fst _ _) target_aut.toMonoidHom

--   -- have foo := MonoidHom.coprod_unique target_hom

--   -- simp at ord_fin
--   --rw [Nat.card_prod] at ord_fin




--   --have conj_gamma := ((MulAut.conj gamma).toMonoidHom.restrict N).restrict (Subgroup.center N)
--   --let comp_hom := MonoidHom.comp conj_gamma center_iso.symm.toMonoidHom


lemma normal_comm_mem_right {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (a b: G) (hb: b ∈ N) :
  ⁅a, b⁆ ∈ N := by

  dsimp [Bracket.bracket]
  have conj_mem := N_normal.conj_mem b (by simp [hb]) a
  conv =>
    arg 2
    equals (a * b * a⁻¹) * b⁻¹ => group

  apply Subgroup.mul_mem
  . exact conj_mem
  . simpa using hb

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
    have prev_cur_mem_N := Subgroup.lowerCentralSeries_le_self N _ prev.pos_first
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
      exact Subgroup.lowerCentralSeries_le_self N _ prev.pos_first
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


-- lemma nilpotent_of_comm_trivial {G: Type*} [Group G] (S: Set G) (n: ℕ) (hS: iterate_comm_set S n = {1}):
--   ∃ k: ℕ, lowerCentralSeries (Subgroup.closure S) k = ⊥ := by
--   induction n with
--   | zero =>
--     use 0
--     simp
--     simp [iterate_comm_set] at hS
--     ext a
--     simp
--     have closure_eq: Subgroup.closure S = Subgroup.closure {1} := by
--       rw [hS]

--     simp at closure_eq
--     rw [Subgroup.closure_singleton_one] at closure_eq
--     have a_mem := a.property
--     simp_rw [closure_eq] at a_mem
--     simp at a_mem
--     exact a_mem
--   | succ n ih =>
--     sorry

-- lemma RepeatComm_eventually_le {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (a b: ℕ):
--   ∃ n: ℕ, a ≤ (RepeatComm_min N_normal gamma_alpha n).fst ∨ b ≤ (RepeatComm_min N_normal gamma_alpha n).snd := by

--   have unbounded := prod_lex_has_unbounded (RepeatComm_min_strict_mono N_normal gamma_alpha)
--   -- TODO - deduplicate most of these cases
--   cases unbounded
--   .
--     rename_i fst_unbounded
--     rw [not_bddAbove_iff] at fst_unbounded
--     specialize fst_unbounded a
--     obtain ⟨n, hn⟩ := fst_unbounded
--     simp at hn
--     obtain ⟨⟨c, c_eq⟩, a_lt_n⟩ := hn
--     use c
--     left
--     rw [c_eq]
--     exact Nat.le_of_succ_le a_lt_n
--   .
--     rename_i snd_unbounded
--     rw [not_bddAbove_iff] at snd_unbounded
--     specialize snd_unbounded b
--     obtain ⟨n, hn⟩ := snd_unbounded
--     simp at hn
--     obtain ⟨⟨c, c_eq⟩, b_lt_n⟩ := hn
--     use c
--     right
--     rw [c_eq]
--     exact Nat.le_of_succ_le b_lt_n

lemma iterated_mem_iterated_set {G: Type*} [DecidableEq G] [Group G] (base right: G) (S: Finset G) (base_mem: base ∈ S) (right_mem: right ∈ S) (n: ℕ): iteratedCommutator base right n ∈ iterate_comm_set S n := by
  induction n with
  | zero =>
    simp [iterate_comm_set, iteratedCommutator]
    exact base_mem
  | succ n ih =>
    conv =>
      arg 2
      equals ⁅iteratedCommutator base right n, right⁆ =>
        unfold iteratedCommutator
        rw [Function.iterate_succ']
        simp

    simp [iterate_comm_set]
    use right
    refine ⟨right_mem, ?_⟩
    use iteratedCommutator base right n

lemma one_mem_iterated_comm {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (n m: ℕ) (hn: n ≤ m) (hS: 1 ∈ iterate_comm_set S n):
    1 ∈ iterate_comm_set S m := by

  classical
  induction m, hn using Nat.le_induction with
  | base => exact hS
  | succ n hmn ih =>
    simp [iterate_comm_set]
    by_cases S_empty: S = ∅
    .
      simp [S_empty] at ih
      unfold iterate_comm_set at ih
      simp at ih
      split at ih
      . simp at ih
      . simp at ih
    have S_nonempty: S.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr S_empty
    rw [Finset.nonempty_def] at S_nonempty
    obtain ⟨s, s_mem⟩ := S_nonempty
    use s
    refine ⟨s_mem, ?_⟩
    use 1
    refine ⟨ih, ?_⟩
    simp

lemma comm_subgroup_mem {G: Type*} [DecidableEq G] [Group G] {H: Subgroup G} (S: Finset H) (n: ℕ):
  ↑(iterate_comm_set (Finset.image H.subtype  S) n) ⊆ (H: Set G) := by
    induction n with
    | zero =>
      simp [iterate_comm_set]
      intro h h_mem
      simp
    | succ n ih =>
      simp [iterate_comm_set]
      intro h h_mem h_mem_s
      intro a ha
      simp
      have a_mem := ih ha
      simp [Bracket.bracket]
      apply Subgroup.mul_mem
      . apply Subgroup.mul_mem
        . apply Subgroup.mul_mem
          . exact a_mem
          . exact h_mem
        . simp
          exact a_mem
      . simp
        exact h_mem


lemma iterate_comm_subgroup {G: Type*} [DecidableEq G] [Group G] {H: Subgroup G} (S: Finset H) (h: H) (n: ℕ):
  h ∈ (iterate_comm_set S n) ↔ h.val ∈ iterate_comm_set (Finset.image H.subtype S) n := by
    induction n generalizing h with
    | zero =>
      simp [iterate_comm_set]
    | succ n ih =>
      dsimp [iterate_comm_set]
      simp
      refine ⟨?_, ?_⟩
      .
        intro h_mem
        obtain ⟨b, b_mem, ⟨b_mem_S, a, h_eq⟩⟩ := h_mem
        obtain ⟨a_mem_h, a_mem_comm, h_eq_comm⟩ := h_eq
        use b
        use ?_
        . use a
          refine ⟨?_, ?_⟩
          .
            rw [ih] at a_mem_comm
            simp at a_mem_comm
            exact a_mem_comm
          . rw [← h_eq_comm]
            simp [Bracket.bracket]
        . use b_mem
      . intro data_mem
        obtain ⟨b, ⟨b_mem_H, b_mem_S⟩, ⟨a, a_mem_comm, h_eq⟩⟩ := data_mem
        use b
        use b_mem_H
        refine ⟨?_, ?_⟩
        . exact b_mem_S
        . use a
          use ?_
          . refine ⟨?_, ?_⟩
            .
              rw [ih]
              simp
              exact a_mem_comm
            .
              ext
              rw [← h_eq]
              simp [Bracket.bracket]
          .
            simp [Bracket.bracket] at h_eq
            have iterate_subset := comm_subgroup_mem S n a_mem_comm
            simpa using iterate_subset


-- TODO - upstream to mathlib
lemma list_foldr_replicate (A: Type*) (a b: A) (n: ℕ) (f: A → A → A) :
    List.foldr f a (List.replicate n b) = Nat.iterate (f b) n a := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [List.replicate_succ]
    rw [List.foldr_cons]
    rw [ih]
    rw [Function.iterate_succ']
    rfl

lemma list_fold_comm_one {G: Type*} [Group G] (l: List G) :
    List.foldr (fun x y => ⁅y, x⁆) (1 : G) l = 1 := by
  induction l with
  | nil =>
    simp
  | cons head tail ih =>
    simp only [List.foldr_cons]
    rw [ih]
    simp

lemma nat_iterate_comm_one (G: Type*) [Group G] (g: G) (n: ℕ):
    (Nat.iterate (fun x => ⁅x, g⁆) n 1) = 1 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ']
    simp
    rw [ih]
    simp

-- TODO - why can't linarith or omega find this?
lemma nat_le_mul (a n: ℕ) (hn: n ≠ 0): a ≤ n * a := by
  conv =>
    arg 1
    equals 1 * a =>
      simp

  apply Nat.mul_le_mul
  . omega
  . simp

-- List.countP (fun a ↦ !decide (↑a = gamma_alpha)) l
lemma count_mem_group_implies_lowercentral {G: Type*} [Group G] {N': Subgroup G} [∀ a: G, Decidable (a ∈ N')] (N'_normal: N'.Normal) (l: List G) (g: G)
    (l_nonempty: l ≠ []) (count_ne_zero: (l.countP (fun a => decide (a ∈ N'))) ≠ 0):
    l.foldr (fun acc s ↦ ⁅s, acc⁆) g ∈ Subgroup.lowerCentralSeries N' ((l.countP (fun a => decide (a ∈ N'))) - 1) := by

  induction l with
  | nil =>
    simp at l_nonempty
  | cons head tail ih =>
    by_cases head_in_N': head ∈ N'
    .
      simp only [List.countP_cons, List.foldr_cons, head_in_N', decide_true, if_true,
        Nat.add_sub_cancel]
      by_cases tail_empty: tail = []
      .
        simp [tail_empty]
        apply normal_comm_mem_right N'_normal
        exact head_in_N'
      .

        by_cases count_eq_zero: (tail.countP (fun a => decide (a ∈ N'))) = 0
        .
          simp [count_eq_zero]
          apply normal_comm_mem_right N'_normal
          exact head_in_N'
        .
          have count_sub_eq: (tail.countP (fun a => decide (a ∈ N'))) = (tail.countP (fun a => decide (a ∈ N'))) - 1 + 1 := by
            omega

          rw [count_sub_eq]
          specialize ih (by simpa using tail_empty) count_eq_zero
          exact Subgroup.commutator_mem_commutator ih head_in_N'
    . rw [List.countP_cons]
      simp only [head_in_N', decide_false, Bool.false_eq_true, ↓reduceIte]


      have tail_nonempty: tail ≠ [] := by
        by_contra!
        simp [this] at count_ne_zero
        contradiction

      rw [List.countP_cons] at count_ne_zero
      simp only [head_in_N', decide_false, Bool.false_eq_true, ↓reduceIte] at count_ne_zero
      rw [add_zero] at count_ne_zero
      specialize ih tail_nonempty count_ne_zero
      rw [List.foldr_cons]
      apply normal_comm_mem
      . infer_instance
      . exact ih


#print axioms count_mem_group_implies_lowercentral
  -- induction l using Nat.strongRecMeasure (f := (l.countP (fun a => decide (a ∈ N'))))
  -- case ind p ih =>

  --   sorry

  -- rw [Group.isNilpotent_iff]
  -- rw [Group.isNilpotent_iff] at hG
  -- obtain ⟨n, hn⟩ := hG
  -- use n
  -- induction n with
  -- | zero =>
  --   simp
  --   simp at hn
  --   sorry
  -- | succ n ih =>
  --   rw [Subgroup.eq_top_iff']
  --   intro x
  --   rw [mem_upperCentralSeries_succ_iff]
  --   intro y
  --   rw [Subgroup.eq_top_iff'] at hn
  --   have x_prop := x.property
  --   rw [Subgroup.mem_map] at x_prop
  --   obtain ⟨a, a_mem, x_eq⟩ := x_prop
  --   specialize hn ⟨a, a_mem⟩
  --   rw [mem_upperCentralSeries_succ_iff] at hn
  --   have y_prop := y.property
  --   have x_prop := x.property
  --   rw [Subgroup.mem_map] at y_prop
  --   obtain ⟨b, b_mem, y_eq⟩ := y_prop
  --   specialize hn ⟨b, b_mem⟩
  --   simp at hn
  --   rw [← Subgroup.mem_map_iff_mem (f := f.comp (Subgroup.subtype _)) (by sorry)] at hn



  --   sorry
  -- apply_fun (Subgroup.map (Subgroup.subtype _)) at hn
  -- use n
  -- sorry

-- `Subgroup.map_toSubmonoid` rewrites the `.carrier` predicate of `Subgroup.map`, which breaks the
-- `unattach`/commutator rewrites below. Disable it for this proof.
-- `Subgroup.coe_subtype` rewrites `⇑H.subtype` to `Subtype.val`, which desynchronises the index
-- type `↥(Finset.image (⇑H.subtype) S ∪ {gamma_alpha})` of `l`/`gamma_list` from the goal and makes
-- the `rw`s below fail on a motive that is only defeq at default transparency. Disable it too.
attribute [-simp] Subgroup.map_toSubmonoid Subgroup.coe_subtype in
lemma unipotent_commutator_trivial {G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) {N': Subgroup H} [H_normal: H.Normal] [N'_char: N'.Characteristic] [N'_nilpotent: Group.IsNilpotent N'] (gamma_alpha: G) (gamma_not_n: ¬(gamma_alpha ∈ (Subgroup.map (Subgroup.subtype _) N'))) (m: ℕ)
  (h_gamma_alpha: ∀ g ∈ N', iteratedCommutator g.val gamma_alpha m = 1)
  (S: Finset H) (hS: Subgroup.closure S = N'):
  Group.IsNilpotent (Subgroup.closure ((Finset.image (Subgroup.subtype _) S) ∪ {gamma_alpha})) := by

  classical

  by_cases m_eq: m = 0
  .
    simp [iteratedCommutator, m_eq] at h_gamma_alpha
    have N'_bot: N' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      simpa using h_gamma_alpha

    --rw [N'_bot]

    let foo := Subgroup.closureCommGroupOfComm (k := (↑(Finset.image (⇑H.subtype) S) ∪ {gamma_alpha})) ?_
    .

      apply CommGroup.isNilpotent
    . intro x hx y hy
      by_cases S_empty: S = ∅
      . simp [S_empty] at hx hy
        grind
      .
        have S_eq: S = {1} := by
          simp only [N'_bot, Subgroup.closure_eq_bot_iff] at hS
          have S_subset: S ⊆ {1} := by
            grind
          grind
        simp [S_eq] at hx hy
        aesop
  -- `S` generates `N'`, so it lands inside `N'`, and its image inside `Subgroup.map H.subtype N'`.
  have S_sub_N': ∀ y ∈ S, y ∈ N' := by
    intro y hy
    rw [← hS]
    exact Subgroup.subset_closure hy
  have image_sub_map: ∀ g ∈ Finset.image (⇑H.subtype) S, g ∈ Subgroup.map H.subtype N' := by
    intro g hg
    rw [Finset.mem_image] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨y, S_sub_N' y hy, rfl⟩

  have nilpotent_map: Group.IsNilpotent ↥(Subgroup.map H.subtype N') := by
    apply map_nilpotent
    . exact Subgroup.subtype_injective H
    . exact N'_nilpotent

  rw [nilpotent_iff_lowerCentralSeries]
  use ((1 + (Group.nilpotencyClass ↥(Subgroup.map H.subtype N'))) * (m + 1)) + 2

  apply comm_trivial_implies_nilpotent (S := Finset.image (fun (a: ↑((Finset.image (Subgroup.subtype _) S) ∪ {gamma_alpha})) => ⟨a.val, by (
    apply Subgroup.mem_closure_of_mem
    have a_prop := a.property
    simp at a_prop
    simp
    exact a_prop
  )⟩) Finset.univ)
  .


    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply Subgroup.map_injective (Subgroup.subtype_injective _)
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      have h := y.property
      rw [Finset.mem_union] at h
      rcases h with h | h
      · exact Set.mem_union_left _ h
      · exact Set.mem_union_right _ (Finset.mem_singleton.mp h)
    · intro hg
      exact ⟨⟨g, by apply Subgroup.mem_closure_of_mem; exact hg⟩,
        ⟨⟨g, by simpa using hg⟩, rfl⟩, rfl⟩
  .
    ext a
    rw [iterate_comm_subgroup]

    -- The image of the attached generating set back down into `G` is the original
    -- `Finset.image H.subtype S ∪ {gamma_alpha}`.
    conv =>
      arg 1
      arg 1
      arg 1
      equals (Finset.image (⇑H.subtype) S) ∪ {gamma_alpha} =>
        rw [Finset.image_image, Finset.univ_eq_attach]
        exact Finset.attach_image_val

    refine ⟨?_, ?_⟩
    .
      intro a_mem
      rw [← Finset.mem_coe] at a_mem
      rw [iterate_comm_set_eq_fold] at a_mem
      simp only [Set.mem_setOf_eq] at a_mem
      obtain ⟨s, l, l_length, a_eq⟩ := a_mem

      -- TODO - extract this to its own lemma
      have subsequent_comm_one: ∀ g: N', ∀ k: ℕ, m ≤ k → iteratedCommutator g.val.val gamma_alpha k = 1 := by
        intro g k hk
        simp [iteratedCommutator]

        apply Nat.le.dest at hk
        obtain ⟨t, ht⟩ := hk
        rw [← ht]
        rw [Function.iterate_add_apply]
        simp [iteratedCommutator] at h_gamma_alpha

        -- Use the fact that N' is invariant to conjugation by gamma
        have comm_in_H: ∀ t: ℕ, (fun x ↦ ⁅x, gamma_alpha⁆)^[t] g ∈ H := by
          clear ht
          intro t
          induction t with
          | zero =>
            simp
          | succ t ih =>
            rw [Function.iterate_succ']
            simp
            apply normal_comm_mem
            . infer_instance
            . exact ih

        have comm_in_N': (fun x ↦ ⁅x, gamma_alpha⁆)^[t] g ∈ (Subgroup.map (Subgroup.subtype _) N') := by
          clear ht
          induction t with
          | zero =>
            simpa using g_mem
          | succ t ih =>
            simp_rw [Function.iterate_succ']
            simp only [Function.comp_apply, Subgroup.subtype_apply,
              Subtype.exists, exists_and_right, exists_eq_right]
            apply normal_comm_mem
            .
              infer_instance
            . exact ih

        simp at comm_in_N'
        obtain ⟨foo, bar⟩ := comm_in_N'
        specialize h_gamma_alpha _ (comm_in_H _) bar
        rw [h_gamma_alpha]


      have adjacent_or_count := list_adjacent_elements l (fun x => decide (x = gamma_alpha)) (m + 1)
      rw [l_length] at adjacent_or_count
      cases adjacent_or_count
      .
        rename_i adjancent_gamma
        obtain ⟨gamma_list, h_gamma_list, gamma_list_len, eq_gamma_alpha⟩ := adjancent_gamma

        have eq_gamma_alpha_unattach: ∀ b ∈ gamma_list.unattach, b = gamma_alpha := by
          intro b hb
          rw [List.mem_unattach] at hb
          obtain ⟨b_mem, other⟩ := hb
          specialize eq_gamma_alpha _ other
          simp at eq_gamma_alpha
          exact eq_gamma_alpha


        -- TODO - why isn't there List.ext for a ∈ l ?
        have gamma_list_eq: gamma_list.unattach = List.replicate gamma_list.unattach.length gamma_alpha := by
          apply List.eq_replicate_of_mem
          intro b hb
          specialize eq_gamma_alpha_unattach b hb
          simp at eq_gamma_alpha
          grind



        refine Finset.mem_singleton.mpr ?_
        ext
        rw [← a_eq]
        rw [List.IsInfix] at h_gamma_list
        obtain ⟨l_prefix, l_suffix, h_list_eq⟩ := h_gamma_list
        rw [← h_list_eq]
        simp only [List.unattach_append, List.foldr_append, OneMemClass.coe_one]
        rw [gamma_list_eq]
        rw [list_foldr_replicate]
        unfold iteratedCommutator at h_gamma_alpha
        unfold iteratedCommutator at subsequent_comm_one
        simp [] at subsequent_comm_one

          --simp [l_suffix_nil]

        have s_mem := s.property
        rw [Finset.mem_union] at s_mem
        cases s_mem
        . rename_i s_mem_N'
          rw [subsequent_comm_one]
          . rw [list_fold_comm_one]
          .
            clear h_list_eq
            induction l_suffix with
            | nil =>
              simp at s_mem_N'
              obtain ⟨hs, s_mem⟩ := s_mem_N'
              simp
              exact hs
            | cons head tail ih =>
              simp
              apply normal_comm_mem
              . infer_instance
              . exact ih
          .
            clear h_list_eq
            rw [← Subgroup.mem_map_iff_mem (f := H.subtype) (Subgroup.subtype_injective H)]
            induction l_suffix with
            | nil =>
              simp at s_mem_N'
              obtain ⟨hs, s_mem⟩ := s_mem_N'
              simp
              use hs
              rw [← hS]
              exact Subgroup.subset_closure s_mem
            | cons head tail ih =>
              simp [-Subgroup.mem_map]
              apply normal_comm_mem (by infer_instance)
              exact ih
          . rw [List.length_unattach]
            omega
        .
          rename_i s_eq_gamma
          simp at s_eq_gamma
          rw [s_eq_gamma]

          have gamma_len_eq: gamma_list.unattach.length = gamma_list.unattach.length - 1 + 1 := by
            rw [List.length_unattach]
            omega

          rw [gamma_len_eq]
          simp

          clear h_list_eq

          -- TODO - this can be simplified a lot
          have fold_mem: ⁅List.foldr (fun acc s ↦ ⁅s, acc⁆) gamma_alpha l_suffix.unattach, gamma_alpha⁆ ∈ (((Subgroup.map (Subgroup.subtype _) N').carrier ∪ {gamma_alpha}) : Set G) := by
            induction l_suffix with
            | nil =>
              simp
            | cons head tail ih =>
              have head_prop := head.prop
              rw [Finset.mem_union] at head_prop

              cases head_prop
              .
                rename_i head_in_N
                rw [Set.mem_union] at ih
                apply Set.mem_union_left
                apply normal_comm_mem (by infer_instance)
                apply normal_comm_mem_right (by infer_instance)
                exact image_sub_map _ head_in_N
              . rename_i head_gamma
                simp at head_gamma
                --rw [head_gamma]
                cases ih
                . rename_i left
                  simp only [List.unattach_cons, List.foldr_cons]
                  rw [head_gamma]
                  apply Set.mem_union_left
                  apply normal_comm_mem (by infer_instance)
                  exact left
                .
                  rename_i right
                  apply Set.mem_union_left
                  simp at right
                  simp only [List.unattach_cons, List.foldr_cons]
                  rw [head_gamma]
                  rw [right]
                  simp

          rw [Set.mem_union] at fold_mem
          cases fold_mem
          . rename_i fold_in_N
            simp at fold_in_N
            rw [subsequent_comm_one]
            . rw [list_fold_comm_one]
            .
              obtain ⟨foo, bar⟩ := fold_in_N
              exact foo
            . obtain ⟨foo, bar⟩ := fold_in_N
              exact bar
            . omega
          . rename_i fold_eq_gamma
            simp at fold_eq_gamma
            rw [fold_eq_gamma]


            have gamma_sub_sub: gamma_list.length - 1 = gamma_list.length - 1 - 1 + 1 := by omega
            rw [gamma_sub_sub]
            rw [Function.iterate_succ]
            simp
            rw [nat_iterate_comm_one]
            rw [list_fold_comm_one]

      .
        rename_i count_not_gamma
        simp at count_not_gamma
        rw [mul_comm] at count_not_gamma
        rw [Nat.mul_add_div] at count_not_gamma
        rw [Nat.div_eq_of_lt] at count_not_gamma
        . simp at count_not_gamma

          refine Finset.mem_singleton.mpr ?_
          ext
          rw [← a_eq]

          conv at count_not_gamma =>
            arg 2
            arg 1
            equals (fun (a: ↥(Finset.image (⇑H.subtype) S ∪ {gamma_alpha})) => decide (a.val ∈ (((Subgroup.map (Subgroup.subtype _) N'))))) =>
              ext x
              simp
              rw [← decide_not]
              congr
              simp
              refine ⟨?_, ?_⟩
              . intro hx other
                rw [← hx] at gamma_not_n
                simp at gamma_not_n
                apply gamma_not_n other
              . intro hx
                have x_prop := x.prop
                rw [Finset.mem_union] at x_prop
                simp [hx] at x_prop
                cases x_prop
                . rename_i mem_N'
                  obtain ⟨mem_H, mem_N⟩ := mem_N'
                  exact absurd (S_sub_N' _ mem_N) (hx mem_H)
                . rename_i x_eq
                  exact x_eq


          rw [add_comm] at count_not_gamma

          conv at count_not_gamma =>
            arg 2
            -- TODO - clean up and upstream to mathlib
            equals l.unattach.countP (fun a => decide (a ∈ (((Subgroup.map (Subgroup.subtype _) N'))))) =>
              clear count_not_gamma l_length a_eq
              rw [show l.unattach = l.map (·.val) from rfl, List.countP_map]; rfl


          have foo := count_mem_group_implies_lowercentral (N' := (Subgroup.map H.subtype N')) (by infer_instance) l.unattach s ?_ ?_
          .
            rw [Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le (by omega)] at foo
            simpa using foo

          .
            -- TODO - this is ridiculously overcomplicated
            have l_nonempty: l ≠ [] := by
              grind

            have l_len_ne: l.length ≠ 0 := by
              omega

            have l_unattach_len_ne: l.unattach.length ≠ 0 := by
              rw [List.length_unattach]
              exact l_len_ne

            grind
          . omega
        . omega
        . omega
    .
      intro a_eq
      replace a_eq : a = 1 := Finset.mem_singleton.mp a_eq
      -- `S` need not contain `1`, so start the iterated commutator at `gamma_alpha`
      -- instead: `⁅gamma_alpha, gamma_alpha⁆ = 1`, and the remaining iterations stay at `1`.
      have iterate_mem := iterated_mem_iterated_set gamma_alpha gamma_alpha
        (Finset.image (⇑H.subtype) S ∪ {gamma_alpha}) (by simp) (by simp)
        ((1 + ((Group.nilpotencyClass ↥(Subgroup.map H.subtype N')))) * (m + 1) + 2)
      have comm_one : iteratedCommutator gamma_alpha gamma_alpha
          ((1 + ((Group.nilpotencyClass ↥(Subgroup.map H.subtype N')))) * (m + 1) + 2) = 1 := by
        unfold iteratedCommutator
        rw [Function.iterate_add_apply]
        simp [nat_iterate_comm_one]
      rw [comm_one] at iterate_mem
      rw [a_eq]
      simpa using iterate_mem

#print axioms unipotent_commutator_trivial




-- TODO - this theorem statement is wrong
lemma lowerCentralSeriefs_bracket_pow {G: Type*} [DecidableEq G] [Group G] {N: Subgroup G} [hN: N.Normal]
  (base: N) (right: G) (k n: ℕ) :
    (iteratedCommutatorNormal base (right^n) k) ∈ (⊤ : Subgroup (↥N)).lowerCentralSeries k := by

  induction k with
  | zero =>
    simp
  | succ k ih =>



    rw [iteratedCommutatorNormal]
    rw [Function.iterate_succ']
    simp
    rw [← Subgroup.mem_map_iff_mem (f := N.subtype) (by exact Subgroup.subtype_injective N)]
    conv =>
      arg 2
      simp

    -- nth_rw 1 [Bracket.bracket]
    -- nth_rw 1 [commutatorElement]
    -- simp only []
    -- nth_rw 1 [mul_assoc]
    -- nth_rw 1 [mul_assoc]
    simp
    -- rw [← iterate_comm_generates (S := Set.univ) (hS := by simp)]
    -- rw [iterate_comm_set_eq_fold]
    -- rw [Subgroup.normalClosure]
    -- simp
    use ?_
    .
      --rw [← iterate_comm_generates (S := Finset.univ) (hS := by simp)]

      --apply Subgroup.mem_closure_of_mem
      sorry
      -- simp
      -- use iteratedCommutatorNormal base (right ^ n) k
      -- use ?_
      -- .
      --   refine ⟨?_, ?_⟩
      --   . simpa using ih
      --   .
      -- . simp
    .
      apply normal_comm_mem hN
      simp
    -- rw [Subgroup.mem_map]

    -- apply Subgroup.mem_closure_of_mem
    -- rw [Group.conjugatesOfSet]
    -- rw [Set.mem_iUnion]
    -- use (iteratedCommutatorNormal base (right^n) k)
    -- simp


    -- rw [mem_lowerCentralSeries_succ_iff]

    --   sorry
    -- rw [Bracket.bracket]

    --. sorry

    -- induction a with
    -- | zero =>
    --   simp [iteratedCommutatorNormal] at h_lower
    --   simp [iteratedCommutatorNormal]
    --   exact h_lower
    -- | succ a ih_a =>
    --   rw [iteratedCommutatorNormal]
    --   rw [Function.iterate_succ']
    --   simp
    --   rw [← Subgroup.mem_map_iff_mem (f := N.subtype) (by exact Subgroup.subtype_injective N)]
    --   conv =>
    --     arg 2
    --     simp

    --   nth_rw 1 [Bracket.bracket]
    --   nth_rw 1 [commutatorElement]
    --   simp only []
    --   nth_rw 1 [mul_assoc]
    --   nth_rw 1 [mul_assoc]
    --   apply Subgroup.mul_mem
    --   .

    --     sorry
    --   . sorry




    -- induction m with
    -- | zero =>
    --   simp [iteratedCommutatorNormal]
    --   conv =>
    --     arg 2
    --     equals 1 =>
    --       sorry

    --   simp

    -- | succ m ih_m =>

    --   sorry

-- lemma iterated_comm_normal_eq_one_of_le {T: Type*} [Group T] {N: Subgroup T} [hN: N.Normal] (base: N) (right: T)
--     (n m k: ℕ) (hm: n ≤ m) (h_eq_one: iteratedCommutatorNormal base (right^n) k = 1): iteratedCommutatorNormal base (right^m) k = 1 := by

--   induction m with
--   | zero =>
--     simp [iteratedCommutatorNormal]
--     simp at hm
--     simp [hm] at h_eq_one
--     simp [iteratedCommutatorNormal] at h_eq_one
--     exact h_eq_one
--   | succ a ih =>
--     rw [Subtype.ext_iff]
--     rw [iterated_comm_normal_eq_iterated]
--     rw [iteratedCommutator]
--     simp [Bracket.bracket]

--     rw [Function.iterate_succ']
--     simp
--     simp
--     have prev := ih n (by omega)

--     sorry


-- lemma gamma_pow_unipotent {G: Type*} [Group G] {N': Subgroup G} (N'_normal: N'.Normal) (N'_nilpotent: Group.IsNilpotent N'):
--     ∃ gamma: G, ∃ a : ℕ, ∃ m: ℕ, ∀ g : N', iteratedCommutatorNormal g (gamma^a) m = 1 := by


--   obtain ⟨n, h⟩ : ∃ n, Group.nilpotencyClass N' = n := ⟨_, rfl⟩
--   have class_le_ne: Group.nilpotencyClass N' ≤ n := by
--     omega
--   clear h
--   induction n generalizing G with
--   | zero =>
--     simp at class_le_ne
--     rw [nilpotencyClass_zero_iff_subsingleton] at class_le_ne
--     use 1
--     use 1
--     use 1
--     intro g

--     have g_eq_one: g = 1 := by
--       sorry

--     simp [iteratedCommutatorNormal, g_eq_one]
--   | succ n ih =>



--     have hn : Group.nilpotencyClass (N' ⧸ Subgroup.center N') ≤ n := by
--       simp [nilpotencyClass_quotient_center]
--       exact class_le_ne


--     let a := QuotientGroup.mk' (Subgroup.center N')
--     let N_mod_Z := (Subgroup.comap (QuotientGroup.mk' (Subgroup.center N')) ⊤)

--     let prev_nilpotent := ih (N' := N_mod_Z) (by infer_instance) (by infer_instance) (by
--       simp [N_mod_Z]
--       sorry

--     -- This is not actually a homomorphism because map_one' is false
--       -- let f : (N' ⧸ Subgroup.center N') →* (Subgroup.comap (QuotientGroup.mk' (Subgroup.center ↥N')) ⊤) := {
--       --   toFun := fun x => ⟨x.out, by
--       --     simp
--       --   ⟩
--       --   map_one' := by
--       --     simp
--       --   map_mul' := _
--       -- }

--       -- have foo := nilpotencyClass_le_of_surjective f (sorry)
--       -- grw [foo]
--       -- exact hn
--     )
--     obtain ⟨gamma, a, m, prev_comm⟩ := prev_nilpotent

--     have gamma_unipotent_center: ∃ m', ∃ z, ∀ g ∈ (Subgroup.center N'), iteratedCommutatorNormal g (gamma^m') z = 1 := by
--       sorry

--     obtain ⟨m', z, hz⟩ := gamma_unipotent_center
--     use gamma
--     use a
--     use (z + m)
--     intro g
--     specialize prev_comm ⟨g, by simp [N_mod_Z]⟩

--     rw [Subtype.ext_iff] at prev_comm
--     apply_fun (QuotientGroup.mk' (Subgroup.center ↥N')) at prev_comm
--     simp at prev_comm

--     rw [Subtype.ext_iff]
--     rw [iterated_comm_normal_eq_iterated]
--     simp [iteratedCommutator]
--     rw [Function.iterate_add_apply]


--     have double_comm := hz _ prev_comm
--     rw [iterated_comm_normal_eq_iterated] at double_comm
--     rw [Subtype.ext_iff] at double_comm
--     rw [iterated_comm_normal_eq_iterated] at double_comm
--     simp [iteratedCommutator] at double_comm




--     conv at double_comm =>
--       lhs
--       arg 3
--       equals ((fun x ↦ ⁅x, gamma.val ^ a⁆)^[m] g) =>
--         clear hz prev_comm double_comm
--         induction m generalizing g with
--         | zero =>
--           simp
--         | succ m ih =>
--           rw [Function.iterate_succ]
--           simp
--           rw [ih]
--           rfl

--     rw [← Function.iterate_add_apply] at double_comm











--     sorry

--   --have foo := nilpotent_center_quotient_ind N' (P := fun N  N_group N_nilpotent => ∃ a m, ∀ (g : N), iteratedCommutatorNormal g (gamma ^ a) m = 1)

--   induction N' using Nat.strongRecMeasure (f := Group.nilpotencyClass N')
--   case ind G_group N ih =>
--     by_cases class_zero: Group.nilpotencyClass N = 0
--     .
--       rw [nilpotencyClass_zero_iff_subsingleton] at class_zero

--       use 1
--       use 1
--       intro g

--       have g_eq_one: g = 1 := by
--         sorry

--       simp [iteratedCommutatorNormal, g_eq_one]
--     .
--       let a := QuotientGroup.mk' (Subgroup.center N)
--       let N_mod_Z := Subgroup.map (N.subtype) (Subgroup.comap (QuotientGroup.mk' (Subgroup.center N)) ⊤)
--       let prev_nilpotent := ih N_mod_Z ?_ ?_ ?_ ?_
--       .
--         obtain ⟨a, m, prev_comm⟩ := prev_nilpotent

--         have gamma_unipotent_center: ∃ z, ∀ g ∈ (Subgroup.center N), iteratedCommutator g.val (gamma^a) z ∈ Subgroup.map (N.subtype) (Subgroup.center N) := by
--           sorry

--         obtain ⟨z, hz⟩ := gamma_unipotent_center


--         use a
--         use (m + 1)
--         intro g

--         have comm_in_center := prev_comm ⟨g, by simp [N_mod_Z]⟩

--         have one_mem: (1: N_mod_Z).val ∈ N_mod_Z := by
--           simp [N_mod_Z]


--         dsimp [N_mod_Z] at one_mem
--         rw [Subgroup.mem_map] at one_mem
--         obtain ⟨x, x_mem, x_eq⟩ := one_mem




--         unfold N_mod_Z at comm_in_center
--         apply_fun (fun a => (by

--           have a_prop := a.prop
--           rw [Subgroup.mem_map] at a_prop


--         )) at comm_in_center


--         rw [Subtype.ext_iff] at comm_in_center
--         rw [Subtype.ext_iff] at comm_in_center



--         apply_fun Quotient.out at comm_in_center
--         conv at comm_in_center =>
--           equals ↑(Quotient.out _) =>
--             sorry
--         nth_rw 1 [QuotientGroup.out_eq']
--         simp at comm_in_center




-- -- This probably needs the semidirect product
-- lemma closure_mem_repeatComm {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (gamma_alpha: G) (n: ℕ):
--   ∀ g ∈ { x | ∃ p ∈ lowerCentralSeries (Subgroup.closure ↑(N.carrier ∪ {gamma_alpha})) (n), ∃ q, x = ⁅p.val, q⁆ }, ∃ data ∈ RepeatComm N_normal gamma_alpha (n + 1), g = data.cur := by

--     intro g g_mem
--     induction n with
--     | zero =>
--       simp at g_mem
--       obtain ⟨p, p_in, q, g_eq⟩ := g_mem
--       simp [RepeatComm]

--       use {
--         cur := p
--         pos := (0, 0)
--         pos_first := by
--           simp [lowerCentralSeries]
--         pos_second := by
--           simp
--       }
--       have g_prop := g.property
--       apply Subgroup.closure_induction (p := fun g hg => ∃ data ∈ RepeatComm N_normal gamma_alpha (0 + 1), g = data.cur) (k := N.carrier ∪ {gamma_alpha}) g_mem
--       .
--         rw [RepeatComm]
--         use {
--           cur := 1
--           pos := (1, 0)
--           pos_first := by
--             simp [lowerCentralSeries]
--           pos_second := by
--             simp
--         }
--         rw [Set.mem_sUnion]
--         refine ⟨?_, by simp⟩
--         simp
--         use {
--           cur := 1
--           pos := (0, 0)
--           pos_first := by
--             simp [lowerCentralSeries]
--           pos_second := by
--             simp
--         }
--         simp [RepeatComm]
--         use 1
--         use (by simp)
--         simp [G''_comm]
--         -- TODO - take this as a hypothesis
--         have gamma_alpha_ne_one: 1 ≠ gamma_alpha := by
--           sorry
--         simp [gamma_alpha_ne_one]
--       .
--         intro x y hx hy x_cur y_cur
--         rw [RepeatComm] at x_cur
--         rw [RepeatComm] at y_cur
--         obtain ⟨x_data, x_data_in, x_eq⟩ := x_cur
--         obtain ⟨y_data, y_data_in, y_eq⟩ := y_cur

--         simp [RepeatComm]


--       simp at g_mem
--       simp [RepeatComm]
--       use {
--         cur := g
--         pos := (0, 0)
--         pos_first := by
--           simp [lowerCentralSeries]
--         pos_second := by
--           simp
--       }


--     | succ k ih =>
--       sorry



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


-- [a, b] = aba⁻¹b⁻¹
-- [a, b^n] = a(b^n)a⁻¹(b^n)⁻¹
