module

public import Mathlib
public import Gromov.MatrixSubsum
public import Gromov.AbelianFg
public import Gromov.ToMathlib.GroupTheory.Closure
public import Gromov.ToMathlib.GroupTheory.Nilpotent
public import Gromov.ToMathlib.Data.List.Infix
public import Gromov.ToMathlib.Order.Prod.Lex

/-!
# Iterated commutators and the lower central series

`iteratedCommutator`, the generating sets `iterate_comm_set`, and
`lower_central_generates_succ`.
-/

public section

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

@[expose]
def iteratedCommutator {T: Type*} [Group T] (base right: T) (n: ℕ) := Nat.iterate (fun x => ⁅x, right⁆) n base


@[expose]
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
