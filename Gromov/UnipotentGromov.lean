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


instance subgroup_map_finite {A B: Type*} [Group A] [Group B] (f: A →* B) (G: Subgroup A) [Finite G]: Finite (Subgroup.map f G) := by
  have foo: (Subgroup.map f G) ≃ (Set.image f G.carrier) := {
    toFun := fun a => a
    invFun := fun a => a
  }
  rw [Equiv.finite_iff foo]
  rw [Set.finite_coe_iff]
  apply Finite.Set.finite_image

-- TODO - generalize and pr to mathlib
lemma fg_of_subgroup_fg_comm {A : Type*} [CommGroup A] [Group.FG A] (H : Subgroup A) : H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  have : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h := IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)
  rw [Submodule.fg_iff_addSubgroup_fg] at h
  simpa using h

lemma fg_extension {A: Type*} [Group A] (N: Subgroup A) [N.Normal] (hN: N.FG) (hQ: Group.FG (A ⧸ N)): Group.FG A := by
  classical
  obtain ⟨S_Q, hS_Q⟩ := hQ
  obtain ⟨S_N, hS_N⟩ := hN
  let SQ_out := Finset.image (fun (a: (A ⧸ N)) => a.out) S_Q
  have SQ_eq: S_Q = Finset.image (QuotientGroup.mk' _) SQ_out := by
    simp [SQ_out]
    ext a
    simp

  rw [Group.fg_def, Subgroup.fg_iff]
  rw [SQ_eq] at hS_Q
  use S_N ∪ SQ_out
  refine ⟨?_, ?_⟩
  .
    simp [SQ_out]
    rw [Subgroup.closure_union]
    simp [hS_N]
    ext a
    simp
    by_cases mem_N: a ∈ N
    . apply Subgroup.mem_sup_left
      exact mem_N
    .
      let a_map: (A ⧸ N) := a
      have a_mem_top: a_map ∈ (⊤ : Subgroup (A ⧸ N)) := by
        simp

      rw [← hS_Q] at a_mem_top
      simp only [Finset.coe_image] at a_mem_top
      rw [← MonoidHom.map_closure] at a_mem_top
      simp at a_mem_top
      obtain ⟨k, hk⟩ := a_mem_top
      simp [SQ_out] at hk
      simp [a_map] at hk
      have a_eq := hk.2
      rw [QuotientGroup.eq] at a_eq
      rw [← Subgroup.mul_mem_cancel_left (x := k⁻¹)]
      .
        apply Subgroup.mem_sup_left
        exact a_eq
      . apply Subgroup.mem_sup_right
        simp
        exact hk.1

  . simp

lemma fg_domain_of_ker_range {A B: Type*} [Group A] [Group B] (f : A →* B) (hA: Subgroup.FG f.ker) (hB: Subgroup.FG f.range): Group.FG A := by
  have new_fg := fg_extension (f.ker) hA
  apply new_fg
  have equiv := QuotientGroup.quotientKerEquivRange f
  rw [← Group.fg_iff_subgroup_fg] at hB
  apply Group.fg_of_surjective (f := equiv.symm.toMonoidHom)
  simp
  exact MulEquiv.surjective equiv.symm

lemma Group.FG.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : Group.FG G) :
    Group.FG H :=
  haveI := h
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

set_option maxHeartbeats 5000000 in
lemma fg_of_subgroup_fg_nilpotent {A: Type*} [DecidableEq A] [Group A] [Group.IsNilpotent A] (A_fg: Group.FG A) (H: Subgroup A): H.FG := by
  classical
  revert H
  induction hn: Group.nilpotencyClass A using Nat.strong_induction_on generalizing A with
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


    rw [← Group.fg_iff_subgroup_fg]
    apply fg_domain_of_ker_range ((QuotientGroup.mk' ((⊤: Subgroup A).lowerCentralSeries n)).comp H.subtype)
    .
      -- The kernel is `N.subgroupOf H = (H ⊓ N).subgroupOf H`, which is the same abstract group as
      -- `(H ⊓ N).subgroupOf N` — the version we proved FG using that `N` is abelian.
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype,
        ← Subgroup.inf_subgroupOf_left, ← Group.fg_iff_subgroup_fg]
      exact Group.FG.of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe inf_le_right).trans
          (Subgroup.subgroupOfEquivOfLe inf_le_left).symm)
        ((Group.fg_iff_subgroup_fg _).mpr h_inf_fg)
    .
      -- The range is the image of `H` in `A ⧸ Cⁿ A`, which is FG by the induction hypothesis.
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact ih (Subgroup.map (QuotientGroup.mk' _) H)

lemma mul_aut_iterate {G: Type*} [Group G] (f: MulAut G) (n: ℕ): f^[n] = ⇑(f ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext a
    rw [Function.iterate_succ_apply, pow_succ, MulAut.mul_apply, ← ih]


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


@[simp]
lemma toIntLinearMap_id {M : Type*}  [AddCommGroup M]: (AddMonoidHom.id M).toIntLinearMap = LinearMap.id := by
  ext a
  simp

/-- Compare cardinalities of two images of the same underlying products, pushed through a
homomorphism `ψ` and through an injective homomorphism `j`.  Used to move a bound proved in
`↥N'` across to the quotient `↥(Subgroup.center ↥N') ⧸ torsion`. -/
theorem card_image_listProd_hom_le {C Q N ι : Type*}
    [Group C] [Group Q] [Group N] [DecidableEq Q] [DecidableEq N]
    (ψ : C →* Q) (j : C →* N) (hj : Function.Injective j)
    (P : Finset (Finset ι)) (f : ι → C) :
    (P.image (fun x => (List.map (fun i => ψ (f i)) x.toList).prod)).card
      ≤ (P.image (fun x => (List.map (fun i => j (f i)) x.toList).prod)).card := by
  classical
  have h1 : ∀ x : Finset ι,
      (List.map (fun i => ψ (f i)) x.toList).prod = ψ ((List.map f x.toList).prod) := by
    intro x
    rw [show (fun i => ψ (f i)) = (ψ : C → Q) ∘ f from rfl, ← List.map_map, List.prod_hom]
  have h2 : ∀ x : Finset ι,
      (List.map (fun i => j (f i)) x.toList).prod = j ((List.map f x.toList).prod) := by
    intro x
    rw [show (fun i => j (f i)) = (j : C → N) ∘ f from rfl, ← List.map_map, List.prod_hom]
  simp_rw [h1, h2]
  rw [show (fun x : Finset ι => ψ ((List.map f x.toList).prod))
        = ψ ∘ (fun x : Finset ι => (List.map f x.toList).prod) from rfl,
     show (fun x : Finset ι => j ((List.map f x.toList).prod))
        = j ∘ (fun x : Finset ι => (List.map f x.toList).prod) from rfl,
     ← Finset.image_image, ← Finset.image_image, Finset.card_image_of_injective _ hj]
  exact Finset.card_image_le

/-- Transport a `gamma_conj_bound`-style bound along a common "source" group `C`: out of `C`
there is an injective `j` into the group `N` where the bound is known, and a surjective `ψ`
onto the group `Q` where it is wanted, each intertwining the respective self-maps. -/
theorem conjBound_transport {C Q N : Type*} [Group C] [Group Q] [Group N]
    [DecidableEq Q] [DecidableEq N]
    {fC : C → C} {fQ : Q → Q} {fN : N → N}
    (ψ : C →* Q) (hψ : Function.Surjective ψ) (j : C →* N) (hj : Function.Injective j)
    (hψcomm : ∀ x, ψ (fC x) = fQ (ψ x)) (hjcomm : ∀ x, j (fC x) = fN (j x))
    (hbound : ∀ k : ℕ, 0 < k → ∀ g : N, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fN^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q) :
    ∀ k : ℕ, 0 < k → ∀ g : Q, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fQ^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q := by
  have hiterψ : ∀ (n : ℕ) (x : C), ψ (fC^[n] x) = fQ^[n] (ψ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hψcomm]
  have hiterj : ∀ (n : ℕ) (x : C), j (fC^[n] x) = fN^[n] (j x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hjcomm]
  intro k hk gQ
  obtain ⟨gC, rfl⟩ := hψ gQ
  obtain ⟨p, q, ppos, hb⟩ := hbound k hk (j gC)
  refine ⟨p, q, ppos, ?_⟩
  intro b hb' a ha hab
  refine le_trans ?_ (hb b hb' a ha hab)
  simp_rw [← hiterψ, ← hiterj]
  exact card_image_listProd_hom_le ψ j hj ((Finset.Ico a b).attach.powerset)
    (fun (i : ↥(Finset.Ico a b)) => fC^[k * ↑i] gC)

/-- Final step of isolating `K`, reducing the `h_poly` log inequality to a statement in `ℕ`.

Splits `Real.log ↑(p * K ^ q)` into `Real.log ↑p + q * Real.log ↑K`, then eliminates the
`Real.log ↑K` using `Real.log_natCast_le_rpow_div` at `ε := 1/4`, which gives
`Real.log K ≤ 4 * K ^ (1/4)`; squaring therefore contributes only a `K ^ (1/2)` term, which
the right-hand `K` dominates.  (At `ε := 1/2` the reduction would be unsound for `q ≥ 1`.)
The hypothesis mentions `K` only on the right, and is an inequality of naturals. -/
theorem log_pow_sq_lt_of_lt (M p q K : ℕ) (hp : 0 < p)
    (h : ⌈4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2⌉₊ + 2 * M < K) :
    ((4 * (q:ℝ) + Real.log ((p * K ^ q : ℕ) : ℝ)) / Real.log 2) ^ 2 + (M:ℝ) < (K:ℝ) := by
  have hK1 : 1 ≤ K := by omega
  have hpr : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hKr : ((K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit : Real.log ((p * K ^ q : ℕ) : ℝ) = Real.log p + q * Real.log K := by
    push_cast; rw [Real.log_mul hpr (pow_ne_zero _ hKr), Real.log_pow]
  rw [hsplit]
  have h' : 4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2 + 2 * (M:ℝ) < (K:ℝ) := by
    have hceil := Nat.le_ceil (4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2)
    have hcast : ((⌈4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2⌉₊ + 2 * M : ℕ) : ℝ)
        < (K:ℝ) := by exact_mod_cast h
    push_cast at hcast
    linarith
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK1
  have hlogK0 : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
  have hlogp0 : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hM0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  set u : ℝ := (K:ℝ) ^ ((1:ℝ)/4) with hu
  have hu1 : (1:ℝ) ≤ u := by
    rw [hu]; exact Real.one_le_rpow (by exact_mod_cast hK1) (by norm_num)
  have hu4 : u ^ 4 = (K:ℝ) := by
    rw [hu, ← Real.rpow_natCast ((K:ℝ) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hK0.le]; norm_num
  have hlogK : Real.log (K:ℝ) ≤ 4 * u := by
    calc Real.log (K:ℝ) ≤ (K:ℝ) ^ ((1:ℝ)/4) / ((1:ℝ)/4) :=
          Real.log_natCast_le_rpow_div K (by norm_num)
      _ = 4 * u := by rw [hu]; ring
  have hnum : 4 * (q:ℝ) + (Real.log p + q * Real.log K) ≤ (8 * (q:ℝ) + Real.log p) * u := by
    nlinarith
  have hsq : ((4 * (q:ℝ) + (Real.log p + q * Real.log K)) / Real.log 2) ^ 2
      ≤ (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 * u ^ 2 := by
    have hstep : ((4 * (q:ℝ) + (Real.log p + q * Real.log K)) / Real.log 2) ^ 2
        ≤ ((8 * (q:ℝ) + Real.log p) * u / Real.log 2) ^ 2 := by gcongr
    calc _ ≤ ((8 * (q:ℝ) + Real.log p) * u / Real.log 2) ^ 2 := hstep
      _ = (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 * u ^ 2 := by field_simp
  set D : ℝ := (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hgoal : D * u ^ 2 + (M:ℝ) < (K:ℝ) := by
    nlinarith [sq_nonneg (u ^ 2 - 2 * D), hu1, hD0, hM0, hu4, h']
  linarith [hsq, hgoal]

def gamma_conj_bound {H: Type*}  [DecidableEq H] [Group H]  {N': Subgroup H} (gamma: MulAut N') := ∀ k: ℕ, (0 < k) →  ∀ g, ∃ p q: ℕ, 0 < p ∧ ∀ b: ℕ, 0 < b → ∀ a: ℕ, (0 < a) → (a < b) → ((Finset.image (fun x ↦ (List.map (fun (i:  ↥(Finset.Ico a b)) ↦ (gamma)^[k * ↑i] g) x.toList).prod))
        (Finset.Ico a b).attach.powerset).card ≤ p * (b^q) * (b - a)^q

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 40000 in
lemma exists_gamma_n_unipotent_center_N' {H: Type*} [DecidableEq H] [Group H] {N': Subgroup H} [N'_normal: N'.Normal] (N'_nilpotent: Group.IsNilpotent N') (hN': Subgroup.FG N') (gamma: MulAut N')
  (gamma_conj: gamma_conj_bound gamma):
     ∃ a, a ≠ 0 ∧ ∀ k: ℕ, 0 < k → ∃ n, ∀ g ∈ Subgroup.center N', Nat.iterate (fun x => x * ((gamma^[a*k]) x⁻¹)) n g = 1 := by

  classical


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

  have unipotent_on_quot: ∃ a, 0 < a ∧ ∀ p: ℕ, 0 < p → ∃ n, ∀ g : (Subgroup.center ↥N') ⧸ torsion, Nat.iterate (fun x => x * ((gamma_lift^[a * orderOf new_gamma_torsion * p] x⁻¹))) n g = 1 := by
    wlog nontrivial_quot: Nontrivial ((Subgroup.center ↥N') ⧸ torsion)
    .
      clear this
      simp at nontrivial_quot
      use 1
      refine ⟨by simp, ?_⟩
      intro p hp
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


    let fin_dim: Module.Finite ℤ add_quot := by infer_instance

    let gamma_add := gamma_lift.toAdditive.toAddMonoidHom.toIntLinearMap
    let B := (Module.finBasis ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion)))
    let gamma_matrix := gamma_add.toMatrix B B
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


    have rank_nonzero: NeZero (Module.finrank ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion))) := by
      apply NeZero.of_pos
      apply Module.finrank_pos


    have gamma_lift_conj: ∀ k: ℕ, (0 < k) →  ∀ g, ∃ p q: ℕ, 0 < p ∧ ∀ b: ℕ, 0 < b → ∀ a: ℕ, (0 < a) → (a < b) → (Finset.image (fun x ↦ (List.map (fun (i:  ↥(Finset.Ico a b)) ↦ (gamma_lift)^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * (b^q) * (b - a)^q := by

      -- Same shape as the `final_gamma` transport: the products live in
      -- `↥(Subgroup.center ↥N')`, mapped out injectively by `Subgroup.subtype` (where
      -- `gamma_conj` gives the bound) and surjectively by `QuotientGroup.mk'` (where it
      -- is wanted).
      classical
      exact conjBound_transport
        (fC := fun x : ↥(Subgroup.center ↥N') =>
          (⟨gamma x, gamma_mem_center x⟩ : ↥(Subgroup.center ↥N')))
        (fQ := ⇑gamma_lift) (fN := ⇑gamma)
        (QuotientGroup.mk' torsion) (QuotientGroup.mk'_surjective _)
        ((Subgroup.center ↥N').subtype) (Subgroup.subtype_injective _)
        (fun x => (swap_gamma_lift x).symm) (fun x => rfl) gamma_conj

    have eigen_norm_one: ∀ (k : Module.End.Eigenvalues (Matrix.toLin' (((unitOfInvertible gamma_matrix).val).map (Int.castRingHom ℂ)))), ‖k.val‖ = 1 := by
      apply int_matrix_poly_growth_eigenvalue
      .
        intro k hk v
        -- name the (fixed) group element the iterates are applied to
        set g : ↥(Subgroup.center ↥N') ⧸ torsion :=
          Additive.toMul ((Finsupp.linearCombination ℤ ⇑B)
            ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin dim)).symm v)) with hg


        obtain ⟨p, q, p_pos, hq⟩ := gamma_lift_conj ⌈Real.logb ‖k‖ 3⌉₊ (by
          simp
          apply Real.logb_pos
          . grind
          . grind
        ) g
        let K: ℕ := (⌈4 * ((8 * ↑q + Real.log ↑p) ^ 2 / Real.log 2 ^ 2) ^ 2⌉₊ + 2 * ⌈Real.logb ‖k‖ 3⌉₊) + 1


        have hpq := hq K (by simp [K]) ⌈Real.logb ‖k‖ 3⌉₊ (by
          simp
          apply Real.logb_pos
          . grind
          . grind
        ) (by
          simp [K]
          rw [two_mul]
          grw [Nat.le_ceil (a := Real.logb ‖k‖ 3)]
          grind
        )

        use p * K ^ q
        use q
        use K

        refine ⟨?_, ?_, ?_, ?_⟩
        . apply mul_pos
          . exact p_pos
          . apply pow_pos
            simp [K]

        . simp [K]
          rw [two_mul]
          grw [Nat.le_ceil (a := Real.logb ‖k‖ 3)]
          grind
        .
          -- Isolate `K` on the right of
          --   `X < Real.log 2 * (↑K - ↑⌈Real.logb ‖k‖ 3⌉₊) ^ (1/2)`.
          -- Divide by `Real.log 2 > 0`, bound the LHS by its absolute value (so no sign
          -- assumption on `X` is needed), rewrite `|y| = √(y ^ 2)` and use strict
          -- monotonicity of `√`, then move the subtraction across.  `K` is never unfolded.
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          rw [← Real.sqrt_eq_rpow, ← div_lt_iff₀' hlog2]
          refine lt_of_le_of_lt (le_abs_self _) ?_
          rw [← Real.sqrt_sq_eq_abs]
          refine Real.sqrt_lt_sqrt (sq_nonneg _) ?_
          rw [lt_sub_iff_add_lt]
          -- `K` still occurs on the left inside `Real.log ↑(p * K ^ q)`.  This splits that
          -- logarithm and eliminates the resulting `Real.log ↑K`, leaving a goal in `ℕ` with
          -- `K` alone on the right.
          refine log_pow_sq_lt_of_lt _ p q K p_pos ?_
          -- ⊢ ⌈4 * ((8 * ↑q + Real.log ↑p) ^ 2 / Real.log 2 ^ 2) ^ 2⌉₊
          --     + 2 * ⌈Real.logb ‖k‖ 3⌉₊ < K
          simp [K]
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


    let a := KroneckerPow (unitOfInvertible gamma_matrix) eigen_norm_one
    use a
    refine ⟨(by
      apply KroneckerPow_pos
    ), ?_⟩
    intro p hp


    have unipotent_gamma_matrix := int_matrix_unipotent (by
      apply Module.finrank_pos
    ) (unitOfInvertible gamma_matrix) (by
      apply eigen_norm_one
    ) (n := p * orderOf new_gamma_torsion) (hn := by positivity)
    obtain ⟨n, hm⟩ := unipotent_gamma_matrix


    use n
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

    have x_mul_gamma_eq: ∀ q: ℕ, (fun x => x * (⇑gamma_lift)^[q] x⁻¹) = Additive.toMul ∘ (-((MonoidHom.toAdditive gamma_lift.toMonoidHom).toIntLinearMap ^ (q) - LinearMap.id)).toFun ∘ (Additive.ofMul) := by
      intro q
      ext x
      conv =>
        rhs
        equals Additive.toMul ((-((MonoidHom.toAdditive gamma_lift.toMonoidHom).toIntLinearMap ^ (q) - LinearMap.id)).toFun (Additive.ofMul x)) =>
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
    -- collapse the `Matrix.toLin B B (LinearMap.toMatrix B B _)` round-trip, which plain
    -- `rfl` cannot see through
    rw [Matrix.toLin_toMatrix]

    -- TODO - figure out how the order gets swapped
    have mul_eq: a * orderOf new_gamma_torsion * p = p * orderOf new_gamma_torsion * a := by ring
    simp_rw [mul_eq]
    rfl


  obtain ⟨quot_pow, quot_pow_pos, h_quot_pow⟩ := unipotent_on_quot
  use (quot_pow * ( orderOf new_gamma_torsion))
  refine ⟨by positivity, ?_⟩
  intro p hp

  obtain ⟨quot_n, h_quot_n⟩ := h_quot_pow p hp


  use quot_n + 1
  intro g hg


  have new_gamma_pow: new_gamma_torsion^[quot_pow * (orderOf new_gamma_torsion) * p] = id := by
    rw [mul_comm (a := quot_pow), mul_assoc, Function.iterate_mul]
    rw [mul_aut_iterate]
    simp

  have orig_new_gamma_pow := new_gamma_pow


  specialize h_quot_n (QuotientGroup.mk ⟨g, hg⟩)


  have swap_iter: ∀ n, ∀ g: Subgroup.center N', (fun x ↦ x * (gamma_lift^[quot_pow * orderOf new_gamma_torsion * p]) x⁻¹)^[n] g = QuotientGroup.mk ⟨((fun x ↦ x * (gamma^[quot_pow * orderOf new_gamma_torsion * p]) x⁻¹)^[n] g), (by
    rw [mul_aut_iterate]
    simp
    induction n generalizing g with
    | zero =>
      simp
    | succ n ih =>
      simp
      have mul_mem_center: (↑g * ((gamma ^ (quot_pow * orderOf new_gamma_torsion * p )) ↑g)⁻¹) ∈ Subgroup.center N' := by
        apply Subgroup.mul_mem
        . simp
        .
          simp
          have center_char: (Subgroup.center N').Characteristic := by
            infer_instance
          rw [Subgroup.characteristic_iff_le_comap] at center_char
          specialize center_char (gamma ^ (quot_pow * orderOf new_gamma_torsion * p)) g.prop
          simpa using center_char
      conv =>
        pattern (↑g * ((gamma ^ (quot_pow * orderOf new_gamma_torsion * p)) ↑g)⁻¹)
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
  simp_rw [new_gamma_pow]
  simp

  -- OLD CODE


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 160000 in
/--{G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) [H.Normal]--/
lemma exists_gamma_n_unipotent_N' {H: Type*} [DecidableEq H] [Group H] {N': Subgroup H} [N'_normal: N'.Normal] (N'_nilpotent: Group.IsNilpotent N') (hN': Subgroup.FG N') (gamma: MulAut N') (gamma_conj: gamma_conj_bound gamma):
    ∀ p: ℕ, 0 < p → ∃ a n, a ≠ 0 ∧ ∀ g : N', Nat.iterate (fun x => x * ((gamma^[a*p]) x⁻¹)) n g = 1 := by


  classical
  by_cases N'_subsingle: Subsingleton N'
  .
    intro p hp
    use 1
    use 1
    simp
    intro a ha
    have order := Subsingleton.orderOf_eq (⟨_, ha⟩ : N')
    simp at order
    simp [order, iteratedCommutator]
    rw [mul_aut_iterate]
    simp


  induction hn: Group.nilpotencyClass N' using Nat.strong_induction_on generalizing H N' with
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
      intro p hp
      obtain ⟨z_a, h_z_a, z_a_temp⟩ := exists_gamma_n_unipotent_center_N' (N' := N') (N'_nilpotent) (hN') gamma gamma_conj
      obtain ⟨z_n, h_z_unipotent⟩ := z_a_temp p hp
      use z_a

      use z_n
      refine ⟨by positivity, ?_⟩
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

      rw [← Group.fg_iff_subgroup_fg]
      apply Subgroup.fg_of_index_ne_zero
    ) final_gamma (by
      classical
      refine conjBound_transport (fC := ⇑gamma) (fQ := ⇑final_gamma) (fN := ⇑gamma)
        (((Subgroup.topEquiv (G := ↥N' ⧸ Subgroup.center ↥N')).symm.toMonoidHom).comp
          (QuotientGroup.mk' (Subgroup.center ↥N')))
        ?_ (MonoidHom.id ↥N') Function.injective_id ?_ (fun x => rfl) gamma_conj
      · exact (Subgroup.topEquiv (G := ↥N' ⧸ Subgroup.center ↥N')).symm.surjective.comp
          (QuotientGroup.mk'_surjective _)
      · intro x
        simp [final_gamma, aut_transfer, first_map, gamma_quot, QuotientGroup.congr_mk]
    ) top_subsingle rfl

    clear ih
    intro p hp
    obtain ⟨z_a, h_z_a, z_a_temp⟩ := exists_gamma_n_unipotent_center_N' (N' := N') (N'_nilpotent) (hN') (gamma) (by
      apply gamma_conj
    )

    obtain ⟨a, n, ha, h_prev⟩ := foo (z_a * p) (by positivity)
    obtain ⟨z_n, h_z_unipotent⟩ := z_a_temp (a * p) (by positivity)

    use a * z_a
    use z_n + n
    refine ⟨by positivity, ?_⟩
    intro g
    let g_h_prev: (⊤ : Subgroup (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N'))) := ⟨⟨g, by simp⟩, by simp⟩
    specialize h_prev g_h_prev
    rw [Function.iterate_add_apply]

    specialize h_z_unipotent ((fun x ↦ x * ((gamma^[a*z_a*p]) (x⁻¹)))^[n] g) ?_
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

      rw [← QuotientGroup.eq_one_iff]
      rw [← coe_iter]
      simp_rw [← mul_assoc] at h_prev
      simpa using h_prev


    .
      simp_rw [mul_aut_iterate] at h_z_unipotent
      rw [mul_aut_iterate]
      simp_rw [← mul_assoc] at h_z_unipotent
      have reorder: z_a * a * p = a * z_a * p := by ring
      simp_rw [reorder] at h_z_unipotent
      exact h_z_unipotent


--   -- use pow_eq_one_of_norm_le_one (Kronecker's Theorem) once mathlib is bumped


--   --   sorry


--   -- Module.free_of_finite_type_torsion_free'
--   -- QuotientGroup.instIsMulTorsionFree


--   --   -- QuotientGroup.nontrivial_iff
--   --   apply Module.finrank_pos


--   --     sorry

--   --   sorry


--   --   simp [K]
--   --   sorry


--   --   -- rw [MulEquiv.toMonoidHom_eq_coe]
--   --   -- rw [MonoidHom.coe_coe]

--   --   -- rw [MonoidHom.pow_map]

--   --   -- simp
--   --   -- dsimp only [ord_fin]


--   --   sorry


--   --   use sorry
--   --   simp


--   --   sorry


--   -- simp at ord_fin
--   --rw [Nat.card_prod] at ord_fin


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

            have l_len_ne: l.length ≠ 0 := by
              omega


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

