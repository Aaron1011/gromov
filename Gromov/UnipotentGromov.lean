import Mathlib
import Gromov.Unipotent.GammaN

/-!
# Triviality of the unipotent commutator

`unipotent_commutator_trivial`.

Root of the `Gromov.Unipotent` hierarchy.
-/

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

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
