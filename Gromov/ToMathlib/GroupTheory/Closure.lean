import Mathlib

/-!
# Subgroup closures

General-purpose material extracted from the Gromov development, destined for mathlib.
-/

open scoped Pointwise Finset

set_option maxHeartbeats 300000 in
lemma closure_iterate_mulact {T: Type*} [Group T] [DecidableEq T] (a b: T) (n: ℤ)
  (conj_in: (a^n * b * a^(-n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs))))
  (conj_inv_in: (a^(-n) * b * a^(n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs)))) :
 (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) = (Subgroup.closure (G := T) (Set.range (fun (m : ℤ) => a^m * b * a^(-m)))) := by
  ext x
  refine ⟨?_, ?_⟩
  .
    intro hx
    apply Subgroup.closure_mono (h := (fun (m: ℤ) ↦ a ^ m * b * a ^ (-m)) '' Set.Ioo (-n.natAbs) n.natAbs)
    .
      intro y hy
      simp at hy
      simp
      obtain ⟨m, hm, y_eq⟩ := hy
      use m
    . exact hx
  .
    intro hx
    have closed_under_conj: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a * y * a⁻¹ ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: m < (n.natAbs : ℤ) - 1
        . apply Subgroup.subset_closure
          simp
          use (m + 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            . omega
            .
              apply_fun (fun (z: ℤ) => z + 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                exact m_lt_n_sub
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) 1
          .
            rw [← mul_self_zpow]
            simp
            repeat rw [← mul_assoc]
        .
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (|n|) - 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← inv_zpow']
          rw [mul_assoc]
          rw [← zpow_add_one]
          simp
          simp at conj_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_inv_in
            exact conj_inv_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        simp at mul_mem
        simp
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem

    -- TODO - deduplicate this
    have closed_under_conj_inv: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a⁻¹ * y * a ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: (-n.natAbs : ℤ) < m - 1
        . apply Subgroup.subset_closure
          simp
          use (m - 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            .
              simp at m_lt_n_sub
              omega

            .
              apply_fun (fun (z: ℤ) => z - 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                omega
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-1)
          .
            repeat rw [← mul_assoc]
            nth_rw 2 [← zpow_neg_one]
            rw [← zpow_add]
            rw [add_comm, ← sub_eq_add_neg]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← inv_zpow]
              rw [inv_zpow']
              rw [mul_zpow_self]
              rw [add_comm]
            simp
            rw [← inv_zpow]
            simp
            rw [sub_eq_add_neg]

        .
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (-|n|) + 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [← mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← zpow_neg_one]
          rw [mul_assoc]
          rw [mul_assoc]
          rw [mul_assoc]
          simp
          repeat rw [← mul_assoc]
          simp at conj_inv_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_inv_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_in
            exact conj_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        repeat rw [← mul_assoc] at mul_mem
        simp at mul_mem
        simp
        repeat rw [← mul_assoc]
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem


    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp at hy
      obtain ⟨m, hm, y_eq⟩ := hy
      by_cases m_in_range: m ∈ Set.Ioo (-n.natAbs : ℤ) n.natAbs
      .
        apply Subgroup.subset_closure
        simp
        use m
        simp at m_in_range
        refine ⟨by omega, by simp⟩
      .
        simp only [Set.mem_Ioo] at m_in_range
        rw [not_and_or] at m_in_range
        simp at m_in_range
        by_cases m_pos: 0 < m
        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            rw [← m_eq_abs] at this
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              exact conj_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              simp at conj_inv_in
              rw [n_eq_neg_abs] at conj_inv_in
              simp at conj_inv_in
              rw [n_eq_neg_abs]
              simp
              exact conj_inv_in
          | succ p hsucc ih =>
            specialize closed_under_conj _ ih
            norm_cast
            rw [pow_succ']
            repeat rw [← mul_assoc] at closed_under_conj
            simp at closed_under_conj
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj

        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = -m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              simp at conj_inv_in
              exact conj_inv_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              rw [n_eq_neg_abs] at conj_in
              simp at conj_in
              rw [n_eq_neg_abs]
              simp
              exact conj_in
          | succ p hsucc ih =>
            specialize closed_under_conj_inv _ ih
            simp at ih
            norm_cast
            rw [zpow_negSucc]
            rw [pow_succ]
            repeat rw [← mul_assoc] at closed_under_conj_inv
            simp at closed_under_conj_inv
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj_inv


    | one => apply Subgroup.one_mem
    | mul y z hy hz y_mem z_mem =>
      apply Subgroup.mul_mem
      . exact y_mem
      . exact z_mem
    | inv y hy y_mem =>
      apply Subgroup.inv_mem _ y_mem

#print axioms closure_iterate_mulact

-- TODO - replace this with Subgroup.coe_mul_of_left_le_normalizer_right
lemma subgroup_coe_sup_invariant {G: Type*} [Group G] {A B: Subgroup G} (hab: ∀ b ∈ B, ∀ a ∈ A, (b * a * b⁻¹) ∈ A): ↑((A ⊔ B) : Subgroup G) = (A: Set G) * (B: Set G) := by
  ext a
  simp
  refine ⟨?_, ?_⟩
  .
    intro ha
    rw [Subgroup.sup_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      cases hx
      . rename_i x_mem_a
        conv =>
          arg 2
          equals x * 1 => simp
        apply Set.mul_mem_mul
        . exact x_mem_a
        . simp
      .
        rename_i x_mem_b
        conv =>
          arg 2
          equals 1 * x => simp
        apply Set.mul_mem_mul
        . simp
        . simpa using x_mem_b
    | one =>
      conv =>
        arg 2
        equals 1 * 1 => simp
      apply Set.mul_mem_mul
      . simp
      . simp
    | mul x y hx hy x_mem y_mem =>
      rw [Set.mem_mul] at x_mem y_mem
      obtain ⟨b, b_mem, c, c_mem, x_eq⟩ := x_mem
      obtain ⟨d, d_mem, e, e_mem, y_eq⟩ := y_mem

      rw [← x_eq, ← y_eq]
      rw [mul_assoc]
      nth_rw 2 [← mul_assoc]
      conv =>
        arg 2
        equals (b * (c * d * c⁻¹)) * (c * e) =>
          group

      apply Set.mul_mem_mul
      . simp
        apply Subgroup.mul_mem
        . simpa using b_mem
        .
          apply hab
          . simpa using c_mem
          . simpa using d_mem
      .
        simp
        apply Subgroup.mul_mem
        . simpa using c_mem
        . simpa using e_mem
    | inv x hx other =>
      rw [← Set.mem_inv]
      simp [-Set.mem_inv]
      rw [Set.mem_mul] at other
      obtain ⟨a, ha, b, hb, x_eq⟩ := other
      rw [← x_eq]
      conv =>
        arg 2
        equals b * (b⁻¹ * a * b) =>
          group

      apply Set.mul_mem_mul
      . exact hb
      .
        have foo := hab b⁻¹ (by simpa using hb) a ha
        simpa using foo
  . intro ha
    rw [Set.mem_mul] at ha
    obtain ⟨x, hx, y, hy, hxy⟩ := ha
    rw [Subgroup.sup_eq_closure]
    rw [Subgroup.closure_union]
    rw [← hxy]
    apply Subgroup.mul_mem_sup
    . apply Subgroup.mem_closure_of_mem
      exact hx
    . apply Subgroup.mem_closure_of_mem
      exact hy

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

-- TODO - deduplicate with with 'mem_S_prod_list'
lemma mem_closure_prod_list {G: Type*} [Group G] (S: Set G) (S_eq_Sinv: S = S⁻¹) (x: G) (hx: x ∈ Subgroup.closure S): ∃ l: List S, l.unattach.prod = x := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  specialize foo hx
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  conv at mem_s =>
    intro y hy
    rw [← S_eq_Sinv]
    simp
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold List.unattach
  simp [prod_eq]
