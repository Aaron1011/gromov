module

public import Mathlib
public import Gromov.ThreeTwoGrowth

/-!
# The sets `S_n` generate the kernel

`e_i_and_gamma_generates_G`, `three_two_gamma_m_generates` and the finite generation of the
kernel of `φ`.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

def e_i_with_gamma (φ: (Additive G) →+ ℤ) (γ : G) (s: S): Additive G := (ofMul s.val) + ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))


-- The 'e_i' terms from Vikman 3.2, together with γ, generate the original group G
lemma e_i_and_gamma_generates_G (φ: (Additive G) →+ ℤ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure ({1, γ, γ⁻¹} ∪ ((e_i_with_gamma φ γ) '' Set.univ)) = (Subgroup.closure S) := by

  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ

  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))

  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))

  have e_i_regular_zero: ∀ s: S, φ (ofMul (e_i_regular s)) = 0 := by
    dsimp [ofMul]
    intro s
    unfold e_i_regular
    simp
    simp [phi_ofmul]

  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp

  conv =>
    arg 1
    arg 1
    arg 2
    arg 1
    equals e_i_regular =>
      rfl
  rw [closure_enlarge]
  apply Subgroup.closure_eq_of_le
  .
    rw [hGS.generates]
    exact fun ⦃a⦄ a ↦ trivial
  .
    simp
    intro s hs
    simp
    rw [← mem_toSubmonoid]
    rw [Subgroup.closure_toSubmonoid]
    dsimp [Membership.mem]
    rw [Submonoid.closure_eq_image_prod]
    -- TODO - why do we need any of this?
    show s ∈ List.prod '' _
    rw [Set.mem_image]


    have foo := Submonoid.exists_list_of_mem_closure (s := ((S ∪ S⁻¹) : Set G)) (x := s)
    rw [← Subgroup.closure_toSubmonoid _] at foo
    simp only [mem_toSubmonoid, Finset.mem_coe] at foo
    have generates := hGS.generates
    have x_in_top: s ∈ (⊤: Set G) := by
      simp

    rw [← generates] at x_in_top
    specialize foo x_in_top
    obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
    norm_cast at l_mem_s
    rw [s_union_sinv] at l_mem_s

    let l_attach := l.attach
    let list_with_mem: List S := (l_attach).map (fun a => ⟨a.val, l_mem_s a.val a.prop⟩)
    let new_list := list_with_mem.map (fun s => (e_i s) + ofMul (γ^(((φ (ofMul s.val))))))

    have cancel_add_minus: max_phi - 1 + 1 = max_phi := by
      omega

    use new_list
    refine ⟨?_, ?_⟩
    .
      simp
      intro x hx
      unfold new_list list_with_mem l_attach at hx
      simp at hx
      obtain ⟨a, ha, x_eq_sum⟩ := hx
      left

      have gamma_phi_in_minus_plus: γ^(φ a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1  +1) := by
        by_cases val_pos: 0 < φ a
        .
          have eq_self: Int.natAbs (φ a) = φ a := by
            simp [val_pos]
            linarith
          conv =>
            arg 2
            equals γ ^ (Int.natAbs (φ a)) =>
              nth_rw 1 [← eq_self]
              norm_cast
          apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
          . simp
          .
            rw [cancel_add_minus]
            unfold max_phi
            simp
            right
            apply Finset.le_max'
            simp
            use a
            refine ⟨l_mem_s a ha, ?_⟩
            conv =>
              pattern ofMul a
              equals a => rfl
          .
            apply Set.pow_mem_pow
            simp
        .
          have eq_neg_abs: (φ a) = -(φ a).natAbs := by
            rw [← Int.abs_eq_natAbs]
            simp at val_pos
            rw [← abs_eq_neg_self] at val_pos
            omega
          rw [eq_neg_abs]
          conv =>
            arg 2
            equals (γ⁻¹) ^ (↑(φ a).natAbs) =>
              simp
              rw [Int.abs_eq_natAbs]
              norm_cast
          -- TOOD - deduplicate this with the positive case
          apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
          . simp
          .
            rw [cancel_add_minus]
            unfold max_phi
            simp
            right
            apply Finset.le_max'
            simp
            use a
            refine ⟨l_mem_s a ha, ?_⟩
            conv =>
              pattern ofMul a
              equals a => rfl
          .
            apply Set.pow_mem_pow
            simp
      have a_mem_s: a ∈ S := by exact l_mem_s a ha
      have prod_mem_power: e_i_regular ⟨a, a_mem_s⟩ * γ ^ φ (ofMul a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1 + 1 + 1) := by
        rw [pow_succ']
        rw [Set.mem_mul]
        use e_i_regular ⟨a, a_mem_s⟩
        refine ⟨by simp, ?_⟩
        use γ ^ φ (ofMul a)
        refine ⟨gamma_phi_in_minus_plus, ?_⟩
        simp

      have prod_eq_sum: e_i ⟨a, l_mem_s a ha⟩ + φ (ofMul a) • ofMul γ = (e_i_regular ⟨a, a_mem_s⟩) * (γ ^ φ (ofMul a)) := by
        simp [e_i, e_i_regular, cancel_add_minus]


        conv =>
          rhs
          arg 1
          equals ofMul (a* γ^(-(φ (ofMul a)))) =>
            simp

        apply_fun (fun x => x * (γ ^ (- φ (ofMul a))))
        .
          simp only
          simp
          conv =>
            lhs
            equals a * (γ ^ φ (ofMul a))⁻¹ =>
              simp
              rfl
          conv =>
            rhs
            rhs
            equals ofMul (γ ^ (- φ (ofMul a))) =>
              simp

          rw [← ofMul_mul]
          conv =>
            rhs
            equals (a * γ ^ (-φ (ofMul a))) =>
              rfl
          simp
        .
          exact mul_left_injective (γ ^ (-φ (ofMul a)))


      rw [← x_eq_sum]
      rw [prod_eq_sum]
      rw [cancel_add_minus] at prod_mem_power
      apply prod_mem_power


    unfold new_list list_with_mem l_attach
    simp
    conv =>
      arg 1
      arg 1
      arg 1
      arg 1
      intro z
      unfold e_i
      simp
    simp
    conv =>
      arg 1
      arg 1
      arg 1
      equals id =>
        rfl
    convert l_prod using 2
    exact List.map_id l


#print axioms e_i_and_gamma_generates_G

-- The kernel of `φ` is generated by {γ_m_i}
set_option maxHeartbeats 1000000
lemma three_two_gamma_m_generates (φ: (Additive G) →+ ℤ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S)  φ γ))) = AddSubgroup.toSubgroup φ.ker := by
  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ
  --
  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))


  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))
  have e_i_zero: ∀ s: S, φ (e_i s) = 0 := by
    intro s
    unfold e_i
    simp
    simp [phi_ofmul]

  have e_i_regular_zero: ∀ s: S, φ (ofMul (e_i_regular s)) = 0 := by
    dsimp [ofMul]
    intro s
    unfold e_i_regular
    simp
    simp [phi_ofmul]

  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp


  have new_closure_e_i := e_i_and_gamma_generates_G φ γ hγ
  let gamma_m := fun (m: ℤ) (s: S) => γ^m * (e_i s).toMul * γ^(-m)
  have gamma_m_ker_phi: (Subgroup.closure (Set.range (Function.uncurry gamma_m))) = φ.ker.toSubgroup := by
    ext z
    refine ⟨?_, ?_⟩
    . intro hz
      have foo := Submonoid.exists_list_of_mem_closure (s := Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) (x := z)
      rw [← Subgroup.closure_toSubmonoid _] at foo
      specialize foo hz
      obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
      rw [← l_prod]
      rw [← MonoidHom.coe_toMultiplicative_ker]
      show (AddMonoidHom.toMultiplicative φ) (List.prod (l : List (Multiplicative (Additive G)))) = 1
      rw [map_list_prod]
      apply List.prod_eq_one
      intro x hx
      simp at hx
      obtain ⟨a, a_mem_l, phi_a⟩ := hx
      specialize l_mem_s a a_mem_l
      unfold gamma_m at l_mem_s
      simp at l_mem_s
      rw [← phi_a]
      match l_mem_s with
      | .inl a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
      | .inr a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        apply_fun Inv.inv at prod_eq_a
        simp at prod_eq_a
        -- TODO - deduplicate this with the branch above
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
    .
      intro hz

      -- We need to write 'γ^a (f⁻¹ )' as an element of e_i


      have foo := Submonoid.exists_list_of_mem_closure (s := ({1, γ, γ⁻¹} ∪ e_i '' Set.univ) ∪ ({1, γ, γ⁻¹} ∪ e_i '' Set.univ)⁻¹) (x := z)
      apply_fun Subgroup.toSubmonoid at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i

      have e_i_eq: e_i = e_i_with_gamma φ γ := rfl
      rw [← e_i_eq] at new_closure_e_i
      rw [new_closure_e_i] at foo
      rw [← Subgroup.closure_toSubmonoid _] at foo
      simp only [mem_toSubmonoid, Finset.mem_coe] at foo

      conv at foo =>
        intro hz
        arg 1
        intro l
        lhs
        intro y
        intro hy
        rw [Set.union_comm {1, γ, γ⁻¹} (e_i '' Set.univ)]
        rw [Set.union_assoc]
        arg 1
        rhs
        rw [Set.union_comm]
        rw [Set.union_inv]
        rw [Set.union_assoc]
        rhs
        simp

      have generates := hGS.generates
      have z_in_top: z ∈ (⊤: Set G) := by
        simp

      rw [← generates] at z_in_top
      have z_eq_prod := foo z_in_top
      clear foo

      let E: Set G := {γ, γ⁻¹} ∪ Set.range e_i_regular ∪ (Set.range e_i_regular)⁻¹

      let rec rewrite_list (list: List (E)) (hlist: φ (ofMul list.unattach.prod) = 0): { t: List (((Set.range (Function.uncurry gamma_m) : (Set G)) ∪ (Set.range (Function.uncurry gamma_m))⁻¹ : (Set G))) // list.unattach.prod = t.unattach.prod } := by
        let is_gamma: E → Bool := fun (k: E) => k = γ ∨ k = γ⁻¹
        let is_gamma_prop: E → Prop := fun (k: E) => k = γ ∨ k = γ⁻¹
        have eq_split: list = list.takeWhile is_gamma ++ list.dropWhile is_gamma := by
          exact Eq.symm List.takeWhile_append_dropWhile
        by_cases header_eq_full: list.takeWhile is_gamma = list
        .
          have list_eq_gamma_m: ∃ m: ℤ, list.unattach.prod = γ ^ m := by
            unfold is_gamma at header_eq_full
            clear eq_split is_gamma is_gamma_prop hlist

            induction list with
            | nil =>
              use 0
              simp
            | cons h t ih =>
              have h_gamma: h = γ ∨ h = γ⁻¹ := by
                simp at header_eq_full
                exact header_eq_full.1
              rw [List.takeWhile_cons_of_pos] at header_eq_full
              .
                rw [List.cons_eq_cons] at header_eq_full
                specialize ih header_eq_full.2
                obtain ⟨m, hm⟩ := ih
                by_cases h_eq_gamma: h = γ
                .
                  use (m + 1)
                  simp [h_eq_gamma, hm]
                  exact mul_self_zpow γ m
                . use (-1 + m)
                  simp [h_eq_gamma] at h_gamma
                  simp [h_gamma, hm]
                  rw [← zpow_neg_one]
                  rw [zpow_add]
              . simp [h_gamma]


          have empty_prod_eq: list.unattach.prod = ([] : List E).unattach.prod := by
            obtain ⟨m, hm⟩ := list_eq_gamma_m
            rw [hm]
            simp
            rw [hm] at hlist
            simp at hlist
            simp [phi_ofmul] at hlist
            simp [hlist]

          exact ⟨[], empty_prod_eq⟩
        .

          have tail_nonempty: list.dropWhile is_gamma ≠ [] := by
            rw [not_iff_not.mpr List.takeWhile_eq_self_iff] at header_eq_full
            rw [← not_iff_not.mpr List.dropWhile_eq_nil_iff] at header_eq_full
            exact header_eq_full

          have dropwhile_len_gt: 0 < (list.dropWhile is_gamma).length := by
            exact List.length_pos_iff.mpr tail_nonempty

          have not_is_gamma := List.dropWhile_get_zero_not is_gamma list dropwhile_len_gt
          simp at not_is_gamma

          have not_is_gamma_prop: ¬ is_gamma_prop (List.dropWhile is_gamma list)[0] := by
            dsimp [is_gamma_prop]
            dsimp [is_gamma] at not_is_gamma
            exact of_decide_eq_false not_is_gamma

          simp [is_gamma_prop] at not_is_gamma_prop
          have drop_head_in_e_i: (List.dropWhile is_gamma list)[0].val ∈ (Set.range e_i_regular) ∪ (Set.range e_i_regular)⁻¹ := by
            have drop_in_E: (List.dropWhile is_gamma list)[0].val ∈ E := by
              simp [E]
            simp only [E] at drop_in_E
            simp_rw [Set.union_assoc] at drop_in_E
            rw [Set.mem_union] at drop_in_E
            have not_in_left: (List.dropWhile is_gamma list)[0].val ∉ ({γ, γ⁻¹} : Set G) := by
              simp [not_is_gamma_prop]

            -- TODO - why can't simp handle this?
            have in_right := Or.resolve_left drop_in_E not_in_left
            exact in_right


          let m := ((list.takeWhile is_gamma).map (fun (k : E) => if k = γ then 1 else if k = γ⁻¹ then -1 else 0)).sum

          have in_range: γ ^ m * ↑(List.dropWhile is_gamma list)[0] * γ ^ (-m) ∈ (Set.range (Function.uncurry gamma_m)) ∪ ((Set.range (Function.uncurry gamma_m)))⁻¹ := by
            simp [gamma_m]
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              left
              use m
              use s
              use s_in_S
              simp
              rw [← eq_e_i]
              rfl
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              right
              use m
              use s
              use s_in_S
              conv =>
                rhs
                rw [← mul_assoc]
              simp
              rw [← eq_e_i]
              rfl

          have phi_ofmul_gamma: φ (ofMul γ) = 1 := by
            exact hγ

          have gamma_ne_inv: γ ≠ γ⁻¹ := by
            by_contra this
            apply_fun ofMul at this
            apply_fun φ at this
            rw [phi_ofmul_gamma] at this
            rw [ofMul_inv] at this
            rw [AddMonoidHom.map_neg] at this
            rw [phi_ofmul_gamma] at this
            omega

          let gamma_copy: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ⁻¹, by simp [E]⟩
          let gamma_copy_inv: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ⁻¹, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ, by simp [E]⟩

          have gamma_copy_prod: gamma_copy.unattach.prod = γ^m := by
            simp [gamma_copy]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have gamma_copy_inv_prod: gamma_copy_inv.unattach.prod = γ^(-m) := by
            simp [gamma_copy_inv]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have E_inhabited: Inhabited E := by
            use γ
            simp [E]

          have header_prod: (List.takeWhile is_gamma list).unattach.prod = γ^m := by
            have my_lemma := take_count_sum_eq_exp (List.takeWhile is_gamma list) γ gamma_ne_inv ?_
            .
              rw [my_lemma]
            .
              have foo (x: E) := List.mem_takeWhile_imp (p := fun (val: E) => (val = γ ∨ val = γ⁻¹)) (l := list) (x := x)
              conv at foo =>
                intro x hx
                equals ↑x = γ ∨ ↑x = γ⁻¹ =>
                  simp
              exact foo

          -- 'γ^n * a * γ^(_n) * γn * tail', as a list of elements in E
          let mega_list := (gamma_copy ++ [(List.dropWhile is_gamma list)[0]] ++ gamma_copy_inv) ++ (gamma_copy ++ (list.dropWhile is_gamma).tail)
          have mega_list_prod: mega_list.unattach.prod = list.unattach.prod := by
            simp [mega_list]
            simp [gamma_copy_prod, gamma_copy_inv_prod]
            conv =>
              rhs
              rw [eq_split]
              rw [List.unattach_append]
              simp
            have dropwhile_not_nul : (List.dropWhile is_gamma list) ≠ [] := by
              exact tail_nonempty
            apply_fun (fun x => x * (List.dropWhile is_gamma list).unattach.prod⁻¹)
            .
              simp
              conv =>
                pattern _[0]
                equals (List.dropWhile is_gamma list).headI =>
                  rw [← List.head_eq_getElem_zero dropwhile_not_nul]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.head_eq_getElem_zero]
                  exact
                    Eq.symm
                      (List.getI_eq_getElem (List.dropWhile is_gamma list)
                        (List.length_pos_iff.mpr dropwhile_not_nul))

              have unattach_len_pos: 0 < (List.dropWhile is_gamma list).unattach.length := by
                rw [List.length_unattach]
                exact List.length_pos_iff.mpr dropwhile_not_nul

              -- TODO - this is gross, and should be removed
              letI : Inhabited G := {
                default := 1
              }

              conv =>
                lhs
                lhs
                rhs
                equals (List.dropWhile is_gamma list).unattach.headI * (List.dropWhile is_gamma list).unattach.tail.prod =>
                  rw [← List.getI_zero_eq_headI]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.getI_eq_getElem _ (List.length_pos_iff.mpr dropwhile_not_nul)]
                  rw [List.getI_eq_getElem _ unattach_len_pos]
                  simp [List.getElem_unattach _ unattach_len_pos]
                  rw [list_tail_unattach]

              rw [List.headI_mul_tail_prod_of_ne_nil]
              .
                simp
                simp [header_prod]
              .
                by_contra this
                rw [List.eq_nil_iff_length_eq_zero] at this
                rw [List.length_unattach] at this
                rw [← List.eq_nil_iff_length_eq_zero] at this
                contradiction


            . exact mul_left_injective (List.dropWhile is_gamma list).unattach.prod⁻¹

          have sublist_phi_zero: φ (gamma_copy ++ (List.dropWhile is_gamma list).tail).unattach.prod = 0 := by
            rw [← mega_list_prod] at hlist
            unfold mega_list at hlist
            simp at hlist
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [inv_eq_iff_eq_inv.symm] at eq_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist

          have count_head_lt: (List.map (fun (k: E) ↦ if ↑k = γ then (1 : ℤ) else if ↑k = γ⁻¹ then -1 else 0)
          (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list)).sum.natAbs ≤ (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list).length := by
            induction (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list) with
            | nil =>
              simp
            | cons h t ih =>
              simp
              split_ifs
              . omega
              . omega
              . omega

          let rewritten_sub_list := (rewrite_list (gamma_copy ++ (list.dropWhile is_gamma).tail) sublist_phi_zero)
          let return_list := (⟨γ^m * (List.dropWhile is_gamma list)[0] * γ^(-m), in_range⟩) :: rewritten_sub_list.val

          -- Show that the list (rewritten in terms of `γ^m * e_i * γ^(-m)` terms) is in the kernel of φ


          have mega_list_prod_preserve: mega_list.unattach.prod = return_list.unattach.prod := by
            unfold mega_list return_list
            simp
            rw [gamma_copy_prod]
            rw [gamma_copy_inv_prod]
            simp
            rw [← rewritten_sub_list.property]
            simp
            rw [gamma_copy_prod]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← mul_assoc]
              simp
            rw [mul_assoc]

          have return_list_prod: list.unattach.prod = return_list.unattach.prod := by
            rw [← mega_list_prod_preserve]
            exact mega_list_prod.symm


          exact ⟨return_list, return_list_prod⟩
      termination_by list.length
      decreasing_by {
        simp
        split_ifs
        .
          simp
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
        .
          simp-- [count_gamma_copy]
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
      }

      obtain ⟨z_list, h_z_list⟩ := z_eq_prod
      rw [← list_filter_one] at h_z_list
      have z_filter_mem_e: ∀ p ∈ (List.filter (fun s ↦ !decide (s = 1)) z_list), p ∈ E := by
        intro p hp
        dsimp [E]
        simp at hp
        obtain ⟨h_z_list_in, _⟩ := h_z_list
        specialize h_z_list_in p hp.1
        rw [Set.mem_union] at h_z_list_in
        rw [Set.mem_union] at h_z_list_in
        match h_z_list_in with
        | .inl h_z_list_in =>
          simp at h_z_list_in
          obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
          apply Set.mem_union_left
          apply Set.mem_union_right
          simp
          use a
          use a_mem_s
        | .inr h_z_list_in =>
          simp at h_z_list_in
          match h_z_list_in with
          | .inl h_z_list_in =>
            obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
            apply Set.mem_union_right
            simp
            use a
            use a_mem_s
          | .inr h_z_list_in =>
            simp [hp.2] at h_z_list_in
            apply Set.mem_union_left
            apply Set.mem_union_left
            simp
            exact h_z_list_in.symm

      let my_res := rewrite_list ((z_list.filter (fun s ↦ !decide (s = 1))).attach.map (fun (g) => ⟨g.val, z_filter_mem_e g.val g.property⟩)) (by
        simp
        -- TODO - there has to be a less awful way of doing this
        conv =>
          arg 1
          arg 2
          arg 1
          arg 2
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            clear h_z_list

            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        rw [← ofMul_list_prod]
        rw [h_z_list.2]
        exact hz
      )
      have my_res_prop := my_res.property
      rw [← Subgroup.mem_toSubmonoid]
      rw [Subgroup.closure_toSubmonoid _]
      conv =>
        equals z ∈ (Submonoid.closure (Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) : Set _) =>
          rfl
      rw [Submonoid.closure_eq_image_prod]
      rw [Set.mem_image]
      use my_res.val.unattach
      refine ⟨?_, ?_⟩
      . simp only [Set.mem_setOf_eq]
        intro x hx
        rw [List.mem_unattach] at hx
        obtain ⟨x_prop, _⟩ := hx
        exact x_prop
      .
        rw [← my_res_prop]
        conv =>
          pattern List.unattach _
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        exact h_z_list.2
  exact gamma_m_ker_phi

lemma three_two_S_n_subset_ker {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (phi_gamma: φ γ = 1) (n: ℕ):
   ↑(three_two_S_n S φ γ n) ⊆ Additive.toMul '' φ.ker.carrier := by

  intro x hx
  simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at hx
  obtain ⟨m, m_in_range, s, s_mem_s, prod_eq_x⟩ := hx
  apply_fun ofMul at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  apply_fun φ at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  simp at prod_eq_x
  conv at prod_eq_x =>
    arg 1
    arg 2
    equals (ofMul s + -(φ (ofMul s) • ofMul γ)) => rfl

  simp at prod_eq_x
  conv at prod_eq_x =>
    pattern φ (ofMul γ)
    equals φ γ => rfl

  simp [phi_gamma] at prod_eq_x
  simp
  exact id (Eq.symm prod_eq_x)

lemma three_two_S_n_generates  (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ : Additive G) (phi_gamma: φ γ = 1): ∃ n, AddSubgroup.closure (Additive.ofMul '' (three_two_S_n S φ γ (n))) = φ.ker := by
  obtain ⟨n, hn⟩ := three_poly_poly_growth_all_s_n d hG γ φ
  use n
  ext z
  refine ⟨?_, ?_⟩
  . intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      have x_mem: x ∈ three_two_S_n S φ γ n := by
        simp at hx
        exact hx

      obtain ⟨y, hy, hyx⟩ := (three_two_S_n_subset_ker S φ γ phi_gamma n) x_mem
      rw [← hyx]
      exact hy
    | zero =>
      simp
    | add y z y_mem z_mem hy hz =>
      exact (AddSubgroup.add_mem_cancel_right φ.ker hz).mpr hy
    | neg x x_mem hx =>
      exact AddSubgroup.neg_mem φ.ker hx
  . intro hz
    have generates_ker := three_two_gamma_m_generates φ γ phi_gamma

    have hz' : z ∈ Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S) φ γ))) := by
      rw [generates_ker]; exact hz

    have hz'' : z ∈ (Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S) φ γ)))).toSubmonoid := hz'
    rw [Subgroup.closure_toSubmonoid] at hz''
    have exists_prod := Submonoid.exists_list_of_mem_closure (M := Multiplicative (Additive G)) hz''
    obtain ⟨l, l_mem, z_eq_prod⟩ := exists_prod
    rw [← z_eq_prod]
    conv =>
      arg 2
      equals ofMul l.prod => rfl
    apply AddSubgroup.list_sum_mem
    simp only [Additive.forall]
    intro a ha
    specialize l_mem (ofMul a) ha
    rcases (Set.mem_union _ _ _).mp l_mem with l_mem | l_mem
    · obtain ⟨⟨p, s, s_mem⟩, helper_eq_a⟩ := Set.mem_range.mp l_mem
      simp only [Function.uncurry_apply_pair] at helper_eq_a
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      apply (AddSubgroup.mem_toSubgroup' _ (gamma_m_helper φ γ p ⟨s, s_mem⟩)).mp
      rw [AddSubgroup.toSubgroup'_closure]
      simp
      exact hn
    · rw [← AddSubgroup.neg_mem_iff]
      obtain ⟨⟨p, s, s_mem⟩, helper_eq_a⟩ := Set.mem_range.mp (Set.mem_inv.mp l_mem)
      simp only [Function.uncurry_apply_pair] at helper_eq_a
      conv at helper_eq_a =>
        rhs
        equals -ofMul a => rfl
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      apply (AddSubgroup.mem_toSubgroup' _ (gamma_m_helper φ γ p ⟨s, s_mem⟩)).mp
      rw [AddSubgroup.toSubgroup'_closure]
      simp
      exact hn

lemma three_two_ker_fg  (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ): φ.ker.FG := by
  rw [AddSubgroup.fg_iff]
  obtain ⟨γ, hγ⟩ := hφ 1
  obtain ⟨n, hn⟩ := three_two_S_n_generates d hd hG φ γ hγ
  use ofMul '' ↑(three_two_S_n S φ γ n)
  refine ⟨hn, ?_⟩
  rw [Set.finite_image_iff]
  .
    simp
  . intro a b hab
    simpa using hab


-- Extract a generatating set for the kernel of φ
noncomputable def S_n_ker_phi  {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1) (n: ℕ)  : Finset φ.ker := (three_two_S_n S φ γ n).attach.image (fun x => ⟨x.val, (by
obtain ⟨y, hy, hyx⟩ := (three_two_S_n_subset_ker S φ γ hγ n) x.property
rw [← hyx]
exact hy
)⟩) ∪ {0}

omit hGS in
lemma finite_virtually_nilpotent {G: Type*} [Group G] [Finite G]: Group.IsVirtuallyNilpotent G := by
  rw [Group.IsVirtuallyNilpotent]
  use ⊥
  refine ⟨?_, ?_⟩
  . exact Group.isNilpotent_of_subsingleton
    -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
  . infer_instance

end GeneratesNS
