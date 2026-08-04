module

public import Mathlib
public import Gromov.Unitary.HnLowerBound

/-!
# Distinct words in `H_n`

`words_distinct` and the resulting cardinality bound `H_n_ball_S_card` for balls in the word
metric.
-/

public section

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
lemma words_distinct {m : ℕ} (k: Fin m) (c : ℝ) (c_pos : 0 < c) (c_lt : c < 1 / 40)
 (data : HnData)
 (pows_i : Fin m → ℕ)
 (pows_j: Fin m → ℕ)
 (pows_i_le : ∀ i : Fin m, (pows_i i) ≤ c * (H_n_eps data.hd)⁻¹)
 (pows_j_le : ∀ i : Fin m, (pows_j i) ≤ c * (H_n_eps data.hd)⁻¹)
 (pows_lt_eq: ∀ j : Fin m, j < k → pows_i j = pows_j j)
 (pows_j_lt_k: (pows_j k) < (pows_i k)):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^(pows_i i))).prod ≠ (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^(pows_j i))).prod := by


  by_contra!

  nth_rw 2 [← List.prod_take_mul_prod_drop (i := k)] at this
  rw [← List.prod_take_mul_prod_drop (i := k)] at this
  -- TODO - generalize this and PR to mathlib
  conv at this =>
    lhs
    lhs
    arg 1
    equals List.take k (List.ofFn fun (i: Fin k) ↦ ((theorem_3_8_h_n data i).g ^ pows_i ⟨i, by omega⟩)) =>
      --clear a_k_lt pows_i_le pows_j_le pows_ne this
      ext i l
      rw [List.getElem?_take]
      rw [List.getElem?_take]
      simp
      by_cases i_lt_k: i < k
      .
        simp [i_lt_k]
        have i_lt_m: i < m := by omega
        simp [i_lt_m]
      . simp [i_lt_k]

  conv at this =>
    rhs
    lhs
    arg 1
    equals List.take k (List.ofFn fun (i: Fin k) ↦ ((theorem_3_8_h_n data i).g ^ pows_j ⟨i, by omega⟩)) =>
      --clear a_k_lt pows_i_le pows_j_le pows_ne this
      ext i l
      rw [List.getElem?_take]
      rw [List.getElem?_take]
      simp
      by_cases i_lt_k: i < k
      .
        simp [i_lt_k]
        have i_lt_m: i < m := by omega
        simp [i_lt_m]
      . simp [i_lt_k]


  conv at this =>
    lhs
    lhs
    arg 1
    arg 2
    arg 1
    intro i
    rw [pows_lt_eq _ (by
      have i_prop := i.is_lt
      exact i_prop
    )]


  rw [mul_right_inj] at this
  nth_rw 2 [List.ofFn_congr (n := m - k + k) (by
    omega
  )] at this
  rw [List.ofFn_congr (n := m - k + k) (by
    omega
  )] at this
  rw [list_ofFn_drop] at this
  rw [list_ofFn_drop] at this
  nth_rw 2 [List.ofFn_congr (n := m - k - 1 + 1) (by
    omega
  )] at this
  rw [List.ofFn_congr (n := m - k - 1 + 1) (by
    omega
  )] at this
  rw [List.ofFn_succ] at this
  rw [List.prod_cons] at this
  rw [List.ofFn_succ] at this
  rw [List.prod_cons] at this
  apply inv_mul_eq_of_eq_mul at this
  rw [← mul_assoc] at this
  simp at this
  rw [← zpow_natCast] at this
  rw [← zpow_natCast] at this
  rw [← zpow_neg] at this
  rw [← zpow_add] at this


  ring_nf at this
  have rhs_le := H_n_prod_le_k (c := c) (m := m) (k := (m - k - 1)) (a := k) (by omega) c_pos c_lt pows_j data pows_j_le
  ring_nf at rhs_le
  rw [← this] at rhs_le


  -- Fin (5)
  -- Fin (5 + 0)
  -- Fin (0 + 5)

  have lhs_ge: ‖((theorem_3_8_h_n data (k)).g ^ (-(pows_j ⟨k, by omega⟩ : ℤ) + (pows_i ⟨k, by omega⟩))).val.val * (List.ofFn fun (i: Fin (m - k - 1)) ↦ (theorem_3_8_h_n data (1 + i + k)).g ^ pows_i ⟨1 + i + k, by omega⟩).prod.val.val - 1‖ ≥ (9 / 10) * ‖(theorem_3_8_h_n data k).g.val.val - 1‖ := by
    have m_minus_k: m - k - 1 + 1 = m - k := by
      omega

    conv =>
      lhs
      arg 1
      equals ((((theorem_3_8_h_n data ↑k).g ^ (-(pows_j k : ℤ) + ↑(pows_i k)))).val.val - 1) * (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (1 + i + k)).g^(pows_i (⟨1 + i + k, by omega⟩) ))).prod + (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (1 + i + k)).g^(pows_i (⟨1 + i + k, by omega⟩) ))).prod - 1 =>
        rw [sub_mul]
        simp


    have pows_nat: (-((pows_j k) : ℤ) + (pows_i k)) = (((-(pows_j k) : ℤ) + (pows_i k))).toNat := by
      simp
      linarith


    rw [← add_sub]
    grw [(norm_sub_le_norm_add _ _).ge]
    rw [CStarRing.norm_mul_mem_unitary]
    rw [pows_nat]
    rw [zpow_natCast]
    rw [SubmonoidClass.coe_pow]
    rw [SubmonoidClass.coe_pow]
    grw [H_n_single_pow_lower_bound]

    -- TODO : figure out why we can't use 'simp_rw' here
    conv =>
      lhs
      rhs
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      intro i
      simp only [add_comm]
      arg 1
      arg 1
      arg 2
      equals (k.val + 1) + i =>
        group

    conv =>
      lhs
      rhs
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      intro i
      arg 2
      arg 1
      arg 1
      equals (k.val + 1) + i =>
        group

    grw [H_n_prod_le_k (c := c)]
    . linarith
    .
      rw [add_assoc]
      rw [m_minus_k]
      simp
    . exact c_pos
    . exact c_lt
    . exact pows_i_le
    .
      linarith
    .
      conv =>
        lhs
        equals (-((pows_j k) : ℝ) + ((pows_i k) : ℝ)) =>
          rw [add_comm]
          rw [← sub_eq_add_neg]
          rw [add_comm]
          rw [← sub_eq_add_neg]
          simp
          rw [Nat.cast_sub (by linarith)]

      rw [add_comm]
      rw [← sub_eq_add_neg]
      have pow_j_ge: 0 ≤ (pows_j k : ℝ) := by
        positivity
      grw [pows_i_le]
      grw [pow_j_ge.ge]
      simp
      grw [c_lt]
      apply mul_le_mul
      . norm_num
      .
        rw [inv_le_inv₀]
        .
          have my_prop := (theorem_3_8_h_n data k).g_dist
          exact my_prop
        . apply H_n_eps_pos
        . have my_prop := (theorem_3_8_h_n data k).g_dist_nonzero
          positivity
      . simp
        exact (H_n_eps_pos data.hd).le
      . norm_num
      . simp
        have foo := H_n_eps_pos data.hd
        linarith
    . simp [-SubmonoidClass.coe_list_prod]


  rw [ge_iff_le] at lhs_ge

  have one_tenth_lt:  1 / 10 * ‖(theorem_3_8_h_n data ↑k).g.val.val - 1‖ < (9 / 10) * ‖(theorem_3_8_h_n data ↑k).g.val.val - 1‖ := by
    apply mul_lt_mul
    . norm_num
    . simp
    .
      have ne_zero := (theorem_3_8_h_n data ↑k).g_dist_nonzero
      positivity
    . norm_num


  have add_swap (a b : ℕ): 1 + a + b = 1 + b + a := by
    omega

  have add_swap_pows_i (a b: ℕ) (add_lt: 1 + a + b < m): pows_i ⟨1 + a + b, by omega⟩ = pows_i ⟨1 + b + a, by omega⟩ := by
    simp_rw [add_swap]


  grw [lhs_ge] at one_tenth_lt
  ring_nf at one_tenth_lt
  conv at rhs_le =>
    lhs
    arg 1
    lhs
    rhs
    rhs
    rhs
    arg 1
    arg 1
    intro i
    rw [add_swap_pows_i]
    lhs
    rw [add_swap]


  norm_cast at rhs_le
  norm_cast at one_tenth_lt
  grw [rhs_le] at one_tenth_lt
  simp at one_tenth_lt


#print axioms words_distinct

-- ContinuousLinearMap.norm_id


omit h_n_eps_data in
lemma list_prod_pow {T: Type*} [Group T] (m: ℕ) (elems: Fin m → T) (pows: Fin m → ℕ):
  (List.ofFn (fun (i: Fin m) => (elems i)^(pows i))).prod = (List.ofFn (fun (i : Fin m) => List.replicate (pows i) (elems i))).flatten.prod := by

  induction m with
  | zero =>
    simp
  | succ m ih =>
    have prod_eq := ih (Fin.init elems) (Fin.init pows)
    rw [List.ofFn_succ']
    rw [List.ofFn_succ']
    simp
    simpa [Fin.init] using prod_eq

lemma H_n_pows_mem_ball_G {m : ℕ}
  (data : HnData) (pows : Fin m → ℕ)
  (c: ℝ)
  (pows_le : ∀ i : Fin m, (pows i) ≤ ⌊c * (H_n_eps data.hd)⁻¹⌋₊):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod.val ∈ (data.G.carrier ^ (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹)))) := by

  let replicate_pow (i: Fin m) := List.replicate (pows i) ((theorem_3_8_h_n data i).g)
  let nested_list := List.ofFn (fun (i : Fin (m)) => replicate_pow i)
  let nested_prod := List.prod_flatten (l := nested_list)
  conv at nested_prod =>
    rhs
    equals (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod =>
      simp [nested_list, replicate_pow]
      apply congr (rfl)
      ext i g
      simp


  rw [Set.mem_pow]
  -- We have an upper bound for the list, so pad out the list with '1's to reach the upper bound
  let base_list := (fun (i: Fin (nested_list.flatten.length)) => nested_list.flatten[i])
  let full_list := Fin.append base_list (fun (i: Fin (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) - nested_list.flatten.length)) => 1)

  have len_le_upper: nested_list.flatten.length ≤ (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹))) := by
    simp [nested_list, replicate_pow]
    simp [Fin.sum_ofFn]
    grw [Finset.sum_le_card_nsmul (n := ⌊ (c * (H_n_eps data.hd)⁻¹)⌋₊)]
    . simp
    . intro x _
      apply pows_le


  use (fun i => full_list (i.cast (by omega)))
  .


    conv =>
      lhs
      equals (List.ofFn (fun (i: Fin ((m * (Nat.floor (c * (H_n_eps data.hd)⁻¹))))) => (full_list (i.cast (by omega))))).prod.val =>
        simp
        apply congr (rfl)
        ext i g
        simp


    simp only [full_list, base_list]
    rw [← List.ofFn_congr]
    rw [List.ofFn_fin_append]
    rw [list_prod_pow]
    conv =>
      lhs
      arg 1
      arg 1
      lhs
      equals nested_list.flatten =>
        ext i g
        simp [-List.length_flatten, List.getElem?_eq_some_iff]

    dsimp [nested_list, replicate_pow]
    rw [List.prod_append]
    . simp [-List.prod_flatten]
    . omega


#print axioms H_n_pows_mem_ball_G

-- Unfold the commutators from theorem_3_8_h_n as a list of elements
@[expose]
noncomputable def theorem_3_8_h_n_list (data: HnData) (m: ℕ): List (data.S) :=
  match m with
  | 0 => [data.h]
  | a + 1 => [(theorem_3_8_h_n_left_S data (theorem_3_8_h_n data a)).choose]
              ++ theorem_3_8_h_n_list data a
              ++ [⟨(theorem_3_8_h_n_left_S data (theorem_3_8_h_n data a)).choose.val⁻¹, (by
                apply data.S_inv
                simp
              )⟩]
              ++ (List.map (fun s => ⟨s.val⁻¹, by apply data.S_inv; simp⟩) (theorem_3_8_h_n_list data a)).reverse


set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
lemma theorem_3_8_h_n_list_prod_eq (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data m).unattach.prod = (theorem_3_8_h_n data m).g := by
  induction m with
  | zero =>
    unfold theorem_3_8_h_n_list
    simp [theorem_3_8_h_n]
  | succ a ih =>
    unfold theorem_3_8_h_n_list
    simp [theorem_3_8_h_n]
    simp [Bracket.bracket]
    rw [ih]
    conv =>
      lhs
      rhs
      rhs
      rhs
      arg 1
      arg 1
      equals List.map Inv.inv (theorem_3_8_h_n_list data a).unattach =>
        ext i g
        simp


    rw [← List.prod_inv_reverse]
    rw [ih]
    group

-- Note - this is (2^(m - 1)) in Vikman, since the list in indexed starting at 1 in the paper
set_option synthInstance.maxHeartbeats 1000000 in
lemma theorem_3_8_h_n_list_length_initial_upper_bound  (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data (m)).length ≤ (3 * (2 ^ (m))) - 2 := by
  induction m with
  | zero =>
    unfold theorem_3_8_h_n_list
    simp
  | succ a ih =>
    unfold theorem_3_8_h_n_list
    -- TODO - can grind somehow solve all of this?
    simp
    grw [ih]
    ring
    rw [Nat.sub_mul]
    ring
    zify
    rw [Nat.cast_sub]
    .
      push_cast
      ring
      rw [Nat.cast_sub]
      . push_cast
        ring
        linarith
      .
        by_cases a_eq_zero: a = 0
        .
          simp [a_eq_zero]
        .
          have a_eq_sub_succ: a = (a - 1) + 1 := by omega
          rw [a_eq_sub_succ]
          rw [Nat.pow_succ]
          rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          apply Nat.le_mul_of_pos_right
          positivity
    .
      rw [← ge_iff_le]
      grw [(Nat.one_le_pow _ _ ?_).ge]
      . norm_num
      . norm_num


-- The c' constant from Vikman
@[expose]
def c' := 3

-- TODO - figure out how to merge this with 'theorem_3_8_h_n_list_length_initial_upper_bound'
lemma theorem_3_8_h_n_list_length_upper_bound  (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data (m)).length ≤ c' * (2 ^ m) := by
  grw [theorem_3_8_h_n_list_length_initial_upper_bound data m]
  simp [c']


omit h_n_eps_data in
lemma list_concat_unattach {T: Type*} {p: T → Prop} (l: List { x: T // p x}) (a: { x: T // p x}): (l.concat a).unattach = l.unattach.concat a.val := by
  simp


lemma H_n_pows_mem_ball_S {m : ℕ}
  (m_gt: 0 < m) (data : HnData) (pows : Fin m → ℕ)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (pows_le : ∀ i : Fin m, (pows i) ≤ ⌊c * (H_n_eps data.hd)⁻¹⌋₊):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod.val ∈ Subtype.val '' (data.S ^ ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m))) := by

  rw [Set.mem_image]
  simp_rw [Set.mem_pow]
  use (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod


  -- A list with the same product as g_list, but expressed in terms of elements of S
  let g_as_s_list := (List.ofFn (fun (i: Fin m) => List.replicate (pows i) (theorem_3_8_h_n_list data i))).flatten.flatten


  have g_as_list_prod_eq_pow: g_as_s_list.unattach.prod = (List.ofFn (fun (i: Fin m) => (List.replicate (pows i) (theorem_3_8_h_n_list data i)).flatten.unattach.prod)).unattach.prod := by
    dsimp [g_as_s_list]
    clear m_gt
    induction m with
    | zero =>
      simp
    | succ m ih =>
      have prev_prod := ih (Fin.init pows) (by
        intro i
        apply pows_le
      )
      nth_rw 2 [List.ofFn_succ']
      simp only [Fin.init] at prev_prod
      conv =>
        rhs
        pattern List.ofFn _
        arg 1
        intro i
        simp


      rw [List.ofFn_succ']
      conv at prev_prod =>
        rhs
        pattern List.ofFn _
        arg 1
        intro i
        simp


      rw [list_concat_unattach]
      rw [List.prod_concat]
      rw [← prev_prod]
      simp


  have g_list_mem := H_n_pows_mem_ball_G data pows c pows_le
  rw [Set.mem_pow] at g_list_mem
  obtain ⟨g_list, g_list_prod⟩ := g_list_mem


  have lists_prod_eq: g_as_s_list.unattach.prod = (List.ofFn g_list).unattach.prod := by
    rw [g_as_list_prod_eq_pow]
    conv =>
      rhs
      unfold List.unattach
    simp only [List.map_ofFn]
    rw [Function.comp_def]
    rw [g_list_prod]
    simp
    simp_rw [theorem_3_8_h_n_list_prod_eq]
    unfold List.unattach
    simp [Function.comp_def]


  have g_as_s_list_len: g_as_s_list.length ≤ c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m) := by
    simp [g_as_s_list]
    rw [List.sum_ofFn]
    simp
    grw [Finset.sum_le_sum (g := fun i => (pows i) * c' * (2 ^ m))]
    .
      grw [Finset.sum_le_card_nsmul (n := ⌊c * (H_n_eps data.hd)⁻¹⌋₊ * c' * (2^m))]
      .
        simp
        ring
        rfl
      .
        intro i _
        grw [pows_le]
    . intro i _
      grw [theorem_3_8_h_n_list_length_upper_bound]
      ring
      grw [i.isLt]
      simp


  let padded_list := Fin.append (fun (i: Fin (g_as_s_list.length)) => g_as_s_list[i]) (fun (i: Fin (((c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m)) - g_as_s_list.length))) => ⟨1, data.S_one⟩)


  refine ⟨?_, rfl⟩
  .
    use (fun i => padded_list (i.cast (by omega)))
    conv =>
      lhs
      equals (List.ofFn (fun i => padded_list i)).unattach.prod =>
        simp
        apply congr (rfl)
        ext i g
        nth_rw 2 [List.ofFn_congr (n := (c' * ⌊c * (H_n_eps data.hd)⁻¹⌋₊ * m * 2 ^ m))]
        . simp
        . omega


    rw [List.ofFn_fin_append]
    simp
    rw [Subtype.ext_iff]
    rw [lists_prod_eq]
    conv at g_list_prod =>
      lhs
      equals (List.ofFn g_list).unattach.prod =>
        apply congr rfl
        ext i g
        simp
    rw [g_list_prod]

#print axioms H_n_pows_mem_ball_S


-- In Vikman, this is (1 + ⌊c * (H_n_eps data.hd)⁻¹⌋₊) (since the powers include the upper bound of c*ε ⁻¹)
-- However, the proof works fine with the weaker lower bound ⌊c * (H_n_eps data.hd)⁻¹⌋₊
-- so I'm using that instead (since it avoids the need to deal with different Fin values)
lemma H_n_ball_S_card {m : ℕ}
  (m_gt: 0 < m) (data : HnData)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40):
  (⌊c * (H_n_eps data.hd)⁻¹⌋₊)^m ≤  #(data.S_finite.toFinset ^ ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m))) := by


  let my_set: Finset (Fin m → Fin (⌊c * (H_n_eps data.hd)⁻¹⌋₊)) := Finset.univ
  have my_card := Finset.card_univ (α := (Fin m → Fin (⌊c * (H_n_eps data.hd)⁻¹⌋₊)))
  rw [Fintype.card_pi_const] at my_card
  conv at my_card =>
    rhs
    simp


  rw [← my_card]
  apply Finset.card_le_card_of_injOn (f := fun pows => (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^((pows i).val))).prod)
  .
    intro pows _
    simp
    -- TODO - modify H_n_pows_mem_ball_S so that this can just be 'apply'
    have my_pows := H_n_pows_mem_ball_S m_gt data (fun i => (pows i).val) c c_pos c_lt ?_
    .
      rw [Set.mem_image] at my_pows
      obtain ⟨g, g_mem, g_eq⟩ := my_pows
      rw [← Subtype.ext_iff] at g_eq
      rw [← g_eq]
      exact g_mem
    . intro i
      simp
  .
    intro pows_i _ pows_j _
    contrapose
    intro pows_neq
    rw [funext_iff] at pows_neq
    simp at pows_neq

    have exists_minimal_k := exists_minimal_of_wellFoundedLT (fun (i: Fin m) => pows_i i ≠ pows_j i) pows_neq
    obtain ⟨k, k_minimal⟩ := exists_minimal_k
    -- TODO - figure out why this pushes a goal of 'False' if we don't use 'generalizing'
    wlog pow_j_lt_i: (pows_j k).val < (pows_i k).val generalizing pows_i pows_j

    .
      conv at k_minimal =>
        arg 1
        intro i
        rw [ne_comm]


      have words_neq := this (pows_j := pows_i) (pows_i := pows_j) (by simp) (by simp) ?_ k_minimal ?_
      .
        rw [eq_comm]
        exact words_neq
      .
        obtain ⟨x, hx⟩ := pows_neq
        use x
        exact fun a ↦ hx (id (Eq.symm a))
      .
        have k_neq := k_minimal.prop
        omega
    .
      simp at k_minimal

      have eps_pos := H_n_eps_pos data.hd

      have prods_neq := words_distinct (m := m) k c c_pos c_lt data (fun i => pows_i i) (fun i => pows_j i) ?_ ?_ ?_ ?_
      . simpa using prods_neq
      .
        intro i
        rw [← Nat.le_floor_iff]
        omega
        positivity
      . intro i
        rw [← Nat.le_floor_iff]
        omega
        positivity
      .
        intro j hk
        have foo := Minimal.not_prop_of_lt k_minimal hk
        simp at foo
        exact congrArg Fin.val foo
      .
        simpa using pow_j_lt_i


#print axioms H_n_ball_S_card

abbrev swap_le {a b: ℝ} (_: a ≤ b): Prop := b < a

-- Our lower bound gives us a contradiction with polynomial growth

end HnEpsData
