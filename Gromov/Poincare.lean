module

public import Mathlib
public import Gromov.Packing

/-!
# The Poincaré inequality

`poincare_inequality` and the packing-averaged form `lemma_3_25_poincare`.
-/

@[expose] public section

set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

noncomputable def f_avg (R: ℝ) (f : G → ℝ) := (#((finite_closed_ball 1 R).toFinset) : ℝ)⁻¹ * ∑ y ∈ (finite_closed_ball 1 R).toFinset, f y
noncomputable def f_avg_c (g: G) (R: ℝ) (f : G → ℝ) := (#((finite_closed_ball 1 R).toFinset) : ℝ)⁻¹ * ∑ y ∈ B_c_r g R, f y

noncomputable def deriv_sq_R (f: G → ℝ) (x: G) := ∑ s ∈ S, (f (x * s) - f x)^2

-- Reindexing `s ↦ s⁻¹` over the symmetric generating set `S` turns a right-gradient of
-- `f ∘ (·⁻¹)` into a left-gradient of `f` at the inverted point.
omit v_wrapper_inst in
lemma deriv_sq_R_inv_comp (f: G → ℝ) (x: G):
    deriv_sq_R (fun y => f y⁻¹) x = deriv_sq f x⁻¹ := by
  unfold deriv_sq_R deriv_sq
  apply Finset.sum_nbij' (i := fun s => s⁻¹) (j := fun s => s⁻¹) <;>
    simp +contextual [hGS.has_inv, mul_inv_rev]

omit v_wrapper_inst in
lemma three_term_cs (a b: ℝ) (n: Type*) {s: Finset n} (f: n → ℝ): a + (∑ x ∈ s, f x) + b ≤ √(a^2 + (∑ x ∈ s, (f x)^2) + b^2) * √(2 + #(s)) := by
  conv =>
    lhs
    equals ∑ x ∈ (s.disjSum {a}).disjSum {b}, (x.elim (fun y => y.elim f id) id) * 1 =>
      simp
      rw [add_comm]

  grw [Real.sum_mul_le_sqrt_mul_sqrt]
  simp
  grind

omit v_wrapper_inst in
lemma ball_x_one_subset (x: G): (Metric.closedBall x 1) ⊆ ((x) • S) ∪ ((MulOpposite.op x • S))  := by
  intro a ha
  simp
  simp at ha
  rw [Set.mem_smul_set]
  simp [dist, WordDist] at ha
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod_self (x * a⁻¹)
  simp [ProdS] at l_prod
  by_cases l_len_eq: l.length = 0
  .
    have l_eq: l = [] := by grind
    simp [l_eq] at l_prod
    rw [eq_comm, mul_inv_eq_one] at l_prod
    left
    use 1
    simp [one_mem]
    grind
  .
    rw [← l_len] at ha
    have l_len_one: l.length = 1 := by grind
    rw [List.length_eq_one_iff] at l_len_one
    obtain ⟨s, hs⟩ := l_len_one
    simp [hs] at l_prod
    right
    use s⁻¹
    simp
    rw [eq_comm, mul_inv_eq_iff_eq_mul] at l_prod

    rw [l_prod]
    refine ⟨?_, ?_⟩
    .
      rw [← Finset.mem_inv']
      rw [← S_eq_Sinv]
      simp
    .
      simp [l_prod]
omit v_wrapper_inst in
lemma le_of_sub_eq (a b c: ℝ) (ha: a = b - c) (hc: 0 ≤ c): a ≤ b := by
  grind

lemma double_ball_sum (R: ℕ) (hR: 0 < R) (f: G → ℝ) (hf: ∀ g, 0 ≤ f g): ∑ x ∈ B_r (↑(R - 1)), ∑ y ∈ (Metric.closedBall x 1), f y ≤ 2 * #S * ∑ x ∈ B_r R, f x := by
  classical

  grw [Finset.sum_le_sum (g := fun x =>  ∑ y ∈ ((x) • S) ∪ ((MulOpposite.op x • S)), f y)]
  .
    have union_sub (x: G) := Finset.sum_union_inter (f := f) (s₁ := x • S) (s₂ := (MulOpposite.op x • S))
    simp_rw [← eq_sub_iff_add_eq] at union_sub
    have foo (x) := le_of_sub_eq _ _ _ (union_sub x) (by
      apply Finset.sum_nonneg
      simp [hf]
    )
    grw [Finset.sum_le_sum (h := fun x hx => foo x)]

    simp_rw [← Finset.image_smul]
    conv =>
      lhs
      arg 2
      intro x
      rw [Finset.sum_image (by simp)]
      rw [Finset.sum_image (by simp)]

    have card_le (i: G) : #({a ∈ B_r ↑(R - 1) ×ˢ S | a.1 • a.2 = i}) ≤ #S := by
      apply Finset.card_le_card_of_injOn (f := fun p => p.1⁻¹ * i)
      . intro a ha
        simp at ha
        simp
        simp [← ha.2]
        grind
      . intro a ha b hb hab
        simp at hab
        simp at ha
        simp at hb
        have ha_2 := ha.2
        have hb_2 := hb.2
        rw [Prod.ext_iff]
        rw [← ha_2] at hb_2
        simp [hab] at hb_2
        grind

    have card_le_rev (i: G) : #({a ∈ B_r ↑(R - 1) ×ˢ S | a.2 * a.1 = i}) ≤ #S := by
      apply Finset.card_le_card_of_injOn (f := fun p => i * p.1⁻¹)
      . intro a ha
        simp at ha
        simp
        simp [← ha.2]
        grind
      . intro a ha b hb hab
        simp at hab
        simp at ha
        simp at hb
        have ha_2 := ha.2
        have hb_2 := hb.2
        rw [Prod.ext_iff]
        rw [← ha_2] at hb_2
        simp [hab] at hb_2
        grind

    simp_rw [Finset.sum_add_distrib]
    rw [← Finset.sum_product']
    rw [← Finset.sum_product']
    simp_rw [Finset.sum_comp]
    grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r R)]
    .
      grw [Finset.sum_le_sum (g := fun i => #S • f i)]
      .
        simp
        rw [← Finset.mul_sum]
        rw [add_comm]
        grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r R)]
        .
          grw [Finset.sum_le_sum (g := fun i => #S • f i)]
          .
            simp
            rw [← Finset.mul_sum]
            rw [← mul_add]
            grind
          .
            intro i hi
            simp
            -- TODO - why doesn't grw work here
            apply mul_le_mul
            . simp
              apply card_le_rev
            . simp
            . apply hf
            . simp
        .
          rw [Finset.image_subset_iff]
          intro x hx
          simp at hx
          simp [B_r, dist, WordDist_one]
          grw [word_norm_mul_le]
          simp [B_r, dist, WordDist_one] at hx
          grw [hx.1]
          have norm_s := word_norm_le x.2 [⟨x.2, hx.2⟩] (by simp [ProdS])
          grw [norm_s]
          simp [hR]
          grind
        . intros
          apply mul_nonneg
          . simp
          . apply hf
      . intro i hi
        grw [card_le]
        apply hf

    . rw [Finset.image_subset_iff]
      intro x hx
      simp at hx
      simp [B_r, dist, WordDist_one]
      grw [word_norm_mul_le]
      simp [B_r, dist, WordDist_one] at hx
      grw [hx.1]
      have norm_s := word_norm_le x.2 [⟨x.2, hx.2⟩] (by simp [ProdS])
      grw [norm_s]
      simp [hR]
    . intros
      simp
      apply mul_nonneg
      . simp
      . apply hf
  . intro i hi
    grw [Finset.sum_le_sum_of_subset_of_nonneg]
    .
      simp
      apply ball_x_one_subset
    . intros
      apply hf

-- TODO - get rid of some lemmas, since mathlib already has Metric.smul_closedBall defined

-- Theorem 3.20
set_option maxHeartbeats 3500000 in
lemma poincare_inequality (R: ℕ) (f: G → ℝ): ∑ x ∈ (B_r (R - 1)), |f x - (f_avg (R - 1) f)|^2 ≤
    16 * R^2 * #S * (#(B_r (2 * R - 2))) / #(B_r (R - 1)) * ∑ x ∈ (B_r (3 * R)), deriv_sq_R f x := by

  by_cases R_nonpos: R = 0
  .
    simp [R_nonpos, f_avg, B_r]

  let δ_f (x: G) := ∑ x ∈ (finite_closed_ball x 1).toFinset, deriv_sq_R f x

  have f_sub_le (x: G): |f x - f_avg (R - 1) f| ≤ √((#((B_r (R - 1))) : ℝ)⁻¹ * (∑ y ∈ (B_r (R - 1)), (f x - f y)^2)) := by
    rw [f_avg]
    conv =>
      lhs
      arg 1
      arg 1
      equals (#((B_r (↑R - 1))) : ℝ)⁻¹ * ∑ y ∈ (B_r (↑R - 1)), f x =>
        simp
        rw [inv_mul_cancel_left₀]
        simp [B_r]
        exact Set.ncard_ne_zero_of_mem (a := 1) (by simp; grind) (finite_closed_ball 1 _)

    rw [B_r]
    rw [← mul_sub]
    rw [abs_mul]
    rw [← Finset.sum_sub_distrib]
    grw [Finset.abs_sum_le_sum_abs]
    conv =>
      lhs
      rhs
      arg 2
      intro i
      equals |f x - f i| * 1 => simp
    grw [Real.sum_mul_le_sqrt_mul_sqrt]
    simp [Real.sqrt_eq_rpow]
    rw [← Real.rpow_neg_one]
    rw [mul_comm]
    rw [mul_assoc]
    rw [← Real.rpow_add]
    .
      norm_num
      simp
      rw [Real.mul_rpow]
      .
        field_simp
        rw [← Real.rpow_mul]
        .
          simp
        . positivity
      . positivity
      . positivity

    . simp
      rw [Set.ncard_pos (finite_closed_ball 1 _)]
      exact ⟨1, by simp; grind⟩

  let γ (z: G) (i: ℕ) := ((word_norm_prod_self z).choose.take i).unattach.prod
  have gamma_zero (z: G): γ z 0 = 1 := by simp [γ]
  have gamma_norm (z: G): γ z (WordNorm z) = z := by
    simp [γ]
    obtain ⟨prod, len_eq⟩ := (word_norm_prod_self z).choose_spec
    simp [ProdS] at prod
    conv =>
      arg 1
      pattern (WordNorm z)
      rw [← len_eq]

    simp
    exact prod

  have gamma_i_norm_le (z: G) (i: ℕ): WordNorm (γ z i) ≤ i := by
    simp [γ]

    have i_le := word_norm_le ((word_norm_prod_self z).choose.take i).unattach.prod ((word_norm_prod_self z).choose.take i) (by simp [ProdS])
    grw [List.length_take_le] at i_le
    exact i_le

  have gamma_sum (z: G) (hz: z ∈ B_r (2*R - 2)): ∑ x ∈ B_r (R - 1), ∑ i ∈ Finset.range (WordNorm z), δ_f (x * (γ z i)) ≤ 2 * R * ∑ x ∈ B_r (3*R - 1), δ_f x := by

    rw [← Finset.sum_product']
    rw [Finset.sum_comp]
    simp
    grw [Finset.sum_le_sum (g := fun a => (((2 * R) : ℝ) * (δ_f a)))]
    .
      rw [← Finset.mul_sum]
      grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r (3*R - 1))]
      .
        intro p hp
        simp at hp
        obtain ⟨a, b, ⟨a_mem, b_lt⟩, p_eq⟩ := hp
        rw [← p_eq]
        simp [B_r, dist, WordDist_one]
        grw [word_norm_mul_le]
        simp [B_r, dist, WordDist_one] at a_mem
        simp [B_r, dist, WordDist_one] at hz
        simp
        grw [a_mem]
        grw [gamma_i_norm_le]
        grw [b_lt]
        grw [hz]
        grind
      . intro p hp _
        simp [δ_f, deriv_sq_R]
        positivity
    .
      intro b hb
      simp at hb
      obtain ⟨x, n, ⟨x_mem, n_lt⟩, b_eq⟩ := hb
      grw [Finset.card_le_card (t := (Finset.range (2 * R)).image (fun n => (b * ((γ z n)⁻¹), n)))]
      .
        grw [Finset.card_image_le]
        . simp
        . simp [δ_f, deriv_sq_R]
          positivity
      .
        simp [δ_f, deriv_sq_R]
        positivity
      .
        intro p hp
        simp at hp
        simp
        use p.2
        refine ⟨?_, ?_⟩
        .

          by_contra!
          grw [hp.1.2] at this
          simp [B_r, dist, WordDist_one] at hz
          conv at hz =>
            rhs
            equals ↑(2*R - 2) =>
              rw [Nat.cast_sub]
              simp
              grind

          norm_cast at hz
          grind
        .
          ext
          . simp [← hp.2]
          . simp

  have diff_le_delta_sum (x y: G) (hx: x ∈ B_r (R - 1)) (hy: y ∈ B_r (R - 1)): |f y - f x| ≤ √((2 * R) * (∑ i ∈ Finset.range (WordNorm (x⁻¹ * y)), δ_f (x * γ (x⁻¹ * y) i))) := by

    have inv_prod_le: WordNorm (x⁻¹ * y) ≤ 2*R - 2 := by
      grw [word_norm_mul_le]
      rw [← word_norm_inv]
      simp [B_r, dist, WordDist_one] at hx hy
      conv at hx =>
        rhs
        equals ↑(R - 1) =>
          rw [Nat.cast_sub]
          simp
          grind
      conv at hy =>
        rhs
        equals ↑(R - 1) =>
          rw [Nat.cast_sub]
          simp
          grind
      norm_cast at hx hy
      grw [hx, hy]
      grind

    have root_le_R: √(WordNorm (x⁻¹ * y)) ≤ √(2*R) := by
      rw [Real.sqrt_le_sqrt_iff]
      . norm_cast
        grw [inv_prod_le]
        simp
      . simp

    conv =>
      lhs
      equals |(f (x * γ (x⁻¹ * y) (WordNorm (x⁻¹ * y)))) - f (x * γ (x⁻¹ * y) 0)| =>
        simp [gamma_zero, gamma_norm]

    rw [← Finset.sum_range_sub (n := WordNorm (x⁻¹ * y)) (f := fun i => f (x * γ (x⁻¹ * y) i))]
    grw [Finset.abs_sum_le_sum_abs]
    conv =>
      lhs
      arg 2
      intro i
      rw [← mul_one (a := |_|)]

    grw [Real.sum_mul_le_sqrt_mul_sqrt]
    simp
    grw [root_le_R]

    have sum_le_delta: ∑ x_1 ∈ Finset.range (WordNorm (x⁻¹ * y)), (f (x * γ (x⁻¹ * y) x_1) - f (x * γ (x⁻¹ * y) (x_1 + 1))) ^ 2 ≤ ∑ n ∈ Finset.range (WordNorm (x⁻¹ * y)), δ_f (x * (γ (x⁻¹ * y) n)) := by
      apply Finset.sum_le_sum
      intro n hn
      simp [δ_f, deriv_sq_R]
      rw [← Finset.add_sum_erase (a := (x * γ (x⁻¹ * y) n))]
      .
        apply le_add_of_le_of_nonneg
        .
          let s := (word_norm_prod_self (x⁻¹ * y)).choose[n]?.getD ⟨1, one_mem⟩
          rw [← Finset.add_sum_erase (a := s.val) (h := by simp)]
          apply le_add_of_le_of_nonneg
          .
            rw [sub_sq_comm]
            conv =>
              rhs
              lhs
              arg 1
              arg 1
              equals x * γ (x⁻¹ * y) (n + 1) =>

                rw [mul_assoc, mul_left_cancel_iff]
                simp [γ, s]
                -- TODO - we can probably use hn instead of this case split
                by_cases n_add_lt: (n) < (word_norm_prod_self (x⁻¹ * y)).choose.length
                .
                  simp [n_add_lt]
                  rw [List.take_add_one]
                  simp
                  rw [getElem?_pos]
                  . simp
                  . grind
                .
                  simp [n_add_lt]
                  rw [List.take_add_one]
                  simp
                  rw [getElem?_neg]
                  . simp
                  . grind
          . positivity
        . positivity
      . simp [dist, WordDist, word_norm_one]

    simp_rw [sub_sq_comm]
    grw [sum_le_delta]
    rw [mul_comm]
    simp

  conv at f_sub_le =>
    intro x
    rw [Real.le_sqrt (by
      simp
    ) (by
      positivity
    )]
  grw [Finset.sum_le_sum (h := fun x hx => f_sub_le x)]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  rw [← Finset.mul_sum]
  rw [inv_mul_le_iff₀ (by norm_cast; simp; simp [B_r]; grind)]
  conv at diff_le_delta_sum =>
    intro x y hx hy
    rw [Real.le_sqrt (by simp) (by
      simp [δ_f, deriv_sq_R];
      positivity
    )]
  simp_rw [sq_abs] at diff_le_delta_sum
  grw [Finset.sum_le_sum (h := fun a ha => diff_le_delta_sum a.2 a.1 (by
    simp at ha
    simp [B_r]
    simp [B_r] at ha
    grind
  )
  (by
    grind
  ))]
  simp_rw [← Finset.mul_sum]
  rw [mul_comm]
  rw [← le_div_iff₀ (by simp; grind)]
  rw [Finset.sum_product]
  simp only []
  rw [Finset.sum_comm]
  -- TODO - use gcongr here
  grw [Finset.sum_le_sum (g := fun z => ∑ x ∈ B_r (2*R - 2), ∑ i ∈ Finset.range (WordNorm x), δ_f (z * γ x i))]
  .
    rw [Finset.sum_comm]
    grw [Finset.sum_le_sum (h := gamma_sum)]
    simp [δ_f]
    have b_card_ne : #(B_r (↑R - 1)) ≠ 0 := by
      simp [B_r]
      exact Set.ncard_ne_zero_of_mem (a := 1) (by simp; grind) (finite_closed_ball 1 _)
    have b_card_two_ne: #(B_r (2 * (↑R - 1))) ≠ 0 := by
      simp [B_r]
      exact Set.ncard_ne_zero_of_mem (a := 1) (by simp; grind) (finite_closed_ball 1 _)
    field_simp
    norm_num
    conv =>
      lhs
      rhs
      arg 1
      arg 1
      equals ↑(R*3 - 1) =>
        rw [Nat.cast_sub]
        simp
        grind
    grw [double_ball_sum]
    .
      norm_cast

      have four_le: (4: ℝ) ≤ 8 := by
        grind
      grw [four_le]
      simp [deriv_sq_R]
      ring
      simp
      simp [deriv_sq_R]
      positivity
    . simp
      grind
    . intro g
      simp [deriv_sq_R]
      positivity

  . intro a ha
    rw [Finset.sum_comp (g := fun y => a⁻¹ * y) (f := fun x => ∑ x_1 ∈ Finset.range (WordNorm (x)), δ_f (a * γ (x) x_1))]
    grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r (2*R - 2))]
    .
      simp_rw [inv_mul_eq_iff_eq_mul]
      simp_rw [Finset.card_filter]
      simp
      apply Finset.sum_le_sum
      intro x hx
      split_ifs
      . simp
      . simp [δ_f, deriv_sq_R]
        positivity
    .
      rw [Finset.image_subset_iff]
      intro x hx
      simp [B_r, dist, WordDist_one]
      simp [B_r, dist, WordDist_one] at ha hx
      grw [word_norm_mul_le]
      rw [← word_norm_inv]
      simp
      grw [ha, hx]
      grind
    .
      intros
      simp [δ_f, deriv_sq_R]
      positivity

#print axioms poincare_inequality

-- `B_r` is centred at `1`, so it is closed under inversion (`word_norm_inv`).
omit v_wrapper_inst in
lemma mem_B_r_inv (r: ℝ) (x: G): x⁻¹ ∈ B_r r ↔ x ∈ B_r r := by
  simp [B_r, dist, WordDist_one, ← word_norm_inv]

lemma sum_B_r_inv (r: ℝ) (g: G → ℝ): ∑ x ∈ B_r r, g x⁻¹ = ∑ x ∈ B_r r, g x := by
  apply Finset.sum_nbij' (i := fun x => x⁻¹) (j := fun x => x⁻¹) <;>
    simp +contextual [mem_B_r_inv]

lemma f_avg_inv (r: ℝ) (f: G → ℝ): f_avg r (fun y => f y⁻¹) = f_avg r f := by
  unfold f_avg
  rw [show (finite_closed_ball (1: G) r).toFinset = B_r r from rfl, sum_B_r_inv]

-- Theorem 3.20, restated for the *left* Cayley graph. Rather than mirroring the (long) proof of
-- `poincare_inequality`, we conjugate it by the inversion `x ↦ x⁻¹`: this is a bijection of every
-- `B_r r` (`mem_B_r_inv`) and carries `deriv_sq_R` to `deriv_sq` (`deriv_sq_R_inv_comp`).
lemma poincare_inequality_left (R: ℕ) (f: G → ℝ): ∑ x ∈ (B_r (R - 1)), |f x - (f_avg (R - 1) f)|^2 ≤
    16 * R^2 * #S * (#(B_r (2 * R - 2))) / #(B_r (R - 1)) * ∑ x ∈ (B_r (3 * R)), deriv_sq f x := by
  have poincare := poincare_inequality R (fun y => f y⁻¹)
  rw [f_avg_inv] at poincare
  rw [show (∑ x ∈ B_r ((R: ℝ) - 1), |f x⁻¹ - f_avg ((R: ℝ) - 1) f| ^ 2)
      = ∑ x ∈ B_r ((R: ℝ) - 1), |f x - f_avg ((R: ℝ) - 1) f| ^ 2 from
    sum_B_r_inv _ (fun x => |f x - f_avg ((R: ℝ) - 1) f| ^ 2)] at poincare
  rw [show (∑ x ∈ B_r (3 * (R: ℝ)), deriv_sq_R (fun y => f y⁻¹) x)
      = ∑ x ∈ B_r (3 * (R: ℝ)), deriv_sq f x from by
    rw [← sum_B_r_inv (3 * (R: ℝ)) (fun x => deriv_sq f x)]
    exact Finset.sum_congr rfl (fun x _ => deriv_sq_R_inv_comp f x)] at poincare
  exact poincare

#print axioms poincare_inequality_left

omit v_wrapper_inst in
lemma card_B_r_eq (R: ℕ): #(B_r R) = #(S ^ R) := by
  rw [← card_closed_ball_eq]
  simp [B_r]

lemma lemma_3_25_poincare (data: GoodScalesData b) (j: (X_j data)) (f: G → ℝ): ∑ x ∈ (B_c_r j (R_1 data )), |f x - (f_avg_c j (R_1 data ) f)|^2 ≤
    16 * (R_1 data + 1)^2 * #S * (Real.exp (a data.d)) * ∑ x ∈ (B_c_r j (3 * (R_1 data + 1))), deriv_sq f x := by

  have R_1_pos: 0 < R_1 data := by
    simp [R_1]

  -- `deriv_sq` is invariant under right translation, and `B_c_r j r` is the right translate
  -- `B_r r * j`, so the left-handed Poincaré inequality is the one that transfers here.
  have poincare := poincare_inequality_left (R_1 data + 1) (f ∘ (fun g => g * j.val))

  simp at poincare
  rw [← Finset.sum_image (f := fun x => ((f (x)) - f_avg (↑(R_1 data)) (f ∘ fun g ↦ g * j)) ^ 2) (by simp)] at poincare
  conv at poincare =>
    lhs
    arg 1
    equals B_c_r j ((R_1 data) ) =>
      rw [B_c_r_eq_smul]
      rw [← Finset.image_smul]
      simp

  conv at poincare =>
    lhs
    arg 2
    intro x
    arg 1
    rhs
    equals f_avg_c j ((R_1 data) ) f =>
      simp [f_avg_c, f_avg]
      rw [B_c_r_eq_smul]
      rw [← Finset.image_smul]
      rw [Finset.sum_image]
      .
        simp
        left
        simp [B_r]
      . simp

  simp_rw [sq_abs]
  grw [poincare]
  clear poincare

  have vol_frac_le: ↑(#(B_r (2 * (↑(R_1 data) + 1) - 2))) / ↑(#(B_r ↑(R_1 data))) ≤ Real.exp (a data.d) := by


    rw [← Real.log_le_iff_le_exp]
    . rw [Real.log_div]
      .


        rw [card_B_r_eq]
        conv =>
          lhs
          arg 1
          arg 1
          arg 1
          arg 1
          arg 1
          equals ↑(2 * ((R_1 data) + 1) - 2) =>
            simp
        rw [card_B_r_eq]
        grw [log_card_pow_sub_le (b := b) (k := (GoodScales data).i_1 + 1) (j := (GoodScales data).i_1)]
        .
          grw [(GoodScales data).first_h_i]
        .
          apply (GoodScales data).i_1_ge
        . simp
        . simp
          grind
        . simp
          have h_i_1 := (GoodScales data).i_1_ge
          simp [i₀, R'] at h_i_1
          simp [R_1]
          ring
          grind
        .
          simp [R_1]
      . simp only [B_r, Set.toFinite_toFinset, ne_eq, Nat.cast_eq_zero]
        apply Finset.card_ne_zero_of_mem (a := 1)
        simp [R_1]
      . simp only [B_r, Set.toFinite_toFinset, ne_eq, Nat.cast_eq_zero]
        apply Finset.card_ne_zero_of_mem (a := 1)
        simp [R_1]
    . apply mul_pos
      . simp only [B_r, Set.toFinite_toFinset]
        norm_cast
        rw [Finset.card_pos]
        use 1
        simp [R_1]
      .
        simp [-Set.toFinset_card]
        use 1
        simp [B_r, R_1]
  .
    rw [mul_div_assoc]
    norm_num
    grw [vol_frac_le]
    .

      conv =>
        lhs
        rhs
        equals  ∑ x ∈ B_c_r j (3 * ↑(R_1 data + 1)), deriv_sq f x =>

          rw [B_c_r_eq_smul]
          rw [← Finset.image_smul]
          rw [Finset.sum_image (by simp)]
          norm_cast
          apply congrArg
          ext x
          simp [deriv_sq]
          group
      simp
    . simp [deriv_sq]
      positivity

-- Estimating functions relative to cover

end V_Wrapper_Section

end GeneratesNS
