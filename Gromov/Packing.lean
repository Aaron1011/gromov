module

public import Mathlib
public import Gromov.VWrapper

/-!
# Ball packing at a good scale

The packing sets `B`, `B_half`, `B_3` at a good scale, their finiteness and disjointness, and
the intersection-multiplicity bound `card_B_le_exp_wa`.
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

variable {b : Module.Basis ι ℝ V}

structure GoodScalesData (b : Module.Basis ι ℝ V) where
  w: ℕ
  d: ℕ
  hw: 0 < w
  hd: 0 < d
  w_gt: 4 < w
  h_growth: growth_bound b d

noncomputable def GoodScales (data: GoodScalesData b) := Classical.choice (lemma_3_24 b data.w data.d data.hw data.hd data.h_growth)

noncomputable def R_1 (data: GoodScalesData b) := 2 * 16^(GoodScales data).i_1
noncomputable def R_2 (data: GoodScalesData b) := 16^(GoodScales data).i_2

-- TODO - does it matter than 'Metric.maximalSeparatedSet' uses 'R_1 < dist' instead of 'R_1 <= dist' ?
def X_j (data: GoodScalesData b) := Metric.maximalSeparatedSet (R_1 data) ((Metric.closedBall (1: G) (R_2 data)))
-- A collection of disjoint balls that cover the ball R_2
def B (data: GoodScalesData b) := (fun a => Metric.closedBall a (R_1 data)) '' (X_j data)
def B_half (data: GoodScalesData b) := (fun a => Metric.closedBall a (R_1 data / 2)) '' (X_j data)
def B_3 (data: GoodScalesData b) := (fun a => Metric.closedBall a (3 * (R_1 data + 1))) '' (X_j data)

lemma X_j_finite (data: GoodScalesData b): (X_j data).Finite := by
  apply Set.Finite.subset (finite_closed_ball (1 : G) (R_2 data))
  simp [X_j]
  apply Metric.maximalSeparatedSet_subset

lemma B_ball_injective_on (data: GoodScalesData b) (R: ℝ) (R_pos: 0 ≤ R) (hR: R ≤ R_1 data): Set.InjOn (fun a => Metric.closedBall a (R)) (X_j data) := by
  intro a ha b hb hab
  by_contra!
  simp at hab
  simp [X_j] at ha hb

  have sep := Metric.isSeparated_maximalSeparatedSet (ε := (R_1 data)) (A := (Metric.closedBall (1 : G) ↑(R_2 data)))
  specialize sep ha hb this

  have b_mem: b ∈ Metric.closedBall a ((R)) := by
    rw [hab]
    simp
    grind

  simp at b_mem
  simp [edist, PseudoMetricSpace.edist] at sep
  rw [dist_comm] at b_mem
  simp [dist] at b_mem
  norm_cast at b_mem
  rify at sep
  grw [b_mem] at sep
  norm_cast at sep
  grind

lemma B_covers_R2 (data: GoodScalesData b): Metric.closedBall 1 (R_2 data) ⊆ ⋃₀ (B data) := by
  by_contra!
  rw [Set.not_subset] at this
  obtain ⟨x, x_mem, x_not_mem⟩ := this

  -- Metric.maximalSeparatedSet_subset
  have card_le := Metric.encard_le_of_isSeparated (C := (X_j data) ∪ {x}) (ε := (R_1 data)) (A := ( (Metric.closedBall 1 (R_2 data)))) ?_ ?_ ?_
  .
    simp [X_j] at card_le
    rw [Set.encard_insert_of_notMem] at card_le
    rw [Set.Finite.encard_eq_coe_toFinset_card] at card_le
    . norm_cast at card_le

      grind
    .
      apply Set.Finite.subset (s := Metric.closedBall 1 (R_2 data))
      . apply finite_closed_ball
      . apply Metric.maximalSeparatedSet_subset
    .
      simp at x_not_mem
      simp only [B, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        not_lt, X_j] at x_not_mem

      by_contra!
      specialize x_not_mem x this
      simp [R_1] at x_not_mem
  .
    apply Set.union_subset
    . simp [X_j]
      grw [Metric.maximalSeparatedSet_subset]
    .
      simp at x_mem
      simpa using x_mem
  .
    simp
    apply Metric.IsSeparated.insert
    . simp [X_j]
      apply Metric.isSeparated_maximalSeparatedSet
    . intro y hy hxy
      simp [B] at x_not_mem
      specialize x_not_mem y hy
      simp [edist, PseudoMetricSpace.edist]
      simp [dist] at x_not_mem
      exact x_not_mem
  .
    rw [← lt_top_iff_ne_top]
    grw [Metric.packingNumber_le_encard_self]
    simp
    apply finite_closed_ball

lemma B_half_disjoint (data: GoodScalesData b): (B_half data).PairwiseDisjoint id := by
  simp [Set.pairwiseDisjoint_iff]
  intro X hX Y hY hXY
  obtain ⟨a, ha⟩ := hXY
  simp [B_half] at hX hY
  obtain ⟨x, x_mem, hx⟩ := hX
  obtain ⟨y, y_mem, hy⟩ := hY

  by_cases x_eq_y : x = y
  .
    rw [x_eq_y] at hx
    rw [← hx, ← hy]

  rw [← hx, ← hy] at ha
  simp at ha
  obtain ⟨a_dist_x, a_dist_y⟩ := ha

  simp [X_j] at x_mem
  have is_sep := Metric.isSeparated_maximalSeparatedSet (ε := ((R_1 data))) (A := Metric.closedBall (1: G) (R_2 data))

  unfold Metric.IsSeparated Set.Pairwise at is_sep
  have x_sep := is_sep x_mem y_mem x_eq_y
  simp at x_sep

  have x_y_dist_bad := dist_triangle x a y
  rw [dist_comm x a] at x_y_dist_bad
  grw [a_dist_x, a_dist_y] at x_y_dist_bad
  simp at x_y_dist_bad
  -- TODO - we need a lemma that edist = ↑dist
  simp [edist, PseudoMetricSpace.edist] at x_sep
  simp [dist] at x_y_dist_bad
  grind

-- Intersection multiplicity. See https://www.math.ucdavis.edu/~kapovich/EPR/kapovich_drutu.pdf page 24 for the definition
-- (search for 'multiplicity')
noncomputable def InterMult_f  (S: Set (Set G)) := (fun A => (Set.encard A).toNat) '' { A: Set (Set G) | A ⊆ S ∧ ⋂₀ A ≠ ∅ }
noncomputable def InterMult (S: Set (Set G)) := sSup (InterMult_f S)

omit v_wrapper_inst in
lemma smul_origin_ball_subset (a: G) (r: ℝ): (MulOpposite.op a) • Metric.closedBall 1 r ⊆ Metric.closedBall a r := by
  intro x hx
  simp
  rw [Set.mem_smul_set] at hx
  obtain ⟨y, hy, x_eq⟩ := hx
  rw [← x_eq]
  simp [dist, WordDist]
  simp at hy
  simp [dist, WordDist] at hy
  exact hy

omit v_wrapper_inst in
lemma ball_subset_smul_origin (a: G) (r: ℝ): Metric.closedBall a r ⊆ (MulOpposite.op a) • Metric.closedBall 1 r := by
  intro x hx
  simp at hx
  simpa using hx

lemma ball_smul_eq_origin (a: G) (r: ℝ): Metric.closedBall a r = (MulOpposite.op a) • Metric.closedBall 1 r := by
  ext x
  have foo := smul_origin_ball_subset a r
  have bar := ball_subset_smul_origin a r
  grind

lemma B_finite (data: GoodScalesData b): (B data).Finite := by
  simp [B]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_closed_ball

lemma B_half_finite (data: GoodScalesData b): (B_half data).Finite := by
  simp [B_half]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_closed_ball

noncomputable def B_finsets (data: GoodScalesData b): Finset (Finset G) := Finset.image ((fun a => (finite_closed_ball a (R_1 data )).toFinset)) (X_j_finite data).toFinset

-- TODO - combine this with 'B_half'
noncomputable def B_half_finsets (data: GoodScalesData b): Finset (Finset G) := Finset.image ((fun a => (finite_closed_ball a (R_1 data / 2)).toFinset)) (X_j_finite data).toFinset

lemma B_3_finite (data: GoodScalesData b): (B_3 data).Finite := by
  simp [B_3]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_closed_ball

-- Suprisingly, we can prove an upper bound with 4*R_1, rather than the 8*R_1 from the paper
lemma inter_mult_helper (data: GoodScalesData b): InterMult (B_3 data) * #(S ^ ((R_1 data) / 2)) ≤ #(S ^ (4 * (R_1 data + 1))) := by
  classical
  apply Nat.mul_le_of_le_div
  unfold InterMult
  by_cases h_s: InterMult_f (B_3 data) = ∅
  . simp [h_s]
  .
    rw [csSup_le_iff]
    .
      intro n hn
      simp [InterMult_f] at hn
      obtain ⟨X, ⟨X_subset, X_inter⟩, X_card⟩ := hn
      rw [← X_card]
      have X_finite := Set.Finite.subset (B_3_finite data) X_subset
      rw [Set.Finite.encard_eq_coe_toFinset_card X_finite]
      simp
      rw [Nat.le_div_iff_mul_le]
      .
        have X_inner_nonempty: ∀ t ∈ X, ∃ a, a ∈ (X_j data) ∧ Metric.closedBall a (3 * (R_1 data + 1)) = t := by
          intro t ht
          specialize X_subset ht
          simp [B_3] at X_subset
          exact X_subset

        rw [← closed_ball_eq_S_pow]
        rw [← smul_eq_mul]
        rw [← Finset.sum_const]

        grw [Finset.sum_le_sum (g := fun a => if ha: a ∈ X then #(finite_closed_ball (X_inner_nonempty a ha).choose ((R_1 data) / 2)).toFinset else 0)]
        .
          rw [← closed_ball_eq_S_pow]
          rw [Finset.sum_dite]
          rw [← Finset.card_biUnion]
          .
            rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at X_inter
            obtain ⟨base, h_base⟩ := X_inter

            simp only [Finset.sum_const_zero, add_zero]
            nth_rw 2 [← Finset.card_smul_finset (MulOpposite.op base)]
            apply Finset.card_le_card
            rw [← Finset.coe_subset]
            rw [Finset.coe_smul_finset]
            conv =>
              rhs
              arg 2
              simp

            rw [← ball_smul_eq_origin]
            intro a ha
            simp at ha
            simp
            obtain ⟨c, hc, a_dist⟩ := ha
            .
              let q := (X_inner_nonempty c hc).choose
              grw [dist_triangle _ q]
              conv at a_dist =>
                arg 1
                arg 2
                equals q =>
                  simp [q]

              grw [a_dist]
              simp at h_base
              specialize h_base c hc

              have q_prop := (X_inner_nonempty c hc).choose_spec
              rw [← q_prop.2] at h_base
              simp at h_base
              rw [dist_comm] at h_base
              simp [q]
              grw [h_base]
              grind
          .
            rw [Finset.pairwiseDisjoint_iff]
            intro a _ b _ hab
            rw [Subtype.ext_iff]

            have from_b := B_half_disjoint data
            have a_prop := a.prop
            have b_prop := b.prop
            simp [-SetLike.coe_mem] at a_prop
            simp [-SetLike.coe_mem] at b_prop
            simp [B_half] at from_b

            let a_center := (X_inner_nonempty _ a_prop).choose
            let b_center := (X_inner_nonempty _ b_prop).choose
            obtain ⟨a_center_mem, a_eq⟩ := (X_inner_nonempty _ a_prop).choose_spec
            obtain ⟨b_center_mem, b_eq⟩ := (X_inner_nonempty _ b_prop).choose_spec

            rw [Set.pairwiseDisjoint_iff] at from_b
            simp only [Set.mem_image, id_eq, forall_exists_index, and_imp] at from_b
            simp at hab
            have inter_eq := from_b a_center a_center_mem (i := (Metric.closedBall a_center (↑(R_1 data) / 2) )) (?_) b_center b_center_mem (j := (Metric.closedBall b_center (↑(R_1 data) / 2) )) (?_) ?_
            .

              rw [← a_eq, ← b_eq]
              simp [a_center, b_center] at inter_eq
              apply B_ball_injective_on data (R_1 data / 2) (by grind) (by simp [R_1]) at inter_eq
              .
                simp [inter_eq]
              . grind
              . grind
            . rfl
            . rfl
            . simp [a_center, b_center]
              rw [← Finset.coe_nonempty] at hab
              simp at hab
              exact hab

        . intro y hy
          simp at hy
          simp only [hy, ↓reduceDIte]
          nth_rw 1 [← Finset.card_smul_finset (MulOpposite.op (X_inner_nonempty y hy).choose)]
          apply Finset.card_le_card
          intro a ha
          simp at ha
          simp
          rw [Finset.mem_smul_finset] at ha
          obtain ⟨z, z_mem, z_mul_eq⟩ := ha
          simp at z_mem
          rw [← z_mul_eq]
          simp
          simp [dist, WordDist]
          rw [← word_norm_inv]
          simp [dist, WordDist_one] at z_mem
          norm_cast
          grw [z_mem]
          grw [Nat.cast_div_le]
          simp

      . simp
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    .
      unfold BddAbove
      use (B_3 data).encard.toNat
      rw [mem_upperBounds]
      intro x hx
      simp [InterMult_f] at hx
      obtain ⟨a, b, x_eq⟩ := hx
      rw [← x_eq]
      apply ENat.toNat_le_toNat
      .
        apply Set.encard_le_encard
        grind
      . simp
        apply B_3_finite
    . rw [Set.nonempty_iff_ne_empty]
      grind

noncomputable def B_r (r: ℝ) := (finite_closed_ball 1 r).toFinset
noncomputable def B_c_r (g: G) (r: ℝ) := (finite_closed_ball g r).toFinset

omit v_wrapper_inst in
lemma B_c_r_eq_smul (a: G) (r: ℝ): B_c_r a r = (MulOpposite.op a) • B_r r := by
  rw [B_c_r, B_r]
  rw [← Finset.coe_inj]
  simp

lemma pack_center_helper (data: GoodScalesData b) (x: G): #{ c ∈ (X_j_finite data).toFinset | x ∈ B_c_r c (3 * (R_1 data + 1)) } * #(S ^ ((R_1 data) / 2)) ≤ #(S ^ (4 * (R_1 data + 1))) := by
  rw [← closed_ball_eq_S_pow]
  rw [← smul_eq_mul]
  rw [← Finset.sum_const]

  rw [← closed_ball_eq_S_pow]
  grw [Finset.sum_le_sum (g := fun a => #(B_c_r a ↑((R_1 data : ℝ) / 2)))]
  .
    rw [← Finset.card_biUnion]
    .
      nth_rw 2 [← Finset.card_smul_finset (MulOpposite.op x)]
      apply Finset.card_le_card
      rw [← Finset.coe_subset]

      intro a ha
      simp at ha
      obtain ⟨p, ⟨p_mem, a_mem⟩⟩ := ha
      simp
      simp [B_c_r] at a_mem
      grw [dist_triangle _ p]
      grw [a_mem]
      have p_dist := p_mem.1
      simp [X_j] at p_dist
      apply Metric.maximalSeparatedSet_subset at p_dist
      simp at p_dist
      have x_mem := p_mem.2
      simp [B_c_r] at x_mem
      rw [dist_comm] at x_mem
      grw [x_mem]
      rw [mul_add]
      ring
      grind
    .
      rw [Finset.pairwiseDisjoint_iff]
      intro a ha b hb hab

      have from_b := B_half_disjoint data
      simp at ha hb
      simp [B_half] at from_b

      rw [Set.pairwiseDisjoint_iff] at from_b
      simp only [Set.mem_image, id_eq, forall_exists_index, and_imp] at from_b
      have inter_eq := from_b a ha.1 (i := (Metric.closedBall a ((↑(R_1 data) : ℝ) / 2) )) (?_) b hb.1 (j := (Metric.closedBall b (↑(R_1 data : ℝ) / 2) )) (?_) ?_
      .
        apply B_ball_injective_on data (R_1 data / 2) (by grind) (by simp [R_1]) at inter_eq
        .
          simp [inter_eq]
        . grind
        . grind
      . rfl
      . rfl
      .
        rw [← Finset.coe_nonempty] at hab
        simp [B_c_r] at hab
        simpa using hab
  .
    intro a ha
    simp at ha
    simp [B_c_r_eq_smul, B_r]
    rw [Nat.cast_div]
    . simp
    . simp [R_1]
    . simp

/-- Common step for Lemma 3.25 (a) and (b).

`h i = log (#(S ^ 16 ^ i) * det (Q_{16 ^ i}) ^ (dim V)⁻¹)` splits into a log-cardinality term
plus a determinant term. The determinant term is monotone in the scale (Proposition 3.22, via
`Q_R_lin_sub_pos_semi_def` and `matrix_det_montone`), so it is non-negative and can be dropped,
leaving a comparison of ball cardinalities that follows from `Finset.card_pow_mono`. -/
lemma log_card_pow_sub_le {j k m n : ℕ} (hj : i₀ ≤ j) (hjk : j ≤ k) (hm0 : m ≠ 0)
    (hm : m ≤ 16 ^ k) (hn : 16 ^ j ≤ n) :
    Real.log (#(S ^ m)) - Real.log (#(S ^ n)) ≤ h b k - h b j := by
  have card_pos : ∀ p : ℕ, (0:ℝ) < #(S ^ p) := by
    intro p
    simp
    apply Finset.Nonempty.pow
    exact S_nonempty
  have i₀_le_j : ((16:ℝ) ^ i₀) ≤ ((16 ^ j : ℕ) : ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hj
  have i₀_le_k : ((16:ℝ) ^ i₀) ≤ ((16 ^ k : ℕ) : ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (hj.trans hjk)
  have pd_j : (Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).PosDef := Q_R_matrix_pos_def_i₀ b _ i₀_le_j
  -- Proposition 3.22: the determinant is monotone in the scale, so the determinant part of
  -- `h k - h j` is non-negative and may be discarded.
  have det_le : (Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).det ≤ (Q_R_matrix b ((16 ^ k : ℕ) : ℝ)).det := by
    apply matrix_det_montone
    . exact pd_j
    . unfold Q_R_matrix
      rw [← map_sub]
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      apply Q_R_lin_sub_pos_semi_def
      push_cast
      exact pow_le_pow_right₀ (by norm_num) hjk
  have dim_nonneg : (0:ℝ) ≤ (dim V)⁻¹ := by
    simp [dim]
  have log_det_le :
      Real.log ((Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).det ^ (dim V)⁻¹) ≤
        Real.log ((Q_R_matrix b ((16 ^ k : ℕ) : ℝ)).det ^ (dim V)⁻¹) :=
    Real.log_le_log (Real.rpow_pos_of_pos pd_j.det_pos _)
      (Real.rpow_le_rpow pd_j.det_pos.le det_le dim_nonneg)
  have card_le :
      Real.log ((#(S ^ m) : ℝ)) - Real.log ((#(S ^ n) : ℝ)) ≤
        Real.log ((#(S ^ 16 ^ k) : ℝ)) - Real.log ((#(S ^ 16 ^ j) : ℝ)) := by
    apply sub_le_sub
    . apply Real.log_le_log (card_pos m)
      norm_cast
      exact Finset.card_pow_mono hm0 hm
    . apply Real.log_le_log (card_pos (16 ^ j))
      norm_cast
      exact Finset.card_pow_mono (by positivity) hn
  simp only [h, f]
  rw [Real.log_mul, Real.log_mul]
  . linarith
  . exact ne_of_gt (card_pos (16 ^ j))
  . exact ne_of_gt (Real.rpow_pos_of_pos pd_j.det_pos _)
  . exact ne_of_gt (card_pos (16 ^ k))
  . exact ne_of_gt (Real.rpow_pos_of_pos
      (Q_R_matrix_pos_def_i₀ b _ i₀_le_k).det_pos _)

-- Lemma 3.25 (a)

lemma log_inter_mult_b3 (data: GoodScalesData b): InterMult (B_3 data) ≤ Real.exp (a data.d) := by
  by_cases mult_zero: InterMult (B_3 data) = 0
  . simp [mult_zero]
    positivity

  rw [← Real.log_le_iff_le_exp]
  have foo := inter_mult_helper data
  rw [← Nat.le_div_iff_mul_le] at foo
  grw [foo]
  .
    grw [Nat.cast_div_le]
    .
      rw [Real.log_div]
      .
        have bound := (GoodScales data).first_h_i
        grw [← bound]

        apply log_card_pow_sub_le (GoodScales data).i_1_ge (Nat.le_succ _)
        . simp [R_1]
        . rw [pow_succ]
          simp [R_1]
          ring
          rw [← le_tsub_iff_right]
          .
            rw [← Nat.mul_sub]
            norm_num
            grw [← Nat.one_le_pow]
            . simp
            . simp
          . simp
        . simp [R_1]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    . simp
      refine ⟨?_, ?_⟩
      . apply Finset.Nonempty.pow
        simp [S_nonempty]
      .
        apply Finset.card_pow_mono
        . simp [R_1]
        . grind
  .
    simp
    apply Finset.Nonempty.pow
    simp [S_nonempty]
  . simp
    grind

lemma log_pack_center_helper (data: GoodScalesData b) (x: G): #{ c ∈ (X_j_finite data).toFinset | x ∈ B_c_r c (3 * (R_1 data + 1)) } ≤ Real.exp (a data.d) := by
  by_cases inter_empty: { c ∈ (X_j_finite data).toFinset | x ∈ B_c_r c (3 * (R_1 data + 1)) } = ∅
  . simp [inter_empty]
    apply Real.exp_nonneg

  rw [← Real.log_le_iff_le_exp]
  have foo := pack_center_helper data x
  rw [← Nat.le_div_iff_mul_le] at foo
  grw [foo]
  .
    grw [Nat.cast_div_le]
    .
      rw [Real.log_div]
      .
        have bound := (GoodScales data).first_h_i
        grw [← bound]

        apply log_card_pow_sub_le (GoodScales data).i_1_ge (Nat.le_succ _)
        . simp [R_1]
        . rw [pow_succ]
          simp [R_1]
          ring
          rw [← le_tsub_iff_right]
          .
            rw [← Nat.mul_sub]
            norm_num
            grw [← Nat.one_le_pow]
            . simp
            . simp
          . simp
        . simp [R_1]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    . simp
      refine ⟨?_, ?_⟩
      . apply Finset.Nonempty.pow
        simp [S_nonempty]
      .
        apply Finset.card_pow_mono
        . simp [R_1]
        . grind
  .
    simp
    rw [Finset.nonempty_iff_ne_empty]
    simpa using inter_empty
  . simp
    apply Finset.Nonempty.pow
    simp [S_nonempty]
  . simp
    rw [Finset.nonempty_iff_ne_empty]
    simpa using inter_empty

#print axioms inter_mult_helper
#print axioms log_inter_mult_b3
#print axioms log_pack_center_helper

-- Lemma 3.25 (b)
lemma card_B_le_exp_wa (data: GoodScalesData b): #(B_finite data).toFinset < Real.exp (data.w * (a data.d)) := by
  have B_union := Finset.card_biUnion (s := (B_half_finsets data)) (t := id) ?_
  .
    simp at B_union
    have sum_le := Finset.sum_eq_card_nsmul (f := fun (u: Finset G) => #u) (s := B_half_finsets data) (b := #(S ^ (R_1 data / 2))) ?_
    .
      rw [← Nat.card_eq_card_finite_toFinset]
      simp [B]
      grw [Set.ncard_image_le (hs := by apply X_j_finite)]
      conv at sum_le =>
        rhs
        lhs
        simp [B_half_finsets]
        rw [Finset.card_image_iff.mpr (by
          have foo := B_ball_injective_on data (R_1 data / 2) (by grind) (by simp [R_1])
          conv =>
            rhs
            equals (X_j data) =>
              simp

          intro a ha b hb hab
          specialize foo ha hb
          specialize foo (by simpa using hab)
          exact foo
        )]
      simp at sum_le
      rw [eq_comm] at sum_le
      apply le_of_eq at sum_le
      rw [← Nat.le_div_iff_mul_le (by simp; apply Finset.Nonempty.pow; simp [S_nonempty])] at sum_le
      conv at sum_le =>
        lhs
        equals (X_j data).ncard =>
          rw [Set.ncard_eq_toFinset_card (hs := by apply X_j_finite)]

      grw [sum_le]
      rw [← B_union]
      grw [Finset.card_le_card (t := (finite_closed_ball (1: G) ↑(2 * (R_2 data))).toFinset)]
      .
        grw [Nat.cast_div_le]
        rw [card_closed_ball_eq]
        .
          rw [← Real.log_lt_iff_lt_exp]
          .
            apply lt_of_le_of_lt ?_  ((GoodScales data).h_diff_lt_w)
            rw [Real.log_div (by simp; grind [S_nonempty]) (by simp; grind [S_nonempty])]
            apply log_card_pow_sub_le (GoodScales data).i_1_ge
            . -- `i_2 - i_1 > w ≥ 0` forces `i_1 < i_2`
              have hdiff := (GoodScales data).i_diff_mem
              simp [Set.mem_Ioo] at hdiff
              omega
            . simp [R_2]
            . rw [pow_succ]
              simp [R_2]
              omega
            . simp [R_1]
          .
            apply div_pos
            . simp
              apply Finset.Nonempty.pow
              simp [S_nonempty]
            . simp
              apply Finset.Nonempty.pow
              simp [S_nonempty]
      .
        intro a ha
        simp at ha
        obtain ⟨x, x_mem, hx⟩ := ha
        simp [B_half_finsets] at x_mem
        simp
        obtain ⟨c, hc, x_eq⟩ := x_mem
        grw [dist_triangle _ c]
        rw [← x_eq] at hx
        simp at hx
        grw [hx]
        simp [X_j] at hc
        grw [Metric.maximalSeparatedSet_subset] at hc
        simp at hc
        grw [hc]
        simp [R_1, R_2]
        have i_1_le:  (GoodScales data).i_1 ≤  (GoodScales data).i_2 := by
          have foo :=  (GoodScales data).i_diff_mem
          simp at foo
          grind
        grw [i_1_le]
        .
          grind
        . simp
    .
      intro b hb
      simp [B_half_finsets] at hb
      obtain ⟨c, c_mem, b_eq⟩ := hb
      rw [← b_eq]
      rw [← Set.toFinite_toFinset]
      rw [← Nat.card_eq_card_finite_toFinset]
      rw [ball_smul_eq_origin]

      -- TODO - make the various finite/fintype/card conversion less awful
      conv =>
        lhs
        equals (MulOpposite.op c • (Metric.closedBall (1: G) (↑(R_1 data) / 2))).ncard =>
          simp

      simp [-Metric.smul_closedBall]
      conv =>
        lhs
        equals #(finite_closed_ball 1 ↑((R_1 data) / 2)).toFinset =>
          simp
          rw [Set.ncard_eq_toFinset_card']
          simp [R_1]
      rw [card_closed_ball_eq]

  .
    -- TODO - there must be a less horrendous way of dealing with Finset here
    simp [B_half_finsets]
    have foo := B_half_disjoint data
    simp [B_half] at foo
    unfold Set.PairwiseDisjoint Set.Pairwise
    unfold Set.PairwiseDisjoint Set.Pairwise at foo
    simp
    simp at foo
    intro a ha b hb hab p hp_a hp_b
    simp at hp_a hp_b
    specialize foo a ha b hb hab hp_a hp_b
    simpa using foo

end V_Wrapper_Section

end GeneratesNS
