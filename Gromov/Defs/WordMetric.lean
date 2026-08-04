module

public import Mathlib

/-!
# The `Generates` class and the word metric

The `Generates` class packaging a finitely generated group with a symmetric generating set, the
definition of polynomial growth, and the word norm / word metric on `G` with its `MetricSpace`
instance.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

-- Based on https://github.com/YaelDillies/LeanCamCombi/blob/b6312bee17293272af6bdcdb47b3ffe98fca46a4/LeanCamCombi/GrowthInGroups/Lecture1.lean#L41
-- and the Vikman paper
def HasPolynomialGrowthD {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (d: ℕ): Prop := ∃ a: ℕ, ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d
def HasPolynomialGrowth  {G: Type*} [Group G] [DecidableEq G] (S: Finset G): Prop := ∃ d, HasPolynomialGrowthD S d


-- TODO - I don't really understand why `S` needs to be an `outParam`?
-- If I remove that, then the `PseudoMetricSpace G` starts erroring
-- See also:
-- * `set_option synthInstance.checkSynthOrder false`
class Generates where
  G: Type*
  g_group: Group G
  g_eq: DecidableEq G
  S: Finset G
  hS: Nonempty S
  generates : ((closure (S : Set G) : Set G) = ⊤)
  -- This should be fine, since the growth rate doesn't depend on the generating set
  one_mem: (1 : G) ∈ S
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S
  g_infinite: Infinite G
  -- TODO - should this carry data and the actual value 'd'?
  g_growth: HasPolynomialGrowth S

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

instance G_group: Group G := hGS.g_group
instance G_dec_eq: DecidableEq G := hGS.g_eq


lemma s_union_sinv : S ∪ S⁻¹ = S := by
  ext a
  have foo := hGS.has_inv (a⁻¹)
  simp only [inv_inv] at foo
  simpa using foo

lemma S_eq_Sinv: S = S⁻¹ := by
  ext a
  refine ⟨?_, ?_⟩
  . intro ha
    have a_inv := hGS.has_inv a ha
    exact Finset.mem_inv'.mpr a_inv
  . intro ha
    simp at ha
    have a_inv := hGS.has_inv a⁻¹ ha
    simp only [inv_inv] at a_inv
    exact a_inv

instance G_FG: Group.FG G := {
  out := by
    unfold Subgroup.FG
    use S
    have foo := hGS.generates
    simp at foo
    exact foo
}


lemma mem_closure (x: G): x ∈ closure (S : Set G) := by
  have hg := hGS.generates
  simp only [Set.top_eq_univ, coe_eq_univ] at hg
  simp [hg]

-- Predicate stating that an element of G equals a product of elements of S
def ProdS (x: G) (l: List S): Prop := l.unattach.prod = x

-- Each element of G can be written as a product of elements of S in at least one way
lemma mem_S_prod_list (x: G): ∃ l: List S, ProdS x l := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  simp only [mem_toSubmonoid, Finset.mem_coe] at foo
  specialize foo (mem_closure x)
  norm_cast at foo
  rw [s_union_sinv] at foo
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold ProdS
  unfold List.unattach
  simp [prod_eq]

omit hGS in
lemma list_tail_unattach (T: Type*)  {p : T → Prop} (l: List { x : T // p x}): l.tail.unattach = l.unattach.tail := by
  unfold List.unattach
  simp

noncomputable def WordNorm (g: G) := sInf {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l}

lemma word_norm_prod (g: G) (n: ℕ) (hgn: WordNorm g = n): ∃ l: List S, ProdS g l ∧ l.length = n := by
  have foo := Nat.sInf_mem (s := {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l})
  obtain ⟨l, hl⟩ := mem_S_prod_list  g
  unfold ProdS at hl
  rw [Set.nonempty_def] at foo
  specialize foo ⟨l.length, ⟨l, ⟨by simp, hl⟩⟩⟩
  simp only [Set.mem_setOf_eq] at foo
  obtain ⟨l, ⟨hl, hl_prod⟩⟩ := foo
  rw [← hgn]
  exact ⟨l, ⟨hl_prod, hl⟩⟩

-- TODO - we might want to adjust our definition to avoid this annoying case
lemma word_norm_one: WordNorm 1 = 0 := by
  simp [WordNorm, ProdS]

lemma word_norm_prod_self (g: G): ∃ l: List S, ProdS g l ∧ l.length = WordNorm  g := by
  exact word_norm_prod  g (WordNorm  g) rfl

lemma word_norm_le (g: G) (l: List S) (hgl: ProdS g l): WordNorm  g ≤ l.length := by
  unfold WordNorm
  apply Nat.sInf_le
  use l

-- TODO - this probably needs to be swapped to make 'gAct' work
noncomputable def WordDist (x y: G) := WordNorm  (y * x⁻¹)

lemma WordDist_self (x: G): WordDist  x x = 0 := by
  unfold WordDist
  rw [mul_inv_cancel]
  unfold WordNorm
  simp only [Nat.sInf_eq_zero, Set.mem_setOf_eq, List.length_eq_zero_iff, exists_eq_left]
  left
  rfl

lemma WordDist_swap_le (x y: G): WordDist  y x ≤ WordDist  x y := by
  unfold WordDist
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod (y * x⁻¹) (WordNorm (y * x⁻¹)) (rfl)
  unfold ProdS at l_prod
  apply_fun (fun x => x⁻¹) at l_prod
  rw [mul_inv_rev, inv_inv] at l_prod
  rw [List.prod_inv_reverse] at l_prod

  have commute_unattach: List.map (Inv.inv) l.unattach = (l.map (fun x => ⟨x.val⁻¹, hGS.has_inv x.val x.property⟩)).unattach := by
    apply List.ext_getElem?
    intro i
    simp


  rw [commute_unattach, ← List.unattach_reverse] at l_prod
  have prod_le := word_norm_le  (x * y⁻¹) _ l_prod
  conv at prod_le =>
    rhs
    equals l.length =>
      simp
  rw [l_len] at prod_le
  exact prod_le

lemma WordDist_comm (x y: G): WordDist  x y = WordDist  y x := by
  have le_left := WordDist_swap_le  x y
  have le_right := WordDist_swap_le  y x
  exact Nat.le_antisymm le_right le_left

lemma WordDist_triangle (x y z: G): WordDist  x z ≤ WordDist  x y + WordDist  y z := by

  unfold WordDist
  obtain ⟨l_x_y, x_y_prod, x_y_len⟩ := word_norm_prod_self  (y * x⁻¹)
  obtain ⟨l_y_z, y_z_prod, y_z_len⟩ := word_norm_prod_self  (z * y⁻¹)
  unfold ProdS at x_y_prod
  unfold ProdS at y_z_prod

  have prod_append: ProdS  (z * x⁻¹) (l_y_z ++ l_x_y) := by
    unfold ProdS
    simp
    rw [x_y_prod, y_z_prod]
    rw [← mul_assoc]
    simp

  have le_append := word_norm_le  (z * x⁻¹) _ prod_append
  rw [List.length_append] at le_append
  rw [x_y_len, y_z_len] at le_append
  rw [add_comm] at le_append
  exact le_append

-- TODO - I'm not certain that these are actually the correct instances for the proof


noncomputable instance WordDist.instPseudoMetricSpace: PseudoMetricSpace G where
  dist x y := WordDist  x y
  dist_self x := by
    norm_cast
    exact WordDist_self  x
  dist_comm x y := by
    norm_cast
    exact WordDist_comm  x y
  dist_triangle x y z := by
    norm_cast
    exact WordDist_triangle  x y z

lemma word_norm_eq_zero {x y: G} (hdist: WordDist x y = 0): x = y := by
  simp [WordDist, WordNorm] at hdist
  match hdist with
  | .inl empty_prod =>
    unfold ProdS at empty_prod
    simp only [List.unattach_nil, List.prod_nil] at empty_prod
    apply_fun (fun y => y * x) at empty_prod
    simpa using empty_prod
  | .inr empty_set =>
    obtain ⟨l, hl⟩ := mem_S_prod_list  (y * x⁻¹)
    unfold ProdS at hl
    have len_in_set: l.unattach.length ∈ (∅ : Set ℕ) := by
      rw [← empty_set]
      simp only [List.length_unattach, Set.mem_setOf_eq]
      use l
      refine ⟨rfl, hl⟩
    simp only [Set.mem_empty_iff_false] at len_in_set

lemma dist_word_mul {x y : G} (hy: y ∈ S): dist x (y * x) ≤ 1 := by
  simp [dist, WordDist, WordNorm]
  apply csInf_le
  . simp
  . simp
    use [⟨y, hy⟩]
    simp [ProdS]

lemma dist_word_mul_le {x y z : G} (hy: y ∈ S): dist x (y * z) ≤ 1 + dist x z := by
  conv =>
    lhs
    simp [dist, WordDist, WordNorm]

  grw [csInf_le (a := 1 + (WordDist x z))]
  . simp [dist]
  . simp
  . simp

    have dist_eq: dist x z = dist x z := rfl
    conv at dist_eq =>
      lhs
      simp [dist, WordDist, WordNorm]

    have inf_mem := csInf_mem (s := {n | ∃ l, l.length = n ∧ ProdS (z * x⁻¹) l}) ?_
    .
      simp at inf_mem
      obtain ⟨l, l_len, l_prod⟩ := inf_mem
      simp [ProdS] at l_prod
      use [⟨y, hy⟩] ++ l
      simp [l_len, WordDist, WordNorm]
      rw [add_comm]
      simp
      simp [ProdS]
      rw [l_prod]
      group
    .
      obtain ⟨l, l_prod⟩ := mem_S_prod_list (z * x⁻¹)
      use l.length
      simp
      use l

lemma word_norm_mul_le (x y: G): WordNorm (x * y) ≤ WordNorm x + WordNorm y := by
  nth_rw 1 [WordNorm]
  rw [csInf_le_iff]
  .

    intro n hn
    rw [mem_lowerBounds] at hn
    simp at hn

    obtain ⟨x_l, x_l_prod, x_l_len⟩ := word_norm_prod_self x
    obtain ⟨y_l, y_l_prod, y_l_len⟩ := word_norm_prod_self y

    have concat_prod: (x_l ++ y_l).unattach.prod = x*y := by
      simp [ProdS] at x_l_prod y_l_prod
      simp [x_l_prod, y_l_prod]

    grw [hn (x_l ++ y_l).length (x_l ++ y_l) rfl concat_prod]
    simp
    grind
  . simp
  .
    obtain ⟨l, l_prod, l_len⟩ := word_norm_prod_self (x * y)
    use l.length
    simp
    use l


lemma word_norm_pow (x : G) (n: ℕ): WordNorm (x^n) ≤ n * WordNorm x := by
  induction n with
  | zero =>
    simp [word_norm_one]
  | succ n ih =>
    rw [pow_succ]
    grw [word_norm_mul_le]
    grw [ih]
    rw [add_mul]
    simp


lemma word_norm_list_prod_le (l: List G): WordNorm (l.prod) ≤ (l.map WordNorm).sum := by
  induction l with
  | nil =>
    simp [word_norm_one]
  | cons head tail ih =>
    simp
    grw [word_norm_mul_le]
    grw [ih]


lemma dist_word_le_mul {x y z : G} (hy: y ∈ S): WordDist x z ≤ (WordDist x (y * z)) + 1 := by
  by_cases x_eq: x = y * z
  . simp [x_eq]
    rw [WordDist_self]
    simp
    simp [WordDist_comm]
    have mul_dist := dist_word_mul (x := z) (y := y) hy
    simp [dist] at mul_dist
    exact mul_dist


  conv =>
    lhs
    simp [dist, WordDist, WordNorm]


  grw [csInf_le (a := (WordDist x (y * z)) + 1)]
  .
    simp


  simp
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod (n := WordDist x (y * z)) (y * z * x⁻¹) (rfl)
  match l with
  | [] =>
    simp [ProdS] at l_prod
    simp at l_len
    simp [← l_len]
    simp [ProdS]
    rw [eq_comm] at l_prod
    rw [mul_inv_eq_one] at l_prod
    grind
  | h::tail =>
    use [ ⟨y⁻¹, by simp [hGS.has_inv, hy]⟩, ⟨h.val, by simp [hGS.has_inv]⟩,] ++ tail
    simp [ProdS]
    simp [← l_len]
    simp [ProdS] at l_prod
    simp [l_prod]
    group

lemma word_dist_mul_eq {x y z : G} (hy: y ∈ S): WordDist x z = (WordDist x (y * z)) + 1 ∨ WordDist x z + 1 = (WordDist x (y * z)) ∨ WordDist x z = (WordDist x (y * z)) := by
  have first := dist_word_le_mul (x := x) (y := y) (z := z) hy
  have second := dist_word_le_mul (x := x) (y := y⁻¹) (z := (y * z)) (by rw [S_eq_Sinv]; simp [hy])
  simp at second
  grind

noncomputable instance WordDist.instMetricSpace: MetricSpace G where
  eq_of_dist_eq_zero := by
    intro x y hdist
    apply word_norm_eq_zero
    simp [dist] at hdist
    exact hdist

-- TODO - is there an easier way to transfer all of the theorems/instances from `G` to `Additive G`?


lemma word_norm_inv_le (x: G): WordNorm x ≤ WordNorm x⁻¹ := by
  simp [WordNorm]
  apply csInf_le'
  simp
  obtain ⟨lx, x_prod, x_len⟩ := word_norm_prod_self x⁻¹
  use (lx.map (fun (x: S) => ⟨x.val⁻¹, by (
      rw [← Finset.mem_inv']
      rw [← S_eq_Sinv]
      simp
    )⟩)).reverse
  refine ⟨?_, ?_⟩
  .
    simp
    exact x_len
  .
    simp [ProdS]

    clear x_len

    induction lx generalizing x with
    | nil =>
      simp
      simp [ProdS] at x_prod
      grind
    | cons head tail ih =>
      simp
      simp [ProdS] at x_prod
      simp [ProdS] at ih
      rw [ih (x := tail.unattach.prod⁻¹)]
      .
        rw[← inv_eq_iff_eq_inv] at x_prod
        simp [← x_prod]
      . simp


lemma word_norm_inv (x: G): WordNorm x = WordNorm x⁻¹ := by
  apply Nat.le_antisymm
  . apply word_norm_inv_le
  .
    conv =>
      rhs
      equals WordNorm x⁻¹⁻¹ => simp
    apply word_norm_inv_le


lemma WordDist_one (x: G): WordDist x 1 = WordNorm x := by
  simp [WordDist]
  rw [← word_norm_inv]

end GeneratesNS
