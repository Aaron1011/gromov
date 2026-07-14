import Mathlib

set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false
--set_option linter.unusedVariables true
--set_option linter.unusedVariables.analyzeTactics true

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
-- [hGS': Generates (S := S')] [hS': Nonempty S]


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
  have eq_through_y: z * x⁻¹ = z  * y * y⁻¹ * x⁻¹ := by
    simp

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

noncomputable instance WordDist.instPseudoMetricSpaceAddOpp: PseudoMetricSpace (Additive G) where
  dist x y := dist x.toMul y.toMul
  dist_self x := by
    apply PseudoMetricSpace.dist_self
  dist_comm x y := by
    apply PseudoMetricSpace.dist_comm
  dist_triangle x y z := by
    apply PseudoMetricSpace.dist_triangle

noncomputable instance WordDist.instMetricSpaceAddOpp: MetricSpace (Additive G) where
  eq_of_dist_eq_zero := by
    intro x y hxy
    have := MetricSpace.eq_of_dist_eq_zero (x := x.toMul) (y := y.toMul) hxy
    exact this

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


-- noncomputable instance WordNorm.instSemiNormedGroup: SeminormedGroup G where
--   norm := fun g => WordNorm g
--   dist_eq := by
--     intro x y
--     simp [dist, WordDist]
--     sorry



--def WordMetricSpace := MetricSpace.ofDistTopology ()
noncomputable instance WordDist.instMeasurableSpace: MeasurableSpace G := borel G

noncomputable instance WordDist.instMeasureableSpaceOpp: MeasurableSpace (Additive G) := borel (Additive G)

noncomputable instance WordDist.instBorelSpace: BorelSpace G where
  measurable_eq := rfl


noncomputable instance WordDist.instBorelSpaceAddOpp: BorelSpace (Additive G) where
  measurable_eq := rfl

-- TODO - are we really supposed to be using a metric topology if it turns out to be the discrete topology?
lemma singleton_open (x: G): IsOpen {x} := by
  rw [Metric.isOpen_singleton_iff]
  use 1
  simp only [gt_iff_lt, zero_lt_one, true_and]
  intro y hy
  simp [dist] at hy
  have dist_zero := dist_eq_zero (x := y) (y := x)
  simp [dist] at dist_zero
  rw [dist_zero] at hy
  exact hy

instance discreteTopology: DiscreteTopology G := by
  rw [← singletons_open_iff_discrete]
  exact singleton_open

instance : ContinuousMul G where
  continuous_mul := continuous_of_discreteTopology

instance : ContinuousInv G where
  continuous_inv := continuous_of_discreteTopology

instance: IsTopologicalGroup G where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology


-- instance IsTopologicalGroupAddOpp: IsTopologicalAddGroup (Additive G) where
--   continuous_add := continuous_of_discreteTopology
--   continuous_neg := continuous_of_discreteTopology

-- Define Haar measure so that singleton sets have measure 1 -
-- I think this is what we want in order to be able to nicely convert integrals to sums
noncomputable def haarSingleton: TopologicalSpace.PositiveCompacts G := {
  carrier := {1}
  isCompact' := by
    simp
  interior_nonempty' := by
    have one_mem: (1 : G) ∈ interior {1} := by
      rw [mem_interior]
      use {1}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨1, one_mem⟩
}

lemma mul_singleton_carrier: (haarSingleton.carrier) = ({1} : (Set G)) := by
  unfold haarSingleton
  rfl

noncomputable abbrev myHaar := MeasureTheory.Measure.haarMeasure haarSingleton

noncomputable instance WordDist.measureSpace: MeasureTheory.MeasureSpace G := {
  volume := myHaar
}

noncomputable def addHaarSingleton: TopologicalSpace.PositiveCompacts (Additive G) := {
  carrier := {0}
  isCompact' := by
    simp
  interior_nonempty' := by
    have zero_mem: (0 : Additive G) ∈ interior {0} := by
      rw [mem_interior]
      use {0}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨0, zero_mem⟩
}

lemma singleton_carrier: (addHaarSingleton.carrier) = ({0} : (Set (Additive G))) := by
  unfold addHaarSingleton
  rfl

noncomputable abbrev myHaarAddOpp := MeasureTheory.Measure.addHaarMeasure (G := Additive G) addHaarSingleton


instance countable_G: Countable G := by
  apply Function.Surjective.countable (f := fun (x: List S) => x.unattach.prod)
  intro g
  obtain ⟨l, hl⟩ := mem_S_prod_list  g
  use l
  simp only
  unfold ProdS at hl
  rw [hl]


-- TODO - use the fact that G is finitely generated
instance countable_add_G: Countable (Additive G) := by
  exact inferInstanceAs (Countable G)


lemma singleton_pairwise_disjoint {T: Type*} (s: Set (T)) : s.PairwiseDisjoint Set.singleton := by
  refine Set.pairwiseDisjoint_iff.mpr ?_
  intro a ha b hb hab
  unfold Set.singleton at hab
  simp at hab
  exact hab.symm





-- Use the fact that we have the discrete topology
set_option maxHeartbeats 500000 in
lemma my_add_haar_eq_count: (myHaarAddOpp) = MeasureTheory.Measure.count := by
  ext s hs
  by_cases s_finite: Set.Finite s
  .
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.Measure.count_apply_finite s s_finite]
    rw [MeasureTheory.measure_biUnion]
    .
      -- TODO - extract 'measure {a} = 1' to a lemma
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      rw [ENNReal.tsum_set_const]
      simp
      norm_cast
      rw [Set.Finite.encard_eq_coe_toFinset_card s_finite]
    . exact Set.Finite.countable s_finite
    .
      apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp
  .
    have s_infinite: s.Infinite := by
      exact s_finite
    rw [MeasureTheory.Measure.count_apply_infinite s_infinite]
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.measure_biUnion]
    .
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      simp only [ENNReal.tsum_one, ENat.toENNReal_eq_top, ENat.card_eq_top]
      exact Set.infinite_coe_iff.mpr s_finite
    . exact Set.to_countable s
    . apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp

lemma my_haar_eq_count: (myHaar) = MeasureTheory.Measure.count := by
  ext s hs
  by_cases s_finite: Set.Finite s
  .
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.Measure.count_apply_finite s s_finite]
    rw [MeasureTheory.measure_biUnion]
    .
      -- TODO - extract 'measure {a} = 1' to a lemma
      simp_rw [MeasureTheory.Measure.haar_singleton]
      unfold myHaar
      simp_rw [← mul_singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.haarMeasure_self]
      rw [ENNReal.tsum_set_const]
      simp
      norm_cast
      rw [Set.Finite.encard_eq_coe_toFinset_card s_finite]
    . exact Set.Finite.countable s_finite
    .
      apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp
  .
    have s_infinite: s.Infinite := by
      exact s_finite
    rw [MeasureTheory.Measure.count_apply_infinite s_infinite]
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.measure_biUnion]
    .
      simp_rw [MeasureTheory.Measure.haar_singleton]
      unfold myHaar
      simp_rw [← mul_singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.haarMeasure_self]
      simp only [ENNReal.tsum_one, ENat.toENNReal_eq_top, ENat.card_eq_top]
      exact Set.infinite_coe_iff.mpr s_finite
    . exact Set.to_countable s
    . apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp


instance my_add_haar_left_invariant: (myHaarAddOpp.IsAddLeftInvariant (G := Additive (G))) := by
  rw [my_add_haar_eq_count]
  infer_instance

instance my_add_haar_right_invariant: (myHaarAddOpp.IsAddRightInvariant (G := Additive (G))) := by
  rw [my_add_haar_eq_count]
  infer_instance




-- With the counting measure, A.E is the same as everywgere
lemma count_ae_everywhere (p: G → Prop): (∀ᵐ g ∂(MeasureTheory.Measure.count), p g) = ∀ a: G, p a := by
  rw [MeasureTheory.ae_iff]
  simp [MeasureTheory.Measure.count_eq_zero_iff]
  -- TODO - there has to be a much simpler way of proving this
  refine ⟨?_, ?_⟩
  . intro h
    intro a
    by_contra this
    have a_in: a ∈ {a | ¬ p a} := by
      simp [this]
    have foo := Set.nonempty_of_mem a_in
    rw [← Set.not_nonempty_iff_eq_empty] at h
    contradiction
  . intro h
    by_contra this
    simp at this
    rw [← ne_eq] at this
    rw [← Set.nonempty_iff_ne_empty'] at this
    obtain ⟨a, ha⟩ := this
    specialize h a
    simp at ha
    contradiction

lemma ae_eventually_everywhere {f g: G → ℝ}: ((∀ᵐ (x : G), f x = g x)) ↔ (f = g) := by
  simp [MeasureTheory.volume]
  simp_rw [my_haar_eq_count]
  have foo := count_ae_everywhere (p := fun a => f a = g a)
  conv at foo =>
    rhs
    equals f = g =>
      have my_ext := funext_iff (f := f) (g := g)
      simp at my_ext
      simp
      exact id (Iff.symm my_ext)

  simp
  simp at foo
  exact foo


@[simp]
lemma ae_eq_everywhere {f g: G → ℝ}: (f =ᶠ[MeasureTheory.ae MeasureTheory.volume (α := G)] g) ↔ (f = g) := by
  simp [Filter.EventuallyEq]
  apply ae_eventually_everywhere


-- Use the fact that our measure is the counting measure (since we have the discrete topology),
-- and negating a finite set of points in an additive group leaves the cardinality unchanged
instance myNegInvariant: MeasureTheory.Measure.IsNegInvariant (myHaarAddOpp) := {
  neg_eq_self := by
    rw [my_add_haar_eq_count]
    simp only [MeasureTheory.Measure.neg_eq_self]
}





-- Definition 3.5 in Vikman - a harmonic function on G
-- Note that our multiplication order is swapped: f (s * x) instead of f (x * s)
-- This is needed to make it match up with the result of MeasureTheory.convolution
-- TODO - can we combine these
def Harmonic (f: G → ℝ): Prop := ∀ x: G, f x = ((1 : ℝ) / #(S)) * ∑ s ∈ S, f (s * x)
def HarmonicR (f: G → ℝ): Prop := ∀ x: G, f x = ((1 : ℝ) / #(S)) * ∑ s ∈ S, f (s * x)

-- A Lipschitz harmonic function from section 3.2 of Vikman
structure LipschitzH [Generates ] where
  -- The underlying function
  toFun: G → ℝ
  -- The function is Lipschitz for some constant C
  lipschitz: ∃ C, LipschitzWith C toFun
  -- The function is harmonic
  harmonic: Harmonic  toFun

def IsLipschitz (f: G → ℝ) := ∃ C, LipschitzWith C f

instance: FunLike (LipschitzH) G ℝ where
  coe := LipschitzH.toFun
  -- TODO - why does this work? I blindly copied it from `OneHom.funLike`
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem LipschitzH.ext [Generates ] {f g: LipschitzH} (h: ∀ x, f.toFun x = g.toFun x): f = g := DFunLike.ext _ _ h

instance LipschitzH.add [Generates ] : Add (LipschitzH) := {
  add := fun f g => {
    toFun := fun x => f.toFun x + g.toFun x
    lipschitz := by
      obtain ⟨C1, hC1⟩ := f.lipschitz
      obtain ⟨C2, hC2⟩ := g.lipschitz
      use C1 + C2
      exact LipschitzWith.add hC1 hC2
    harmonic := by
      unfold Harmonic
      intro x
      have ha := f.harmonic
      have hb := g.harmonic
      unfold Harmonic at ha hb
      simp_rw [ha x, hb x]
      field_simp
      rw [← Finset.sum_add_distrib]
  }
}


-- TODO - mark this as a simp lemma
@[simp]
lemma LipschitzH_apply [Generates ] (f: LipschitzH) (x: G): f x = f.toFun x := rfl


lemma S_nonempty: S.Nonempty := by exact Finset.nonempty_coe_sort.mp hS

lemma S_card_ne_zero_re: (#(S) : ℝ) ≠ 0 := by
  norm_cast
  simp
  have foo := hS
  simp only [nonempty_subtype] at foo
  exact Finset.nonempty_iff_ne_empty.mp foo

lemma S_card_ne_zero: (#(S) : ℂ) ≠ 0 := by
  norm_cast
  simp
  have foo := hS
  simp only [nonempty_subtype] at foo
  exact Finset.nonempty_iff_ne_empty.mp foo

def ConstLipschitzH (z: ℝ) : LipschitzH := {
  toFun := fun x => z
  lipschitz := by
    use 0
    apply LipschitzWith.const
  harmonic := by
    unfold Harmonic
    intro x
    simp
    field_simp
    have foo := S_card_ne_zero_re
    field_simp
}

lemma ConstLipschitzH_apply (z : ℝ) (g: G): (ConstLipschitzH z) g = z := by
  unfold ConstLipschitzH
  rfl

instance LipschitzH.zero [Generates ] : Zero (LipschitzH) := {
  zero := {
    toFun := fun x => 0
    lipschitz := by
      use 0
      exact LipschitzWith.const 0
    harmonic := by simp [Harmonic]
  }
}

def LipschitzH.const (k: ℝ) : LipschitzH := {
  toFun := fun x => k
  lipschitz := by
    use 0
    exact LipschitzWith.const _
  harmonic := by
    simp [Harmonic]
    have foo := S_card_ne_zero_re
    field_simp [foo]
}


@[simp]
theorem LipschitzH.add_apply (f g: LipschitzH) (x: G): (f + g).toFun x = f x + g x := by
  unfold LipschitzH.add
  rfl


instance lipschitzSMul: SMul ℝ (LipschitzH) := {
  smul := fun c f => {
    toFun := fun x => c * f.toFun x
    lipschitz := by
      conv =>
        rhs
        intro C
        rhs
        equals (fun (x: ℝ) => c * x) ∘ f.toFun =>
          unfold Function.comp
          simp
      obtain ⟨C, hC⟩ := f.lipschitz
      use ‖c‖₊ * C
      apply LipschitzWith.comp (lipschitzWith_smul _) hC
    harmonic := by
      unfold Harmonic
      intro x
      field_simp
      rw [← Finset.mul_sum]
      rw [← mul_div]
      rw [mul_eq_mul_left_iff]
      left
      have hf := f.harmonic x
      unfold Harmonic at hf
      simp at hf
      field_simp at hf
      exact hf
  }
}


instance negLipschitzH: Neg (LipschitzH) := {
  neg := fun f => {
    toFun := fun x => -f.toFun x
    lipschitz := by
      obtain ⟨C, hC⟩ := f.lipschitz
      use C
      exact LipschitzWith.neg hC
    harmonic := by
      have f_harmonic := f.harmonic
      simp [Harmonic] at f_harmonic
      unfold Harmonic
      intro g
      simp
      specialize f_harmonic g
      exact f_harmonic
  }
}

-- TODO - is there an existing instance we should be using here?
instance subLipschithZ: Sub (LipschitzH) := {
  sub := fun f g => f + -g
}

instance lipschitzSmulZ: SMul ℤ (LipschitzH) := {
  smul := fun n f => (n : ℝ) • f
}



@[simp]
lemma lipschitz_neg_tofun (f: LipschitzH): (-f).toFun = -(f.toFun) := by
  rfl


@[simp]
lemma lipschitz_add_tofun (f g: LipschitzH): (f + g).toFun = f.toFun + g.toFun := by
  rfl

@[simp]
lemma lipschitz_sub_tofun (f g: LipschitzH): (f - g).toFun = f.toFun - g.toFun := by
  rfl

@[simp]
lemma lipschitz_smul_tofun (c: ℝ) (f: LipschitzH): (c • f).toFun = c • f.toFun := by
  rfl

instance LipschitzH.addMonoid [Generates ] : AddMonoid (LipschitzH) := {
  LipschitzH.zero,
  LipschitzH.add with
  add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
  zero_add := fun _ => ext fun _ => zero_add _
  add_zero := fun _ => ext fun _ => add_zero _
  nsmul := fun n f => (n : ℝ) • f
  nsmul_zero := by
    intro f
    dsimp [HSMul.hSMul, SMul.smul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
  nsmul_succ := by
    intro n f
    ext g
    simp [lipschitz_smul_tofun]
    rw [add_mul]
    simp
}



-- -- See https://github.com/leanprover-community/mathlib4/blob/6c6e0180f0d3dc9f47f85532f48d268d8656789a/Mathlib/Topology/ContinuousMap/Bounded/Normed.lean#L194-L196
-- instance lipschitzHAddCommGroup: AddCommGroup (LipschitzH) := by
--   apply DFunLike.coe_injective.addCommGroup
--   .
--     ext g
--     simp [DFunLike.coe]
--     unfold Zero.toOfNat0
--     simp [Zero.zero]
--   .
--     intro x y
--     simp [DFunLike.coe]
--     ext g
--     simp [DFunLike.coe]
--   . intro f
--     ext g
--     simp [DFunLike.coe]
--     simp [negLipschitzH]
--   .
--     intro f h
--     ext g
--     simp [DFunLike.coe]
--     conv =>
--       lhs
--       dsimp [HSub.hSub]
--     simp [subLipschithZ]
--     simp [DFunLike.coe]
--     simp [negLipschitzH]
--     rw [sub_eq_add_neg]
--   . intro f
--     intro n
--     simp [DFunLike.coe]
--     dsimp [HSMul.hSMul]
--     dsimp [SMul.smul]



instance LipschitzH.instAddCommMonoid: AddCommMonoid (LipschitzH) := {
  LipschitzH.addMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _
}



instance LipschitzH.instAddCommGroup: AddCommGroup (LipschitzH) := {
  LipschitzH.instAddCommMonoid with
  sub_eq_add_neg := by
    intro f h
    ext g
    simp [lipschitz_sub_tofun, lipschitz_add_tofun, lipschitz_neg_tofun]
    rfl
  zsmul := fun n f => (n : ℝ) • f
  zsmul_zero' := by
    intro f
    ext g
    simp only [HSMul.hSMul, SMul.smul, DFunLike.coe, Int.cast_zero, zero_mul]
    rfl
  neg_add_cancel := by
    intro f
    ext g
    simp [negLipschitzH]
    rfl
  zsmul_succ' := by
    intro n f
    simp
    ext g
    simp [lipschitz_smul_tofun]
    rw [add_mul]
    simp
  zsmul_neg' := by
    intro n hn
    simp
    ext g
    simp [lipschitz_smul_tofun]
    group
}


-- V is the vector space
-- abbrev V := Module ℝ (LipschitzH)



@[simp]
lemma zero_apply (x: G): (0: LipschitzH ).toFun x = 0 := by
  unfold LipschitzH.zero
  rfl


@[simp]
theorem LipschitzH.finset_sum_apply {ι: Type*} [Fintype ι] [DecidableEq ι] (s: Finset ι) (f: ι → LipschitzH) (x: G): (∑ i ∈ s, f i) x = (∑ i ∈ s, f i x) := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s a_not_mem ih =>
    rw [Finset.sum_insert a_not_mem]
    rw [LipschitzH_apply, add_apply]
    rw [ih]
    rw [Finset.sum_insert a_not_mem]


--set_option pp.all true

instance lipschitzHVectorSpace : Module ℝ (LipschitzH) := {
  smul := lipschitzSMul.smul
  one_smul := by simp [HSMul.hSMul, SMul.smul]
  mul_smul := by
    intro x y f
    simp [HSMul.hSMul, SMul.smul]
    ext g
    rw [mul_assoc]
  smul_zero := by
    intro c
    dsimp [HSMul.hSMul, SMul.smul]
    ext g
    simp
  smul_add := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [mul_add]
    ext p
    simp [DFunLike.coe]
  add_smul := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [add_mul]
    ext p
    simp [DFunLike.coe]
  zero_smul := by
    intro a
    ext g
    simp [HSMul.hSMul, SMul.smul, DFunLike.coe]
}

noncomputable instance finite_ball (x: G) (r: ℝ): Set.Finite (Metric.ball x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
  have foo := List.finite_length_le S (WordNorm x + ⌈r⌉₊)
  rw [← Set.finite_coe_iff, Set.coe_setOf] at foo
  apply Finite.of_injective (β := {l : List S // l.length ≤ WordNorm x + ⌈r⌉₊}) (fun a => ⟨a.val, by (
    have ha := a.prop
    simp [-Subtype.coe_prop] at ha
    obtain ⟨y, hy, a_prod⟩ := ha
    have ⟨prod_eq, prod_len⟩ := (word_norm_prod_self y).choose_spec
    rw [a_prod] at prod_len
    rw [prod_len]
    simp [dist] at hy
    conv =>
      lhs
      equals WordDist 1 y =>
        simp [WordDist]


    grw [WordDist_triangle (y := x)]
    nth_rw 2 [WordDist_comm]
    simp [WordDist]
    simp [WordDist] at hy
    rw [← Nat.lt_ceil] at hy
    grind
  )⟩) ?_
  intro a b hab
  grind
) (by
  intro a ha b hb hab
  have a_prop := (word_norm_prod_self a).choose_spec.1
  have b_prop := (word_norm_prod_self b).choose_spec.1
  rw [← a_prop, ← b_prop]
  simp [hab]
)

-- TODO - deduplicate 99% of this with finite_ball
noncomputable instance finite_closed_ball (x: G) (r: ℝ): Set.Finite (Metric.closedBall x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
  have foo := List.finite_length_le S (WordNorm x + ⌈r⌉₊)
  rw [← Set.finite_coe_iff, Set.coe_setOf] at foo
  apply Finite.of_injective (β := {l : List S // l.length ≤ WordNorm x + ⌈r⌉₊}) (fun a => ⟨a.val, by (
    have ha := a.prop
    simp [-Subtype.coe_prop] at ha
    obtain ⟨y, hy, a_prod⟩ := ha
    have ⟨prod_eq, prod_len⟩ := (word_norm_prod_self y).choose_spec
    rw [a_prod] at prod_len
    rw [prod_len]
    simp [dist] at hy
    conv =>
      lhs
      equals WordDist 1 y =>
        simp [WordDist]


    grw [WordDist_triangle (y := x)]
    nth_rw 2 [WordDist_comm]
    simp [WordDist]
    simp [WordDist] at hy
    -- This is the only part that's different from finite_ball
    grw [Nat.le_ceil (a := r)] at hy
    simpa using hy
  )⟩) ?_
  intro a b hab
  grind
) (by
  intro a ha b hb hab
  have a_prop := (word_norm_prod_self a).choose_spec.1
  have b_prop := (word_norm_prod_self b).choose_spec.1
  rw [← a_prop, ← b_prop]
  simp [hab]
)



-- TODO - I don't think we can use this, as `MeasureTheory.convolution' would require our group to be commutative
-- (via `NormedAddCommGroup`)
open scoped Convolution
open MeasureTheory
-- TODO - should we define this using 'Lp'?
-- NOTE - the Mathlib convolution uses the opposite order of arguments as in the Vikman paper (g(x - t) instead of g(t - x))
-- I originally used 'MulOpposite' make our usage agree with the paper, but this made it an enormous pain to work with
-- (since while Additive G is defeq to G, MulOpposite G is not defeq to G)
-- Nothing in the paper should actually depend on this (since we take a convolution over a symmetric generating set S)
-- Some of our definitions will have an inverse or order swap compared to the paper, but this is better than
-- fighting with 'MulOpposite' every time we need to prove something about a convolution

-- Note - there's some defeq abuse going on here, as we're passing in 'f' and 'g' directly (they take in G, not 'Additive G')
-- However, this makes it much easier to prove properties about this via the `MeasureTheory.ConvolutionExists` API
noncomputable def Conv (f g: G → ℝ) (x: G) : ℝ :=
  (MeasureTheory.convolution (G := Additive G) f g (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp x)



def ConvExists (f g: G → ℝ) := MeasureTheory.ConvolutionExists (G := Additive G) (fun x => f x.toMul) (fun x => g x.toMul) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp

def ConvExistsAt (f g: G → ℝ) (x: G) := MeasureTheory.ConvolutionExistsAt (G := Additive G) (fun x => f x.toMul) (fun x => g x.toMul) x (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp


-- Defintion 3.11 in Vikman: The function 'μ',  not to be confused with a measure on a measure space
noncomputable def mu: G → ℝ := ((1 : ℝ) / (#(S) : ℝ)) • ∑ s ∈ S, Pi.single s (1 : ℝ)

-- Definition 3.11 in Vikman - the m-fold convolution of μ with itself
noncomputable def muConv (n: ℕ): G → ℝ := (Nat.iterate (fun f => Conv  f (mu )) n) (mu )


-- TODO - this is left over from when I used MulOpposite
-- we should remove all usages of this
abbrev opAdd (g : G) := Additive.ofMul g


lemma conv_eq_sum {f h: G → ℝ} (hconv: ConvExists f h) (g: G): Conv f h g = ∑' (a : Additive G), f (a) * h (g * (Additive.toMul a)⁻¹) := by
  unfold Conv
  unfold MeasureTheory.convolution
  rw [MeasureTheory.integral_countable']
  .
    simp_rw [MeasureTheory.measureReal_def]
    unfold myHaarAddOpp
    simp_rw [MeasureTheory.Measure.addHaar_singleton]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    simp_rw [← singleton_carrier]
    simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    field_simp

    -- TODO - avoid defeq abuse here
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals h (Additive.ofMul g - a) =>
        rfl

    conv =>
      rhs
      arg 1
      intro a
      rhs
      arg 1
      equals Additive.ofMul g - a =>
        unfold Additive.toMul
        unfold Additive.ofMul
        simp
        rw [sub_eq_add_neg]
        rfl

  . exact (hconv (opAdd g))


lemma conv_eq_sum'  {f h: G → ℝ} (hconv: ConvExists f h): Conv f h = fun g => ∑' (a : Additive G), f ((Additive.toMul a)) * h (g * (Additive.toMul a)⁻¹) := by
  funext g
  exact conv_eq_sum hconv g


abbrev delta (s: G): G → ℝ := Pi.single s 1


-- A versi on of `conv_exists` where at least one of the functions has finite support
-- This lets us avoid dealing with 'MemLp' in most cases
lemma conv_exists_fin_supp (f g: G → ℝ) (hfg: f.support.Finite ∨ g.support.Finite): ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
  intro x
  apply Continuous.integrable_of_hasCompactSupport
  . exact continuous_of_discreteTopology
  .
    unfold HasCompactSupport
    rw [isCompact_iff_finite]
    dsimp [tsupport]
    rw [closure_discrete]
    simp only [Function.support_mul]
    match hfg with
    | .inl hf =>
      apply Set.Finite.inter_of_left
      apply Set.Finite.subset (s := opAdd '' f.support)
      . unfold opAdd
        exact Set.Finite.image (fun g ↦ Additive.ofMul g) hf
      . intro a ha
        simp at ha
        simp [opAdd]
        exact ha
    | .inr hg =>
      apply Set.Finite.inter_of_right
      let myFun := fun a => -(opAdd a) + x
      have finite_image := Set.finite_image_iff (f := myFun) (s := g.support) ?_
      .
        conv =>
          arg 1
          equals (myFun '' Function.support g) =>
            ext a
            simp
            refine ⟨?_, ?_⟩
            . intro ha
              use (Additive.toMul x) / ((Additive.toMul a))
              refine ⟨ha, ?_⟩
              simp [myFun, opAdd]
            . intro ha
              simp [myFun, opAdd] at ha
              obtain ⟨b, b_zero, a_eq⟩ := ha
              rw [← a_eq]
              simp [b_zero]
        rw [finite_image]
        exact hg
      .
        simp [myFun, opAdd]

-- Proposition 3.12, item 1, in Vikman
lemma f_conv_delta (f: G → ℝ) (g s: G): (Conv  f (delta s)) g = f (s⁻¹ * g) := by
  unfold delta
  rw [conv_eq_sum]
  .
    rw [tsum_eq_sum (s := {opAdd ((s⁻¹ * g))}) ?_]
    .
      simp
      -- TODO - why does this need 'conv'?
      conv =>
        lhs
        arg 2
        arg 3
        simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right]
      rw [← mul_assoc]
      -- TODO - why is 'simp' not doing these?
      rw [mul_inv_cancel]
      rw [one_mul]
      simp
      rfl
    .
      intro b hb
      simp only [Finset.mem_singleton] at hb
      simp only [mul_eq_zero]
      right
      apply Pi.single_eq_of_ne
      apply_fun (fun x => s⁻¹ * x)
      simp
      apply_fun (fun x => (x * (Additive.toMul b)) )
      simp
      rw [eq_comm]
      unfold opAdd at hb
      apply_fun Additive.ofMul
      simp
      apply_fun (fun x => x + b)
      simp only []
      rw [add_assoc]
      simp
      exact hb
  .
    apply conv_exists_fin_supp
    right
    simp


lemma mu_finsupp: (mu ).support.Finite := by
  simp [mu]
  rw [Function.support_const_smul_of_ne_zero]
  .
    apply Set.Finite.subset (s := ⋃ i ∈ S, Function.support (Pi.single i (1 : ℝ)))
    .
      simp
      exact Set.toFinite (⋃ i ∈ S, {i})
    .
      conv =>
        lhs
        arg 1
        equals fun (x: G) => ∑ s ∈ S, Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) x =>
          funext a
          simp
      apply Finset.support_sum (s := S) (f := fun i => Pi.single i (1: ℝ))
  . simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

#print axioms mu_finsupp

-- Proposition 3.12, item 2, in Vikman
lemma f_conv_mu (f: G → ℝ): (Conv  f (mu )) = fun g => ((1 : ℝ) / (#(S) : ℝ)) * ∑ s ∈ S, f (s * g) := by
  funext g
  rw [conv_eq_sum]
  .

    dsimp [mu]
    simp_rw [← mul_assoc]
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals (∑ s ∈ S, (Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) ((g * (Additive.toMul a)⁻¹)))) =>
        simp

    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum]
    .
      --rw [Finset.sum_comm]
      have delta_conv := f_conv_delta  f g
      conv at delta_conv =>
        intro x
        rw [conv_eq_sum (by
          apply conv_exists_fin_supp
          right
          simp
        )]

      simp_rw [mul_comm, mul_assoc]
      --simp_rw [← mul_tsum]
      conv =>
        lhs
        rhs
        intro x
        arg 1
        intro b
        rw [mul_comm]
        rw [mul_assoc]
      simp [delta] at delta_conv
      conv at delta_conv =>
        intro x
        lhs
        arg 1
        intro a
        rw [mul_comm]
      conv =>
        lhs
        rhs
        intro x
        rw [Summable.tsum_mul_left (hf := by (
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (   x⁻¹ * g  ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
          --apply f_mul_mu_summable
        ))]
        rw [delta_conv x]

      simp
      rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [mul_comm]
      simp
      left
      conv =>
        lhs
        arg 1
        equals S⁻¹ =>
          exact S_eq_Sinv
      simp
    .
      intro s hs
      by_cases card_zero: #(S) = 0
      .
        simp [card_zero]
      .
        conv =>
          arg 1
          intro a
          rw [mul_assoc, mul_comm, mul_assoc]
        rw [summable_mul_left_iff]
        .
          -- TODO - deduplicate this
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (s⁻¹ * g ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
          --apply f_mul_mu_summable
        .
          simp [card_zero]
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp




noncomputable def conv_mu_lp2 (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := MeasureTheory.MemLp.toLp (Conv f (mu )) (by
  rw [MeasureTheory.MemLp]
  refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [f_conv_mu]
  --apply ENNReal.rpow_lt_top_of_nonneg
  --. simp
  --.
  simp_rw [Finset.mul_sum]
  --  (1 : ℝ) / (#(S) : ℝ) * f (a * s)
  have other := MeasureTheory.memLp_finset_sum (μ := MeasureTheory.volume (α := G)) (s := S) (p := 2) (f := fun s a => ((1 : ℝ) / (#(S) : ℝ)) * f (s * a)) (by
    intro s hs
    simp
    apply MeasureTheory.MemLp.const_mul
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      simp_rw [my_haar_eq_count]
      rw [MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self s]
      have mem_f := Lp.memLp f
      simp [volume, my_haar_eq_count] at mem_f
      exact mem_f
    . apply AEMeasurable.of_discrete
  )
  have sum_norm := other.2
  simp [eLpNorm, eLpNorm'] at sum_norm
  field_simp at sum_norm
  field_simp
  exact sum_norm
)

-- The Vikman paper defines the Laplace operator as a function ' ∆ : ℓ2(G) → ℓ2(G)'
-- However, we later have '∆ H_n', where H_n is only known to be in L∞
-- We should eventually refactor this, but for we, we just define it twice, once with just plain functions
-- The 'b' is for 'base' (we should come up with a better name)
noncomputable def Laplace_b (f: G → ℝ): G → ℝ := f - (Conv f (mu ))
noncomputable def Laplace (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := f - (conv_mu_lp2 f)


-- TODO - make this Finite to avoid a non-compuatable Fintype instance
noncomputable instance fintype_ball (x: G) (r: ℝ): Fintype ↑(Metric.ball x r) := Set.Finite.fintype (finite_ball _ _)
noncomputable instance fintype_closedBall (x: G) (r: ℝ): Fintype ↑(Metric.closedBall x r) := Set.Finite.fintype (finite_closed_ball _ _)

instance fintype_ball_boundary (x: G) (r: ℝ): Fintype ↑{y | dist y x = r} := by
  sorry

-- Graphs and Discrete Direchlet Spaces
-- https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-GraphTh/Keller/KellerLenzWojciechowski_GraphsAndDiscreteDirichletSpaces_wu_version.pdf


-- Lemma 12.2 in Keller (Graphs and Discrete Dirichlet Spaces), specialized to harmonic functions: L(u) = 0
--lemma laplace_harmonic_cutoff (f φ : G → ℝ) (x): ∑ x ∈ Metric.ball 1 (2 * r), ∑ s ∈ S, |(f x) - f (s * x)|^2


-- lemma s_sinv_split_one: S = (S \ {1}) ∪ (S⁻¹ \ {1}) ∪ {1} := by
--   rw [← s_union_sinv]
--   ext a
--   by_cases a_eq_one: a = 1
--   .
--     simp [a_eq_one]
--     apply hGS.one_mem
--   .
--     simp [a_eq_one]
--     grind




-- New argument:
-- Write ∑ s ∈ S (f x - f (x * s))^2
-- = ∑ s ∈ S (f x)^2 - (f x) (f ( x * s)) + (f (x * s))^2
-- = |S| * (f x)^2 - (f x) * |S| * (f x) + |S| * (f x)^2 -- use harmonicity, and simplify the shift 'f ( x *s)' when summing over all x
-- = |S| * (f x)^2

-- New approach
-- (f△f) = f(f - (f ⬝ μ)) = f^2 - f(f ⬝ μ)

--  f^2 - f(f ⬝ μ) +

-- Other stuff:
--   (∑ s ∈ S, (f x - f (x * s)))^2
-- = (∑ s_1 ∈ S, ∑ s_2 ∈ S, ((f x) - f(x * s_1))*((f x) - f(x * s_2)
-- = (∑ s_1 ∈ S, ∑ s_2 ∈ S, (f x)^2 - (f x)(f (x * s_1)) - (f x) (f (x * s_2)) + (f (x * s_1))(f (x * s_2)))
-- = (∑ s_1 ∈ S, ∑ s_2 ∈ S, (f x)^2 - (f x)((f (x * s_1) - (f (x * s_2))) + (f (x * s_1))(f (x * s_2)))
lemma harmonic_stokes_theorem (f: G → ℝ) (hf: Harmonic f) (r: ℝ): ∑ x ∈ Metric.ball 1 (2 * r), ∑ s ∈ S, (f x - f (x * s))^2 = 0 := by
  sorry
  --rw [s_sinv_split_one]
  --rw []


  -- Use this if we end up with closedBall in the theorem statement
  -- conv =>
  --   arg 1
  --   arg 1
  --   equals (Metric.ball 1 (2 * r)).toFinset ∪ {x : G | dist x 1 = 2 * r}.toFinset =>
  --     rw [← Set.toFinset_union]
  --     simp_rw [Metric.closedBall, Metric.ball]
  --     simp [le_iff_lt_or_eq]
  --     rw [Set.setOf_or]

  -- rw [Finset.sum_union]
  -- conv =>
  --   lhs
  --   lhs
  --   equals 0 =>


  --     sorry
  -- simp_rw [Metric.closedBall]

  --sorry

--instance V_FiniteDimentional: FiniteDimensional ℂ (LipschitzH) := by
  -- This is a very long part of the proof in Vikman
--  sorry


def ConstF: Submodule ℝ (LipschitzH) := {
  carrier := Set.range ConstLipschitzH
  add_mem' := by
    intro a b ha hb
    simp at ha
    simp at hb
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    simp
    use (x + y)
    ext g
    simp [ConstLipschitzH]
    rw [← hx, ← hy]
    dsimp [ConstLipschitzH]
  zero_mem' := by
    use (0 : ℝ)
    simp [ConstLipschitzH]
    ext g
    simp
  smul_mem' := by
    intro c f hf
    simp at hf
    simp
    obtain ⟨x, hx⟩ := hf
    use (c * x)
    ext g
    simp [ConstLipschitzH]
    left
    rw [← hx]
    simp [ConstLipschitzH]
}

instance isometricGMul: IsIsometricSMul (MulOpposite G) (G) where
  isometry_smul := by
    intro g
    simp [Isometry]
    intro a b
    simp [edist]
    simp [PseudoMetricSpace.edist]
    simp [WordDist]
    group


-- instance isometricGMul: IsIsometricSMul G G where
--   isometry_smul := by
--     intro g
--     simp [Isometry]
--     intro a b
--     simp [edist]
--     simp [PseudoMetricSpace.edist]
--     simp [WordDist]
--     group


def gAct (g: G) (v: LipschitzH ): LipschitzH  := {
  toFun := fun x => v (x * g)
  lipschitz := by
    obtain ⟨C, hC⟩ := v.lipschitz
    use C
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [lipschitzWith_iff_dist_le_mul] at hC
    specialize hC (x * g) (y * g)
    simp [DFunLike.coe]
    grw [hC]
    simp [dist, WordDist]
    group
  harmonic := by
    unfold Harmonic
    intro x
    simp
    have v_harmonic := v.harmonic
    simp [Harmonic] at v_harmonic
    specialize v_harmonic (x * g)
    rw [v_harmonic]
    simp_rw [← mul_assoc]
}

lemma gAct_mul (g h : G) (f: LipschitzH ): gAct (g * h) f = gAct g (gAct h f) := by
  unfold gAct
  ext x
  simp [DFunLike.coe]
  rw [← mul_assoc]



def gAct_const (g: G) (z: ℝ): gAct g (ConstLipschitzH z) = ConstLipschitzH z := by
  unfold gAct
  unfold ConstLipschitzH
  ext x
  simp [DFunLike.coe]

#synth Module ℝ (LipschitzH)
#synth AddCommGroup (LipschitzH)

abbrev W := (LipschitzH) ⧸ ConstF

#synth Module ℝ (W)

def gActW (g: G): W → W := Quotient.lift (fun f => Submodule.Quotient.mk (gAct g f)) (by
  intro f h hfh
  simp
  rw [Submodule.Quotient.eq']
  replace hfh := ConstF.quotientRel_def.mp hfh
  dsimp [gAct]
  simp [HAdd.hAdd]
  dsimp [Add.add]
  simp [ConstF] at hfh
  obtain ⟨z, hz⟩ := hfh
  simp [ConstLipschitzH] at hz
  simp [ConstF]
  simp [ConstLipschitzH]
  use -z
  ext a
  apply_fun LipschitzH.toFun at hz
  have app_eq := congrFun hz (a * g)
  simp at app_eq
  rw [app_eq]
  simp
  rw [sub_eq_add_neg]
  rw [add_comm]
)



-- Defintion 3.14 from Vikman
-- We offset by one to avoid the need to carry around a '0 < n' hypothesis everywgere
noncomputable def f_n (n: ℕ) (g: G): ℝ := ((1: ℝ) / ((n + 1): ℝ)) * ∑ m: Fin (n + 1), muConv  (m.val) g


end GeneratesNS
