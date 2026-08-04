module

public import Mathlib
public import Gromov.Defs.WordMetric

/-!
# Topology, measurability and Haar measure on `G`

`G` is discrete, so its Haar measure is the counting measure. This file records the Borel and
measure-space instances and the resulting a.e.-triviality lemmas.
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

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

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
  rw [discreteTopology_iff_isOpen_singleton]
  exact singleton_open

instance : ContinuousMul G where
  continuous_mul := continuous_of_discreteTopology

instance : ContinuousInv G where
  continuous_inv := continuous_of_discreteTopology

instance: IsTopologicalGroup G where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology


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


omit hGS in
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

end GeneratesNS
