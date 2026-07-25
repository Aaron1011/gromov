import Mathlib

/-!
# Right coset covers by a constant subgroup

Right-handed analogues of the `leftCoset_cover_const` results in
`Mathlib/GroupTheory/CosetCover.lean`, where they are intended to go.

Upstreaming status: ready modulo style (line lengths, `simp` squeezing).
-/

namespace Subgroup

variable {G : Type*} [Group G]

section rightCoset_cover_const

variable {ι : Type*} {s : Finset ι} {H : Subgroup G} {g : ι → G}

@[to_additive]
theorem rightCoset_cover_const_iff_surjOn :
    ⋃ i ∈ s, (MulOpposite.op (g i)) • (H : Set G) = Set.univ ↔
      Set.SurjOn ((fun a => Quotient.mk _ (g a)) :
        ι → (Quotient (QuotientGroup.rightRel H))) s Set.univ := by
  -- QuotientGroup.quotientRightRelEquivQuotientLeftRel
  simp [Set.eq_univ_iff_forall, mem_rightCoset_iff, Set.SurjOn,
    Quotient.forall, Quotient.eq, QuotientGroup.rightRel_apply]

variable (hcovers : ⋃ i ∈ s, (MulOpposite.op (g i)) • (H : Set G) = Set.univ)
include hcovers

@[to_additive]
theorem finiteIndex_of_rightCoset_cover_const : H.FiniteIndex := by
  simp_rw [rightCoset_cover_const_iff_surjOn] at hcovers
  have := Set.finite_univ_iff.mp <| Set.Finite.of_surjOn _ hcovers s.finite_toSet
  rw [Equiv.finite_iff (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)] at this
  exact H.finiteIndex_of_finite_quotient

end rightCoset_cover_const

end Subgroup
