module

public import Mathlib

/-!
# Products of one-sided limits

Staging ground for `Filter.TendstoNhdsWithinIoi.mul`, the two-function analogue of the existing
`Filter.TendstoNhdsWithinIoi.const_mul` / `Filter.TendstoNhdsWithinIoi.mul_const` lemmas in
`Mathlib.Topology.Algebra.Monoid`. Intended to be upstreamed into that file later.
-/

public section

open Filter Topology Set

/-- If `f` and `g` tend to `c` and `d` respectively from the right, and both limit points are
nonnegative, then `f * g` tends to `c * d` from the right. This is the two-function analogue of
`Filter.TendstoNhdsWithinIoi.const_mul` and `Filter.TendstoNhdsWithinIoi.mul_const`; since neither
factor is constant it requires joint continuity of multiplication (`ContinuousMul`) rather than
merely `SeparatelyContinuousMul`. -/
theorem Filter.TendstoNhdsWithinIoi.mul {α 𝕜 : Type*} [MulZeroClass 𝕜] [Preorder 𝕜]
    [TopologicalSpace 𝕜] [ContinuousMul 𝕜] [PosMulStrictMono 𝕜] [MulPosMono 𝕜] {l : Filter α}
    {f g : α → 𝕜} {c d : 𝕜} (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : Tendsto f l (𝓝[>] c))
    (hg : Tendsto g l (𝓝[>] d)) : Tendsto (fun a => f a * g a) l (𝓝[>] (c * d)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin hf).mul (tendsto_nhds_of_tendsto_nhdsWithin hg)) <|
    ((tendsto_nhdsWithin_iff.mp hf).2.and (tendsto_nhdsWithin_iff.mp hg).2).mono
      fun _ ⟨hfa, hga⟩ => by rw [Set.mem_Ioi] at *; exact mul_lt_mul'' hfa hga hc hd

/-- A `squeeze_zero` landing in `𝓝[>] 0` rather than `𝓝 0`: if `0 < f ≤ g` eventually and `g`
tends to `0`, then `f` tends to `0` from the right. Companion to `squeeze_zero'` (which only
concludes `Tendsto f t₀ (𝓝 0)`). -/
theorem squeeze_zero_nhdsGT {α : Type*} {f g : α → ℝ} {t₀ : Filter α}
    (hf : ∀ᶠ t in t₀, 0 < f t) (hft : ∀ᶠ t in t₀, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (squeeze_zero' (hf.mono fun _ h => h.le) hft g0) (hf.mono fun _ h => Set.mem_Ioi.mpr h)
