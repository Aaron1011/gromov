module

public import Mathlib
public import Gromov.ThreeTwoGenerates

/-!
# Polynomial growth of the kernel, and growth exponent zero

`three_two_kernel_poly_growth`, and that a group of growth exponent zero is finite.
-/

public section

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

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

omit hGS in
structure GeneratesWithParam (G: Type*) [Group G] [DecidableEq G] where
  S: Finset G
  hS: Nonempty S
  generates : ((closure (S : Set G) : Set G) = ⊤)
  -- This should be fine, since the growth rate doesn't depend on the generating set
  one_mem: (1 : G) ∈ S
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S
  g_infinite: Infinite G

lemma one_mem_S  {G: Type*} [Group G] [DecidableEq G] {n: ℕ} (data: Theorem3_1_Input G) (hGS: GeneratesWithParam data.G') (γ: Additive data.G') (hγ: data.φ γ = 1): 0 ∈ S_n_ker_phi hGS.S data.φ γ hγ n := by
  simp [S_n_ker_phi]


-- The generating set of `ker φ` used below, shared between the `new_g_growth`
-- hypothesis and the `S` field so that `g_growth := new_g_growth` is definitionally
-- trivial (avoids an expensive `whnf` on the two separately-elaborated `Finset`s).
omit hGS in
@[expose]
noncomputable def ker_S {G: Type*} [Group G] [DecidableEq G] (data: Theorem3_1_Input G)
    (hGS: GeneratesWithParam data.G') (γ: data.G') (hγ: data.φ γ = 1) (n: ℕ) :
    Finset (Multiplicative data.φ.ker) :=
  (Finset.image Additive.toMul (S_n_ker_phi hGS.S data.φ γ hγ n)) ∪
    (Finset.image Additive.toMul ((S_n_ker_phi hGS.S data.φ γ hγ n)))⁻¹

-- TODO - figure out how to make this a 'let' without adding it to typeclass search
omit hGS in
@[expose]
noncomputable def ker_generates {n: ℕ} {G: Type*} [Group G] [DecidableEq G] (data: Theorem3_1_Input G) (hGS: GeneratesWithParam data.G') (γ: data.G') (hγ: data.φ γ = 1)
  (ker_infinite: Infinite (Multiplicative data.φ.ker))
  (ker_generates: AddSubgroup.closure (Additive.ofMul '' (three_two_S_n hGS.S data.φ γ (n))) = data.φ.ker)
  ( new_g_growth: HasPolynomialGrowth (ker_S data hGS γ hγ n))
  : Generates := {
  G := (Multiplicative data.φ.ker)
  g_group := by infer_instance
  g_eq := by infer_instance
  S := ker_S data hGS γ hγ n
  hS := by
    use 1
    simp only [ker_S]
    simp
    exact one_mem_S data hGS γ hγ
  generates := by
    simp only [ker_S]
    simp
    rw [Subgroup.closure_union]
    conv =>
      arg 1
      arg 1
      equals ⊤ =>

        let f := (AddSubgroup.subtype data.φ.ker).toMultiplicative
        ext a
        simp
        rw [AddSubgroup.ext_iff] at ker_generates
        specialize ker_generates a.val
        have foo := ker_generates.mpr a.prop
        conv at foo =>
          arg 2
          equals Additive.ofMul a.val => rfl

        apply (AddSubgroup.mem_toSubgroup' _ _).mpr at foo
        rw [AddSubgroup.toSubgroup'_closure] at foo
        simp at foo
        unfold S_n_ker_phi
        simp
        first
          | erw [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
          | rw [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
          | simp only [Finset.coe_insert, Set.image_insert_eq, toMul_zero, Subgroup.closure_insert_one]
        rw [← Subgroup.mem_map_iff_mem (f := f)]
        .
          simp only [f, Subgroup.subtype_apply]
          rw [MonoidHom.map_closure]
          simp
          conv =>
            arg 2
            equals a.val => rfl
          conv =>
            arg 1
            arg 1
            equals ((three_two_S_n hGS.S data.φ γ n : Finset ↥data.G') : Set ↥data.G') =>
              ext b
              constructor
              · intro hb
                obtain ⟨c, hc, rfl⟩ := hb
                obtain ⟨d, hd, rfl⟩ := hc
                obtain ⟨y, rfl⟩ := hd
                exact y.2
              · intro hb
                have hbk : b ∈ three_two_S_n hGS.S data.φ γ n := by simpa using hb
                exact ⟨_, ⟨_, ⟨⟨b, hbk⟩, rfl⟩, rfl⟩, rfl⟩
          exact foo
        . simp [f]
          intro x y hxy
          simpa using hxy
    simp
  one_mem := by
    apply Finset.mem_union_left
    rw [Finset.mem_image]
    use 0
    simp
    -- TODO - figure out wht 'apply one_mem_S' is slow
    exact one_mem_S data hGS γ hγ

  has_inv := by
    intro g hg
    simp only [ker_S] at hg ⊢
    simp at hg
    simp
    rw [or_comm]
    exact hg
  g_infinite := by
    exact ker_infinite
  g_growth := by convert new_g_growth using 2
}


lemma three_two_kernel_poly_growth  (d: ℕ) (hd: d >= 1) (n: ℕ) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1)
 : HasPolynomialGrowthD (G := Multiplicative φ.ker) (d - 1) (S := (S_n_ker_phi S φ γ hγ n) ∪ (S_n_ker_phi S φ γ hγ n)⁻¹) := by

  -- The set S_n, viewed a subset of ker φ


  obtain ⟨a, ha⟩ := hG

  by_cases a_eq_zero: a = 0
  .
    simp [a_eq_zero] at ha
    specialize ha 1 (by simp)
    simp at ha
    have s_nonempty := hGS.one_mem
    grind


  unfold HasPolynomialGrowthD


  have S_n_poly := poly_growth_equiv a d (by omega) S ((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1}) S_eq_Sinv hGS.one_mem (by simpa using hGS.generates) ha
  obtain ⟨b, hb, ker_poly⟩ := S_n_poly


  use b * (2 ^ d)

  intro r hr
  specialize ker_poly (2 * r) (by omega)


  let mul_by_i := fun (g: G) (i: Fin r) => g * (γ ^ i.val)
  have new_phi_gamma: φ (Additive.ofMul γ) = 1 := hγ
  have card_mul_range (g: G): #(Finset.image (mul_by_i g) Finset.univ) = r := by
    rw [Finset.card_image_of_injOn]
    . simp
    .

      intro j _ k _ mul_eq
      simp [mul_by_i] at mul_eq
      apply_fun φ ∘ (Additive.ofMul) at mul_eq
      simp [new_phi_gamma] at mul_eq
      rw [Fin.ext_iff]
      exact mul_eq

  have card_union: #((((((S_n_ker_phi S φ γ hγ n) ∪ (-(S_n_ker_phi S φ γ hγ n))).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) = r * #(r • ((S_n_ker_phi S φ γ hγ n) ∪ -((S_n_ker_phi S φ γ hγ n)))) := by
    rw [Finset.card_biUnion]
    .
      simp_rw [card_mul_range]
      simp
      rw [mul_comm]
      conv =>
        lhs
        arg 2
        arg 1
        equals r • ((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)) =>
          ext a
          rw [Finset.mem_image]
          simp_rw [Finset.mem_pow]
          refine Iff.trans ?_ Finset.mem_nsmul.symm
          refine ⟨?_, ?_⟩
          . intro h
            obtain ⟨b, ⟨f, hf⟩, b_eq_a⟩ := h
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image] at f_prop
              obtain ⟨g, g_mem, hg⟩ := f_prop
              rw [← hg]
              exact g_mem
            )⟩)
            rw [← b_eq_a]
            rw [← hf]
            rfl
          . intro h
            obtain ⟨f, hf⟩ := h
            use a
            refine ⟨?_, rfl⟩
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image]
              use (f i).val
              refine ⟨f_prop, ?_⟩
              rfl
            )⟩)
            rw [← hf]
            rfl


    .
      intro a ha b hb hab x h_first h_second
      simp at h_first
      simp at h_second
      simp

      by_contra!
      obtain ⟨p, hp⟩ := this
      have orig_h_first := h_first hp
      have orig_h_second := h_second hp
      specialize h_first hp
      specialize h_second hp

      simp at h_first
      simp at h_second

      obtain ⟨y, hy⟩ := h_first
      obtain ⟨z, hz⟩ := h_second

      have orig_hy := hy
      have orig_hz := hz

      rw [← hz] at hy
      simp [mul_by_i] at hy
      apply_fun φ ∘ (Additive.ofMul) at hy
      simp [new_phi_gamma] at hy

      have a_ker: a.val ∈ φ.ker := by
        simp

      have b_ker: b.val ∈ φ.ker := by
        simp

      rw [AddMonoidHom.mem_ker] at a_ker
      rw [AddMonoidHom.mem_ker] at b_ker
      simp [ofMul] at hy
      simp [a_ker, b_ker] at hy

      rw [← Fin.ext_iff] at hy
      rw [hy] at orig_hy
      rw [← orig_hy] at orig_hz
      simp [mul_by_i] at orig_hz
      rw [eq_comm] at orig_hz
      contradiction


  have card_union_le: #((((((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) ≤ #(((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1}) ^ (2 * r)) := by
    grw [Finset.card_le_card]
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨s, s_mem, a_mem⟩ := ha
    rw [Finset.mem_image] at a_mem
    obtain ⟨k, _, hk⟩ := a_mem
    simp [mul_by_i] at hk
    rw [← hk]
    rw [two_mul]
    rw [pow_add]
    apply Finset.mul_mem_mul
    .
      unfold S_n_ker_phi at s_mem

      rw [Finset.mem_image] at s_mem
      obtain ⟨z, z_mem, hz⟩ := s_mem
      rw [← hz]

      rw [Finset.mem_pow] at z_mem
      obtain ⟨f, hf⟩ := z_mem
      rw [Finset.mem_pow]
      use (fun i => ⟨(f i).val.val, (by
        have f_prop := (f i).property
        rw [Finset.mem_image] at f_prop
        obtain ⟨g, g_mem, hg⟩ := f_prop
        rw [← hg]
        simp at g_mem
        cases g_mem
        .
          rename_i g_eq_zero
          apply Finset.mem_union_right
          rw [Finset.mem_singleton, g_eq_zero]
          first | rfl | simp
        . rename_i g_eq_nonzero
          cases g_eq_nonzero
          . rename_i left
            obtain ⟨z, z_mem, hz⟩ := left
            rw [← hz]
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            exact z_mem
          .
            rename_i right
            obtain ⟨z, z_mem, hz⟩ := right
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_right
            simp
            conv =>
              arg 2
              equals (-g).val =>
                rfl
            rw [← hz]
            exact z_mem
      )⟩)
      rw [← hf, ofMul_list_prod, List.map_ofFn]
      first
        | (erw [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
        | (rw [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
        | (simp only [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
    .


      have gamma_r_subset: ({γ, 1} : Finset G)^r ⊆ ((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1})^r := by
        apply Finset.pow_subset_pow
        . grind
        . grind
        . simp

      have gamma_subset: ({γ, 1} : Finset G)^k.val ⊆ ({γ, 1} : Finset G)^r := by
        apply Finset.pow_subset_pow
        . simp
        . simp
        . simp


      have gamma_mem_self: γ^k.val ∈ ({γ, 1} : Finset G)^k.val := by
        apply Finset.pow_mem_pow
        simp

      grind


  rw [card_union] at card_union_le
  grw [ker_poly] at card_union_le
  rw [mul_pow] at card_union_le
  rw [← mul_assoc] at card_union_le
  rw [mul_comm] at card_union_le
  rw [← Nat.le_div_iff_mul_le] at card_union_le
  .
    rw [Nat.mul_div_assoc] at card_union_le
    .
      nth_rw 3 [← pow_one (a := r)] at card_union_le
      rw [Nat.pow_div] at card_union_le
      .
        -- TODO - get rid of this obnoxious  Additive/Multiplicative defeq abuse
        conv =>
          lhs
          arg 1
          equals r • ((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)) =>
            ext a
            rw [Finset.mem_pow]
            -- TODO - why do we need explicit args here
            refine Iff.trans ?_ Finset.mem_nsmul.symm
            refine ⟨?_, ?_⟩
            .
              intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
            . intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
        exact card_union_le
      . omega
      . omega

    .
      nth_rw 1 [← pow_one (a := r)]
      apply Nat.pow_dvd_pow
      omega
  . omega

#print axioms three_two_kernel_poly_growth


omit hGS in
lemma set_smul_eq_mul {G: Type*} [Group G] (g: G) (A: Set G): g • A = {g} * A := by
  ext a
  rw [Set.mem_smul_set]
  rw [Set.mem_mul]
  simp

/-- Degree-zero polynomial growth forces `G` to be finite: the balls `S ^ n` have bounded
cardinality, so some `S ^ y` already contains all of `Subgroup.closure S = ⊤`.

Extracted from the `zero` case of `main_gromov_theorem`, which now calls it. -/
lemma finite_of_growth_zero (h: HasPolynomialGrowthD S 0): Finite G := by
    simp [HasPolynomialGrowthD] at h
    obtain ⟨a, ha⟩ := h

    have S_closure := hGS.generates

    let pow_cards := Set.range (fun (n: ℕ) => #(S ^ n))
    -- TODO - this can probably be much simpler
    have pow_cards_bounded: ∃ y, ∀ n ∈ pow_cards, n ≤ y := by
      use a
      intro n hn
      simp [pow_cards] at hn
      obtain ⟨y, hy⟩ := hn
      rw [← hy]

      by_cases y_eq_zero: y = 0
      . simp [y_eq_zero]

        -- TODO - deduplicate this
        have a_ne_zero: a ≠ 0 := by
          by_contra!
          rw [this] at ha
          have hg_one := ha 1 (by omega)
          simp at hg_one
          have one_mem := hGS.one_mem
          rw [hg_one] at one_mem
          simp at one_mem

        omega
      . by_cases y_eq_one: y = 1
        .
          simp [y_eq_one]
          have card_mono := Finset.card_pow_mono (s := S) (m := 1) (n := 2) (by simp) (by simp)
          have card_two_le := ha 2 (by simp)
          simp at card_mono
          linarith
        .
          exact ha y (by omega)


    classical
    have max_card_mem := Nat.sSup_mem (s := pow_cards) ?_ ?_
    . simp [pow_cards] at max_card_mem
      obtain ⟨y, hy⟩ := max_card_mem


      have all_closure_mem: ∀ s ∈ (Subgroup.closure S), s ∈ (S ^ y) := by
        intro s hs
        induction hs using Subgroup.closure_induction with
        | one =>
          apply Finset.one_mem_pow
          exact Generates.one_mem
        | mem x hx =>
          by_cases y_eq_zero: y = 0
          .
            rw [y_eq_zero]
            rw [y_eq_zero] at hy
            simp at hy
            simp
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have S_one_le := find_le #(S) ?_
            .
              simp [pow_cards] at S_one_le
              rw [← hy] at S_one_le
              rw [Finset.card_le_one] at S_one_le
              have one_mem: 1 ∈ S := by exact Generates.one_mem
              have x_eq := S_one_le 1 one_mem x hx
              apply x_eq.symm
            . simp [pow_cards]
              use 1
              simp
          .
            have pow_mono := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (n := y) (m := 1) (by omega)
            simp at pow_mono
            apply pow_mono hx
        | mul a b a_mem_closure b_mem_closure a_mem_pow b_mem_pow =>
          by_cases y_eq_zero: y = 0
          .
            simp [y_eq_zero]
            simp [y_eq_zero] at a_mem_pow b_mem_pow
            simp [a_mem_pow, b_mem_pow]
          .
            by_contra!
            have a_b_mem_two: a * b ∈ (S ^ (y * 2)) := by
              have mem_mul := Finset.mul_mem_mul a_mem_pow b_mem_pow
              rw [← pow_two] at mem_mul
              rw [← pow_mul] at mem_mul
              exact mem_mul

            have subset := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (m := y) (n := (y * 2)) (by omega)

            have strict_subset : (S ^ y) ⊂ (S ^ (y * 2)) := by
              rw [Finset.ssubset_iff_of_subset subset]
              use (a * b)

            have card_lt: #(S ^ y) < #(S ^ (y * 2)) := by
              exact Finset.card_lt_card strict_subset


            rw [hy] at card_lt
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have reverse_le := find_le #(S ^ (y * 2)) ?_
            .
              simp [pow_cards] at reverse_le
              linarith
            . simp [pow_cards]
        | inv a ha a_mem_pow =>
          rw [← Finset.mem_inv']
          rw [← inv_pow]
          rw [← S_eq_Sinv]
          exact a_mem_pow

      have G_finite: Finite G := by
        rw [← Set.finite_univ_iff]
        have univ_eq: (Set.univ : Set G) = (S ^ y) := by
          simp at S_closure

          apply_fun (fun y => y.carrier) at S_closure
          conv at S_closure =>
            rhs
            equals Set.univ =>
              exact rfl

          rw [← S_closure]
          ext a
          refine ⟨?_, ?_⟩
          . intro ha
            simp at ha
            rw [← Finset.coe_pow]
            exact all_closure_mem a ha
          . intro ha
            simp
            exact mem_closure a

        rw [univ_eq]
        rw [← Finset.coe_pow]
        exact Finset.finite_toSet (S ^ y)
      exact G_finite
    .
      simp [pow_cards]
      apply Set.range_nonempty
    .
      rw [bddAbove_def]
      exact pow_cards_bounded

/-- The constant in a polynomial growth bound is positive: `a = 0` would force `S ^ 1 = ∅`,
contradicting `1 ∈ S`. -/
lemma growth_const_pos {d a : ℕ} (ha: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d): 0 < a := by
  by_contra!
  simp at this
  rw [this] at ha
  have hg_one := ha 1 (by omega)
  simp at hg_one
  have one_mem := hGS.one_mem
  rw [hg_one] at one_mem
  simp at one_mem

/-- The exponent in a polynomial growth bound is positive, since `G` is infinite. -/
lemma growth_exponent_pos {d : ℕ} (h: HasPolynomialGrowthD S d): 0 < d := by
  by_contra!
  simp at this
  subst this
  have := finite_of_growth_zero h
  have := hGS.g_infinite
  exact (not_finite G)

-- TODO - add an explicit top-level universe parameter to avoid this 'omit hGS' hack

end GeneratesNS
