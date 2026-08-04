import Mathlib
import Gromov.GrowthZero

/-!
# Gromov's theorem on groups of polynomial growth

`theorem_3_1`, the inductive step, and the main result `main_gromov_theorem`: a finitely
generated group of polynomial growth is virtually nilpotent.
-/

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

set_option maxHeartbeats 2500000 in
omit hGS in
lemma theorem_3_1.{u} [hGS: Generates.{u}] (data: Theorem3_1_Input G) (d: ℕ) (hd: 1 ≤ d) (h_growth: HasPolynomialGrowthD S d)
(inductive_gromov: ∀ (Q_generates: Generates.{u}),(Q_growth : (HasPolynomialGrowthD (Q_generates.S)) (d - 1)) → Group.IsVirtuallyNilpotent Q_generates.G)
: Group.IsVirtuallyNilpotent G := by
  letI inst_dec_G : DecidableEq G := G_dec_eq

  have G'_finite_index := data.finite_index
  have G'_fg: Group.FG data.G' := by
    apply Subgroup.fg_of_index_ne_zero

  have G'_fg_out : ∃ T : Finset ↥data.G', Subgroup.closure (T : Set ↥data.G') = ⊤ := G'_fg.out

  -- A symmetric generating set for G'
  let S_G' := G'_fg_out.choose ∪  G'_fg_out.choose⁻¹ ∪ {1}

  -- TODO - factor out this proof that a subgroup has polynomial growth
  have G'_poly: HasPolynomialGrowthD (G := data.G') S_G' d := by
    unfold HasPolynomialGrowthD
    obtain ⟨a, ha⟩ := h_growth

    have a_pos: 0 < a := by
      by_contra!
      simp at this
      simp [this] at ha
      specialize ha 1 (by simp)
      simp at ha
      have s_one := hGS.one_mem
      grind

    have my_equiv := poly_growth_equiv a d a_pos S (Finset.image Subtype.val S_G')
      S_eq_Sinv hGS.one_mem (by simpa using hGS.generates) ha

    obtain ⟨b, hb, poly_growth_G'⟩ := my_equiv

    use b
    intro n hn
    rw [← Finset.card_image_of_injective (f := data.G'.subtype)]
    .
      rw [Finset.image_pow]
      exact poly_growth_G' n hn
    . simp



  -- NOTE: this IS registered as a local instance, and deliberately shadows `hGS` for the
  -- unqualified `G`/`S` below (most of the proof works inside `data.G'`).  Where the ambient
  -- group is meant instead, write `hGS.S` / `hGS.G` explicitly.
  let new_generates: Generates := {
    G := data.G'
    g_group := by infer_instance
    g_eq := by infer_instance
    S := S_G'
    hS := by
      simp [S_G']
    generates := by
      simp [S_G']
      rw [Subgroup.closure_union]
      rw [G'_fg_out.choose_spec]
      simp
    one_mem := by
      simp [S_G']
    has_inv := by
      intro g hg
      unfold S_G'
      unfold S_G' at hg
      rw [← Finset.mem_inv']
      simp
      simp at hg
      grind
    g_infinite := by
      have index_ne := G'_finite_index.index_ne_zero
      simp [Subgroup.index] at index_ne
      -- TODO - generalize and upstream this to mathlib
      by_contra!
      have finite_iff := Subgroup.finite_iff_finite_and_finiteIndex data.G'
      simp [this, G'_finite_index] at finite_iff
      have G_infinite := hGS.g_infinite
      rw [← not_finite_iff_infinite] at G_infinite
      contradiction
    g_growth := by
      use d
  }


  obtain ⟨γ, hγ⟩ := data.hφ 1
  obtain ⟨n, generates_with_n⟩ := three_two_S_n_generates  (hGS := new_generates) d hd G'_poly data.φ γ hγ
  have kernel_poly := three_two_kernel_poly_growth (hGS := new_generates) d hd n G'_poly data.φ γ hγ
  have kernel_fg := three_two_ker_fg (hGS := new_generates) d hd G'_poly data.φ data.hφ


  rw [← AddGroup.fg_iff_addSubgroup_fg] at kernel_fg
  rw [AddGroup.fg_iff_mul_fg] at kernel_fg


  let orig_ker_phi := (S_n_ker_phi S data.φ γ hγ 1)

  let new_generate_data: GeneratesWithParam data.G' := {
    S := new_generates.S
    hS := new_generates.hS
    generates := new_generates.generates
    one_mem := new_generates.one_mem
    has_inv := new_generates.has_inv
    g_infinite := new_generates.g_infinite
  }

  have kernel_virtually_nilpotent: Group.IsVirtuallyNilpotent (Multiplicative data.φ.ker) := by
    by_cases kernel_finite: Finite (Multiplicative data.φ.ker)
    .
      rw [Group.IsVirtuallyNilpotent]
      use ⊥
      refine ⟨?_, ?_⟩
      . exact Group.isNilpotent_of_subsingleton
        -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
      . infer_instance
    .
      rw [not_finite_iff_infinite] at kernel_finite

      have new_kernel_poly := kernel_poly
      -- TODO - get rid of defeq abuse
      conv at new_kernel_poly =>
        arg 1
        equals (((Finset.image Additive.toMul (S_n_ker_phi S data.φ γ hγ n)) ∪ (Inv.inv (α := Finset (Multiplicative _))) (Finset.image Additive.toMul ((S_n_ker_phi S data.φ γ hγ n))))) =>
          ext a
          refine ⟨?_, ?_⟩
          . intro ha
            rw [Finset.mem_union]
            rw [Finset.mem_image]
            simp at ha
            cases ha
            . rename_i left
              left
              use a
              refine ⟨left, rfl⟩
            . rename_i right
              right
              rw [Finset.mem_inv']
              rw [Finset.mem_image]
              use Additive.ofMul a⁻¹
              refine ⟨right, rfl⟩
          .
            intro ha
            rw [Finset.mem_union] at ha
            rw [Finset.mem_union]
            cases ha
            . rename_i left
              simp at left
              left
              exact left
            . rename_i right
              rw [Finset.mem_inv'] at right
              rw [Finset.mem_image] at right
              obtain ⟨b, hb, a_eq⟩ := right
              right
              rw [Finset.mem_inv']
              rw [← a_eq]
              exact hb


      let foo := ker_generates data new_generate_data γ hγ kernel_finite (by
        exact generates_with_n
      ) (by
        use (d - 1)
        simp only [ker_S]
        exact new_kernel_poly
      )
      let bar := inductive_gromov foo new_kernel_poly
      apply inductive_gromov foo
      exact new_kernel_poly
  .
    obtain ⟨pre_N, pre_N_nilpotent, pre_N_finiteindex⟩ := kernel_virtually_nilpotent
    let N := pre_N.normalCore
    have N_normal: N.Normal := Subgroup.normalCore_normal pre_N
    have N_finite_index: N.FiniteIndex := Subgroup.finiteIndex_normalCore pre_N
    have N_nilpotent: Group.IsNilpotent N := by
      have normalCore_iso := Subgroup.subgroupOfEquivOfLe (Subgroup.normalCore_le pre_N)
      unfold N
      rw [← Group.isNilpotent_congr normalCore_iso]
      apply Subgroup.isNilpotent


    rw [Subgroup.finiteIndex_iff] at N_finite_index
    let N' := Subgroup.closure (Set.range (fun (a: Multiplicative data.φ.ker) => a ^ N.index))


    let new_N'_map : _ →* _ := {
      toFun := fun (g: (Multiplicative ↥data.φ.ker)) => Additive.toMul (data.φ.ker.subtype g)
      map_one' := rfl
      map_mul' := by
        intro x y
        rfl
    }


    let new_N': Subgroup (data.G') := Subgroup.map new_N'_map N'

    have N'_le_N: N' ≤ N := by
      unfold N'
      simp
      intro n hn
      rw [Set.mem_range] at hn
      obtain ⟨a, ha⟩ := hn
      rw [← ha]
      apply Subgroup.pow_index_mem

    have N'_nilpotent: Group.IsNilpotent N' := by
      rw [← Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe N'_le_N)]
      -- TODO - why isn't 'N_nilpotent' found by typeclass synthesis?
      apply isNilpotent (N'.subgroupOf N) (hG := N_nilpotent)


    have N'_char: Subgroup.Characteristic N' := by
      rw [Subgroup.characteristic_iff_map_eq]
      intro f
      unfold N'
      simp
      rw [MonoidHom.map_closure]
      simp
      congr
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        rw [Set.mem_image] at ha
        obtain ⟨b, hb, ab_eq⟩ := ha
        rw [Set.mem_range] at hb
        obtain ⟨c, hc⟩ := hb
        rw [← hc] at ab_eq
        simp at ab_eq
        grind
      . intro ha
        rw [Set.mem_range] at ha
        obtain ⟨b, hb⟩ := ha
        rw [← hb]
        rw [Set.mem_image]
        use f⁻¹ (b ^ N.index)
        refine ⟨?_, by simp⟩
        simp

    have N'_normal: N'.Normal := by
      infer_instance


    have N'_index: N'.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff]
      rw [← Subgroup.relIndex_mul_index N'_le_N]
      simp
      refine ⟨?_, ?_⟩
      .
        unfold Subgroup.relIndex
        rw [← ne_eq, ← Subgroup.finiteIndex_iff]
        rw [Subgroup.finiteIndex_iff_finite_quotient]
        -- TODO - why do we need this explicit instance?
        have foo : Group.IsNilpotent (↥N ⧸ N'.subgroupOf N) := by
          infer_instance
        apply finite_of_nilpotent_fg_order
        intro n
        rw [isOfFinOrder_iff_pow_eq_one]
        use N.index
        refine ⟨by omega, ?_⟩
        -- TODO - there should be a much simpler proof
        let a := n.out
        rw [← QuotientGroup.out_eq' (a := n)]
        conv =>
          lhs
          arg 1
          equals QuotientGroup.mk' _ (n).out =>
            rfl

        rw [← MonoidHom.map_pow]
        simp only [QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq_one_iff]
        rw [Subgroup.mem_subgroupOf]
        unfold N'
        apply Subgroup.mem_closure_of_mem
        rw [Set.mem_range]
        use n.out
        simp
      .
        exact N_finite_index


    have N'_fg: Subgroup.FG N' := by
      rw [← Group.fg_iff_subgroup_fg]
      apply Subgroup.fg_of_index_ne_zero


    let gamma_conj_hom: data.φ.ker →+ data.φ.ker := {
      toFun := fun a => ⟨γ + a + (-γ), (by
        simp
        exact a.prop
      )⟩
      map_zero' := by simp
      map_add' := by
        intro a b
        simp
    }
    let gamma_conj_ker: AddAut (data.φ.ker) := AddEquiv.ofBijective gamma_conj_hom (by
      unfold Function.Bijective
      refine ⟨?_, ?_⟩
      . intro a b hab
        simp [gamma_conj_hom] at hab
        exact hab
      .
        intro b
        use ⟨(-γ) + b + γ, by (
          simp
          exact b.prop
        )⟩
        simp [gamma_conj_hom]
        simp_rw [← add_assoc]
        simp
    )
    let gamma_conj_ker_mul := AddEquiv.toMultiplicative gamma_conj_ker
    let gamma_conj_N' := MulAut.characteristic N' gamma_conj_ker_mul

    -- The underlying element of `data.G'` of an element of `N'`, with every `Additive` /
    -- `Multiplicative` conversion spelled out instead of relying on definitional unfolding:
    -- `↥N' → Multiplicative ↥data.φ.ker → ↥data.φ.ker → Additive ↥data.G' → ↥data.G'`.
    let N'_val : ↥N' →* ↥data.G' :=
      (AddMonoidHom.toMultiplicativeLeft data.φ.ker.subtype).comp N'.subtype

    have gamma_conj_ker_apply: ∀ a: ↥data.φ.ker,
        data.φ.ker.subtype (gamma_conj_ker a) = γ + data.φ.ker.subtype a + -γ := by
      intro a
      rw [show gamma_conj_ker a = gamma_conj_hom a from AddEquiv.ofBijective_apply _ _ _]
      simp [gamma_conj_hom]

    have gamma_conj_step: ∀ g: ↥N',
        N'_val (gamma_conj_N' g) = Additive.toMul γ * N'_val g * (Additive.toMul γ)⁻¹ := by
      intro g
      simp only [N'_val, gamma_conj_N', gamma_conj_ker_mul, MonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.coe_toMultiplicativeLeft, Subgroup.coe_subtype,
        MulAut.characteristic_apply_apply_coe, AddEquiv.toMultiplicative_apply_apply,
        AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.toMultiplicative_apply_apply,
        AddMonoidHom.coe_coe, toAdd_ofAdd, gamma_conj_ker_apply, toMul_add, toMul_neg]

    have gamma_conj_iter_val: ∀ (n: ℕ), ∀ g: ↥N',
        N'_val (gamma_conj_N'^[n] g)
          = Additive.toMul γ ^ n * N'_val g * (Additive.toMul γ ^ n)⁻¹ := by
      intro n
      induction n with
      | zero =>
        intro g
        simp only [Function.iterate_zero_apply, pow_zero, one_mul, inv_one, mul_one]
      | succ n ih =>
        intro g
        rw [Function.iterate_succ_apply', gamma_conj_step, ih]
        group

    -- The two membership proofs needed to write the conjugate `γ^n * g * γ⁻ⁿ` back as an
    -- element of `↥N'`.
    have conj_mem_ker: ∀ (n: ℕ), ∀ g: ↥N',
        Additive.ofMul (Additive.toMul γ ^ n * N'_val g * (Additive.toMul γ ^ n)⁻¹)
          ∈ data.φ.ker := by
      intro n g
      rw [← gamma_conj_iter_val n g]
      exact (Multiplicative.toAdd (N'.subtype (gamma_conj_N'^[n] g))).2

    have conj_val_eq: ∀ (n: ℕ), ∀ g: ↥N',
        (Multiplicative.ofAdd
            (⟨Additive.ofMul (Additive.toMul γ ^ n * N'_val g * (Additive.toMul γ ^ n)⁻¹),
              conj_mem_ker n g⟩ : ↥data.φ.ker))
          = N'.subtype (gamma_conj_N'^[n] g) := by
      intro n g
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd (Multiplicative.toAdd _)
      congr 1
      apply Subtype.ext
      exact congrArg Additive.ofMul (gamma_conj_iter_val n g).symm

    have conj_mem_N': ∀ (n: ℕ), ∀ g: ↥N',
        (Multiplicative.ofAdd
            (⟨Additive.ofMul (Additive.toMul γ ^ n * N'_val g * (Additive.toMul γ ^ n)⁻¹),
              conj_mem_ker n g⟩ : ↥data.φ.ker)) ∈ N' := by
      intro n g
      rw [conj_val_eq n g]
      exact (gamma_conj_N'^[n] g).2

    have gamma_conj_iter: ∀ (n: ℕ), ∀ g: ↥N',
        gamma_conj_N'^[n] g
          = ⟨Multiplicative.ofAdd
              (⟨Additive.ofMul (Additive.toMul γ ^ n * N'_val g * (Additive.toMul γ ^ n)⁻¹),
                conj_mem_ker n g⟩ : ↥data.φ.ker), conj_mem_N' n g⟩ := by
      intro n g
      exact Subtype.ext (conj_val_eq n g).symm

    have gamma_conj_card: ∀ k: ℕ, (0 < k) →  ∀ g, ∃ p q: ℕ, 0 < p ∧ ∀ b: ℕ, 0 < b → ∀ a: ℕ, (0 < a) → (a < b) → ((Finset.image (fun x ↦ (List.map (fun (i: Finset.Ico a b) ↦ (gamma_conj_N')^[k * ↑i] g) x.toList).prod))
        (Finset.Ico a b).attach.powerset).card ≤ p * (b^q) * (b - a)^q := by

      have s_poly := hGS.g_growth
      unfold HasPolynomialGrowth at s_poly
      obtain ⟨q, hq⟩ := s_poly
      unfold HasPolynomialGrowthD at hq
      obtain ⟨p, hp⟩ := hq
      intro k k_pos x


      obtain ⟨x_list, x_prod, x_list_prod⟩ :=
        word_norm_prod_self (hGS := hGS) x.val.toAdd.val.toMul.val
      obtain ⟨gamma_list, gamma_prod, gamma_list_prod⟩ :=
        word_norm_prod_self (hGS := hGS) (Additive.toMul γ).val


      -- `(hGS := hGS)` is required: `new_generates` shadows the ambient instance here,
      -- so a bare `S` would resolve to `new_generates.S`.
      have p_pos: 0 < p := growth_const_pos (hGS := hGS) hp

      have q_pos: 0 < q := growth_exponent_pos (hGS := hGS) ⟨p, hp⟩
      use p * (((max x_list.length gamma_list.length) * (4 * k)) ^ q)
      use q


      have gamma_len_pos: 1 ≤  gamma_list.length := by
        by_contra!
        simp at this
        simp [ProdS, this] at gamma_prod
        have gamma_eq: γ = 0 := by
          have gamma_coe := Subtype.coe_eq_of_eq_mk gamma_prod.symm
          apply_fun (fun a => Additive.ofMul a) at gamma_coe
          rw [ofMul_toMul] at gamma_coe
          exact gamma_coe
        simp [gamma_eq] at hγ

      refine ⟨?_, ?_⟩
      .
        apply mul_pos
        . exact p_pos
        .
          rw [pow_pos_iff]
          .
            positivity
          . grind


      intro b hb
      intro a ha hab

      have mul_nozero: 1 ≤  2 * k * b := by
        rw [mul_assoc]
        apply one_le_mul
        . simp
        . apply one_le_mul
          . grind
          . grind


      grw [← Finset.card_image_of_injOn (f := fun a => a.val.toAdd.val.toMul.val) (by simp)]
      grw [Finset.card_le_card (t := hGS.S^((b - a) * ((max x_list.length gamma_list.length) * (4 * k * b)) ))]
      ·

        grw [hp]
        .
          rw [mul_pow]
          ring
          simp
        .
          simp
          apply one_le_mul
          . grind
          .
            rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]


            positivity
      -- side goal from `card_le_card`: the image is contained in `hGS.S`
      ·
        intro g hg
        simp at hg
        obtain ⟨s, hs, g_eq⟩ := hg
        simp [ProdS] at x_prod
        simp [ProdS] at gamma_prod
        rw [eq_comm] at x_prod
        rw [eq_comm] at gamma_prod
        have gamma_eq := Subtype.coe_eq_of_eq_mk gamma_prod
        apply_fun (fun a => Additive.ofMul a) at gamma_eq
        rw [ofMul_toMul] at gamma_eq

        have x_eq := Subtype.coe_eq_of_eq_mk x_prod
        apply_fun (fun a => Additive.ofMul a) at x_eq
        rw [ofMul_toMul] at x_eq
        have x_eq := Subtype.coe_eq_of_eq_mk x_eq
        apply_fun (fun a => Multiplicative.ofAdd a) at x_eq
        rw [ofAdd_toAdd] at x_eq
        have x_eq := Subtype.coe_eq_of_eq_mk x_eq
        simp_rw [x_eq] at g_eq
        simp_rw [gamma_conj_iter] at g_eq
        simp at g_eq
        simp_rw [gamma_eq] at g_eq
        rw [← g_eq]
        rw [← closed_ball_eq_S_pow (hGS := hGS)]
        simp [-le_sup_iff]
        simp only [dist, WordDist_one]
        norm_cast
        simp_rw [Function.comp_def]
        simp [-le_sup_iff]
        grw [word_norm_list_prod_le (hGS := hGS)]
        rw [List.unattach.eq_def (l := s.toList)]
        nth_rw 2 [List.map_map]
        grw [List.sum_le_sum (g := Function.const _ ((max x_list.length gamma_list.length) * (4 * k * b)))]
        .
          simp [-le_sup_iff]
          grw [Finset.card_le_univ]
          simp
        .
          intro y hy
          simp at hy
          obtain ⟨m, ⟨⟨m_range, m_mem⟩, y_eq⟩⟩ := hy
          rw [← y_eq]
          grw [word_norm_mul_le (hGS := hGS)]
          grw [word_norm_mul_le (hGS := hGS)]
          rw [← word_norm_inv (hGS := hGS)]
          grw [word_norm_pow (hGS := hGS)]
          rw [← gamma_prod, ← gamma_list_prod]
          simp [N'_val]
          rw [← x_prod, ← x_list_prod]
          grw [m_range.2]
          ring
          have four_eq: 4 = (2 + 2) := by norm_num
          rw [four_eq, mul_add]
          apply add_le_add
          . simp
            grw [le_max_right (b := gamma_list.length)]
          . grw [← le_max_left (a := x_list.length)]
            ring
            nlinarith


    obtain ⟨α, m, alpha_nonzero, alpha_is_unipotent_conj⟩ := exists_gamma_n_unipotent_N' (N' := N')  N'_nilpotent N'_fg gamma_conj_N' gamma_conj_card 1 (by simp)
    simp_rw [mul_one] at alpha_is_unipotent_conj

    have alpha_is_unipotent: ∀ g ∈ N', Nat.iterate (fun x => ⁅x, γ.toMul^α⁆) m g.val = 1 := by
      -- One commutator step with `γ^α` is the `N'_val`-image of one step of
      -- `x ↦ x * gamma_conj_N'^[α] x⁻¹`, which is the map `exists_gamma_n_unipotent_N'` iterates.
      have commutator_step: ∀ x: ↥N',
          ⁅N'_val x, Additive.toMul γ ^ α⁆ = N'_val (x * (gamma_conj_N'^[α]) x⁻¹) := by
        intro x
        rw [map_mul, gamma_conj_iter_val α x⁻¹, map_inv, commutatorElement_def]
        group

      have commutator_iterate: ∀ (k: ℕ), ∀ x: ↥N',
          (fun y => ⁅y, Additive.toMul γ ^ α⁆)^[k] (N'_val x)
            = N'_val ((fun y => y * (gamma_conj_N'^[α]) y⁻¹)^[k] x) := by
        intro k
        induction k with
        | zero =>
          intro x
          simp only [Function.iterate_zero_apply]
        | succ k ih =>
          intro x
          simp only [Function.iterate_succ_apply]
          rw [commutator_step x, ih]

      intro g hg
      -- `g.val` in the statement above is `N'_val ⟨g, hg⟩` modulo the `Multiplicative` /
      -- `Additive` type synonyms; this `show` is the one place that identification is used.
      show (fun x => ⁅x, Additive.toMul γ ^ α⁆)^[m] (N'_val ⟨g, hg⟩) = 1
      rw [commutator_iterate m ⟨g, hg⟩, alpha_is_unipotent_conj ⟨g, hg⟩, map_one]

    -- TODO - generalize and upstream to mathlib
    have phi_ker_normal: (AddSubgroup.toSubgroup' data.φ.ker).Normal := by
      have phi_normal: data.φ.ker.Normal := by
        infer_instance
      exact {
        conj_mem := by
          intro a ha g
          have foo := phi_normal.conj_mem a ha g
          exact foo
      }


    haveI : Subgroup.Characteristic N' := N'_char
    have alpha_nilpotent := unipotent_commutator_trivial (G := data.G') (H := data.φ.ker.toSubgroup') (N' := N') (N'_char := N'_char) (N'_nilpotent := by
      exact N'_nilpotent
    ) (γ.toMul^α) (by
      intro hx
      by_contra!

      have gamma_alpha_mem_ker: (γ.toMul^α) ∈ data.φ.ker :=
        Subgroup.map_subtype_le _ hx

      simp at gamma_alpha_mem_ker
      clear * - hγ α gamma_alpha_mem_ker alpha_nonzero
      have gak : data.φ (α • γ) = 0 := gamma_alpha_mem_ker
      rw [AddMonoidHom.map_nsmul, hγ] at gak
      simp at gak
      exact alpha_nonzero gak
    ) m alpha_is_unipotent N'_fg.choose N'_fg.choose_spec

    have map_N'_invariant_gamma {n: ℕ}: ∀ b ∈ Subgroup.closure {γ.toMul^n}, ∀ a ∈ map new_N'_map (Subgroup.closure ↑(Exists.choose N'_fg)), b * a * b⁻¹ ∈ map new_N'_map (Subgroup.closure ↑(Exists.choose N'_fg))  := by
      intro gamma_pow h_gamma_pow n hn
      let conj_aut := MulAut.conjNormal gamma_pow (H := data.φ.ker.toSubgroup')
      have conj_map := N'_char.fixed conj_aut
      rw [Subgroup.ext_iff] at conj_map
      rw [Subgroup.mem_map]

      have conj_mem_ker: gamma_pow * n * gamma_pow⁻¹ ∈ data.φ.ker := by
        rw [Subgroup.mem_map] at hn
        obtain ⟨y, hy, n_eq⟩ := hn
        have hn0 : data.φ (Additive.ofMul n) = 0 := by
          rw [← n_eq]
          exact y.2
        show data.φ (Additive.ofMul gamma_pow + Additive.ofMul n + (-(Additive.ofMul gamma_pow))) = 0
        rw [map_add, map_add, map_neg, hn0]
        abel

      use ⟨gamma_pow * n * gamma_pow⁻¹, conj_mem_ker⟩
      .
        refine ⟨?_, ?_⟩
        .

          rw [Subgroup.mem_map] at hn
          obtain ⟨y, hy, n_eq⟩ := hn
          conv =>
            arg 2
            equals conj_aut y =>
              refine Subtype.ext ?_
              simp [conj_aut]
              simp [← n_eq, new_N'_map]
              rfl
          specialize conj_map y
          rw [Subgroup.mem_comap] at conj_map
          have N'_spec := N'_fg.choose_spec
          rw [N'_spec] at hy
          simp [hy] at conj_map
          rw [N'_spec]
          exact conj_map
        .
          rfl

    have map_N'_invariant_gamma_one := map_N'_invariant_gamma (n := 1)
    simp only [pow_one] at map_N'_invariant_gamma_one

    rw [Group.IsVirtuallyNilpotent]
    rw [Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ (Subgroup.subtype _) (by simp))] at alpha_nilpotent
    -- TODO - this is wrong. We need to use {toMul γ} so that we can prove that it has finite index (G'' is defined using
    -- just gamma, not gamma^alpha)
    use (map data.G'.subtype (Subgroup.closure (↑(Finset.image (⇑(AddSubgroup.toSubgroup' data.φ.ker).subtype) (Exists.choose N'_fg)) ∪ {toMul γ ^ α})))

    refine ⟨?_, ?_⟩
    .
      exact alpha_nilpotent
    .
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map]
      simp
      refine ⟨?_, ?_⟩
      .

        simp_rw [Set.insert_eq]

        have gamma_alpha_le_gamma: (Subgroup.closure ({toMul γ ^ α} ∪ (new_N'_map '' (N'_fg.choose)) )) ≤ (Subgroup.closure ({toMul γ} ∪ (new_N'_map '' (N'_fg.choose)))) := by
          simp
          intro g hg
          rw [Set.insert_eq]
          cases hg
          . rename_i g_eq_gamma
            rw [Subgroup.closure_union]
            apply Subgroup.mem_sup_left
            rw [Subgroup.mem_closure_singleton]
            use α
            rw [g_eq_gamma]
            simp
          . rename_i g_mem_map
            rw [Subgroup.closure_union]
            apply Subgroup.mem_sup_right
            apply Subgroup.mem_closure_of_mem
            exact g_mem_map

        conv =>
          arg 1
          arg 1
          arg 1
          arg 1
          arg 2
          equals (new_N'_map '' (N'_fg.choose)) => rfl
        rw [← Subgroup.relIndex_mul_index gamma_alpha_le_gamma]
        simp
        refine ⟨?_, ?_⟩
        .
          unfold Subgroup.relIndex
          rw [← ne_eq]
          rw [← Subgroup.finiteIndex_iff]
          apply Subgroup.finiteIndex_of_rightCoset_cover_const (s := Finset.Ioo (-α : ℤ) (α)) (g := fun a => ⟨a • γ, (by
            rw [Set.insert_eq, Subgroup.closure_union]
            apply Subgroup.mem_sup_left
            rw [Subgroup.mem_closure_singleton]
            use a
            rfl
          )⟩)
          ext g
          simp
          have g_prop := g.property
          simp_rw [Set.insert_eq, Subgroup.closure_union] at g_prop
          rw [← MonoidHom.map_closure] at g_prop
          simp at g_prop
          rw [← SetLike.mem_coe] at g_prop
          rw [sup_comm] at g_prop


          rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
            (Subgroup.le_normalizer_of_conj_mem map_N'_invariant_gamma_one)] at g_prop
          rw [Set.mem_mul] at g_prop
          obtain ⟨b, hb, a, ha, g_eq⟩ := g_prop
          simp at ha
          rw [Subgroup.mem_closure_singleton] at ha
          obtain ⟨z, hz⟩ := ha
          use z % α
          refine ⟨?_, ?_⟩
          .
            have foo := Int.emod_lt_abs z (b := α) (by grind)
            rw [lt_abs] at foo
            refine ⟨?_, ?_⟩
            .
              have bar := Int.emod_nonneg z (b := α) (by simpa using alpha_nonzero)
              grind
            . grind
          .
            rw [Set.mem_smul_set]
            use ⟨(Additive.ofMul b) + (((α : ℤ) * (z / (α : ℤ))) • γ), ?_⟩
            .
              refine ⟨?_, ?_⟩
              .
                simp
                rw [Subgroup.mem_subgroupOf]
                simp_rw [Set.insert_eq, Subgroup.closure_union]
                rw [← SetLike.mem_coe]
                rw [sup_comm]
                rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.le_normalizer_of_conj_mem (by
                  simp_rw [← MonoidHom.map_closure]
                  apply map_N'_invariant_gamma
                ))]
                apply Set.mul_mem_mul
                .
                  simp
                  rw [← MonoidHom.map_closure]
                  exact hb
                .
                  simp
                  rw [Subgroup.mem_closure_singleton]
                  use (z / (α : ℤ))
                  conv =>
                    lhs
                    arg 1
                    equals toMul γ ^ (α : ℤ) =>
                      simp

                  rw [← zpow_mul]
              .
                simp
                rw [Subtype.ext_iff]
                simp
                rw [← g_eq, ←hz]
                nth_rw 3 [← Int.mul_ediv_add_emod (a := z) (b := α)]
                rw [← toMul_zsmul]
                conv =>
                  lhs
                  equals (ofMul b) + ((↑α * (z / ↑α)) • γ) + ((z % ↑α) • γ) =>
                    rfl


                rw [add_zsmul]
                rw [add_assoc]
                rfl
            .
              simp_rw [Set.insert_eq, Subgroup.closure_union]
              rw [sup_comm]
              rw [← SetLike.mem_coe]

              rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.le_normalizer_of_conj_mem (by
                simp_rw [← MonoidHom.map_closure]
                apply map_N'_invariant_gamma_one
              ))]
              apply Set.mul_mem_mul
              .
                simp
                rw [← MonoidHom.map_closure]
                exact hb
              .
                simp [Subgroup.mem_closure_singleton]
        .
          obtain ⟨s, s_compl, s_cosets⟩ := Subgroup.exists_leftTransversal_of_FiniteIndex (D := N') (H := ⊤) (by simp)
          simp at s_cosets

          rw [← ne_eq]
          rw [← Subgroup.finiteIndex_iff]
          apply Subgroup.finiteIndex_of_leftCoset_cover_const (s := s) (g := fun g => g.val.val.toMul)
          simp_rw [Set.insert_eq, Subgroup.closure_union]
          rename_bvar i → g


          conv =>
            arg 1
            arg 1
            intro i
            arg 1
            intro hi
            rw [sup_comm]
            rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.le_normalizer_of_conj_mem (by
              intro gamma_pow h_gamma_pow n hn
              simp_rw [← MonoidHom.map_closure] at hn
              simp_rw [← MonoidHom.map_closure]
              apply map_N'_invariant_gamma_one _ h_gamma_pow _ hn
            ))]
            rw [set_smul_eq_mul]
            rw [← mul_assoc]
            rw [← set_smul_eq_mul]


          simp_rw [← Set.iUnion_mul]
          conv =>
            arg 1
            arg 1
            equals Additive.toMul '' data.φ.ker =>
              apply_fun (fun s => Additive.toMul '' (Subtype.val '' s)) at s_cosets
              conv at s_cosets =>
                rhs
                equals Additive.toMul '' data.φ.ker =>
                  ext a
                  simp
              rw [← s_cosets]
              conv =>
                arg 1
                arg 1
                intro i
                arg 1
                intro hi
                arg 2

              simp_rw [← MonoidHom.map_closure]

              simp only [Set.image_image]
              first
                | erw [Set.image_iUnion₂]
                | rw [Set.image_iUnion₂]
                | simp only [Set.image_iUnion]
              apply Set.iUnion_congr
              intro i
              apply Set.iUnion_congr
              intro hi
              ext z
              simp only [closure_eq, coe_map]
              rw [Set.mem_smul_set]
              rw [Set.mem_image]
              refine ⟨?_, ?_⟩
              .
                intro hy
                obtain ⟨a, ha⟩ := hy
                have foo := ha.1
                rw [Set.mem_image] at foo
                obtain ⟨b, b_mem, a_eq_b⟩ := foo
                have N'_gen := N'_fg.choose_spec
                rw [N'_gen] at b_mem
                refine ⟨(↑i : Multiplicative ↥data.φ.ker) • b, Set.smul_mem_smul_set b_mem, ?_⟩
                rw [← ha.2, ← a_eq_b]
                rfl
              .
                intro hx
                obtain ⟨x, hx, x_eq⟩ := hx
                erw [Set.mem_smul_set] at hx
                obtain ⟨n, hn, x_eq_n⟩ := hx
                refine ⟨new_N'_map n, ?_, ?_⟩
                .
                  rw [Set.mem_image]
                  have N'_gen := N'_fg.choose_spec
                  rw [← N'_gen] at hn
                  exact ⟨n, hn, rfl⟩
                . rw [← x_eq, ← x_eq_n]
                  rfl


          conv =>
            arg 1
            lhs
            equals ↑data.φ.ker.toSubgroup' =>
              ext a
              simp

          rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _]
          .
            simp
            rw [eq_top_iff]
            have ker_gen := e_i_and_gamma_generates_G data.φ γ hγ
            have foo := new_generates.generates
            simp at foo
            rw [← foo, ← ker_gen]
            simp_rw [Subgroup.closure_union]
            conv =>
              lhs
              arg 1
              equals Subgroup.closure {γ.toMul} =>
                simp [Subgroup.closure_union]
                conv =>
                  lhs
                  arg 1
                  equals {γ.toMul, γ.toMul⁻¹} => rfl
                rw [Set.insert_eq]
                rw [Subgroup.closure_union]
                simp

            simp_rw [← Subgroup.closure_union]
            rw [Subgroup.closure_le]
            rw [Set.union_subset_iff]
            refine ⟨?_, ?_⟩
            .
              intro a ha
              simp at ha
              simp
              apply Subgroup.mem_sup_right
              simp [ha]
            .
              intro a ha
              apply Subgroup.mem_sup_left
              simp
              simp at ha
              obtain ⟨p, hp, a_eq⟩ := ha
              simp [e_i_with_gamma] at a_eq
              rw [← a_eq]
              conv =>
                arg 1
                arg 2
                equals (ofMul p) + -((data.φ (ofMul p)) • γ) =>
                  rfl


              simp [hγ]
          .
            apply Subgroup.le_normalizer_of_conj_mem
            intro b hb a ha
            rw [Subgroup.mem_closure_singleton] at hb
            obtain ⟨n, b_eq⟩ := hb
            simp [← b_eq]
            simp at ha
            exact ha
      . have foo := data.finite_index
        rw [Subgroup.finiteIndex_iff] at foo
        exact foo


-- Decompose list of {e_k, γ}:

-- The starting list must have the powers of γ sum to zero (since it's in the kernel of φ)


-- Map the list in a way that maintains the invariant that the powers of γ sum to zero:
-- If the head is e_i, then map it to γ_0,i = e_i
-- Otherwise, collect gamma terms:
-- If we get γ^a e_i * γ^b, then
-- * If the head is γ^n e_i for some n (collecting up adjacent γ), then choose γ_n,i = γ^n * e_i * γ^(-n)
-- * If the remaining list is just γ^n, then n must be 0 (since we maintained the invariant)

#print axioms three_two_gamma_m_generates
#print axioms three_two_ker_fg

-- NOTE: from https://www.numdam.org/item/PMIHES_1981__53__53_0.pdf
-- it looks like our definition of 'polynomial growth' should use `S ∪ S⁻¹`
theorem main_gromov_theorem (n: ℕ) (h: HasPolynomialGrowthD S n): Group.IsVirtuallyNilpotent G := by
  induction hn: n generalizing hGS n with
  | zero =>
    rw [hn] at h
    have G_finite := finite_of_growth_zero h
    rw [Group.IsVirtuallyNilpotent]
    use ⊥
    refine ⟨?_, ?_⟩
    . exact Group.isNilpotent_of_subsingleton
      -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
    . infer_instance
  | succ k ih =>
    obtain ⟨data⟩ := exists_theorem_3_1_input h
    -- Consider changing 'theorem_3_1' to make 'inductive_gromov' take in 'Generates',
    -- to avoid fiddling with 'FG.out' (which might not be symmetric)
    apply theorem_3_1 data n (by omega) h
    intro Q_generates Q_poly

    by_cases Q_finite: Finite Q_generates.G
    .
      rw [Group.IsVirtuallyNilpotent]
      use ⊥
      refine ⟨?_, ?_⟩
      . exact Group.isNilpotent_of_subsingleton
        -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
      . infer_instance
    .
      have prev := @ih Q_generates (n - 1) Q_poly (by omega)
      exact prev

#print sorries main_gromov_theorem
#print axioms main_gromov_theorem

end GeneratesNS
