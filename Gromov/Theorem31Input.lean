import Mathlib
import Gromov.RhoAbelian

/-!
# Constructing a `Theorem3_1_Input`

The finite-image case `rho_g_case_finite` and `exists_theorem_3_1_input`.
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

set_option maxHeartbeats 9000000

open MeasureTheory

open MeasureTheory

-- TODO - figure out why we need these


#print axioms laplace_bounded
#print axioms laplace_self_adjoint
#print axioms laplace_positive_semidefinite


#synth Module ℝ (Lp ℝ 2 (μ := MeasureTheory.volume (α := G)))


omit hGS in
lemma rangeRestrict_range {A B: Type*} [Group A] [Group B] (f: A →* B): f.rangeRestrict.range = ⊤ := by
  ext a
  have a_prop := a.property
  simp only [mem_top, iff_true]
  rw [MonoidHom.mem_range] at a_prop
  rw [MonoidHom.mem_range]
  obtain ⟨x, hx⟩ := a_prop
  use x
  ext
  simp [hx]


lemma rho_g_case_finite (hr: Finite (↥(rho_g))): Nonempty (Theorem3_1_Input G) := by
  unfold rho_g at hr

  have ker_finite_index := Subgroup.finiteIndex_ker (GRepW_base)
  let G' := (GRepW_base).ker

  let G'_action := (GRepW_base).domRestrict G'

  have act_ker (g: G) := MonoidHom.mem_ker (f := (GRepW_base)) (x := g)

  have act_v (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): Submodule.Quotient.mk (GRep  g f) = (Submodule.Quotient.mk (f) : W) := by
    simp [GRep]
    have apply_g := (act_ker g).mp hg
    simp [GRepW_base, GRepW_non_invertible, GRep] at apply_g
    apply_fun Units.val at apply_g
    rw [Representation.asGroupHom_apply] at apply_g
    rw [Representation.quotient_apply] at apply_g
    apply_fun (fun y => y (Submodule.Quotient.mk f)) at apply_g
    simp at apply_g
    exact apply_g

  let extract_const (f: LipschitzH) (hf: f ∈ ConstF ) := f 1

  simp_rw [Submodule.Quotient.eq] at act_v

  -- As proved in 'act_v', we have  '(GRep g f) - f' is a constant function. We can therefore evaluate
  -- it any poitn in G (here, 1) to get the constant
  let lambda_g := fun (g: G') (f: LipschitzH ) => ((GRep g.val) f - f) 1
  let lambda_g_dual (g: G'): Module.Dual ℝ (LipschitzH) := {
    toFun := fun w => lambda_g g w
    map_add' := by
      intro x y
      simp [lambda_g]
      abel
    map_smul' := by
      intro c x
      simp [lambda_g]
      rw [mul_sub]
  }

  -- TODO - this could be much cleaner
  have act_eq_lambda (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): (gAct g f) = f + ConstLipschitzH (lambda_g ⟨g, hg⟩ f) := by
    have act := act_v g hg f
    simp [GRep, gAct, ConstF] at act
    simp [gAct]
    obtain ⟨y, hy⟩ := act
    simp [lambda_g, GRep, gAct]
    ext a
    simp
    apply_fun (fun l => l.toFun) at hy
    have app_a := congrFun hy a
    simp [lipschitz_sub_tofun] at app_a
    rw [eq_comm] at app_a
    apply eq_add_of_sub_eq at app_a
    rw [app_a]
    rw [add_comm]
    simp [LipschitzH_apply]
    simp [LipschitzH_apply] at hy
    have other_app := congrFun hy 1
    simp at other_app
    rw [← other_app]
    simp [ConstLipschitzH]

  have lambda_const (g: (GRepW_base).ker) (f: LipschitzH ) (k: ℝ): (lambda_g g (f + (ConstLipschitzH k))) = (lambda_g g f) := by
    simp [lambda_g, GRep, gAct]
    simp [ConstLipschitzH]


  let lambda_g_hom: G' →* Multiplicative (Module.Dual ℝ (LipschitzH)) := {
    toFun := fun g => Multiplicative.ofAdd (lambda_g_dual g)
    map_one' := by
      simp [lambda_g_dual]
      simp [lambda_g]
      ext f
      simp
    map_mul' := by
      intro g h
      ext f
      simp [lambda_g_dual]
      conv =>
        lhs
        dsimp [lambda_g]
      simp [GRep]
      rw [gAct_mul]
      rw [act_eq_lambda h.val h.property]
      rw [act_eq_lambda g.val g.property]
      rw [lambda_const]
      simp [ConstLipschitzH]
      group
  }

  by_cases lambda_g_infinite: Infinite (lambda_g_hom.range)
  .

    apply g_hom_abelian G' ?_ lambda_g_hom.rangeRestrict ?_ lambda_g_hom.rangeRestrict.range ?_ ?_ ?_ ?_
    . simp [G']
      exact ker_finite_index
    . exact MonoidHom.rangeRestrict_surjective lambda_g_hom
    . rw [rangeRestrict_range]
      simp
      -- TODO: PR this to mathlib
      apply (Equiv.infinite_iff (α := lambda_g_hom.range) _).mp
      . exact lambda_g_infinite
      . exact {
          toFun := fun g => ⟨g, trivial⟩
          invFun := fun g => g.val
          left_inv := by simp [Function.LeftInverse]
          right_inv := by simp [Function.RightInverse, Function.LeftInverse]
        }
    . exact {
        is_comm := {
          comm := by
            intro a b
            ext
            simp
            rw [add_comm]
        }
      }
    . rw [Subgroup.finiteIndex_iff]
      rw [rangeRestrict_range]
      simp
    . rw [rangeRestrict_range]
      simp
      exact Group.FG.out
  .
    simp only [not_infinite_iff_finite] at lambda_g_infinite
    let G'' := lambda_g_hom.ker
    have G''_finite_index := Subgroup.finiteIndex_ker lambda_g_hom

  -- TODO - this could be a lot cleaner
    have G''_act_v (g: lambda_g_hom.ker) (x: G) (f: LipschitzH ): f (x * g) = f x := by
      specialize act_v g
      simp at act_v
      have g_prop := g.property
      rw [MonoidHom.mem_ker] at g_prop
      simp [lambda_g_hom, lambda_g_dual, lambda_g, GRep] at g_prop
      apply_fun (fun p => p f) at g_prop
      simp at g_prop
      rw [sub_eq_zero] at g_prop
      simp [gAct] at g_prop
      specialize act_v f
      simp [GRep, gAct, ConstF] at act_v
      obtain ⟨y, hy⟩ := act_v
      simp [ConstLipschitzH] at hy
      apply_fun (fun l => l.toFun) at hy
      simp at hy
      rw [Pi.sub_def] at hy
      have eval_one := hy
      apply_fun (fun f => f 1) at eval_one
      apply_fun (fun f => f x) at hy
      simp at hy
      simp at eval_one
      rw [← g_prop] at eval_one
      simp at eval_one
      rw [eq_comm] at hy
      apply eq_add_of_sub_eq' at hy
      simp
      rw [hy]
      simp
      exact eval_one


    -- View G'' as a subgroup of G
    let G''_subgroup_G := (Subgroup.map G'.subtype lambda_g_hom.ker)

    -- TODO - clean up this proof
    have G''_subgroup_finite_index: G''_subgroup_G.FiniteIndex := by
      unfold G''_subgroup_G
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map]
      simp
      unfold G'
      rw [Subgroup.finiteIndex_iff] at ker_finite_index
      refine ⟨?_, ker_finite_index⟩
      rw [Subgroup.finiteIndex_iff] at G''_finite_index
      exact G''_finite_index


    have finite_quotient := Subgroup.finite_quotient_of_finiteIndex (H := G''_subgroup_G)

    have coset_union := QuotientGroup.univ_eq_iUnion_smul G''_subgroup_G
    have f_range_eq (f: LipschitzH ): Set.range f = Set.range ((fun (x: G ⧸ G''_subgroup_G) => f (x.out))) := by
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        simp at ha
        obtain ⟨y, hy⟩ := ha
        have y_mem: y ∈ Set.univ := by simp
        rw [coset_union] at y_mem
        simp at y_mem
        obtain ⟨i, hi⟩ := y_mem
        rw [Set.mem_smul_set] at hi
        obtain ⟨x, x_mem, y_eq⟩ := hi
        rw [← y_eq] at hy

        unfold G''_subgroup_G at x_mem
        simp at x_mem
        obtain ⟨x_mem_g', hx'⟩ := x_mem

        have x_mem_ker: ⟨x, x_mem_g'⟩ ∈ lambda_g_hom.ker := by
          simp
          exact hx'

        let x_ker: lambda_g_hom.ker := ⟨⟨x, x_mem_g'⟩, x_mem_ker⟩
        have f_translate := G''_act_v x_ker i.out f

        simp only [Set.mem_range]
        use i
        rw [← f_translate]
        exact hy
      . intro ha
        simp only [Set.mem_range] at ha
        obtain ⟨y, hy⟩ := ha
        simp
        simp at hy
        use y.out


    have all_f_const (f: LipschitzH ): ∃ z: ℝ, f = ConstLipschitzH z := by
      have f_max := Set.Finite.exists_maximalFor (fun y => ‖y‖) (Set.range f) ?_ ?_
      obtain ⟨z, z_mem, hz⟩ := f_max

      have z_max: ∀ p ∈ Set.range f, ‖p‖ ≤ ‖z‖ := by
        intro p hp
        simp at hp
        obtain ⟨y, hy⟩ := hp
        by_cases p_le_z: ‖p‖ ≤ ‖z‖
        . exact p_le_z
        . simp at p_le_z

          have f_le := hz (j := f.toFun y) ?_ ?_
          .
            simp at f_le
            rw [← hy]
            exact f_le
          . simp
          . simp
            rw [← hy] at p_le_z
            linarith

      simp at z_mem
      obtain ⟨g_max, f_g_max_eq⟩ := z_mem

      have f_const_fn := harmonic_abs_max_implies_const  f.toFun (by
        have f_harmonic := f.harmonic
        simp [Harmonic] at f_harmonic
        simp [Laplace_b, f_conv_mu]
        ext x
        simp
        have f_harmonic_real := f_harmonic x
        rw [sub_eq_zero]
        exact f_harmonic_real
      ) g_max (by
        intro a
        specialize z_max ((f.toFun a)) (by (
          simp
        ))
        rw [← f_g_max_eq] at z_max
        simpa using z_max
      )

      use (f g_max)
      ext a
      have app := congrFun f_const_fn a
      rw [app]
      simp [ConstLipschitzH]
      .
        rw [f_range_eq]
        apply Set.finite_range
      . apply Set.range_nonempty

    obtain ⟨f, nontrivial_f⟩ := exists_nontrivial_harmonic
    obtain ⟨z, f_eq_const⟩ := all_f_const f
    specialize nontrivial_f z
    contradiction


-- TODO - upstream to mathlib
omit hGS in
lemma exists_theorem_3_1_input [hGS: Generates ] {d: ℕ} (hd: HasPolynomialGrowthD S d): Nonempty (Theorem3_1_Input G) := by
  by_cases rho_g_infinite: Infinite (↥(rho_g))
  . exact rho_g_case_infinite hd rho_g_infinite
  . exact rho_g_case_finite (by simpa using rho_g_infinite)

end GeneratesNS
