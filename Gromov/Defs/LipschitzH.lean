module

public import Mathlib
public import Gromov.Defs.Measure

/-!
# Lipschitz harmonic functions

The type `LipschitzH` of Lipschitz harmonic functions on `G`, its additive and vector space
structure, and finiteness of balls.
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

def Harmonic (f: G → ℝ): Prop := ∀ x: G, f x = ((1 : ℝ) / #(S)) * ∑ s ∈ S, f (s * x)
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
  coe_injective f g h := by cases f; cases g; congr

/-- Nothing here is ever evaluated, and there is no computable equality test on `LipschitzH`
anyway, so decide equality classically once and for all. Supplying a single concrete instance
for this one type — rather than `open Classical`, which also overrides the *computable*
instances on e.g. `G` and `Fin n` — means every `DecidableEq` on `LipschitzH`, on a subspace
`↥V`, or on a basis index `↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)` resolves to the same term,
so no diamonds arise. Same idiom as `GL_W_DecidableEq` in `Gromov.lean`. -/
noncomputable instance LipschitzH_DecidableEq: DecidableEq (LipschitzH) :=
  Classical.typeDecidableEq _

omit hGS in
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
omit hGS in
@[simp]
lemma LipschitzH_apply [Generates ] (f: LipschitzH) (x: G): f x = f.toFun x := rfl


lemma S_nonempty: S.Nonempty := by exact Finset.nonempty_coe_sort.mp hS

lemma S_card_ne_zero_re: (#(S) : ℝ) ≠ 0 := by
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


instance LipschitzH.zero [Generates ] : Zero (LipschitzH) := {
  zero := {
    toFun := fun x => 0
    lipschitz := by
      use 0
      exact LipschitzWith.const 0
    harmonic := by simp [Harmonic]
  }
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
    show (((n + 1 : ℕ) : ℝ) • f).toFun g = (((n : ℕ) : ℝ) • f).toFun g + f.toFun g
    simp [lipschitz_smul_tofun]
    push_cast
    ring
}


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
    ext g
    show (((n + 1 : ℕ) : ℝ) • f).toFun g = (((n : ℕ) : ℝ) • f).toFun g + f.toFun g
    simp [lipschitz_smul_tofun]
    push_cast
    ring
  zsmul_neg' := by
    intro n hn
    ext g
    show ((Int.negSucc n : ℝ) • hn).toFun g = -((((n + 1 : ℕ) : ℝ)) • hn).toFun g
    simp [lipschitz_smul_tofun]
    push_cast
    ring
}


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

lemma finite_ball (x: G) (r: ℝ): Set.Finite (Metric.ball x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
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
lemma finite_closed_ball (x: G) (r: ℝ): Set.Finite (Metric.closedBall x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
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

end GeneratesNS
