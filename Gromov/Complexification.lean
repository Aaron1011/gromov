import Mathlib

/-!
# Complexification of a real inner product space

This file builds the complexification `Cx V` of a real inner product space `V`, realised
concretely as pairs `(x, y)` thought of as `x + i y`.  It provides the complex module and
complex inner product space structure, the dimension formula
`finrank ℂ (Cx V) = finrank ℝ V`, and the complexification of a continuous real-linear map,
packaged as an injective monoid homomorphism on units.

`Cx V` is primarily a **complex** vector space; its real structure is the restriction of scalars
of the complex one (via `NormedSpace.complexToReal`), so the real normed/analysis instances agree
with the complex ones rather than forming a diamond.

This is the device that lets the Gromov development keep its Lipschitz harmonic functions
real-valued while still feeding the (irreducibly complex) compact-Lie / unitary-trick step:
the real representation is complexified here, just before the unitary machinery is invoked.
-/

open scoped ComplexConjugate

/-- The complexification of a real vector space `V`, realised as pairs `(x, y) ≃ x + i y`. -/
def Cx (V : Type*) := V × V

namespace Cx

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

instance : AddCommGroup (Cx V) := inferInstanceAs (AddCommGroup (V × V))

/-- Real part of an element of the complexification. -/
def fst (p : Cx V) : V := (p : V × V).1
/-- Imaginary part of an element of the complexification. -/
def snd (p : Cx V) : V := (p : V × V).2

@[simp] lemma fst_mk (a b : V) : fst ((a, b) : Cx V) = a := rfl
@[simp] lemma snd_mk (a b : V) : snd ((a, b) : Cx V) = b := rfl
@[ext] lemma ext {p q : Cx V} (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := Prod.ext h1 h2

@[simp] lemma add_fst (p q : Cx V) : (p + q).fst = p.fst + q.fst := rfl
@[simp] lemma add_snd (p q : Cx V) : (p + q).snd = p.snd + q.snd := rfl
@[simp] lemma zero_fst : (0 : Cx V).fst = 0 := rfl
@[simp] lemma zero_snd : (0 : Cx V).snd = 0 := rfl
@[simp] lemma neg_fst (p : Cx V) : (-p).fst = -p.fst := rfl
@[simp] lemma neg_snd (p : Cx V) : (-p).snd = -p.snd := rfl

/-- Complex scalar multiplication: `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`. -/
noncomputable instance : SMul ℂ (Cx V) where
  smul c p := (show V × V from (c.re • p.fst - c.im • p.snd, c.im • p.fst + c.re • p.snd))

@[simp] lemma csmul_fst (c : ℂ) (p : Cx V) : (c • p).fst = c.re • p.fst - c.im • p.snd := rfl
@[simp] lemma csmul_snd (c : ℂ) (p : Cx V) : (c • p).snd = c.im • p.fst + c.re • p.snd := rfl

noncomputable instance : Module ℂ (Cx V) where
  one_smul p := by ext <;> simp
  mul_smul a b p := by ext <;> simp [Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by ext <;> simp
  smul_add c p q := by ext <;> simp <;> module
  add_smul a b p := by ext <;> simp [Complex.add_re, Complex.add_im] <;> module
  zero_smul p := by ext <;> simp

/-- The Hermitian form on the complexification, conjugate-linear in the first argument. -/
noncomputable def innerC (u v : Cx V) : ℂ :=
  ((inner ℝ u.fst v.fst + inner ℝ u.snd v.snd : ℝ) : ℂ)
    + Complex.I * (((inner ℝ u.fst v.snd - inner ℝ u.snd v.fst : ℝ) : ℂ))

lemma innerC_self_re (u : Cx V) :
    (innerC u u).re = inner ℝ u.fst u.fst + inner ℝ u.snd u.snd := by
  simp only [innerC, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- The inner product space core on the complexification. -/
noncomputable def coreC : InnerProductSpace.Core ℂ (Cx V) where
  inner := innerC
  conj_inner_symm u v := by unfold innerC; simp [Complex.ext_iff, real_inner_comm]
  re_inner_nonneg u := by
    show 0 ≤ (innerC u u).re
    rw [innerC_self_re]; exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left u v w := by unfold innerC; simp [inner_add_left]; ring
  smul_left c u v := by
    unfold innerC
    simp only [csmul_fst, csmul_snd, inner_sub_left, inner_add_left, real_inner_smul_left]
    push_cast
    simp [Complex.ext_iff]
    constructor <;> ring
  definite u h := by
    have hre := congrArg Complex.re h
    rw [innerC_self_re] at hre
    simp only [Complex.zero_re] at hre
    have a := real_inner_self_nonneg (x := u.fst)
    have b := real_inner_self_nonneg (x := u.snd)
    have h1 : inner ℝ u.fst u.fst = 0 := le_antisymm (by linarith) a
    have h2 : inner ℝ u.snd u.snd = 0 := le_antisymm (by linarith) b
    ext
    · exact inner_self_eq_zero.mp h1
    · exact inner_self_eq_zero.mp h2

noncomputable instance : NormedAddCommGroup (Cx V) := coreC.toNormedAddCommGroup
noncomputable instance : InnerProductSpace ℂ (Cx V) := InnerProductSpace.ofCore coreC.toCore

/-!
### Real structure

The real module / normed structure is the restriction of scalars of the complex one, supplied by
`NormedSpace.complexToReal`.  The real scalar action is `r • p = (r : ℂ) • p`, componentwise.
-/

instance : IsScalarTower ℝ ℂ (Cx V) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

lemma rsmul_eq (r : ℝ) (p : Cx V) : r • p = (r : ℂ) • p := by
  rw [← algebraMap_smul ℂ r p, Complex.coe_algebraMap]

@[simp] lemma rsmul_fst (r : ℝ) (p : Cx V) : (r • p).fst = r • p.fst := by
  rw [rsmul_eq]
  simp only [csmul_fst, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
@[simp] lemma rsmul_snd (r : ℝ) (p : Cx V) : (r • p).snd = r • p.snd := by
  rw [rsmul_eq]
  simp only [csmul_snd, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

/-- The complexification, as an `ℝ`-linear space, is `V × V`. -/
def toProdₗ : Cx V ≃ₗ[ℝ] V × V where
  toFun p := (p.fst, p.snd)
  map_add' p q := by simp
  map_smul' r p := by ext <;> simp
  invFun q := ((q.1, q.2) : Cx V)
  left_inv p := by ext <;> rfl
  right_inv q := by ext <;> rfl

instance [FiniteDimensional ℝ V] : FiniteDimensional ℝ (Cx V) :=
  toProdₗ.symm.finiteDimensional

instance [FiniteDimensional ℝ V] : FiniteDimensional ℂ (Cx V) :=
  Module.Finite.of_restrictScalars_finite ℝ ℂ (Cx V)

@[simp] lemma finrank_eq [FiniteDimensional ℝ V] :
    Module.finrank ℂ (Cx V) = Module.finrank ℝ V := by
  have hreal : Module.finrank ℝ (Cx V) = 2 * Module.finrank ℝ V := by
    rw [toProdₗ.finrank_eq, Module.finrank_prod]; ring
  have htower : Module.finrank ℝ ℂ * Module.finrank ℂ (Cx V) = Module.finrank ℝ (Cx V) :=
    Module.finrank_mul_finrank ℝ ℂ (Cx V)
  have h2 : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [h2] at htower
  omega

/-! ### Complexification of a real-linear map -/

/-- Complexification of a continuous real-linear map as a `ℂ`-linear map, acting componentwise
on `(x, y) ≃ x + i y`. -/
noncomputable def mapL (f : V →L[ℝ] V) : Cx V →ₗ[ℂ] Cx V where
  toFun p := (show V × V from (f p.fst, f p.snd))
  map_add' p q := by ext <;> simp [map_add]
  map_smul' c p := by ext <;> simp [map_sub, map_add, map_smul]

@[simp] lemma mapL_fst (f : V →L[ℝ] V) (p : Cx V) : (mapL f p).fst = f p.fst := rfl
@[simp] lemma mapL_snd (f : V →L[ℝ] V) (p : Cx V) : (mapL f p).snd = f p.snd := rfl

lemma mapL_comp (f g : V →L[ℝ] V) : mapL (f.comp g) = (mapL f).comp (mapL g) := by
  ext p <;> simp

@[simp] lemma mapL_id : mapL (ContinuousLinearMap.id ℝ V) = LinearMap.id := by
  ext p <;> simp

variable [FiniteDimensional ℝ V]

/-- Complexification of a continuous real-linear map as a continuous `ℂ`-linear map. -/
noncomputable def mapCLM (f : V →L[ℝ] V) : Cx V →L[ℂ] Cx V := (mapL f).toContinuousLinearMap

@[simp] lemma mapCLM_apply (f : V →L[ℝ] V) (p : Cx V) : mapCLM f p = mapL f p := rfl

/-- Complexification as a monoid homomorphism on endomorphisms (composition ↦ composition). -/
noncomputable def mapCLMHom : (V →L[ℝ] V) →* (Cx V →L[ℂ] Cx V) where
  toFun := mapCLM
  map_one' := by ext p <;> simp
  map_mul' f g := by ext p <;> simp

lemma mapCLM_continuous : Continuous (mapCLM : (V →L[ℝ] V) → (Cx V →L[ℂ] Cx V)) := by
  have hlin : IsLinearMap ℝ (mapCLM : (V →L[ℝ] V) → (Cx V →L[ℂ] Cx V)) :=
    { map_add := fun f g => by ext p <;> simp
      map_smul := fun r f => by
        ext p
        · simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, mapCLM_apply, mapL_fst, rsmul_fst]
        · simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, mapCLM_apply, mapL_snd, rsmul_snd] }
  exact hlin.mk'.continuous_of_finiteDimensional

lemma mapCLM_injective : Function.Injective (mapCLM : (V →L[ℝ] V) → Cx V →L[ℂ] Cx V) := by
  intro f g h
  ext x
  have hx := congrArg (fun T : Cx V →L[ℂ] Cx V => (T ((x, 0) : Cx V)).fst) h
  simpa using hx

/-- Complexification as an injective group homomorphism on units. -/
noncomputable def unitsMapHom : (V →L[ℝ] V)ˣ →* (Cx V →L[ℂ] Cx V)ˣ := Units.map mapCLMHom

lemma unitsMapHom_injective :
    Function.Injective (unitsMapHom : (V →L[ℝ] V)ˣ → (Cx V →L[ℂ] Cx V)ˣ) :=
  Units.map_injective mapCLM_injective

lemma unitsMapHom_continuous :
    Continuous (unitsMapHom : (V →L[ℝ] V)ˣ → (Cx V →L[ℂ] Cx V)ˣ) := by
  apply Units.continuous_iff.mpr
  exact ⟨mapCLM_continuous.comp Units.continuous_val,
         mapCLM_continuous.comp Units.continuous_coe_inv⟩

end Cx
