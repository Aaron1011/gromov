module

public import Mathlib

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

public section

open scoped ComplexConjugate

/-- The complexification of a real vector space `V`, realised as pairs `(x, y) ≃ x + i y`. -/
@[expose]
def Cx (V : Type*) := V × V

namespace Cx

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

instance : AddCommGroup (Cx V) := inferInstanceAs (AddCommGroup (V × V))

/-- Real part of an element of the complexification. -/
@[expose]
def fst (p : Cx V) : V := (p : V × V).1
/-- Imaginary part of an element of the complexification. -/
@[expose]
def snd (p : Cx V) : V := (p : V × V).2

omit [InnerProductSpace ℝ V] in
@[simp] lemma fst_mk (a b : V) : fst ((a, b) : Cx V) = a := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma snd_mk (a b : V) : snd ((a, b) : Cx V) = b := rfl
omit [InnerProductSpace ℝ V] in
@[ext] lemma ext {p q : Cx V} (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := Prod.ext h1 h2

omit [InnerProductSpace ℝ V] in
@[simp] lemma add_fst (p q : Cx V) : (p + q).fst = p.fst + q.fst := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma add_snd (p q : Cx V) : (p + q).snd = p.snd + q.snd := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma zero_fst : (0 : Cx V).fst = 0 := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma zero_snd : (0 : Cx V).snd = 0 := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma neg_fst (p : Cx V) : (-p).fst = -p.fst := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma neg_snd (p : Cx V) : (-p).snd = -p.snd := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma sub_fst (p q : Cx V) : (p - q).fst = p.fst - q.fst := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma sub_snd (p q : Cx V) : (p - q).snd = p.snd - q.snd := rfl

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
@[expose]
noncomputable def innerC (u v : Cx V) : ℂ :=
  ((inner ℝ u.fst v.fst + inner ℝ u.snd v.snd : ℝ) : ℂ)
    + Complex.I * (((inner ℝ u.fst v.snd - inner ℝ u.snd v.fst : ℝ) : ℂ))

lemma innerC_self_re (u : Cx V) :
    (innerC u u).re = inner ℝ u.fst u.fst + inner ℝ u.snd u.snd := by
  simp only [innerC, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- The inner product space core on the complexification. -/
@[expose]
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
### Completeness

`Cx V` carries the `L²` norm of its two components, so it is isometric to `V × V` with the `L²`
norm and inherits completeness from `V`.  This is what makes `Cx V →L[ℂ] Cx V` a C⋆-algebra, and
hence what makes Mathlib's continuous functional calculus (`cfc`) available on complexified
operators: the `ContinuousFunctionalCalculus ℝ _ IsSelfAdjoint` instance is derived from the
complex one, so it is not available on `V →L[ℝ] V` itself.
-/

@[simp] lemma norm_sq_eq (p : Cx V) : ‖p‖ ^ 2 = ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  show (innerC p p).re = _
  rw [innerC_self_re, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

lemma norm_eq (p : Cx V) : ‖p‖ = Real.sqrt (‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2) := by
  rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg p)]

/-- The complexification is isometric to `V × V` carrying the `L²` norm. -/
@[expose]
noncomputable def isometryProdL2 : Cx V ≃ᵢ WithLp 2 (V × V) where
  toFun p := WithLp.toLp 2 ((p.fst, p.snd) : V × V)
  invFun q := ((WithLp.ofLp q).1, (WithLp.ofLp q).2)
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun := by
    refine Isometry.of_dist_eq fun p q => ?_
    rw [dist_eq_norm, dist_eq_norm, WithLp.prod_norm_eq_of_L2, norm_eq]
    rfl

@[expose]
instance [CompleteSpace V] : CompleteSpace (Cx V) := isometryProdL2.completeSpace

/-!
### Real structure

The real module / normed structure is the restriction of scalars of the complex one, supplied by
`NormedSpace.complexToReal`.  The real scalar action is `r • p = (r : ℂ) • p`, componentwise.
-/

@[expose]
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
@[expose]
def toProdₗ : Cx V ≃ₗ[ℝ] V × V where
  toFun p := (p.fst, p.snd)
  map_add' p q := by simp
  map_smul' r p := by ext <;> simp
  invFun q := ((q.1, q.2) : Cx V)
  left_inv p := by ext <;> rfl
  right_inv q := by ext <;> rfl

@[expose]
instance [FiniteDimensional ℝ V] : FiniteDimensional ℝ (Cx V) :=
  toProdₗ.symm.finiteDimensional

@[expose]
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
@[expose]
noncomputable def mapL (f : V →L[ℝ] V) : Cx V →ₗ[ℂ] Cx V where
  toFun p := (show V × V from (f p.fst, f p.snd))
  map_add' p q := by ext <;> simp [map_add] <;> rfl
  map_smul' c p := by ext <;> simp [map_sub, map_add, map_smul] <;> rfl

@[simp] lemma mapL_fst (f : V →L[ℝ] V) (p : Cx V) : (mapL f p).fst = f p.fst := rfl
@[simp] lemma mapL_snd (f : V →L[ℝ] V) (p : Cx V) : (mapL f p).snd = f p.snd := rfl


@[simp] lemma mapL_id : mapL (ContinuousLinearMap.id ℝ V) = LinearMap.id := by
  ext p <;> simp

lemma norm_mapL_le (f : V →L[ℝ] V) (p : Cx V) : ‖mapL f p‖ ≤ ‖f‖ * ‖p‖ := by
  have h1 : ‖f p.fst‖ ^ 2 + ‖f p.snd‖ ^ 2 ≤ (‖f‖ * ‖p‖) ^ 2 := by
    have s1 : ‖f p.fst‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖p.fst‖ ^ 2 := by
      have h := f.le_opNorm p.fst
      have := norm_nonneg (f p.fst)
      nlinarith
    have s2 : ‖f p.snd‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖p.snd‖ ^ 2 := by
      have h := f.le_opNorm p.snd
      have := norm_nonneg (f p.snd)
      nlinarith
    rw [mul_pow, norm_sq_eq p]
    linarith
  calc ‖mapL f p‖ = Real.sqrt (‖f p.fst‖ ^ 2 + ‖f p.snd‖ ^ 2) := by rw [norm_eq]; rfl
    _ ≤ Real.sqrt ((‖f‖ * ‖p‖) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖f‖ * ‖p‖ := Real.sqrt_sq (by positivity)

/-- Complexification of a continuous real-linear map as a continuous `ℂ`-linear map. -/
@[expose]
noncomputable def mapCLM (f : V →L[ℝ] V) : Cx V →L[ℂ] Cx V :=
  (mapL f).mkContinuous ‖f‖ (norm_mapL_le f)

@[simp] lemma mapCLM_apply (f : V →L[ℝ] V) (p : Cx V) : mapCLM f p = mapL f p := rfl

lemma norm_mapCLM_le (f : V →L[ℝ] V) : ‖mapCLM f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

lemma mapCLM_sub (f g : V →L[ℝ] V) : mapCLM f - mapCLM g = mapCLM (f - g) := by
  ext p <;> rfl

/-- Complexification as a monoid homomorphism on endomorphisms (composition ↦ composition). -/
@[expose]
noncomputable def mapCLMHom : (V →L[ℝ] V) →* (Cx V →L[ℂ] Cx V) where
  toFun := mapCLM
  map_one' := by ext p <;> simp
  map_mul' f g := by ext p <;> simp

lemma mapCLM_continuous : Continuous (mapCLM : (V →L[ℝ] V) → (Cx V →L[ℂ] Cx V)) := by
  have h : LipschitzWith 1 (mapCLM : (V →L[ℝ] V) → (Cx V →L[ℂ] Cx V)) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, mapCLM_sub]
    simpa using norm_mapCLM_le (f - g)
  exact h.continuous

lemma mapCLM_injective : Function.Injective (mapCLM : (V →L[ℝ] V) → Cx V →L[ℂ] Cx V) := by
  intro f g h
  ext x
  have hx := congrArg (fun T : Cx V →L[ℂ] Cx V => (T ((x, 0) : Cx V)).fst) h
  exact hx

/-- Complexification as an injective group homomorphism on units. -/
@[expose]
noncomputable def unitsMapHom : (V →L[ℝ] V)ˣ →* (Cx V →L[ℂ] Cx V)ˣ := Units.map mapCLMHom

lemma unitsMapHom_injective :
    Function.Injective (unitsMapHom : (V →L[ℝ] V)ˣ → (Cx V →L[ℂ] Cx V)ˣ) :=
  Units.map_injective mapCLM_injective

lemma unitsMapHom_continuous :
    Continuous (unitsMapHom : (V →L[ℝ] V)ˣ → (Cx V →L[ℂ] Cx V)ˣ) := by
  apply Units.continuous_iff.mpr
  exact ⟨mapCLM_continuous.comp Units.continuous_val,
         mapCLM_continuous.comp Units.continuous_coe_inv⟩

/-!
### Self-adjointness

The complexification of a self-adjoint operator is self-adjoint.  Together with the
`CompleteSpace (Cx V)` instance above, this is what lets `cfc f (mapCLM Δ) (p := IsSelfAdjoint)`
elaborate *and* lets the `cfc` API lemmas discharge their `IsSelfAdjoint` side conditions.
-/

lemma isSymmetric_mapCLM [CompleteSpace V] {f : V →L[ℝ] V} (hf : IsSelfAdjoint f) :
    (mapCLM f : Cx V →ₗ[ℂ] Cx V).IsSymmetric := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hf
  have hs' : ∀ a b : V, inner ℝ (f a) b = inner ℝ a (f b) := fun a b => hs a b
  intro u v
  show innerC (mapL f u) v = innerC u (mapL f v)
  simp only [innerC, mapL_fst, mapL_snd, hs']

lemma isSelfAdjoint_mapCLM [CompleteSpace V] {f : V →L[ℝ] V} (hf : IsSelfAdjoint f) :
    IsSelfAdjoint (mapCLM f) := (isSymmetric_mapCLM hf).isSelfAdjoint

/-!
### Spectrum

Complexification preserves the spectrum *at real points*: `mapCLM f` is invertible exactly when
`f` is, because `mapCLM f` acts componentwise and so is bijective exactly when `f` is.

Note this is **not** the same as saying `spectrum ℂ (mapCLM f) = ((↑) '' spectrum ℝ f)`, which is
false in general: rotation by a quarter turn on `ℝ²` has empty real spectrum but complex spectrum
`{I, -I}`.  Only the real points of `spectrum ℂ (mapCLM f)` correspond to `spectrum ℝ f`; see
`ofReal_mem_spectrum_mapCLM_iff`.  For a self-adjoint `f` the complex spectrum is real anyway, so
in that case nothing is lost.
-/

@[simp] lemma mapCLM_one : mapCLM (1 : V →L[ℝ] V) = 1 := by ext p <;> rfl

lemma mapCLM_rsmul (r : ℝ) (f : V →L[ℝ] V) : mapCLM (r • f) = r • mapCLM f := by
  ext p <;> simp

lemma mapCLM_algebraMap (r : ℝ) :
    mapCLM (algebraMap ℝ (V →L[ℝ] V) r) = algebraMap ℝ (Cx V →L[ℂ] Cx V) r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mapCLM_rsmul, mapCLM_one]

lemma bijective_mapCLM_iff (f : V →L[ℝ] V) :
    Function.Bijective (mapCLM f) ↔ Function.Bijective f := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x x' h => ?_, fun y => ?_⟩
    · have : ((x, 0) : Cx V) = ((x', 0) : Cx V) := hinj (by ext; exacts [h, rfl])
      exact congrArg Cx.fst this
    · obtain ⟨p, hp⟩ := hsurj ((y, 0) : Cx V)
      exact ⟨p.fst, congrArg Cx.fst hp⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun p q h => ?_, fun q => ?_⟩
    · exact Cx.ext (hinj (congrArg Cx.fst h)) (hinj (congrArg Cx.snd h))
    · obtain ⟨a, ha⟩ := hsurj q.fst
      obtain ⟨b, hb⟩ := hsurj q.snd
      exact ⟨((a, b) : Cx V), by ext; exacts [ha, hb]⟩

lemma isUnit_mapCLM_iff [CompleteSpace V] (f : V →L[ℝ] V) : IsUnit (mapCLM f) ↔ IsUnit f := by
  rw [ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.isUnit_iff_bijective,
    bijective_mapCLM_iff]

/-- Complexification preserves the real spectrum.  This is the form the continuous functional
calculus wants, since `cfc` over `ℝ` is stated in terms of `spectrum ℝ`. -/
lemma spectrum_mapCLM [CompleteSpace V] (f : V →L[ℝ] V) :
    spectrum ℝ (mapCLM f) = spectrum ℝ f := by
  ext r
  simp only [spectrum.mem_iff]
  rw [← mapCLM_algebraMap, mapCLM_sub, isUnit_mapCLM_iff]


end Cx
