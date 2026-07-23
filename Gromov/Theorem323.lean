import Mathlib
import Mathlib.Algebra.Group.Gromov.Defs
import Mathlib.Algebra.Group.Gromov.LipschitzNorm
import Mathlib.Algebra.Group.Gromov.TendstoTactic
import Mathlib.Algebra.Group.Gromov.TendstoNhdsMul

set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false


open scoped Finset
open scoped Pointwise



-- Ported from Mathlib.Data.Matrix.Mul (not present in this mathlib version).
-- Remove once this file is bumped to a mathlib that includes it.
open Matrix in
theorem Matrix.dot_mulVec_eq_sum_sum {m n R : Type*} [Fintype n] [Fintype m] [NonUnitalSemiring R]
    (v : m → R) (A : Matrix m n R) (w : n → R) :
    v ⬝ᵥ (A *ᵥ w) = ∑ j, ∑ i, v i * A i j * w j := by
  simp_rw [dotProduct_mulVec, dotProduct, vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]

/-- Reindexing both bases of a `LinearMap.toMatrix₂` by an equiv turns it into a `submatrix`. -/
theorem LinearMap.toMatrix₂_reindex {R M ι κ : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R M) (e : ι ≃ κ) (B : M →ₗ[R] M →ₗ[R] R) :
    LinearMap.toMatrix₂ (b.reindex e) (b.reindex e) B
      = (LinearMap.toMatrix₂ b b B).submatrix e.symm e.symm := by
  ext i j
  simp [LinearMap.toMatrix₂_apply, Module.Basis.reindex_apply, Matrix.submatrix_apply]

/-- The determinant of `LinearMap.toMatrix₂` is invariant under reindexing the basis. -/
theorem LinearMap.toMatrix₂_reindex_det {R M ι κ : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R M) (e : ι ≃ κ) (B : M →ₗ[R] M →ₗ[R] R) :
    (LinearMap.toMatrix₂ (b.reindex e) (b.reindex e) B).det
      = (LinearMap.toMatrix₂ b b B).det := by
  rw [LinearMap.toMatrix₂_reindex, Matrix.det_submatrix_equiv_self]

/-- For two bases `b`, `c` of the same real vector space, the `LinearMap.toMatrix₂`
determinants differ by a fixed positive constant `K = (b.reindex e).det c)²` (the square of the
change-of-basis determinant), **uniformly in the bilinear form** `B`. In particular the ratio of
two such determinants (e.g. at different scales) is basis-independent. -/
theorem LinearMap.toMatrix₂_det_basis_change {M ι κ : Type*} [AddCommGroup M] [Module ℝ M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ M) (c : Module.Basis κ ℝ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ,
      (LinearMap.toMatrix₂ c c B).det = K * (LinearMap.toMatrix₂ b b B).det := by
  let e := b.indexEquiv c
  refine ⟨((b.reindex e).det ⇑c) ^ 2, ?_, fun B => ?_⟩
  · have hne : (b.reindex e).det ⇑c ≠ 0 := by
      rw [Module.Basis.det_apply]
      exact left_ne_zero_of_mul_eq_one (by
        rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one])
    positivity
  · rw [← LinearMap.toMatrix₂_reindex_det b e B,
        ← LinearMap.toMatrix₂_mul_basis_toMatrix (b₁ := b.reindex e) (b₂ := b.reindex e) c c B,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply]
    ring

-- TODO - generalize and upstream
-- Based on https://math.stackexchange.com/questions/1101184/show-that-if-x-succeq-y-then-detx-ge-dety
lemma matrix_psd_det_one {n: Type*} [Fintype n] [DecidableEq n] (A: Matrix n n ℝ) (ha: A.PosSemidef): 1 ≤ (A + 1).det := by
  have foo := ha.isHermitian.spectral_theorem
  have H := ha.isHermitian
  simp at foo
  rw [foo]
  conv =>
    rhs
    arg 1
    equals H.eigenvectorUnitary * ((Matrix.diagonal H.eigenvalues) + 1) * (star H.eigenvectorUnitary) =>
      rw [mul_add, add_mul]
      simp

  rw [Matrix.det_conj_of_mul_eq_one]
  .
    rw [← Matrix.diagonal_one']
    rw [Matrix.diagonal_add]
    simp
    apply Finset.one_le_prod
    intro i _
    have foo := ha.eigenvalues_nonneg
    grind
  . simp
  . simp


open MatrixOrder in
lemma matrix_det_montone {n: Type*} [Fintype n] [DecidableEq n] (A B: Matrix n n ℝ) (hb: B.PosDef) (hab: (A - B).PosSemidef): B.det ≤ A.det := by

  have invert_sqrt: Invertible (CFC.sqrt B) := by
    apply Matrix.invertibleOfIsUnitDet
    rw [Matrix.PosSemidef.det_sqrt hb.posSemidef]
    simp
    rw [← ne_eq, Real.sqrt_ne_zero]
    . grind [hb.det_pos]
    . grind [hb.det_pos]


  have det_prod_eq: A.det = B.det * ((CFC.sqrt B)⁻¹ * (A - B) * (CFC.sqrt B)⁻¹ + 1).det := by
    conv =>
      lhs
      arg 1
      equals (CFC.sqrt B) * (CFC.sqrt B)⁻¹ * A * (CFC.sqrt B)⁻¹ * (CFC.sqrt B) =>
        simp


    rw [mul_assoc, mul_assoc, mul_assoc]
    rw [Matrix.det_mul]
    rw [← mul_assoc, ← mul_assoc]
    rw [Matrix.det_mul]
    ring
    rw [hb.posSemidef.det_sqrt]
    simp only [RCLike.sqrt_real]
    rw [Real.sq_sqrt (by grind [hb.det_pos])]
    rw [mul_sub]
    rw [sub_mul]
    conv =>
      rhs
      rhs
      rhs
      lhs
      rhs
      arg 1
      arg 2
      rw [← CFC.sqrt_mul_sqrt_self (a := B)]

    simp

  rw [det_prod_eq]
  rw [le_mul_iff_one_le_right]
  .
    apply matrix_psd_det_one
    rw [hb.posSemidef.inv_sqrt]
    have foo := (CFC.sqrt_nonneg B⁻¹)
    rw [Matrix.le_iff] at foo
    simp at foo
    nth_rw 2 [← foo.isHermitian.eq]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact hab
  . apply hb.det_pos


-- TODO - upstream. Mathlib only has `Finset.sum_biUnion` (which needs `PairwiseDisjoint`)
-- and the `ENNReal` `tsum` versions.
theorem Finset.sum_biUnion_le {κ α : Type*} [DecidableEq α] {s: Finset κ} {t: κ → Finset α}
    {f: α → ℝ} (hf: ∀ x, 0 ≤ f x): ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hnn: 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith


namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS


noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)
noncomputable def Q_R_lin (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R u.val v.val
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}

lemma Q_R_lin_apply (V: Submodule ℝ LipschitzH) (R: ℝ) (u v: V): Q_R_lin V R u v = Q_R R u v := by
  rfl

noncomputable def Q_R_lin_plain (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R u.val v.val
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}






open scoped Topology


-- These definitions go outside, since we need to explicitly vary the V that we pass in for the theorem statement
noncomputable def V_basis (V: Submodule ℝ LipschitzH) := Module.Basis.ofVectorSpace ℝ V
noncomputable def Q_R_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (R: ℝ) := ((Q_R_lin V R).toMatrix₂ b b)
noncomputable def my_expr {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (d: ℝ) (R : ℕ) := #(S ^ R) * ((Q_R_matrix b R).det ^ ((1 : ℝ) / Module.finrank ℝ V)) / (R ^ d)
-- This is a liminf < ∞ in Vikman, but we can actually prove that it goes to 0, which makes things much easier to work with
noncomputable def growth_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (d: ℝ) := Filter.Tendsto (fun (R: ℕ) => my_expr b d R) (Filter.atTop) ((𝓝[>] 0))

lemma Q_R_lin_symm (V: Submodule ℝ LipschitzH) (R: ℝ): (Q_R_lin V R).IsSymm := {
  eq := by
    intro u v
    simp [Q_R_lin, Q_R]
    simp_rw [mul_comm]
}

lemma Q_R_lin_hermetian {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (R: ℝ): (Q_R_matrix b R).IsHermitian := by
  rw [Q_R_matrix, ← LinearMap.isSymm_iff_isHermitian_toMatrix]
  apply Q_R_lin_symm

lemma Q_R_lin_sub_pos_semi_def (V : Submodule ℝ LipschitzH) (R_1 R_2: ℝ) (hr: R_1 ≤ R_2): ((Q_R_lin V R_2) - Q_R_lin V R_1).IsPosSemidef := by
  rw [LinearMap.isPosSemidef_def]
  refine ⟨?_, ?_⟩
  .
    rw [sub_eq_add_neg]
    apply LinearMap.IsSymm.add
    . apply Q_R_lin_symm
    .
      -- TODO - add smul/neg lemmas so that we don't need to inline the proof here
      exact {
        eq := by
          intro u v
          simp [Q_R_lin, Q_R]
          simp_rw [mul_comm]
    }
  .
    rw [LinearMap.isNonneg_def]
    intro x
    simp [Q_R_lin, Q_R]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    .
      simp [Metric.closedBall]
      grind
    . intro a ha a_not
      rw [← pow_two]
      positivity

lemma v_r_all_nonzero (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V]: ∃ R: ℝ, ∀ u ∈ V, u ≠ 0 → ∃ g ∈ Metric.closedBall 1 R, u g ≠ 0 := by
  let zero_ball (n: ℕ): Submodule ℝ V := {
      carrier := {v: V | ∀ g ∈ Metric.closedBall 1 n, v.val g = 0}
      add_mem' := by
        intro a b ha hb
        simp at ha hb
        simp
        grind
      zero_mem' := by
        simp
      smul_mem' := by
        intro c x hx
        simp at hx
        simp
        intro g hg
        grind
  }

  let f: ℕ →o (Submodule ℝ V)ᵒᵈ := {
    toFun := zero_ball
    monotone' := by
      intro a b hab x hx
      simp [zero_ball] at hx
      simp [zero_ball]
      intro g hg
      apply hx g
      grw [hab] at hg
      exact hg
  }
  have artintian: IsArtinian ℝ V := by infer_instance
  rw [← monotone_stabilizes_iff_artinian] at artintian
  specialize artintian f
  obtain ⟨n, hn⟩ := artintian

  have inter_zero: ⨅ n: ℕ, zero_ball n = 0 := by
    ext a
    simp only [Submodule.mem_iInf, Submodule.zero_eq_bot, Submodule.mem_bot]
    refine ⟨?_, ?_⟩
    .
      intro hi
      ext g
      specialize hi (WordNorm g)
      simp [zero_ball] at hi
      specialize hi g
      simp [dist, WordDist_one] at hi
      simp [hi]
    . intro hi
      simp [hi]

  rw [← Antitone.iInf_nat_add (k := n)] at inter_zero
  .
    conv at inter_zero =>
      lhs
      arg 1
      intro k
      equals zero_ball n =>
        specialize hn (k + n) (by simp)
        simp [f] at hn
        exact hn.symm

    simp at inter_zero
    simp [zero_ball] at inter_zero
    use n
    intro u hu
    rw [Set.ext_iff] at inter_zero
    specialize inter_zero ⟨u, hu⟩
    simp at inter_zero
    intro u_ne_zero
    simp [u_ne_zero] at inter_zero
    simp
    exact inter_zero
  . intro a b hab
    simp [zero_ball]
    intro u hu hg
    intro g g_dist
    specialize hg g
    grw [hab] at g_dist
    specialize hg g_dist
    exact hg



noncomputable def R'_ (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V] : ℝ := (v_r_all_nonzero V).choose


lemma Q_R_pos_on_R' {V: Submodule ℝ LipschitzH} (v: V) (hv: v ≠ 0) [FiniteDimensional ℝ V] [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)] (R: ℝ) (hR: (R'_ V) ≤ R): 0 < Q_R R v v := by
  simp [Q_R]
  rw [Finset.sum_pos_iff_of_nonneg]
  .
    by_contra!
    simp_rw [← pow_two] at this
    simp only [sq_nonpos_iff] at this

    have foo := (v_r_all_nonzero V).choose_spec (v) (by apply Submodule.coe_mem) ?_
    .
      obtain ⟨g, g_mem, x_g_nonzero⟩ := foo
      specialize this g ?_
      .
        simp
        unfold R'_ at hR
        grw [hR] at g_mem
        simpa using g_mem
      .
        simp at x_g_nonzero
        contradiction
    .
      conv =>
        rhs
        equals (0: V) =>
          simp

      rw [ne_eq, ← Subtype.ext_iff]
      rw [← ne_eq]
      exact hv
  . intro y hy
    rw [← pow_two]
    positivity

lemma Q_R_matrix_pos_def {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} [FiniteDimensional ℝ V] (b : Module.Basis ι ℝ ↥V) (R: ℝ) (hR: (R'_ V) ≤ R): (Q_R_matrix b R).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Q_R_lin_hermetian b _)
  intro x hx
  simp [Q_R_matrix]
  conv =>
    rhs
    lhs
    equals (star x) => simp
  rw [star_dotProduct_toMatrix₂_mulVec]
  apply Q_R_pos_on_R'
  . rw [LinearEquiv.map_ne_zero_iff]
    exact hx
  . exact hR

#print sorries Q_R_matrix_pos_def

-- TODO - generalize and upstream
theorem LipschitzWith.sum {ι : Type*} {α : Type*} {E : Type*}
    [PseudoEMetricSpace α] [SeminormedAddCommGroup E]
    {s : Finset ι} {f : ι → α → E} {K : ι → NNReal}
    (hf : ∀ i ∈ s, LipschitzWith (K i) (f i)) :
    LipschitzWith (∑ i ∈ s, K i) (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using LipschitzWith.const (α := α) (0 : E)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))



section V_variable

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V] (hV : Even (Module.finrank V))  [V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)]

instance nonempty_basis: Nonempty ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V) := Module.Basis.index_nonempty (Module.Basis.ofVectorSpace _ _)

-- TODO - generalize and upstream
lemma euclidean_of_lp_le {ι : Type*} [Fintype ι] (x: EuclideanSpace ℝ ι) (i: ι):
    |x.ofLp i| ≤ ‖x‖ := by

  rw [EuclideanSpace.norm_eq]
  rw [Real.le_sqrt]
  .
    simp
    apply Finset.single_le_sum (a := i)
    . intro i _
      positivity
    . simp
  . simp
  . positivity


/-- The Lipschitz constant `‖(b i).val‖` of the `i`-th vector of the basis `b` of `V`. -/
noncomputable def v_lipschitz_constant {ι : Type*} (b : Module.Basis ι ℝ ↥V) (i : ι) : ℝ :=
  ‖(b i).val‖

/-- The value at the origin `‖(b i).val 1‖` of the `i`-th vector of the basis `b` of `V`. -/
noncomputable def v_origin_norm {ι : Type*} (b : Module.Basis ι ℝ ↥V) (i : ι) : ℝ :=
  ‖(b i).val 1‖

/-- The maximum, over vectors of the basis `b`, of the Lipschitz constant `v_lipschitz_constant`. -/
noncomputable def max_lipschitz {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  v_lipschitz_constant b (Finite.exists_max (v_lipschitz_constant b)).choose

/-- The maximum, over vectors of the basis `b`, of the value at the origin `v_origin_norm`. -/
noncomputable def max_origin {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  v_origin_norm b (Finite.exists_max (v_origin_norm b)).choose

lemma le_max_lipschitz {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (i) : v_lipschitz_constant b i ≤ max_lipschitz b :=
  (Finite.exists_max (v_lipschitz_constant b)).choose_spec i

lemma le_max_origin {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (i) : v_origin_norm b i ≤ max_origin b :=
  (Finite.exists_max (v_origin_norm b)).choose_spec i

lemma max_lipschitz_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ max_lipschitz b := by
  unfold max_lipschitz v_lipschitz_constant; positivity

lemma max_origin_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ max_origin b := by
  unfold max_origin v_origin_norm; positivity

/-- The `R`-independent constant appearing in `det_bound` (the `(1 + R) ^ 2` factor is kept
separate, in the statement of `det_bound`). -/
noncomputable def det_bound_const {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  ((Module.finrank ℝ ↥V) * max_lipschitz b + (Module.finrank ℝ ↥V) * max_origin b) ^ 2

lemma det_bound_const_nonneg {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : 0 ≤ det_bound_const b := by
  simp [det_bound_const]
  positivity

lemma det_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) (R: ℕ) (hR: (R'_ V) ≤ R):
    ((Q_R_matrix b R).det ^ ((1: ℝ) / Module.finrank ℝ V))
      ≤ det_bound_const b * (1 + R) ^ 2 * #(S ^ R) := by
  classical
  let argmax_eigen := (Finite.exists_max (Q_R_lin_hermetian b R).eigenvalues).choose
  let m :=  (Q_R_lin_hermetian b R).eigenvalues (argmax_eigen)
  let m_vec := (Q_R_lin_hermetian b R).eigenvectorBasis argmax_eigen
  let m_vec_V := b.equivFun.symm (m_vec.ofLp)

  let v_lipschitz_constant := v_lipschitz_constant b
  let v_origin_norm := v_origin_norm b
  let max_lipschitz := max_lipschitz b
  let max_origin := max_origin b
  have h_max_lipschitz : ∀ i, v_lipschitz_constant i ≤ max_lipschitz := le_max_lipschitz b
  have h_max_origin : ∀ i, v_origin_norm i ≤ max_origin := le_max_origin b
  obtain hB := iterated_lipschitz_bound m_vec_V.val

  -- have B_nonneg: 0 ≤ B := by
  --   specialize hB 1
  --   simp at hB
  --   have foo := abs_nonneg ((m_vec_V).val.toFun 1)
  --   grw [hB] at foo
  --   apply nonneg_of_mul_nonneg_left foo (by grind)
  rw [show det_bound_const b * (1 + R) ^ 2
        = (((Module.finrank ℝ ↥V) * max_lipschitz
            + (Module.finrank ℝ ↥V) * max_origin) * (1 + R)) ^ 2 from by
      simp only [max_lipschitz, max_origin, det_bound_const]; ring]
  rw [(Q_R_lin_hermetian b R).det_eq_prod_eigenvalues]
  grw [Finset.prod_le_prod (g := fun _ => m)]
  .
    simp
    rw [← Module.finrank_eq_card_basis b]
    rw [←  Real.rpow_natCast]
    rw [← Real.rpow_mul]
    .
      have finrank_pos := Module.finrank_pos (R := ℝ) (M := V)
      field_simp [finrank_pos]
      simp
      unfold m
      rw [Matrix.IsHermitian.eigenvalues_eq]
      simp [Q_R_matrix]
      have foo := dotProduct_toMatrix₂_mulVec b b (Q_R_lin V R)
      conv at foo =>
        intro x y
        lhs
        lhs
        equals x =>
          ext a
          simp
      conv at foo =>
        intro x y
        lhs
        rhs
        rhs
        equals y =>
          ext a
          simp
      rw [foo]
      simp only [Q_R_lin, Q_R, LipschitzH_apply,  map_sum,
        map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_sum, LinearMap.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le]
      simp_rw [← pow_two]
      grw [Finset.sum_le_card_nsmul (n := (((((Module.finrank ℝ ↥V)) * max_lipschitz + ((Module.finrank ℝ ↥V) * max_origin)) * (1 + R)) ^ 2))]
      .
        rw [← card_closed_ball_eq]
        simp
        rw [mul_comm]
        field_simp
        simp
      .
        intro x hx
        specialize hB x
        simp
        simp at hB
        rw [← Real.sqrt_sq_eq_abs] at hB
        rw [Real.sqrt_le_iff] at hB
        have foo := hB.2
        .
          simp at foo
          simp [dist, WordDist_one] at hx
          grw [hx] at foo
          conv =>
            lhs
            arg 1
            arg 1
            arg 2
            intro x
            arg 1
            arg 1
            arg 1
            equals (Q_R_lin_hermetian b ↑R).eigenvectorBasis =>
              rfl
          conv at foo =>
            lhs
            simp [m_vec_V, m_vec]
          grw [foo]
          rw [mul_pow, mul_pow]
          rw [mul_le_mul_iff_left₀]
          .
            rw [pow_le_pow_iff_left₀]
            . apply add_le_add
              .
                simp [max_lipschitz]
                have foo := (m_vec_V).val.lipschitz.choose_spec
                conv at foo =>
                  arg 2
                  simp [m_vec_V]

                conv =>
                  lhs
                  equals ‖m_vec_V.val‖₊ =>
                    rfl
                simp [m_vec_V]
                --grw [norm_sum_l]
                grw [norm_sum_le]
                grw [Finset.sum_le_card_nsmul (n := ↑max_lipschitz)]
                .
                  simp
                  rw [← Module.finrank_eq_card_basis b]
                .
                  intro i _
                  simp [norm_smul]
                  grw [euclidean_of_lp_le]
                  simp [m_vec]
                  apply h_max_lipschitz
              .
                simp [m_vec_V, m_vec]
                rw [← LipschitzH_apply]
                rw [LipschitzH.finset_sum_apply]
                grw [Finset.abs_sum_le_sum_abs]
                grw [Finset.sum_le_card_nsmul (n := max_origin)]
                . simp
                  rw [← Module.finrank_eq_card_basis b]
                .
                  intro i hi
                  simp
                  grw [euclidean_of_lp_le]
                  simp
                  apply h_max_origin
            . positivity
            . exact add_nonneg (mul_nonneg (by positivity) (max_lipschitz_nonneg b))
                (mul_nonneg (by positivity) (max_origin_nonneg b))
            . simp
          . positivity

    . unfold m
      apply Matrix.PosSemidef.eigenvalues_nonneg
      apply (Q_R_matrix_pos_def b R hR).posSemidef
  .
    apply Finset.prod_nonneg
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def b R hR).posSemidef
  .
    intro i _
    apply Matrix.PosSemidef.eigenvalues_nonneg
    apply (Q_R_matrix_pos_def b R hR).posSemidef
  . intro i _
    unfold m
    have foo := (Finite.exists_max (Q_R_lin_hermetian b R).eigenvalues).choose_spec
    apply foo i

#print axioms det_bound
end V_variable

-- Everything in this section freely references fields from V_Wrapper
section V_Wrapper_Section

class V_Wrapper where
  V: Submodule ℝ LipschitzH
  V_finite: FiniteDimensional ℝ V
  V_nontrivial: Nontrivial V
  V_even: Even (Module.finrank ℝ V)
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ V)

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

local instance v_finite_dim_inst: FiniteDimensional ℝ V := v_wrapper_inst.V_finite
local instance v_nontrivial_inst: Nontrivial V := v_wrapper_inst.V_nontrivial
local instance V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ V) := v_wrapper_inst.V_decidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private noncomputable def R' := R'_ V


-- Todo - is the better way to declare theorem_3_23 so that the constant is not allowed to depend on V?
-- TODO - can this somehow be merged with V_wrapper?
structure V_Data where
  V: Submodule ℝ LipschitzH
  hV: FiniteDimensional ℝ V
  (V_even : Even (Module.finrank ℝ V))
  V_decidable: DecidableEq ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)


noncomputable def Q_R_single (R : ℝ) (u: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g)^2

lemma Q_R_single_eq (R: ℝ) (u : G → ℝ): Q_R_single R u = Q_R R u u := by
  unfold Q_R_single Q_R
  simp_rw [pow_two]





-- Finding good scales:

private noncomputable def dim (V: Type*) [AddCommMonoid V] [Module ℝ V] : ℝ := Module.finrank ℝ V

private noncomputable def i₀ : ℕ := Nat.clog 16 ⌈R'⌉₊

lemma Q_R_matrix_pos_def_i₀ (b : Module.Basis ι ℝ V) (R: ℝ) (hR: 16 ^ (i₀) ≤ R): (Q_R_matrix b R).PosDef := by
  apply Q_R_matrix_pos_def
  simp [i₀] at hR
  have foo := Nat.le_pow_clog (b := 16) (x := ⌈R'_ V⌉₊) (by simp)
  have r_ceil := Nat.le_ceil (R')
  unfold R' at r_ceil
  grw [r_ceil]
  grw [foo]
  simp
  unfold R' at hR
  grw [hR]

private noncomputable def f (b : Module.Basis ι ℝ V) (R: ℕ): ℝ := #(S ^ R) * (Q_R_matrix b R).det ^ (dim V)⁻¹
private noncomputable def h (b : Module.Basis ι ℝ V) (i: ℕ): ℝ := Real.log (f b (16 ^ i))

-- Matrix.le_iff


lemma f_monotone_on (bas : Module.Basis ι ℝ V): MonotoneOn (f bas) (Set.Ici ⌈R'⌉₊) := by
  intro x hx y hy hxy
  unfold f
  grw [Finset.pow_subset_pow_right (n := y)]
  .
    rw [mul_le_mul_iff_right₀]
    .
      rw [Real.rpow_le_rpow_iff]
      .
        apply matrix_det_montone
        .
          apply Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
        .
          unfold Q_R_matrix
          rw [← map_sub]
          rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
          apply Q_R_lin_sub_pos_semi_def
          simpa using hxy
      .
        have foo := Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
        grind [foo.det_pos]
      .
        have foo := Q_R_matrix_pos_def bas y (by simp [R'] at hy; exact hy)
        grind [foo.det_pos]
      . simp [dim]
        exact Module.finrank_pos
    .
      simp
      apply Finset.Nonempty.pow
      apply S_nonempty

  . apply Real.rpow_nonneg
    have foo := Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
    grind [foo.det_pos]
  . apply hGS.one_mem
  . exact hxy

lemma h_montone_on (bas : Module.Basis ι ℝ V): MonotoneOn (h bas) (Set.Ici i₀) := by
  unfold h
  rw [← Function.comp_def]
  apply MonotoneOn.comp
  . apply Real.strictMonoOn_log.monotoneOn
  .
    rw [← Function.comp_def]
    apply MonotoneOn.comp
    . apply f_monotone_on bas
    .
      conv =>
        arg 1
        equals fun n => 16 ^ n =>
          simp
      apply (pow_right_monotone (by simp)).monotoneOn
    . intro a ha
      simp [i₀] at ha
      simp
      rw [Nat.clog_le_iff_le_pow] at ha
      .
        rify at ha
        grw [Nat.le_ceil (a := R')]
        exact ha
      . simp
  .
    intro a ha
    simp
    simp at ha
    simp [f]
    apply mul_pos
    . simp
      apply Finset.Nonempty.pow
      apply S_nonempty
    .
      apply Real.rpow_pos_of_pos
      apply (Q_R_matrix_pos_def_i₀ bas _ ?_).det_pos
      rw [pow_le_pow_iff_right₀]
      . exact ha
      . simp



lemma growth_implies_lim_h (b : Module.Basis ι ℝ V) (d: ℕ) (h_growth: growth_bound b d): Filter.Tendsto (fun (i: ℕ) => (h b i - d * i * Real.log 16)) Filter.atTop Filter.atBot := by
  unfold growth_bound my_expr at h_growth
  have pow_tendsto: Filter.Tendsto (fun n => 16 ^ n) Filter.atTop Filter.atTop := by
    apply StrictMono.tendsto_atTop
    apply pow_right_strictMono₀
    simp

  have log_tendsto := Real.tendsto_log_nhdsGT_zero
  -- Real.tendsto_log_nhdsNE_zero
  have comp_pow := Filter.Tendsto.comp h_growth pow_tendsto
  have comp_log := log_tendsto.comp comp_pow
  simp [Function.comp_def] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀] at comp_log
  conv at comp_log =>
    arg 1
    intro x
    rw [Real.log_div (by
      rw [mul_ne_zero_iff]
      refine ⟨?_, ?_⟩
      . simp
        grind [S_nonempty]
      .
        have det_pos := (Q_R_matrix_pos_def_i₀ b (16 ^ (x + i₀)) (by
          rw [add_comm]
          rw [pow_add]
          simp
          norm_cast
          apply Nat.one_le_pow
          simp
        )).det_pos

        rw [Real.rpow_ne_zero]
        . grind
        . grind
        .
          norm_cast
          rw [inv_eq_zero]
          norm_cast
          rw [← ne_eq, Nat.ne_zero_iff_zero_lt]
          apply Module.finrank_pos
    ) (by simp)]
    simp
  simp [h, f, dim]
  simp_rw [← mul_assoc] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀]
  simp
  exact comp_log

#print axioms growth_implies_lim_h

noncomputable def a (d: ℕ) := 4 * d * Real.log 16


lemma exists_j_0_for_h (b : Module.Basis ι ℝ V) (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound b d): ∃ j_0: ℕ, h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * j_0) < w * (a d) := by
  by_contra!

  have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (i₀ + 3 * w * n)) (m := 0) (n := N) (by simp)
  simp_rw [eq_comm, sub_eq_iff_eq_add] at h_sum

  have h_gt (N: ℕ): h b (i₀ + (3 * w * N)) ≥ 4 * d * w * N * (Real.log 16) + h b i₀ := by
    rw [h_sum]
    grw [← Finset.card_nsmul_le_sum (n := w * (a d))]
    .
      simp
      simp [a]
      grind
    . intro n hn
      apply this

  have h_diff_ge (N: ℕ): h b (i₀ + (3 * w * N)) - d * (i₀ + 3 * w * N) * Real.log 16 ≥ d * (w * N - i₀) * (Real.log 16) + h b i₀ := by
    grw [h_gt]
    simp
    grind

  have rhs_diverges: Filter.Tendsto (fun N => d * (w * N - i₀) * (Real.log 16) + h b i₀) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    rw [Filter.tendsto_mul_const_atTop_of_pos (by positivity)]
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    simp_rw [sub_eq_add_neg]
    apply Filter.tendsto_atTop_add_const_right
    conv =>
      arg 1
      equals fun x => w * x =>
        simp
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    apply Filter.tendsto_id

  apply growth_implies_lim_h at h_growth
  rw [Filter.tendsto_atTop_atBot] at h_growth
  rw [Filter.tendsto_atTop_atTop] at rhs_diverges

  obtain ⟨positive_start, h_positive_start⟩ := rhs_diverges 1
  obtain ⟨negative_start, h_negative_start⟩ := h_growth 0

  specialize h_positive_start (max ⌈positive_start⌉₊ negative_start) (by
    apply le_max_of_le_left
    apply Nat.le_ceil
  )
  -- TODO - why can't grind just solve this?
  specialize h_negative_start (i₀ + 3 * w * max ⌈positive_start⌉₊ negative_start) (by
    have le_max: negative_start ≤ max ⌈positive_start⌉₊ negative_start := by
      simp
    conv =>
      lhs
      equals 0 + negative_start => simp
    apply Nat.add_le_add
    . simp
    .
      conv =>
        lhs
        equals 1 * negative_start => simp
      apply Nat.mul_le_mul
      . grind
      . simp
  )

  have h_ge_one := h_diff_ge (max ⌈positive_start⌉₊ negative_start)
  norm_cast at h_ge_one
  norm_cast at h_positive_start
  grw [← h_positive_start] at h_ge_one
  grind




structure Lemma3_24_data (b : Module.Basis ι ℝ V) (d w: ℕ) where
  i_1 : ℕ
  i_2 : ℕ
  i_1_ge: i₀ ≤ i_1
  i_2_ge: i₀ ≤ i_2
  i_2_pos: 0 < i_2
  i_diff_mem: i_2 - i_1 ∈ Set.Ioo w (3 * w)
  h_diff_lt_w: h b (i_2 + 1) - h b i_1 < w * (a d)
  first_h_i: h b (i_1 + 1) - h b i_1 < (a d)
  second_h_i : h b (i_2 + 1) - h b i_2 < (a d)

lemma lemma_3_24 (b : Module.Basis ι ℝ V) (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound b d): Nonempty (Lemma3_24_data b d w) := by
  obtain ⟨j_0, h_j_0⟩ := exists_j_0_for_h b w d hw hd h_growth
  let m := i₀ + 3 * w * j_0

  have exists_i1: ∃ i_1: ℕ, i_1 ∈ Set.Ico m (m + w) ∧ h b (i_1 + 1) - h b i_1 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (m + n)) (m := 0) (n := w) (by simp)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h b (m + w) - h b (m) ≤ h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on b
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on b
        . simp [m]
        . simp [m]
        . simp [m]


    have h_le_w_a_d : h b (m  + w) - h b m ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h b (m + w) - h b m := by
      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
      . intro x hx
        apply this
        simpa using hx
    grind

  -- TODO - can this be deduplicated with exists_i1 ?
  have exists_i2: ∃ i_2: ℕ, i_2 ∈ Set.Ico (m + 2*w) (m + 3 * w) ∧ h b (i_2 + 1) - h b i_2 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (m + n)) (m := (2 * w)) (n := (3 * w)) (by grind)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h b (m + 3 * w) - h b (m + 2 * w) ≤ h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on b
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on b
        . simp [m]
        . simp [m]
          grind
        . simp [m]


    have h_le_w_a_d : h b (m  + 3 * w) - h b (m + 2 * w) ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h b (m + 3 * w) - h b (m + 2* w) := by

      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
        rw [← Nat.sub_mul]
        simp
      . intro x hx
        apply this
        simp
        simp at hx
        exact hx
    grind

  obtain ⟨i_1, h_i_1⟩ := exists_i1
  obtain ⟨i_2, h_i_2⟩ := exists_i2
  have diff_i_lt: h b (i_2 + 1) - h b i_1 < w * (a d) := by
    grw [h_montone_on b _ _ (b := i₀ + 3 * w * (j_0 + 1))]
    .
      apply LE.le.trans_lt ?_ h_j_0
      apply sub_le_sub_left
      apply h_montone_on b
      . simp
      . simp
        grind
      . grind
    . simp at h_i_2
      grind
    . simp
      simp at h_i_2
      grind
    . simp [m]

  apply Nonempty.intro
  exact {
    i_1 := i_1
    i_2 := i_2
    i_1_ge := by grind
    i_2_ge := by grind
    i_2_pos := by grind
    i_diff_mem := by grind
    h_diff_lt_w := diff_i_lt
    first_h_i := h_i_1.2
    second_h_i := h_i_2.2
  }

-- Controlled cover

variable {b : Module.Basis ι ℝ V}

structure GoodScalesData (b : Module.Basis ι ℝ V) where
  w: ℕ
  d: ℕ
  hw: 0 < w
  hd: 0 < d
  w_gt: 4 < w
  h_growth: growth_bound b d

noncomputable def GoodScales (data: GoodScalesData b) := Classical.choice (lemma_3_24 b data.w data.d data.hw data.hd data.h_growth)

noncomputable def R_1 (data: GoodScalesData b) := 2 * 16^(GoodScales data).i_1
noncomputable def R_2 (data: GoodScalesData b) := 16^(GoodScales data).i_2

-- TODO - does it matter than 'Metric.maximalSeparatedSet' uses 'R_1 < dist' instead of 'R_1 <= dist' ?
def X_j (data: GoodScalesData b) := Metric.maximalSeparatedSet (R_1 data) ((Metric.closedBall (1: G) (R_2 data)))
-- A collection of disjoint balls that cover the ball R_2
def B (data: GoodScalesData b) := (fun a => Metric.closedBall a (R_1 data)) '' (X_j data)
def B_half (data: GoodScalesData b) := (fun a => Metric.closedBall a (R_1 data / 2)) '' (X_j data)
def B_3 (data: GoodScalesData b) := (fun a => Metric.closedBall a (3 * R_1 data)) '' (X_j data)

lemma X_j_finite (data: GoodScalesData b): (X_j data).Finite := by
  apply Set.Finite.subset (finite_closed_ball (1 : G) (R_2 data))
  simp [X_j]
  apply Metric.maximalSeparatedSet_subset

lemma B_ball_injective_on (data: GoodScalesData b) (R: ℝ) (R_pos: 0 ≤ R) (hR: R ≤ R_1 data): Set.InjOn (fun a => Metric.closedBall a (R)) (X_j data) := by
  intro a ha b hb hab
  by_contra!
  simp at hab
  simp [X_j] at ha hb

  have sep := Metric.isSeparated_maximalSeparatedSet (ε := (R_1 data)) (A := (Metric.closedBall (1 : G) ↑(R_2 data)))
  specialize sep ha hb this

  have b_mem: b ∈ Metric.closedBall a ((R)) := by
    rw [hab]
    simp
    grind

  simp at b_mem
  simp [edist, PseudoMetricSpace.edist] at sep
  rw [dist_comm] at b_mem
  simp [dist] at b_mem
  norm_cast at b_mem
  rify at sep
  grw [b_mem] at sep
  norm_cast at sep
  grind

lemma B_covers_R2 (data: GoodScalesData b): Metric.closedBall 1 (R_2 data) ⊆ ⋃₀ (B data) := by
  by_contra!
  rw [Set.not_subset] at this
  obtain ⟨x, x_mem, x_not_mem⟩ := this

  -- Metric.maximalSeparatedSet_subset
  have card_le := Metric.encard_le_of_isSeparated (C := (X_j data) ∪ {x}) (ε := (R_1 data)) (A := ( (Metric.closedBall 1 (R_2 data)))) ?_ ?_ ?_
  .
    simp [X_j] at card_le
    rw [Set.encard_insert_of_notMem] at card_le
    rw [Set.Finite.encard_eq_coe_toFinset_card] at card_le
    . norm_cast at card_le

      grind
    .
      apply Set.Finite.subset (s := Metric.closedBall 1 (R_2 data))
      . apply finite_closed_ball
      . apply Metric.maximalSeparatedSet_subset
    .
      simp at x_not_mem
      simp only [B, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        not_lt, X_j] at x_not_mem

      by_contra!
      specialize x_not_mem x this
      simp [R_1] at x_not_mem
      --norm_cast at x_not_mem
      --grind
  .
    apply Set.union_subset
    . simp [X_j]
      grw [Metric.maximalSeparatedSet_subset]
    .
      simp at x_mem
      simpa using x_mem
  .
    simp
    apply Metric.IsSeparated.insert
    . simp [X_j]
      apply Metric.isSeparated_maximalSeparatedSet
    . intro y hy hxy
      simp [B] at x_not_mem
      specialize x_not_mem y hy
      simp [edist, PseudoMetricSpace.edist]
      simp [dist] at x_not_mem
      exact x_not_mem
  .
    rw [← lt_top_iff_ne_top]
    grw [Metric.packingNumber_le_encard_self]
    simp
    apply finite_closed_ball

lemma B_half_disjoint (data: GoodScalesData b): (B_half data).PairwiseDisjoint id := by
  simp [Set.pairwiseDisjoint_iff]
  intro X hX Y hY hXY
  obtain ⟨a, ha⟩ := hXY
  simp [B_half] at hX hY
  obtain ⟨x, x_mem, hx⟩ := hX
  obtain ⟨y, y_mem, hy⟩ := hY

  by_cases x_eq_y : x = y
  .
    rw [x_eq_y] at hx
    rw [← hx, ← hy]


  rw [← hx, ← hy] at ha
  simp at ha
  obtain ⟨a_dist_x, a_dist_y⟩ := ha

  simp [X_j] at x_mem
  have is_sep := Metric.isSeparated_maximalSeparatedSet (ε := ((R_1 data))) (A := Metric.closedBall (1: G) (R_2 data))

  unfold Metric.IsSeparated Set.Pairwise at is_sep
  have x_sep := is_sep x_mem y_mem x_eq_y
  simp at x_sep


  have x_y_dist_bad := dist_triangle x a y
  rw [dist_comm x a] at x_y_dist_bad
  grw [a_dist_x, a_dist_y] at x_y_dist_bad
  simp at x_y_dist_bad
  -- TODO - we need a lemma that edist = ↑dist
  simp [edist, PseudoMetricSpace.edist] at x_sep
  simp [dist] at x_y_dist_bad
  grind


-- Intersection multiplicity. See https://www.math.ucdavis.edu/~kapovich/EPR/kapovich_drutu.pdf page 24 for the definition
-- (search for 'multiplicity')
noncomputable def InterMult_f  (S: Set (Set G)) := (fun A => (Set.encard A).toNat) '' { A: Set (Set G) | A ⊆ S ∧ ⋂₀ A ≠ ∅ }
noncomputable def InterMult (S: Set (Set G)) := sSup (InterMult_f S)

lemma smul_origin_ball_subset (a: G) (r: ℝ): (MulOpposite.op a) • Metric.closedBall 1 r ⊆ Metric.closedBall a r := by
  intro x hx
  simp
  rw [Set.mem_smul_set] at hx
  obtain ⟨y, hy, x_eq⟩ := hx
  rw [← x_eq]
  simp [dist, WordDist]
  simp at hy
  simp [dist, WordDist] at hy
  exact hy

lemma ball_subset_smul_origin (a: G) (r: ℝ): Metric.closedBall a r ⊆ (MulOpposite.op a) • Metric.closedBall 1 r := by
  intro x hx
  simp at hx
  simpa using hx

lemma ball_smul_eq_origin (a: G) (r: ℝ): Metric.closedBall a r = (MulOpposite.op a) • Metric.closedBall 1 r := by
  ext x
  have foo := smul_origin_ball_subset a r
  have bar := ball_subset_smul_origin a r
  grind


lemma B_finite (data: GoodScalesData b): (B data).Finite := by
  simp [B]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_closed_ball

lemma B_half_finite (data: GoodScalesData b): (B_half data).Finite := by
  simp [B_half]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_closed_ball

noncomputable def B_finsets (data: GoodScalesData b): Finset (Finset G) := Finset.image ((fun a => (finite_closed_ball a (R_1 data )).toFinset)) (X_j_finite data).toFinset


-- TODO - combine this with 'B_half'
noncomputable def B_half_finsets (data: GoodScalesData b): Finset (Finset G) := Finset.image ((fun a => (finite_closed_ball a (R_1 data / 2)).toFinset)) (X_j_finite data).toFinset

lemma B_3_finite (data: GoodScalesData b): (B_3 data).Finite := by
  simp [B_3]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_closed_ball

-- Suprisingly, we can prove an upper bound with 4*R_1, rather than the 8*R_1 from the paper
lemma inter_mult_helper (data: GoodScalesData b): InterMult (B_3 data) * #(S ^ ((R_1 data) / 2)) ≤ #(S ^ (4 * (R_1 data))) := by
  classical
  apply Nat.mul_le_of_le_div
  unfold InterMult
  by_cases h_s: InterMult_f (B_3 data) = ∅
  . simp [h_s]
  .
    rw [csSup_le_iff]
    .
      intro n hn
      simp [InterMult_f] at hn
      obtain ⟨X, ⟨X_subset, X_inter⟩, X_card⟩ := hn
      rw [← X_card]
      have X_finite := Set.Finite.subset (B_3_finite data) X_subset
      rw [Set.Finite.encard_eq_coe_toFinset_card X_finite]
      simp
      rw [Nat.le_div_iff_mul_le]
      .
        have X_inner_nonempty: ∀ t ∈ X, ∃ a, a ∈ (X_j data) ∧ Metric.closedBall a (3 * R_1 data) = t := by
          intro t ht
          specialize X_subset ht
          simp [B_3] at X_subset
          exact X_subset

        rw [← closed_ball_eq_S_pow]
        rw [← smul_eq_mul]
        rw [← Finset.sum_const]

        grw [Finset.sum_le_sum (g := fun a => if ha: a ∈ X then #(finite_closed_ball (X_inner_nonempty a ha).choose ((R_1 data) / 2)).toFinset else 0)]
        .
          rw [← closed_ball_eq_S_pow]
          --rw [← Finset.sum_attach]
          rw [Finset.sum_dite]
          rw [← Finset.card_biUnion]
          .
            rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at X_inter
            obtain ⟨base, h_base⟩ := X_inter

            simp only [Finset.sum_const_zero, add_zero]
            nth_rw 2 [← Finset.card_smul_finset (MulOpposite.op base)]
            apply Finset.card_le_card
            rw [← Finset.coe_subset]
            rw [Finset.coe_smul_finset]
            conv =>
              rhs
              arg 2
              simp

            rw [← ball_smul_eq_origin]
            intro a ha
            simp at ha
            simp
            obtain ⟨c, hc, a_dist⟩ := ha
            .
              let q := (X_inner_nonempty c hc).choose
              grw [dist_triangle _ q]
              conv at a_dist =>
                arg 1
                arg 2
                equals q =>
                  simp [q]

              simp
              grw [a_dist]
              simp at h_base
              specialize h_base c hc

              have q_prop := (X_inner_nonempty c hc).choose_spec
              rw [← q_prop.2] at h_base
              simp at h_base
              rw [dist_comm] at h_base
              simp [q]
              grw [h_base]
              grind
          .
            rw [Finset.pairwiseDisjoint_iff]
            intro a _ b _ hab
            rw [Subtype.ext_iff]

            have from_b := B_half_disjoint data
            have a_prop := a.prop
            have b_prop := b.prop
            simp [-SetLike.coe_mem] at a_prop
            simp [-SetLike.coe_mem] at b_prop
            simp [B_half] at from_b

            let a_center := (X_inner_nonempty _ a_prop).choose
            let b_center := (X_inner_nonempty _ b_prop).choose
            obtain ⟨a_center_mem, a_eq⟩ := (X_inner_nonempty _ a_prop).choose_spec
            obtain ⟨b_center_mem, b_eq⟩ := (X_inner_nonempty _ b_prop).choose_spec


            rw [Set.pairwiseDisjoint_iff] at from_b
            simp only [Set.mem_image, id_eq, forall_exists_index, and_imp] at from_b
            simp at hab
            have inter_eq := from_b a_center a_center_mem (i := (Metric.closedBall a_center (↑(R_1 data) / 2) )) (?_) b_center b_center_mem (j := (Metric.closedBall b_center (↑(R_1 data) / 2) )) (?_) ?_
            .

              rw [← a_eq, ← b_eq]
              simp [a_center, b_center] at inter_eq
              apply B_ball_injective_on data (R_1 data / 2) (by grind) (by simp [R_1]) at inter_eq
              .
                simp [inter_eq]
              . grind
              . grind
            . rfl
            . rfl
            . simp [a_center, b_center]
              rw [← Finset.coe_nonempty] at hab
              simp at hab
              exact hab

        . intro y hy
          simp at hy
          simp only [hy, ↓reduceDIte]
          nth_rw 1 [← Finset.card_smul_finset (MulOpposite.op (X_inner_nonempty y hy).choose)]
          apply Finset.card_le_card
          intro a ha
          simp at ha
          simp
          rw [Finset.mem_smul_finset] at ha
          obtain ⟨z, z_mem, z_mul_eq⟩ := ha
          simp at z_mem
          rw [← z_mul_eq]
          simp
          simp [dist, WordDist]
          rw [← word_norm_inv]
          simp [dist, WordDist_one] at z_mem
          norm_cast
          grw [z_mem]
          grw [Nat.cast_div_le]
          simp

      . simp
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    .
      unfold BddAbove
      use (B_3 data).encard.toNat
      rw [mem_upperBounds]
      intro x hx
      simp [InterMult_f] at hx
      obtain ⟨a, b, x_eq⟩ := hx
      rw [← x_eq]
      apply ENat.toNat_le_toNat
      .
        apply Set.encard_le_encard
        grind
      . simp
        apply B_3_finite
    . rw [Set.nonempty_iff_ne_empty]
      grind

/-- Common step for Lemma 3.25 (a) and (b).

`h i = log (#(S ^ 16 ^ i) * det (Q_{16 ^ i}) ^ (dim V)⁻¹)` splits into a log-cardinality term
plus a determinant term. The determinant term is monotone in the scale (Proposition 3.22, via
`Q_R_lin_sub_pos_semi_def` and `matrix_det_montone`), so it is non-negative and can be dropped,
leaving a comparison of ball cardinalities that follows from `Finset.card_pow_mono`. -/
lemma log_card_pow_sub_le {j k m n : ℕ} (hj : i₀ ≤ j) (hjk : j ≤ k) (hm0 : m ≠ 0)
    (hm : m ≤ 16 ^ k) (hn : 16 ^ j ≤ n) :
    Real.log (#(S ^ m)) - Real.log (#(S ^ n)) ≤ h b k - h b j := by
  have card_pos : ∀ p : ℕ, (0:ℝ) < #(S ^ p) := by
    intro p
    simp
    apply Finset.Nonempty.pow
    exact S_nonempty
  have i₀_le_j : ((16:ℝ) ^ i₀) ≤ ((16 ^ j : ℕ) : ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hj
  have i₀_le_k : ((16:ℝ) ^ i₀) ≤ ((16 ^ k : ℕ) : ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (hj.trans hjk)
  have pd_j : (Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).PosDef := Q_R_matrix_pos_def_i₀ b _ i₀_le_j
  -- Proposition 3.22: the determinant is monotone in the scale, so the determinant part of
  -- `h k - h j` is non-negative and may be discarded.
  have det_le : (Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).det ≤ (Q_R_matrix b ((16 ^ k : ℕ) : ℝ)).det := by
    apply matrix_det_montone
    . exact pd_j
    . unfold Q_R_matrix
      rw [← map_sub]
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      apply Q_R_lin_sub_pos_semi_def
      push_cast
      exact pow_le_pow_right₀ (by norm_num) hjk
  have dim_nonneg : (0:ℝ) ≤ (dim V)⁻¹ := by
    simp [dim]
  have log_det_le :
      Real.log ((Q_R_matrix b ((16 ^ j : ℕ) : ℝ)).det ^ (dim V)⁻¹) ≤
        Real.log ((Q_R_matrix b ((16 ^ k : ℕ) : ℝ)).det ^ (dim V)⁻¹) :=
    Real.log_le_log (Real.rpow_pos_of_pos pd_j.det_pos _)
      (Real.rpow_le_rpow pd_j.det_pos.le det_le dim_nonneg)
  have card_le :
      Real.log ((#(S ^ m) : ℝ)) - Real.log ((#(S ^ n) : ℝ)) ≤
        Real.log ((#(S ^ 16 ^ k) : ℝ)) - Real.log ((#(S ^ 16 ^ j) : ℝ)) := by
    apply sub_le_sub
    . apply Real.log_le_log (card_pos m)
      norm_cast
      exact Finset.card_pow_mono hm0 hm
    . apply Real.log_le_log (card_pos (16 ^ j))
      norm_cast
      exact Finset.card_pow_mono (by positivity) hn
  simp only [h, f]
  rw [Real.log_mul, Real.log_mul]
  . linarith
  . exact ne_of_gt (card_pos (16 ^ j))
  . exact ne_of_gt (Real.rpow_pos_of_pos pd_j.det_pos _)
  . exact ne_of_gt (card_pos (16 ^ k))
  . exact ne_of_gt (Real.rpow_pos_of_pos
      (Q_R_matrix_pos_def_i₀ b _ i₀_le_k).det_pos _)

-- Lemma 3.25 (a)

lemma log_inter_mult_b3 (data: GoodScalesData b): InterMult (B_3 data) ≤ Real.exp (a data.d) := by
  by_cases mult_zero: InterMult (B_3 data) = 0
  . simp [mult_zero]
    positivity

  rw [← Real.log_le_iff_le_exp]
  have foo := inter_mult_helper data
  rw [← Nat.le_div_iff_mul_le] at foo
  grw [foo]
  .
    grw [Nat.cast_div_le]
    .
      rw [Real.log_div]
      .
        have bound := (GoodScales data).first_h_i
        grw [← bound]
        apply log_card_pow_sub_le (GoodScales data).i_1_ge (Nat.le_succ _)
        . simp [R_1]
        . rw [pow_succ]
          simp [R_1]
          omega
        . simp [R_1]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . norm_cast
        rw [Finset.card_eq_zero]
        rw [← ne_eq, ← Finset.nonempty_iff_ne_empty]
        apply Finset.Nonempty.pow
        simp [S_nonempty]
    . simp
      refine ⟨?_, ?_⟩
      . apply Finset.Nonempty.pow
        simp [S_nonempty]
      .
        apply Finset.card_pow_mono
        . simp [R_1]
        . grind
  .
    simp
    apply Finset.Nonempty.pow
    simp [S_nonempty]
  . simp
    grind

#print axioms inter_mult_helper
#print axioms log_inter_mult_b3


noncomputable def B_r (r: ℝ) := (finite_closed_ball 1 r).toFinset
noncomputable def B_c_r (g: G) (r: ℝ) := (finite_closed_ball g r).toFinset

-- Lemma 3.25 (b)
lemma card_B_le_exp_wa (data: GoodScalesData b): #(B_finite data).toFinset < Real.exp (data.w * (a data.d)) := by
  --rw [← Nat.card_eq_card_finite_toFinset]
  have B_union := Finset.card_biUnion (s := (B_half_finsets data)) (t := id) ?_
  .
    simp at B_union
    have sum_le := Finset.sum_eq_card_nsmul (f := fun (u: Finset G) => #u) (s := B_half_finsets data) (b := #(S ^ (R_1 data / 2))) ?_
    .
      rw [← Nat.card_eq_card_finite_toFinset]
      simp [B]
      grw [Set.ncard_image_le (hs := by apply X_j_finite)]
      conv at sum_le =>
        rhs
        lhs
        simp [B_half_finsets]
        rw [Finset.card_image_iff.mpr (by
          have foo := B_ball_injective_on data (R_1 data / 2) (by grind) (by simp [R_1])
          conv =>
            rhs
            equals (X_j data) =>
              simp

          intro a ha b hb hab
          specialize foo ha hb
          specialize foo (by simpa using hab)
          exact foo
        )]
      simp at sum_le
      rw [eq_comm] at sum_le
      apply le_of_eq at sum_le
      rw [← Nat.le_div_iff_mul_le (by simp; apply Finset.Nonempty.pow; simp [S_nonempty])] at sum_le
      conv at sum_le =>
        lhs
        equals (X_j data).ncard =>
          rw [Set.ncard_eq_toFinset_card (hs := by apply X_j_finite)]

      grw [sum_le]
      rw [← B_union]
      grw [Finset.card_le_card (t := (finite_closed_ball (1: G) ↑(2 * (R_2 data))).toFinset)]
      .
        grw [Nat.cast_div_le]
        rw [card_closed_ball_eq]
        .
          rw [← Real.log_lt_iff_lt_exp]
          .
            apply lt_of_le_of_lt ?_  ((GoodScales data).h_diff_lt_w)
            rw [Real.log_div (by simp; grind [S_nonempty]) (by simp; grind [S_nonempty])]
            apply log_card_pow_sub_le (GoodScales data).i_1_ge
            . -- `i_2 - i_1 > w ≥ 0` forces `i_1 < i_2`
              have hdiff := (GoodScales data).i_diff_mem
              simp [Set.mem_Ioo] at hdiff
              omega
            . simp [R_2]
            . rw [pow_succ]
              simp [R_2]
              omega
            . simp [R_1]
          .
            apply div_pos
            . simp
              apply Finset.Nonempty.pow
              simp [S_nonempty]
            . simp
              apply Finset.Nonempty.pow
              simp [S_nonempty]
      .
        intro a ha
        simp at ha
        obtain ⟨x, x_mem, hx⟩ := ha
        simp [B_half_finsets] at x_mem
        simp
        obtain ⟨c, hc, x_eq⟩ := x_mem
        grw [dist_triangle _ c]
        rw [← x_eq] at hx
        simp at hx
        grw [hx]
        simp [X_j] at hc
        grw [Metric.maximalSeparatedSet_subset] at hc
        simp at hc
        grw [hc]
        simp [R_1, R_2]
        have i_1_le:  (GoodScales data).i_1 ≤  (GoodScales data).i_2 := by
          have foo :=  (GoodScales data).i_diff_mem
          simp at foo
          grind
        grw [i_1_le]
        .
          grind
        . simp
    .
      intro b hb
      simp
      simp [B_half_finsets] at hb
      obtain ⟨c, c_mem, b_eq⟩ := hb
      rw [← b_eq]
      rw [← Set.toFinite_toFinset]
      rw [← Nat.card_eq_card_finite_toFinset]
      rw [ball_smul_eq_origin]

      -- TODO - make the various finite/fintype/card conversion less awful
      conv =>
        lhs
        equals (MulOpposite.op c • (Metric.closedBall (1: G) (↑(R_1 data) / 2))).ncard =>
          simp
          have b_finite := finite_closed_ball c ↑((R_1 data) / 2)
          rw [Set.ncard_eq_toFinset_card']
          simp


      simp [-Metric.smul_closedBall]
      conv =>
        lhs
        equals #(finite_closed_ball 1 ↑((R_1 data) / 2)).toFinset =>
          simp
          have b_finite := finite_closed_ball 1 ↑((R_1 data) / 2)
          rw [Set.ncard_eq_toFinset_card']
          simp [R_1]
      rw [card_closed_ball_eq]


  .
    -- TODO - there must be a less horrendous way of dealing with Finset here
    simp [B_half_finsets]
    have foo := B_half_disjoint data
    simp [B_half] at foo
    unfold Set.PairwiseDisjoint Set.Pairwise
    unfold Set.PairwiseDisjoint Set.Pairwise at foo
    simp
    simp at foo
    intro a ha b hb hab p hp_a hp_b
    simp at hp_a hp_b
    specialize foo a ha b hb hab hp_a hp_b
    simpa using foo


noncomputable def f_avg (R: ℝ) (f : G → ℝ) := (#((finite_closed_ball 1 R).toFinset) : ℝ)⁻¹ * ∑ y ∈ (finite_closed_ball 1 R).toFinset, f y
noncomputable def f_avg_c (g: G) (R: ℝ) (f : G → ℝ) := (#((finite_closed_ball 1 R).toFinset) : ℝ)⁻¹ * ∑ y ∈ B_c_r g R, f y

-- (#S : ℝ)⁻¹ *
-- The gradient-squared for the *right* Cayley graph (edges `{x, x * s}`), as in Vikman Def 2.12.
-- This is the orientation used internally by `poincare_inequality`, whose proof translates
-- geodesics on the left (`x * γ z i`). It is invariant under left translation, and so is NOT
-- the orientation compatible with our right-invariant `WordDist x y = WordNorm (y * x⁻¹)`.
noncomputable def deriv_sq_R (f: G → ℝ) (x: G) := ∑ s ∈ S, (f (x * s) - f x)^2

-- The gradient-squared for the *left* Cayley graph (edges `{x, s * x}`).
-- Note that, as with `Harmonic`, our multiplication order is swapped relative to the paper:
-- `f (s * x)` instead of `f (x * s)`. This is what makes it agree with `MeasureTheory.convolution`
-- (see the note above `Conv` in `Defs.lean`) and with the right-invariant `WordDist`, so that
-- the balls `B_c_r j r = B_r r * j` are right translates and no `MulOpposite` leaks into the
-- convolution terms. `deriv_sq` is invariant under right translation:
-- `deriv_sq (f ∘ (· * j)) x = deriv_sq f (x * j)`, which is what Lemma 3.25 (c) needs.
noncomputable def deriv_sq (f: G → ℝ) (x: G) := ∑ s ∈ S, (f (s * x) - f x)^2

-- Reindexing `s ↦ s⁻¹` over the symmetric generating set `S` turns a right-gradient of
-- `f ∘ (·⁻¹)` into a left-gradient of `f` at the inverted point.
lemma deriv_sq_R_inv_comp (f: G → ℝ) (x: G):
    deriv_sq_R (fun y => f y⁻¹) x = deriv_sq f x⁻¹ := by
  unfold deriv_sq_R deriv_sq
  apply Finset.sum_nbij' (i := fun s => s⁻¹) (j := fun s => s⁻¹) <;>
    simp +contextual [hGS.has_inv, mul_inv_rev]

lemma three_term_cs (a b: ℝ) (n: Type*) {s: Finset n} (f: n → ℝ): a + (∑ x ∈ s, f x) + b ≤ √(a^2 + (∑ x ∈ s, (f x)^2) + b^2) * √(2 + #(s)) := by
  conv =>
    lhs
    equals ∑ x ∈ (s.disjSum {a}).disjSum {b}, (x.elim (fun y => y.elim f id) id) * 1 =>
      simp
      rw [add_comm]

  grw [Real.sum_mul_le_sqrt_mul_sqrt]
  simp
  grind


lemma ball_x_one_subset (x: G): (Metric.closedBall x 1) ⊆ ((x) • S) ∪ ((MulOpposite.op x • S))  := by
  intro a ha
  simp
  simp at ha
  rw [Set.mem_smul_set]
  simp [dist, WordDist] at ha
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod_self (x * a⁻¹)
  simp [ProdS] at l_prod
  by_cases l_len_eq: l.length = 0
  .
    have l_eq: l = [] := by grind
    simp [l_eq] at l_prod
    rw [eq_comm, mul_inv_eq_one] at l_prod
    left
    use 1
    simp [one_mem]
    grind
  .
    rw [← l_len] at ha
    have l_len_one: l.length = 1 := by grind
    rw [List.length_eq_one_iff] at l_len_one
    obtain ⟨s, hs⟩ := l_len_one
    simp [hs] at l_prod
    right
    use s⁻¹
    simp
    rw [eq_comm, mul_inv_eq_iff_eq_mul] at l_prod

    rw [l_prod]
    refine ⟨?_, ?_⟩
    .
      rw [← Finset.mem_inv']
      rw [← S_eq_Sinv]
      simp
    .
      simp [l_prod]

  -- . intro ha
  --   simp at ha
  --   simp
  --   cases ha
  --   .
  --     rename_i ha
  --     rw [Set.mem_smul_set] at ha
  --     obtain ⟨s, s_mem, hs⟩ := ha
  --     rw [← hs]
  --     rw [dist_comm]
  --     simp [dist, WordDist]
  --     grw [dist_word_mul_le]
  --     .
  --     simp [dist, WordDist]
  --     simp
  --     -- TODO make this a lemma in Defs.lean
  --     have s_norm := word_norm_le s [⟨s, s_mem⟩] (by simp [ProdS])
  --     simpa using s_norm

lemma le_of_sub_eq (a b c: ℝ) (ha: a = b - c) (hc: 0 ≤ c): a ≤ b := by
  grind

lemma double_ball_sum (R: ℕ) (hR: 0 < R) (f: G → ℝ) (hf: ∀ g, 0 ≤ f g): ∑ x ∈ B_r (↑(R - 1)), ∑ y ∈ (Metric.closedBall x 1), f y ≤ 2 * #S * ∑ x ∈ B_r R, f x := by
  classical


  grw [Finset.sum_le_sum (g := fun x =>  ∑ y ∈ ((x) • S) ∪ ((MulOpposite.op x • S)), f y)]
  .
    have union_sub (x: G) := Finset.sum_union_inter (f := f) (s₁ := x • S) (s₂ := (MulOpposite.op x • S))
    simp_rw [← eq_sub_iff_add_eq] at union_sub
    have foo (x) := le_of_sub_eq _ _ _ (union_sub x) (by
      apply Finset.sum_nonneg
      simp [hf]
    )
    grw [Finset.sum_le_sum (h := fun x hx => foo x)]


    simp_rw [← Finset.image_smul]
    conv =>
      lhs
      arg 2
      intro x
      rw [Finset.sum_image (by simp)]
      rw [Finset.sum_image (by simp)]

    have card_le (i: G) : #({a ∈ B_r ↑(R - 1) ×ˢ S | a.1 • a.2 = i}) ≤ #S := by
      apply Finset.card_le_card_of_injOn (f := fun p => p.1⁻¹ * i)
      . intro a ha
        simp at ha
        simp
        simp [← ha.2]
        grind
      . intro a ha b hb hab
        simp at hab
        simp at ha
        simp at hb
        have ha_2 := ha.2
        have hb_2 := hb.2
        rw [Prod.ext_iff]
        rw [← ha_2] at hb_2
        simp [hab] at hb_2
        grind

    have card_le_rev (i: G) : #({a ∈ B_r ↑(R - 1) ×ˢ S | a.2 * a.1 = i}) ≤ #S := by
      apply Finset.card_le_card_of_injOn (f := fun p => i * p.1⁻¹)
      . intro a ha
        simp at ha
        simp
        simp [← ha.2]
        grind
      . intro a ha b hb hab
        simp at hab
        simp at ha
        simp at hb
        have ha_2 := ha.2
        have hb_2 := hb.2
        rw [Prod.ext_iff]
        rw [← ha_2] at hb_2
        simp [hab] at hb_2
        grind

    simp_rw [Finset.sum_add_distrib]
    rw [← Finset.sum_product']
    rw [← Finset.sum_product']
    simp_rw [Finset.sum_comp]
    grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r R)]
    .
      grw [Finset.sum_le_sum (g := fun i => #S • f i)]
      .
        simp
        rw [← Finset.mul_sum]
        rw [add_comm]
        grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r R)]
        .
          grw [Finset.sum_le_sum (g := fun i => #S • f i)]
          .
            simp
            rw [← Finset.mul_sum]
            rw [← mul_add]
            grind
          .
            intro i hi
            simp
            simp at card_le_rev
            -- TODO - why doesn't grw work here
            apply mul_le_mul
            . simp
              apply card_le_rev
            . simp
            . apply hf
            . simp
        .
          rw [Finset.image_subset_iff]
          intro x hx
          simp at hx
          simp [B_r, dist, WordDist_one]
          grw [word_norm_mul_le]
          simp [B_r, dist, WordDist_one] at hx
          grw [hx.1]
          have norm_s := word_norm_le x.2 [⟨x.2, hx.2⟩] (by simp [ProdS])
          grw [norm_s]
          simp [hR]
          grind
        . intros
          apply mul_nonneg
          . simp
          . apply hf
      . intro i hi
        grw [card_le]
        apply hf


    . rw [Finset.image_subset_iff]
      intro x hx
      simp at hx
      simp [B_r, dist, WordDist_one]
      grw [word_norm_mul_le]
      simp [B_r, dist, WordDist_one] at hx
      grw [hx.1]
      have norm_s := word_norm_le x.2 [⟨x.2, hx.2⟩] (by simp [ProdS])
      grw [norm_s]
      simp [hR]
    . intros
      simp
      apply mul_nonneg
      . simp
      . apply hf
  . intro i hi
    grw [Finset.sum_le_sum_of_subset_of_nonneg]
    .
      simp
      apply ball_x_one_subset
    . intros
      apply hf


-- TODO - get rid of some lemmas, since mathlib already has Metric.smul_closedBall defined
lemma B_c_r_eq_smul (a: G) (r: ℝ): B_c_r a r = (MulOpposite.op a) • B_r r := by
  rw [B_c_r, B_r]
  rw [← Finset.coe_inj]
  simp?

-- lemma B_c_r_eq_smul_normal (a: G) (r: ℝ): a • B_r r ⊆ B_c_r a r := by
--   rw [B_c_r, B_r]
--   intro x hx
--   simp
--   simp at hx
--   rw [Finset.mem_smul_finset] at hx
--   obtain ⟨k, k_mem, k_eq⟩ := hx
--   rw [← k_eq]
--   simp [dist, WordDist]
--   rw [← Finset.coe_inj]
--   simp

-- Theorem 3.20
set_option maxHeartbeats 3500000 in
lemma poincare_inequality (R: ℕ) (f: G → ℝ): ∑ x ∈ (B_r (R - 1)), |f x - (f_avg (R - 1) f)|^2 ≤
    16 * R^2 * #S * (#(B_r (2 * R - 2))) / #(B_r (R - 1)) * ∑ x ∈ (B_r (3 * R)), deriv_sq_R f x := by

  by_cases R_nonpos: R = 0
  .
    simp [R_nonpos, f_avg, B_r]

  let δ_f (x: G) := ∑ x ∈ (finite_closed_ball x 1).toFinset, deriv_sq_R f x

  have f_sub_le (x: G): |f x - f_avg (R - 1) f| ≤ √((#((B_r (R - 1))) : ℝ)⁻¹ * (∑ y ∈ (B_r (R - 1)), (f x - f y)^2)) := by
    rw [f_avg]
    conv =>
      lhs
      arg 1
      arg 1
      equals (#((B_r (↑R - 1))) : ℝ)⁻¹ * ∑ y ∈ (B_r (↑R - 1)), f x =>
        simp
        rw [inv_mul_cancel_left₀]
        simp [B_r]
        rw [Fintype.card_eq_zero_iff]
        simp
        grind

    rw [B_r]
    rw [← mul_sub]
    rw [abs_mul]
    rw [← Finset.sum_sub_distrib]
    grw [Finset.abs_sum_le_sum_abs]
    conv =>
      lhs
      rhs
      arg 2
      intro i
      equals |f x - f i| * 1 => simp
    grw [Real.sum_mul_le_sqrt_mul_sqrt]
    simp [Real.sqrt_eq_rpow]
    rw [← Real.rpow_neg_one]
    rw [mul_comm]
    rw [mul_assoc]
    rw [← Real.rpow_add]
    .
      norm_num
      simp
      rw [Real.mul_rpow]
      .
        field_simp
        rw [← Real.rpow_mul]
        .
          simp
        . positivity
      . positivity
      . positivity

    . simp
      rw [Fintype.card_pos_iff]
      simp
      use 1
      simp
      grind


  let γ (z: G) (i: ℕ) := ((word_norm_prod_self z).choose.take i).unattach.prod
  have gamma_zero (z: G): γ z 0 = 1 := by simp [γ]
  have gamma_norm (z: G): γ z (WordNorm z) = z := by
    simp [γ]
    obtain ⟨prod, len_eq⟩ := (word_norm_prod_self z).choose_spec
    simp [ProdS] at prod
    conv =>
      arg 1
      pattern (WordNorm z)
      rw [← len_eq]

    simp
    exact prod

  have gamma_i_norm_le (z: G) (i: ℕ): WordNorm (γ z i) ≤ i := by
    simp [γ]

    have i_le := word_norm_le ((word_norm_prod_self z).choose.take i).unattach.prod ((word_norm_prod_self z).choose.take i) (by simp [ProdS])
    grw [List.length_take_le] at i_le
    exact i_le



  have gamma_sum (z: G) (hz: z ∈ B_r (2*R - 2)): ∑ x ∈ B_r (R - 1), ∑ i ∈ Finset.range (WordNorm z), δ_f (x * (γ z i)) ≤ 2 * R * ∑ x ∈ B_r (3*R - 1), δ_f x := by

    rw [← Finset.sum_product']
    rw [Finset.sum_comp]
    simp
    grw [Finset.sum_le_sum (g := fun a => (((2 * R) : ℝ) * (δ_f a)))]
    .
      rw [← Finset.mul_sum]
      grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r (3*R - 1))]
      .
        intro p hp
        simp at hp
        obtain ⟨a, b, ⟨a_mem, b_lt⟩, p_eq⟩ := hp
        rw [← p_eq]
        simp [B_r, dist, WordDist_one]
        grw [word_norm_mul_le]
        simp [B_r, dist, WordDist_one] at a_mem
        simp [B_r, dist, WordDist_one] at hz
        simp
        grw [a_mem]
        grw [gamma_i_norm_le]
        grw [b_lt]
        grw [hz]
        grind
      . intro p hp _
        simp [δ_f, deriv_sq_R]
        positivity
    .
      intro b hb
      simp at hb
      obtain ⟨x, n, ⟨x_mem, n_lt⟩, b_eq⟩ := hb
      grw [Finset.card_le_card (t := (Finset.range (2 * R)).image (fun n => (b * ((γ z n)⁻¹), n)))]
      .
        grw [Finset.card_image_le]
        . simp
        . simp [δ_f, deriv_sq_R]
          positivity
      .
        simp [δ_f, deriv_sq_R]
        positivity
      .
        intro p hp
        simp at hp
        simp
        use p.2
        refine ⟨?_, ?_⟩
        .

          by_contra!
          grw [hp.1.2] at this
          simp [B_r, dist, WordDist_one] at hz
          conv at hz =>
            rhs
            equals ↑(2*R - 2) =>
              rw [Nat.cast_sub]
              simp
              grind

          norm_cast at hz
          grind
        .
          ext
          . simp [← hp.2]
          . simp



  have diff_le_delta_sum (x y: G) (hx: x ∈ B_r (R - 1)) (hy: y ∈ B_r (R - 1)): |f y - f x| ≤ √((2 * R) * (∑ i ∈ Finset.range (WordNorm (x⁻¹ * y)), δ_f (x * γ (x⁻¹ * y) i))) := by



    have inv_prod_le: WordNorm (x⁻¹ * y) ≤ 2*R - 2 := by
      grw [word_norm_mul_le]
      rw [← word_norm_inv]
      simp [B_r, dist, WordDist_one] at hx hy
      conv at hx =>
        rhs
        equals ↑(R - 1) =>
          rw [Nat.cast_sub]
          simp
          grind
      conv at hy =>
        rhs
        equals ↑(R - 1) =>
          rw [Nat.cast_sub]
          simp
          grind
      norm_cast at hx hy
      grw [hx, hy]
      grind

    have root_le_R: √(WordNorm (x⁻¹ * y)) ≤ √(2*R) := by
      rw [Real.sqrt_le_sqrt_iff]
      . norm_cast
        grw [inv_prod_le]
        simp
      . simp


    conv =>
      lhs
      equals |(f (x * γ (x⁻¹ * y) (WordNorm (x⁻¹ * y)))) - f (x * γ (x⁻¹ * y) 0)| =>
        simp [gamma_zero, gamma_norm]

    rw [← Finset.sum_range_sub (n := WordNorm (x⁻¹ * y)) (f := fun i => f (x * γ (x⁻¹ * y) i))]
    grw [Finset.abs_sum_le_sum_abs]
    conv =>
      lhs
      arg 2
      intro i
      rw [← mul_one (a := |_|)]


    grw [Real.sum_mul_le_sqrt_mul_sqrt]
    simp
    grw [root_le_R]


    have sum_le_delta: ∑ x_1 ∈ Finset.range (WordNorm (x⁻¹ * y)), (f (x * γ (x⁻¹ * y) x_1) - f (x * γ (x⁻¹ * y) (x_1 + 1))) ^ 2 ≤ ∑ n ∈ Finset.range (WordNorm (x⁻¹ * y)), δ_f (x * (γ (x⁻¹ * y) n)) := by
      apply Finset.sum_le_sum
      intro n hn
      simp [δ_f, deriv_sq_R]
      rw [← Finset.add_sum_erase (a := (x * γ (x⁻¹ * y) n))]
      .
        apply le_add_of_le_of_nonneg
        .
          let s := (word_norm_prod_self (x⁻¹ * y)).choose[n]?.getD ⟨1, one_mem⟩
          rw [← Finset.add_sum_erase (a := s.val) (h := by simp)]
          apply le_add_of_le_of_nonneg
          .
            rw [sub_sq_comm]
            conv =>
              rhs
              lhs
              arg 1
              arg 1
              equals x * γ (x⁻¹ * y) (n + 1) =>

                rw [mul_assoc, mul_left_cancel_iff]
                simp [γ, s]
                -- TODO - we can probably use hn instead of this case split
                by_cases n_add_lt: (n) < (word_norm_prod_self (x⁻¹ * y)).choose.length
                .
                  simp [n_add_lt]
                  rw [List.take_add_one]
                  simp
                  rw [getElem?_pos]
                  . simp
                  . grind
                .
                  simp [n_add_lt]
                  rw [List.take_add_one]
                  simp
                  rw [getElem?_neg]
                  . simp
                  . grind
          . positivity
        . positivity
      . simp [dist, WordDist, word_norm_one]



    simp_rw [sub_sq_comm]
    grw [sum_le_delta]
    rw [mul_comm]
    simp

  conv at f_sub_le =>
    intro x
    rw [Real.le_sqrt (by
      simp
    ) (by
      positivity
    )]
  grw [Finset.sum_le_sum (h := fun x hx => f_sub_le x)]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  rw [← Finset.mul_sum]
  rw [inv_mul_le_iff₀ (by norm_cast; simp; simp [B_r]; grind)]
  conv at diff_le_delta_sum =>
    intro x y hx hy
    rw [Real.le_sqrt (by simp) (by
      simp [δ_f, deriv_sq_R];
      positivity
    )]
  simp_rw [sq_abs] at diff_le_delta_sum
  grw [Finset.sum_le_sum (h := fun a ha => diff_le_delta_sum a.2 a.1 (by
    simp at ha
    simp [B_r]
    simp [B_r] at ha
    grind
  )
  (by
    grind
  ))]
  simp_rw [← Finset.mul_sum]
  rw [mul_comm]
  rw [← le_div_iff₀ (by simp; grind)]
  rw [Finset.sum_product]
  simp only []
  --rw [Finset.sum_comm]
  --simp_rw [Finset.sum_comp]
  rw [Finset.sum_comm]
  -- TODO - use gcongr here
  grw [Finset.sum_le_sum (g := fun z => ∑ x ∈ B_r (2*R - 2), ∑ i ∈ Finset.range (WordNorm x), δ_f (z * γ x i))]
  .
    rw [Finset.sum_comm]
    grw [Finset.sum_le_sum (h := gamma_sum)]
    simp [δ_f]
    have b_card_ne : #(B_r (↑R - 1)) ≠ 0 := by
      simp [B_r]
      rw [Fintype.card_eq_zero_iff]
      simp
      grind
    have b_card_two_ne: #(B_r (2 * (↑R - 1))) ≠ 0 := by
      simp [B_r]
      rw [Fintype.card_eq_zero_iff]
      simp
      grind
    field_simp
    norm_num
    conv =>
      lhs
      rhs
      arg 1
      arg 1
      equals ↑(R*3 - 1) =>
        rw [Nat.cast_sub]
        simp
        grind
    grw [double_ball_sum]
    .
      norm_cast


      have four_le: (4: ℝ) ≤ 8 := by
        grind
      grw [four_le]
      simp [deriv_sq_R]
      ring
      simp
      simp [deriv_sq_R]
      positivity
    . simp
      grind
    . intro g
      simp [deriv_sq_R]
      positivity

  . intro a ha
    rw [Finset.sum_comp (g := fun y => a⁻¹ * y) (f := fun x => ∑ x_1 ∈ Finset.range (WordNorm (x)), δ_f (a * γ (x) x_1))]
    grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r (2*R - 2))]
    .
      simp_rw [inv_mul_eq_iff_eq_mul]
      simp_rw [Finset.card_filter]
      simp
      apply Finset.sum_le_sum
      intro x hx
      split_ifs
      . simp
      . simp [δ_f, deriv_sq_R]
        positivity
    .
      rw [Finset.image_subset_iff]
      intro x hx
      simp [B_r, dist, WordDist_one]
      simp [B_r, dist, WordDist_one] at ha hx
      grw [word_norm_mul_le]
      rw [← word_norm_inv]
      simp
      grw [ha, hx]
      grind
    .
      intros
      simp [δ_f, deriv_sq_R]
      positivity


#print axioms poincare_inequality

-- `B_r` is centred at `1`, so it is closed under inversion (`word_norm_inv`).
lemma mem_B_r_inv (r: ℝ) (x: G): x⁻¹ ∈ B_r r ↔ x ∈ B_r r := by
  simp [B_r, dist, WordDist_one, ← word_norm_inv]

lemma sum_B_r_inv (r: ℝ) (g: G → ℝ): ∑ x ∈ B_r r, g x⁻¹ = ∑ x ∈ B_r r, g x := by
  apply Finset.sum_nbij' (i := fun x => x⁻¹) (j := fun x => x⁻¹) <;>
    simp +contextual [mem_B_r_inv]

lemma f_avg_inv (r: ℝ) (f: G → ℝ): f_avg r (fun y => f y⁻¹) = f_avg r f := by
  unfold f_avg
  rw [show (finite_closed_ball (1: G) r).toFinset = B_r r from rfl, sum_B_r_inv]

-- Theorem 3.20, restated for the *left* Cayley graph. Rather than mirroring the (long) proof of
-- `poincare_inequality`, we conjugate it by the inversion `x ↦ x⁻¹`: this is a bijection of every
-- `B_r r` (`mem_B_r_inv`) and carries `deriv_sq_R` to `deriv_sq` (`deriv_sq_R_inv_comp`).
lemma poincare_inequality_left (R: ℕ) (f: G → ℝ): ∑ x ∈ (B_r (R - 1)), |f x - (f_avg (R - 1) f)|^2 ≤
    16 * R^2 * #S * (#(B_r (2 * R - 2))) / #(B_r (R - 1)) * ∑ x ∈ (B_r (3 * R)), deriv_sq f x := by
  have poincare := poincare_inequality R (fun y => f y⁻¹)
  rw [f_avg_inv] at poincare
  rw [show (∑ x ∈ B_r ((R: ℝ) - 1), |f x⁻¹ - f_avg ((R: ℝ) - 1) f| ^ 2)
      = ∑ x ∈ B_r ((R: ℝ) - 1), |f x - f_avg ((R: ℝ) - 1) f| ^ 2 from
    sum_B_r_inv _ (fun x => |f x - f_avg ((R: ℝ) - 1) f| ^ 2)] at poincare
  rw [show (∑ x ∈ B_r (3 * (R: ℝ)), deriv_sq_R (fun y => f y⁻¹) x)
      = ∑ x ∈ B_r (3 * (R: ℝ)), deriv_sq f x from by
    rw [← sum_B_r_inv (3 * (R: ℝ)) (fun x => deriv_sq f x)]
    exact Finset.sum_congr rfl (fun x _ => deriv_sq_R_inv_comp f x)] at poincare
  exact poincare

#print axioms poincare_inequality_left

lemma card_B_r_eq (R: ℕ): #(B_r R) = #(S ^ R) := by
  rw [← card_closed_ball_eq]
  simp [B_r]

lemma lemma_3_25_poincare (data: GoodScalesData b) (j: (X_j data)) (f: G → ℝ): ∑ x ∈ (B_c_r j (R_1 data )), |f x - (f_avg_c j (R_1 data ) f)|^2 ≤
    16 * (R_1 data + 1)^2 * #S * (Real.exp (a data.d)) * ∑ x ∈ (B_c_r j (3 * (R_1 data + 1))), deriv_sq f x := by

  have R_1_pos: 0 < R_1 data := by
    simp [R_1]


  -- `deriv_sq` is invariant under right translation, and `B_c_r j r` is the right translate
  -- `B_r r * j`, so the left-handed Poincaré inequality is the one that transfers here.
  have poincare := poincare_inequality_left (R_1 data + 1) (f ∘ (fun g => g * j.val))

  simp at poincare
  rw [← Finset.sum_image (f := fun x => ((f (x)) - f_avg (↑(R_1 data)) (f ∘ fun g ↦ g * j)) ^ 2) (by simp)] at poincare
  conv at poincare =>
    lhs
    arg 1
    equals B_c_r j ((R_1 data) ) =>
      rw [B_c_r_eq_smul]
      rw [← Finset.image_smul]
      simp


  conv at poincare =>
    lhs
    arg 2
    intro x
    arg 1
    rhs
    equals f_avg_c j ((R_1 data) ) f =>
      simp [f_avg_c, f_avg]
      rw [B_c_r_eq_smul]
      rw [← Finset.image_smul]
      rw [Finset.sum_image]
      .
        simp
        left
        simp [B_r]
      . simp

  simp_rw [sq_abs]
  grw [poincare]
  clear poincare

  have vol_frac_le: ↑(#(B_r (2 * (↑(R_1 data) + 1) - 2))) / ↑(#(B_r ↑(R_1 data))) ≤ Real.exp (a data.d) := by
    -- by_cases R_one: (R_1 data) = 1
    -- . simp [B_r, R_one]
    --   simp [a]
    --   norm_cast

    --   positivity



    rw [← Real.log_le_iff_le_exp]
    . rw [Real.log_div]
      .
        have sub_eq: 2 * (R_1 data: ℝ) - 2 = ↑(2*(R_1 data) - 2) := by
          rw [Nat.cast_sub]
          .
            simp
          . grind

        have sub_one_eq: (R_1 data: ℝ) - 1 = ↑(R_1 data - 1) := by
          rw [Nat.cast_sub]
          . simp
          . grind


        --rw [sub_eq, sub_one_eq,card_B_r_eq]
        rw [card_B_r_eq]
        conv =>
          lhs
          arg 1
          arg 1
          arg 1
          arg 1
          arg 1
          equals ↑(2 * ((R_1 data) + 1) - 2) =>
            simp
        rw [card_B_r_eq]
        grw [log_card_pow_sub_le (b := b) (k := (GoodScales data).i_1 + 1) (j := (GoodScales data).i_1)]
        .
          grw [(GoodScales data).first_h_i]
        .
          apply (GoodScales data).i_1_ge
        . simp
        . simp
          grind
        . simp
          have h_i_1 := (GoodScales data).i_1_ge
          simp [i₀, R'] at h_i_1
          simp [R_1]
          ring
          grind
        .
          simp [R_1]
          -- norm_num
          -- ring
          -- grind
      . simp only [B_r, Set.toFinite_toFinset, ne_eq, Nat.cast_eq_zero]
        apply Finset.card_ne_zero_of_mem (a := 1)
        simp [R_1]
        --norm_cast
      . simp only [B_r, Set.toFinite_toFinset, ne_eq, Nat.cast_eq_zero]
        apply Finset.card_ne_zero_of_mem (a := 1)
        simp [R_1]
        --norm_cast
    . apply mul_pos
      . simp only [B_r, Set.toFinite_toFinset]
        norm_cast
        rw [Finset.card_pos]
        use 1
        simp [R_1]
        --norm_cast
      .
        simp [-Set.toFinset_card]
        use 1
        simp [B_r, R_1]
        --norm_cast
  .
    rw [mul_div_assoc]
    norm_num
    grw [vol_frac_le]
    . simp

      conv =>
        lhs
        rhs
        equals  ∑ x ∈ B_c_r j (3 * ↑(R_1 data + 1)), deriv_sq f x =>
          --simp [deriv_sq]

          --simp_rw [← Finset.sum_comp]
          rw [B_c_r_eq_smul]
          rw [← Finset.image_smul]
          rw [Finset.sum_image (by simp)]
          norm_cast
          apply congrArg
          ext x
          simp [deriv_sq]
          group
      simp
    . simp [deriv_sq]
      positivity

-- Estimating functions relative to cover

noncomputable def J (data: GoodScalesData b) := #((X_j_finite data).toFinset)
noncomputable def phi (data: GoodScalesData b): V →ₗ[ℝ] EuclideanSpace ℝ (B_finsets data) := {
  toFun := fun u => WithLp.toLp 2 (fun (j: B_finsets data) => ((#j.val : ℝ)⁻¹) * ∑ x ∈ j.val, u.val x)
  map_add' := by
    intro x y
    simp
    simp_rw [Finset.sum_add_distrib]
    simp_rw [mul_add]
    ext a
    simp
  map_smul' := by
    intro k V
    ext a
    simp
    simp_rw [← Finset.mul_sum]
    ring
}

def C: ℝ := 32 * (#S)

set_option maxHeartbeats 2500000 in
lemma lemma_3_26_a (data: GoodScalesData b) (u: V): Q_R (R_2 data) u u ≤ 2 * (#(S^(R_1 data ))) * ‖(phi data u)‖^2 + C * (Real.exp ((a data.d))) * Real.exp (↑data.w * a data.d) * (R_1 data + 1)^2 * (∑ x ∈ B_r (2 * R_2 data), deriv_sq u x)  := by

  rw [Q_R]
  let a := ⋃₀ (B data)
  grw [Finset.sum_le_sum_of_subset_of_nonneg (t := (B_finsets data).biUnion id)]
  .
    grw [Finset.sum_biUnion_le (fun x => mul_self_nonneg ((↑u : LipschitzH) x))]
    .
      have u_bound (x: G) (j: B_finsets data): (u.val x)^2 ≤ 2 * ((u.val x - (phi data u).ofLp j)^2 + ((phi data u).ofLp j)^2) := by
        calc
          _ = |u.val x - ((phi data u).ofLp j) + (phi data u).ofLp j|^2 := by
            simp
          _ ≤ (|u.val x - (phi data u).ofLp j| + |(phi data u).ofLp j|)^2 := by
            grw [abs_add_le]
          _ = _ := by
            rw [add_sq]
          _ ≤ _ := by
            grw [two_mul_le_add_sq]
            simp [sq_abs]
            grind

      rw [← Finset.sum_finset_coe]
      simp_rw [← pow_two]
      simp
      grw [Finset.sum_le_sum (g := fun (j: B_finsets data) => ∑ x ∈ j, 2 * ((u.val x - (phi data u).ofLp j)^2 + ((phi data u).ofLp j)^2))]
      .

        simp_rw [← Finset.mul_sum]
        simp_rw [Finset.sum_add_distrib]
        simp
        have card_j_eq (j: B_finsets data): #j.val = #(S^(R_1 data)) := by
          have hj := j.prop
          simp only [B_finsets] at hj
          simp [-SetLike.coe_mem] at hj
          obtain ⟨x, hx, x_eq⟩ := hj
          rw [← x_eq]
          have foo := B_c_r_eq_smul x (R_1 data )
          simp [B_c_r] at foo
          rw [foo]
          simp
          -- conv =>
          --   lhs
          --   arg 1
          --   arg 1
          --   equals ↑((R_1 data) ) =>
          --     rw [Nat.cast_sub]
          --     .
          --       simp [R_1]
          --     . simp [R_1]
          --       grind

          rw [card_B_r_eq]

        simp [card_j_eq]
        simp_rw [← Finset.mul_sum]
        conv =>
          lhs
          rhs
          rhs
          rhs
          rw [← Finset.univ_eq_attach]
          rw [← EuclideanSpace.real_norm_sq_eq]


        -- The summand only depends on `↑j`, so we can drop the `.attach` and only then
        -- unfold `B_finsets` into a `Finset.image` and push the function call inwards.
        have phi_eq (j : B_finsets data) :
            ((phi data) u).ofLp j = (#(j : Finset G) : ℝ)⁻¹ * ∑ x ∈ (j : Finset G), (u : G → ℝ) x :=
          rfl
        simp_rw [phi_eq]
        have attach_eq := Finset.sum_attach (B_finsets data)
          (fun j => ∑ x ∈ j, ((u : G → ℝ) x - (#j : ℝ)⁻¹ * ∑ y ∈ j, (u : G → ℝ) y) ^ 2)
        beta_reduce at attach_eq
        simp only [show (↑u : LipschitzH).toFun = ⇑(↑u : LipschitzH) from rfl, attach_eq]
        simp only [B_finsets]
        rw [Finset.sum_image]
        .
          rw [mul_add]


          rw [add_comm]
          apply add_le_add
          .
            ring
            simp


          .

            conv =>
              lhs
              rhs
              arg 2
              intro x
              equals ∑ x_1 ∈ B_c_r x (R_1 data ), (u.val.toFun x_1 - (f_avg_c x (R_1 data ) u.val.toFun)) ^ 2 =>
                apply Finset.sum_congr
                . simp [B_c_r]
                . intro y hy
                  simp [f_avg_c, B_c_r, -Set.toFinset_card]
                  conv =>
                    lhs
                    lhs
                    pattern #(Metric.closedBall x (↑(R_1 data) )).toFinset
                    equals #(B_c_r x (R_1 data)) =>
                      simp [B_c_r]
                  rw [B_c_r_eq_smul]
                  simp [B_r]

            conv =>
              lhs
              rhs
              arg 2
              intro x
              arg 2
              intro y
              rw [← sq_abs]
            rw [← Finset.sum_finset_coe]
            simp only [SetLike.coe_sort_coe, Finset.univ_eq_attach]
            grw [Finset.sum_le_sum (h := fun (a : {x // x ∈ (X_j_finite data).toFinset}) _ =>
              lemma_3_25_poincare data ⟨a.val, (X_j_finite data).mem_toFinset.mp a.prop⟩
                (f := u.val.toFun))]


            simp_rw [← Finset.mul_sum]
            grw [Finset.sum_le_sum (g := fun (i: (X_j_finite data).toFinset) => ∑ x ∈ B_r (2 * (R_2 data)), deriv_sq (u.val).toFun x)]
            .

              have b_card := card_B_le_exp_wa data
              rw [← Set.ncard_eq_toFinset_card (hs := by apply B_finite)] at b_card
              simp [B] at b_card
              simp
              rw [← Set.ncard_eq_toFinset_card (hs := by apply X_j_finite)]

              rw [(Set.ncard_image_iff (by apply X_j_finite)).mpr] at b_card
              . grw [b_card]
                .
                  simp [C]
                  field_simp
                  norm_num
                  norm_cast
                  simp
                  rw [mul_comm 32]
                  apply le_refl
                . simp [deriv_sq]
                  positivity
              . apply B_ball_injective_on
                . simp
                . simp
            . intro i hi
              apply Finset.sum_le_sum_of_subset_of_nonneg
              .
                simp [-Finset.mem_attach] at hi
                have i_prop := i.prop
                simp [-SetLike.coe_mem, X_j] at i_prop
                intro p hp
                simp [B_r]
                grw [dist_triangle _ i.val]
                simp [B_c_r] at hp
                grw [hp]
                have i_mem := Metric.maximalSeparatedSet_subset i_prop
                simp at i_mem
                grw [i_mem]
                rw [two_mul]
                apply add_le_add
                . simp [R_1, R_2]
                  field_simp
                  rw [mul_add]
                  simp
                  ring

                  have i_sub := (GoodScales data).i_diff_mem
                  simp at i_sub
                  have first := i_sub.1
                  have i1_lt : (GoodScales data).i_1 < (GoodScales data).i_2 - data.w := by
                    grind

                  have explicit_w := data.w_gt
                  have i_1_lt_const: (GoodScales data).i_1 < (GoodScales data).i_2 - 4 := by
                    grind

                  grw [i_1_lt_const]
                  rw [← Real.rpow_natCast]
                  rw [Nat.cast_sub (by grind)]
                  rw [Real.rpow_sub]
                  norm_num
                  ring
                  have i_2_pos := (GoodScales data).i_2_pos
                  have i_2_ge : 1 ≤ (GoodScales data).i_2 := by grind

                  have three_le: (3: ℝ) < (16 ^ (GoodScales data).i_2) / 2 := by
                    field_simp
                    norm_num

                    grw [← i_2_ge]
                    .
                      simp
                      norm_num
                    . simp
                  nth_grw 1 [three_le]
                  .
                    simp
                    field_simp
                    norm_num
                  . simp
                  . simp






                  -- grw [i1_lt]
                  -- rw [mul_add]
                  -- norm_num
                  -- .


                  --   conv =>
                  --     pattern 16 ^ _
                  --     rw [← Real.rpow_natCast]
                  --     rw [Nat.cast_sub (by grind)]
                  --     rw [sub_eq_add_neg]
                  --     rw [Real.rpow_add (by simp)]

                  --   norm_cast
                  --   norm_num
                  --   field_simp
                  --   rw [mul_add]
                  --   norm_num
                  --   rw [← mul_assoc]
                  --   ring
                  --   field_simp
                  --   rw [← pow_add]

                  --   rw [Nat.pow_sub]
                  --   rw [Real.pow]
                  --   s orry
                  -- . simp
                . simp
                -- simp [B_r, dist, WordDist_one]
                -- simp [B_c_r, dist, WordDist] at hp


              . intros
                simp [deriv_sq]
                positivity

            -- simp_rw [B_c_r_eq_smul]
            -- simp_rw [← Finset.image_smul]
            -- conv =>
            --   lhs
            --   rhs
            --   rhs
            --   arg 2
            --   intro j
            --   rw [Finset.sum_image (by simp)]


            -- rw [← Finset.sum_product']
            -- rw [Finset.sum_comp]
            -- grw [Finset.sum_le_sum_of_subset_of_nonneg (t := B_r (2 * R_2 data))]
            -- .
            --   clear a
            --   grw [Finset.sum_le_sum (g := fun i => (Real.exp (a data.d)) * deriv_sq (u.val).toFun i)]
            --   . simp_rw [← Finset.mul_sum]
            --     simp [C]
            --     field_simp
            --     norm_num
            --     norm_cast
            --     rw [← Real.exp_nat_mul]
            --     simp
            --     rw [mul_comm 32]
            --     apply le_refl
            --   .
            --     intro x hx
            --     have mult_le := log_inter_mult_b3 data
            --     simp
            --     apply mul_le_mul
            --     .
            --       simp [InterMult, InterMult_f, B_3] at mult_le
            --       s orry

            --     . simp
            --     . simp [deriv_sq]
            --       positivity
            --     . positivity
            -- .
            --   rw [Finset.image_subset_iff]
            --   intro x hx
            --   simp at hx
            --   simp [B_r, dist, WordDist_one]
            --   simp [B_r] at hx
            --   grw [word_norm_mul_le]
            --   simp [dist, WordDist_one] at hx
            --   simp
            --   grw [hx]
            --   have x_prop := x.1.prop
            --   simp [-SetLike.coe_mem] at x_prop
            --   simp [X_j] at x_prop
            --   have x_mem := Metric.maximalSeparatedSet_subset x_prop
            --   simp [dist, WordDist_one] at x_mem
            --   grw [x_mem]
            --   rw [two_mul]
            --   apply add_le_add
            --   .
            --     simp [R_1, R_2]
            --     have i_sub := (GoodScales data).i_diff_mem
            --     simp at i_sub
            --     have i_2_gt: (GoodScales data).i_1 < (GoodScales data).i_2 := by
            --       grind

            --     rw [mul_add]
            --     norm_cast
            --     norm_num


            --   . simp
            --  ∑ x ∈ B_c_r (↑i) (↑(R_1 data) - 1), |(↑u).toFun x - f_avg_c (↑i) (↑(R_1 data) - 1) (↑u).toFun| ^ 2
            -- ∑ i ∈ ⋯.toFinset.attach, ∑ y ∈ B_c_r (↑i) (↑(R_1 data) - 1), |(↑u).toFun y - f_avg_c (↑i) (↑(R_1 data) - 1) (↑u).toFun| ^ 2
            -- simp
            -- intros
            -- simp [deriv_sq]
            -- positivity
        .
          simp
          have foo := B_ball_injective_on data (R_1 data ) (by simp [R_1]) (by simp)
          intro a ha b hb hab
          specialize foo ha hb (by
            simp
            simp at hab
            exact hab
          )
          exact foo



        -- rw [Finset.sum_attach]
        -- simp [Finset.sum_image]
        -- grw [Finset.sum_le_sum]



      . intro j hj
        apply Finset.sum_le_sum
        intro x hx
        apply u_bound



  .
    have cover := B_covers_R2 data
    simp
    intro a ha
    specialize cover ha
    simp [B_finsets]
    simp [B] at cover

    exact cover
  . intros
    rw [← pow_two]
    positivity

#print axioms lemma_3_26_a

-- Controlled grwoth

-- Lemma 3.27

/-- The determinant of `Q_R_matrix` at two bases of `V` differs by a positive constant that is
**uniform in the scale `R`**. Hence the determinant *ratio* between two scales — and so the
`h`-difference used to select good scales — is basis-independent. -/
lemma Q_R_matrix_det_basis_change {index : Type*} [Fintype index] [DecidableEq index]
    (b_1 : Module.Basis ι ℝ V) (b_2 : Module.Basis index ℝ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, (Q_R_matrix b_2 R).det = K * (Q_R_matrix b_1 R).det := by
  obtain ⟨K, hK, hB⟩ := LinearMap.toMatrix₂_det_basis_change b_1 b_2
  refine ⟨K, hK, fun R => ?_⟩
  have h2 : Q_R_matrix b_2 R = LinearMap.toMatrix₂ b_2 b_2 (Q_R_lin_plain V R) := by
    simp only [Q_R_matrix]; ext i j; simp [Q_R_lin, Q_R_lin_plain]
  have h1 : Q_R_matrix b_1 R = LinearMap.toMatrix₂ b_1 b_1 (Q_R_lin_plain V R) := by
    simp only [Q_R_matrix]; ext i j; simp [Q_R_lin, Q_R_lin_plain]
  rw [h2, h1, hB]


lemma growth_bound_basis_change (d: ℕ) {index: Type*} [Fintype index] [DecidableEq index] (b_1: Module.Basis ι ℝ V) (b_2: Module.Basis index ℝ V) (h_growth: growth_bound b_1 d) : growth_bound b_2 d := by
  -- the two bases index the same space, so their index types are canonically equivalent
  let equiv : ι ≃ index := b_1.indexEquiv b_2
  unfold growth_bound my_expr Q_R_matrix
  unfold growth_bound my_expr Q_R_matrix at h_growth
  have conv_plain: ∀ R, (LinearMap.toMatrix₂ b_2 b_2) (Q_R_lin V ↑R) = (LinearMap.toMatrix₂ b_2 b_2) (Q_R_lin_plain V ↑R) := by
    intro R
    ext i j
    simp [Q_R_lin, Q_R_lin_plain]

  have conv_plain_b_1: ∀ R, (LinearMap.toMatrix₂ b_1 b_1) (Q_R_lin V ↑R) = (LinearMap.toMatrix₂ b_1 b_1) (Q_R_lin_plain V ↑R) := by
    intro R
    ext i j
    simp [Q_R_lin, Q_R_lin_plain]

  -- The two change-of-basis determinant factors are transposes of each other, hence equal,
  -- and their common value is nonzero since it is the determinant of an (invertible) basis-change
  -- matrix (`(b_1.reindex equiv).toMatrix b_2`).
  have heq_det : ((b_1.toMatrix ⇑b_2).transpose.submatrix id ⇑equiv.symm).det
               = ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det := by
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have hne_det : ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det ≠ 0 := by
    rw [← Module.Basis.toMatrix_reindex]
    have hmul : ((b_1.reindex equiv).toMatrix ⇑b_2).det
              * (b_2.toMatrix ⇑(b_1.reindex equiv)).det = 1 := by
      rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one hmul

  simp_rw [conv_plain]
  conv =>
    arg 1
    intro R
    rw [← Matrix.det_reindex_self equiv.symm]
    rw [← LinearMap.toMatrix₂_mul_basis_toMatrix (b₁ := b_1.reindex equiv) (b₂ := b_1.reindex equiv)]
    simp [-LinearMap.toMatrix₂_mul_basis_toMatrix]
    rw [mul_assoc]
    rw [mul_comm _ (((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det)]
    rw [← mul_assoc]
    rw [Real.mul_rpow (by rw [heq_det]; exact mul_self_nonneg _) (by
      apply Matrix.PosSemidef.det_nonneg
      conv =>
        arg 1
        equals (LinearMap.toMatrix₂ (b_1.reindex equiv) (b_1.reindex equiv)) (Q_R_lin V ↑R) =>
          ext i j
          simp [Q_R_lin, Q_R_lin_plain]

      -- TODO - make this a standalone lemma
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      rw [LinearMap.isPosSemidef_def]
      refine ⟨?_, ?_⟩
      .
        apply Q_R_lin_symm
      .
        rw [LinearMap.isNonneg_def]
        intro x
        simp [Q_R_lin, Q_R]
        simp_rw [← pow_two]
        positivity

    )]
    rw [← mul_assoc]
    rw [mul_comm ((#(S ^ R)) : ℝ)]
    rw [mul_assoc]
    rw [mul_div_assoc]



  let K := (((b_1.toMatrix ⇑b_2).transpose.submatrix id ⇑equiv.symm).det *
          ((b_1.toMatrix ⇑b_2).submatrix (⇑equiv.symm) id).det) ^ (↑(Module.finrank ℝ ↥V) : ℝ)⁻¹
  conv =>
    rhs
    equals (nhdsWithin (K * 0) (Set.Ioi (K * 0))) =>
      simp

  apply Filter.TendstoNhdsWithinIoi.const_mul
  .
    apply Real.rpow_pos_of_pos
    rw [heq_det]
    exact mul_self_pos.mpr hne_det
  .
    simp_rw [LinearMap.toMatrix₂_reindex_det]
    simp_rw [conv_plain_b_1] at h_growth
    simp at h_growth
    apply h_growth


set_option maxHeartbeats 2500000 in
lemma exists_bounded_doubling_subspace (data: GoodScalesData b): ∃ U: Submodule ℝ LipschitzH, U ≤ V ∧ dim V ≤ 2 * dim U ∧ ∀ f ∈ U, Q_R (16 * (R_2 data)) f f ≤ Real.exp (2 * (a data.d)) * Q_R ((R_2 data)) f f := by
  classical


  let R := 16 ^ ((GoodScales data).i_2)
  have h_R: R'_ V ≤ ↑R := by
    have foo := (GoodScales data).i_2_ge
    simp [i₀] at foo
    have pow_le := Nat.le_pow_clog (b := 16) (x := ⌈R'_ V⌉₊) (by simp)
    have r_ceil := Nat.le_ceil (R')
    unfold R' at r_ceil
    grw [r_ceil]
    grw [pow_le]
    simp [R]
    rw [pow_le_pow_iff_right₀]
    . exact foo
    . simp

  have q_r_base_pos_def := (Q_R_matrix_pos_def_i₀ b (16 ^ ((GoodScales data).i_2)) (by
    simp [i₀]
    rw [pow_le_pow_iff_right₀]
    . sorry
    . simp
  ))

  -- Full (definite) inner product core, registered as a local instance so that
  -- `toNormedAddCommGroup` / `ofCore` pick it up by inference.
  letI Q_R_inner_core: InnerProductSpace.Core ℝ V := {
    inner := fun u v => Q_R R u.val v.val
    conj_inner_symm := by
      simp [Q_R]
      grind
    re_inner_nonneg := by
      simp [Q_R]
      sorry
    add_left := by
      simp
      sorry
    smul_left := by
      simp
      sorry
    definite := fun x hx => by
      by_contra hne
      exact absurd hx (ne_of_gt (Q_R_pos_on_R' x hne R h_R))
  }

  -- Install the definite Q_R-derived NORM (not just a seminorm) *before* `ofCore`, so the
  -- ambient LipschitzH norm on `↥V` is shadowed and `Q_R_inner` is over this `NormedAddCommGroup`.
  letI Q_R_norm : NormedAddCommGroup ↥V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  -- Also expose the seminorm projection as a *direct* local instance, so it shadows the
  -- ambient `V.seminormedAddCommGroup` (a bare `NormedAddCommGroup` letI does not).
  letI Q_R_seminorm : SeminormedAddCommGroup ↥V := Q_R_norm.toSeminormedAddCommGroup
  letI Q_R_inner : InnerProductSpace ℝ ↥V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ ↥V)

  have norm_eq_q_r : ∀ x : ↥V, ‖x‖ = Real.sqrt (Q_R R x x) := fun _ => rfl
  have norm_sq_eq_q_r : ∀ x : ↥V, ‖x‖^2 = (Q_R R x x) := by
    intro x
    rw [norm_eq_q_r]
    rw [Real.sq_sqrt]
    simp [Q_R]
    simp_rw [← pow_two]
    positivity
  have inner_eq_q_r  : ∀ x y : ↥V, inner ℝ x y = Q_R R x y := fun _ _ => rfl

  --have semi : SeminormedAddCommGroup V := by infer_instance
  --have inner_prod := Matrix.toNormedAddCommGroup _ q_r_base_pos_def
  obtain ⟨v_orthogonal_orig, v_orthogonal_orig_eval⟩ := LinearMap.BilinForm.exists_orthogonal_basis (Q_R_lin_symm V R)
  let v_orthonormal := v_orthogonal_orig.unitsSMul (fun a => Units.mk0 ‖v_orthogonal_orig a‖⁻¹ (by
    simp
    exact Module.Basis.ne_zero v_orthogonal_orig a
  ))

  --let q_r_16_lin_eigen := LinearMap.IsSymmetric.eigenvectorBasis (T := )
  let q_r_16_m := (Q_R_lin V (16 * R)).toMatrix₂ v_orthonormal v_orthonormal
  have q_r_16_m_hermitian: q_r_16_m.IsHermitian := by
    simp [q_r_16_m]
    apply (LinearMap.isSymm_iff_isHermitian_toMatrix _).mp
    apply Q_R_lin_symm

  let q_r_16_eigen := q_r_16_m_hermitian.eigenvectorBasis.toBasis
  let eigen_basis_V :=  (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ ↥V) → ℝ)).trans v_orthonormal.equivFun.symm
  -- let norm_eigen_q_r (i: Fin (Module.finrank ℝ ↥V)) := ‖eigen_basis_V (q_r_16_eigen i)‖

  -- let v_map_normalize := Module.Basis.constr q_r_16_eigen ℝ (fun a => (norm_eigen_q_r a)⁻¹ • (q_r_16_eigen a))
  -- let v_map_normalize_inv := Module.Basis.constr q_r_16_eigen ℝ (fun a => (norm_eigen_q_r) • (q_r_16_eigen a))
  -- let v_map_normalize_equiv := LinearEquiv.ofLinear (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) v_map_normalize v_map_normalize_inv (σ₁₂:= RingHom.id ℝ) (σ₂₁ := RingHom.id ℝ) (R₂ := ℝ) (R := ℝ) (by
  --   sorry
  -- ) (by
  --   sorry
  -- )
  -- let v_orthonormal := Module.Basis.map q_r_16_eigen v_map_normalize_equiv

  let remapped_ortho := Module.Basis.map q_r_16_eigen eigen_basis_V

  let Q_R_ortho := (Q_R_lin V R).toMatrix₂ remapped_ortho remapped_ortho
  have Q_R_ortho_m_hermitian: Q_R_ortho.IsHermitian := by
    simp [Q_R_ortho]
    apply (LinearMap.isSymm_iff_isHermitian_toMatrix _).mp
    apply Q_R_lin_symm

  have v_orthonormal_isortho : (Q_R_lin V ↑R).IsOrthoᵢ remapped_ortho := by
    simp [remapped_ortho]
    rw [LinearMap.isOrthoᵢ_def]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
    intro x y hxy
    have x_mem := x.prop
    simp [-Subtype.coe_prop] at x_mem
    --specialize v_orthogonal_orig_eval x y hxy
    --simp [v_map_normalize_equiv, v_map_normalize]
    simp [eigen_basis_V, v_orthonormal]
    simp_rw [Module.Basis.unitsSMul_apply]
    simp_rw [Units.smul_def]
    simp_rw [map_smul]
    simp
    simp_rw [Finset.mul_sum]
    conv =>
      lhs
      arg 2
      intro i
      rw [Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hij
        simp
        right
        right
        right
        right
        -- TODO - why doesn't an 'rw' with this work?
        apply v_orthogonal_orig_eval _ _ hij
      )]

    ring
    simp [norm_eq_q_r]
    have Q_R_pos: ∀ i, 0 ≤ Q_R ↑R ⇑(v_orthogonal_orig i).val ⇑(v_orthogonal_orig i).val := by
      intro i
      simp [Q_R, ← pow_two]
      positivity
    conv =>
      lhs
      arg 2
      intro i
      rw [Real.sq_sqrt (by apply Q_R_pos)]
    field_simp
    have eval_nonzero: ∀ i, (Q_R_lin V ↑R) (v_orthogonal_orig i) (v_orthogonal_orig i) ≠ 0 := by
      intro i
      simp [Q_R_lin]
      apply ne_of_gt
      apply Q_R_pos_on_R'
      . exact Module.Basis.ne_zero v_orthogonal_orig i
      . exact h_R
    conv =>
      lhs
      arg 2
      intro i
      rw [mul_div_assoc]
      rhs
      equals ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) / ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) =>
        rfl


    field_simp [eval_nonzero]
    have inner_zero :=  q_r_16_m_hermitian.eigenvectorBasis.inner_eq_zero hxy
    rw [EuclideanSpace.inner_eq_star_dotProduct] at inner_zero
    simp [dotProduct] at inner_zero
    exact inner_zero


  have q_r_lin_remapped_one: ∀ i, ((Q_R_lin V ↑R) (remapped_ortho i)) (remapped_ortho i) = 1 := by
    intro i
    simp [remapped_ortho]
    simp [eigen_basis_V,]
    ring
    field_simp
    simp only [eigen_basis_V, q_r_16_eigen]
    simp
    simp_rw [Finset.mul_sum]
    simp [v_orthonormal]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval

    simp_rw [Module.Basis.unitsSMul_apply]
    simp_rw [Units.smul_def]
    simp_rw [map_smul]
    simp

    conv =>
      lhs
      arg 2
      intro i
      rw [Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hij
        simp
        right
        right
        right
        right
        -- TODO - why doesn't an 'rw' with this work?
        apply v_orthogonal_orig_eval _ _ hij
      )]


    ring
    simp [norm_eq_q_r]
    have Q_R_pos: ∀ i, 0 ≤ Q_R ↑R ⇑(v_orthogonal_orig i).val ⇑(v_orthogonal_orig i).val := by
      intro i
      simp [Q_R, ← pow_two]
      positivity
    conv =>
      lhs
      arg 2
      intro i
      rw [Real.sq_sqrt (by apply Q_R_pos)]
    field_simp
    have eval_nonzero: ∀ i, (Q_R_lin V ↑R) (v_orthogonal_orig i) (v_orthogonal_orig i) ≠ 0 := by
      intro i
      simp [Q_R_lin]
      apply ne_of_gt
      apply Q_R_pos_on_R'
      . exact Module.Basis.ne_zero v_orthogonal_orig i
      . exact h_R
    conv =>
      lhs
      arg 2
      intro i
      rw [mul_div_assoc]
      rhs
      equals ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) / ((Q_R_lin V ↑R) (v_orthogonal_orig i)) (v_orthogonal_orig i) =>
        rfl


    field_simp [eval_nonzero]
    have one_eq: (1: ℝ) = 1^2 := by
      simp
    rw [one_eq, ← OrthonormalBasis.norm_eq_one (q_r_16_m_hermitian.eigenvectorBasis) i]
    rw [EuclideanSpace.real_norm_sq_eq]

  -- TODO - an enormous amount of this should get deduplicated with v_orthonormal_isortho
  have Q_R_ortho_eq_1: Q_R_ortho = 1 := by
    ext i j
    simp [Q_R_ortho, Matrix.one_apply]
    split_ifs
    .
      rename_i i_eq_j
      rw [i_eq_j]
      apply q_r_lin_remapped_one
    .
      rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
      apply v_orthonormal_isortho
      grind

  let Q_R_16_new_ortho := (Q_R_lin V (16 *R)).toMatrix₂ remapped_ortho remapped_ortho
  have Q_R_16_new_ortho_hermitian: Q_R_16_new_ortho.IsHermitian := by
    simp [Q_R_16_new_ortho]
    apply (LinearMap.isSymm_iff_isHermitian_toMatrix _).mp
    apply Q_R_lin_symm

  have det_Q_R_one: Q_R_ortho.det = 1 := by
    simp [Q_R_ortho_eq_1]

  have det_Q_R_16_ge: 1 ≤ Q_R_16_new_ortho.det := by
    rw [← det_Q_R_one]
    apply matrix_det_montone
    .
      simp [Q_R_ortho]
      apply Matrix.PosDef.of_dotProduct_mulVec_pos (?_)
      .
        intro x hx
        simp [Q_R_matrix]
        conv =>
          rhs
          lhs
          equals (star x) => simp
        rw [star_dotProduct_toMatrix₂_mulVec]
        apply Q_R_pos_on_R'
        . rw [LinearEquiv.map_ne_zero_iff]
          exact hx
        . exact h_R
      . apply Q_R_ortho_m_hermitian
    .
      simp [Q_R_16_new_ortho, Q_R_ortho]
      rw [← map_sub]
      rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
      apply Q_R_lin_sub_pos_semi_def
      norm_cast
      grind



  have q_r_16_remapped_orthogonal : (Q_R_lin_plain V (16 * R)).IsOrthoᵢ remapped_ortho := by
    simp [remapped_ortho]
    rw [LinearMap.isOrthoᵢ_def]
    rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_orig_eval
    intro x y hxy
    have x_mem := x.prop
    simp [-Subtype.coe_prop] at x_mem
    simp
    rw [apply_eq_dotProduct_toMatrix₂_mulVec (v_orthonormal) (v_orthonormal)]
    simp
    simp [eigen_basis_V]
    have repr_self: ∀ x, (∑ i, fun₀ | i => (q_r_16_eigen x).ofLp i) = (q_r_16_eigen x).ofLp := by
      intro z
      conv =>
        lhs
        arg 2
        intro i
        equals Pi.single i ((q_r_16_eigen z).ofLp i) =>
          simp
          ext a
          rw [Finsupp.single_apply]
          rw [Pi.single_apply]
          have foo := eq_comm (a := i) (b := a)
          simp_rw [foo]


      ext a
      simp

    simp [repr_self]
    unfold q_r_16_eigen
    unfold q_r_16_m
    conv =>
      lhs
      rhs
      lhs
      equals q_r_16_m => rfl

    have tobasis_lp: ∀ x, (q_r_16_m_hermitian.eigenvectorBasis.toBasis x).ofLp = (q_r_16_m_hermitian.eigenvectorBasis x).ofLp := by
      simp
    simp [tobasis_lp]
    rw [Matrix.IsHermitian.mulVec_eigenvectorBasis q_r_16_m_hermitian]
    simp
    right
    conv =>
      lhs
      rhs
      equals star ((q_r_16_m_hermitian.eigenvectorBasis y).ofLp) =>
        simp

    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    apply OrthonormalBasis.inner_eq_zero
    exact hxy.symm


  have new_growth := data.h_growth
  have nonempty_fin: Nonempty (Fin (Module.finrank ℝ ↥V)) := by
    use 0
    apply Module.finrank_pos
  apply growth_bound_basis_change data.d b remapped_ortho at new_growth

  -- let new_scales := (GoodScales {
  --   w := data.w
  --   d := data.d
  --   hw := data.hw
  --   hd := data.hd
  --   w_gt := data.w_gt
  --   h_growth := new_growth
  -- } (b := remapped_ortho))
  have a_gt := (GoodScales data).second_h_i
  simp [h, f] at a_gt
  rw [Real.log_mul] at a_gt
  .
    have log_pos_first: 0 ≤ Real.log ↑(#(S ^ 16 ^ ((GoodScales data).i_2 + 1))) := by
      apply Real.log_nonneg
      simp
      apply Finset.Nonempty.pow
      simp [S_nonempty]

    have log_second: Real.log ↑(#(S ^ 16 ^ (GoodScales data).i_2)) ≤ Real.log ↑(#(S ^ 16 ^ ((GoodScales data).i_2 + 1))) := by
      apply Real.log_le_log
      . simp
        apply Finset.Nonempty.pow
        simp [S_nonempty]
      . simp
        apply Finset.card_le_card
        apply Finset.pow_subset_pow_right
        . simp [one_mem]
        . grind


    --
    have inner_x_self (x: V) (k: ℝ) (hk: ∀ i ∈ (remapped_ortho.repr x).support, (Q_R_lin_plain V (16 * R) (remapped_ortho i) (remapped_ortho i)) ≤ k * (Q_R_lin_plain V (R) (remapped_ortho i) (remapped_ortho i))) : Q_R_lin_plain V (16 * R) x x ≤ k * Q_R_lin_plain V (R) x x := by
      rw [←  Module.Basis.sum_repr remapped_ortho (u := x)]
      have inner_sum_eq: ∀ i, ∑ i_1, inner ℝ ((remapped_ortho.repr x) i_1 • remapped_ortho i_1) ((remapped_ortho.repr x) i • remapped_ortho i) = inner ℝ ((remapped_ortho.repr x) i • remapped_ortho i) ((remapped_ortho.repr x) i • remapped_ortho i) := by
        intro i
        rw [Finset.sum_eq_single i]
        . intro k hk k_neq
          rw [inner_eq_q_r]
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
          specialize v_orthonormal_isortho k i k_neq
          simp [Q_R_lin] at v_orthonormal_isortho
          simp [Q_R]
          simp [Q_R] at v_orthonormal_isortho
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          simp_rw [mul_comm ((remapped_ortho.repr x) i)]
          simp_rw [← mul_assoc]
          rw [← Finset.sum_mul]
          simp [v_orthonormal_isortho]
        .
          intro hi
          simp at hi


      have q_r_16_sum_eq: ∀ i, ∑ i_1, Q_R_lin_plain V (16 * R) ((remapped_ortho.repr x) i_1 • remapped_ortho i_1) ((remapped_ortho.repr x) i • remapped_ortho i) = Q_R_lin_plain V (16 * R) ((remapped_ortho.repr x) i • remapped_ortho i) ((remapped_ortho.repr x) i • remapped_ortho i) := by
        intro i
        rw [Finset.sum_eq_single i]
        . intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at q_r_16_remapped_orthogonal
          specialize q_r_16_remapped_orthogonal k i k_neq
          simp [Q_R_lin_plain] at q_r_16_remapped_orthogonal
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at q_r_16_remapped_orthogonal
          right
          right
          simp [q_r_16_remapped_orthogonal]
        .
          intro hi
          simp at hi

      rw [map_sum]
      simp_rw [map_sum]
      simp [Finset.sum_apply]
      conv =>
        rhs
        rhs
        arg 2
        intro i
        rw [Finset.sum_eq_single i (by
          intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
          right
          specialize v_orthonormal_isortho k i k_neq
          simp [Q_R_lin] at v_orthonormal_isortho
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at v_orthonormal_isortho
          simp [v_orthonormal_isortho]
        ) (by
          intro hi
          simp at hi
        )]
        -- equals inner ℝ ((remapped_ortho.repr x) i • remapped_ortho i) ((remapped_ortho.repr y) i • remapped_ortho i) =>
        --   rw [inner_sum_eq]


      -- simp_rw [inner_smul_left]
      -- simp_rw [inner_smul_right]
      -- simp
      -- simp_rw [norm_sq_eq_q_r]
      -- have norm_ortho: ∀ i, ‖remapped_ortho i‖^2 = 1 := by
      --   intro i
      --   rw [norm_sq_eq_q_r]
      --   have foo := q_r_lin_remapped_one i
      --   simp [Q_R_lin] at foo
      --   exact foo

      -- simp [norm_ortho]

      -- New code

      conv =>
        rhs
        rw [←  Module.Basis.sum_repr remapped_ortho (u := x)]


      simp_rw [map_sum]
      simp
      simp_rw [Finset.mul_sum]
      conv =>
        lhs
        arg 2
        intro i
        rw [Finset.sum_eq_single i (by
          intro k hk k_neq
          simp [map_smul]
          rw [LinearMap.isOrthoᵢ_def] at q_r_16_remapped_orthogonal
          specialize q_r_16_remapped_orthogonal k i k_neq
          simp [Q_R_lin_plain] at q_r_16_remapped_orthogonal
          simp [Q_R_lin_plain, Q_R]
          simp [Q_R] at q_r_16_remapped_orthogonal
          right
          right
          simp [q_r_16_remapped_orthogonal]
        ) (by
          intro hi
          simp at hi
        )]

      apply Finset.sum_le_sum
      intro i hi
      by_cases i_mem_inter: i ∈ (remapped_ortho.repr x).support
      .
        conv =>
          lhs
          equals ((Q_R_lin_plain V (16 * ↑R)) (remapped_ortho i)) (remapped_ortho i)  * (remapped_ortho.repr x) i * (remapped_ortho.repr x) i =>
            ring

        conv =>
          rhs
          equals k * ((Q_R_lin_plain V ↑R) (remapped_ortho i)) (remapped_ortho i) * (remapped_ortho.repr x) i * (remapped_ortho.repr x) i =>
            ring


        rw [mul_assoc]
        nth_rw 2 [mul_assoc]
        specialize hk i i_mem_inter
        grw [hk]
        . ring
          simp
        . rw [← pow_two]
          positivity
      .
        simp at i_mem_inter
        simp [i_mem_inter]




      -- rw [apply_eq_dotProduct_toMatrix₂_mulVec (v_orthonormal) (v_orthonormal)]
      -- simp [eigen_basis_V]
      -- have repr_self: ∀ x, (∑ i, fun₀ | i => (q_r_16_eigen x).ofLp i) = (q_r_16_eigen x).ofLp := by
      --   intro z
      --   conv =>
      --     lhs
      --     arg 2
      --     intro i
      --     equals Pi.single i ((q_r_16_eigen z).ofLp i) =>
      --       simp
      --       ext a
      --       rw [Finsupp.single_apply]
      --       rw [Pi.single_apply]
      --       have foo := eq_comm (a := i) (b := a)
      --       simp_rw [foo]


      --   ext a
      --   simp

      -- simp [repr_self]
      -- unfold q_r_16_eigen
      -- unfold q_r_16_m
      -- conv =>
      --   lhs
      --   rhs
      --   lhs
      --   equals q_r_16_m => rfl

      -- have tobasis_lp: ∀ x, (q_r_16_m_hermitian.eigenvectorBasis.toBasis x).ofLp = (q_r_16_m_hermitian.eigenvectorBasis x).ofLp := by
      --   simp
      -- simp [tobasis_lp]
      -- rw [Matrix.IsHermitian.mulVec_eigenvectorBasis q_r_16_m_hermitian]
      -- simp
      -- right
      -- conv =>
      --   lhs
      --   rhs
      --   equals star ((q_r_16_m_hermitian.eigenvectorBasis y).ofLp) =>
      --     simp

      -- rw [← EuclideanSpace.inner_eq_star_dotProduct]




      -- simp

      -- rw [Orthonormal.inner_sum]
      -- . sorry
      -- . simp [remapped_ortho, q_r_16_eigen]

      -- sorry


    grw [← log_second] at a_gt
    rw [Real.log_mul] at a_gt
    .
      simp at a_gt
      rw [Real.log_rpow] at a_gt
      rw [Real.log_rpow] at a_gt
      rw [← mul_sub] at a_gt
      rw [← Real.log_div] at a_gt
      .


        simp [Q_R_matrix] at a_gt

        let large_basis: Finset _ := { i: Fin (Module.finrank ℝ ↥V) | (Real.exp (2 * (a data.d))) * Q_R_lin V (R) (remapped_ortho i) (remapped_ortho i) < Q_R_lin V (16 * R) (remapped_ortho i) (remapped_ortho i)}
        let small_basis: Finset _ := { i: Fin (Module.finrank ℝ ↥V) | ¬((Real.exp (2 * (a data.d))) * Q_R_lin V (R) (remapped_ortho i) (remapped_ortho i) < Q_R_lin V (16 * R) (remapped_ortho i) (remapped_ortho i))}
        let large_submodule := Submodule.span ℝ ((Finset.image remapped_ortho large_basis) : Set V)
        let large_submodule := Submodule.span ℝ ((Finset.image remapped_ortho large_basis) : Set V)
        by_cases dim_small: 2 * dim large_submodule < dim V
        .
          let small_submodule := Submodule.span ℝ ((Finset.image remapped_ortho Finset.univ ) \ (Finset.image remapped_ortho large_basis) : Set V)
          use Submodule.map V.subtype small_submodule
          refine ⟨?_, ?_, ?_⟩
          . apply Submodule.map_subtype_le
          . simp [dim]
            simp [dim] at dim_small
            have large_small_compl: IsCompl large_submodule small_submodule := by
              simp [large_submodule, small_submodule]
              have diff_eq: Set.range ⇑remapped_ortho \ ⇑remapped_ortho '' ↑large_basis = Set.image remapped_ortho small_basis := by
                ext a
                simp [large_basis, small_basis]
                grind
              rw [diff_eq]
              apply LinearIndependent.isCompl_span_image
              . apply Module.Basis.linearIndependent
              . simp
              . apply IsCompl.of_eq
                . simp
                  ext a
                  simp [large_basis, small_basis]
                . simp
                  ext a
                  simp [large_basis, small_basis]
                  grind

            have dim_sum := Submodule.finrank_add_eq_of_isCompl large_small_compl
            rw [eq_comm, add_comm] at dim_sum

            apply Nat.sub_eq_of_eq_add at dim_sum
            rw [← dim_sum]
            rw [Nat.cast_sub (by apply Submodule.finrank_le)]
            rw [mul_sub]
            have dim_le := Submodule.finrank_le large_submodule
            simp
            rw [le_sub_iff_add_le']
            grw [dim_small]
            ring
            simp
          .
            have all_le: ∀ f ∈ small_submodule, Q_R_lin V (16 * ↑(R_2 data)) f f ≤ Real.exp (2 * a data.d) * Q_R_lin V ↑(R_2 data) f f := by
              intro f hf
              apply inner_x_self
              intro i hi
              simp only [small_submodule, ← Finset.coe_sdiff] at hf
              rw [Submodule.mem_span_finset] at hf
              obtain ⟨g, g_supp, f_eq_g⟩ := hf
              rw [← f_eq_g] at hi
              rw [Finset.sum_sdiff_eq_sub] at hi
              .
                simp at hi
                rw [Finset.sum_image (by simp; apply Module.Basis.injective)] at hi
                rw [Finset.sum_image (by apply (Module.Basis.injective _).injOn)] at hi
                simp at hi
                have i_not_mem: ¬(i ∈ large_basis) := by
                  by_contra!
                  rw [Finset.sum_eq_single_of_mem i this] at hi
                  .
                    rw [Finset.sum_eq_single_of_mem i (by simp)] at hi
                    . simp at hi
                    . intro k hk i_neq
                      simp
                      right
                      simp [Finsupp.single_apply, i_neq]
                  . intro k hk i_neq
                    simp
                    right
                    simp [Finsupp.single_apply, i_neq]

                simp [large_basis] at i_not_mem
                simp [Q_R_lin_plain]
                simp [Q_R_lin] at i_not_mem
                simpa using i_not_mem



              . apply Finset.image_subset_image
                simp
            intro f hf
            simp at hf
            obtain ⟨f_mem_V, hf⟩ := hf
            specialize all_le ⟨_, f_mem_V⟩ hf
            apply all_le

        simp at dim_small
        have basis_change := Q_R_matrix_det_basis_change remapped_ortho b
        obtain ⟨K, k_pos, hK⟩ := basis_change
        simp [Q_R_matrix] at hK
        simp [hK] at a_gt
        field_simp at a_gt
        unfold Q_R_ortho at det_Q_R_one
        simp [R] at det_Q_R_one
        simp [det_Q_R_one] at a_gt
        rw [Matrix.IsHermitian.det_eq_prod_eigenvalues] at a_gt
        .
          rw [Real.log_prod] at a_gt
          .
            grw [← Finset.card_nsmul_le_sum] at a_gt
            sorry
            sorry
            sorry
            sorry
          . intro i
            simp
            sorry
          --grw [← Finset.pow_card_le_prod] at a_gt
          --sorry
        .
          simp [Q_R_16_new_ortho, R] at Q_R_16_new_ortho_hermitian
          field_simp at Q_R_16_new_ortho_hermitian
          rw [pow_succ']
          apply Q_R_16_new_ortho_hermitian

        -- OLD - BAD

        -- have h_Q_R_16_remapped: (Q_R_lin V (16 * ↑R)).IsOrthoᵢ ⇑remapped_ortho := by
        --   rw [LinearMap.isOrthoᵢ_def]
        --   intro i h hij
        --   simp [remapped_ortho, eigen_basis_V]

        --   sorry


        -- have eigen_ge_one: ∀ i, 1 ≤ Q_R_16_new_ortho_hermitian.eigenvalues i := by
        --   intro i
        --   rw [Matrix.IsHermitian.eigenvalues_eq]
        --   rw [star_dotProduct_toMatrix₂_mulVec]
        --   simp [Q_R_16_new_ortho]
        --   simp_rw [Finset.mul_sum]
        --   have one_le_q_r_16_diag: ∀ k, 1 ≤ (Q_R_lin V (16 * ↑R)) (remapped_ortho k) (remapped_ortho k) := by
        --     intro k
        --     simp [Q_R_lin, Q_R]
        --     grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := B_r R)]
        --     .
        --       have Q_r_one_app: Q_R_ortho k k = 1 := by
        --         simp [Q_R_ortho_eq_1]

        --       simp [Q_R_ortho, Q_R_lin, Q_R] at Q_r_one_app
        --       simp [B_r]
        --       rw [Q_r_one_app]

        --     . simp [B_r]
        --       apply Metric.closedBall_subset_closedBall
        --       norm_cast
        --       grind
        --     . intro k hk k_not
        --       rw [← pow_two]
        --       positivity

        --   --grw [← Finset.single_le_sum (a := ⟨0, by exact Module.finrank_pos⟩)]


        --   --rw [← Finset.sum_attach]
        --   --apply Finset.single_le_sum


        --   -- Q_R_16_remapped
        --   --simp_rw [← LinearMap.toMatrix₂_apply]
        --   rw [LinearMap.isOrthoᵢ_def] at h_Q_R_16_remapped


        --   conv =>
        --     rhs
        --     arg 2
        --     intro p
        --     arg 2
        --     intro y

        --   --simp_rw [← Finset.mul_sum]

        --   rw [← Finset.sum_product']
        --   rw [← Finset.sum_sdiff (s₁ := {x | x.1 = x.2}) (by simp)]
        --   have one_eq: (1: ℝ ) = 0 + 1 := by
        --     simp
        --   rw [one_eq]
        --   apply add_le_add
        --   .



        --     apply Finset.sum_nonneg
        --     intro p hp
        --     rw [h_Q_R_16_remapped]
        --     .
        --       simp
        --     . simp at hp
        --       grind

        --     -- --grw [← Finset.sum_le_sum_of_subset_of_nonneg]
        --     -- have mul_eigen := Matrix.IsHermitian.mulVec_eigenvectorBasis (Q_R_16_new_ortho_hermitian)
        --     -- simp [Q_R_16_new_ortho] at mul_eigen
        --     -- simp_rw [Matrix.mulVec_eq_sum] at mul_eigen
        --     -- simp at mul_eigen

        --     -- --simp? [-Finset.sum_sdiff_eq_sub, remapped_ortho, v_orthonormal, v_map_normalize_equiv, v_map_normalize, eigen_basis_V]
        --     -- --simp_rw [← LinearMap.toMatrix₂_apply]
        --     -- --simp [eigen_basis_V]
        --     -- conv =>
        --     --   rhs
        --     --   arg 2
        --     --   intro x
        --     --   rhs
        --     --   rhs
        --     --   simp [remapped_ortho, v_orthonormal, v_map_normalize_equiv, v_map_normalize, eigen_basis_V, norm_eigen_q_r]
        --     --   rw [← LinearMap.toMatrix₂_apply]


        --     -- have transpose_eq: ((LinearMap.toMatrix₂ remapped_ortho remapped_ortho) (Q_R_lin V (16 * ↑R))).IsSymm := by
        --     --   exact
        --     --     Matrix.isSymm_conjTranspose_iff.mp
        --     --       (congrArg Matrix.transpose Q_R_16_new_ortho_hermitian)

        --     -- simp_rw [transpose_eq.eq] at mul_eigen
        --     -- rw [Finset.sum_finset_product_right (s := Finset.univ) (t := fun p => Finset.univ \ {p})]
        --     -- .
        --     --   simp [-Finset.sum_sdiff_eq_sub]

        --     --   conv =>
        --     --     rhs
        --     --     arg 2
        --     --     intro p
        --     --     arg 2
        --     --     intro q
        --     --     rw [← mul_assoc, mul_comm ((Q_R_16_new_ortho_hermitian.eigenvectorBasis i).ofLp q), mul_assoc]


        --     --   simp_rw [← Finset.mul_sum]
        --     --   simp_rw [mul_comm]

        --     --   sorry
        --     -- . intro p
        --     --   simp

        --   .
        --     rw [Finset.sum_congr (s₂ := { x | x.1 = x.2}) (g := fun x => ((Q_R_16_new_ortho_hermitian.eigenvectorBasis i).ofLp x.1) ^2 * ((Q_R_lin V (16 * ↑R)) (remapped_ortho x.1)) (remapped_ortho x.1))]
        --     .

        --       grw [← Finset.sum_le_sum (f := fun x => (Q_R_16_new_ortho_hermitian.eigenvectorBasis i).ofLp x.1 ^ 2)]
        --       .
        --         simp
        --         rw [Finset.sum_finset_product_right (s := Finset.univ) (t := fun a => {a})]
        --         . simp
        --           rw [← EuclideanSpace.real_norm_sq_eq]
        --           simp
        --         . intro p
        --           simp
        --       . intro x hx
        --         apply le_mul_of_one_le_right
        --         . positivity
        --         .
        --           apply one_le_q_r_16_diag

        --       -- rw [Finset.sum_product]
        --       -- sorry
        --       --rw [Finset.sum_product']
        --     . simp
        --     . intro p hp
        --       simp at hp
        --       simp [hp]
        --       ring

        --     -- grw [← Finset.card_nsmul_le_sum (n := 1)]
        --     -- . simp
        --     --   sorry
        --     -- .
        --     --   intro p hp
        --     --   rw [Finset.sum_congr (s₂ := { x | x.1 = x.2}) ]


        --   simp [remapped_ortho, eigen_basis_V, q_r_16_eigen]
        --   simp_rw [Finset.mul_sum]
        --   rw [← Finset.sum_product']
        --   grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := {x ∈ Finset.univ ×ˢ Finset.univ | x.1 = x.2})]
        --   .
        --     simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
        --     simp
        --     simp_rw [Finset.mul_sum]
        --     simp_rw [← Finset.sum_product']
        --     grw [← Finset.card_nsmul_le_sum (n := 1)]
        --     . simp
        --       sorry
        --     .
        --       intro p hp

        --       grw [← Finset.sum_le_sum_of_subset_of_nonneg (s := {y ∈ Finset.univ ×ˢ Finset.univ | y.1 = y.2})]
        --       .
        --         grw [← Finset.card_nsmul_le_sum (n := 1)]
        --         . simp
        --           sorry
        --         . intro y hy
        --           simp at hy
        --           simp at hp
        --           simp [hp, hy]

        --       . sorry
        --       . sorry
        --     grw [← Finset.nsmu]

        --   . simp
        --   . intro p hp p_not_mem
        --     --apply Finset.sum_nonneg
        --     --intro x hx
        --     --rw [← mul_assoc, ← mul_assoc]
        --     simp at p_not_mem
        --     simp [v_orthonormal, v_map_normalize_equiv, v_map_normalize, q_r_16_eigen]
        --     simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
        --     simp
        --     split_ifs
        --     .

        --       sorry
        --     all_goals { simp }

        --     -- apply mul_nonneg
        --     -- . sorry
        --     -- . sorry

        --   grw [← Finset.card_nsmul_le_sum (n := 1)]
        --   . simp
        --     norm_cast
        --     have rank_pos := Module.finrank_pos (R := ℝ) (M := V)
        --     apply one_le_mul
        --     . grind
        --     . grind
        --   .
        --     intro q hq

        --     sorry

        --   simp_rw [← Finset.sum_product']
        --   simp_rw [Finset.sum_apply]


        --   rw [star_dotProduct_toMatrix₂_mulVec]
        --   have eval_eq := dotProduct_toMatrix₂_mulVec (Q_R_16_new_ortho_hermitian.eigenvectorBasis.toBasis) (Q_R_16_new_ortho_hermitian.eigenvectorBasis.toBasis) (σ₁ := RingHom.id _) (σ₂ := RingHom.id _)

        --   simp at eval_eq
        --   specialize eval_eq
        --   rw [eval_eq]
        --   simp only [Q_R_16_new_ortho]
        --   rw [dotProduct_toMatrix₂_mulVec]
        --   rw [Matrix.dot_mulVec_eq_sum_sum]
        --   simp
        --   simp_rw [← Finset.sum_attach_univ]
        --   apply Finset.single_le_sum
        --   simp [remapped_ortho, eigen_basis_V, v_orthonormal, q_r_16_eigen, v_map_normalize_equiv, v_map_normalize, norm_eigen_q_r]
        --   simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
        --   simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]





        -- have v_orthonormal_isortho : (Q_R_lin V ↑R).IsOrthoᵢ eigen_basis_V := by
        --   rw [LinearMap.isOrthoᵢ_def]
        --   rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_eval
        --   intro x y hxy
        --   simp only [eigen_basis_V]
        --   simp [v_orthonormal]



        --   have new := v_orthogonal_eval
        --   specialize v_orthogonal_eval x y hxy
        --   simp [v_map_normalize_equiv, v_map_normalize]
        --   right
        --   right
        --   exact v_orthogonal_eval


        -- have v_orthonormal_isortho : (Q_R_lin V ↑R).IsOrthoᵢ v_orthonormal := by
        --   simp [v_orthonormal]
        --   rw [LinearMap.isOrthoᵢ_def]
        --   rw [LinearMap.isOrthoᵢ_def] at v_orthogonal_eval
        --   intro x y hxy
        --   have x_mem := x.prop
        --   simp [-Subtype.coe_prop] at x_mem
        --   specialize v_orthogonal_eval x y hxy
        --   simp [v_map_normalize_equiv, v_map_normalize]
        --   right
        --   right
        --   exact v_orthogonal_eval


        -- let Q_R_ortho := (Q_R_lin V R).toMatrix₂ v_orthonormal v_orthonormal
        -- have Q_R_ortho_hermitian: Q_R_ortho.IsHermitian := by
        --   simp [Q_R_ortho]
        --   apply (LinearMap.isSymm_iff_isHermitian_toMatrix _).mp
        --   apply Q_R_lin_symm

        -- have Q_R_ortho_eq_1: Q_R_ortho = 1 := by
        --   ext i j
        --   simp [Q_R_ortho, Matrix.one_apply]
        --   split_ifs
        --   .
        --     rename_i i_eq_j
        --     rw [i_eq_j]
        --     simp [v_orthonormal, v_map_normalize_equiv, v_map_normalize]
        --     rw [norm_eq_q_r]
        --     ring
        --     simp [Q_R_lin]
        --     have q_i_nonzero: 0 < (Q_R ↑R) (v_orthogonal j) (v_orthogonal j) := by
        --       apply Q_R_pos_on_R'
        --       . apply Module.Basis.ne_zero
        --       . simp [R, R'_]
        --         sorry

        --     rw [Real.sq_sqrt]
        --     .
        --       field_simp
        --       rfl
        --     . simp [Q_R]
        --       simp_rw [← pow_two]
        --       positivity
        --   .
        --     simp [Q_R_lin]
        --     rw [LinearMap.isOrthoᵢ_def] at v_orthonormal_isortho
        --     specialize v_orthonormal_isortho i j (by grind)
        --     simp [Q_R_lin] at v_orthonormal_isortho
        --     exact v_orthonormal_isortho



        -- have Q_R_ortho_det_one: Q_R_ortho.det = 1 := by
        --   simp [Q_R_ortho_eq_1]








        -- let base_spectral := q_r_base_pos_def.isHermitian.eigenvectorBasis
        -- let Q_r_change := LinearMap.toMatrix₂ (base_spectral.toBasis) (base_spectral.toBasis) (N₂ := ℝ) (σ₁ := RingHom.id _) (σ₂ := RingHom.id _)
        -- let base_repr := LinearMap.toMatrix₂ (V_basis V) (V_basis V)  (N₂ := ℝ) (σ₁ := RingHom.id _) (σ₂ := RingHom.id _)
        -- let combined := base_repr.trans Q_r_change.symm

        -- let remapped_Q_r := (combined (Q_R_lin V R)).toMatrix₂ base_spectral.toBasis base_spectral.toBasis
        -- let remapped_Q_r_16 :=  (combined (Q_R_lin V (16*R))).toMatrix₂ base_spectral.toBasis base_spectral.toBasis

        -- have Q_r_det : remapped_Q_r.det = 1 := by
        --   have hermitian_remap: remapped_Q_r.IsHermitian := by
        --     simp [remapped_Q_r]
        --     apply (LinearMap.isSymm_iff_isHermitian_toMatrix base_spectral.toBasis).mp
        --     simp [combined, Q_r_change, base_repr, base_spectral]


        --     rw [LinearMap.isSymm_def]
        --     simp [Q_r_change]
        --     intro x y
        --     sorry

        --   have eigen_one: ∀ a ∈ Set.range hermitian_remap.eigenvalues, a = 1 := by
        --     intro a ha
        --     rw [Set.mem_range] at ha
        --     obtain ⟨k, kh⟩ := ha
        --     have foo := hermitian_remap.mulVec_eigenvectorBasis k
        --     simp [remapped_Q_r, base_spectral, combined] at foo

        --     have eigen_repr: (hermitian_remap.eigenvectorBasis k) = hermitian_remap.eigenvectorBasis.repr ((hermitian_remap.eigenvectorBasis k)) := by
        --       sorry

        --     sorry
        --   rw [hermitian_remap.det_eq_prod_eigenvalues]
        --   sorry



            --rw [← LinearMap.isSymm_iff_isHermitian_toMatrix]
            --rw [Matrix.isHermitian_iff_isSymmetric]
            --simp
            --rw [← LinearMap.isSymm_iff_isHermitian_toMatrix]






        -- have foo := combined.symm (q_r_base_pos_def.isHermitian.eigenvectorBasis sorry)


        -- let base_spectral_v := (base_spectral.toBasis.map (base_spectral.repr))
        -- let q_r_eigenbasis := (Q_R_lin V R).toMatrix₂ base_spectral_v base_spectral_v

        -- let basis := q_r_base_pos_def.isHermitian.eigenvectorBasis.toBasis.det

        -- let q_r_16 := (Q_R_matrix V (16 ^ ((GoodScales data).i_2 + 1)))

        -- have q_r_16_eval (i: ↑(Module.Basis.ofVectorSpaceIndex ℝ ↥V)): 1 ≤ ((basis i)) ⬝ᵥ (q_r_16.mulVec (basis i)) := by
        --   have base_eval := Matrix.IsHermitian.mulVec_eigenvectorBasis q_r_base_pos_def.isHermitian i
        --   --have r_16_eval_pos :=
        --   have eval := star_dotProduct_toMatrix₂_mulVec (b := basis.toBasis) (B := Q_R_lin V (16 ^ ((GoodScales data).i_2 + 1)))
        --   sorry


        -- rw [pos_def.isHermitian.det_eq_prod_eigenvalues] at a_gt



        --rw [Q_R_matrix_pos_def]
      . sorry
      . sorry
      . sorry
      . sorry
    . simp
      have foo := S_nonempty
      grind
    . sorry


    -- grw [← log_pos_first] at a_gt
    -- rw [Real.log_mul] at a_gt
    -- .
    --   simp at a_gt
    --   rw [sub_add_eq_sub_sub] at a_gt
    --   grw [log_second] at a_gt

    -- . sorry
    -- . sorry
  . sorry
  . sorry






end V_Wrapper_Section

-- Theorem 3.23
lemma theorem_3_23 (d: ℝ): ∃ C: ℕ, ∀ data: V_Data, (haveI := data.hV; haveI := data.V_decidable; growth_bound (V_basis data.V) d) → (Module.finrank ℝ data.V) < C := by
  have C: ℕ := sorry
  use C
  intro data h_growth


  sorry


open scoped Topology

-- TODO - do we really need the double by_contra here?
-- Theorem 3.19
set_option maxHeartbeats 2500000 in
instance Lipschitz_finite_dimensional: FiniteDimensional ℝ LipschitzH := by
  classical
  by_contra!
  have B := Module.Basis.ofVectorSpace ℝ LipschitzH

  have B_infinite: Infinite ((Module.Basis.ofVectorSpaceIndex ℝ LipschitzH)) := by
    by_contra fin_basis
    simp at fin_basis
    have finite_module := Module.Finite.of_basis B
    have finite_dim: FiniteDimensional ℝ LipschitzH := by
      infer_instance
    contradiction


  obtain ⟨d, hd⟩ := hGS.g_growth
  obtain ⟨C, V_bound⟩ := theorem_3_23 ((d + 3) + (d + 3))

  obtain ⟨fin_basis_idx, card_fin_basis_idx⟩ := B_infinite.exists_subset_card_eq _ (2 + C * 2)
  let fin_basis := Finset.image (B) fin_basis_idx
  let large_v: V_Data := {
    V := Submodule.span ℝ fin_basis
    hV := by infer_instance
    V_even := by
      rw [finrank_span_finset_eq_card]
      .
        simp [fin_basis]
        rw [Finset.card_image_of_injective]
        . grind
        .

          exact Module.Basis.injective B
      .
        simp [fin_basis]
        apply LinearIndepOn.id_image
        exact Module.Basis.linearIndepOn B ↑fin_basis_idx
    V_decidable := by
      infer_instance
  }
  specialize V_bound large_v ?_
  .
    simp [growth_bound, my_expr]
    -- have ne_top_of_zero (a: ENNReal) (ha: a ≤ 0): a ≠ ⊤ := by
    --   simp at ha
    --   simp [ha]
    -- apply ne_top_of_zero
    -- simp
    -- apply Filter.Tendsto.liminf_eq
    -- conv =>
    --   pattern nhds 0
    --   equals nhds ((ENNReal.ofReal (0 * 0))) =>
    --     simp

    -- apply ENNReal.tendsto_ofReal
    norm_cast
    conv =>
      arg 1
      intro a
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [Nat.pow_add]
    push_cast
    conv =>
      arg 1
      intro a
      rw [div_mul_eq_div_mul_one_div]
      rw [mul_comm _ (1 / _)]
      rw [← mul_assoc]

    have nontrivial_v : Nontrivial large_v.V := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      rw [finrank_span_finset_eq_card]
      .
        simp [fin_basis]
        rw [← Finset.card_ne_zero]
        grind
      .
        simp [fin_basis]
        apply LinearIndepOn.id_image
        exact Module.Basis.linearIndepOn B ↑fin_basis_idx


    conv =>
      pattern (𝓝[>] 0)
      equals (𝓝[>] (0 * 0)) => simp

    apply Filter.TendstoNhdsWithinIoi.mul (by simp) (by simp)
    .
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      simp
      -- (R' (V := V))
      let R'' := ⌈R'_ large_v.V⌉₊
      haveI := large_v.hV
      haveI := nontrivial_v
      rw [← Filter.tendsto_add_atTop_iff_nat R'']
      --  Filter.tendsto_add_atTop_iff_nat
      apply squeeze_zero_nhdsGT (g := (fun (R: ℕ) => (det_bound_const (V_basis large_v.V) * (1 + (R + R'')) ^ 2 * ((a * (R + R'')^d : ℝ))) / ((R + R'') ^ (↑d + 3) : ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro R R_pos
        have det_pos := (Q_R_matrix_pos_def (V_basis large_v.V) (R + R'') (by
          -- TODO - why is this so messy?
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ large_v.V)
          rw [add_comm]
          simp
          grind
        )).det_pos
        norm_cast at det_pos
        have hrr : 0 < R + R'' := by omega
        positivity
      .
        apply Filter.Eventually.of_forall
        intro R
        have foo := det_bound (V_basis large_v.V) (R := R + R'') (by
          simp [R'']
          norm_cast
          have foo := Nat.le_ceil (a := R'_ (V := large_v.V))
          rw [add_comm]
          simp
          grind
        )
        simp
        rw [one_div] at foo
        push_cast at foo
        refine le_trans (mul_le_mul_of_nonneg_right foo (by positivity)) ?_
        by_cases const_zero: det_bound_const (V_basis large_v.V) = 0
        .
          simp [const_zero]

        field_simp
        rw [mul_div_assoc]
        rw [mul_div_assoc]
        rw [mul_assoc]
        rw [mul_le_mul_iff_right₀]
        .
          by_cases r_zero: (R + R'') = 0
          .
            norm_cast
            simp [r_zero]
          .
            grw [s_growth (R + R'') (by grind)]
            norm_cast
            simp
            rw [mul_div_assoc]
        .
          have nonneg := det_bound_const_nonneg (V_basis large_v.V)
          grind
      . poly_tendsto
    .
      --apply Asymptotics.IsLittleO.tendsto_div_nhds_zero
      unfold HasPolynomialGrowthD at hd
      obtain ⟨a, s_growth⟩ := hd
      apply squeeze_zero_nhdsGT (g := (fun (n: ℝ) => (a * n^d : ℝ) / (n ^ (↑d + 3))) ∘ (fun (n: ℕ) => (n: ℝ)))
      .
        rw [Filter.eventually_atTop]
        use 1
        intro n hn
        have card_nonzero: (0: ℝ) < #(S ^ n) := by
          simp
          apply Finset.Nonempty.pow
          apply S_nonempty

        norm_cast
        positivity
      .
        apply Filter.Eventually.of_forall
        intro n
        by_cases hn: n = 0
        .
          simp [hn]
        .
          grw [s_growth n (by grind)]
          norm_cast
          simp
      . poly_tendsto
  .
    -- TODO - deduplicate
    rw [finrank_span_finset_eq_card] at V_bound
    .
      simp [fin_basis] at V_bound
      rw [Finset.card_image_of_injective] at V_bound
      .
        simp [card_fin_basis_idx] at V_bound
        grind
      . exact Module.Basis.injective B
    .
      simp [fin_basis]
      apply LinearIndepOn.id_image
      exact Module.Basis.linearIndepOn B ↑fin_basis_idx

#synth FiniteDimensional ℝ LipschitzH
