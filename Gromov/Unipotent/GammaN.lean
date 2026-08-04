module

public import Mathlib
public import Gromov.Unipotent.FG

/-!
# Existence of a unipotent `γ_n`

`exists_gamma_n_unipotent_center_N'` and `exists_gamma_n_unipotent_N'`.
-/

public section

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

/-- Transport a `gamma_conj_bound`-style bound along a common "source" group `C`: out of `C`
there is an injective `j` into the group `N` where the bound is known, and a surjective `ψ`
onto the group `Q` where it is wanted, each intertwining the respective self-maps. -/
theorem conjBound_transport {C Q N : Type*} [Group C] [Group Q] [Group N]
    [DecidableEq Q] [DecidableEq N]
    {fC : C → C} {fQ : Q → Q} {fN : N → N}
    (ψ : C →* Q) (hψ : Function.Surjective ψ) (j : C →* N) (hj : Function.Injective j)
    (hψcomm : ∀ x, ψ (fC x) = fQ (ψ x)) (hjcomm : ∀ x, j (fC x) = fN (j x))
    (hbound : ∀ k : ℕ, 0 < k → ∀ g : N, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fN^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q) :
    ∀ k : ℕ, 0 < k → ∀ g : Q, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fQ^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q := by
  have hiterψ : ∀ (n : ℕ) (x : C), ψ (fC^[n] x) = fQ^[n] (ψ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hψcomm]
  have hiterj : ∀ (n : ℕ) (x : C), j (fC^[n] x) = fN^[n] (j x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hjcomm]
  intro k hk gQ
  obtain ⟨gC, rfl⟩ := hψ gQ
  obtain ⟨p, q, ppos, hb⟩ := hbound k hk (j gC)
  refine ⟨p, q, ppos, ?_⟩
  intro b hb' a ha hab
  refine le_trans ?_ (hb b hb' a ha hab)
  simp_rw [← hiterψ, ← hiterj]
  exact card_image_listProd_hom_le ψ j hj ((Finset.Ico a b).attach.powerset)
    (fun (i : ↥(Finset.Ico a b)) => fC^[k * ↑i] gC)

/-- Final step of isolating `K`, reducing the `h_poly` log inequality to a statement in `ℕ`.

Splits `Real.log ↑(p * K ^ q)` into `Real.log ↑p + q * Real.log ↑K`, then eliminates the
`Real.log ↑K` using `Real.log_natCast_le_rpow_div` at `ε := 1/4`, which gives
`Real.log K ≤ 4 * K ^ (1/4)`; squaring therefore contributes only a `K ^ (1/2)` term, which
the right-hand `K` dominates.  (At `ε := 1/2` the reduction would be unsound for `q ≥ 1`.)
The hypothesis mentions `K` only on the right, and is an inequality of naturals. -/
theorem log_pow_sq_lt_of_lt (M p q K : ℕ) (hp : 0 < p)
    (h : ⌈4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2⌉₊ + 2 * M < K) :
    ((4 * (q:ℝ) + Real.log ((p * K ^ q : ℕ) : ℝ)) / Real.log 2) ^ 2 + (M:ℝ) < (K:ℝ) := by
  have hK1 : 1 ≤ K := by omega
  have hpr : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hKr : ((K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit : Real.log ((p * K ^ q : ℕ) : ℝ) = Real.log p + q * Real.log K := by
    push_cast; rw [Real.log_mul hpr (pow_ne_zero _ hKr), Real.log_pow]
  rw [hsplit]
  have h' : 4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2 + 2 * (M:ℝ) < (K:ℝ) := by
    have hceil := Nat.le_ceil (4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2)
    have hcast : ((⌈4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2⌉₊ + 2 * M : ℕ) : ℝ)
        < (K:ℝ) := by exact_mod_cast h
    push_cast at hcast
    linarith
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK1
  have hlogK0 : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
  have hlogp0 : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hM0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  set u : ℝ := (K:ℝ) ^ ((1:ℝ)/4) with hu
  have hu1 : (1:ℝ) ≤ u := by
    rw [hu]; exact Real.one_le_rpow (by exact_mod_cast hK1) (by norm_num)
  have hu4 : u ^ 4 = (K:ℝ) := by
    rw [hu, ← Real.rpow_natCast ((K:ℝ) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hK0.le]; norm_num
  have hlogK : Real.log (K:ℝ) ≤ 4 * u := by
    calc Real.log (K:ℝ) ≤ (K:ℝ) ^ ((1:ℝ)/4) / ((1:ℝ)/4) :=
          Real.log_natCast_le_rpow_div K (by norm_num)
      _ = 4 * u := by rw [hu]; ring
  have hnum : 4 * (q:ℝ) + (Real.log p + q * Real.log K) ≤ (8 * (q:ℝ) + Real.log p) * u := by
    nlinarith
  have hsq : ((4 * (q:ℝ) + (Real.log p + q * Real.log K)) / Real.log 2) ^ 2
      ≤ (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 * u ^ 2 := by
    have hstep : ((4 * (q:ℝ) + (Real.log p + q * Real.log K)) / Real.log 2) ^ 2
        ≤ ((8 * (q:ℝ) + Real.log p) * u / Real.log 2) ^ 2 := by gcongr
    calc _ ≤ ((8 * (q:ℝ) + Real.log p) * u / Real.log 2) ^ 2 := hstep
      _ = (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 * u ^ 2 := by field_simp
  set D : ℝ := (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hgoal : D * u ^ 2 + (M:ℝ) < (K:ℝ) := by
    nlinarith [sq_nonneg (u ^ 2 - 2 * D), hu1, hD0, hM0, hu4, h']
  linarith [hsq, hgoal]

@[expose]
def gamma_conj_bound {H: Type*}  [DecidableEq H] [Group H]  {N': Subgroup H} (gamma: MulAut N') := ∀ k: ℕ, (0 < k) →  ∀ g, ∃ p q: ℕ, 0 < p ∧ ∀ b: ℕ, 0 < b → ∀ a: ℕ, (0 < a) → (a < b) → ((Finset.image (fun x ↦ (List.map (fun (i:  ↥(Finset.Ico a b)) ↦ (gamma)^[k * ↑i] g) x.toList).prod))
        (Finset.Ico a b).attach.powerset).card ≤ p * (b^q) * (b - a)^q

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 40000 in
lemma exists_gamma_n_unipotent_center_N' {H: Type*} [DecidableEq H] [Group H] {N': Subgroup H} [N'_normal: N'.Normal] (N'_nilpotent: Group.IsNilpotent N') (hN': Subgroup.FG N') (gamma: MulAut N')
  (gamma_conj: gamma_conj_bound gamma):
     ∃ a, a ≠ 0 ∧ ∀ k: ℕ, 0 < k → ∃ n, ∀ g ∈ Subgroup.center N', Nat.iterate (fun x => x * ((gamma^[a*k]) x⁻¹)) n g = 1 := by

  classical


  let torsion := CommGroup.torsion (Subgroup.center N')
  have center_fg: Group.FG (Subgroup.center N') := by
    rw [Group.fg_iff_subgroup_fg]

    apply fg_of_subgroup_fg_nilpotent
    rw [Group.fg_iff_subgroup_fg]
    apply hN'
  have torsion_fg : Group.FG torsion := by
    simp
    rw [Subgroup.fg_iff_add_fg]
    have : Module.Finite ℤ (Additive (Subgroup.center N')) := Module.Finite.iff_addGroup_fg.mpr (by
      apply AddGroup.fg_of_group_fg
    )
    let foo: IsNoetherian ℤ (AddSubgroup.toIntSubmodule torsion.toAddSubgroup) := by
      infer_instance
    have h := IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule torsion.toAddSubgroup)
    rw [Submodule.fg_iff_addSubgroup_fg] at h
    simpa using h

  have fg_top: (⊤ : Subgroup (Subgroup.center N')).FG := by
    rw [← Group.fg_def]
    apply center_fg

    -- Submodule.FG.of_le
  have T_finite := CommGroup.finite_of_fg_isMulTorsion torsion (by
    simp [torsion]
    rw [IsMulTorsion]
    intro g
    have foo := g.prop
    rw [CommGroup.mem_torsion] at foo
    rw [isOfFinOrder_iff_pow_eq_one]
    rw [isOfFinOrder_iff_pow_eq_one] at foo
    obtain ⟨n, n_pos, hg⟩ := foo
    use n
    refine ⟨n_pos, ?_⟩
    rw [Subtype.ext_iff]
    exact hg
  )

  let gamma_center := MulAut.characteristic (Subgroup.center N') gamma
  have t_char: torsion.Characteristic := torsion_characteristic
  let torsion_N := Subgroup.map (Subgroup.subtype _) torsion
  let gamma_torsion := MonoidHom.domRestrict gamma.toMonoidHom torsion_N
  let new_gamma_torsion_hom := MonoidHom.codRestrict gamma_torsion torsion_N (by
    rw [Subgroup.characteristic_iff_map_le] at t_char
    specialize t_char
    intro x
    simp [torsion_N]
    use ?_
    .
      rw [CommGroup.mem_torsion]
      simp [gamma_torsion]
      rw [isOfFinOrder_iff_pow_eq_one]
      simp
      rw [← isOfFinOrder_iff_pow_eq_one]
      conv =>
        arg 1
        equals gamma.toMonoidHom x =>
          simp
      apply MonoidHom.isOfFinOrder
      have x_prop := x.prop
      unfold torsion_N at x_prop
      simp [-SetLike.coe_mem] at x_prop
      obtain ⟨x_mem, x_mem_torsion⟩ := x_prop
      rw [CommGroup.mem_torsion] at x_mem_torsion
      rw [isOfFinOrder_iff_pow_eq_one] at x_mem_torsion
      simp at x_mem_torsion
      rw [← isOfFinOrder_iff_pow_eq_one] at x_mem_torsion
      simpa using x_mem_torsion
    .
      simp [gamma_torsion]
      have char_center := Subgroup.centerCharacteristic (G := N')
      rw [Subgroup.characteristic_iff_map_eq] at char_center
      specialize char_center gamma
      rw [← char_center]
      simp
      have x_prop := x.prop
      unfold torsion_N at x_prop
      simp [-SetLike.coe_mem] at x_prop
      obtain ⟨x_center, hx⟩ := x_prop
      exact x_center
  )

  let new_gamma_torsion := MulAut.characteristic torsion_N gamma


  have finite_aut: Finite (MulAut (torsion_N)) := by infer_instance
  have fin_order_new_gamma := isOfFinOrder_of_finite new_gamma_torsion

  have order_pos: 0 < orderOf new_gamma_torsion := by
    rw [← Nat.ne_zero_iff_zero_lt]
    rw [orderOf_ne_zero_iff]
    apply fin_order_new_gamma

  have iter_gamma_coe: ∀ n, ∀ g, (⇑new_gamma_torsion)^[n] g = gamma^[n] g := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ]
      simp
      rw [ih]
      simp [new_gamma_torsion, new_gamma_torsion_hom, gamma_torsion]


  let gamma_lift := QuotientGroup.congr (torsion) torsion gamma_center (by
    rw [Subgroup.characteristic_iff_map_eq] at t_char
    specialize t_char gamma_center
    exact t_char
  )


  have gamma_mem_center:  ∀ g: Subgroup.center N', gamma g ∈ Subgroup.center N' := by
    intro g
    have center_char: (Subgroup.center N').Characteristic := by
      infer_instance
    rw [Subgroup.characteristic_iff_le_comap] at center_char
    specialize center_char (gamma) g.prop
    simp at center_char
    exact center_char

  have gamma_iter_mem_center: ∀ n, ∀ g: Subgroup.center N', gamma^[n] g ∈ Subgroup.center N' := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ]
      simp
      apply ih ⟨_, gamma_mem_center g⟩


  have swap_gamma_lift: ∀ g: Subgroup.center N', gamma_lift ↑g = ↑(⟨((gamma) g), by apply gamma_mem_center⟩ : Subgroup.center N') := by
    intro g
    simp [gamma_lift, gamma_center]
    rfl

  have swap_gamma_lift_iter: ∀ n, ∀ g: Subgroup.center N', gamma_lift^[n] ↑g = ↑(⟨((gamma^[n]) g), by apply gamma_iter_mem_center⟩ : Subgroup.center N') := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ']
      simp only [Function.comp_apply]
      rw [ih]
      rw [swap_gamma_lift]
      simp_rw [Function.iterate_succ']
      simp

  have unipotent_on_quot: ∃ a, 0 < a ∧ ∀ p: ℕ, 0 < p → ∃ n, ∀ g : (Subgroup.center ↥N') ⧸ torsion, Nat.iterate (fun x => x * ((gamma_lift^[a * orderOf new_gamma_torsion * p] x⁻¹))) n g = 1 := by
    wlog nontrivial_quot: Nontrivial ((Subgroup.center ↥N') ⧸ torsion)
    .
      clear this
      simp at nontrivial_quot
      use 1
      refine ⟨by simp, ?_⟩
      intro p hp
      use 1
      simp
      intro g
      have quot_subsingelton: Subsingleton ((Subgroup.center ↥N') ⧸ torsion) := by
        rw [QuotientGroup.subsingleton_iff]
        exact nontrivial_quot

      have g_eq := Subsingleton.eq_one g
      simp [g_eq]


    let foo: CommGroup (Subgroup.center N') := by infer_instance
    -- if the additive picture is wanted, this is *definitionally* the same type:
    have add_torsion_free: IsAddTorsionFree
        (Additive ↥(Subgroup.center ↥N') ⧸ AddCommGroup.torsion (Additive ↥(Subgroup.center ↥N'))) := by
      infer_instance

    let add_quot := (Additive ↥(Subgroup.center ↥N') ⧸ AddCommGroup.torsion (Additive ↥(Subgroup.center ↥N')))


    let fin_dim: Module.Finite ℤ add_quot := by infer_instance

    let gamma_add := gamma_lift.toAdditive.toAddMonoidHom.toIntLinearMap
    let B := (Module.finBasis ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion)))
    let gamma_matrix := gamma_add.toMatrix B B
    have invertible_gamma: Invertible gamma_matrix := {
      invOf := ((gamma_lift.toAdditive).symm.toAddMonoidHom).toIntLinearMap.toMatrix B B
      invOf_mul_self := by
        simp [gamma_matrix, gamma_add]
        rw [← LinearMap.toMatrix_mul]
        rw [← toIntLinearMap_comp_mul]
        simp
      mul_invOf_self := by
        simp [gamma_matrix, gamma_add]
        rw [← LinearMap.toMatrix_mul]
        rw [← toIntLinearMap_comp_mul]
        simp
    }

    let dim := Module.finrank ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion))
    let equiv (v: Fin _ → ℤ) := (Finsupp.linearEquivFunOnFinite ℤ _ (Fin dim)).symm v
    let remap (v: Fin _ → ℤ) := Finsupp.linearCombination _ B (equiv v)

    have gamma_matrix_mulVec: ∀ v: (Fin dim) → ℤ , remap ((gamma_matrix).mulVec (equiv v)) = Additive.ofMul (gamma_lift (Additive.toMul (remap v))) := by
      intro v
      unfold gamma_matrix
      rw [← Module.Basis.repr_linearCombination (v := (equiv v)) (b := B)]
      rw [LinearMap.toMatrix_mulVec_repr]
      simp [remap, gamma_add, equiv]


    have gamma_matrix_mulVec_pow: ∀ n: ℕ, ∀ v: (Fin dim) → ℤ , remap ((gamma_matrix^n).mulVec (equiv v)) = Additive.ofMul (gamma_lift^[n] (Additive.toMul (remap v))) := by
      intro n
      induction n with
      | zero =>
        intro v
        simp [remap, equiv]
      | succ n ih =>
        intro v
        rw [Function.iterate_succ_apply', pow_succ', ← Matrix.mulVec_mulVec]
        rw [show ((gamma_matrix ^ n).mulVec ⇑(equiv v))
              = ⇑(equiv ((gamma_matrix ^ n).mulVec ⇑(equiv v))) from rfl]
        rw [gamma_matrix_mulVec, ih]
        rfl


    have rank_nonzero: NeZero (Module.finrank ℤ (Additive (↥(Subgroup.center ↥N') ⧸ torsion))) := by
      apply NeZero.of_pos
      apply Module.finrank_pos


    have gamma_lift_conj: ∀ k: ℕ, (0 < k) →  ∀ g, ∃ p q: ℕ, 0 < p ∧ ∀ b: ℕ, 0 < b → ∀ a: ℕ, (0 < a) → (a < b) → (Finset.image (fun x ↦ (List.map (fun (i:  ↥(Finset.Ico a b)) ↦ (gamma_lift)^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * (b^q) * (b - a)^q := by

      -- Same shape as the `final_gamma` transport: the products live in
      -- `↥(Subgroup.center ↥N')`, mapped out injectively by `Subgroup.subtype` (where
      -- `gamma_conj` gives the bound) and surjectively by `QuotientGroup.mk'` (where it
      -- is wanted).
      classical
      exact conjBound_transport
        (fC := fun x : ↥(Subgroup.center ↥N') =>
          (⟨gamma x, gamma_mem_center x⟩ : ↥(Subgroup.center ↥N')))
        (fQ := ⇑gamma_lift) (fN := ⇑gamma)
        (QuotientGroup.mk' torsion) (QuotientGroup.mk'_surjective _)
        ((Subgroup.center ↥N').subtype) (Subgroup.subtype_injective _)
        (fun x => (swap_gamma_lift x).symm) (fun x => rfl) gamma_conj

    have eigen_norm_one: ∀ (k : Module.End.Eigenvalues (Matrix.toLin' (((unitOfInvertible gamma_matrix).val).map (Int.castRingHom ℂ)))), ‖k.val‖ = 1 := by
      apply int_matrix_poly_growth_eigenvalue
      .
        intro k hk v
        -- name the (fixed) group element the iterates are applied to
        set g : ↥(Subgroup.center ↥N') ⧸ torsion :=
          Additive.toMul ((Finsupp.linearCombination ℤ ⇑B)
            ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin dim)).symm v)) with hg


        obtain ⟨p, q, p_pos, hq⟩ := gamma_lift_conj ⌈Real.logb ‖k‖ 3⌉₊ (by
          simp
          apply Real.logb_pos
          . grind
          . grind
        ) g
        let K: ℕ := (⌈4 * ((8 * ↑q + Real.log ↑p) ^ 2 / Real.log 2 ^ 2) ^ 2⌉₊ + 2 * ⌈Real.logb ‖k‖ 3⌉₊) + 1


        have hpq := hq K (by simp [K]) ⌈Real.logb ‖k‖ 3⌉₊ (by
          simp
          apply Real.logb_pos
          . grind
          . grind
        ) (by
          simp [K]
          rw [two_mul]
          grw [Nat.le_ceil (a := Real.logb ‖k‖ 3)]
          grind
        )

        use p * K ^ q
        use q
        use K

        refine ⟨?_, ?_, ?_, ?_⟩
        . apply mul_pos
          . exact p_pos
          . apply pow_pos
            simp [K]

        . simp [K]
          rw [two_mul]
          grw [Nat.le_ceil (a := Real.logb ‖k‖ 3)]
          grind
        .
          -- Isolate `K` on the right of
          --   `X < Real.log 2 * (↑K - ↑⌈Real.logb ‖k‖ 3⌉₊) ^ (1/2)`.
          -- Divide by `Real.log 2 > 0`, bound the LHS by its absolute value (so no sign
          -- assumption on `X` is needed), rewrite `|y| = √(y ^ 2)` and use strict
          -- monotonicity of `√`, then move the subtraction across.  `K` is never unfolded.
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          rw [← Real.sqrt_eq_rpow, ← div_lt_iff₀' hlog2]
          refine lt_of_le_of_lt (le_abs_self _) ?_
          rw [← Real.sqrt_sq_eq_abs]
          refine Real.sqrt_lt_sqrt (sq_nonneg _) ?_
          rw [lt_sub_iff_add_lt]
          -- `K` still occurs on the left inside `Real.log ↑(p * K ^ q)`.  This splits that
          -- logarithm and eliminates the resulting `Real.log ↑K`, leaving a goal in `ℕ` with
          -- `K` alone on the right.
          refine log_pow_sq_lt_of_lt _ p q K p_pos ?_
          -- ⊢ ⌈4 * ((8 * ↑q + Real.log ↑p) ^ 2 / Real.log 2 ^ 2) ^ 2⌉₊
          --     + 2 * ⌈Real.logb ‖k‖ 3⌉₊ < K
          simp [K]
        .
          rw [← (Finset.card_image_iff (f := fun a => remap (Finsupp.equivFunOnFinite.symm a))).mpr]
          .
            rw [Finset.image_image]
            simp [remap, equiv]
            rw [Function.comp_def]
            simp_rw [map_sum]
            simp [remap, equiv] at gamma_matrix_mulVec_pow
            simp_rw [← pow_mul]
            simp_rw [gamma_matrix_mulVec_pow]
            -- Turn each subsum into `Additive.ofMul` of a product in the group, keeping the
            -- index set as the subtype `↥(Finset.Ico N_1 N_2)`.
            simp_rw [← ofMul_prod]
            -- `Additive.ofMul` is a bijection, so it does not affect the cardinality: pull it
            -- out of the image and discard it.
            rw [← Function.comp_def Additive.ofMul, ← Finset.image_image,
              Finset.card_image_of_injective _ (Equiv.injective _)]


            simp_rw [← Finset.prod_map_toList]

            grw [hpq]
            -- TODO - we might be able to make the goal stronger, if we don't actually need the factor of 2 in it
            rw [pow_mul']
            apply mul_le_mul
            . simp
            . apply Nat.le_pow
              simp
            . simp
            . simp
          . apply Function.Injective.injOn
            intro a b hab
            simp [remap, equiv] at hab
            rw [Function.Injective.eq_iff (linearIndependent_iff_injective_finsuppLinearCombination.mp ?_)] at hab
            . simpa using hab
            . apply Module.Basis.linearIndependent


    let a := KroneckerPow (unitOfInvertible gamma_matrix) eigen_norm_one
    use a
    refine ⟨(by
      apply KroneckerPow_pos
    ), ?_⟩
    intro p hp


    have unipotent_gamma_matrix := int_matrix_unipotent (by
      apply Module.finrank_pos
    ) (unitOfInvertible gamma_matrix) (by
      apply eigen_norm_one
    ) (n := p * orderOf new_gamma_torsion) (hn := by positivity)
    obtain ⟨n, hm⟩ := unipotent_gamma_matrix


    use n
    intro g
    apply_fun (fun f => f.toLin (Module.finBasis _ _) (Module.finBasis _ _)) at hm
    rw [LinearMap.ext_iff] at hm
    specialize hm g
    simp [gamma_matrix] at hm
    simp [gamma_add] at hm
    conv at hm =>
      rhs
      equals 0 => rfl


    apply_fun (fun f => (f).toMul) at hm
    conv at hm =>
      rhs
      equals 1 => rfl

    rw [← neg_sub] at hm
    rw [neg_pow] at hm
    simp at hm
    rw [Module.End.mul_eq_comp] at hm
    simp at hm
    simp [Function.comp_def] at hm
    apply (LinearMap.ker_eq_bot'.mp (by
      ext a
      clear hm
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        simp
        simp at ih
        exact ih
    )) at hm
    rw [← toMul_eq_one] at hm
    rw [← hm]
    clear hm

    have x_mul_gamma_eq: ∀ q: ℕ, (fun x => x * (⇑gamma_lift)^[q] x⁻¹) = Additive.toMul ∘ (-((MonoidHom.toAdditive gamma_lift.toMonoidHom).toIntLinearMap ^ (q) - LinearMap.id)).toFun ∘ (Additive.ofMul) := by
      intro q
      ext x
      conv =>
        rhs
        equals Additive.toMul ((-((MonoidHom.toAdditive gamma_lift.toMonoidHom).toIntLinearMap ^ (q) - LinearMap.id)).toFun (Additive.ofMul x)) =>
          rfl
      simp
      rw [toIntLinearMap_pow_apply]
      simp
      rw [Function.comp_def]
      rw [div_eq_mul_inv]
      simp
      rfl

    rw [x_mul_gamma_eq]
    simp
    rw [Module.End.coe_pow]
    -- collapse the `Matrix.toLin B B (LinearMap.toMatrix B B _)` round-trip, which plain
    -- `rfl` cannot see through
    rw [Matrix.toLin_toMatrix]

    -- TODO - figure out how the order gets swapped
    have mul_eq: a * orderOf new_gamma_torsion * p = p * orderOf new_gamma_torsion * a := by ring
    simp_rw [mul_eq]
    rfl


  obtain ⟨quot_pow, quot_pow_pos, h_quot_pow⟩ := unipotent_on_quot
  use (quot_pow * ( orderOf new_gamma_torsion))
  refine ⟨by positivity, ?_⟩
  intro p hp

  obtain ⟨quot_n, h_quot_n⟩ := h_quot_pow p hp


  use quot_n + 1
  intro g hg


  have new_gamma_pow: new_gamma_torsion^[quot_pow * (orderOf new_gamma_torsion) * p] = id := by
    rw [mul_comm (a := quot_pow), mul_assoc, Function.iterate_mul]
    rw [mul_aut_iterate]
    simp

  have orig_new_gamma_pow := new_gamma_pow


  specialize h_quot_n (QuotientGroup.mk ⟨g, hg⟩)


  have swap_iter: ∀ n, ∀ g: Subgroup.center N', (fun x ↦ x * (gamma_lift^[quot_pow * orderOf new_gamma_torsion * p]) x⁻¹)^[n] g = QuotientGroup.mk ⟨((fun x ↦ x * (gamma^[quot_pow * orderOf new_gamma_torsion * p]) x⁻¹)^[n] g), (by
    rw [mul_aut_iterate]
    simp
    induction n generalizing g with
    | zero =>
      simp
    | succ n ih =>
      simp
      have mul_mem_center: (↑g * ((gamma ^ (quot_pow * orderOf new_gamma_torsion * p )) ↑g)⁻¹) ∈ Subgroup.center N' := by
        apply Subgroup.mul_mem
        . simp
        .
          simp
          have center_char: (Subgroup.center N').Characteristic := by
            infer_instance
          rw [Subgroup.characteristic_iff_le_comap] at center_char
          specialize center_char (gamma ^ (quot_pow * orderOf new_gamma_torsion * p)) g.prop
          simpa using center_char
      conv =>
        pattern (↑g * ((gamma ^ (quot_pow * orderOf new_gamma_torsion * p)) ↑g)⁻¹)
        equals ↑(⟨_, mul_mem_center⟩ : Subgroup.center N') =>
          rfl
      apply ih

  )⟩ := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ']
      rw [Function.comp_def]
      beta_reduce
      rw [ih]
      simp_rw [Function.iterate_succ']
      simp
      rw [swap_gamma_lift_iter]
      rfl


  rw [swap_iter] at h_quot_n
  rw [QuotientGroup.eq_one_iff] at h_quot_n
  rw [Function.iterate_succ']
  simp


  rw [funext_iff] at new_gamma_pow
  apply Subgroup.mem_map_of_mem (Subgroup.center ↥N').subtype at h_quot_n
  specialize new_gamma_pow ⟨_, h_quot_n⟩
  simp at new_gamma_pow


  rw [Subtype.ext_iff] at new_gamma_pow
  rw [iter_gamma_coe] at new_gamma_pow
  simp at new_gamma_pow
  simp_rw [new_gamma_pow]
  simp

  -- OLD CODE


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 160000 in
/--{G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) [H.Normal]--/
lemma exists_gamma_n_unipotent_N' {H: Type*} [DecidableEq H] [Group H] {N': Subgroup H} [N'_normal: N'.Normal] (N'_nilpotent: Group.IsNilpotent N') (hN': Subgroup.FG N') (gamma: MulAut N') (gamma_conj: gamma_conj_bound gamma):
    ∀ p: ℕ, 0 < p → ∃ a n, a ≠ 0 ∧ ∀ g : N', Nat.iterate (fun x => x * ((gamma^[a*p]) x⁻¹)) n g = 1 := by


  classical
  by_cases N'_subsingle: Subsingleton N'
  .
    intro p hp
    use 1
    use 1
    simp
    intro a ha
    have order := Subsingleton.orderOf_eq (⟨_, ha⟩ : N')
    simp at order
    simp [order, iteratedCommutator]
    rw [mul_aut_iterate]
    simp


  induction hn: Group.nilpotencyClass N' using Nat.strong_induction_on generalizing H N' with
  | h n ih =>

    let new_N' := (⊤ : Subgroup (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N')))
    let first_map := (MulAut.congr (Subgroup.topEquiv (G := ↥N' ⧸ Subgroup.center ↥N'))).symm
    let aut_transfer := first_map
    let gamma_quot := QuotientGroup.congr (Subgroup.center N') (Subgroup.center N') gamma (by
      conv =>
        lhs
        arg 1
        equals gamma.toMonoidHom =>
          simp
      rw [Subgroup.characteristic_iff_map_eq.mp]
      exact Subgroup.centerCharacteristic
    )
    let final_gamma := aut_transfer gamma_quot

    by_cases top_subsingle: Subsingleton (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N'))
    .
      intro p hp
      obtain ⟨z_a, h_z_a, z_a_temp⟩ := exists_gamma_n_unipotent_center_N' (N' := N') (N'_nilpotent) (hN') gamma gamma_conj
      obtain ⟨z_n, h_z_unipotent⟩ := z_a_temp p hp
      use z_a

      use z_n
      refine ⟨by positivity, ?_⟩
      intro g
      have foo := top_subsingle.allEq
      simp at foo
      have center_top: Subgroup.center N' = ⊤ := by
        rw [← QuotientGroup.subsingleton_iff]
        exact {
          allEq := foo
        }


      apply h_z_unipotent
      simp [center_top]

    have foo := ih (Group.nilpotencyClass (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N'))) (by
      grw [Subgroup.nilpotencyClass_le]
      simp [nilpotencyClass_quotient_center]
      rw [← hn]
      simp
      by_contra!
      simp at this
      rw [nilpotencyClass_zero_iff_subsingleton] at this
      contradiction
    ) (H := N' ⧸ Subgroup.center N') (N' := ⊤) (by simp; apply Group.nilpotent_quotient_of_nilpotent) (by
      have fg_quot: Group.FG (↥N' ⧸ Subgroup.center ↥N') := by
        rw [← Group.fg_iff_subgroup_fg] at hN'
        apply QuotientGroup.fg

      rw [← Group.fg_iff_subgroup_fg]
      apply Subgroup.fg_of_index_ne_zero
    ) final_gamma (by
      classical
      refine conjBound_transport (fC := ⇑gamma) (fQ := ⇑final_gamma) (fN := ⇑gamma)
        (((Subgroup.topEquiv (G := ↥N' ⧸ Subgroup.center ↥N')).symm.toMonoidHom).comp
          (QuotientGroup.mk' (Subgroup.center ↥N')))
        ?_ (MonoidHom.id ↥N') Function.injective_id ?_ (fun x => rfl) gamma_conj
      · exact (Subgroup.topEquiv (G := ↥N' ⧸ Subgroup.center ↥N')).symm.surjective.comp
          (QuotientGroup.mk'_surjective _)
      · intro x
        simp [final_gamma, aut_transfer, first_map, gamma_quot, QuotientGroup.congr_mk]
    ) top_subsingle rfl

    clear ih
    intro p hp
    obtain ⟨z_a, h_z_a, z_a_temp⟩ := exists_gamma_n_unipotent_center_N' (N' := N') (N'_nilpotent) (hN') (gamma) (by
      apply gamma_conj
    )

    obtain ⟨a, n, ha, h_prev⟩ := foo (z_a * p) (by positivity)
    obtain ⟨z_n, h_z_unipotent⟩ := z_a_temp (a * p) (by positivity)

    use a * z_a
    use z_n + n
    refine ⟨by positivity, ?_⟩
    intro g
    let g_h_prev: (⊤ : Subgroup (⊤ : Subgroup (↥N' ⧸ Subgroup.center ↥N'))) := ⟨⟨g, by simp⟩, by simp⟩
    specialize h_prev g_h_prev
    rw [Function.iterate_add_apply]

    specialize h_z_unipotent ((fun x ↦ x * ((gamma^[a*z_a*p]) (x⁻¹)))^[n] g) ?_
    .

      have swap_gamma_base: ∀ x, (gamma) x = ((final_gamma) ⟨x, by simp⟩).val := by
        intro x
        simp [final_gamma, aut_transfer, first_map]
        rfl

      have swap_gamma: ∀ x, ∀ m: ℕ, (gamma^[m]) x = ((final_gamma^[m]) ⟨x, by simp⟩).val := by
        intro x m
        induction m generalizing x with
        | zero =>
          simp
        | succ m ih_m =>
          rw [Function.iterate_succ]
          simp
          rw [ih_m]
          rw [swap_gamma_base]


      have coe_iter: ∀ m: ℕ, ((fun x ↦ x * (final_gamma^[m]) x⁻¹)^[n] g_h_prev).val = (fun x ↦ x * (gamma^[m]) x⁻¹)^[n] g := by
        clear h_prev
        intro m
        induction n with
        | zero =>
          simp
          simp [g_h_prev]
        | succ n ind_n =>
          simp_rw [Function.iterate_succ']
          simp
          simp at ind_n
          simp [ind_n]
          rw [swap_gamma]
          simp
          rw [← ind_n]

      rw [← QuotientGroup.eq_one_iff]
      rw [← coe_iter]
      simp_rw [← mul_assoc] at h_prev
      simpa using h_prev


    .
      simp_rw [mul_aut_iterate] at h_z_unipotent
      rw [mul_aut_iterate]
      simp_rw [← mul_assoc] at h_z_unipotent
      have reorder: z_a * a * p = a * z_a * p := by ring
      simp_rw [reorder] at h_z_unipotent
      exact h_z_unipotent


--   -- use pow_eq_one_of_norm_le_one (Kronecker's Theorem) once mathlib is bumped


--   --   sorry


--   -- Module.free_of_finite_type_torsion_free'
--   -- QuotientGroup.instIsMulTorsionFree


--   --   -- QuotientGroup.nontrivial_iff
--   --   apply Module.finrank_pos


--   --     sorry

--   --   sorry


--   --   simp [K]
--   --   sorry


--   --   -- rw [MulEquiv.toMonoidHom_eq_coe]
--   --   -- rw [MonoidHom.coe_coe]

--   --   -- rw [MonoidHom.pow_map]

--   --   -- simp
--   --   -- dsimp only [ord_fin]


--   --   sorry


--   --   use sorry
--   --   simp


--   --   sorry


--   -- simp at ord_fin
--   --rw [Nat.card_prod] at ord_fin
