/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

The following was proved by Aristotle:

- lemma star_normal_maxGenEigenspace_eq_eigenspace  {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] (f: Module.End ℂ A) (hf: IsStarNormal f) (k: ℂ):
    f.maxGenEigenspace k = f.eigenspace k
-/

import Mathlib

lemma star_normal_toContinuousLinearMap {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]  (f: A →ₗ[ℂ] A):
    IsStarNormal f ↔ IsStarNormal (LinearMap.toContinuousLinearMap f) := by

  rw [isStarNormal_iff]
  rw [isStarNormal_iff]
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  rw [LinearMap.star_eq_adjoint]
  rw [commute_iff_eq]
  rw [commute_iff_eq]
  rw [LinearMap.ext_iff]
  rw [ContinuousLinearMap.ext_iff]
  simp

-- https://math.stackexchange.com/a/4217008/367657
lemma eigenvalue_adjoint {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] {f: Module.End ℂ A} {k: ℂ} {v: A} (hf: IsStarNormal f):
  f.HasEigenvector k v ↔ (star f).HasEigenvector (star k) v := by

  -- TODO - figure out a way to re-use 'spectrum.map_star'
  have hf_cont := hf
  rw [star_normal_toContinuousLinearMap] at hf_cont
  rw [Module.End.hasEigenvector_iff]
  rw [Module.End.hasEigenvector_iff]
  have ker_toContinuousLinearMap : ∀ X : A →ₗ[ℂ] A,
      (LinearMap.toContinuousLinearMap X).ker = LinearMap.ker X := fun X => by
    simp [LinearMap.coe_toContinuousLinearMap]
  by_cases v_eq_zero: v = 0
  . simp [v_eq_zero]
  .
    simp only [ne_eq, v_eq_zero, not_false_eq_true, and_true]
    rw [Module.End.eigenspace_def]
    rw [← ker_toContinuousLinearMap]
    rw [← ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker]
    .
      rw [← LinearMap.adjoint_toContinuousLinearMap]
      rw [ker_toContinuousLinearMap]
      rw [Module.End.eigenspace_def]
      rw [LinearMap.star_eq_adjoint]
      rw [map_sub]
      rw [LinearEquiv.map_smulₛₗ]
      conv =>
        pattern 1
        equals LinearMap.id =>
          rw [LinearMap.ext_iff]
          simp
      rw [LinearMap.adjoint_id]
      simp
    .
      rw [← star_normal_toContinuousLinearMap]
      apply Commute.isStarNormal_sub
      rw [commute_iff_eq]
      simp

lemma eigenvector_orthogonal {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] (f: Module.End ℂ A) (j k: ℂ) (v w: A)
  (hf: IsStarNormal f) (hjv: f.HasEigenvector j v) (hkw: f.HasEigenvector k w) (hjk: j ≠ k): inner ℂ v w = 0 := by

  have first_eq: inner ℂ v (f w) = k * (inner ℂ v w) := by
    apply Module.End.HasEigenvector.apply_eq_smul at hkw
    rw [hkw]
    simp

  have second_eq: inner ℂ v (f w) = j * (inner ℂ v w) := by
    rw [← LinearMap.adjoint_inner_left]
    rw [eigenvalue_adjoint hf] at hjv
    apply Module.End.HasEigenvector.apply_eq_smul at hjv
    rw [LinearMap.star_eq_adjoint] at hjv
    rw [hjv]
    rw [inner_smul_left]
    simp

  rw [second_eq] at first_eq
  simp [hjk] at first_eq
  exact first_eq

lemma eigenspace_orthogonal  {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] (f: Module.End ℂ A) (hf: IsStarNormal f) (j k: ℂ) (hjk: j ≠ k):
    f.eigenspace k ⟂ f.eigenspace j := by

  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  by_cases v_eq_zero: v = 0
  . simp [v_eq_zero]

  by_cases w_eq_zero: w = 0
  . simp [w_eq_zero]
  rw [eigenvector_orthogonal f k j]
  . exact hf
  .
    rw [Module.End.hasEigenvector_iff]
    refine ⟨hv, v_eq_zero⟩
  .
    rw [Module.End.hasEigenvector_iff]
    refine ⟨hw, w_eq_zero⟩
  . exact id (Ne.symm hjk)

noncomputable section AristotleLemmas

/-
For a star-normal operator f, the kernel of f^2 is equal to the kernel of f.
-/
lemma IsStarNormal.ker_sq_eq_ker {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (f : Module.End ℂ A) (hf : IsStarNormal f) :
    LinearMap.ker (f ^ 2) = LinearMap.ker f := by
      -- Let's take an element x in the kernel of f squared. Then f(f(x)) = 0.
      have h1 : ∀ x, f (f x) = 0 → f x = 0 := by
        -- Since $f$ is star-normal, we have $f^* f = f f^*$. Therefore, $f^*(f(x)) = f(f^*(x))$.
        have h_comm : ∀ x, f.adjoint (f x) = f (f.adjoint x) := by
          -- Since $f$ is star-normal, we have $f * f^* = f^* * f$. Therefore, for any $x$, $f(f^*(x)) = f^*(f(x))$.
          have h_comm : f * f.adjoint = f.adjoint * f := by
            cases hf;
            (expose_names; exact id (Commute.symm star_comm_self));
          exact fun x => by simpa using congr_arg ( fun g => g x ) h_comm.symm;
        -- Since $f$ is star-normal, we have $f^* f = f f^*$. Therefore, $f^*(f(x)) = f(f^*(x))$. Applying $f^*$ to both sides of $f(f(x)) = 0$, we get $f^*(f(f(x))) = f^*(0) = 0$.
        have h_apply_adjoint : ∀ x, f (f x) = 0 → f.adjoint (f x) = 0 := by
          intro x hx
          have h_apply_adjoint : inner ℂ (f.adjoint (f x)) (f.adjoint (f x)) = inner ℂ (f x) (f (f.adjoint (f x))) := by
            rw [ ← LinearMap.adjoint_inner_right ];
            rw [ LinearMap.adjoint_adjoint ];
          simp_all +decide [ ← h_comm ];
        intro x hx
        have h_inner : inner ℂ (f x) (f x) = inner ℂ x (f.adjoint (f x)) := by
          rw [ LinearMap.adjoint_inner_right ];
        simp_all +decide [ inner_self_eq_norm_sq_to_K ];
      aesop

end AristotleLemmas

lemma star_normal_maxGenEigenspace_eq_eigenspace  {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] {f: Module.End ℂ A} (hf: IsStarNormal f) {k: ℂ}:
    f.maxGenEigenspace k = f.eigenspace k := by
  apply le_antisymm;
  · intro x hx
    aesop;
    -- Since $f$ is star-normal, we have $\ker((f - kI)^2) = \ker(f - kI)$.
    have h_ker_sq_eq_ker : LinearMap.ker ((f - k • 1) ^ 2) = LinearMap.ker (f - k • 1) := by
      apply IsStarNormal.ker_sq_eq_ker;
      -- Since $f$ is star-normal, we have $f * star f = star f * f$. Therefore, $(f - k • 1) * star (f - k • 1) = star (f - k • 1) * (f - k • 1)$.
      have h_star_normal : (f - k • 1) * star (f - k • 1) = star (f - k • 1) * (f - k • 1) := by
        simp_all +decide [ sub_mul, mul_sub, smul_sub, sub_smul ];
        simp_all +decide [ sub_eq_iff_eq_add, IsStarNormal, smul_smul ];
        simp_all +decide [ mul_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm ];
        exact Eq.symm (star_comm_self' f);
      exact (isStarNormal_iff (f - k • 1)).mpr (id (Eq.symm h_star_normal));
    -- By induction on $w$, we can show that $\ker((f - kI)^w) = \ker(f - kI)$ for all $w \geq 1$.
    have h_ker_pow_eq_ker : ∀ w ≥ 1, LinearMap.ker ((f - k • 1) ^ w) = LinearMap.ker (f - k • 1) := by
      intro w hw
      induction' w, Nat.succ_le.mpr hw using Nat.le_induction with w hw ih;
      · simp +decide;
      · simp_all +decide [ pow_succ, LinearMap.ker_comp ];
        simp_all +decide [ SetLike.ext_iff, LinearMap.mem_ker ];
        intro x; specialize ih ( f x - k • x ) ; simp_all +decide [ sub_eq_iff_eq_add, pow_succ, mul_sub, sub_mul ] ;
    by_cases hw : 1 ≤ w <;> aesop;
    replace h_ker_pow_eq_ker := SetLike.ext_iff.mp ( h_ker_pow_eq_ker w hw ) x; aesop;
    exact eq_of_sub_eq_zero h_ker_pow_eq_ker;
  · exact Module.End.eigenspace_le_maxGenEigenspace

#print axioms star_normal_maxGenEigenspace_eq_eigenspace
