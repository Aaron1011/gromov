import Mathlib

open scoped Matrix.L2OpNorm

lemma shrinking_conjugators (n: ℕ) (g h: Matrix.unitaryGroup (Fin n) ℂ):
  ‖⁅g, h⁆.val - 1‖ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
  dsimp only [Bracket.bracket]
  calc
    _ = ‖((g* h).val - (h * g).val) * (g⁻¹ * h⁻¹)‖ := by
      rw [sub_mul]
      repeat rw [ ← Submonoid.coe_mul]
      conv =>
        rhs
        arg 1
        rhs
        arg 1
        equals 1 => group
      repeat rw [← mul_assoc]
      simp
    _ = ‖((g* h).val - (h * g).val)‖ := by
      rw [ ← Submonoid.coe_mul]
      rw [CStarRing.norm_mul_coe_unitary]
    _ = ‖(g* h).val - g - h + 1 - ((h*g).val - h - g + 1)‖ := by
      abel
    _ = ‖(g.val - 1)*(h.val - 1) - (h.val - 1)*(g.val - 1)‖ := by
      conv =>
        rhs
        repeat rw [mul_sub]
        repeat rw [sub_mul]
      field_simp
      abel_nf
    _ ≤ ‖(g.val - 1)*(h.val - 1)‖ + ‖(h.val - 1)*(g.val - 1)‖ := by
      apply norm_sub_le
    _ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
      have norm_sub_g := Matrix.l2_opNorm_mul (g.val - 1) (h.val - 1)
      have norm_sub_h := Matrix.l2_opNorm_mul (h.val - 1) (g.val - 1)
      rw [mul_comm] at norm_sub_h
      linarith
