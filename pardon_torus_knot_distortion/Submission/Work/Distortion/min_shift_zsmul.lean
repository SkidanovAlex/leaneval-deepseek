import Mathlib

/-!
# Reduction of the "min of `|y|` and `T - |y|`" shift invariant

For a real period `T ≥ 0`, the map `y ↦ min |y| (T - |y|)` (on the range `|y| ≤ T`)
agrees with the distance of `y` to the lattice `T ℤ`; equivalently it is the norm of
the class of `y` in the additive circle `AddCircle T`.  Since `x` and `x + n * T`
have the same class in `AddCircle T`, this quantity is unchanged.

This is the elementary fact underlying `Work.Distortion.min_shift_zsmul`.
-/

namespace Work.Distortion

/-- For `|y| ≤ 1`, the quantity `min |y| (1 - |y|)` is the distance of `y` to `ℤ`,
expressed via `Int.fract`. -/
lemma min_fract_eq_min_abs {y : ℝ} (hy : |y| ≤ 1) :
    min (Int.fract y) (1 - Int.fract y) = min |y| (1 - |y|) := by
  rcases le_or_gt 0 y with hy0 | hy0
  · rcases lt_or_eq_of_le ((abs_le.mp hy).2) with hlt | heq
    · rw [Int.fract_eq_self.mpr ⟨hy0, hlt⟩, abs_of_nonneg hy0]
    · subst heq
      rw [Int.fract_one, abs_one]
      norm_num
  · have hy1 : -1 ≤ y := (abs_le.mp hy).1
    have hf : Int.fract y = y + 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, -1, by ring⟩
    rw [hf, abs_of_neg hy0]
    rw [show (1 : ℝ) - (y + 1) = -y from by ring]
    rw [show (1 : ℝ) - (-y) = 1 + y from by ring]
    rw [min_comm]
    congr 1
    ring

/-- For `T > 0` and `|y| ≤ T`, the norm of the class of `y` in `AddCircle T` equals
`min |y| (T - |y|)`. -/
lemma norm_addCircle_eq_min {T : ℝ} (hT : 0 < T) {y : ℝ} (hy : |y| ≤ T) :
    ‖(y : AddCircle T)‖ = min |y| (T - |y|) := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hTinv : |T⁻¹| = T⁻¹ := abs_of_pos (inv_pos.mpr hT)
  have hu1 : |T⁻¹ * y| ≤ 1 := by
    rw [abs_mul, hTinv, ← div_eq_inv_mul, div_le_one hT]
    exact hy
  rw [AddCircle.norm_eq' T hT]
  rw [abs_sub_round_eq_min]
  rw [min_fract_eq_min_abs hu1]
  rw [mul_min_of_nonneg _ _ hT.le]
  have h1 : T * |T⁻¹ * y| = |y| := by
    rw [abs_mul, hTinv, ← mul_assoc, mul_inv_cancel₀ hTne, one_mul]
  have h2 : T * (1 - |T⁻¹ * y|) = T - |y| := by
    rw [mul_sub, mul_one, h1]
  rw [h1, h2]

theorem min_shift_zsmul (T x : ℝ) (n : ℤ) (hT : 0 ≤ T) (hx : |x| ≤ T)
    (hy : |x + n * T| ≤ T) :
    min |x + n * T| (T - |x + n * T|) = min |x| (T - |x|) := by
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · subst hT0
    have hx0 : |x| = 0 := le_antisymm hx (abs_nonneg x)
    have hxz : x = 0 := abs_eq_zero.mp hx0
    subst hxz
    simp
  · have e1 : ‖(x : AddCircle T)‖ = min |x| (T - |x|) := norm_addCircle_eq_min hTpos hx
    have e2 : ‖(↑(x + n * T) : AddCircle T)‖ = min |x + n * T| (T - |x + n * T|) :=
      norm_addCircle_eq_min hTpos hy
    have hcoe : (↑(x + n * T) : AddCircle T) = (↑x : AddCircle T) := by
      rw [show x + n * T = x + n • T by rw [zsmul_eq_mul]]
      rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
    rw [← e2, ← e1, hcoe]

end Work.Distortion
