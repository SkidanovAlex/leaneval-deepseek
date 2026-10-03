import Mathlib

namespace Work.KMTAreas.A4

/-- Elementary decay arithmetic: for `M ≥ 3` and `1 ≤ y`, `y/16 ≤ x` the quantity
`√(x^{-M}) = x^{-M/2}` is dominated by `16^{M/2} · y^{-M/2}`.  The constant
`16^{M/2} = 4^M` is exactly the loss produced by the constraint `x ≥ y/16`. -/
theorem sivDecayArith (M : ℕ) (hM : 2 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x y : ℝ), 1 ≤ y → y / 16 ≤ x →
      Real.sqrt (x ^ (-(M : ℝ))) ≤ K * y ^ (-((M : ℝ) / 2)) := by
  refine ⟨(16 : ℝ) ^ ((M : ℝ) / 2), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro x y hy hx
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hx0 : 0 < x := by linarith
  have hy16 : 0 < y / 16 := by linarith
  have hc : -((M : ℝ) / 2) ≤ 0 := by
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hsqrt : Real.sqrt (x ^ (-(M : ℝ))) = x ^ (-((M : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    ring_nf
  rw [hsqrt]
  calc x ^ (-((M : ℝ) / 2)) ≤ (y / 16) ^ (-((M : ℝ) / 2)) :=
        Real.rpow_le_rpow_of_nonpos hy16 hx hc
    _ = ((1 / 16 : ℝ) * y) ^ (-((M : ℝ) / 2)) := by ring_nf
    _ = (1 / 16 : ℝ) ^ (-((M : ℝ) / 2)) * y ^ (-((M : ℝ) / 2)) := by
        rw [Real.mul_rpow (by norm_num) hy0.le]
    _ = (16 : ℝ) ^ ((M : ℝ) / 2) * y ^ (-((M : ℝ) / 2)) := by
        congr 1
        rw [show (1 / 16 : ℝ) = (16 : ℝ)⁻¹ by norm_num,
          Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 16),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16), inv_inv]

end Work.KMTAreas.A4
