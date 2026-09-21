import Mathlib

namespace Work.OddVolterra.RowIdentity

/-- The truncated power `z ^ n * √z` (which vanishes identically for `z ≤ 0`) coincides
everywhere with the real power `z ^ (n + 1/2)`.  For `z ≥ 0` this is the usual additivity of
`Real.rpow`, while for `z < 0` both sides vanish: the left one because `√z = 0`, and the
right one because `cos ((n + 1/2) π) = 0`. -/
theorem pow_mul_sqrt_eq_rpow (n : ℕ) (z : ℝ) :
    z ^ n * Real.sqrt z = z ^ (n + 1 / 2 : ℝ) := by
  rcases le_or_gt 0 z with hz | hz
  · rw [Real.sqrt_eq_rpow z, ← Real.rpow_natCast z n,
      ← Real.rpow_add' hz (by positivity : ((n : ℝ) + 1 / 2) ≠ 0)]
  · rw [Real.sqrt_eq_zero_of_nonpos hz.le, mul_zero, Real.rpow_def_of_neg hz]
    have hpi : ((n : ℝ) + 1 / 2) * Real.pi = ↑n * Real.pi + Real.pi / 2 := by ring
    rw [hpi]
    have hcos : Real.cos (↑n * Real.pi + Real.pi / 2) = 0 := by
      rw [Real.cos_eq_zero_iff]
      exact ⟨(n : ℤ), by push_cast; ring⟩
    rw [hcos, mul_zero]

theorem contDiff_trunc_pow_sqrt (n : ℕ) :
    ContDiff ℝ n (fun z : ℝ => z ^ n * Real.sqrt z) := by
  rw [show (fun z : ℝ => z ^ n * Real.sqrt z) = fun z => z ^ (n + 1 / 2 : ℝ) from
    funext (pow_mul_sqrt_eq_rpow n)]
  exact Real.contDiff_rpow_const_of_le (p := (n : ℝ) + 1 / 2) (by norm_num)

end Work.OddVolterra.RowIdentity
