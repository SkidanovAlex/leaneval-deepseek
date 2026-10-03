import Mathlib

namespace Work.KMTAreas.SupNorm

/-- Auxiliary identity: `A ^ q * √(B/A) = A ^ (q - 1/2) * B ^ (1/2)` for `A, B > 0`. -/
private lemma rpow_sqrt_aux_left {A B q : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A ^ q * Real.sqrt (B / A) = A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) := by
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hA
  have hB0 : (0 : ℝ) ≤ B := le_of_lt hB
  have hsq : Real.sqrt (B / A) = B ^ (1 / 2 : ℝ) * A ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hB0 hA0]
    rw [div_eq_mul_inv, ← Real.rpow_neg hA0 (1 / 2 : ℝ)]
  calc A ^ q * Real.sqrt (B / A)
      = A ^ q * (B ^ (1 / 2 : ℝ) * A ^ (-(1 / 2) : ℝ)) := by rw [hsq]
    _ = (A ^ q * A ^ (-(1 / 2) : ℝ)) * B ^ (1 / 2 : ℝ) := by ring
    _ = A ^ (q + -(1 / 2)) * B ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hA]
    _ = A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) := by
          rw [show q + -(1 / 2) = q - 1 / 2 by ring]

/-- Auxiliary identity: `B ^ q * (√(B/A)) ^ (1 - 2q) = A ^ (q - 1/2) * B ^ (1/2)`
for `A, B > 0`. -/
private lemma rpow_sqrt_aux_right {A B q : ℝ} (hA : 0 < A) (hB : 0 < B) :
    B ^ q * (Real.sqrt (B / A)) ^ (1 - 2 * q) = A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) := by
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hA
  have hB0 : (0 : ℝ) ≤ B := le_of_lt hB
  have hBA0 : (0 : ℝ) ≤ B / A := div_nonneg hB0 hA0
  calc B ^ q * (Real.sqrt (B / A)) ^ (1 - 2 * q)
      = B ^ q * (B / A) ^ ((1 / 2 : ℝ) * (1 - 2 * q)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hBA0 (1 / 2 : ℝ) (1 - 2 * q)]
    _ = B ^ q * (B / A) ^ ((1 - 2 * q) / 2) := by
          rw [show (1 / 2 : ℝ) * (1 - 2 * q) = (1 - 2 * q) / 2 by ring]
    _ = B ^ q * (B ^ ((1 - 2 * q) / 2) / A ^ ((1 - 2 * q) / 2)) := by
          rw [Real.div_rpow hB0 hA0]
    _ = (B ^ q * B ^ ((1 - 2 * q) / 2)) / A ^ ((1 - 2 * q) / 2) := by ring
    _ = B ^ (q + (1 - 2 * q) / 2) / A ^ ((1 - 2 * q) / 2) := by
          rw [← Real.rpow_add hB q ((1 - 2 * q) / 2)]
    _ = B ^ (1 / 2 : ℝ) / A ^ ((1 - 2 * q) / 2) := by
          rw [show q + (1 - 2 * q) / 2 = (1 / 2 : ℝ) by ring]
    _ = B ^ (1 / 2 : ℝ) * A ^ (-((1 - 2 * q) / 2)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hA0 ((1 - 2 * q) / 2)]
    _ = B ^ (1 / 2 : ℝ) * A ^ (q - 1 / 2) := by
          rw [show -((1 - 2 * q) / 2) = q - 1 / 2 by ring]
    _ = A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) := by rw [mul_comm]

theorem min_inv_sq_rpow_algebra_real {A B q : ℝ} (hA : 0 < A) (hB : 0 < B) (hq : 1 / 2 < q) :
    2 * (A ^ q * Real.sqrt (B / A) + B ^ q * (Real.sqrt (B / A)) ^ (1 - 2 * q) / (2 * q - 1))
      = 2 * A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) * (2 * q / (2 * q - 1)) := by
  have hc : (0 : ℝ) < 2 * q - 1 := by linarith
  have hcne : 2 * q - 1 ≠ 0 := ne_of_gt hc
  rw [rpow_sqrt_aux_left hA hB, rpow_sqrt_aux_right hA hB]
  field_simp
  ring

end Work.KMTAreas.SupNorm
