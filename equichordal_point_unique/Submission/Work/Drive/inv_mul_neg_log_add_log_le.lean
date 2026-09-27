import Mathlib

namespace Work.Drive

/-- Since `m ≤ s`, `log m ≤ log s`, and the identity
`(1/k) * (-log (d^k * s)) + log d = (1/k) * (-log s)` reduces the claim to
`(1/k) * (-log s) ≤ (1/k) * (-log m)`. -/
theorem inv_mul_neg_log_add_log_le {d s m : ℝ} {k : ℕ}
    (hd : 0 < d) (hm : 0 < m) (hms : m ≤ s) (hk : 1 ≤ k) :
    (1 / (k : ℝ)) * (-Real.log (d ^ k * s)) + Real.log d
      ≤ -(1 / (k : ℝ)) * Real.log m := by
  have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hdk : (0 : ℝ) < d ^ k := pow_pos hd k
  have hdkne : d ^ k ≠ 0 := ne_of_gt hdk
  have hsne : s ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hms)
  have hlog : Real.log (d ^ k * s) = (k : ℝ) * Real.log d + Real.log s := by
    rw [Real.log_mul hdkne hsne, Real.log_pow]
  rw [hlog]
  have hmain : (1 / (k : ℝ)) * (-((k : ℝ) * Real.log d + Real.log s)) + Real.log d
      = (1 / (k : ℝ)) * (-Real.log s) := by
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk1
    field_simp
    ring
  rw [hmain]
  have hle : -Real.log s ≤ -Real.log m := by
    have := Real.log_le_log hm hms
    linarith
  have hnonneg : 0 ≤ 1 / (k : ℝ) := by positivity
  calc (1 / (k : ℝ)) * (-Real.log s) ≤ (1 / (k : ℝ)) * (-Real.log m) :=
        mul_le_mul_of_nonneg_left hle hnonneg
    _ = -(1 / (k : ℝ)) * Real.log m := by ring

end Work.Drive
