import Mathlib

namespace Work.Mostow

theorem LogRatioArcosh (A B c : ℝ) (hA : 0 < A) (hB : 0 < B) (hc : 1 ≤ c)
    (hQ : A ^ 2 + B ^ 2 - 2 * c * A * B ≤ 0) :
    |Real.log A - Real.log B| ≤ Real.arcosh c := by
  have hABpos : 0 < 2 * A * B := by positivity
  -- cosh of the log-ratio in terms of A and B
  have hcosh : 2 * A * B * Real.cosh (Real.log A - Real.log B) = A ^ 2 + B ^ 2 := by
    have h1 : Real.exp (Real.log A - Real.log B) = A / B := by
      rw [Real.exp_sub, Real.exp_log hA, Real.exp_log hB]
    have h2 : Real.exp (-(Real.log A - Real.log B)) = B / A := by
      rw [show -(Real.log A - Real.log B) = Real.log B - Real.log A by ring, Real.exp_sub,
        Real.exp_log hB, Real.exp_log hA]
    rw [Real.cosh_eq, h1, h2]
    field_simp
  -- hence cosh of the log-ratio is at most c
  have hle : Real.cosh (Real.log A - Real.log B) ≤ c := by
    have h3 : 2 * A * B * Real.cosh (Real.log A - Real.log B) ≤ 2 * A * B * c := by
      nlinarith [hcosh, hQ]
    exact le_of_mul_le_mul_left h3 hABpos
  have habs : Real.cosh |Real.log A - Real.log B| ≤ c := by
    simpa [Real.cosh_abs] using hle
  have hcpos : 0 < c := by linarith
  have h4 : Real.arcosh (Real.cosh |Real.log A - Real.log B|) ≤ Real.arcosh c :=
    (Real.arcosh_le_arcosh (Real.cosh_pos _) hcpos).2 habs
  rwa [Real.arcosh_cosh (abs_nonneg _)] at h4

end Work.Mostow
