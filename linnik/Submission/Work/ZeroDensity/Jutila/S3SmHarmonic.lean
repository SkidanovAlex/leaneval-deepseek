import Mathlib

namespace Work.ZeroDensity.Jutila

theorem S3SmHarmonic (X : ℕ) (hX : 1 ≤ X) :
    ∑ m ∈ Finset.Icc 1 X, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log (X : ℝ) := by
  have h : (harmonic X : ℝ) ≤ 1 + Real.log (X : ℝ) := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

end Work.ZeroDensity.Jutila
