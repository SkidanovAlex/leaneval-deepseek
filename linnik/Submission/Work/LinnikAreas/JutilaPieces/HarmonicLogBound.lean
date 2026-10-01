import Mathlib

namespace Work.LinnikAreas.JutilaPieces

/-- The partial harmonic sum `∑_{m=1}^n 1/m` is at most `1 + log n`.
This follows from Mathlib's bound `harmonic n ≤ 1 + Real.log n`
(`Mathlib/NumberTheory/Harmonic/Bounds.lean`), transported from `ℚ` to `ℝ`. -/
theorem HarmonicLogBound (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

end Work.LinnikAreas.JutilaPieces
