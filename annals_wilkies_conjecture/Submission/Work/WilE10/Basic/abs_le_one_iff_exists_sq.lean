import Mathlib
import Submission.Work.WilE10.Psi

namespace Work.WilE10.Basic

/-- A real number lies in `[-1,1]` iff `1 - w ^ 2` is a square. -/
theorem abs_le_one_iff_exists_sq {w : ℝ} : |w| ≤ 1 ↔ ∃ v : ℝ, 1 - w ^ 2 = v ^ 2 := by
  constructor
  · intro h
    have hw : w ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one w).mpr h
    exact ⟨Real.sqrt (1 - w ^ 2), (Real.sq_sqrt (by linarith)).symm⟩
  · rintro ⟨v, hv⟩
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [sq_nonneg v]

end Work.WilE10.Basic
