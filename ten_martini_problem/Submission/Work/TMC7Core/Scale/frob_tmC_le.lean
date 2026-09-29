import Mathlib
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Scale

/-- The norm of a real number seen as a complex number. -/
lemma norm_ofReal_cast (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

/-- `frob (tmC lam E y) ≤ sqrt ((‖E‖ + 2|lam|)^2 + 2)`.

The transfer matrix is `!![E - v, -1; 1, 0]` with `v = 2λ cos(2πy)`, so
`frob² = ‖E - v‖² + 1 + 1 ≤ (‖E‖ + 2|λ|)² + 2`, since `‖E - v‖ ≤ ‖E‖ + ‖v‖`
and `‖v‖ = |2λ cos(2πy)| ≤ 2|λ|`. -/
theorem frob_tmC_le (lam : ℝ) (E : ℂ) (y : ℝ) :
    Work.TMC7Core.frob (Work.TMC7Core.tmC lam E y) ≤ Real.sqrt ((‖E‖ + 2 * |lam|) ^ 2 + 2) := by
  set a : ℂ := E - ((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ) with ha
  have hsq : Work.TMC7Core.frob (Work.TMC7Core.tmC lam E y) ^ 2 = ‖a‖ ^ 2 + 2 := by
    rw [Work.TMC7Core.frob_sq]
    simp [Work.TMC7Core.tmC, ha]
    ring
  have hb : ‖a‖ ≤ ‖E‖ + 2 * |lam| := by
    have h1 : ‖a‖ ≤ ‖E‖ + ‖((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ)‖ := by
      rw [ha]; exact norm_sub_le _ _
    have h2 : ‖((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ)‖ ≤ 2 * |lam| := by
      have hc : |Real.cos (2 * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
      rw [norm_ofReal_cast, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg lam, hc]
    linarith
  have hb0 : 0 ≤ ‖E‖ + 2 * |lam| := by positivity
  calc Work.TMC7Core.frob (Work.TMC7Core.tmC lam E y)
      = Real.sqrt (Work.TMC7Core.frob (Work.TMC7Core.tmC lam E y) ^ 2) :=
        (Real.sqrt_sq (Work.TMC7Core.frob_nonneg _)).symm
    _ ≤ Real.sqrt ((‖E‖ + 2 * |lam|) ^ 2 + 2) := by
        apply Real.sqrt_le_sqrt
        rw [hsq]
        nlinarith [pow_le_pow_left₀ (norm_nonneg a) hb 2]

end Work.TMC7Core.Scale
