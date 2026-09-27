import Mathlib
import Submission.Work.Drive.linearPlaneChart

namespace Work.Drive

/-- The straight line between two vectors avoids the origin on the open unit interval exactly when the two are not negatively proportional. -/
theorem interp_ne_zero_iff {A B : Eucl 3} :
    (∀ s : ℝ, 0 < s → s < 1 → (1 - s) • A + s • B ≠ 0) ↔
      ¬ ∃ c : ℝ, c < 0 ∧ B = c • A := by
  constructor
  · -- A negative proportionality makes the point at `s = 1/(1-c)` hit the origin.
    intro h ⟨c, hc, hBA⟩
    have h1c : (0 : ℝ) < 1 - c := by linarith
    have hsp : 0 < 1 / (1 - c) := by positivity
    have hsl : 1 / (1 - c) < 1 := by
      rw [div_lt_one h1c]; linarith
    refine h (1 / (1 - c)) hsp hsl ?_
    rw [hBA, smul_smul, ← add_smul]
    have hthis : (1 - 1 / (1 - c)) + 1 / (1 - c) * c = (0 : ℝ) := by
      field_simp
      ring
    rw [hthis, zero_smul]
  · -- Conversely a zero on the open segment exhibits a negative proportionality.
    rintro h s hs hlt hzero
    have h1s : (0 : ℝ) < 1 - s := by linarith
    have hsne : s ≠ 0 := ne_of_gt hs
    refine h ⟨-(1 - s) / s, ?_, ?_⟩
    · rw [neg_div]
      exact neg_lt_zero.mpr (div_pos h1s hs)
    · have h1 : s • B = -((1 - s) • A) := eq_neg_of_add_eq_zero_right hzero
      calc B = s⁻¹ • (s • B) := by rw [smul_smul, inv_mul_cancel₀ hsne, one_smul]
        _ = s⁻¹ • (-((1 - s) • A)) := by rw [h1]
        _ = (-(1 - s) / s) • A := by
              rw [smul_neg, smul_smul, ← neg_smul]
              congr 1
              ring

end Work.Drive
