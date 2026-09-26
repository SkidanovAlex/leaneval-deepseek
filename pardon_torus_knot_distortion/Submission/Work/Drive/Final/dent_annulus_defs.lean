import Mathlib

/-!
# `det2`: the transverse-intersection determinant of two linear forms on the parameter plane

The margin analysis of L4b (`AUDIT_pardon_unconditional.md` §31.6, `NOTES_LEAD_L4b.md` §1 C) measures
how far a pair of differentials (of the sweep height and of a face functional, or of the sweep height
and of the box norm) is from being *proportional*, by the determinant of their `2 × 2` matrix in the
basis `(1, 0), (0, 1)` of the parameter plane.
-/

namespace Work.Drive.Final

/-- The determinant of the pair of linear forms `L, D` on `ℝ × ℝ`, in the basis `(1, 0), (0, 1)`. -/
def det2 (L D : (ℝ × ℝ) →L[ℝ] ℝ) : ℝ :=
  L (1, 0) * D (0, 1) - L (0, 1) * D (1, 0)

theorem det2_sub_eq (L L' D : (ℝ × ℝ) →L[ℝ] ℝ) :
    det2 L' D - det2 L D =
      (L' - L) (1, 0) * D (0, 1) - (L' - L) (0, 1) * D (1, 0) := by
  simp only [det2, ContinuousLinearMap.sub_apply]
  ring

/-- **The determinant is Lipschitz in its first argument**: replacing `L` by `L'` moves it by at most
`2 ‖L' − L‖ ‖D‖`. -/
theorem det2_sub_le (L L' D : (ℝ × ℝ) →L[ℝ] ℝ) :
    |det2 L' D - det2 L D| ≤ 2 * ‖L' - L‖ * ‖D‖ := by
  have h1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have h2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have ha : |(L' - L) (1, 0)| ≤ ‖L' - L‖ := by
    have := (L' - L).le_opNorm ((1 : ℝ), (0 : ℝ))
    simpa [h1] using this
  have hb : |D (0, 1)| ≤ ‖D‖ := by
    have := D.le_opNorm ((0 : ℝ), (1 : ℝ))
    simpa [h2] using this
  have hc : |(L' - L) (0, 1)| ≤ ‖L' - L‖ := by
    have := (L' - L).le_opNorm ((0 : ℝ), (1 : ℝ))
    simpa [h2] using this
  have hd : |D (1, 0)| ≤ ‖D‖ := by
    have := D.le_opNorm ((1 : ℝ), (0 : ℝ))
    simpa [h1] using this
  rw [det2_sub_eq]
  have hn : (0 : ℝ) ≤ ‖L' - L‖ := norm_nonneg _
  have hD : (0 : ℝ) ≤ ‖D‖ := norm_nonneg _
  calc |(L' - L) (1, 0) * D (0, 1) - (L' - L) (0, 1) * D (1, 0)|
      ≤ |(L' - L) (1, 0) * D (0, 1)| + |(L' - L) (0, 1) * D (1, 0)| := abs_sub _ _
    _ = |(L' - L) (1, 0)| * |D (0, 1)| + |(L' - L) (0, 1)| * |D (1, 0)| := by
        rw [abs_mul, abs_mul]
    _ ≤ ‖L' - L‖ * ‖D‖ + ‖L' - L‖ * ‖D‖ := by
        exact add_le_add (mul_le_mul ha hb (abs_nonneg _) hn) (mul_le_mul hc hd (abs_nonneg _) hn)
    _ = 2 * ‖L' - L‖ * ‖D‖ := by ring

end Work.Drive.Final
