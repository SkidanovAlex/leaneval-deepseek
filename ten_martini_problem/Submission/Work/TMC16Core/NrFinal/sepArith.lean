import Mathlib

namespace Work.TMC16Core.NrFinal

/-- Arithmetic for the `σ ≥ L` case: `4L ≤ qn` and `M ≤ (123/160)/qn`. -/
theorem arithA2 {qn L M : ℝ} (hqn : 0 < qn) (hL : 0 ≤ L) (h4L : 4 * L ≤ qn)
    (hM : M ≤ (123 / 160) / qn) :
    1 / (32 * qn) ≤ 1 / (qn + L) - M := by
  have hqL : 0 < qn + L := by linarith
  have h5 : 0 < 5 * qn := by linarith
  have h1 : 4 / (5 * qn) ≤ 1 / (qn + L) := by
    rw [div_le_div_iff₀ h5 hqL]; linarith
  have h3 : 4 / (5 * qn) - (123 / 160) / qn = 1 / (32 * qn) := by
    field_simp; ring
  linarith [h1, h3]

/-- Arithmetic for the `σ < L` case: `0 < L`, `4L ≤ qn` and `M ≤ 1/qn`. -/
theorem arithB2 {qn L M : ℝ} (hqn : 0 < qn) (hL : 0 < L) (h4L : 4 * L ≤ qn)
    (hM : M ≤ 1 / qn) :
    1 / (32 * qn) ≤ 1 / (2 * L) - M := by
  have h2L : 0 < 2 * L := by linarith
  have h1 : 2 / qn ≤ 1 / (2 * L) := by
    rw [div_le_div_iff₀ hqn h2L]; linarith
  have h4 : 1 / (32 * qn) ≤ 1 / qn :=
    one_div_le_one_div_of_le hqn (by linarith)
  have h3 : 2 / qn - 1 / qn = 1 / qn := by ring
  linarith [h1, h3, h4]

end Work.TMC16Core.NrFinal
