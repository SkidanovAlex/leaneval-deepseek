import Mathlib

namespace Work.WilE3.Taylor.CaseII

theorem aux_coeff_eq_zero_of_minor_ne_zero {k : ℕ} {g w : Fin k → ℝ}
    {c d : ℝ} (h : ∀ l : Fin k, c * g l + d * w l = 0)
    (hminor : ∃ i j : Fin k, g i * w j - g j * w i ≠ 0) : c = 0 ∧ d = 0 := by
  obtain ⟨i, j, hij⟩ := hminor
  have hi := h i
  have hj := h j
  -- Multiply the relation at `i` and at `j` by the other coordinate.
  have hcgi : c * g i = -(d * w i) := by linarith
  have hcgj : c * g j = -(d * w j) := by linarith
  have hdwi : d * w i = -(c * g i) := by linarith
  have hdwj : d * w j = -(c * g j) := by linarith
  -- The minor vanishes when multiplied by `c`, respectively by `d`.
  have hc : c * (g i * w j - g j * w i) = 0 := by
    calc c * (g i * w j - g j * w i)
        = (c * g i) * w j - (c * g j) * w i := by ring
      _ = (-(d * w i)) * w j - (-(d * w j)) * w i := by rw [hcgi, hcgj]
      _ = 0 := by ring
  have hd : d * (g i * w j - g j * w i) = 0 := by
    calc d * (g i * w j - g j * w i)
        = g i * (d * w j) - g j * (d * w i) := by ring
      _ = g i * (-(c * g j)) - g j * (-(c * g i)) := by rw [hdwj, hdwi]
      _ = 0 := by ring
  exact ⟨(mul_eq_zero.mp hc).resolve_right hij, (mul_eq_zero.mp hd).resolve_right hij⟩

end Work.WilE3.Taylor.CaseII
