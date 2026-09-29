import Mathlib
import Submission.Work.TMComp.C7Aux.rtlSchedule

namespace Work.TMC7Core.Scale

theorem rtlWeightPointwise (cκ C₀ : ℝ) (Q : ℕ → ℕ) (i : ℕ) (hcκ : 0 < cκ) (hC₀ : 0 ≤ C₀)
    (hQ1 : 1 ≤ Q i)
    (hbig2 : 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) :
    9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q i : ℝ) / 2))
        + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q i : ℝ)
      ≤ (76 * C₀ + 9) * Real.exp (-(cκ * (Q i : ℝ) / 2)) := by
  set M : ℝ := (Work.TMComp.C7Aux.rtlMM cκ Q i : ℝ) with hM
  have hMge : Real.exp (cκ * (Q i : ℝ) / 2) / 10 ≤ M := by
    rw [hM]; exact Work.TMComp.C7Aux.rtlMM_ge cκ Q i hbig2
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hMge
  have hEinv : Real.exp (-(cκ * (Q i : ℝ) / 2))
      = (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ := by
    rw [Real.exp_neg]
  have hMinv : 1 / M ≤ 10 * Real.exp (-(cκ * (Q i : ℝ) / 2)) := by
    rw [hEinv, div_le_iff₀ hMpos]
    have h1 : 10 * (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ * (Real.exp (cκ * (Q i : ℝ) / 2) / 10)
        ≤ 10 * (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ * M :=
      mul_le_mul_of_nonneg_left hMge (by positivity)
    have h2 : 10 * (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ * (Real.exp (cκ * (Q i : ℝ) / 2) / 10) = 1 := by
      field_simp
    linarith [h1, h2]
  have h1 : 4 * C₀ / M ≤ 40 * C₀ * Real.exp (-(cκ * (Q i : ℝ) / 2)) := by
    have h4 : (0 : ℝ) ≤ 4 * C₀ := by linarith
    calc 4 * C₀ / M = 4 * C₀ * (1 / M) := by rw [mul_one_div]
      _ ≤ 4 * C₀ * (10 * Real.exp (-(cκ * (Q i : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hMinv h4
      _ = 40 * C₀ * Real.exp (-(cκ * (Q i : ℝ) / 2)) := by ring
  have hkey : 9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q i : ℝ) / 2))
        + 40 * C₀ * Real.exp (-(cκ * (Q i : ℝ) / 2))
      = (76 * C₀ + 9) * Real.exp (-(cκ * (Q i : ℝ) / 2)) := by ring
  linarith [h1, hkey]

end Work.TMC7Core.Scale
