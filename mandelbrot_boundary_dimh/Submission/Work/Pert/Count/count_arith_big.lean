import Mathlib

namespace Work.Pert.Count

theorem count_arith_big {a s : ℝ} {n : ℕ} (ha : 0 < a) (hs : a ≤ s) (hs2 : 1 ≤ 2 * s) :
    ((n : ℝ) + 1) ≤ 30 * (s / a) * (1 + (n : ℝ) * a) := by
  have hsa : (1 : ℝ) ≤ s / a := by
    rw [one_le_div ha]
    exact hs
  have hs_half : (1 : ℝ) / 2 ≤ s := by linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hterm : 30 * (s / a) * (1 + (n : ℝ) * a) = 30 * (s / a) + 30 * s * (n : ℝ) := by
    have h1 : (s / a) * ((n : ℝ) * a) = (n : ℝ) * s := by
      field_simp
    calc 30 * (s / a) * (1 + (n : ℝ) * a)
        = 30 * (s / a) + 30 * ((s / a) * ((n : ℝ) * a)) := by ring
      _ = 30 * (s / a) + 30 * ((n : ℝ) * s) := by rw [h1]
      _ = 30 * (s / a) + 30 * s * (n : ℝ) := by ring
  rw [hterm]
  have h2 : 15 * (n : ℝ) ≤ 30 * s * (n : ℝ) := by nlinarith
  nlinarith [hsa, h2, hn]

end Work.Pert.Count
