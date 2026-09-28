import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.NA

/-- Arithmetic assembly lemma for the Hasse-principle paper: bounding the size of the
Veronese coefficient box.  Writing `N = NN d n`, the product
`(2A/W+1)^N · W^N` is `(2A+W)^N ≤ (3A)^N = 3^N A^N` since `W ≤ A`, while
`(C / φ^{1/6})^{1/(4n)} = C^{1/(4n)} / φ^{1/(24n)}` holds exactly. -/
theorem final_arith (d n : ℕ) (C C₁ W A φ : ℝ) (hd : 2 ≤ d) (hn : 3 ≤ n)
    (hC : 0 < C) (hC₁ : 0 < C₁) (hW : 0 < W) (hWA : W ≤ A) (hA : 0 ≤ A) (hφ : 1 < φ) :
    (2 * A / W + 1) ^ (Work.HP.NN d n) *
        ((C / φ ^ ((1:ℝ)/6)) ^ (1 / (4 * (n : ℝ))) * (W ^ (Work.HP.NN d n) * Real.exp (5 * C₁)))
      ≤ (3 ^ Work.HP.NN d n * C ^ (1 / (4 * (n : ℝ))) * Real.exp (5 * C₁)) * A ^ Work.HP.NN d n
          / φ ^ (1 / (24 * (n : ℝ))) := by
  have hWpos : 0 < W := hW
  have hApos : 0 < A := lt_of_lt_of_le hWpos hWA
  have hφpos : 0 < φ := by linarith
  -- The box-growth estimate: `(2A/W+1)^N * W^N = (2A+W)^N ≤ (3A)^N = 3^N A^N`.
  have hS : (2 * A / W + 1) ^ (Work.HP.NN d n) * W ^ (Work.HP.NN d n)
      ≤ 3 ^ (Work.HP.NN d n) * A ^ (Work.HP.NN d n) := by
    have hmul : (2 * A / W + 1) * W = 2 * A + W := by field_simp
    calc (2 * A / W + 1) ^ (Work.HP.NN d n) * W ^ (Work.HP.NN d n)
        = (2 * A + W) ^ (Work.HP.NN d n) := by rw [← mul_pow, hmul]
      _ ≤ (3 * A) ^ (Work.HP.NN d n) := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 3 ^ (Work.HP.NN d n) * A ^ (Work.HP.NN d n) := by rw [mul_pow]
  -- The exponent identity: `(C/φ^{1/6})^{1/(4n)} = C^{1/(4n)}/φ^{1/(24n)}`.
  have hQ : (C / φ ^ ((1:ℝ)/6)) ^ (1 / (4 * (n : ℝ)))
      = C ^ (1 / (4 * (n : ℝ))) / φ ^ (1 / (24 * (n : ℝ))) := by
    rw [Real.div_rpow (le_of_lt hC) (le_of_lt (Real.rpow_pos_of_pos hφpos _))]
    congr 1
    rw [← Real.rpow_mul (le_of_lt hφpos) ((1:ℝ)/6) (1 / (4 * (n : ℝ)))]
    congr 1
    ring
  calc (2 * A / W + 1) ^ (Work.HP.NN d n) *
        ((C / φ ^ ((1:ℝ)/6)) ^ (1 / (4 * (n : ℝ))) * (W ^ (Work.HP.NN d n) * Real.exp (5 * C₁)))
      = Real.exp (5 * C₁) * ((C / φ ^ ((1:ℝ)/6)) ^ (1 / (4 * (n : ℝ))) *
          ((2 * A / W + 1) ^ (Work.HP.NN d n) * W ^ (Work.HP.NN d n))) := by ring
    _ ≤ Real.exp (5 * C₁) * ((C ^ (1 / (4 * (n : ℝ))) / φ ^ (1 / (24 * (n : ℝ)))) *
          (3 ^ (Work.HP.NN d n) * A ^ (Work.HP.NN d n))) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        rw [hQ]
        exact mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (3 ^ Work.HP.NN d n * C ^ (1 / (4 * (n : ℝ))) * Real.exp (5 * C₁)) * A ^ Work.HP.NN d n
          / φ ^ (1 / (24 * (n : ℝ))) := by ring

end Work.HP.NA
