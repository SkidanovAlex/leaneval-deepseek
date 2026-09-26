import Mathlib
import Submission.Work.CKFinal.rpow_exp_neg_bound

namespace Work.CKFinal

/-- Elementary rearrangement: for `0 ≤ B` and `0 < y`,
`y * (B / y) ^ t = B ^ t * y ^ (1 - t)`. -/
private lemma mul_div_rpow (B y t : ℝ) (hB : 0 ≤ B) (hy : 0 < y) :
    y * (B / y) ^ t = B ^ t * y ^ (1 - t) := by
  have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
  have h1 : (B / y) ^ t = B ^ t * y ^ (-t) := by
    rw [Real.div_rpow hB hy0, div_eq_mul_inv, ← Real.rpow_neg hy0 t]
  rw [h1, show y * (B ^ t * y ^ (-t)) = B ^ t * (y * y ^ (-t)) by ring]
  congr 1
  calc y * y ^ (-t) = y ^ (1 : ℝ) * y ^ (-t) := by rw [Real.rpow_one]
    _ = y ^ ((1 : ℝ) + -t) := (Real.rpow_add hy 1 (-t)).symm
    _ = y ^ (1 - t) := by rw [show (1 : ℝ) + -t = 1 - t by ring]

/-- Tail strip bound: for `y ≥ 2`, `C ≥ 0`, `β ≥ 0`,
`C (2 + y) e^{-2π y} ≤ 2C ((β+1)/(2π e))^{β+1} y^{-β}`.

The content is the global maximum principle for `u ↦ u^t e^{-u}`
(`rpow_exp_neg_bound`) combined with `2 + y ≤ 2y`. -/
theorem tail_strip_bound (C β : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β) :
    ∀ y : ℝ, 2 ≤ y →
      C * (2 + y) * Real.exp (-(2 * Real.pi * y)) ≤
        (2 * C * ((β + 1) / (2 * Real.pi * Real.exp 1)) ^ (β + 1)) * y ^ (-β) := by
  intro y hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hu : (0 : ℝ) ≤ 2 * Real.pi * y := by positivity
  have hupos : (0 : ℝ) < 2 * Real.pi * y := by positivity
  have ht0 : (0 : ℝ) ≤ β + 1 := by linarith
  have h1 := rpow_exp_neg_bound (β + 1) (2 * Real.pi * y) ht0 hu
  have h2 : Real.exp (-(2 * Real.pi * y)) ≤
      ((β + 1) / Real.exp 1) ^ (β + 1) / (2 * Real.pi * y) ^ (β + 1) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hupos (β + 1)), mul_comm]
    exact h1
  have h3 : ((β + 1) / Real.exp 1) ^ (β + 1) / (2 * Real.pi * y) ^ (β + 1) =
      (((β + 1) / (2 * Real.pi * Real.exp 1)) / y) ^ (β + 1) := by
    rw [← Real.div_rpow (by positivity : (0 : ℝ) ≤ (β + 1) / Real.exp 1) hu]
    congr 1
    rw [div_div, div_div]
    congr 1
    ring
  have hRnn : (0 : ℝ) ≤ (((β + 1) / (2 * Real.pi * Real.exp 1)) / y) ^ (β + 1) :=
    Real.rpow_nonneg (by positivity) _
  have h2y : 2 + y ≤ 2 * y := by linarith
  have hhelp : y * (((β + 1) / (2 * Real.pi * Real.exp 1)) / y) ^ (β + 1)
      = ((β + 1) / (2 * Real.pi * Real.exp 1)) ^ (β + 1) * y ^ (-β) := by
    have := mul_div_rpow ((β + 1) / (2 * Real.pi * Real.exp 1)) y (β + 1) (by positivity) hy0
    rwa [show 1 - (β + 1) = -β by ring] at this
  have hkey : (2 + y) * Real.exp (-(2 * Real.pi * y)) ≤
      2 * ((β + 1) / (2 * Real.pi * Real.exp 1)) ^ (β + 1) * y ^ (-β) := by
    calc (2 + y) * Real.exp (-(2 * Real.pi * y))
        ≤ (2 + y) * (((β + 1) / (2 * Real.pi * Real.exp 1)) / y) ^ (β + 1) :=
          mul_le_mul_of_nonneg_left (by rw [← h3]; exact h2) (by linarith)
      _ ≤ (2 * y) * (((β + 1) / (2 * Real.pi * Real.exp 1)) / y) ^ (β + 1) :=
          mul_le_mul_of_nonneg_right h2y hRnn
      _ = 2 * ((β + 1) / (2 * Real.pi * Real.exp 1)) ^ (β + 1) * y ^ (-β) := by
          rw [mul_assoc, hhelp]; ring
  calc C * (2 + y) * Real.exp (-(2 * Real.pi * y))
      = C * ((2 + y) * Real.exp (-(2 * Real.pi * y))) := by ring
    _ ≤ C * (2 * ((β + 1) / (2 * Real.pi * Real.exp 1)) ^ (β + 1) * y ^ (-β)) :=
        mul_le_mul_of_nonneg_left hkey hC
    _ = (2 * C * ((β + 1) / (2 * Real.pi * Real.exp 1)) ^ (β + 1)) * y ^ (-β) := by ring

end Work.CKFinal
