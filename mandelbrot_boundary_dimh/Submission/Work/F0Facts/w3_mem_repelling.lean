import Mathlib
import Submission.Work.F0Facts.FinvRegion
import Submission.Work.F0Facts.Basic

namespace Work.F0Facts

open Filter Topology Set Metric
open scoped Topology

noncomputable section

/-!
# `w3` lies in the repelling region

`w3 = (-1 + √3 i)/2` is a primitive cube root of unity, with `f₀ w3 = -1`.  The repelling
region is `repelling = {w | 2 ≤ ‖1 + 4w‖ + re (1 + 4w)}`.  For `w3` we have
`1 + 4 w3 = -1 + 2√3 i`, whose real part is `-1` and whose modulus is `√13 ≥ 3`; hence
`‖1 + 4 w3‖ + re (1 + 4 w3) = √13 - 1 ≥ 2`.
-/

/-- The value `1 + 4 * w3` in rectangular coordinates. -/
lemma one_add_four_w3 : (1 : ℂ) + 4 * w3 = -1 + (2 * Real.sqrt 3 : ℂ) * Complex.I := by
  rw [w3]; ring

lemma one_add_four_w3_re : (1 + 4 * w3).re = -1 := by
  rw [one_add_four_w3]; simp

lemma one_add_four_w3_im : (1 + 4 * w3).im = 2 * Real.sqrt 3 := by
  rw [one_add_four_w3]; simp

lemma norm_one_add_four_w3 : ‖(1 : ℂ) + 4 * w3‖ = Real.sqrt 13 := by
  have hnormSq : Complex.normSq (1 + 4 * w3) = 13 := by
    rw [Complex.normSq_apply, one_add_four_w3_re, one_add_four_w3_im]
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hsq : ‖(1 : ℂ) + 4 * w3‖ ^ 2 = 13 := by
    rw [Complex.sq_norm, hnormSq]
  rw [show ‖(1 : ℂ) + 4 * w3‖ = Real.sqrt (‖(1 : ℂ) + 4 * w3‖ ^ 2) by
        rw [Real.sqrt_sq (norm_nonneg _)], hsq]

theorem w3_mem_repelling : w3 ∈ repelling := by
  have hnorm : (3 : ℝ) ≤ ‖(1 : ℂ) + 4 * w3‖ := by
    rw [norm_one_add_four_w3]
    exact (Real.le_sqrt' (show (0 : ℝ) < 3 by norm_num)).mpr (by norm_num)
  show 2 ≤ ‖(1 : ℂ) + 4 * w3‖ + (1 + 4 * w3).re
  rw [one_add_four_w3_re]
  linarith

end

end Work.F0Facts
