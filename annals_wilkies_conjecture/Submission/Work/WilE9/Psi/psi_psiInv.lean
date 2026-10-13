import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Psi

/-- `psi ∘ psiInv = id` on `(-1,1)`. -/
theorem psi_psiInv (y : ℝ) (hy : |y| < 1) :
    WilkiesDesign.E.psi (Work.WilE9.psiInv y) = y := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y, hy]
  have h2 : Real.sqrt (1 + Work.WilE9.psiInv y ^ 2) = 1 / Real.sqrt (1 - y ^ 2) := by
    have hsq : 1 + Work.WilE9.psiInv y ^ 2 = 1 / (1 - y ^ 2) := by
      rw [Work.WilE9.psiInv, div_pow, Real.sq_sqrt (le_of_lt h1)]
      field_simp
      ring
    rw [hsq, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (1 - y ^ 2), Real.sqrt_one, one_div]
  have hs : Real.sqrt (1 - y ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
  rw [WilkiesDesign.E.psi, h2, Work.WilE9.psiInv]
  field_simp

end Work.WilE9.Psi
