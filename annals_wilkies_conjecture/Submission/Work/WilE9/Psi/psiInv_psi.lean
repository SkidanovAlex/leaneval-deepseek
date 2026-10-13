import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Psi

/-- `psiInv ∘ psi = id` on all of `ℝ`. -/
theorem psiInv_psi (x : ℝ) :
    Work.WilE9.psiInv (WilkiesDesign.E.psi x) = x := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h2 : 1 - (WilkiesDesign.E.psi x) ^ 2 = 1 / (1 + x ^ 2) := by
    rw [WilkiesDesign.E.psi, div_pow, Real.sq_sqrt (le_of_lt h1)]
    field_simp
    ring
  rw [Work.WilE9.psiInv, h2, WilkiesDesign.E.psi]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (1 + x ^ 2), Real.sqrt_one, one_div]
  have hs : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
  field_simp

end Work.WilE9.Psi
