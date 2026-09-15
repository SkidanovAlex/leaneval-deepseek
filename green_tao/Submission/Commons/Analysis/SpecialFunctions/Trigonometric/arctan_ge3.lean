import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace Commons.Analysis.SpecialFunctions.Trigonometric

/-- Taylor-style alternating-series lower bound for `arctan` on `[0, +∞)`:
`z - z³/3 + z⁵/5 - z⁷/7 ≤ arctan z` whenever `0 ≤ z`.

Proof: `(arctan - P)′ = 1/(1+t²) - (1 - t² + t⁴ - t⁶) = t⁸/(1+t²) ≥ 0`,
so `arctan - P` is monotone and vanishes at `0`. -/
theorem arctan_ge3 (z : ℝ) (hz : 0 ≤ z) :
    z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 ≤ Real.arctan z := by
  let F : ℝ → ℝ := Real.arctan - (fun u : ℝ => u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7)
  have hId : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id'
  have hP3 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ 3 / 3) (t ^ 2) t := by
    intro t
    convert! (hasDerivAt_pow 3 t).div_const (3 : ℝ) using 1
    norm_num
  have hP5 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ 5 / 5) (t ^ 4) t := by
    intro t
    convert! (hasDerivAt_pow 5 t).div_const (5 : ℝ) using 1
    norm_num
  have hP7 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ 7 / 7) (t ^ 6) t := by
    intro t
    convert! (hasDerivAt_pow 7 t).div_const (7 : ℝ) using 1
    norm_num
  have hP : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7)
      (1 - t ^ 2 + t ^ 4 - t ^ 6) t := by
    intro t
    change HasDerivAt (((fun u : ℝ => u) - (fun u : ℝ => u ^ 3 / 3) +
        (fun u : ℝ => u ^ 5 / 5)) - (fun u : ℝ => u ^ 7 / 7))
      (1 - t ^ 2 + t ^ 4 - t ^ 6) t
    exact ((((hId t).sub (hP3 t)).add (hP5 t)).sub (hP7 t))
  have hF : ∀ t : ℝ, HasDerivAt F (1 / (1 + t ^ 2) - (1 - t ^ 2 + t ^ 4 - t ^ 6)) t := by
    intro t
    change HasDerivAt (Real.arctan - (fun u : ℝ => u - u ^ 3 / 3 + u ^ 5 / 5 - u ^ 7 / 7))
      (1 / (1 + t ^ 2) - (1 - t ^ 2 + t ^ 4 - t ^ 6)) t
    exact (Real.hasDerivAt_arctan t).sub (hP t)
  have hnonneg : ∀ t : ℝ, 0 ≤ 1 / (1 + t ^ 2) - (1 - t ^ 2 + t ^ 4 - t ^ 6) := by
    intro t
    have hd : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    have hEq : 1 / (1 + t ^ 2) - (1 - t ^ 2 + t ^ 4 - t ^ 6) = t ^ 8 / (1 + t ^ 2) := by
      field_simp [hd]
      ring
    rw [hEq]
    positivity
  have hmonoF : Monotone F := monotone_of_hasDerivAt_nonneg hF hnonneg
  have hF0 : F 0 = 0 := by simp [F]
  have hpos : 0 ≤ F z := by
    have := hmonoF hz
    simpa [hF0] using this
  have h : 0 ≤ Real.arctan z - (z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7) := by simpa [F] using hpos
  nlinarith

end Commons.Analysis.SpecialFunctions.Trigonometric
