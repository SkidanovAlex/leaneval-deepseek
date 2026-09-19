import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.arctan_ge3

namespace Commons.Analysis.SpecialFunctions.Trigonometric

/-- Upper Taylor-type bound for `arctan` with alternating series through degree 9:
`arctan z ≤ z - z³/3 + z⁵/5 - z⁷/7 + z⁹/9` for every `0 ≤ z`. -/
theorem arctan_le4 (z : ℝ) (hz : 0 ≤ z) :
    Real.arctan z ≤ z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9 := by
  let G : ℝ → ℝ := ((fun u : ℝ => u) - (fun u : ℝ => u ^ 3 / 3) +
      (fun u : ℝ => u ^ 5 / 5)) - (fun u : ℝ => u ^ 7 / 7) +
      (fun u : ℝ => u ^ 9 / 9) - Real.arctan
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
  have hP9 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ 9 / 9) (t ^ 8) t := by
    intro t
    convert! (hasDerivAt_pow 9 t).div_const (9 : ℝ) using 1
    norm_num
  have hA : ∀ t : ℝ, HasDerivAt Real.arctan (1 / (1 + t ^ 2)) t := Real.hasDerivAt_arctan
  have hG : ∀ t : ℝ, HasDerivAt G (1 - t ^ 2 + t ^ 4 - t ^ 6 + t ^ 8 - 1 / (1 + t ^ 2)) t := by
    intro t
    change HasDerivAt (((((fun u : ℝ => u) - (fun u : ℝ => u ^ 3 / 3) +
        (fun u : ℝ => u ^ 5 / 5)) - (fun u : ℝ => u ^ 7 / 7)) +
        (fun u : ℝ => u ^ 9 / 9)) - Real.arctan)
      (1 - t ^ 2 + t ^ 4 - t ^ 6 + t ^ 8 - 1 / (1 + t ^ 2)) t
    exact (((((hId t).sub (hP3 t)).add (hP5 t)).sub (hP7 t)).add (hP9 t)).sub (hA t)
  have hnonneg : ∀ t : ℝ, 0 ≤ 1 - t ^ 2 + t ^ 4 - t ^ 6 + t ^ 8 - 1 / (1 + t ^ 2) := by
    intro t
    have hd : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    have hEq : 1 - t ^ 2 + t ^ 4 - t ^ 6 + t ^ 8 - 1 / (1 + t ^ 2) = t ^ 10 / (1 + t ^ 2) := by
      field_simp [hd]
      ring
    rw [hEq]
    positivity
  have hmonoG : Monotone G := monotone_of_hasDerivAt_nonneg hG hnonneg
  have hG0 : G 0 = 0 := by simp [G]
  have hpos : 0 ≤ G z := by
    have := hmonoG hz
    simpa [hG0] using this
  have h : 0 ≤ z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9 - Real.arctan z := by
    simpa [G] using hpos
  linarith

end Commons.Analysis.SpecialFunctions.Trigonometric
