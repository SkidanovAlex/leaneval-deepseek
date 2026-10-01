
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

set_option linter.unusedVariables false
namespace Commons.Analysis.SpecialFunctions.Trigonometric

/-- Lower Taylor-type bound: `x - x³/3 ≤ arctan x` for `0 ≤ x`. -/
lemma arctan_lower_poly_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  let F : ℝ → ℝ := Real.arctan - (fun u : ℝ => u) + (fun u : ℝ => u ^ 3 / 3)
  have hF : ∀ t : ℝ, HasDerivAt F (1 / (1 + t ^ 2) - 1 + t ^ 2) t := by
    intro t
    change HasDerivAt ((Real.arctan - (fun u : ℝ => u)) + (fun u : ℝ => u ^ 3 / 3))
      (1 / (1 + t ^ 2) - 1 + t ^ 2) t
    have hpow : HasDerivAt (fun u : ℝ => u ^ 3 / 3) (t ^ 2) t := by
      convert! (hasDerivAt_pow 3 t).div_const (3 : ℝ) using 1
      norm_num
    exact ((Real.hasDerivAt_arctan t).sub (hasDerivAt_id' t)).add hpow
  have hnonneg : ∀ t : ℝ, 0 ≤ 1 / (1 + t ^ 2) - 1 + t ^ 2 := by
    intro t
    have hd : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    have hEq : 1 / (1 + t ^ 2) - 1 + t ^ 2 = t ^ 4 / (1 + t ^ 2) := by
      field_simp [hd]
      ring
    rw [hEq]
    positivity
  have hmonoF : Monotone F := monotone_of_hasDerivAt_nonneg hF hnonneg
  have hF0 : F 0 = 0 := by simp [F]
  have hpos : 0 ≤ F x := by
    have := hmonoF hx
    simpa [hF0] using this
  have h : 0 ≤ Real.arctan x - x + x ^ 3 / 3 := by simpa [F] using hpos
  nlinarith

/-- Upper Taylor-type bound: `arctan x ≤ x - x³/3 + x⁵/5` for `0 ≤ x`. -/
lemma arctan_upper_poly_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  let G : ℝ → ℝ := ((fun u : ℝ => u) - (fun u : ℝ => u ^ 3 / 3) +
      (fun u : ℝ => u ^ 5 / 5)) - Real.arctan
  have hId : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id'
  have hP3 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ 3 / 3) (t ^ 2) t := by
    intro t
    convert! (hasDerivAt_pow 3 t).div_const (3 : ℝ) using 1
    norm_num
  have hP5 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ 5 / 5) (t ^ 4) t := by
    intro t
    convert! (hasDerivAt_pow 5 t).div_const (5 : ℝ) using 1
    norm_num
  have hA : ∀ t : ℝ, HasDerivAt Real.arctan (1 / (1 + t ^ 2)) t := Real.hasDerivAt_arctan
  have hG : ∀ t : ℝ, HasDerivAt G (1 - t ^ 2 + t ^ 4 - 1 / (1 + t ^ 2)) t := by
    intro t
    change HasDerivAt (((fun u : ℝ => u) - (fun u : ℝ => u ^ 3 / 3) +
        (fun u : ℝ => u ^ 5 / 5)) - Real.arctan)
      (1 - t ^ 2 + t ^ 4 - 1 / (1 + t ^ 2)) t
    exact (((hId t).sub (hP3 t)).add (hP5 t)).sub (hA t)
  have hnonneg : ∀ t : ℝ, 0 ≤ 1 - t ^ 2 + t ^ 4 - 1 / (1 + t ^ 2) := by
    intro t
    have hd : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    have hEq : 1 - t ^ 2 + t ^ 4 - 1 / (1 + t ^ 2) = t ^ 6 / (1 + t ^ 2) := by
      field_simp [hd]
      ring
    rw [hEq]
    positivity
  have hmonoG : Monotone G := monotone_of_hasDerivAt_nonneg hG hnonneg
  have hG0 : G 0 = 0 := by simp [G]
  have hpos : 0 ≤ G x := by
    have := hmonoG hx
    simpa [hG0] using this
  have h : 0 ≤ x - x ^ 3 / 3 + x ^ 5 / 5 - Real.arctan x := by simpa [G] using hpos
  nlinarith

/-- Alternating-series Taylor bounds for `arctan` on the unit interval:
`x - x³/3 ≤ arctan x ≤ x - x³/3 + x⁵/5` for `0 ≤ x ≤ 1`. -/
theorem arctan_poly_bounds_on_unit (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x ^ 3 / 3 ≤ Real.arctan x ∧ Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  exact ⟨arctan_lower_poly_of_nonneg hx0, arctan_upper_poly_of_nonneg hx0⟩

end Commons.Analysis.SpecialFunctions.Trigonometric

