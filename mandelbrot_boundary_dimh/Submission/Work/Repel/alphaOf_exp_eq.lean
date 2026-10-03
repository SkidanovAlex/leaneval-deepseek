import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Repel

/-- Since `alphaOf a₁ a₂ β = 1 / ((a₁ : ℂ) - 1 / ((a₂ : ℂ) + β))`, we have
`1 / alphaOf a₁ a₂ β = (a₁ : ℂ) - 1 / ((a₂ : ℂ) + β)` whenever
`(a₁ : ℂ) - 1 / ((a₂ : ℂ) + β) ≠ 0`; in the degenerate case where that quantity vanishes
both sides of the exponential identity below collapse to `1`. -/
theorem alphaOf_exp_eq (a₁ a₂ : ℕ) (β : ℂ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (1 / MandelDim.alphaOf a₁ a₂ β))) =
      Complex.exp (2 * Real.pi * Complex.I * (1 / ((a₂ : ℂ) + β))) := by
  have hD : MandelDim.alphaOf a₁ a₂ β = 1 / ((a₁ : ℂ) - 1 / ((a₂ : ℂ) + β)) := rfl
  have hgoal : Complex.exp (2 * Real.pi * Complex.I * (a₁ : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * (a₁ : ℂ)
        = ((a₁ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_eq_one_iff]
    exact ⟨(a₁ : ℤ), rfl⟩
  by_cases h : (a₁ : ℂ) - 1 / ((a₂ : ℂ) + β) = 0
  · -- degenerate case: `1 / alphaOf = 0` and `1 / (a₂ + β) = a₁`
    have ha : 1 / ((a₂ : ℂ) + β) = (a₁ : ℂ) := (sub_eq_zero.mp h).symm
    have h1 : 1 / MandelDim.alphaOf a₁ a₂ β = 0 := by rw [hD, h]; simp
    rw [h1, ha, mul_zero, neg_zero, Complex.exp_zero, hgoal]
  · -- generic case: `1 / alphaOf = a₁ - 1 / (a₂ + β)`
    have h1 : 1 / MandelDim.alphaOf a₁ a₂ β = (a₁ : ℂ) - 1 / ((a₂ : ℂ) + β) := by
      rw [hD]
      simp only [one_div, inv_inv]
    rw [h1]
    have hkey : -(2 * Real.pi * Complex.I * ((a₁ : ℂ) - 1 / ((a₂ : ℂ) + β))) =
        2 * Real.pi * Complex.I * (1 / ((a₂ : ℂ) + β))
          + -(2 * Real.pi * Complex.I * (a₁ : ℂ)) := by
      ring
    rw [hkey, Complex.exp_add]
    have hg2 : Complex.exp (-(2 * Real.pi * Complex.I * (a₁ : ℂ))) = 1 := by
      rw [show -(2 * Real.pi * Complex.I * (a₁ : ℂ))
          = ((-(a₁ : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      rw [Complex.exp_eq_one_iff]
      exact ⟨-(a₁ : ℤ), rfl⟩
    rw [hg2, mul_one]

end Work.Repel
