import Mathlib

namespace Work.A3

/-- For `d ≥ 1`, `β ≥ 0` and `s : ℕ`:
`(β ^ (-(1/d))) ^ (2*s) = β ^ (-((2*s)/d))`.
This is `Real.rpow_mul_natCast` together with the arithmetic identity
`(-(1/d)) * (2*s) = -((2*s)/d)`. -/
theorem rpow_pow_of_neg_inv (d s : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    (β ^ (-(1:ℝ)/(d:ℝ))) ^ (2*s) = β ^ (-((2*s:ℝ)/(d:ℝ))) := by
  have hexp : (-(1:ℝ)/(d:ℝ)) * ((2*s:ℕ):ℝ) = -((2*s:ℝ)/(d:ℝ)) := by
    have hd0 : (d:ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [← Real.rpow_mul_natCast hβ (-(1:ℝ)/(d:ℝ)) (2*s), hexp]

end Work.A3
