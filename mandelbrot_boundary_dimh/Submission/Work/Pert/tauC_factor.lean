import Mathlib

namespace Work.Pert

/-- Algebraic rearrangement behind `τC` (Shishikura §A.1): with `σ` satisfying
`σ * u₀ = 1 - e^x`, the quantity `σ / (1 - e^{-xw})` rewrites as an explicit product
revealing the factors `(e^x - 1)/x`, `(xw)/(1 - e^{-xw})` and `1/w`. -/
theorem tauC_factor {σ u₀ x w : ℂ} (hu₀ : u₀ ≠ 0) (hx : x ≠ 0) (hw : w ≠ 0)
    (hD : 1 - Complex.exp (-(x * w)) ≠ 0) (hσu : σ * u₀ = 1 - Complex.exp x) :
    σ / (1 - Complex.exp (-(x * w)))
      = -(((Complex.exp x - 1) / x) / u₀) * ((x * w) / (1 - Complex.exp (-(x * w)))) * (1 / w) := by
  have hσ : σ = (1 - Complex.exp x) / u₀ := (eq_div_iff hu₀).mpr hσu
  rw [hσ]
  field_simp
  ring

end Work.Pert
