import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Tail bound for a polynomially weighted exponential.  For `T ≥ 0`, `H ≥ 1` and any `f ≥ 0` on
`Ioi H` with `f v ≤ c₀ (3+T+v)^4 (1+v)^6 exp(-(π/2)v)`,
`∫_{v>H} f ≤ c₀ e^{-(π/2)H} (3+T+H)^4 (1+H)^6 ∫_{s>0} (1+s)^10 e^{-(π/2)s}`.
Substitute `v = H + s` on `Ioi 0` (the map `s ↦ H+s` sends `Ioi 0` onto `Ioi H`; use
`integral_image_eq_integral_abs_deriv_smul`), bound `(3+T+H+s) ≤ (3+T+H)(1+s)` and
`(1+H+s) ≤ (1+H)(1+s)`, and use `MeasureTheory.integral_mono_of_nonneg` with the dominating
function (integrable because `(1+s)^10 e^{-(π/2)s}` is). -/
theorem integral_Ioi_polyexp_le (T H c₀ : ℝ) (hT : 0 ≤ T) (hH : 1 ≤ H) (hc₀ : 0 ≤ c₀)
    (f : ℝ → ℝ)
    (hf0 : ∀ v ∈ Set.Ioi H, 0 ≤ f v)
    (hfe : ∀ v ∈ Set.Ioi H,
      f v ≤ c₀ * ((3 + T + v) ^ 4 * (1 + v) ^ 6 * Real.exp (-(Real.pi / 2) * v))) :
    (∫ v in Set.Ioi H, f v) ≤
      c₀ * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * (1 + H) ^ 6
        * (∫ s in Set.Ioi 0, (1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))) := by
  sorry

end Work.ZeroDensity.Ingham
