import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Numeric tail estimate.  For every `C₀ > 0` there is `A₀ ≥ 6` such that for all `A ≥ A₀` and
`T ≥ 2`, with `H = A log(A T)`,
`C₀ √T (3+T+H)^4 (1+H)^6 e^{-(π/2)H} ≤ π/10`.
Indeed `T ≤ e^{H/A}`, so `√T ≤ e^{H/200}` and (via `3+T ≤ (5/2)T`) `√T (3+T)^4 ≤ (5/2)^4 e^{H/25}`
for `A ≥ 100`, while `3+T+H ≤ (3+T)(1+H)` and `(1+H)^{10} ≤ e^{H/4}` for `H ≥ 500`; hence the left
side is at most `C₀ (5/2)^4 e^{-(π/2-0.295)H}`.  Choose `A₀` with `A₀ log(2A₀)` so large that this is
`≤ π/10` (possible since `t ↦ e^{-t}` is eventually below any positive constant, and any
`A₀ ≥ max 100 (log(10 C₀ (5/2)^4/π)/1.2758 + 1)` works because `H ≥ A₀ log(2A₀) ≥ A₀`). -/
theorem critTailNumeric (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ A₀ : ℝ, 6 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ T : ℝ, 2 ≤ T →
      C₀ * Real.sqrt T * (3 + T + A * Real.log (A * T)) ^ 4
        * (1 + A * Real.log (A * T)) ^ 6
        * Real.exp (-(Real.pi / 2) * (A * Real.log (A * T))) ≤ Real.pi / 10 := by
  sorry

end Work.ZeroDensity.Ingham
