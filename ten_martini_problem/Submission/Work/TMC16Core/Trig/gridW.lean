import Mathlib

/-!
# The `q`-grid distance function `gridW`

`gridW q A j = min_{m ∈ {0,1,2}} |(j : ℝ) + A - m * q|` is the distance from `(j : ℝ) + A`
to the nearest multiple of `q`, valid whenever `0 ≤ A < q` and `j < q` (so that
`(j : ℝ) + A ∈ [0, 2q)`).  It is the auxiliary object in the trigonometric sum estimate
`Work.TMC16Core.Trig.grid_nn_sum`.
-/

noncomputable section

namespace Work.TMC16Core.Trig

/-- Distance from `(j : ℝ) + A` to the nearest multiple of `q`, for `0 ≤ A < q`, `j < q`. -/
noncomputable def gridW (q : ℕ) (A : ℝ) (j : ℕ) : ℝ :=
  min (min ((j : ℝ) + A) |(j : ℝ) + A - (q : ℝ)|) (2 * (q : ℝ) - (j : ℝ) - A)

end Work.TMC16Core.Trig
