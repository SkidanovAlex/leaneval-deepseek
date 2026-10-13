import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllExist.Honesty.G1Aux
import Submission.Work.FTS.EllExist.Honesty.G1Endpoint.g1A_sq_le
import Submission.Work.FTS.EllExist.Honesty.G1Endpoint.g1_endpoint_const
import Submission.Work.FTS.EllExist.Honesty.G1Endpoint.G1_sq_div_cube_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

/-!
# The endpoint bound for the singular Green term `G1`

`G1 α m c z = z ^ (G1s α m) * G1A α m c z` with `G1s α m = -(2m+5)/α =: -a`, `a = G1a α m > 0`,
and `G1A α m c z = ∫_0^z c t t^{a-1} dt`.  This file proves the uniform endpoint bound

  `G1 α m c x ^ 2 / x ^ 3 ≤ G1CPhi α m c`  for every `0 < x < 1`,

with `G1CPhi α m c = G1C0 α m c ^ 2`, `G1C0 α m c = G1M0 c / 2 + 1/(2(2a+3))`,
`G1M0 c = ∫_{(0,1)} c z²/z⁴`.

Route (exactly the estimate recorded in the `G1_est` route comment): factor
`c t t^{a-1} = (c t / t²)·t^{a+1}` and apply Cauchy–Schwarz in `t` over `(0,x)`, bounding the
first factor by `G1M0 c` (monotonicity of the nonnegative integral) and evaluating the second,
`∫_0^x t^{2a+2} = x^{2a+3}/(2a+3)`.  This gives `G1A x² ≤ G1M0 c · x^{2a+3}/(2a+3)`, hence
(dividing by the positive `x^{2a+3}`) `G1 x²/x³ ≤ G1M0 c/(2a+3)`.  Finally
`G1M0 c/(2a+3) ≤ (G1M0 c/2 + 1/(2(2a+3)))²` is the elementary AM–GM identity
`4·(A/2)·(1/(2b)) = A/b` with `b = 2a+3` (equivalently `(A/2 - 1/(2b))² ≥ 0`).

The three ingredients are the lemmas
`Work.FTS.EllExist.Honesty.G1Endpoint.g1A_sq_le`,
`...G1_sq_div_cube_le` and `...g1_endpoint_const`.
-/

/-- **Endpoint bound for the singular Green term `G1`.**  For `0 < x < 1` the weighted square
`G1 x²/x³` is bounded by the constant `G1CPhi α m c`, uniformly in `x` (this is the `x → 0`
endpoint term of the energy identity `G1_energy_identity`). -/
theorem G1_endpoint_bound {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
        ≤ Work.FTS.EllExist.Honesty.G1CPhi α m c := by
  intro x hx0 hx1
  -- `b := 2a + 3 > 0`
  have hb : (0 : ℝ) < 2 * G1a α m + 3 := by
    have := G1a_pos hα m
    linarith
  -- Cauchy–Schwarz: `G1A x² ≤ G1M0 c · x^{2a+3}/(2a+3)`.
  have hcs := G1Endpoint.g1A_sq_le hα m hc h0 x hx0 hx1
  -- Scaling by `x^{-2a-3}`: `G1 x²/x³ ≤ G1M0 c/(2a+3)`.
  have hscale := G1Endpoint.G1_sq_div_cube_le (α := α) m (c := c) hx0 hcs
  -- AM–GM: `A/b ≤ (A/2 + 1/(2b))²`.
  have hconst := G1Endpoint.g1_endpoint_const (A := G1M0 c) (b := 2 * G1a α m + 3)
    (G1M0_nonneg c) hb
  rw [G1CPhi, G1C0]
  linarith

end Work.FTS.EllExist.Honesty
