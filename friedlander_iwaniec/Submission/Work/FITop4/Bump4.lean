/-
# `Submission.Work.FITop4.Bump4` — the explicit `C²` bumps of the round-4 witness

The round-3 witness used `Work.FITop3.sm`, a *clamped quadratic*, which is only `C¹`; the round-4
`IsBetaCoeff` requires the mollifiers of (4.12)/(5.12) to be `C²` (`ContDiff ℝ 2`) with *absolute*
derivative constants.  We therefore use the **clamped quintic** Hermite step

  `quinticStep t = 0` for `t ≤ 0`, `= 1` for `1 ≤ t`, `= t³(10 − 15t + 6t²)` on `[0,1]`,

whose two derivatives match the constants across `0` and `1`, so it is `C²` (but not `C³`:
`p'''(1⁻) = 60`).  Its derivatives are the *polynomials* `p'(t) = 30t²(1−t)² ≤ 2` and
`p''(t) = 60t(1−t)(1−2t) ≤ 6`, so the derivative bounds of the bump are explicit — which is what
the *absolute* constants `cMoll` of `IsBetaCoeff` need.

The bump `smoothBump W L t = quinticStep(t/W)·quinticStep((L−t)/W)` is supported in `(0, L)`,
takes values in `[0,1]`, equals `1` at `t = L/2` (when `L = 2W`), and satisfies
`|bump'| ≤ 4/W`, `|bump''| ≤ 20/W²`.

The properties are proved in `Submission/Work/FITop4/Bump4_props.lean`.
-/
import Mathlib
import Submission.Work.FITop4.Defs4

set_option autoImplicit false

namespace Work.FITop4

noncomputable section

/-- The clamped quintic Hermite step: `0` on `(-∞, 0]`, `1` on `[1, ∞)`, and the quintic
`t³(10 − 15t + 6t²) = 10t³ − 15t⁴ + 6t⁵` in between (with `p(0) = p'(0) = p''(0) = 0`,
`p(1) = 1`, `p'(1) = p''(1) = 0`). -/
def quinticStep (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else t ^ 3 * (10 - 15 * t + 6 * t ^ 2)

/-- The `C²` bump of width parameter `W` and length `L`: the product of two clamped quintic steps,
supported in `(0, L)`, with `smoothBump W (2W) W = 1`. -/
def smoothBump (W L t : ℝ) : ℝ := quinticStep (t / W) * quinticStep ((L - t) / W)

end

end Work.FITop4
