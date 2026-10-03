/-
# `Submission.Work.FITop3.Smooth` — the elementary smooth bumps used by the chapter

Two elementary functions and the bumps built from them:

* `sm` — the clamped quadratic ramp `0` on `(-∞,0]`, `2t²` on `[0,1/2]`, `1-2(1-t)²` on
  `[1/2,1]`, `1` on `[1,∞)`.  It is `C¹`, monotone, and its *discrete* differences satisfy
  `|Δ sm| ≤ 2δ + 2δ²` and `|Δ² sm| ≤ 4δ² + 8δ³` — which is what the finitely-many derivative
  conditions of the paper (`|f^{(j)}| ≪ M^{-j}`, `|p^{(j)}| ≪ (θN)^{-j}`, `|q^{(j)}| ≪ θ^{-j}`,
  `j ≤ 2`) mean in the discrete form the areas use.

* `segBump` / `angBump` — the radial and angular mollifiers of (4.13)/(5.13), and `majorant`,
  the annulus majorant `f` of (5.17)/(5.19).  All three are *products of two ramps*, which is what
  makes their support and their two derivative bounds elementary.

The properties are proved in `Submission.Work.FITop3.Smooth.sm_props` and
`.../Smooth.bump_props`; the concrete witnesses of `IsMajorant` and `IsBetaCoeff` in `Majorant`
and `Witness` are built from these.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FITop3

noncomputable section

/-- The clamped quadratic ramp: `0` for `t ≤ 0`, `2t²` for `0 ≤ t ≤ 1/2`, `1-2(1-t)²` for
`1/2 ≤ t ≤ 1`, `1` for `t ≥ 1`.  It is the `C¹` piecewise-quadratic "smoothstep" with minimal
derivative bounds `|sm'| ≤ 2` and `|sm'|` Lipschitz of constant `4`. -/
def sm (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 / 2 then 2 * t ^ 2 else if t ≤ 1 then 1 - 2 * (1 - t) ^ 2 else 1

/-- A smooth bump on the real line: rises over `[a, a+W]`, equals `1` on `[a+W, a+L-W]`, falls
over `[a+L-W, a+L]`, and vanishes outside `(a, a+L)`.  Used with `a = 0`. -/
def bump (W L t : ℝ) : ℝ := sm (t / W) * sm ((L - t) / W)

/-- The radial mollifier `p` of (4.13): a bump supported on the segment (4.12)
`(N, (1+θ)N]`, equal to `1` on the middle half of it. -/
def segBump (N θ u : ℝ) : ℝ := bump (θ * N / 4) ((1 + θ) * N - N) (u - N)

/-- The angular mollifier `q` of (5.12): a bump supported on the sector
`(0, 2πθ]`, equal to `1` on the middle half of it. -/
def angBump (θ α : ℝ) : ℝ := bump (Real.pi * θ / 2) (2 * Real.pi * θ) α

/-- The annulus majorant `f` of (5.17)/(5.19): supported in `M/4 ≤ u ≤ 4M`, equal to `1` on the
whole dyadic segment `M ≤ u ≤ 2M`.  The upper ramp is twice as wide as the lower one, which is
what makes `f = 1` reach `2M`. -/
def majorant (M : ℝ) (u : ℤ) : ℝ :=
  sm (((u : ℝ) - M / 4) / (3 * M / 4)) * sm ((4 * M - (u : ℝ)) / (2 * M))

end

end Work.FITop3
