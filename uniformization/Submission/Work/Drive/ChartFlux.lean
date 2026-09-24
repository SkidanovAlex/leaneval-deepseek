import Mathlib

/-!
# The flux of a function on a chart annulus

For a function `V : ℂ → ℝ` and a centre `a : ℂ`, the *radial derivative* of `V` at `z` is the
derivative at `t = 1` of `t ↦ V (a + t • (z - a))`, i.e. the derivative of `V` at `z` in the radial
direction `z - a`.  The *flux* of `V` through the circle of radius `r` centred at `a` is then

`2π · average_{|z-a|=r} (radialDeriv V a z)`,

which is `∮_{|z-a|=r} ∂V/∂n ds` for the outward radial normal `n`.  For a harmonic `V` this quantity
is independent of `r` (Cauchy's theorem on the annulus) and equals `2π` times the logarithmic
coefficient of the circle means of `V`.
-/

namespace Work.Drive

/-- The radial derivative of `V` at `z`, relative to the centre `a`. -/
noncomputable def radialDeriv (V : ℂ → ℝ) (a z : ℂ) : ℝ :=
  deriv (fun t : ℝ => V (a + (t : ℂ) * (z - a))) 1

/-- The flux of `V` through the circle of radius `r` centred at `a`. -/
noncomputable def circleFlux (V : ℂ → ℝ) (a : ℂ) (r : ℝ) : ℝ :=
  2 * Real.pi * Real.circleAverage (fun z : ℂ => radialDeriv V a z) a r

end Work.Drive
