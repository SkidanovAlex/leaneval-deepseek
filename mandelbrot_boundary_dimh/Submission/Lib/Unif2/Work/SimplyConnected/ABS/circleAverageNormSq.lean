import Mathlib

/-!
# Ingredients for `⨍ ‖z - a‖² = ‖p - a‖² + r²`

The chart-ball minimum principle (row 3 of `NOTES_globalizedBarrierGlobal_SESSION3.md` §14) needs the
identity
```
⨍ [z ↦ ‖z - a‖²] (p, r) = ‖p - a‖² + r²,
```
which is not in Mathlib or the workspace.  This module banks the first of its two ingredients — the
one that needs no linearity plumbing, only the fact that `‖z - p‖` is constantly `r` on the circle
`sphere p r`:

`circleAverage_norm_sq_sub_center : ⨍ [z ↦ ‖z - p‖²] (p, r) = r²`.

The second ingredient is `⨍ [z ↦ z - p] (p, r) = 0` (equivalently `⨍⟪z - p, p - a⟫ = 0`), which
follows from the integral of `θ ↦ p + r·e^{iθ}` over a full period; with the two, the decomposition
`‖z - a‖² = ‖z - p‖² + 2⟪z - p, p - a⟫ + ‖p - a‖²` and the linearity lemmas
`Real.circleAverage_add/_sub/_fun_smul/_const` give the identity.
-/

open Filter Set
open scoped Topology

namespace Work.SimplyConnected.ABS

/-- On the circle of radius `r > 0` around `p`, the function `z ↦ ‖z - p‖²` is constantly `r²`, so
its circle average is `r²`. -/
theorem circleAverage_norm_sq_sub_center (p : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun z => ‖z - p‖ ^ 2) p r = r ^ 2 := by
  rw [Real.circleAverage_congr_sphere (f₁ := fun z => ‖z - p‖ ^ 2) (f₂ := fun _ => r ^ 2) ?_]
  · exact Real.circleAverage_const (r ^ 2) p r
  · intro z hz
    rw [Metric.mem_sphere, abs_of_pos hr, dist_eq_norm] at hz
    show ‖z - p‖ ^ 2 = r ^ 2
    rw [hz]

/-- The real part of `z - p` has circle average `0` around `p`: it is the real part of the
holomorphic affine map `z ↦ z - p`, hence harmonic, so its average is its value at the centre. -/
theorem circleAverage_sub_center_re (p : ℂ) (r : ℝ) :
    Real.circleAverage (fun z => (z - p).re) p r = 0 := by
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => (z - p).re)
      (Metric.closedBall p |r|) :=
    fun z _ => (analyticAt_id.sub analyticAt_const).harmonicAt_re
  have h := InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm
  simpa using h

/-- The imaginary part of `z - p` has circle average `0` around `p`. -/
theorem circleAverage_sub_center_im (p : ℂ) (r : ℝ) :
    Real.circleAverage (fun z => (z - p).im) p r = 0 := by
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => (z - p).im)
      (Metric.closedBall p |r|) :=
    fun z _ => (analyticAt_id.sub analyticAt_const).harmonicAt_im
  have h := InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm
  simpa using h

/-- **Pointwise expansion.**  `‖z - a‖² = ‖z - p‖² + 2⟪z - p, p - a⟫ + ‖p - a‖²` written out in
real and imaginary parts (the real inner product on `ℂ` is
`⟪x, y⟫_ℝ = x.re * y.re + x.im * y.im`). -/
theorem norm_sq_sub_expansion (z p a : ℂ) :
    ‖z - a‖ ^ 2
      = ‖z - p‖ ^ 2 + 2 * ((z - p).re * (p - a).re + (z - p).im * (p - a).im)
        + ‖p - a‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- The expansion in the *canonical order* for `circleAverage_fun_smul`: the scalar factors
`(p - a).re`, `(p - a).im` on the **left** of the `z`-dependent factors. -/
theorem norm_sq_sub_expansion' (z p a : ℂ) :
    ‖z - a‖ ^ 2
      = ‖z - p‖ ^ 2
        + 2 * ((p - a).re * (z - p).re + (p - a).im * (z - p).im) + ‖p - a‖ ^ 2 := by
  rw [norm_sq_sub_expansion z p a]
  ring

end Work.SimplyConnected.ABS
