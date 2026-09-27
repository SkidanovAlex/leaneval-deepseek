import Mathlib

namespace Work.Drive

/-- The (normalised) argument of `z t₀` plus the imaginary part of the logarithm of `z s / z t₀`,
i.e. the continuous lift of the argument of `z s` through `z t₀`, is differentiable at `t` with
derivative `(deriv z t / z t).im / π`.  This is the derivative of the "local argument" function used
in the winding-number bookkeeping. -/
theorem hasDerivAt_localArg {z : ℝ → ℂ} {t₀ t : ℝ} (hz : HasDerivAt z (deriv z t) t)
    (ht : z t / z t₀ ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => (Complex.arg (z t₀) + (Complex.log (z s / z t₀)).im) / Real.pi)
      ((deriv z t / z t).im / Real.pi) t := by
  -- `z t / z t₀ ∈ slitPlane` forces `z t ≠ 0` and `z t₀ ≠ 0`.
  have hne : z t / z t₀ ≠ 0 := fun h => Complex.zero_notMem_slitPlane (h ▸ ht)
  have hzt : z t ≠ 0 := (div_ne_zero_iff.mp hne).1
  have ht0 : z t₀ ≠ 0 := (div_ne_zero_iff.mp hne).2
  -- The inner map `s ↦ z s / z t₀` is differentiable at `t`.
  have hinner : HasDerivAt (fun s => z s / z t₀) (deriv z t / z t₀) t := hz.div_const (z t₀)
  -- Chain rule with `Complex.log`, differentiable on the slit plane.
  have hlog : HasDerivAt (fun s => Complex.log (z s / z t₀))
      ((z t / z t₀)⁻¹ * (deriv z t / z t₀)) t :=
    HasDerivAt.comp t (Complex.hasDerivAt_log ht) hinner
  -- Simplify the derivative: `(z t / z t₀)⁻¹ * (deriv z t / z t₀) = deriv z t / z t`.
  have hderiv_eq : (z t / z t₀)⁻¹ * (deriv z t / z t₀) = deriv z t / z t := by
    field_simp
  rw [hderiv_eq] at hlog
  -- Take imaginary parts (a continuous `ℝ`-linear projection).
  have him : HasDerivAt (fun s => (Complex.log (z s / z t₀)).im) ((deriv z t / z t).im) t :=
    HasFDerivAt.comp_hasDerivAt t (ContinuousLinearMap.hasFDerivAt Complex.imCLM) hlog
  -- Add the constant `arg (z t₀)` and divide by `π`.
  have hfin := ((hasDerivAt_const (x := t) (Complex.arg (z t₀))).add him).div_const Real.pi
  simpa using hfin

end Work.Drive
