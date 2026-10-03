import Mathlib
import Submission.Work.Pert.PinLogDev.Setup

namespace Work.Pert.PinLogDev

open Complex

/-!
# `Work.Pert.PinLogDev.tauC_primitive`

The explicit antiderivative of the covering coordinate `τ_f(w) = σ / (1 - e^{-2πiαw})`
(`Work.Pert.tauC`, Shishikura (A.1.5)): on the slit plane,

  `d/dw [ σ w + (σ / (2πiα)) · log (1 - e^{-2πiα w}) ] = τ_f(w)`.

Indeed the chain rule on `g z = 1 - e^{-2πiα z}` (whose derivative is `2πiα · e^{-2πiα w}`)
together with `Complex.hasDerivAt_log` (valid at `g w` because `g w` lies in the slit plane)
gives the derivative `σ + (σ / (2πiα)) · (2πiα e^{-2πiαw}) / (1 - e^{-2πiαw})`, and
`(σ/(2πiα)) · (2πiα e)/(1-e) = σ e/(1-e)`, so the total is `σ + σe/(1-e) = σ/(1-e) = τ_f w`.

This is the identity that makes the round trip `pin → anchor → pin` of the pinned Fatou
coordinate exact: the `log M` of the pin cancels the `log (1 - e^{-2πiα w})` of the path integral
with the same coefficient (see `NOTES.md` of this directory).
-/

theorem tauC_primitive (σ α w : ℂ) (hα : α ≠ 0)
    (hslit : (1 - Complex.exp (-(2 * Real.pi * I * α * w))) ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => σ * z + (σ / (2 * Real.pi * I * α)) *
        Complex.log (1 - Complex.exp (-(2 * Real.pi * I * α * z))))
      (Work.Pert.tauC σ α w) w := by
  -- The denominator `1 - e^{-2πiαw}` does not vanish (it lies in the slit plane).
  have hne : (1 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 0 :=
    Complex.slitPlane_ne_zero hslit
  -- Chain rule: `z ↦ e^{-2πiα z}`.
  have hExp : HasDerivAt (fun z : ℂ => Complex.exp (-(2 * Real.pi * I * α * z)))
      (Complex.exp (-(2 * Real.pi * I * α * w)) * (-(2 * Real.pi * I * α))) w := by
    have h1 : HasDerivAt (fun z : ℂ => -(2 * Real.pi * I * α * z)) (-(2 * Real.pi * I * α)) w :=
      (hasDerivAt_const_mul (2 * Real.pi * I * α) (x := w)).neg
    exact (Complex.hasDerivAt_exp (-(2 * Real.pi * I * α * w))).comp w h1
  -- Chain rule: `z ↦ 1 - e^{-2πiα z}`, derivative `2πiα · e^{-2πiα w}`.
  have hinner : HasDerivAt (fun z : ℂ => 1 - Complex.exp (-(2 * Real.pi * I * α * z)))
      (2 * Real.pi * I * α * Complex.exp (-(2 * Real.pi * I * α * w))) w := by
    have h := (hasDerivAt_const (x := w) (c := (1 : ℂ))).sub hExp
    rw [show (0 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * w)) * (-(2 * Real.pi * I * α))
        = 2 * Real.pi * I * α * Complex.exp (-(2 * Real.pi * I * α * w)) from by ring] at h
    exact h
  -- Chain rule for the logarithm (the argument lies in the slit plane) and multiplication by
  -- the constant `σ / (2πiα)`.
  have hmul := (hinner.clog hslit).const_mul (σ / (2 * Real.pi * I * α))
  -- The linear part `z ↦ σ z`.
  have hlin : HasDerivAt (fun z : ℂ => σ * z) σ w :=
    hasDerivAt_const_mul σ (x := w)
  have hsum := hlin.add hmul
  -- The computed value is `τ_f w = σ / (1 - e^{-2πiα w})`.
  rw [show σ + (σ / (2 * Real.pi * I * α)) *
      ((2 * Real.pi * I * α * Complex.exp (-(2 * Real.pi * I * α * w))) /
        (1 - Complex.exp (-(2 * Real.pi * I * α * w)))) = Work.Pert.tauC σ α w from by
    rw [Work.Pert.tauC]
    have hc : (2 * Real.pi * I * α) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hα
    field_simp
    ring] at hsum
  exact hsum

end Work.Pert.PinLogDev
