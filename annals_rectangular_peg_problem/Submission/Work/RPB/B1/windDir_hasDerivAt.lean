import Mathlib
import Submission.Work.RPB.B1.WindLiftDefs

/-!
# The ODE satisfied by the unwound curve `windDir`

For a `C¹` nowhere-zero curve `u : ℝ → ℂ`, the curve

`windDir u s = e^{-i·windPhase u s}·u s`,  `windPhase u s = ∫_0^s Im (u'/u)`,

has derivative a *real* multiple of itself:

`(windDir u)' s = Re (u' s / u s) · windDir u s`.

This is the linear ODE that makes `windDir u` a positive multiple of `u 0` (used in
`Submission.Work.RPB.B1.windInt_lift`).

The proof is a direct computation: `windPhase u` is the primitive of the continuous function
`x ↦ Im (u' x / u x)`, so `(windPhase u)' = Im (u'/u)`; the chain rule on `s ↦ e^{-i·windPhase u s}`
and the product rule then give the claim, using the elementary identity
`Re c · w = c·w - Im c · I · w` for `c = u' s / u s`, `w = u s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory intervalIntegral Filter

namespace Work.RPB.B1

/-- Elementary algebra behind the ODE: if `d = c * w` then
`A * (-(Im c · I)) * w + A * d = Re c · (A * w)`. -/
private lemma windDir_key_deriv (c w d A : ℂ) (hd : d = c * w) :
    A * (-(c.im * Complex.I)) * w + A * d = (c.re : ℂ) * (A * w) := by
  have h1 : (c.re : ℂ) * w = d - (c.im : ℂ) * Complex.I * w := by
    have h := Complex.re_add_im c
    rw [hd]
    linear_combination w * h
  rw [show (c.re : ℂ) * (A * w) = A * ((c.re : ℂ) * w) by ring, h1]
  ring

theorem windDir_hasDerivAt (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hne : ∀ t, u t ≠ 0) :
    ∀ s, HasDerivAt (windDir u) (((deriv u s / u s).re : ℂ) * windDir u s) s := by
  intro s
  -- the logarithmic derivative `u'/u` is continuous
  have hgc : Continuous (fun x : ℝ => (deriv u x / u x).im) :=
    Complex.continuous_im.comp ((hu.continuous_deriv le_rfl).div hu.continuous hne)
  -- `windPhase u` is its primitive, hence has derivative `Im (u'/u)`
  have hphfun : windPhase u = fun s : ℝ => ∫ x in (0 : ℝ)..s, (deriv u x / u x).im := by
    funext s; rfl
  have hphase : HasDerivAt (windPhase u) ((deriv u s / u s).im) s := by
    rw [hphfun]
    exact intervalIntegral.integral_hasDerivAt_right
      (hgc.intervalIntegrable 0 s)
      (hgc.stronglyMeasurableAtFilter volume (nhds s)) hgc.continuousAt
  -- derivative of `s ↦ e^{-i·windPhase u s}`
  have hinner : HasDerivAt (fun x : ℝ => -((windPhase u x : ℂ) * Complex.I))
      (-(((deriv u s / u s).im : ℂ) * Complex.I)) s := by
    have h1 : HasDerivAt (fun x : ℝ => (windPhase u x : ℂ))
        (((deriv u s / u s).im : ℂ)) s := hphase.ofReal_comp
    have h2 := h1.mul_const (-Complex.I)
    simpa [mul_neg] using h2
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (-((windPhase u x : ℂ) * Complex.I)))
      (Complex.exp (-((windPhase u s : ℂ) * Complex.I)) *
        (-(((deriv u s / u s).im : ℂ) * Complex.I))) s :=
    (Complex.hasDerivAt_exp _).comp s hinner
  -- derivative of `u`
  have hud : HasDerivAt u (deriv u s) s := by
    have h : DifferentiableAt ℝ u s := (hu.differentiable (by simp)) s
    simpa using h.hasDerivAt
  have hprod := hexp.mul hud
  -- the algebraic identity closing the computation
  have hd_eq : deriv u s = (deriv u s / u s) * u s := (div_mul_cancel₀ _ (hne s)).symm
  have hmain := windDir_key_deriv (deriv u s / u s) (u s) (deriv u s)
    (Complex.exp (-((windPhase u s : ℂ) * Complex.I))) hd_eq
  have hfun : windDir u
      = fun x : ℝ => Complex.exp (-((windPhase u x : ℂ) * Complex.I)) * u x := by
    funext x; rfl
  rw [hfun]
  show HasDerivAt (fun x : ℝ => Complex.exp (-((windPhase u x : ℂ) * Complex.I)) * u x)
    (((deriv u s / u s).re : ℂ) * (Complex.exp (-((windPhase u s : ℂ) * Complex.I)) * u s)) s
  convert hprod using 1
  exact hmain.symm

end Work.RPB.B1
