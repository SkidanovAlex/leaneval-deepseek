import Mathlib
import Submission.Work.RPB.B1.WindLiftDefs

/-!
# Derivative of `windDir`

`windDir u s = e^{-i·windPhase u s} · u s`, where `windPhase u s = ∫_0^s Im (u'/u)`.
Since `windPhase` is the primitive of the (continuous) integrand `Im (u'/u)`, the derivative of
`exp (-(windPhase u s : ℂ) * I)` is `exp (-(windPhase u s : ℂ) * I) * (-((deriv u s / u s).im : ℂ) * I)`,
and the product rule together with `deriv u s = (deriv u s / u s) * u s` (here `u s ≠ 0`) gives

`(windDir u)' s = exp(-(windPhase u s)*I) * ((-(w.im : ℂ) * I) + w) * u s`

with `w = deriv u s / u s`.  As `w = (w.re : ℂ) + (w.im : ℂ) * I`, the bracket equals `(w.re : ℂ)`,
which is the real (not complex) multiple `(w.re : ℂ) * windDir u s` of `windDir u s` asserted below.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1

/-- The complex number `z` is the sum of its real part and `im z * I`, hence
`-(im z * I) + z = (re z : ℂ)`. -/
private lemma neg_im_mul_I_add (z : ℂ) : -(↑z.im * Complex.I) + z = (↑z.re : ℂ) := by
  refine Complex.ext ?_ ?_ <;> simp

theorem hasDerivAt_windDir (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hne : ∀ t, u t ≠ 0) :
    ∀ s, HasDerivAt (windDir u) (((deriv u s / u s).re : ℂ) * windDir u s) s := by
  intro s
  set c : ℂ := deriv u s / u s with hc
  -- `deriv u` is continuous, hence so is the winding integrand `Im (u'/u)`.
  have hcont_deriv : Continuous (deriv u) := ContDiff.continuous_deriv hu le_rfl
  have hcont_f : Continuous (fun x => (deriv u x / u x).im) :=
    Complex.continuous_im.comp (hcont_deriv.div hu.continuous hne)
  -- Fundamental theorem of calculus for `windPhase`.
  have hphase : HasDerivAt (windPhase u) c.im s := by
    have h1 : HasDerivAt (fun t => ∫ x in (0:ℝ)..t, (deriv u x / u x).im)
        ((deriv u s / u s).im) s :=
      intervalIntegral.integral_hasDerivAt_right (hcont_f.intervalIntegrable 0 s)
        (hcont_f.stronglyMeasurableAtFilter MeasureTheory.volume (nhds s)) hcont_f.continuousAt
    rw [hc]
    rw [show windPhase u = (fun t => ∫ x in (0:ℝ)..t, (deriv u x / u x).im) from rfl]
    exact h1
  -- Derivative of the unimodular factor `exp (-(windPhase · : ℂ) * I)`.
  have hexp : HasDerivAt (fun t => Complex.exp (-((windPhase u t : ℂ) * Complex.I)))
      (Complex.exp (-((windPhase u s : ℂ) * Complex.I)) * (-((c.im : ℂ) * Complex.I))) s := by
    have h2 : HasDerivAt (fun t => -((windPhase u t : ℂ) * Complex.I))
        (-((c.im : ℂ) * Complex.I)) s := by
      have h3 : HasDerivAt (fun t => (windPhase u t : ℂ) * Complex.I) ((c.im : ℂ) * Complex.I) s :=
        (hphase.ofReal_comp).mul_const Complex.I
      exact h3.neg
    exact h2.cexp
  have hud : HasDerivAt u (deriv u s) s :=
    ((hu.differentiable (by norm_num)).differentiableAt).hasDerivAt
  -- Product rule.
  have hprod := hexp.mul hud
  have hdu : deriv u s = c * u s := by
    rw [hc]; exact (div_mul_cancel₀ (deriv u s) (hne s)).symm
  have hmain : HasDerivAt (fun t => Complex.exp (-((windPhase u t : ℂ) * Complex.I)) * u t)
      ((c.re : ℂ) * (Complex.exp (-((windPhase u s : ℂ) * Complex.I)) * u s)) s := by
    refine hprod.congr_deriv ?_
    rw [hdu]
    rw [show Complex.exp (-((windPhase u s : ℂ) * Complex.I)) * (-(↑c.im * Complex.I)) * u s
          + Complex.exp (-((windPhase u s : ℂ) * Complex.I)) * (c * u s)
        = Complex.exp (-((windPhase u s : ℂ) * Complex.I)) *
            ((-(↑c.im * Complex.I) + c) * u s) from by ring]
    rw [neg_im_mul_I_add c]
    ring
  rw [show windDir u = (fun t => Complex.exp (-((windPhase u t : ℂ) * Complex.I)) * u t) from rfl]
  exact hmain

end Work.RPB.B1
