import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# The Fourier transform of an affine piece (GM §9)

Auxiliary file for GM §9: the exact computation of the Fourier transform of one affine
piece `u ↦ f ((c*u+d)/e)`.  The substitution `w = (c*u+d)/e` (i.e. `u = (e*w-d)/c`)
has Jacobian `|e/c|` and turns the phase `e^{-2πi ξ u}` into
`efun (ξ*d/c) · e^{-2πi (ξ*e/c) w}`.
-/

open MeasureTheory Complex

namespace Work.GM.Affine

/-- `efun t = exp (2 π i t)` is the complex exponential of the additive character `𝐞`. -/
lemma efun_eq_fourierChar (t : ℝ) : efun t = (Real.fourierChar t : ℂ) := by
  rw [efun, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The affine change of variable `u = (e/c)*x - d/c` inverts `x = (c*u+d)/e`. -/
private lemma affine_arg {c d e : ℝ} (hc : c ≠ 0) (he : e ≠ 0) (x : ℝ) :
    (c * ((e / c) * x - d / c) + d) / e = x := by
  field_simp
  ring

/-- The phase of the affine piece, after the change of variable `u = (e/c)*x - d/c`. -/
private lemma affine_phase {c d e ξ : ℝ} (hc : c ≠ 0) (_he : e ≠ 0) (x : ℝ) :
    -(((e / c) * x - d / c) * ξ) = -(x * (ξ * e / c)) + ξ * d / c := by
  field_simp
  ring

/-- Real scalar multiplication on `ℂ` is complex multiplication. -/
private lemma real_smul_eq_mul (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := by simp

/-- The change of variables `u = (e/c)*x - d/c` on the line, valid for arbitrary (possibly
non-integrable) integrands thanks to the convention that non-integrable functions have
integral zero. -/
private lemma integral_comp_affine (φ : ℝ → ℂ) {c d e : ℝ} (hc : c ≠ 0) (he : e ≠ 0) :
    ∫ u : ℝ, φ u = |e / c| • ∫ x : ℝ, φ ((e / c) * x - d / c) := by
  have hce : e / c ≠ 0 := div_ne_zero he hc
  have h1 : (|c / e| : ℝ) = |e / c|⁻¹ := by
    rw [← abs_inv]
    congr 1
    exact (inv_div e c).symm
  have key : ∫ x : ℝ, φ ((e / c) * x - d / c) = |e / c|⁻¹ • ∫ y : ℝ, φ y := by
    have hcomp := Measure.integral_comp_mul_left (F := ℂ) (fun y : ℝ => φ (y + -(d / c))) (e / c)
    have htrans : ∫ y : ℝ, (fun y : ℝ => φ (y + -(d / c))) y = ∫ y : ℝ, φ y :=
      integral_add_right_eq_self (fun y : ℝ => φ y) (-(d / c))
    rw [htrans] at hcomp
    simpa [sub_eq_add_neg, h1] using hcomp
  rw [key, smul_smul, mul_inv_cancel₀ (abs_ne_zero.mpr hce), one_smul]

/-- Pointwise form of the substitution: after `u = (e/c)*x - d/c` the integrand of the
Fourier transform of the affine piece is the phase `efun (ξ*d/c)` times the integrand of
`Fhat f (ξ*e/c)`. -/
private lemma piece_pointwise {f : ℝ → ℝ} {c d e ξ : ℝ} (hc : c ≠ 0) (he : e ≠ 0) (x : ℝ) :
    Real.fourierChar (-(((e / c) * x - d / c) * ξ)) •
        ((f ((c * ((e / c) * x - d / c) + d) / e) : ℝ) : ℂ)
      = efun (ξ * d / c) * (Real.fourierChar (-(x * (ξ * e / c))) • ((f x : ℝ) : ℂ)) := by
  rw [affine_arg hc he x, affine_phase hc he x]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [AddChar.map_add_eq_mul, Circle.coe_mul, efun_eq_fourierChar]
  ring

/-- The Fourier transform of one affine piece `u ↦ f ((c*u+d)/e)` (`c ≠ 0`, `e ≠ 0`):
`𝓕 (fun u => (f ((c*u+d)/e) : ℂ)) ξ = (|e/c| : ℂ) * Fhat f (ξ*e/c) * efun (ξ*d/c)`.

(`Fhat f η = 𝓕 (fun u => (f u : ℂ)) η = ∫ u, e^{-2πi u η} f u`, `efun t = exp (2π i t)`.
Derivation: substitute `w = (c*u+d)/e`, i.e. `u = (e*w-d)/c`, with Jacobian `|e/c|`; the phase
becomes `e^{-2πi ξ (e w - d)/c} = efun (ξ*d/c) * e^{-2πi (ξ*e/c) w}`.) -/
theorem fourier_piece {f : ℝ → ℝ} {c d e ξ : ℝ} (hc : c ≠ 0) (he : e ≠ 0) :
    FourierTransform.fourier (fun u : ℝ => ((f ((c * u + d) / e) : ℝ) : ℂ)) ξ
      = ((|e / c| : ℝ) : ℂ) * Fhat f (ξ * e / c) * efun (ξ * d / c) := by
  rw [Real.fourier_real_eq]
  rw [integral_comp_affine
        (φ := fun u : ℝ => Real.fourierChar (-(u * ξ)) • ((f ((c * u + d) / e) : ℝ) : ℂ))
        (c := c) (d := d) (e := e) hc he]
  simp only [piece_pointwise hc he]
  rw [integral_const_mul]
  have h3 : ∫ x : ℝ, Real.fourierChar (-(x * (ξ * e / c))) • ((f x : ℝ) : ℂ)
      = Fhat f (ξ * e / c) := by
    simp only [Fhat]
    rw [Real.fourier_real_eq]
  rw [h3, real_smul_eq_mul]
  ring

end Work.GM.Affine
