import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FITop.Defs
import Submission.Work.FITop3.Defs3

namespace Work.FIArea4

open scoped BigOperators
open scoped Classical

/-! ## Auxiliary facts about `Complex.arg`

The determinant `Δ(z₁,z₂) = Im(z̄₁z₂)` is `|z₁||z₂|·sin(α₂-α₁)` where `αᵢ` is the principal
argument of `zᵢ`; this is the only complex-analytic input to (6.2) for a sector. -/

/-- `Im(z̄₁z₂) = |z₁||z₂|·sin(α₂-α₁)`: the imaginary part of `z̄₁z₂` is the modulus of the product
times the sine of the difference of the principal arguments.  Proved by means of
`Real.Angle`, which records the argument of a product additively. -/
lemma im_starRingEnd_mul (a b : ℂ) :
    (((starRingEnd ℂ) a) * b).im = ‖a‖ * ‖b‖ * Real.sin (b.arg - a.arg) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have h0 : (starRingEnd ℂ) a ≠ 0 := by simp [ha]
  have h1 : ((((starRingEnd ℂ) a) * b).arg : Real.Angle) = ((b.arg - a.arg : ℝ) : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle h0 hb, Complex.arg_conj_coe_angle, Real.Angle.coe_sub]
    abel
  have key : Real.sin ((((starRingEnd ℂ) a) * b).arg) = Real.sin (b.arg - a.arg) := by
    rw [← Real.Angle.sin_coe, h1, Real.Angle.sin_coe]
  rw [← Complex.norm_mul_sin_arg (((starRingEnd ℂ) a) * b), norm_mul, Complex.norm_conj, key]

/-- `√|z|² = |z|` as complex numbers: the Euclidean modulus of a Gaussian integer is the square
root of its norm. -/
lemma sqrt_gnorm (z : GaussianInt) :
    Real.sqrt ((Work.FIPlan.gnorm z : ℝ)) = ‖(z : ℂ)‖ := by
  have h : (Work.FIPlan.gnorm z : ℝ) = ‖(z : ℂ)‖ ^ 2 := by
    rw [Work.FIPlan.gnorm, GaussianInt.natCast_natAbs_norm, GaussianInt.intCast_real_norm,
      Complex.normSq_eq_norm_sq]
  rw [h, Real.sqrt_sq (norm_nonneg _)]

/-- **(6.2) for a sector**: two Gaussian integers in the same sector of angle `2πθ` of the polar
box `(5.14)` have determinant `Δ(z₁,z₂) = Im(z̄₁z₂)` bounded by `2πθ·|z₁||z₂|` — because
`Δ = |z₁||z₂|·sin(α₂-α₁)` with both principal arguments `αᵢ` in an interval of length `2πθ`, and
`|sin x| ≤ |x|`.  This is the sector form of `1 ≤ |Δ| < 4πθN` of (6.2) and bounds the range of the
moduli `d` in §15. -/
theorem absDelta_le_sector (Pa : Work.FITop.Params) (φ : ℝ) {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    (Work.FIPlan.absDelta z1 z2 : ℝ)
      ≤ 2 * Real.pi * Pa.θ * Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ))
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) := by
  have hkey : (Work.FIPlan.Delta z1 z2 : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg) := by
    rw [Work.FIPlan.Delta, GaussianInt.intCast_im, GaussianInt.toComplex_mul,
        GaussianInt.toComplex_star]
    exact im_starRingEnd_mul (z1 : ℂ) (z2 : ℂ)
  have hsin : |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)| ≤ 2 * Real.pi * Pa.θ := by
    have hlt1 : φ < (z1 : ℂ).arg := h1.2.2.2.1
    have hle1 : (z1 : ℂ).arg ≤ φ + 2 * Real.pi * Pa.θ := h1.2.2.2.2
    have hlt2 : φ < (z2 : ℂ).arg := h2.2.2.2.1
    have hle2 : (z2 : ℂ).arg ≤ φ + 2 * Real.pi * Pa.θ := h2.2.2.2.2
    calc |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)| ≤ |(z2 : ℂ).arg - (z1 : ℂ).arg| :=
          Real.abs_sin_le_abs
      _ ≤ 2 * Real.pi * Pa.θ := by
          apply abs_le.mpr; constructor <;> linarith
  calc (Work.FIPlan.absDelta z1 z2 : ℝ)
      = |↑(Work.FIPlan.Delta z1 z2)| := by
          rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
    _ = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)| := by
          rw [hkey]
          simp only [abs_mul, abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * (2 * Real.pi * Pa.θ) := by gcongr
    _ = 2 * Real.pi * Pa.θ * Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ))
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) := by
          rw [sqrt_gnorm z1, sqrt_gnorm z2]; ring

end Work.FIArea4
