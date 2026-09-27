import Mathlib
import Submission.Work.EQ.SymDefs

/-!
# Reflection identities for `polarPt`

`polarPt c r θ = c + r e^{iθ}` for real `c, r, θ`.  We record the elementary
Cartesian form and the reflection/periodicity identities needed by the
equichordal development:

* complex conjugation is `θ ↦ -θ`;
* negating the conjugate reflects the left focus `-a/2` to the right focus
  `a/2` and sends `θ ↦ π - θ`;
* the imaginary part is `r sin θ`;
* on the real axis (`sin θ = 0`) the point is the real number `r cos θ + c`;
* `θ ↦ θ + 2π` is a period.
-/

namespace Work.EQ

open Complex

/-- Cartesian (cosine/sine) form of `polarPt`. -/
lemma polarPtReflect_eq_cos_sin (c r θ : ℝ) :
    polarPt c r θ = ((c + r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [polarPt, Complex.exp_ofReal_mul_I]
  push_cast
  ring

/-- Real part of `polarPt`. -/
lemma polarPtReflect_re (c r θ : ℝ) : (polarPt c r θ).re = c + r * Real.cos θ := by
  rw [polarPtReflect_eq_cos_sin]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- Imaginary part of `polarPt`. -/
lemma polarPtReflect_im (c r θ : ℝ) : (polarPt c r θ).im = r * Real.sin θ := by
  rw [polarPtReflect_eq_cos_sin]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_one, zero_mul, zero_add, add_zero]

/-- Complex conjugation acts as `θ ↦ -θ` on `polarPt` with real centre and radius. -/
lemma polarPtReflect_neg (c r θ : ℝ) : star (polarPt c r θ) = polarPt c r (-θ) := by
  apply Complex.ext
  · simp only [RCLike.star_def, Complex.conj_re, polarPtReflect_re, Real.cos_neg]
  · simp only [RCLike.star_def, Complex.conj_im, polarPtReflect_im, Real.sin_neg]
    ring

theorem polarPt_reflect (a : ℝ) (ρ : ℝ → ℝ) :
    (∀ θ, star (polarPt (-(a/2)) (ρ θ) θ) = polarPt (-(a/2)) (ρ θ) (-θ)) ∧
    (∀ θ, -(star (polarPt (-(a/2)) (ρ θ) θ)) = polarPt (a/2) (ρ θ) (Real.pi - θ)) ∧
    (∀ θ, (polarPt (-(a/2)) (ρ θ) θ).im = ρ θ * Real.sin θ) ∧
    (∀ θ, Real.sin θ = 0 → polarPt (-(a/2)) (ρ θ) θ = ((ρ θ * Real.cos θ - a/2 : ℝ) : ℂ)) ∧
    (∀ θ, polarPt (-(a/2)) (ρ θ) (θ + 2 * Real.pi) = polarPt (-(a/2)) (ρ θ) θ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro θ; exact polarPtReflect_neg _ _ _
  · intro θ
    apply Complex.ext
    · simp only [Complex.neg_re, RCLike.star_def, Complex.conj_re, polarPtReflect_re,
        Real.cos_pi_sub]
      ring
    · simp only [Complex.neg_im, RCLike.star_def, Complex.conj_im, polarPtReflect_im,
        Real.sin_pi_sub]
      ring
  · intro θ; exact polarPtReflect_im _ _ _
  · intro θ h
    rw [polarPtReflect_eq_cos_sin, h]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_inj]
    ring
  · intro θ
    rw [polarPtReflect_eq_cos_sin, polarPtReflect_eq_cos_sin]
    simp [Real.cos_add_two_pi, Real.sin_add_two_pi]

end Work.EQ
