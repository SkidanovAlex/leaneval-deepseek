import Mathlib
import Submission.Work.RPV.Defs

/-!
# The chord through the two points `e^{i(t±r)}` lies on the standard zero section

For the unit circle, the chord joining `e^{i(t+r)}` and `e^{i(t-r)}` has midpoint with
argument `t` and half-length `cos r` (its endpoints subtend the angle `2r` at the origin).
Lifting the chord with phase `a = t + π/2` (the direction of the chord is rotated by `π/2`
from the midpoint direction), the reduced coordinate `u = e^{-ia}(z+w)/√2` becomes purely
imaginary:
`u = -√2 cos r · i`.

Hence `chordPS z w a` agrees with the point `stdZ (-(√2 cos r)) a` of the zero section
with coordinate `-(√2 cos r)` at angle `a`.
-/

open Complex Real

namespace Work.RPV

/-- `2/√2 = √2`. -/
private lemma sqrt2_div_two : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_eq_iff (by positivity : Real.sqrt 2 ≠ 0)]
  linarith

/-- `e^{i(a+b)} = e^{ia} · e^{ib}` for real phases. -/
private lemma exp_ofReal_mul_I_add (a b : ℝ) :
    Complex.exp ((a + b : ℝ) * I) = Complex.exp ((a : ℂ) * I) * Complex.exp ((b : ℂ) * I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `e^{ir} + e^{-ir} = 2 cos r`. -/
private lemma exp_mul_I_add_exp_neg (r : ℝ) :
    Complex.exp ((r : ℂ) * I) + Complex.exp (-((r : ℂ) * I)) = ((2 * Real.cos r : ℝ) : ℂ) := by
  have h : -((r : ℂ) * I) = (starRingEnd ℂ) ((r : ℂ) * I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [h, Complex.exp_conj, Complex.add_conj]
  congr 1
  rw [Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re]

/-- `e^{-i(t+π/2)} = e^{-it} · (−i)`. -/
private lemma exp_neg_add_pi_div_two_mul_I (t : ℝ) :
    Complex.exp (-((t + π / 2 : ℝ) : ℂ) * I) =
      Complex.exp (-((t : ℂ) * I)) * (-Complex.I) := by
  have h : -((t + π / 2 : ℝ) : ℂ) * I = -((t : ℂ) * I) + (((-(π / 2) : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

/-- The reduced coordinate of the chord `(e^{i(t+r)}, e^{i(t-r)})` at phase `t + π/2` is
`-√2 cos r · i`. -/
private lemma chordPS_circle_stdZ_aux (t r : ℝ) :
    Complex.exp (-(((t + π / 2) : ℝ) : ℂ) * I) *
      ((Complex.exp ((t + r : ℝ) * I) + Complex.exp ((t - r : ℝ) * I)) / (Real.sqrt 2 : ℂ))
      = -(((Real.sqrt 2 * Real.cos r : ℝ)) : ℂ) * I := by
  have hz : Complex.exp ((t + r : ℝ) * I) = Complex.exp ((t : ℂ) * I) * Complex.exp ((r : ℂ) * I) :=
    exp_ofReal_mul_I_add t r
  have hw : Complex.exp ((t - r : ℝ) * I)
      = Complex.exp ((t : ℂ) * I) * Complex.exp (-((r : ℂ) * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hzw : Complex.exp ((t + r : ℝ) * I) + Complex.exp ((t - r : ℝ) * I)
      = Complex.exp ((t : ℂ) * I) * ((2 * Real.cos r : ℝ) : ℂ) := by
    rw [hz, hw, ← mul_add, exp_mul_I_add_exp_neg]
  rw [hzw, exp_neg_add_pi_div_two_mul_I, Complex.exp_neg]
  rw [mul_div_assoc, ← Complex.ofReal_div]
  have hcr : (2 * Real.cos r) / Real.sqrt 2 = Real.sqrt 2 * Real.cos r := by
    rw [← div_mul_eq_mul_div, sqrt2_div_two]
  rw [hcr]
  have hE : (Complex.exp ((t : ℂ) * I))⁻¹ * Complex.exp ((t : ℂ) * I) = 1 :=
    inv_mul_cancel₀ (Complex.exp_ne_zero _)
  rw [show (Complex.exp ((t : ℂ) * I))⁻¹ * (-Complex.I) *
        (Complex.exp ((t : ℂ) * I) * ↑(Real.sqrt 2 * Real.cos r))
      = ↑(Real.sqrt 2 * Real.cos r) * (-Complex.I) *
        ((Complex.exp ((t : ℂ) * I))⁻¹ * Complex.exp ((t : ℂ) * I)) from by ring,
    hE, mul_one]
  ring

theorem chordPS_circle_stdZ (t r : ℝ) :
    Work.RPV.chordPS (Complex.exp ((t + r : ℝ) * I)) (Complex.exp ((t - r : ℝ) * I)) (t + π / 2)
      = Work.RPV.stdZ (-(Real.sqrt 2 * Real.cos r)) (t + π / 2) := by
  simp only [Work.RPV.chordPS, Work.RPV.stdZ]
  rw [chordPS_circle_stdZ_aux]
  apply Prod.ext
  · apply Prod.ext
    · simp [Complex.cos_ofReal_re]
    · rfl
  · apply Prod.ext
    · simp
    · rw [Complex.norm_exp, Complex.norm_exp]; simp

end Work.RPV
