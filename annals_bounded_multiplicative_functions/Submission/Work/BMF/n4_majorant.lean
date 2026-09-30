import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.tuple_setup
import Submission.Work.BMF.tent_char_integral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The rescaled Fejér majorant kernel of the N4 counting argument

`n4w C₀ u = 3 * (sinc (π u / (4 C₀)))²` (with the value `3` at `u = 0`) is a nonnegative
real kernel which is at least `1` on `[-2C₀, 2C₀]` and whose Fourier transform is the
rescaled triangle function `n4W C₀ ξ = 12 C₀ (1 - 4 C₀ |ξ|)₊`.

The key input is `Work.BMF.tent_char_integral`: `∫ x, (1-|x|)₊ e(xξ) dx = sinc (πξ)²`,
combined with the change of variables `ξ ↦ ξ / (4C₀)` for the Lebesgue integral on `ℝ`.
-/

namespace Work.BMF

open MeasureTheory

/-- `n4w C₀` in terms of `Real.sinc` (with `Real.sinc 0 = 1`). -/
lemma n4w_eq_sinc (C₀ : ℝ) (hC₀ : 0 < C₀) (u : ℝ) :
    n4w C₀ u = 3 * (Real.sinc (Real.pi * u / (4 * C₀))) ^ 2 := by
  unfold n4w
  rcases eq_or_ne u 0 with rfl | hu
  · simp [Real.sinc_zero]
  · have hne : Real.pi * u / (4 * C₀) ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero Real.pi_ne_zero hu
      · positivity
    rw [ite_eq_right (by simpa using hu), Real.sinc_of_ne_zero hne]

/-- `n4w C₀` is nonnegative. -/
lemma n4w_nonneg (C₀ u : ℝ) : 0 ≤ n4w C₀ u := by
  unfold n4w
  split_ifs with h
  · norm_num
  · positivity

/-- The numerical input `π² ≤ 12` for the lower bound `1 ≤ n4w C₀`. -/
lemma pi_sq_le_twelve : Real.pi ^ 2 ≤ 12 := by
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

/-- The majorant property: `1 ≤ n4w C₀ u` for `|u| ≤ 2 C₀`. -/
lemma n4w_lower (C₀ u : ℝ) (hC₀ : 0 < C₀) (hu : |u| ≤ 2 * C₀) : 1 ≤ n4w C₀ u := by
  have ha : (0 : ℝ) < 4 * C₀ := by linarith
  rw [n4w_eq_sinc C₀ hC₀ u]
  have harg : Real.pi * u / (4 * C₀) = Real.pi * (u / (4 * C₀)) := by ring
  rw [harg]
  have hv : |u / (4 * C₀)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    linarith
  have hsin : 4 / Real.pi ^ 2 ≤ (Real.sinc (Real.pi * (u / (4 * C₀)))) ^ 2 :=
    tfp.sinc_sq_ge (u / (4 * C₀)) hv
  have h1 : (1 : ℝ) ≤ 3 * (4 / Real.pi ^ 2) := by
    rw [show 3 * (4 / Real.pi ^ 2) = 12 / Real.pi ^ 2 by ring]
    exact (one_le_div (by positivity)).mpr pi_sq_le_twelve
  linarith [hsin, h1, mul_le_mul_of_nonneg_left hsin (by norm_num : (0:ℝ) ≤ 3)]

/-- **Fourier transform of a rescaled triangle function.**  For `a > 0` and reals `c, u`,
`∫ ξ, c · (1 - a|ξ|)₊ · e(ξ u) dξ = (c / a) · (sinc (π u / a)) ^ 2`, where `(x)₊ = max x 0`
and `e(t) = exp (2 * π * I * t) = eC t`.

This is the change of variables `ξ = y / a` (`MeasureTheory.Measure.integral_comp_mul_left`)
applied to `Work.BMF.tent_char_integral`, which is the inverse Fourier transform of the
tent function `y ↦ (1 - |y|)₊`. -/
lemma triangle_integral_scaled (a c u : ℝ) (ha : 0 < a) :
    ∫ ξ : ℝ, ((c * max (1 - a * |ξ|) 0 : ℝ) : ℂ) * eC (ξ * u)
      = ((c / a : ℝ) : ℂ) * ((Real.sinc (Real.pi * u / a)) ^ 2 : ℂ) := by
  -- rewrite the integrand as `c * G (a * ξ)` with `G y = (1 - |y|)₊ e(y (u/a))`
  have hpt : (fun ξ : ℝ => ((c * max (1 - a * |ξ|) 0 : ℝ) : ℂ) * eC (ξ * u))
      = fun ξ : ℝ => (c : ℂ) *
          ((((max 0 (1 - |a * ξ|) : ℝ)) : ℂ) * eC ((a * ξ) * (u / a))) := by
    funext ξ
    have h1 : max (1 - a * |ξ|) 0 = max 0 (1 - |a * ξ|) := by
      rw [abs_mul, abs_of_pos ha, max_comm]
    have h2 : (a * ξ) * (u / a) = ξ * u := by field_simp
    rw [h1, h2]
    push_cast
    ring
  rw [hpt, MeasureTheory.integral_const_mul]
  -- change of variables `ξ ↦ a * ξ` on `ℝ` with Lebesgue measure
  have hscale : (∫ ξ : ℝ, (((max 0 (1 - |a * ξ|) : ℝ)) : ℂ) * eC ((a * ξ) * (u / a)))
      = |a⁻¹| • ∫ y : ℝ, (((max 0 (1 - |y|) : ℝ)) : ℂ) * eC (y * (u / a)) :=
    MeasureTheory.Measure.integral_comp_mul_left
      (fun y : ℝ => (((max 0 (1 - |y|) : ℝ)) : ℂ) * eC (y * (u / a))) a
  rw [hscale, abs_of_pos (inv_pos.mpr ha)]
  -- the tent integral
  have htent : (∫ y : ℝ, (((max 0 (1 - |y|) : ℝ)) : ℂ) * eC (y * (u / a)))
      = ((Real.sinc (Real.pi * (u / a))) ^ 2 : ℂ) := by
    simpa only [eC, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]
      using tent_char_integral (u / a)
  rw [htent, Complex.real_smul]
  have harg : Real.pi * u / a = Real.pi * (u / a) := by ring
  rw [harg]
  push_cast
  ring

/-- **The rescaled Fejér kernel used in the N4 counting argument.**
Here `n4w C₀ u = 3 * (Real.sinc (π * u / (4 * C₀)))²` and `n4W C₀ ξ = 12 * C₀ * (1 - 4 * C₀ * |ξ|)₊`
(the latter defined by `max (1 - 4*C₀*|ξ|) 0`); both are defined in `Submission.Work.BMF.tuple_setup`.
The claim is:
1. `n4w C₀` is nonnegative;
2. `1 ≤ n4w C₀ u` for `|u| ≤ 2*C₀`;
3. the Fourier inversion formula `n4w C₀ u = ∫ ξ, n4W C₀ ξ * exp (2π i ξ u)` for every `u`.

Item 3 is the classical computation that the Fourier transform of the triangular function
`ξ ↦ (1 - |ξ|)₊` is `x ↦ (sin(πx)/(πx))²`: from `(sin x / x) = ∫_{-1/2}^{1/2} e^{2πi x ξ} dξ` one
gets `∫_{-1}^1 (1-|ξ|) e^{-2πi x ξ} dξ = (sin (π x) / (π x))²`, which also follows by two
integrations by parts.  Rescaling gives the stated form.  This is needed to convert the
short-window indicator into an integral over `ξ`. -/
theorem n4_majorant (C₀ : ℝ) (hC₀ : 0 < C₀) :
    (∀ u : ℝ, 0 ≤ n4w C₀ u) ∧
    (∀ u : ℝ, |u| ≤ 2 * C₀ → 1 ≤ n4w C₀ u) ∧
    (∀ u : ℝ, (n4w C₀ u : ℂ) =
      ∫ ξ : ℝ, n4W C₀ ξ * Complex.exp (2 * Real.pi * Complex.I * (ξ * u))) := by
  refine ⟨fun u => n4w_nonneg C₀ u, fun u hu => n4w_lower C₀ u hC₀ hu, fun u => ?_⟩
  -- the Fourier transform of the triangle function `n4W`
  have hscaled0 := triangle_integral_scaled (4 * C₀) (12 * C₀) u (by linarith)
  have hkey : (∫ ξ : ℝ, n4W C₀ ξ * Complex.exp (2 * Real.pi * Complex.I * (ξ * u)))
      = ∫ ξ : ℝ, ((12 * C₀ * max (1 - 4 * C₀ * |ξ|) 0 : ℝ) : ℂ) * eC (ξ * u) := by
    simp only [n4W, eC, Complex.ofReal_mul]
  rw [hkey, hscaled0, n4w_eq_sinc C₀ hC₀ u]
  have h3 : 12 * C₀ / (4 * C₀) = 3 := by
    rw [mul_div_mul_right 12 4 hC₀.ne']; norm_num
  rw [h3]
  push_cast
  ring

end Work.BMF
