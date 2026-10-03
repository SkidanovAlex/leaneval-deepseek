import Mathlib

namespace Work.FIArea5.S16

open MeasureTheory Complex Real Filter
open scoped FourierTransform

/-- Integrability of a polynomial multiple of a shifted Gaussian with complex quadratic
exponent: for `re B > 0`, the function `x ↦ x^n · exp (-B x² + C x + D)` (with `x` viewed in `ℂ`)
is integrable on `ℝ`. -/
lemma integrable_pow_mul_cexp_quadratic {B C D : ℂ} (hB : 0 < B.re) (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * Complex.exp (-B * (x : ℂ) ^ 2 + C * (x : ℂ) + D)) := by
  set r : ℝ := B.re / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hnat : (-1 : ℝ) < (n : ℝ) := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hbase : Integrable (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-r * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hrpos hnat
  have hbase' : Integrable (fun x : ℝ => |x| ^ n * Real.exp (-r * x ^ 2)) := by
    refine (hbase.norm).congr ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le, Real.rpow_natCast, abs_pow]
  have hdom : Integrable (fun x : ℝ => Real.exp (C.re ^ 2 / (2 * B.re) + D.re) *
      (|x| ^ n * Real.exp (-r * x ^ 2))) := hbase'.const_mul _
  refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall (fun x => ?_))
  · fun_prop
  · have h1 : ‖(x : ℂ) ^ n * Complex.exp (-B * (x : ℂ) ^ 2 + C * (x : ℂ) + D)‖
        = |x| ^ n * Real.exp (-B.re * x ^ 2 + C.re * x + D.re) := by
      rw [norm_mul, norm_pow, Complex.norm_exp]
      simp [Complex.add_re, Complex.mul_re, Complex.neg_re, ← Complex.ofReal_pow,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [h1]
    have hsplit : Real.exp (-B.re * x ^ 2 + C.re * x + D.re)
        = Real.exp (-r * x ^ 2) * Real.exp (-r * x ^ 2 + C.re * x + D.re) := by
      rw [← Real.exp_add]; congr 1; rw [hr]; ring
    rw [hsplit]
    have hle : Real.exp (-r * x ^ 2 + C.re * x + D.re) ≤ Real.exp (C.re ^ 2 / (2 * B.re) + D.re) := by
      apply Real.exp_le_exp.mpr
      have hkey : C.re ^ 2 / (2 * B.re) + D.re - (-r * x ^ 2 + C.re * x + D.re)
          = (B.re * x - C.re) ^ 2 / (2 * B.re) := by
        rw [hr]; field_simp; ring
      have hpos : (0:ℝ) ≤ (B.re * x - C.re) ^ 2 / (2 * B.re) := by positivity
      linarith
    calc |x| ^ n * (Real.exp (-r * x ^ 2) * Real.exp (-r * x ^ 2 + C.re * x + D.re))
        = (|x| ^ n * Real.exp (-r * x ^ 2)) * Real.exp (-r * x ^ 2 + C.re * x + D.re) := by ring
      _ ≤ (|x| ^ n * Real.exp (-r * x ^ 2)) * Real.exp (C.re ^ 2 / (2 * B.re) + D.re) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = Real.exp (C.re ^ 2 / (2 * B.re) + D.re) * (|x| ^ n * Real.exp (-r * x ^ 2)) := by ring

/-- For an entire `F : ℂ → ℂ`, the `n`-th derivative of the restriction of `F` to `ℝ` at `x`
agrees with the `n`-th complex derivative of `F` at `x`. -/
lemma iteratedDeriv_ofReal_eq {F : ℂ → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => F (y : ℂ)) x = iteratedDeriv n F (x : ℂ) := by
  have hne : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hG : ContDiff ℂ (⊤ : ℕ∞) (iteratedDeriv n F) := by
      rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv n hF
    have hfun : (iteratedDeriv n (fun y : ℝ => F ↑y)) = fun y : ℝ => iteratedDeriv n F ↑y := by
      funext y; exact ih y
    rw [hfun]
    exact (((hG.differentiable hne).differentiableAt.hasDerivAt).comp_ofReal).deriv

/-- **Fourier transform of a polynomially weighted shifted Gaussian.**

For `re a > 0`, `k : ℕ`, and complex shift `b`, the Fourier transform (Mathlib's
`FourierTransform.fourier`, `𝓕 f ξ = ∫ f x * exp (-2πi x ξ)`) of `x ↦ x^k e^{-π a x² + 2π b x}` is
`(i/2π)^k = (1/(-2πi))^k` times the `k`-th derivative of the Gaussian Fourier transform
`w ↦ a^{-1/2} e^{-(π/a)(w + i b)²}`.

Indeed `𝓕(x ↦ e^{-πax²+2πbx})` is Mathlib's `fourier_gaussian_pi'`, and since
`d/dξ (𝓕f)(ξ) = -2πi·𝓕(x f)(ξ)` one has `𝓕(x ↦ x^k f) = (1/(-2πi))^k (𝓕f)^{(k)}`.  (Note the sign:
`(1/(2πi))^k` would be wrong for odd `k`.) -/
theorem fourier_gaussian_poly (k : ℕ) {a : ℂ} (ha : 0 < a.re) (b : ℂ) (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ k) *
        Complex.exp (-Real.pi * a * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ))) ξ
      = (Complex.I / (2 * Real.pi)) ^ k *
        iteratedDeriv k (fun w : ℂ =>
          (1 / a ^ (1 / 2 : ℂ)) * Complex.exp (-Real.pi / a * (w + Complex.I * b) ^ 2)) (ξ : ℂ) := by
  set F : ℂ → ℂ := fun w =>
    (1 / a ^ (1 / 2 : ℂ)) * Complex.exp (-Real.pi / a * (w + Complex.I * b) ^ 2) with hFdef
  set g : ℝ → ℂ := fun x => Complex.exp (-Real.pi * a * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ))
    with hgdef
  have hF : ContDiff ℂ (⊤ : ℕ∞) F := by rw [hFdef]; fun_prop
  have hgauss : FourierTransform.fourier g = fun t : ℝ => F (t : ℂ) := by
    rw [hgdef, hFdef]
    simpa using fourier_gaussian_pi' ha b
  have hBa : 0 < (Real.pi * a).re := by
    rw [Complex.mul_re]; simp; exact mul_pos Real.pi_pos ha
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (fun x : ℝ => x ^ n • g x) := by
    intro n _
    have hEq : (fun x : ℝ => x ^ n • g x) = fun x : ℝ =>
        (x : ℂ) ^ n * Complex.exp (-(Real.pi * a) * (x : ℂ) ^ 2 + (2 * Real.pi * b) * (x : ℂ) + 0) := by
      funext x
      simp only [hgdef]
      rw [show (-Real.pi * a * (x : ℂ) ^ 2 + 2 * Real.pi * b * (x : ℂ)) =
          (-(Real.pi * a) * (x : ℂ) ^ 2 + (2 * Real.pi * b) * (x : ℂ) + 0) from by ring]
      rw [Complex.real_smul, Complex.ofReal_pow]
    rw [hEq]
    exact integrable_pow_mul_cexp_quadratic hBa n
  have hmain : iteratedDeriv k (FourierTransform.fourier g)
      = FourierTransform.fourier (fun x : ℝ => (-2 * ↑Real.pi * Complex.I * ↑x) ^ k • g x) :=
    iteratedDeriv_fourier (f := g) hint le_rfl
  have hL : iteratedDeriv k (FourierTransform.fourier g) ξ = iteratedDeriv k F (ξ : ℂ) := by
    rw [hgauss]
    exact iteratedDeriv_ofReal_eq hF k ξ
  have hR : FourierTransform.fourier (fun x : ℝ => (-2 * ↑Real.pi * Complex.I * ↑x) ^ k • g x) ξ
      = (-2 * ↑Real.pi * Complex.I) ^ k *
        FourierTransform.fourier (fun x : ℝ => (↑x : ℂ) ^ k • g x) ξ := by
    have hfun : (fun x : ℝ => (-2 * ↑Real.pi * Complex.I * ↑x) ^ k • g x)
        = (-2 * ↑Real.pi * Complex.I) ^ k • (fun x : ℝ => (↑x : ℂ) ^ k • g x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_pow]
      ring
    rw [hfun]
    have hs : FourierTransform.fourier (((-2:ℂ) * ↑Real.pi * Complex.I) ^ k •
        (fun x : ℝ => (↑x : ℂ) ^ k • g x))
        = ((-2:ℂ) * ↑Real.pi * Complex.I) ^ k •
          FourierTransform.fourier (fun x : ℝ => (↑x : ℂ) ^ k • g x) :=
      VectorFourier.fourierIntegral_const_smul fourierChar volume (innerₗ ℝ) _ _
    rw [hs]
    rfl
  have hkey : iteratedDeriv k F (ξ : ℂ) = (-2 * ↑Real.pi * Complex.I) ^ k *
      FourierTransform.fourier (fun x : ℝ => (↑x : ℂ) ^ k • g x) ξ := by
    rw [← hL, hmain, hR]
  have hfun2 : (fun x : ℝ => (↑x : ℂ) ^ k * Complex.exp (-Real.pi * a * (↑x) ^ 2 + 2 * Real.pi * b * ↑x))
      = fun x : ℝ => (↑x : ℂ) ^ k • g x := by
    funext x; simp [hgdef]
  rw [hfun2, hkey]
  have hone : (Complex.I / (2 * ↑Real.pi)) * (-2 * ↑Real.pi * Complex.I) = 1 := by
    field_simp
    ring_nf
    simp
  rw [← mul_assoc, ← mul_pow, hone, one_pow, one_mul]

end Work.FIArea5.S16
