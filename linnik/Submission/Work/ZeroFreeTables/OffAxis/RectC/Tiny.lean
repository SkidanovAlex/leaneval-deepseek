/-
# ZeroFreeTables/OffAxis/RectC/Tiny — the tiny window and the HB (9.15) combination

* `Fw_re_nonneg_of_window`: at a test point `s = (1 - λ*/L) + i·Im ρ` and a window of radius
  `δ = λ₁/L` around `1 + i·Im s`, every window summand of HB's Lemma 5.2 window sum is
  *positive*.  For `u` with `‖1 + i·Im s - u‖ ≤ λ₁/L` and `λ₁ ≤ λ*` the complex number
  `z = (s-u) * L` has `Re z ≤ 0` and `|Im z| ≤ λ₁ ≤ 1`, so
  `Re ∫₀^{8/3} e^{-zt} f = ∫₀^{8/3} e^{-Re z · t} cos(Im z · t) f ≥ (1/2)∫₀^{8/3} f = 4/9 > 0`.

* `cheb95_eval`, `cheb95_combination`: HB's Chebyshev inequality (9.15),
  `(3+10x)²(9+10x)² = 14379 + 24480 T₁ + 14900 T₂ + 6000 T₃ + 1250 T₄`, and the resulting
  non-negativity of the combination `14379 K(β,·) + 24480 K(β+iγ,χ) + 14900 K(β+2iγ,χ²)
  + 6000 K(β+3iγ,χ³) + 1250 K(β+4iγ,χ⁴)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72Fc_zero_re

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-! ## The test function `tf72f (3/4)` -/

theorem tf72f_cont34 : ContinuousOn (tf72f (3/4)) (Set.uIcc 0 (8/3)) := by
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 8/3)]
  exact (tf72f_cont (3/4) (by norm_num)).mono (fun t ht => ht.1)

theorem tf72f_nonneg34 : ∀ t : ℝ, 0 ≤ tf72f (3/4) t := tf72f_nonneg (3/4) (by norm_num)

theorem tf72f_supp34 : ∀ t : ℝ, (8:ℝ)/3 ≤ t → tf72f (3/4) t = 0 := by
  intro t ht
  have h : (2:ℝ)/(3/4) = 8/3 := by norm_num
  exact tf72f_supp (3/4) (by norm_num) t (by rw [h]; exact ht)

theorem tf72f_int34 : (∫ t in (0:ℝ)..(8/3), tf72f (3/4) t) = 8/9 := by
  have h := tf72f_intervalIntegral (3/4) (by norm_num)
  rw [show (2:ℝ)/(3/4) = 8/3 by norm_num] at h
  exact h

theorem tf72f_zero34 : tf72f (3/4) 0 = 4/5 := by
  rw [tf72f_at_zero (3/4) (by norm_num)]; norm_num

/-! ## Elementary bounds -/

/-- `cos y ≥ 1/2` for `|y| ≤ 1`. -/
theorem cos_ge_half_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) : (1:ℝ)/2 ≤ Real.cos y := by
  have h := Real.one_sub_sq_div_two_le_cos (x := y)
  have hy2 : y ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg y) hy
  linarith

/-! ## The real-part identity for the Laplace integral -/

/-- The real part of an interval integral is the integral of the real parts. -/
theorem re_intervalIntegral {a b : ℝ} (g : ℝ → ℂ)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    (∫ t in a..b, g t).re = ∫ t in a..b, (g t).re :=
  (intervalIntegral.intervalIntegral_re hg).symm

/-- The real part of `∫₀^{8/3} e^{-zt} f` is the integral of the real part of the kernel. -/
theorem re_laplace (z : ℂ) :
    (∫ t in (0:ℝ)..(8/3),
        Complex.exp (-(z * (t : ℂ))) * ((tf72f (3/4) t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..(8/3),
          Real.exp (-(z.re * t)) * Real.cos (-(z.im * t)) * tf72f (3/4) t := by
  have hcont : ContinuousOn (fun t : ℝ =>
      Complex.exp (-(z * (t : ℂ))) * ((tf72f (3/4) t : ℝ) : ℂ)) (Set.uIcc 0 (8/3)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousOn)
    · exact Complex.continuous_ofReal.comp_continuousOn tf72f_cont34
  rw [re_intervalIntegral _ hcont.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have h1 : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [Complex.mul_re]
  have h2 : (-(z * (t : ℂ))).im = -(z.im * t) := by simp [Complex.mul_im]
  rw [Complex.mul_re, Complex.exp_re, h1, h2, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-! ## The tiny-window positivity -/

/-- **Every window summand is positive at a point of real part `1 - λ*/L`.** -/
theorem Fw_re_nonneg_of_window {L : ℝ} (hL : 1 ≤ L) {lam1 lamstar : ℝ}
    (hlam1 : lam1 ≤ 348/1000) (hstar : lam1 ≤ lamstar) {s u : ℂ}
    (hsre : s.re = 1 - lamstar / L)
    (hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ lam1 / L) :
    0 ≤ (∫ t in (0:ℝ)..(8/3),
            Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((tf72f (3/4) t : ℝ) : ℂ)).re := by
  have hLpos : 0 < L := by linarith
  -- window bounds, cleared of the division by `L`
  have key1 : (1 - u.re) * L ≤ lam1 := by
    have h := Complex.abs_re_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : ((1:ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by simp
    rw [h'] at h
    have h3 : (1 - u.re) ≤ lam1 / L := le_trans (le_abs_self _) (le_trans h hwin)
    have h4 := mul_le_mul_of_nonneg_right h3 hLpos.le
    rwa [div_mul_cancel₀ lam1 hLpos.ne'] at h4
  have key2 : -(lam1) ≤ (1 - u.re) * L := by
    have h := Complex.abs_re_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : ((1:ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by simp
    rw [h'] at h
    have h3 : -(1 - u.re) ≤ lam1 / L := le_trans (neg_le_abs _) (le_trans h hwin)
    have h4 := mul_le_mul_of_nonneg_right h3 hLpos.le
    have h5 : -(1 - u.re) * L = -((1 - u.re) * L) := by ring
    rw [h5, div_mul_cancel₀ lam1 hLpos.ne'] at h4
    linarith
  have key3 : |s.im - u.im| * L ≤ lam1 := by
    have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : ((1:ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
    rw [h'] at h
    have h3 : |s.im - u.im| ≤ lam1 / L := le_trans h hwin
    have h4 := mul_le_mul_of_nonneg_right h3 hLpos.le
    rwa [div_mul_cancel₀ lam1 hLpos.ne'] at h4
  set z : ℂ := (s - u) * L with hz
  have hzre1 : z.re = (s.re - u.re) * L := by simp [hz, Complex.mul_re]
  have hzre : z.re = (1 - u.re) * L - lamstar := by
    rw [hzre1]
    have h2 : s.re - u.re = (1 - u.re) - lamstar / L := by rw [hsre]; ring
    rw [h2, sub_mul, div_mul_cancel₀ lamstar hLpos.ne']
  have hzim : z.im = (s.im - u.im) * L := by simp [hz, Complex.mul_im]
  have hzre_le : z.re ≤ 0 := by rw [hzre]; linarith
  have hzim_abs : |z.im| ≤ 348/1000 := by
    rw [hzim, abs_mul, abs_of_nonneg hLpos.le]
    linarith
  rw [re_laplace z]
  have hcontg : ContinuousOn (fun t : ℝ =>
      Real.exp (-(z.re * t)) * Real.cos (-(z.im * t)) * tf72f (3/4) t) (Set.uIcc 0 (8/3)) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id).neg).continuousOn
    · exact tf72f_cont34
  have hcont1 : ContinuousOn (fun t : ℝ => (1/2 : ℝ) * tf72f (3/4) t) (Set.uIcc 0 (8/3)) :=
    continuousOn_const.mul tf72f_cont34
  have hmono : (∫ t in (0:ℝ)..(8/3), (1/2 : ℝ) * tf72f (3/4) t)
      ≤ ∫ t in (0:ℝ)..(8/3),
          Real.exp (-(z.re * t)) * Real.cos (-(z.im * t)) * tf72f (3/4) t := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 8/3)
      hcont1.intervalIntegrable hcontg.intervalIntegrable
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht3 : t ≤ 8/3 := ht.2
    have hexp : (1:ℝ) ≤ Real.exp (-(z.re * t)) := by
      rw [Real.one_le_exp_iff]
      nlinarith [hzre_le, ht0]
    have hcos : (1:ℝ)/2 ≤ Real.cos (-(z.im * t)) := by
      apply cos_ge_half_of_abs_le_one
      rw [abs_neg, abs_mul, abs_of_nonneg ht0]
      nlinarith [hzim_abs, ht3]
    have hf : 0 ≤ tf72f (3/4) t := tf72f_nonneg34 t
    have hcf : 0 ≤ Real.cos (-(z.im * t)) * tf72f (3/4) t := mul_nonneg (by linarith) hf
    have h1 : (1/2 : ℝ) * tf72f (3/4) t ≤ Real.cos (-(z.im * t)) * tf72f (3/4) t :=
      mul_le_mul_of_nonneg_right hcos hf
    have h2 : Real.cos (-(z.im * t)) * tf72f (3/4) t ≤
        Real.exp (-(z.re * t)) * Real.cos (-(z.im * t)) * tf72f (3/4) t := by
      rw [mul_assoc]
      simpa using mul_le_mul_of_nonneg_right hexp hcf
    linarith
  have hval : (∫ t in (0:ℝ)..(8/3), (1/2 : ℝ) * tf72f (3/4) t) = 4/9 := by
    rw [intervalIntegral.integral_const_mul, tf72f_int34]; norm_num
  linarith [hmono, hval]

/-! ## HB's (9.15) combination -/

/-- HB's Chebyshev inequality (9.15): `(3+10x)²(9+10x)²` in the Chebyshev basis. -/
theorem cheb95_eval (x : ℝ) :
    14379 + 24480 * x + 14900 * (2 * x ^ 2 - 1) + 6000 * (4 * x ^ 3 - 3 * x)
      + 1250 * (8 * x ^ 4 - 8 * x ^ 2 + 1) = (3 + 10 * x) ^ 2 * (9 + 10 * x) ^ 2 := by
  ring

theorem cheb_T_three :
    (Polynomial.Chebyshev.T ℝ (3 : ℤ)) =
      2 * Polynomial.X * Polynomial.Chebyshev.T ℝ (2 : ℤ) - Polynomial.Chebyshev.T ℝ (1 : ℤ) := by
  have h := Polynomial.Chebyshev.T_add_two (R := ℝ) 1
  simpa using h

theorem cheb_T_four :
    (Polynomial.Chebyshev.T ℝ (4 : ℤ)) =
      2 * Polynomial.X * Polynomial.Chebyshev.T ℝ (3 : ℤ) - Polynomial.Chebyshev.T ℝ (2 : ℤ) := by
  have h := Polynomial.Chebyshev.T_add_two (R := ℝ) 2
  simpa using h

/-- The Chebyshev coefficients of HB's (9.15) polynomial. -/
def c95 : ℕ → ℝ := fun k =>
  if k = 0 then 14379 else if k = 1 then 24480 else if k = 2 then 14900
    else if k = 3 then 6000 else if k = 4 then 1250 else 0

/-- **HB's (9.15) combination of `K`-sums.** -/
theorem cheb95_combination {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β γ : ℝ} (hL : 0 < L) (hx₀ : 0 ≤ x₀) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (χ : DirichletCharacter ℂ q) :
    0 ≤ 14379 * Ksum q f L (β : ℂ) 1
      + 24480 * Ksum q f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
      + 14900 * Ksum q f L ((β : ℂ) + 2 * (γ : ℂ) * Complex.I) (χ ^ 2)
      + 6000 * Ksum q f L ((β : ℂ) + 3 * (γ : ℂ) * Complex.I) (χ ^ 3)
      + 1250 * Ksum q f L ((β : ℂ) + 4 * (γ : ℂ) * Complex.I) (χ ^ 4) := by
  have e0 : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ (0 : ℤ)).eval y = 1 := by
    intro y; rw [Polynomial.Chebyshev.T_zero]; simp
  have e1 : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ (1 : ℤ)).eval y = y := by
    intro y; rw [Polynomial.Chebyshev.T_one]; simp
  have e2 : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ (2 : ℤ)).eval y = 2 * y ^ 2 - 1 := by
    intro y; rw [Polynomial.Chebyshev.T_two]; simp
  have e3 : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ (3 : ℤ)).eval y = 4 * y ^ 3 - 3 * y := by
    intro y
    rw [cheb_T_three]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      ← Polynomial.C_eq_natCast, Polynomial.eval_C, e2 y, e1 y]
    norm_num
    ring
  have e4 : ∀ y : ℝ, (Polynomial.Chebyshev.T ℝ (4 : ℤ)).eval y = 8 * y ^ 4 - 8 * y ^ 2 + 1 := by
    intro y
    rw [cheb_T_four]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      ← Polynomial.C_eq_natCast, Polynomial.eval_C, e3 y, e2 y]
    norm_num
    ring
  have hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ ∑ k ∈ Finset.range (4 + 1), c95 k *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x := by
    intro x _
    have hsum : ∑ k ∈ Finset.range (4 + 1), c95 k *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x
        = 14379 + 24480 * x + 14900 * (2 * x ^ 2 - 1) + 6000 * (4 * x ^ 3 - 3 * x)
          + 1250 * (8 * x ^ 4 - 8 * x ^ 2 + 1) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, c95]
      norm_num
      rw [e2 x, e3 x, e4 x]
    rw [hsum, cheb95_eval]
    positivity
  have hmain := ksum_trigPoly_nonneg (β := β) (γ := γ) hf hL hx₀ hsupp hP χ
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c95, pow_zero, pow_one, pow_two] at hmain
  push_cast at hmain
  norm_num at hmain
  simpa only [← pow_two] using hmain

end Work.ZeroFreeTables.OffAxis
