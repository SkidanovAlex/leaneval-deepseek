import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Commons.Analysis.Integral.norm_intervalIntegral_mul_le

open MeasureTheory

namespace Commons.Analysis.Integral

theorem norm_intervalIntegral_mul_le_gen {F Φ : ℂ → ℂ} {M : ℝ} (hM : 0 < M) {A B : ℝ} (hAB : A ≤ B)
    (hΦ : ∀ u : ℂ, u.re ≤ B → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2))
    {v : ℝ} (hv : 1 ≤ |v|)
    (hint : IntervalIntegrable (fun x : ℝ => ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) volume A B)
    (hint2 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I)) volume A B) :
    ‖(∫ x : ℝ in A..B, F ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I))‖ ≤
      (M / (1 + v ^ 2)) * (∫ x : ℝ in A..B, ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) := by
  -- the real and imaginary parts of the point x + v·i
  have hure : ∀ x : ℝ, ((x : ℂ) + (v : ℂ) * Complex.I).re = x := by
    intro x; simp [Complex.add_re]
  have huim : ∀ x : ℝ, ((x : ℂ) + (v : ℂ) * Complex.I).im = v := by
    intro x; simp [Complex.add_im]
  have hnorm_sq : ∀ x : ℝ, ‖((x : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 = x ^ 2 + v ^ 2 := by
    intro x
    rw [Complex.sq_norm, Complex.normSq_apply, hure x, huim x]
    ring
  -- pointwise bound on Φ along the vertical line
  have hΦbound : ∀ x : ℝ, x ≤ B → ‖Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤ M / (1 + v ^ 2) := by
    intro x hx
    have h1 : ‖Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖
        ≤ M / (1 + ‖((x : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2) :=
      hΦ _ (by rw [hure x]; exact hx)
    have hden : (1 : ℝ) + v ^ 2 ≤ 1 + ‖((x : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 := by
      have := hnorm_sq x; nlinarith [sq_nonneg x]
    have hpos : (0 : ℝ) < 1 + v ^ 2 := by nlinarith [sq_nonneg v]
    exact h1.trans (div_le_div_of_nonneg_left hM.le hpos hden)
  have hint3 : IntervalIntegrable
      (fun x : ℝ => (M / (1 + v ^ 2)) * ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) volume A B :=
    hint.const_mul _
  have hint2n : IntervalIntegrable
      (fun x : ℝ => ‖F ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖)
      volume A B :=
    hint2.norm
  calc ‖(∫ x : ℝ in A..B, F ((x : ℂ) + (v : ℂ) * Complex.I) *
          Φ ((x : ℂ) + (v : ℂ) * Complex.I))‖
      ≤ ∫ x : ℝ in A..B,
          ‖F ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hAB
    _ ≤ ∫ x : ℝ in A..B,
          (M / (1 + v ^ 2)) * ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖ := by
        apply intervalIntegral.integral_mono_on hAB hint2n hint3
        intro x hx
        rw [norm_mul]
        have := mul_le_mul_of_nonneg_left (hΦbound x hx.2)
          (norm_nonneg (F ((x : ℂ) + (v : ℂ) * Complex.I)))
        simpa [mul_comm] using this
    _ = (M / (1 + v ^ 2)) *
          (∫ x : ℝ in A..B, ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) :=
        intervalIntegral.integral_const_mul (M / (1 + v ^ 2))
          (fun x : ℝ => ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖)

end Commons.Analysis.Integral