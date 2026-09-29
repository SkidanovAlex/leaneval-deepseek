import Mathlib

/-!
# Analyticity of an exponentially dominated Fourier series

Given coefficients `d k` decaying like `D * exp (-(η * |k|))` for some `η > 0`, the
Fourier series

`w ↦ ∑' k : ℤ, d k * exp (2 * Real.pi * Complex.I * k * w)`

converges and is holomorphic on the open strip `{w : ℂ | 2 * Real.pi * |w.im| < η}`.

The proof is the standard Weierstrass / dominated-convergence argument: on each compact
sub-strip `|z.im| ≤ c` with `2 * Real.pi * c < η`, the general term is dominated by the
summable geometric series `D * exp (-((η - 2πc) * |k|))`, and each term is entire.
-/

namespace Work.TMComp.RedProj.Part2

/-- The dominating series `∑_k D * exp (-(c * |k|))` converges for `c > 0`. -/
private lemma summable_int_exp_neg_mul (D c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℤ => D * Real.exp (-(c * |(k : ℝ)|))) := by
  have hnat : Summable (fun n : ℕ => Real.exp (-(c * (n : ℝ)))) := by
    have h := (Real.summable_exp_nat_mul_iff (a := -c)).mpr (by linarith : -c < 0)
    refine h.congr fun n => ?_
    rw [show (n : ℝ) * -c = -(c * (n : ℝ)) by ring]
  have hint : Summable (fun k : ℤ => Real.exp (-(c * |(k : ℝ)|))) := by
    apply Summable.of_nat_of_neg (f := fun k : ℤ => Real.exp (-(c * |(k : ℝ)|)))
    · simpa using hnat
    · simpa using hnat
  exact Summable.mul_left D hint

/-- The real part of the exponent `2πi k z`. -/
private lemma exp_two_pi_I_mul_re (k : ℤ) (z : ℂ) :
    (2 * Real.pi * Complex.I * (k : ℂ) * z).re = -(2 * Real.pi * (k : ℝ) * z.im) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]

/-- Each Fourier mode `w ↦ d k * exp (2πi k w)` is entire. -/
private lemma differentiable_fourier_term (d : ℤ → ℂ) (k : ℤ) :
    Differentiable ℂ (fun w : ℂ => d k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)) := by
  have h1 : Differentiable ℂ (fun w : ℂ => 2 * Real.pi * Complex.I * (k : ℂ) * w) := by fun_prop
  exact (Complex.differentiable_exp.comp h1).const_mul (d k)

/-- Pointwise domination of the `k`-th term on the strip `|z.im| < c`. -/
private lemma norm_fourier_term_le (d : ℤ → ℂ) (η D c : ℝ) (hD : 0 ≤ D)
    (hd : ∀ k : ℤ, ‖d k‖ ≤ D * Real.exp (-(η * |(k : ℝ)|)))
    (k : ℤ) (z : ℂ) (hz : |z.im| < c) :
    ‖d k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * z)‖
      ≤ D * Real.exp (-((η - 2 * Real.pi * c) * |(k : ℝ)|)) := by
  have hnorm : ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * z)‖
      = Real.exp (-(2 * Real.pi * (k : ℝ) * z.im)) := by
    rw [Complex.norm_exp, exp_two_pi_I_mul_re]
  rw [norm_mul, hnorm]
  have h_exp : Real.exp (-(2 * Real.pi * (k : ℝ) * z.im))
      ≤ Real.exp (2 * Real.pi * c * |(k : ℝ)|) := by
    apply Real.exp_le_exp.mpr
    have hA : 0 ≤ 2 * Real.pi * |(k : ℝ)| := by positivity
    have h1 : -(2 * Real.pi * (k : ℝ) * z.im) ≤ 2 * Real.pi * |(k : ℝ)| * |z.im| := by
      have h2 : -(2 * Real.pi * (k : ℝ) * z.im) = 2 * Real.pi * (-((k : ℝ) * z.im)) := by
        ring
      rw [h2]
      calc 2 * Real.pi * (-((k : ℝ) * z.im))
          ≤ 2 * Real.pi * |(k : ℝ) * z.im| :=
            mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
        _ = 2 * Real.pi * |(k : ℝ)| * |z.im| := by rw [abs_mul]; ring
    refine le_trans h1 ?_
    calc 2 * Real.pi * |(k : ℝ)| * |z.im| ≤ 2 * Real.pi * |(k : ℝ)| * c :=
          mul_le_mul_of_nonneg_left (le_of_lt hz) hA
      _ = 2 * Real.pi * c * |(k : ℝ)| := by ring
  calc ‖d k‖ * Real.exp (-(2 * Real.pi * (k : ℝ) * z.im))
      ≤ (D * Real.exp (-(η * |(k : ℝ)|))) * Real.exp (2 * Real.pi * c * |(k : ℝ)|) :=
        mul_le_mul (hd k) h_exp (Real.exp_pos _).le (mul_nonneg hD (Real.exp_pos _).le)
    _ = D * Real.exp (-((η - 2 * Real.pi * c) * |(k : ℝ)|)) := by
        rw [mul_assoc, ← Real.exp_add,
          show -(η * |(k : ℝ)|) + 2 * Real.pi * c * |(k : ℝ)|
              = -((η - 2 * Real.pi * c) * |(k : ℝ)|) by ring]

/-- The Fourier series is holomorphic on any sub-strip `|z.im| < c` with `2πc < η`. -/
private theorem differentiableOn_tsum_fourier_strip (d : ℤ → ℂ) (η D c : ℝ)
    (hc : 2 * Real.pi * c < η)
    (hd : ∀ k : ℤ, ‖d k‖ ≤ D * Real.exp (-(η * |(k : ℝ)|))) :
    DifferentiableOn ℂ
      (fun w : ℂ => ∑' k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w))
      {z : ℂ | |z.im| < c} := by
  have hη' : (0 : ℝ) < η - 2 * Real.pi * c := by linarith
  have hD : 0 ≤ D := by
    have h0 : ‖d 0‖ ≤ D := by simpa using hd 0
    linarith [norm_nonneg (d 0)]
  have hUopen : IsOpen {z : ℂ | |z.im| < c} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact Complex.differentiableOn_tsum_of_summable_norm
    (u := fun k : ℤ => D * Real.exp (-((η - 2 * Real.pi * c) * |(k : ℝ)|)))
    (F := fun (k : ℤ) (w : ℂ) => d k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w))
    (summable_int_exp_neg_mul D (η - 2 * Real.pi * c) hη')
    (fun k => (differentiable_fourier_term d k).differentiableOn)
    hUopen
    (fun k z hz => norm_fourier_term_le d η D c hD hd k z hz)

theorem AnalyticTsumFourier (d : ℤ → ℂ) (η D : ℝ) (hη : 0 < η)
    (hd : ∀ k : ℤ, ‖d k‖ ≤ D * Real.exp (-(η * |(k : ℝ)|))) :
    AnalyticOnNhd ℂ
      (fun w : ℂ => ∑' k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w))
      {w : ℂ | 2 * Real.pi * |w.im| < η} := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  intro w hw
  have hwlt : |w.im| < η / (2 * Real.pi) := by
    rw [lt_div_iff₀ h2pi]
    calc |w.im| * (2 * Real.pi) = 2 * Real.pi * |w.im| := by ring
      _ < η := hw
  set c : ℝ := (|w.im| + η / (2 * Real.pi)) / 2 with hc
  have hclt : |w.im| < c := by rw [hc]; linarith
  have hcgt : c < η / (2 * Real.pi) := by rw [hc]; linarith
  have h2pic : 2 * Real.pi * c < η := by
    have h := mul_lt_mul_of_pos_left hcgt h2pi
    rwa [mul_div_cancel₀ η h2pi.ne'] at h
  have hUopen : IsOpen {z : ℂ | |z.im| < c} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact (differentiableOn_tsum_fourier_strip d η D c h2pic hd).analyticAt
    (hUopen.mem_nhds hclt)

end Work.TMComp.RedProj.Part2
