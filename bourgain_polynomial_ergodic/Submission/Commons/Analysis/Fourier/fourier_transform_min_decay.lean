import Mathlib
import Submission.Commons.Analysis.Calculus.integral_second_difference_le_sq
import Submission.Commons.Analysis.Fourier.fourier_second_difference_identity
import Submission.Commons.Analysis.Complex.tendsto_exp_two_pi_I_mul_sub_one_div

/-!
# Sharp pointwise Fourier decay from an `L¹` bound on the second derivative

If `m : ℝ → ℂ` and its second derivative are integrable then the Fourier transform of `m`
satisfies `‖𝓕 m t‖ ≤ min (∫ ‖m‖) ((∫ ‖m''‖) / (2π|t|)²)` for every `t ≠ 0`.

The density bound is the trivial estimate.  For the decay bound we use the second finite
difference identity
`∫ e^{-2πitx} (m x - 2 m (x+h) + m (x+2h)) = (e^{2πith} - 1)² 𝓕 m t`
together with the sharp `L¹` second-difference estimate `‖Δ_h² m‖₁ ≤ h² ‖m''‖₁`, and let
`h → 0⁺`: since `|e^{2πith} - 1| ~ 2π|t| h`, this produces the exact constant `(2π|t|)⁻²`
without any hypothesis on the behaviour of `m` at infinity.
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Filter
open scoped FourierTransform Topology

/-- The Fourier kernel `x ↦ e^{-2πi t x}` as a function of `x`. -/
private noncomputable def fourierKernel (t x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * t * x))

/-- The Fourier transform of `m` is the integral against the kernel `fourierKernel t`. -/
private lemma fourier_eq_kernel (m : ℝ → ℂ) (t : ℝ) :
    FourierTransform.fourier m t = ∫ x, fourierKernel t x * m x := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  rw [show fourierKernel t x = Complex.exp (-(2 * Real.pi * Complex.I * t * x)) from rfl]
  congr 1
  rw [Real.inner_apply]
  push_cast
  ring

private lemma fourierKernel_norm (t x : ℝ) : ‖fourierKernel t x‖ = 1 := by
  rw [fourierKernel, show -(2 * Real.pi * Complex.I * t * x)
        = ((-(2*Real.pi*t*x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The trivial (frequency zero) bound `‖𝓕 m t‖ ≤ ∫ ‖m‖`. -/
private lemma fourier_norm_le (m : ℝ → ℂ) (t : ℝ) :
    ‖FourierTransform.fourier m t‖ ≤ ∫ x, ‖m x‖ := by
  rw [fourier_eq_kernel]
  calc ‖∫ x, fourierKernel t x * m x‖ ≤ ∫ x, ‖fourierKernel t x * m x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖m x‖ := by
        apply integral_congr_ae; filter_upwards with x
        rw [norm_mul, fourierKernel_norm, one_mul]

/-- The complex slope limit `h ↦ (e^{2πith} - 1)/h → 2πit` as `h → 0⁺`; this encodes
`|e^{2πith} - 1| ~ 2π|t| |h|` and hence the exact constant `(2π|t|)⁻²`. -/
private lemma tendsto_exp_slope (t : ℝ) :
    Tendsto (fun h : ℝ => (Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi * Complex.I * t)) :=
  (Commons.Analysis.Complex.tendsto_exp_two_pi_I_mul_sub_one_div t).mono_left
    (nhdsGT_le_nhdsNE 0)

private lemma norm_two_pi_I_mul (t : ℝ) : ‖2 * Real.pi * Complex.I * t‖ = 2 * Real.pi * |t| := by
  rw [show (2 * Real.pi * Complex.I * t) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

private lemma mul_norm_div_pow_mul_self (z : ℝ) (w : ℂ) {h : ℝ} (hh : h ≠ 0) :
    z * ‖w / h‖ ^ 2 * h ^ 2 = z * ‖w‖ ^ 2 := by
  have hh2 : ‖(h : ℂ)‖ ^ 2 = h ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [norm_div, div_pow, hh2]
  field_simp

theorem fourier_transform_min_decay (m : ℝ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hint0 : MeasureTheory.Integrable m)
    (hint2 : MeasureTheory.Integrable (deriv (deriv m)))
    (hdiff1 : Differentiable ℝ m) (hdiff2 : Differentiable ℝ (deriv m))
    (h0 : ∫ x, ‖m x‖ ≤ A) (h2 : ∫ x, ‖deriv (deriv m) x‖ ≤ B) (t : ℝ) (ht : t ≠ 0) :
    ‖FourierTransform.fourier m t‖ ≤ min A (B / (2 * Real.pi * |t|) ^ 2) := by
  refine le_min ((fourier_norm_le m t).trans h0) ?_
  set z : ℝ := ‖FourierTransform.fourier m t‖ with hz
  -- Bound valid for every `h > 0`.
  have hkey : ∀ h : ℝ, 0 < h →
      z * ‖(Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) / h‖ ^ 2 ≤ B := by
    intro h hh
    have hsd : ∫ x, ‖m x - 2 * m (x + h) + m (x + 2 * h)‖
        ≤ h ^ 2 * ∫ x, ‖deriv (deriv m) x‖ :=
      Commons.Analysis.Calculus.integral_second_difference_le_sq m h hh.le
        hdiff1 hdiff2 hint2
    have hB' : h ^ 2 * ∫ x, ‖deriv (deriv m) x‖ ≤ h ^ 2 * B :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg h)
    have hnorm : z * ‖Complex.exp (2 * Real.pi * Complex.I * t * h) - 1‖ ^ 2
        ≤ ∫ x, ‖m x - 2 * m (x + h) + m (x + 2 * h)‖ := by
      have hid := Commons.Analysis.Fourier.fourier_second_difference_identity m hint0 t h
      have h1 : ‖(Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) ^ 2
            * FourierTransform.fourier m t‖
          ≤ ∫ x, ‖m x - 2 * m (x + h) + m (x + 2 * h)‖ := by
        rw [← hid]
        calc ‖∫ x, fourierKernel t x * (m x - 2 * m (x + h) + m (x + 2 * h))‖
            ≤ ∫ x, ‖fourierKernel t x * (m x - 2 * m (x + h) + m (x + 2 * h))‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ x, ‖m x - 2 * m (x + h) + m (x + 2 * h)‖ := by
              apply integral_congr_ae; filter_upwards with x
              rw [norm_mul, fourierKernel_norm, one_mul]
      rw [norm_mul, norm_pow, ← hz, mul_comm] at h1
      exact h1
    have h2z : z * ‖Complex.exp (2 * Real.pi * Complex.I * t * h) - 1‖ ^ 2 ≤ B * h ^ 2 :=
      hnorm.trans ((hsd.trans hB').trans_eq (mul_comm _ _))
    have hmul := mul_norm_div_pow_mul_self z (Complex.exp (2 * Real.pi * Complex.I * t * h) - 1)
      (ne_of_gt hh)
    have : z * ‖(Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) / h‖ ^ 2 * h ^ 2
        ≤ B * h ^ 2 := by
      rw [hmul]; exact h2z
    exact (mul_le_mul_iff_of_pos_right (pow_pos hh 2)).mp this
  -- Pass to the limit `h → 0⁺`.
  have hlim : Tendsto
      (fun h : ℝ => z * ‖(Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) / h‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (z * (2 * Real.pi * |t|) ^ 2)) := by
    have hbase : Tendsto
        (fun h : ℝ => ‖(Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) / h‖)
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi * |t|)) := by
      have h := (tendsto_exp_slope t).norm
      rw [norm_two_pi_I_mul t] at h
      exact h
    have hsq := hbase.pow 2
    have hz2 : Tendsto
        (fun h : ℝ => z * ‖(Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) / h‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (z * (2 * Real.pi * |t|) ^ 2)) :=
      hsq.const_mul z
    exact hz2
  have hmain : z * (2 * Real.pi * |t|) ^ 2 ≤ B :=
    le_of_tendsto hlim (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact hkey h hh)
  rw [le_div_iff₀ (by
    have : 0 < |t| := abs_pos.mpr ht
    positivity)]
  exact hmain

end Commons.Analysis.Fourier
