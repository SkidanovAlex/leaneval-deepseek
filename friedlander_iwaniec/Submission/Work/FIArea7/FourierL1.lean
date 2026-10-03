import Mathlib
import Submission.Work.FIArea7.SepK
import Submission.Work.FIArea7.FourierDefs
import Submission.Work.FIArea7.SepKFourierIdent
import Submission.Work.FIArea7.CRhoBounds
import Submission.Work.FIArea7.L1IntegralBound

namespace Work.FIArea7

open MeasureTheory intervalIntegral Real Complex Filter
open scoped Topology

noncomputable section

/-! ## The three pointwise bounds for the separating function `sepK`

Throughout, `K = sepK lam eps` with `0 < eps ≤ lam`, and we abbreviate
`A t = |(𝓕 K t).re|` where `𝓕 K t = ∫ y, exp(-2πiyt) K(y) dy`.

* `re_fourier_sepK_le_two_lam`: `A t ≤ 2λ`, the trivial `L¹` bound;
* `re_fourier_sepK_le_sin`: `A t ≤ |sin (2πλt)| / (π|t|)`, from the explicit formula for `𝓕K`;
* `re_fourier_sepK_le_sq`: `A t ≤ 8/(15π²ε t²)` for `|t| ≥ 8/(15πε)`.
-/

/-- The trivial `L¹` bound: `|(𝓕 K t).re| ≤ ∫|K| = 2λ`. -/
lemma re_fourier_sepK_le_two_lam (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) (t : ℝ) :
    |(FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re| ≤ 2 * lam := by
  have hlam : 0 ≤ lam := le_trans hε.le hle
  refine le_trans (Complex.abs_re_le_norm _) ?_
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm (𝕜 := ℝ) (V := ℝ) (W := ℝ)
      Real.fourierChar volume (innerₗ ℝ) (fun y : ℝ => (sepK lam eps y : ℂ)) t
  refine le_trans h ?_
  rw [← integral_abs_sepK hlam hε hle]
  apply integral_mono_of_nonneg
  · filter_upwards with y; exact norm_nonneg _
  · exact (integrable_sepK lam eps hlam hε).abs
  · filter_upwards with y
    simp

/-- The `sinc` bound: `|(𝓕 K t).re| ≤ |sin (2πλt)| / (π|t|)` for `t ≠ 0`, from the explicit
formula `(𝓕K t).re = sin (2πλt)·cRho (εt)/(πt)` and `|cRho| ≤ 1`. -/
lemma re_fourier_sepK_le_sin (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) (t : ℝ)
    (ht : t ≠ 0) :
    |(FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re|
      ≤ |Real.sin (2 * Real.pi * lam * t)| / (Real.pi * |t|) := by
  rw [SepKFourierIdent lam eps hε hle t ht]
  have hεt : eps * t ≠ 0 := mul_ne_zero hε.ne' ht
  have h1 : |cRho (eps * t)| ≤ 1 := le_trans (CRhoBounds (eps * t) hεt) (min_le_left _ _)
  simp only [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- The quadratic decay far out: `|(𝓕 K t).re| ≤ 8/(15π²ε t²)` for `|t| ≥ 8/(15πε)`, from the
explicit formula and the integration-by-parts bound `|cRho s| ≤ 8/(15π|s|)`. -/
lemma re_fourier_sepK_le_sq (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) (t : ℝ)
    (ht : 8 / (15 * Real.pi * eps) ≤ |t|) :
    |(FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re|
      ≤ 8 / (15 * Real.pi ^ 2 * eps * t ^ 2) := by
  have hbpos : 0 < 8 / (15 * Real.pi * eps) := by positivity
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    linarith
  rw [SepKFourierIdent lam eps hε hle t ht0]
  have hεt : eps * t ≠ 0 := mul_ne_zero hε.ne' ht0
  have h2 : |cRho (eps * t)| ≤ 8 / (15 * Real.pi * eps * |t|) := by
    have h := le_trans (CRhoBounds (eps * t) hεt) (min_le_right _ _)
    rw [abs_mul, abs_of_pos hε] at h
    rw [show 15 * Real.pi * (eps * |t|) = 15 * Real.pi * eps * |t| by ring] at h
    exact h
  have hnum : |Real.sin (2 * Real.pi * lam * t)| * |cRho (eps * t)|
      ≤ 8 / (15 * Real.pi * eps * |t|) := by
    calc |Real.sin (2 * Real.pi * lam * t)| * |cRho (eps * t)|
        ≤ 1 * (8 / (15 * Real.pi * eps * |t|)) :=
          mul_le_mul (Real.abs_sin_le_one _) h2 (abs_nonneg _) (by norm_num)
      _ = 8 / (15 * Real.pi * eps * |t|) := by ring
  simp only [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  refine le_trans (div_le_div_of_nonneg_right hnum (by positivity)) ?_
  rw [div_div]
  rw [show (15 * Real.pi * eps * |t|) * (Real.pi * |t|) = 15 * Real.pi ^ 2 * eps * t ^ 2 by
    rw [← sq_abs t]; ring]

/-- The `L¹` bound for the separating function: the real part of the Fourier transform of the
trapezoid `sepK λ ε` has `L¹` norm at most `(2/π)(2 + log (16λ/(15ε)))`.
(Here `FourierTransform.fourier f t = ∫ y, exp(-2πi y t) f y`.) -/
theorem FourierL1 (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) :
    ∫ t : ℝ, |((FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re)|
      ≤ (2 / Real.pi) * (2 + Real.log (16 * lam / (15 * eps))) := by
  refine L1IntegralBound lam eps hε hle
    (fun t => |(FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re|)
    (fun t => abs_nonneg _) (fun t => re_fourier_sepK_le_two_lam lam eps hε hle t)
    (fun t ht => re_fourier_sepK_le_sin lam eps hε hle t ht)
    (fun t ht => re_fourier_sepK_le_sq lam eps hε hle t ht)

end

end Work.FIArea7
