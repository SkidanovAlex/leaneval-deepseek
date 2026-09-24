import Mathlib.Analysis.Fourier.PoissonSummation
import Submission.Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform

/-- Poisson summation in the form needed for oscillatory-integral work: for a smooth compactly
supported `f : ℝ → ℂ`,

`∑' n : ℤ, f n = ∑' k : ℤ, ∫ x, exp(-2πi x k) · f x`.

Proof: `Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport`,
`SchwartzMap.tsum_eq_tsum_fourier` at `x = 0` (where `fourier k 0 = 1`), `SchwartzMap.fourier_coe`
and `Real.fourier_eq'`. -/
theorem poisson_tsum_eq_tsum_fourier {f : ℝ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hcs : HasCompactSupport f) :
    ∑' n : ℤ, f n
      = ∑' k : ℤ, ∫ x : ℝ, Complex.exp (((-2 * Real.pi * (x * (k : ℝ)) : ℝ) : ℂ) * Complex.I) * f x := by
  obtain ⟨g, hg⟩ :=
    Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport hf hcs
  have hbase : ∑' n : ℤ, g n = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) n := by
    have h := SchwartzMap.tsum_eq_tsum_fourier g 0
    simpa [SchwartzMap.fourier_coe] using h
  have h2 : ∀ k : ℤ, 𝓕 (g : ℝ → ℂ) k =
      ∫ x : ℝ, Complex.exp (((-2 * Real.pi * (x * (k : ℝ)) : ℝ) : ℂ) * Complex.I) * f x := by
    intro k
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul, hg, Real.inner_apply]
  calc ∑' n : ℤ, f n = ∑' n : ℤ, g n := tsum_congr fun n => (hg n).symm
    _ = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) n := hbase
    _ = ∑' k : ℤ, ∫ x : ℝ,
          Complex.exp (((-2 * Real.pi * (x * (k : ℝ)) : ℝ) : ℂ) * Complex.I) * f x :=
        tsum_congr h2

end Commons.Analysis.Fourier