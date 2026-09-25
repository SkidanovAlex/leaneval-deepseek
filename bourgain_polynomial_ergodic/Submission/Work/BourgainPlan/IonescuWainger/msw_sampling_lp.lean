import Mathlib
import Submission.Work.Analysis.Fourier.bandlimited_weighted_reproduction
import Submission.Commons.Analysis.Fourier.hausdorff_young_real
import Submission.Work.BourgainPlan.IonescuWainger.cutoff
import Submission.Work.BourgainPlan.IonescuWainger.cutoff_extension_lp
import Submission.Work.BourgainPlan.IonescuWainger.msw_of_cutoff_extension

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal BigOperators Interval

/-- **The Magyar–Stein–Wainger sampling principle** (Tao, arXiv:2008.05066, Proposition `msw`(i)),
in the operator form used in the proof of the Ionescu–Wainger multiplier theorem: if a symbol
`m : ℝ → ℂ` is supported in `[-1/2,1/2]` and its continuous Fourier multiplier is bounded on
`Lᵖ(ℝ)` with norm `≤ A` (the hypothesis `hOp`, tested on band-limited functions), then the
discrete multiplier with the same symbol, i.e. convolution on `ℤ` with the sampled kernel
`K(j) = ∫_{-(1/2)}^{1/2} m(ξ) e^{2πi j ξ} dξ`, is bounded on `ℓᵖ(ℤ)` with norm `≤ C·A`.

USEFUL INPUTS in this workspace: `Submission.Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow`
(the `ℓᵖ ≤ Lᵖ` sampling direction for band-limited functions, `p > 1`),
`Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel` and the private helper
`norm_le_integral_weighted` (the reproducing formula and the pointwise decay bound used for the
reverse direction `Lᵖ ≤ ℓᵖ`), and `Submission.Commons.Analysis.Fourier.sampling_reproducing`. -/
theorem msw_sampling_lp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (hmi : Integrable m)
      (hmsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → m ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ g : ℝ → ℂ, Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv (fun ξ => m ξ * FourierTransform.fourier g ξ) x‖ₑ ^ p ∂volume
          ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume)
      (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ n, n ∉ s → a n = 0),
      ∫⁻ n : ℤ, ‖∑ k ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2),
          m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k‖ₑ ^ p
        ∂Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p) * ∫⁻ n : ℤ, ‖a n‖ₑ ^ p ∂Measure.count := by
  obtain ⟨Cβ, hCβpos, hCβ⟩ := cutoff_extension_lp p hp
  exact msw_of_cutoff_extension p hp ⟨Cβ, hCβpos, hCβ⟩

end Work.BourgainPlan.IonescuWainger
