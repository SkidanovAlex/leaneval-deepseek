/-
# The Riesz–Thorin step of the exponent upgrade (item 2)

The exponent upgrade of `Work.KMTAreas.A7.lacunaryBumpVarEstimate` runs the Ionescu–Wainger
endpoint bound at the even exponent `2k₀` (with `k₀ := max 2 (iwR p)` chosen by
`Work.KMTAreas.A7.exists_endpoint_exponent`, so that `p` and its Hölder dual `p'` both lie in
`[2, 2k₀]`) and the elementary `ℓ²` bound at `2`
(`Work.Analysis.IWMultiplier.IWMultiplierBoundScalar_q2`), then reaches every intermediate exponent
by Riesz–Thorin (`Work.Analysis.IWMultiplier.IWLqBound_interpolation`, proved).

This file isolates that step together with its exponent bookkeeping:

* `IWLqBound_interpolate_two` — the `q₀ = 2` instance of `IWLqBound_interpolation`, with the
  `toReal` normalisations of the two endpoints discharged;
* `exists_interp_theta` — for `2 ≤ q ≤ 2k₀` the existence of the interpolation parameter `θ`,
  `0 ≤ θ ≤ 1`, with `q⁻¹ = (1-θ)/2 + θ/(2k₀)` (so the wiring never has to solve for `θ` itself).
-/
import Mathlib
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators

/-- **Riesz–Thorin at `q₀ = 2`.**  A bound for the Ionescu–Wainger multiplier at the `ℓ²` endpoint
and at the even exponent `2k₀` (`k₀ ≥ 2`) gives, at the interpolated exponent `q` determined by
`θ`, the bound with the log-convex constant `C₂ ^ (1-θ) * C₁ ^ θ`. -/
theorem IWLqBound_interpolate_two {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {q : ENNReal} {k₀ : ℕ} (hk₀ : 2 ≤ k₀)
    {C₂ C₁ : NNReal} (h₂ : Work.Analysis.IWMultiplier.IWLqBound A Φ 2 C₂)
    (h₁ : Work.Analysis.IWMultiplier.IWLqBound A Φ (ENNReal.ofReal (2 * (k₀ : ℝ))) C₁)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hq : (q.toReal)⁻¹ = (1 - θ) * (2 : ℝ)⁻¹ + θ * (2 * (k₀ : ℝ))⁻¹) :
    Work.Analysis.IWMultiplier.IWLqBound A Φ q (C₂ ^ (1 - θ) * C₁ ^ θ) := by
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hk₀)
  refine Work.Analysis.IWMultiplier.IWLqBound_interpolation A Φ h₂ h₁ hθ₀ hθ₁ ?_ ?_ ?_
  · norm_num
  · rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  · simpa using hq

end Work.KMTAreas.A7
