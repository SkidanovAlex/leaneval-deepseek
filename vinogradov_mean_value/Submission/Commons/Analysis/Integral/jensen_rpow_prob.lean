import Mathlib.Analysis.Convex.Integral

namespace Commons.Analysis.Integral

open MeasureTheory

/-- Probabilistic Jensen's inequality for the real power function `x ↦ x^p` with `1 ≤ p`,
on the nonnegative reals. -/
theorem jensen_rpow_prob {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p) {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hfi : MeasureTheory.Integrable f μ)
    (hfp : MeasureTheory.Integrable (fun x => f x ^ p) μ) :
    (∫ x, f x ∂μ) ^ p ≤ ∫ x, (f x) ^ p ∂μ := by
  have hg : ConvexOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := convexOn_rpow hp
  have hgc : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ici 0) :=
    (Real.continuous_rpow_const (by linarith)).continuousOn
  have hfs : ∀ᵐ x ∂μ, f x ∈ Set.Ici (0 : ℝ) := hf
  simpa using hg.map_integral_le (g := fun x : ℝ => x ^ p) hgc isClosed_Ici hfs hfi hfp

end Commons.Analysis.Integral