import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace Commons.Analysis.Measure

theorem locallyIntegrable_of_aestronglyMeasurable_of_integrableOn_sq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [LocallyCompactSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsFiniteMeasureOnCompacts μ] {g : X → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g μ)
    (hg : ∀ K : Set X, IsCompact K →
      MeasureTheory.IntegrableOn (fun x => g x ^ 2) K μ) :
    MeasureTheory.LocallyIntegrable g μ := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  have hμK : μ K < ⊤ := hK.measure_lt_top
  have hone : MeasureTheory.IntegrableOn (fun _ : X => (1 : ℝ)) K μ :=
    MeasureTheory.integrableOn_const (hs := hμK.ne)
  have hsum : MeasureTheory.IntegrableOn (fun x => g x ^ 2 + 1) K μ := by
    show MeasureTheory.Integrable (fun x => g x ^ 2 + 1) (μ.restrict K)
    exact (hg K hK).add hone
  have hbound : ∀ᵐ x ∂(μ.restrict K), ‖g x‖ ≤ g x ^ 2 + 1 :=
    Filter.Eventually.of_forall fun x => by
      have h : |g x| ≤ g x ^ 2 + 1 := by
        nlinarith [sq_nonneg (|g x| - 1 / 2), sq_abs (g x), abs_nonneg (g x)]
      simpa [Real.norm_eq_abs] using h
  show MeasureTheory.Integrable g (μ.restrict K)
  exact hsum.mono' hgm.restrict hbound

end Commons.Analysis.Measure