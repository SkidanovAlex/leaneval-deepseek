import Mathlib
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

namespace Commons.Analysis.Complex

/-- **Injectivity forces a non-vanishing derivative (chartwise).**
Let `X` be a complex one-dimensional manifold and `Φ : X → ℂ` injective and holomorphic
(as seen through the preferred charts).  Then for every `z : X` the derivative of the
chart-`z` representation `Φ ∘ (chartAt ℂ z).symm` at `(chartAt ℂ z) z` is non-zero.

Indeed, a vanishing derivative at a point of a holomorphic function produces two distinct
nearby points with the same value (branch point), which would contradict injectivity of `Φ`,
because the chart inverse is injective on the (open) chart target. -/
theorem deriv_ne_zero_of_injective_analytic
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Φ : X → ℂ} (hinj : Function.Injective Φ)
    (hhol : ∀ x : X, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    {z : X} (hne : ∃ y : X, y ≠ z) :
    deriv (Φ ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) ≠ 0 := by
  have _hne : ∃ y : X, y ≠ z := hne
  -- The chart target is open and contains the image of `z`, so it contains a ball around it.
  obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp (chartAt ℂ z).open_target _
    ((chartAt ℂ z).map_source (mem_chart_source ℂ z))
  -- On that ball, the chart inverse is injective, so `Φ ∘ (chartAt ℂ z).symm` is injective.
  refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hrpos (hhol z) ?_
  intro u hu v hv huv
  have huch : (chartAt ℂ z) ((chartAt ℂ z).symm u) = u := (chartAt ℂ z).right_inv (hrsub hu)
  have hvch : (chartAt ℂ z) ((chartAt ℂ z).symm v) = v := (chartAt ℂ z).right_inv (hrsub hv)
  have hs : (chartAt ℂ z).symm u = (chartAt ℂ z).symm v :=
    hinj (by simpa only [Function.comp_apply] using huv)
  rw [← huch, hs, hvch]

end Commons.Analysis.Complex
