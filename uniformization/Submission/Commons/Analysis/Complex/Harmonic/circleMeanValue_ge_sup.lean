import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.CircleAverage
import Submission.Commons.Analysis.Complex.Harmonic.subharmonic_le_harmonic_of_le_on_sphere

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **The pointwise supremum of two subharmonic functions is subharmonic.**  If `v` and `w` are
continuous on an open set `Ω ⊆ ℂ` and satisfy the circle mean-value inequality at every point
of `Ω`, then so does `z ↦ max (v z) (w z)`. -/
theorem circleMeanValue_ge_sup {Ω : Set ℂ} (hΩ : IsOpen Ω) {v w : ℂ → ℝ}
    (hvcont : ContinuousOn v Ω) (hwcont : ContinuousOn w Ω)
    (hv : ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      v p ≤ Real.circleAverage v p r)
    (hw : ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      w p ≤ Real.circleAverage w p r) :
    ContinuousOn (fun z : ℂ => max (v z) (w z)) Ω ∧
      ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
        max (v p) (w p) ≤ Real.circleAverage (fun z : ℂ => max (v z) (w z)) p r := by
  have hcont_g : ContinuousOn (fun z : ℂ => max (v z) (w z)) Ω := hvcont.sup hwcont
  refine ⟨hcont_g, ?_⟩
  intro p hp r hr hball
  have hsphere : Metric.sphere p r ⊆ Ω :=
    fun z hz => hball (Metric.sphere_subset_closedBall hz)
  have hsphere_abs : Metric.sphere p |r| ⊆ Ω := by
    rw [abs_of_pos hr]; exact hsphere
  have hv_int : CircleIntegrable v p r := (hvcont.mono hsphere_abs).circleIntegrable'
  have hw_int : CircleIntegrable w p r := (hwcont.mono hsphere_abs).circleIntegrable'
  have hg_int : CircleIntegrable (fun z : ℂ => max (v z) (w z)) p r :=
    (hcont_g.mono hsphere_abs).circleIntegrable'
  have hvg : Real.circleAverage v p r ≤ Real.circleAverage (fun z : ℂ => max (v z) (w z)) p r :=
    Real.circleAverage_mono hv_int hg_int (fun x _ => le_max_left _ _)
  have hwg : Real.circleAverage w p r ≤ Real.circleAverage (fun z : ℂ => max (v z) (w z)) p r :=
    Real.circleAverage_mono hw_int hg_int (fun x _ => le_max_right _ _)
  calc max (v p) (w p)
      ≤ max (Real.circleAverage v p r) (Real.circleAverage w p r) :=
        max_le_max (hv p hp r hr hball) (hw p hp r hr hball)
    _ ≤ Real.circleAverage (fun z : ℂ => max (v z) (w z)) p r := max_le hvg hwg

end Commons.Analysis.Complex.Harmonic