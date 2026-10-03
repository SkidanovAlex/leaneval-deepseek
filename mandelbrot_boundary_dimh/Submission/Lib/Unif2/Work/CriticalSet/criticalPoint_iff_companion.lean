import Mathlib
import Submission.Lib.Unif2.Work.CriticalSet.Defs
import Submission.Lib.Unif2.Work.CriticalSet.Fundamentals

namespace Work.CriticalSet

open Filter

/-- The inverse of the preferred chart at `x` is continuous at `(chartAt ℂ x) x`. -/
theorem tendsto_symm_chartAt_companion {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    Filter.Tendsto (chartAt ℂ x).symm (nhds ((chartAt ℂ x) x)) (nhds x) := by
  have h := (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  simp only [ContinuousAt] at h
  rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h

/-- **A point is critical for a harmonic function exactly when the derivative of a holomorphic companion vanishes there.**

`Work.CriticalSet.IsCriticalPointAt u x` unfolds (in the preferred chart at `x`) to
`fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0`.  For harmonic `u` this is equivalent to
the existence of a local holomorphic companion `F` whose complex derivative vanishes at `x`.

Proof strategy.  For (⇒): take `F` from `Submission.exists_holomorphicOnXAt_re_of_harmonic hu`
(holomorphic at `x` with `Re F =ᶠ u` near `x`), and use
`Work.CriticalSet.fderiv_re_eq_zero_iff`
(`AnalyticAt ℂ F z → fderiv ℝ (fun w => (F w).re) z = 0 ↔ deriv F z = 0`)
together with `Filter.EventuallyEq.fderiv_eq`.  For (⇐): from a companion `F` with `Re F =ᶠ u`, deduce
`(u ∘ (chartAt ℂ x).symm) =ᶠ (fun w => ((F ∘ (chartAt ℂ x).symm) w).re)` near `(chartAt ℂ x) x` using the
continuity of `(chartAt ℂ x).symm` and `OpenPartialHomeomorph.left_inv`, then apply
`Filter.EventuallyEq.fderiv_eq` and `Work.CriticalSet.fderiv_re_eq_zero_iff`.  Note that
`Submission.HolomorphicOnXAt F x` *is by definition*
`AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`. -/
theorem criticalPoint_iff_companion {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {x : X}
    (hu : Submission.HarmonicOnXAt u x) :
    IsCriticalPointAt u x ↔ ∃ F : X → ℂ, Submission.HolomorphicOnXAt F x ∧
      (fun y => (F y).re) =ᶠ[nhds x] u ∧
      deriv (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0 := by
  have htend : Filter.Tendsto (chartAt ℂ x).symm (nhds ((chartAt ℂ x) x)) (nhds x) :=
    tendsto_symm_chartAt_companion x
  constructor
  · intro hcrit
    obtain ⟨F, hF, hFre⟩ := Submission.exists_holomorphicOnXAt_re_of_harmonic hu
    refine ⟨F, hF, hFre, ?_⟩
    rw [← Work.CriticalSet.fderiv_re_eq_zero_iff (F := F ∘ (chartAt ℂ x).symm)
      (z := (chartAt ℂ x) x) hF]
    have hEq : (fun w => ((F ∘ (chartAt ℂ x).symm) w).re) =ᶠ[nhds ((chartAt ℂ x) x)]
        (u ∘ (chartAt ℂ x).symm) := by
      filter_upwards [htend.eventually hFre] with w hw
      exact hw
    rw [hEq.fderiv_eq]
    exact hcrit
  · rintro ⟨F, hF, hFre, hderiv⟩
    show fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0
    have hEq : (fun w => ((F ∘ (chartAt ℂ x).symm) w).re) =ᶠ[nhds ((chartAt ℂ x) x)]
        (u ∘ (chartAt ℂ x).symm) := by
      filter_upwards [htend.eventually hFre] with w hw
      exact hw
    rw [← hEq.fderiv_eq]
    rw [Work.CriticalSet.fderiv_re_eq_zero_iff (F := F ∘ (chartAt ℂ x).symm)
      (z := (chartAt ℂ x) x) hF]
    exact hderiv

end Work.CriticalSet
