import Mathlib
import Submission.Work.Drive.chartedSpaceChangeModel

namespace Work.Drive

/-- In the pushed-forward charted space `chartedSpaceChangeModel e.toHomeomorph`, the preferred
chart at `p` is the old preferred chart followed by the linear equivalence `e`. -/
theorem chartAt_chartedSpaceChangeModel_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (e : E ≃L[ℝ] E') (p : M) :
    (fun y : M => @chartAt E' _ M _ (Work.Drive.chartedSpaceChangeModel (𝕜 := ℝ) (M := M)
        e.toHomeomorph) p y) = fun y => e (chartAt E p y) := by
  funext y
  show ((chartAt E p).trans e.toHomeomorph.toOpenPartialHomeomorph) y = e (chartAt E p y)
  rw [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply]
  simp

theorem fderiv_chartAt_chartedSpaceChangeModel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (e : E ≃L[ℝ] E') {k : ℕ} (G : EuclideanSpace ℝ (Fin k) → M)
    (x : EuclideanSpace ℝ (Fin k)) (p : M) (hp : G x ∈ (chartAt E p).source) :
    fderiv ℝ (fun y => @chartAt E' _ M _ (Work.Drive.chartedSpaceChangeModel (𝕜 := ℝ) (M := M)
        e.toHomeomorph) p (G y)) x
      = (e : E →L[ℝ] E').comp (fderiv ℝ (fun y => chartAt E p (G y)) x) := by
  have hfun : (fun y => @chartAt E' _ M _ (Work.Drive.chartedSpaceChangeModel (𝕜 := ℝ) (M := M)
        e.toHomeomorph) p (G y)) = fun y => e (chartAt E p (G y)) := by
    have h := chartAt_chartedSpaceChangeModel_apply (M := M) e p
    funext y
    exact congrFun h (G y)
  rw [hfun]
  by_cases hd : DifferentiableAt ℝ (fun y => chartAt E p (G y)) x
  · have h := ((e : E →L[ℝ] E').hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    simpa [Function.comp_def] using h
  · have hd' : ¬ DifferentiableAt ℝ (fun y => e (chartAt E p (G y))) x := by
      intro h
      apply hd
      have h2 : DifferentiableAt ℝ (fun y => e.symm (e (chartAt E p (G y)))) x :=
        (e.symm : E' →L[ℝ] E).differentiableAt.comp x h
      simpa using h2
    rw [fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd]
    simp

end Work.Drive
