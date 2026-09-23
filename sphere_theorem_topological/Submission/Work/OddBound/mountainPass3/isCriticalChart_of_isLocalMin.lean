import Mathlib
import Submission.Work.OddBound.PolygonChart

/-!
# A local minimum of a `C¹` function is a critical point in any atlas chart

A real function `f` on a charted space `P` that has a local minimum at `z` is critical at `z`
in the sense of `Work.OddBound.IsCriticalChart`: in *any* chart `e` of the atlas around `z`
in which the coordinate expression `f ∘ e.symm` is `C¹` (hence differentiable) at `e z`, the
coordinate derivative of `f ∘ e.symm` vanishes at `e z`.

This is Fermat's theorem pulled back along the chart inverse: the chart inverse is continuous
at `e z` (charts have open target), so the local minimum of `f` at `z` pulls back under
`IsLocalMin.comp_continuous` to a local minimum of the coordinate expression at `e z`, and
`IsLocalMin.hasFDerivAt_eq_zero` finishes.
-/

namespace Work.OddBound.mountainPass3

open scoped Manifold ContDiff

theorem isCriticalChart_of_isLocalMin
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] {f : P → ℝ} {z : P}
    (hz : IsLocalMin f z)
    {e : OpenPartialHomeomorph P H'} (he : e ∈ atlas H' P) (hzsrc : z ∈ e.source)
    (hsm : ContDiffAt ℝ 1 (fun x : H' => f (e.symm x)) (e z)) :
    Work.OddBound.IsCriticalChart H' f z := by
  refine ⟨e, he, hzsrc, ?_⟩
  -- The coordinate expression is differentiable at `e z`, being `C¹` there.
  have hd : DifferentiableAt ℝ (fun x : H' => f (e.symm x)) (e z) :=
    hsm.differentiableAt one_ne_zero
  -- The chart inverse is continuous at `e z` (its target is open and `e z ∈ e.target`).
  have hc : ContinuousAt (fun x : H' => e.symm x) (e z) :=
    e.continuousAt_symm (e.map_source hzsrc)
  have hz' : e.symm (e z) = z := e.left_inv hzsrc
  -- Pull the local minimum of `f` at `z` back to a local minimum of the coordinate
  -- expression at `e z`.
  rw [← hz'] at hz
  have hmin : IsLocalMin (fun x : H' => f (e.symm x)) (e z) := hz.comp_continuous hc
  -- Fermat's theorem: the derivative at a local minimum of a differentiable function vanishes.
  exact hmin.hasFDerivAt_eq_zero hd.hasFDerivAt

end Work.OddBound.mountainPass3
