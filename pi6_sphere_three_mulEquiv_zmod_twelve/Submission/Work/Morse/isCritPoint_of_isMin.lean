import Mathlib
import Submission.Work.Morse.Basic

set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

namespace Work.Morse

/-- A global minimum of a smooth function on a smooth manifold without boundary is a critical
point. -/
theorem isCritPoint_of_isMin {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {p : M} (hmin : ∀ x, f p ≤ f x) :
    IsCritPoint (n := n) f p := by
  -- `f` is differentiable at `p`
  have hmd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f p := hf.mdifferentiableAt (by simp)
  -- write the manifold derivative in the preferred chart at `p`
  rw [IsCritPoint, hmd.mfderiv]
  -- the model space is boundaryless, so the chart range is everything
  have hrange : Set.range (↑(𝓡 n) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      Set.univ := by
    rw [modelWithCornersSelf_coe, Set.range_id]
  rw [hrange, fderivWithin_univ]
  -- in the chart, `f` is just `y ↦ f (chart.symm y)` (the target chart on `ℝ` is the identity)
  have hW : writtenInExtChartAt (𝓡 n) 𝓘(ℝ, ℝ) p f
      = fun y : EuclideanSpace ℝ (Fin n) => f ((extChartAt (𝓡 n) p).symm y) := by
    funext y
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_apply, modelWithCornersSelf_coe]
    simp
  rw [hW]
  -- this chart expression has a global — hence local — minimum at the image of `p`
  have h0 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => f ((extChartAt (𝓡 n) p).symm y))
      ((extChartAt (𝓡 n) p) p) = 0 := by
    apply IsLocalMin.fderiv_eq_zero
    refine Filter.Eventually.of_forall (fun y => ?_)
    show f ((extChartAt (𝓡 n) p).symm ((extChartAt (𝓡 n) p) p)) ≤
      f ((extChartAt (𝓡 n) p).symm y)
    rw [(extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p)]
    exact hmin _
  first
    | (rw [h0]; simp)
    | (ext v; simp [h0])
    | (simp only [h0]; rfl)

end Work.Morse
