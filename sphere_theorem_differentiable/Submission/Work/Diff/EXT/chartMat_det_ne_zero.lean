import Mathlib
import Submission.Work.Diff.EXT.gram_det_ne_zero_linearEquiv
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle

namespace Work.Diff.EXT

/-- **The chart matrix of a Riemannian metric is non-degenerate**: for a chart coordinate `y` in the
target of the extended chart at `x₀`, the matrix of `g` in the coordinate frame of that chart is a
Gram matrix of a basis with respect to a positive definite form, hence has non-zero determinant. -/
theorem chartMat_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) (M := M) g x₀ y)).det ≠ 0 := by
  classical
  let p : M := (extChartAt I x₀).symm y
  -- register the metric `g` as a Riemannian bundle structure, so that the tangent spaces carry
  -- the normed/inner-product structure induced by `g` (needed to apply the linear-algebra lemma)
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- `p` lies in the chart at `x₀`, hence in the base set of the tangent-bundle trivialisation.
  have hp : p ∈ (chartAt H' x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
      have h2 := PartialEquiv.map_target (extChartAt I x₀) hy
      rwa [extChartAt_source] at h2
    exact h1
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hp
  -- the coordinate frame of the chart at `x₀` at the point `p` is the image of a linear equivalence
  let L : E ≃ₗ[ℝ] TangentSpace I p :=
    (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E (TangentSpace I) x₀) p hb).symm
  have hL : ∀ v : E, L v = Submission.Geodesic.frameVector (I := I) x₀ p v := by
    intro v
    dsimp only [L, Submission.Geodesic.frameVector]
    rw [Bundle.Trivialization.linearEquivAt_symm_apply]
    exact (Bundle.Trivialization.symmL_apply (R := ℝ)
      (trivializationAt E (TangentSpace I) x₀) hb v).symm
  -- the chart matrix is therefore a Gram matrix of the metric in the basis `L ∘ bB`
  have hgram : Matrix.of (chartMatFun (I := I) (M := M) g x₀ y) =
      Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        g.inner p (L (Module.finBasis ℝ E i)) (L (Module.finBasis ℝ E j))) := by
    ext i j
    simp only [Matrix.of_apply, chartMatFun]
    change ((g.inner p) (Submission.Geodesic.frameVector (I := I) x₀ p (bB (E := E) i)))
        (Submission.Geodesic.frameVector (I := I) x₀ p (bB (E := E) j)) =
      ((g.inner p) (L (Module.finBasis ℝ E i))) (L (Module.finBasis ℝ E j))
    rw [← hL, ← hL]
  rw [hgram]
  exact gram_det_ne_zero_linearEquiv (V := (fun x : M ↦ TangentSpace I x) p) L (g.inner p)
    (fun v w => g.symm p v w) (fun v hv => g.pos p v hv)

end Work.Diff.EXT
