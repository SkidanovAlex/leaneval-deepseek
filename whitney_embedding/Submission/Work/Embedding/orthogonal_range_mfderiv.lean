import Mathlib
import Submission.Work.Embedding.exists_unique_closest_point
import Submission.Work.Projection.mfderiv_chartAt_decomp

namespace Work.Embedding

open scoped Manifold ContDiff
open Topology Metric

/-- A vector is orthogonal to the range of `mfderiv e q` if and only if the adjoint of the
Fréchet derivative of the chart representation `chartRepN e p` kills it.  The point is that in a
chart at `p`, the manifold derivative of `e` at `q` factors as
`D(chartRepN e p) ∘L mfderiv (chartAt p) q`, and the derivative of the chart is surjective
(it is the derivative of a partial homeomorphism), so the two ranges agree; then one applies
`ContinuousLinearMap.orthogonal_range` (`T.rangeᗮ = T.adjoint.ker`). -/
theorem orthogonal_range_mfderiv {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    {p q : M} (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (v : EuclideanSpace ℝ (Fin N)) :
    v ∈ (mfderiv (𝓡 n) (𝓡 N) e q).rangeᗮ ↔
      (fderiv ℝ (Work.Embedding.chartRepN e p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) q)).adjoint v = 0 := by
  -- The derivative of the chart at `q` is surjective.
  have hTsurj : Function.Surjective
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q) :=
    (mdifferentiable_chart (I := 𝓡 n) p).mfderiv_surjective hq
  -- Chain rule: `mfderiv e q = D(chartRepN e p) ∘L mfderiv (chartAt p) q`.
  have hdec := Work.Projection.mfderiv_chartAt_decomp e he p q hq
  -- Consequently the two ranges agree.
  have hrange : (mfderiv (𝓡 n) (𝓡 N) e q).range =
      (fderiv ℝ (chartRepN e p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) q)).range := by
    rw [hdec]
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q x, rfl⟩
    · rintro y ⟨x, rfl⟩
      obtain ⟨x', rfl⟩ := hTsurj x
      exact ⟨x', rfl⟩
  rw [hrange, ContinuousLinearMap.orthogonal_range, LinearMap.mem_ker]
  exact Iff.rfl

end Work.Embedding
