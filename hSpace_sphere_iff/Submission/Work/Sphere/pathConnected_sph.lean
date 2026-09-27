import Mathlib
import Submission.Work.Sphere.Basic
import Submission.Work.Sphere.contractibleSpace_sph_compl

namespace Work.Sphere

/-- The sphere `Sᵏ` is path connected for `k ≥ 1`: its dimension `k + 1` is `> 1`, so it is
covered by Mathlib's `isPathConnected_sphere`. (For `k = 0` the space `S⁰` is the two point
space `{±1}`, which is not connected, so the hypothesis `1 ≤ k` is necessary.) -/
theorem pathConnected_sph (k : ℕ) (hk : 1 ≤ k) :
    PathConnectedSpace (Submission.Sphere.Sph k) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin (k + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < k + 1)
  have hpc : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere hrank 0 (by norm_num))
  exact hpc

end Work.Sphere
