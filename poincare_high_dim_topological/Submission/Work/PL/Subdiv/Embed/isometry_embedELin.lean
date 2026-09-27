import Mathlib
import Submission.Work.PL.Subdiv.Embed

/-!
# `embedELin N : E N → E (N+1)` is an isometry

`embedELin N` inserts `x : E N` into `E (N+1)` as the first `N` coordinates (last coordinate `0`).
Equivalently, on `Lp` coordinates it extends a vector by a zero coordinate, so it preserves the
Euclidean (L2) norm on the nose, hence preserves distances.

The auxiliary lemmas record the coordinate description (`ofLp` form) and the norm equality; they are
stated in this namespace so that they are available to anything importing this module.
-/

open Set Metric
open scoped BigOperators

namespace Work.PL.Subdiv.Embed

/-- Coordinate description of `embedELin`: the `i`-th coordinate (`i : Fin N`) is unchanged. -/
lemma embedELin_ofLp_castSucc (N : ℕ) (x : PL.E N) (i : Fin N) :
    (Work.PL.Subdiv.embedELin N x).ofLp (Fin.castSucc i) = x.ofLp i := by
  simp [Work.PL.Subdiv.embedELin, WithLp.ofLp_toLp]

/-- Coordinate description of `embedELin`: the last coordinate is `0`. -/
lemma embedELin_ofLp_last (N : ℕ) (x : PL.E N) :
    (Work.PL.Subdiv.embedELin N x).ofLp (Fin.last N) = 0 := by
  simp [Work.PL.Subdiv.embedELin, WithLp.ofLp_toLp]

/-- `embedELin N` preserves the Euclidean norm. -/
lemma norm_embedELin (N : ℕ) (x : PL.E N) :
    ‖Work.PL.Subdiv.embedELin N x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [embedELin_ofLp_castSucc, embedELin_ofLp_last]

theorem isometry_embedELin (N : ℕ) : Isometry (Work.PL.Subdiv.embedELin N) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_embedELin N (x - y)

end Work.PL.Subdiv.Embed
