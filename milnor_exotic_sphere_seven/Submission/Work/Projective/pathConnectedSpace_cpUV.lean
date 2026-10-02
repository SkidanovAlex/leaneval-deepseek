import Mathlib
import Submission.Work.Projective.CPn
import Submission.Work.Projective.cpnUV_homotopyEquiv_sphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `cpU ∩ cpV` in `ℂPⁿ` is path connected

Here `cpU n = chartSet 0` is the affine chart at `0` and `cpV n = ⋃_{i ≠ 0} chartSet i` is the
complement of the point `[1 : 0 : … : 0]`.  The chart at `0` identifies `cpU n ∩ cpV n` with the
punctured model space `ℂⁿ ∖ {0}` (`Work.Projective.cpnUV_homeo`), which for `n ≥ 1` is path
connected because it is the complement of a point in a real vector space of dimension `2n ≥ 2`
(`isPathConnected_compl_singleton_of_one_lt_rank`).
-/

open scoped Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-- **`U ∩ V = chartSet 0 ∩ ⋃_{i ≠ 0} chartSet i` in `ℂPⁿ` is path connected for `n ≥ 1`.**

The chart at `0` maps `U ∩ V` homeomorphically onto the punctured model space `ℂⁿ ∖ {0}`, which is
the complement of the origin in a real vector space of dimension `2n`, hence path connected as soon
as `2n ≥ 2`. -/
theorem pathConnectedSpace_cpUV (n : ℕ) :
    PathConnectedSpace ↥(Work.Projective.cpU (n + 1) ∩ Work.Projective.cpV (n + 1)) := by
  -- The punctured model space `ℂ^{n+1} ∖ {0}` is path connected (real dimension `2(n+1) ≥ 2`).
  haveI : PathConnectedSpace {z : Fin (n + 1) → ℂ // z ≠ 0} := by
    have hrank : 1 < Module.rank ℝ (Fin (n + 1) → ℂ) := by
      rw [← Module.finrank_eq_rank, finrank_real_fin_complex]
      rw [← Nat.cast_one, Nat.cast_lt]
      omega
    exact (isPathConnected_iff_pathConnectedSpace
      (F := ({0} : Set (Fin (n + 1) → ℂ))ᶜ)).mp
      (by simpa using isPathConnected_compl_singleton_of_one_lt_rank hrank 0)
  -- Transfer along the chart homeomorphism `U ∩ V ≃ₜ ℂ^{n+1} ∖ {0}`.
  rw [pathConnectedSpace_iff_univ]
  exact ((cpnUV_homeo (n + 1)).isPathConnected_preimage (s := Set.univ)).mpr
    isPathConnected_univ

end

end Work.Projective
