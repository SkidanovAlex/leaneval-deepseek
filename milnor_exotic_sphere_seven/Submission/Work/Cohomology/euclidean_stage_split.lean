import Mathlib
import Submission.Work.Cohomology.EuclideanStageDefs
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.homologyMV_honest_les
import Submission.Work.Cohomology.free_and_vanishing_ball_compl
import Submission.Work.Cohomology.localClass_union_injective
import Submission.Work.Cohomology.local_generator_convex
import Submission.Work.Cohomology.StageSplitMain
import Submission.Work.Cohomology.stage_split_of_lkMap_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

theorem euclidean_stage_split {N : ℕ} (hN : 1 ≤ N) {k l : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    (c' : Fin l → EuclideanSpace ℝ (Fin N)) (r' : Fin l → ℝ) (hr' : ∀ j, 0 < r' j)
    (hsub : (⋃ j, Metric.closedBall (c' j) (r' j)) ⊆
      interior (⋃ j, Metric.closedBall (c j) (r j)))
    (hcomp : ∀ x ∈ (⋃ j, Metric.closedBall (c j) (r j)),
      ∃ y ∈ (⋃ j, Metric.closedBall (c' j) (r' j)),
        x ∈ connectedComponentIn (⋃ j, Metric.closedBall (c j) (r j)) y) :
    ∃ s : ↥((singularChains ℤ (TopCat.of (Set.compl (⋃ j, Metric.closedBall (c' j) (r' j))))).homology (N - 1)) →ₗ[ℤ]
            ↥((singularChains ℤ (TopCat.of (Set.compl (⋃ j, Metric.closedBall (c j) (r j))))).homology (N - 1)),
      s.comp (Work.Cohomology.complMap (⋃ j, Metric.closedBall (c j) (r j))
        (⋃ j, Metric.closedBall (c' j) (r' j))
        (fun x hx => interior_subset (hsub hx))) = LinearMap.id := by
  obtain ⟨sL, hsL⟩ := Work.Cohomology.LK_stage_split (N := N) hN c r hr c' r' hr' hsub hcomp
  rcases eq_or_lt_of_le hN with h1 | h2
  · subst h1
    exact Work.Cohomology.stage_split_of_lkMap_one (hsub.trans interior_subset) ⟨sL, hsL⟩
  · exact Work.Cohomology.stage_split_of_lkMap_ge_two h2 (hsub.trans interior_subset) ⟨sL, hsL⟩

end Work.Cohomology
