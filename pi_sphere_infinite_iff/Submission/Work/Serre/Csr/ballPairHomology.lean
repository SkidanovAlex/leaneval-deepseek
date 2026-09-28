import Mathlib
import Submission.Work.Cohomology.ballPairHomologyTop
import Submission.Work.Cohomology.puncturedBallSphere
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.euclideanLocalHomologyZero

set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.Csr

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Excision identifies the relative homology of the punctured open ball with that of the punctured
Euclidean space.  The cover is by the ball `U = Metric.ball 0 r` and the complement
`A = {v | v ≠ 0}` of the origin (both open, and `U ∪ A = univ` since `0 ∈ U`). -/
theorem relChainsBallHomologyIso (D : ℕ) (r : ℝ) (hr : 0 < r) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r))
        {z : Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r |
          (z : EuclideanSpace ℝ (Fin D)) ≠ 0}).homology m) ≅
      ((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin D)))
        {v : EuclideanSpace ℝ (Fin D) | v ≠ 0}).homology m)) := by
  have hU : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r) := Metric.isOpen_ball
  have hA : IsOpen {v : EuclideanSpace ℝ (Fin D) | v ≠ 0} := isClosed_singleton.isOpen_compl
  have hcov : Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r ∪
      {v : EuclideanSpace ℝ (Fin D) | v ≠ 0} = Set.univ := by
    ext v
    rcases eq_or_ne v 0 with hv | hv
    · subst hv
      simp [Metric.mem_ball_self hr]
    · simp [hv]
  haveI : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin D)))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r)
        {v : EuclideanSpace ℝ (Fin D) | v ≠ 0}) m) :=
    Work.Cohomology.excision_relChainsMap_isIso
      (X := TopCat.of (EuclideanSpace ℝ (Fin D)))
      (U := Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r)
      (A := {v : EuclideanSpace ℝ (Fin D) | v ≠ 0}) hU hA hcov m
  exact ⟨asIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin D)))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r)
        {v : EuclideanSpace ℝ (Fin D) | v ≠ 0}) m)⟩

/-- The relative homology of the pair (open ball of radius `r`, its punctured version) in
`EuclideanSpace ℝ (Fin D)`: it is `ℤ` in degree `D` and vanishes in every other degree. -/
theorem ballPairHomology (D : ℕ) (hD : 1 ≤ D) (r : ℝ) (hr : 0 < r) :
    (∀ m : ℕ, m ≠ D → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of (Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r))
        {z : Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r |
          (z : EuclideanSpace ℝ (Fin D)) ≠ 0}).homology m)) ∧
    Nonempty ((Work.Cohomology.relChains (TopCat.of (Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r))
        {z : Metric.ball (0 : EuclideanSpace ℝ (Fin D)) r |
          (z : EuclideanSpace ℝ (Fin D)) ≠ 0}).homology D ≅ ModuleCat.of ℤ ℤ) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · obtain ⟨e⟩ := relChainsBallHomologyIso D r hr m
    exact IsZero.of_iso (Work.Cohomology.euclideanLocalHomologyZero D m hD hm) e
  · exact Work.Cohomology.ballPairHomologyTop D hD 0 r hr

end

end Work.Serre.Csr
