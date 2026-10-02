import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relComplex_vanishing_of_homology_free
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.pd_good_iUnion
import Submission.Work.Cohomology.pdHom_iUnion_lift
import Submission.Work.Cohomology.euclidean_top_homology_free_onePoint
import Submission.Work.Cohomology.free_homology_homeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

/-- The image of the open set `U ⊆ ℝ^N` under the canonical open embedding
`OnePoint.some : ℝ^N → S^N = OnePoint ℝ^N`. -/
def onePointImage {N : ℕ} (U : Set (EuclideanSpace ℝ (Fin N))) :
    Set (OnePoint (EuclideanSpace ℝ (Fin N))) :=
  OnePoint.some '' U

theorem isOpen_onePointImage {N : ℕ} (U : Set (EuclideanSpace ℝ (Fin N))) (hU : IsOpen U) :
    IsOpen (onePointImage U) := by
  rw [onePointImage]
  exact OnePoint.isOpenEmbedding_coe.isOpenMap _ hU

theorem euclidean_top_homology_free {N : ℕ} (hN : 1 ≤ N)
    (U : Set (EuclideanSpace ℝ (Fin N))) (hU : IsOpen U) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥U)).homology (N - 1)) := by
  have hU' : IsOpen (onePointImage U) := isOpen_onePointImage U hU
  have hfree := euclidean_top_homology_free_onePoint hN (onePointImage U) hU'
  have e : TopCat.of ↥U ≃ₜ TopCat.of ↥(onePointImage U) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage U
  exact moduleFree_homology_of_homeomorph e (N - 1) hfree

end Work.Cohomology
