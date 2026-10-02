import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.TautEmbedCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.LerayHirsch

theorem tautologicalEmbedding {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.LerayHirsch.TautologicalEmbedding Z :=
  TautEmbed.tautEmbedMap_injective Z

end Work.LerayHirsch
