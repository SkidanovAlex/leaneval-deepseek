import Mathlib
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.Csr.Base
import Submission.Work.Serre.Csr.ballPairHomology
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.Target
import Submission.Work.Cohomology.relChainsHomeomorphCompat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.CsrSharp.Cell

/-- The relative rational homology of the target pair of the per-cell map in a single
`(n+2)`-cell: the pair `(o, o \ {c})` of the open half-ball `o = csrOpenBall n Y ι f i` around the
centre of the `i`-th attached cell and its punctured version is the pair of the `(n+2)`-disc with
its boundary sphere, so its relative rational homology is `ℚ` in degree `n+2` and vanishes
elsewhere.  Over `ℤ` this is `Work.Serre.Csr.csrTargetPair` (which transports
`Work.Serre.Csr.ballPairHomology` along the two homeomorphisms of pairs
`(csrOpenBall, csrCentre) ≅ (dOpen n (1/2), dPunct n (1/2))` and `dOpen n (1/2) ≅ Metric.ball 0 (1/2)`,
see `Submission/Work/Serre/Csr/Target.lean`); the present statement is the `ℚ`-coefficient version,
obtained by base change (`Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int`,
`Work.Serre.Csr.relChainsR_homology_iso_ratUnit`). -/
theorem targetGroups (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    (∀ m : ℕ, m ≠ n+2 → CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.csrOpenBall n Y ι f i))
        {x : ↥(Work.Serre.csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}}).homology m)) ∧
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.csrOpenBall n Y ι f i))
        {x : ↥(Work.Serre.csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}}).homology (n+2)
      ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨hvan, hiso⟩ := Work.Serre.Csr.csrTargetPair n Y ι f i
  exact ⟨fun m hm => Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int
      (TopCat.of ↥(Work.Serre.csrOpenBall n Y ι f i))
      {x : ↥(Work.Serre.csrOpenBall n Y ι f i) |
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}}
      m (hvan m hm),
    Work.Serre.Csr.relChainsR_homology_iso_ratUnit
      (TopCat.of ↥(Work.Serre.csrOpenBall n Y ι f i))
      {x : ↥(Work.Serre.csrOpenBall n Y ι f i) |
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}}
      (n+2) hiso⟩

end Work.Serre.CsrSharp.Cell
