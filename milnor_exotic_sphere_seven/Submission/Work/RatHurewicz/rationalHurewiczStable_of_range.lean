import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.Stems.HurewiczNeutral

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

/-- **The map form of the rational Hurewicz result implies the drive's contract.**  The contract
`Work.Drive.RationalHurewiczStable` is phrased on the cube-level Hurewicz class
`Work.Stems.hurewiczChain`; `Work.RatHurewicz.HurewiczModTorsionRange` is phrased on the induced map
`Work.Stems.hurewiczMapN` of homotopy groups.  The two agree on the class of a cube
(`Work.Stems.hurewiczMapN_mk`), so the range form implies the contract. -/
theorem rationalHurewiczStable_of_range (h : Work.RatHurewicz.HurewiczModTorsionRange) :
    Work.Drive.RationalHurewiczStable := by
  intro k hk X _ x₀ hconn i hi p hp
  refine h k hk X x₀ hconn i hi
    (show HomotopyGroup (Fin (i + 1)) X x₀ from Quotient.mk _ p) ?_
  obtain ⟨N, hN, hNp⟩ := hp
  exact ⟨N, hN, by rw [Work.Stems.hurewiczMapN_mk]; exact hNp⟩

end Work.RatHurewicz
