import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.boxEnergy_le_sectorEnergy`

The free-particle-number box energy `EΛ = ⨅ n, EΛn n` is the infimum over the
*free* particle number of the per-sector box energies.  Consequently, whenever
that family is bounded below (so that the `iInf` is a genuine infimum rather
than Mathlib's junk value for an unbounded-below family), `EΛ` is a lower bound
for each individual sector:

  `EΛ v g ℓ μ d s εT b ≤ EΛn m v g ℓ μ d s εT b`.

This is the trivial half of the particle-number sector decomposition of the box
energy: the box energy is an infimum over the sectors, hence below every sector.
It is used to transfer a per-sector bound to the box energy
(cf. `Sector/boxForm_ge_boxEnergy_fixed.lean`, FS `thm:CompareBoxEnergy`).

The statement is *definitionally* the infimum inequality: `EΛ` unfolds to
`⨅ n : ℕ, EΛn n …`, so `ciInf_le` (the bounded-below form of `iInf_le`) with
the family `f := fun k => EΛn k …` gives the claim at once.
-/

namespace Work.BoseKinLoc.Sector

/-- **`EΛ` is below every particle-number sector.**  With the family of
per-sector box energies `k ↦ EΛn k …` bounded below, `EΛ ≤ EΛn m` for every
`m : ℕ`. -/
theorem boxEnergy_le_sectorEnergy {v g : ℝ³ → ℝ} {ℓ μ d s εT b : ℝ} {m : ℕ}
    (hEo : BddBelow (Set.range (fun k : ℕ => Work.BoseKinLoc.EΛn k v g ℓ μ d s εT b))) :
    Work.BoseKinLoc.EΛ v g ℓ μ d s εT b ≤ Work.BoseKinLoc.EΛn m v g ℓ μ d s εT b := by
  exact ciInf_le hEo m

end Work.BoseKinLoc.Sector
